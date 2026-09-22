import CompCert4Lean.Prototype.Json

namespace CompCert4Lean.Prototype

open CompCert4Lean
open Common.AST Common.Errors
open Backend Backend.Locations
open X86.Machregs X86.Op
open Foundation.Numbers.Rocq.Coq
open Lib.Maps

abbrev z := ZArith.BinInt.Z.of_nat
abbrev pos := PArith.BinPos.Pos.of_nat

instance : Flocq.Core.FLX.Prec_gt_0 (z 53) := by change (0 : Int) < 53; decide
instance : Flocq.Core.FLX.Prec_gt_0 (z 24) := by change (0 : Int) < 24; decide
instance : Flocq.IEEE754.BinarySingleNaN.Prec_lt_emax (z 53) (z 1024) :=
  ⟨by change (53 : Int) < 1024; decide⟩
instance : Flocq.IEEE754.BinarySingleNaN.Prec_lt_emax (z 24) (z 128) :=
  ⟨by change (24 : Int) < 128; decide⟩
instance : Flocq.IEEE754.Binary.BinaryNormalizeCertificate (z 53) (z 1024) :=
  Flocq.IEEE754.Binary.binary64_normalize_certificate_proof
instance : Flocq.IEEE754.Binary.BinaryNormalizeCertificate (z 24) (z 128) :=
  Flocq.IEEE754.Binary.binary32_normalize_certificate_proof
instance : Lib.IEEE754_extra.Bexact_inverse_certificate (z 53) (z 1024) :=
  Lib.IEEE754_extra.binary64_exact_inverse_certificate_proof
instance : Lib.IEEE754_extra.Bexact_inverse_certificate (z 24) (z 128) :=
  Lib.IEEE754_extra.binary32_exact_inverse_certificate_proof

def cfg := Config.pinnedLinuxX86_64 false 0 false false false false false

def selectionOracle : Selection.SelectionOracle :=
  { compileSwitch := fun _ default cases =>
      cases.foldr (fun (key, target) rest => .CTifeq key target rest) (.CTaction default)
    ifConversionHeuristic := fun _ _ _ _ _ _ => false }

def inlineCfg : Inlining.InliningConfig :=
  { enabled := false, functionsCalledOnce := false,
    inlineStatus := fun _ => .noinline, isStatic := fun _ => false }


def enumeration : Linearize.EnumerationService := fun source =>
  (PTree.elements source.fn_code).map Prod.fst


def spillOffset (register : Registers.reg) := z (2 * PArith.BinPos.Pos.to_nat register)

def scratchRegister (type : typ) (index : Nat) : mreg :=
  match type with
  | .Tfloat | .Tsingle =>
      match index with
      | 0 => .X0 | 1 => .X1 | 2 => .X2 | _ => .X3
  | _ =>
      match index with
      | 0 => .AX | 1 => .CX | 2 => .DX | _ => .SI

def spillRead (types : RTLtyping.regenv) (register : Registers.reg) (target : mreg) : LTL.instruction :=
  .Lgetstack .Local (spillOffset register) (types register) target

def spillWrite (types : RTLtyping.regenv) (register : Registers.reg) (source : mreg) : LTL.instruction :=
  .Lsetstack source .Local (spillOffset register) (types register)

def spillArguments (types : RTLtyping.regenv) (arguments : List Registers.reg) :
    LTL.bblock × List mreg :=
  let assigned := arguments.zipIdx.map fun (register, index) =>
    (register, scratchRegister (types register) index)
  (assigned.map (fun (register, target) => spillRead types register target), assigned.map Prod.snd)

def outgoingArgument (types : RTLtyping.regenv) (register : Registers.reg) : rpair loc → LTL.bblock
  | .One (.R target) => [spillRead types register target]
  | .One (.S slot offset type) =>
      let temporary := match type with
        | .Tfloat | .Tsingle => mreg.X15
        | _ => mreg.R11
      [spillRead types register temporary, .Lsetstack temporary slot offset type]
  | .Twolong _ _ => []

def incomingArgument (types : RTLtyping.regenv) (register : Registers.reg) : rpair loc → LTL.bblock
  | .One (.R source) => [spillWrite types register source]
  | .One (.S slot offset type) =>
      let temporary := match type with
        | .Tfloat | .Tsingle => mreg.X15
        | _ => mreg.R11
      [.Lgetstack slot offset type temporary, spillWrite types register temporary]
  | .Twolong _ _ => []

def prepareCall (configuration : Config.CompilerConfig) (types : RTLtyping.regenv)
    (sign : signature) (arguments : List Registers.reg) (target : Sum Registers.reg ident) :
    LTL.bblock × Sum mreg ident :=
  let setup := (arguments.zip (X86.Conventions1.loc_arguments configuration sign)).flatMap
    (fun (register, location) => outgoingArgument types register location)
  match target with
  | .inl register => (setup ++ [spillRead types register .R10], .inl .R10)
  | .inr identifier => (setup, .inr identifier)

def spillOperationResult (types : RTLtyping.regenv) (operation : operation)
    (destination : Registers.reg) : mreg :=
  match operation with
  | .Omulhs | .Omulhu | .Omod | .Omodu
  | .Omullhs | .Omullhu | .Omodl | .Omodlu => .DX
  | _ => scratchRegister (types destination) 0

def spillInstruction (configuration : Config.CompilerConfig) (types : RTLtyping.regenv)
    (returnSign : signature) : RTL.instruction → LTL.bblock
  | .Inop next => [.Lbranch next]
  | .Iop operation arguments destination next =>
      let (setup, registers) := spillArguments types arguments
      let result := spillOperationResult types operation destination
      List.append setup [.Lop operation registers result, spillWrite types destination result, .Lbranch next]
  | .Iload chunk address arguments destination next =>
      let (setup, registers) := spillArguments types arguments
      let result := scratchRegister (types destination) 0
      List.append setup [.Lload chunk address registers result, spillWrite types destination result, .Lbranch next]
  | .Istore chunk address arguments source next =>
      let (setup, registers) := spillArguments types arguments
      let value := scratchRegister (types source) 2
      List.append setup [spillRead types source value, .Lstore chunk address registers value, .Lbranch next]
  | .Icond condition arguments ifTrue ifFalse =>
      let (setup, registers) := spillArguments types arguments
      List.append setup [.Lcond condition registers ifTrue ifFalse]
  | .Ijumptable argument targets => [spillRead types argument .AX, .Ljumptable .AX targets]
  | .Ireturn none => [.Lreturn]
  | .Ireturn (some result) =>
      let target := match X86.Conventions1.loc_result returnSign with
        | .One register => register
        | .Twolong _ _ => mreg.AX
      [spillRead types result target, .Lreturn]
  | .Icall sign target arguments destination next =>
      let (setup, callee) := prepareCall configuration types sign arguments target
      let result := match X86.Conventions1.loc_result sign with
        | .One register => register
        | .Twolong _ _ => mreg.AX
      List.append setup [.Lcall sign callee, spillWrite types destination result, .Lbranch next]
  | .Itailcall sign target arguments =>
      let (setup, callee) := prepareCall configuration types sign arguments target
      List.append setup [.Ltailcall sign callee]
  | .Ibuiltin external arguments result next =>
      let registers := (params_of_builtin_args arguments).eraseDups
      let assigned := registers.zipIdx.map fun (register, index) =>
        (register, scratchRegister (types register) index)
      let setup := assigned.map fun (register, target) => spillRead types register target
      let mappedArgs := arguments.map (map_builtin_arg (fun register =>
        loc.R ((assigned.find? (fun pair => pair.1 == register)).map Prod.snd |>.getD .AX)))
      match result with
      | .BR destination =>
          let output := scratchRegister (types destination) 0
          setup ++ [.Lbuiltin external mappedArgs (.BR output), spillWrite types destination output, .Lbranch next]
      | .BR_none => setup ++ [.Lbuiltin external mappedArgs .BR_none, .Lbranch next]
      | .BR_splitlong _ _ => [.Lbranch next]

def spillAllocator (configuration : Config.CompilerConfig) : Allocation.RegallocOracle := fun source => do
  if (PTree.elements source.fn_code).any (fun (_, instruction) => match instruction with
      | .Ibuiltin _ arguments result _ =>
          (params_of_builtin_args arguments).eraseDups.length > 4 ||
            (match result with | .BR_splitlong _ _ => true | _ => false)
      | _ => false) then
    .Error [.MSG ("spill allocator: unsupported builtin register requirements".toUTF8.toList.foldr .String .EmptyString)]
  else do
  let types ← RTLtyping.type_function configuration source
  let entry := pos (1 + (PTree.elements source.fn_code).foldl
    (fun highest pair => max highest (PArith.BinPos.Pos.to_nat pair.1)) 0)
  let parameters := (source.fn_params.zip (Conventions.loc_parameters configuration source.fn_sig)).flatMap
    (fun (register, location) => incomingArgument types register location)
  .OK { fn_sig := source.fn_sig, fn_stacksize := source.fn_stacksize,
        fn_entrypoint := entry,
        fn_code := PTree.set entry (parameters ++ [.Lbranch source.fn_entrypoint])
          (PTree.map (fun _ instruction => spillInstruction configuration types source.fn_sig instruction)
            source.fn_code) }


end CompCert4Lean.Prototype
