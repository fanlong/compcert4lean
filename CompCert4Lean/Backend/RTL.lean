import CompCert4Lean.Backend.Registers
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.X86.Op

/-!
# Register transfer language

Definition-bearing translation of CompCert's `backend/RTL.v`.  The external-
call environment is threaded explicitly through the transition relation and
whole-program semantics, following the integrated Events API.  Proofs assigned
to later proof migration are represented by transparent proposition
descriptors.
-/

namespace CompCert4Lean.Backend.RTL

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

/-! ## Abstract syntax -/

def node : Type := positive

inductive instruction : Type where
  | Inop (succ : node)
  | Iop (op : operation) (args : List reg) (dest : reg) (succ : node)
  | Iload (chunk : memory_chunk) (addr : addressing) (args : List reg)
      (dest : reg) (succ : node)
  | Istore (chunk : memory_chunk) (addr : addressing) (args : List reg)
      (src : reg) (succ : node)
  | Icall (sig : signature) (fn : Sum reg ident) (args : List reg)
      (dest : reg) (succ : node)
  | Itailcall (sig : signature) (fn : Sum reg ident) (args : List reg)
  | Ibuiltin (ef : external_function) (args : List (builtin_arg reg))
      (dest : builtin_res reg) (succ : node)
  | Icond (cond : condition) (args : List reg) (ifso ifnot : node)
  | Ijumptable (arg : reg) (tbl : List node)
  | Ireturn (res : Option reg)

export instruction
  (Inop Iop Iload Istore Icall Itailcall Ibuiltin Icond Ijumptable Ireturn)

def code : Type := PTree.t instruction

structure function : Type where
  fn_sig : signature
  fn_params : List reg
  fn_stacksize : Z
  fn_code : code
  fn_entrypoint : node

export function (fn_sig fn_params fn_stacksize fn_code fn_entrypoint)

def fundef : Type := CompCert4Lean.Common.AST.fundef function

def program : Type := CompCert4Lean.Common.AST.program fundef Unit

def funsig : fundef → signature
  | .Internal f => f.fn_sig
  | .External ef => ef_sig ef

/-! ## Operational semantics -/

def genv : Type := Genv.t fundef Unit

def regset : Type := Regmap.t val

def init_regs : List val → List reg → regset
  | v :: vs, r :: rs => Regmap.set r v (init_regs vs rs)
  | _, _ => Regmap.init Vundef

inductive stackframe : Type where
  | Stackframe (res : reg) (f : function) (sp : val) (pc : node) (rs : regset)

export stackframe (Stackframe)

inductive state : Type where
  | State (stack : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem)
  | Callstate (stack : List stackframe) (f : fundef) (args : List val) (m : mem)
  | Returnstate (stack : List stackframe) (res : val) (m : mem)

export state (State Callstate Returnstate)

def find_function (ge : genv) (ros : Sum reg ident) (rs : regset) : Option fundef :=
  match ros with
  | .inl r => Genv.find_funct ge (Regmap.get r rs)
  | .inr symb =>
      match Genv.find_symbol ge symb with
      | none => none
      | some b => Genv.find_funct_ptr ge b

inductive step
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) : state → trace → state → Prop where
  | exec_Inop
      (s : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem) (pc' : node)
      (hcode : PTree.get pc f.fn_code = some (Inop pc')) :
      step xi ge (State s f sp pc rs m) E0 (State s f sp pc' rs m)
  | exec_Iop
      (s : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem) (op : operation) (args : List reg)
      (res : reg) (pc' : node) (v : val)
      (hcode : PTree.get pc f.fn_code = some (Iop op args res pc'))
      (heval : eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge sp op (args.map (fun r => Regmap.get r rs)) m = some v) :
      step xi ge (State s f sp pc rs m) E0
        (State s f sp pc' (Regmap.set res v rs) m)
  | exec_Iload
      (s : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem) (chunk : memory_chunk) (addr : addressing)
      (args : List reg) (dst : reg) (pc' : node) (a v : val)
      (hcode : PTree.get pc f.fn_code = some (Iload chunk addr args dst pc'))
      (haddr : eval_addressing ge sp addr (args.map (fun r => Regmap.get r rs)) = some a)
      (hload : Mem.loadv chunk m a = some v) :
      step xi ge (State s f sp pc rs m) E0
        (State s f sp pc' (Regmap.set dst v rs) m)
  | exec_Istore
      (s : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem) (chunk : memory_chunk) (addr : addressing)
      (args : List reg) (src : reg) (pc' : node) (a : val) (m' : mem)
      (hcode : PTree.get pc f.fn_code = some (Istore chunk addr args src pc'))
      (haddr : eval_addressing ge sp addr (args.map (fun r => Regmap.get r rs)) = some a)
      (hstore : Mem.storev chunk m a (Regmap.get src rs) = some m') :
      step xi ge (State s f sp pc rs m) E0 (State s f sp pc' rs m')
  | exec_Icall
      (s : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem) (sig : signature) (ros : Sum reg ident)
      (args : List reg) (res : reg) (pc' : node) (fd : fundef)
      (hcode : PTree.get pc f.fn_code = some (Icall sig ros args res pc'))
      (hfind : find_function ge ros rs = some fd)
      (hsig : funsig fd = sig) :
      step xi ge (State s f sp pc rs m) E0
        (Callstate (Stackframe res f sp pc' rs :: s) fd
          (args.map (fun r => Regmap.get r rs)) m)
  | exec_Itailcall
      (s : List stackframe) (f : function) (stk : block) (pc : node)
      (rs : regset) (m : mem) (sig : signature) (ros : Sum reg ident)
      (args : List reg) (fd : fundef) (m' : mem)
      (hcode : PTree.get pc f.fn_code = some (Itailcall sig ros args))
      (hfind : find_function ge ros rs = some fd)
      (hsig : funsig fd = sig)
      (hfree : Mem.free m stk .Z0 f.fn_stacksize = some m') :
      step xi ge (State s f (Vptr stk Ptrofs.zero) pc rs m) E0
        (Callstate s fd (args.map (fun r => Regmap.get r rs)) m')
  | exec_Ibuiltin
      (s : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem) (ef : external_function)
      (args : List (builtin_arg reg)) (res : builtin_res reg) (pc' : node)
      (vargs : List val) (t : trace) (vres : val) (m' : mem)
      (hcode : PTree.get pc f.fn_code = some (Ibuiltin ef args res pc'))
      (hargs : eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs)
        sp m args vargs)
      (hcall : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs m t vres m') :
      step xi ge (State s f sp pc rs m) t
        (State s f sp pc' (regmap_setres res vres rs) m')
  | exec_Icond
      (s : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem) (cond : condition) (args : List reg)
      (ifso ifnot : node) (b : Bool) (pc' : node)
      (hcode : PTree.get pc f.fn_code = some (Icond cond args ifso ifnot))
      (heval : eval_condition cond (args.map (fun r => Regmap.get r rs)) m = some b)
      (hpc : pc' = if b then ifso else ifnot) :
      step xi ge (State s f sp pc rs m) E0 (State s f sp pc' rs m)
  | exec_Ijumptable
      (s : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem) (arg : reg) (tbl : List node)
      (n : int) (pc' : node)
      (hcode : PTree.get pc f.fn_code = some (Ijumptable arg tbl))
      (harg : Regmap.get arg rs = Vint n)
      (hnth : list_nth_z tbl (Int.unsigned n) = some pc') :
      step xi ge (State s f sp pc rs m) E0 (State s f sp pc' rs m)
  | exec_Ireturn
      (s : List stackframe) (f : function) (stk : block) (pc : node)
      (rs : regset) (m : mem) (ores : Option reg) (m' : mem)
      (hcode : PTree.get pc f.fn_code = some (Ireturn ores))
      (hfree : Mem.free m stk .Z0 f.fn_stacksize = some m') :
      step xi ge (State s f (Vptr stk Ptrofs.zero) pc rs m) E0
        (Returnstate s (regmap_optget ores Vundef rs) m')
  | exec_function_internal
      (s : List stackframe) (f : function) (args : List val)
      (m m' : mem) (stk : block)
      (htypes : Val.has_argtype_list args f.fn_sig.sig_args)
      (halloc : Mem.alloc m .Z0 f.fn_stacksize = (m', stk)) :
      step xi ge (Callstate s (Internal f) args m) E0
        (State s f (Vptr stk Ptrofs.zero) f.fn_entrypoint
          (init_regs args f.fn_params) m')
  | exec_function_external
      (s : List stackframe) (ef : external_function) (args : List val)
      (res : val) (t : trace) (m m' : mem)
      (hcall : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) args m t res m') :
      step xi ge (Callstate s (External ef) args m) t (Returnstate s res m')
  | exec_return
      (res : reg) (f : function) (sp : val) (pc : node) (rs : regset)
      (s : List stackframe) (vres : val) (m : mem) :
      step xi ge (Returnstate (Stackframe res f sp pc rs :: s) vres m) E0
        (State s f sp pc (Regmap.set res vres rs) m)

export step
  (exec_Inop exec_Iop exec_Iload exec_Istore exec_Icall exec_Itailcall
    exec_Ibuiltin exec_Icond exec_Ijumptable exec_Ireturn
    exec_function_internal exec_function_external exec_return)

inductive initial_state (p : program) : state → Prop where
  | intro (b : block) (f : fundef) (m0 : mem)
      (hmem : Genv.init_mem p = some m0)
      (hsymb : Genv.find_symbol (Genv.globalenv p) p.prog_main = some b)
      (hfun : Genv.find_funct_ptr (Genv.globalenv p) b = some f)
      (hsig : funsig f = signature_main) :
      initial_state p (Callstate [] f [] m0)

inductive final_state : state → int → Prop where
  | intro (r : int) (m : mem) : final_state (Returnstate [] (Vint r) m) r

def semantics
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (p : program) :
    CompCert4Lean.Common.Smallstep.semantics :=
  Semantics
    (step (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi)
    (initial_state p)
    final_state
    (Genv.globalenv p)

/-! ## Operations on RTL syntax -/

def transf_function (transf : node → instruction → instruction)
    (f : function) : function :=
  { fn_sig := f.fn_sig
    fn_params := f.fn_params
    fn_stacksize := f.fn_stacksize
    fn_code := PTree.map transf f.fn_code
    fn_entrypoint := f.fn_entrypoint }

def successors_instr : instruction → List node
  | Inop s => [s]
  | Iop _ _ _ s => [s]
  | Iload _ _ _ _ s => [s]
  | Istore _ _ _ _ s => [s]
  | Icall _ _ _ _ s => [s]
  | Itailcall _ _ _ => []
  | Ibuiltin _ _ _ s => [s]
  | Icond _ _ ifso ifnot => [ifso, ifnot]
  | Ijumptable _ tbl => tbl
  | Ireturn _ => []

def successors_map (f : function) : PTree.t (List node) :=
  PTree.map1 successors_instr f.fn_code

def instr_uses : instruction → List reg
  | Inop _ => []
  | Iop _ args _ _ => args
  | Iload _ _ args _ _ => args
  | Istore _ _ args src _ => src :: args
  | Icall _ (.inl r) args _ _ => r :: args
  | Icall _ (.inr _) args _ _ => args
  | Itailcall _ (.inl r) args => r :: args
  | Itailcall _ (.inr _) args => args
  | Ibuiltin _ args _ _ => params_of_builtin_args args
  | Icond _ args _ _ => args
  | Ijumptable arg _ => [arg]
  | Ireturn none => []
  | Ireturn (some arg) => [arg]

def instr_defs : instruction → Option reg
  | Inop _ => none
  | Iop _ _ res _ => some res
  | Iload _ _ _ dst _ => some dst
  | Istore _ _ _ _ _ => none
  | Icall _ _ _ res _ => some res
  | Itailcall _ _ _ => none
  | Ibuiltin _ _ (.BR r) _ => some r
  | Ibuiltin _ _ _ _ => none
  | Icond _ _ _ _ => none
  | Ijumptable _ _ => none
  | Ireturn _ => none

def max_pc_function (f : function) : positive :=
  PTree.fold (fun m pc _ => PArith.BinPos.Pos.max m pc) f.fn_code .xH

def max_pc_function_soundStatement : Prop :=
  ∀ (f : function) (pc : node) (i : instruction),
    PTree.get pc f.fn_code = some i → Ple pc (max_pc_function f)

def max_reg_instr (m : positive) (_pc : node) : instruction → positive
  | Inop _ => m
  | Iop _ args res _ => args.foldl PArith.BinPos.Pos.max
      (PArith.BinPos.Pos.max res m)
  | Iload _ _ args dst _ => args.foldl PArith.BinPos.Pos.max
      (PArith.BinPos.Pos.max dst m)
  | Istore _ _ args src _ => args.foldl PArith.BinPos.Pos.max
      (PArith.BinPos.Pos.max src m)
  | Icall _ (.inl r) args res _ => args.foldl PArith.BinPos.Pos.max
      (PArith.BinPos.Pos.max r (PArith.BinPos.Pos.max res m))
  | Icall _ (.inr _) args res _ => args.foldl PArith.BinPos.Pos.max
      (PArith.BinPos.Pos.max res m)
  | Itailcall _ (.inl r) args => args.foldl PArith.BinPos.Pos.max
      (PArith.BinPos.Pos.max r m)
  | Itailcall _ (.inr _) args => args.foldl PArith.BinPos.Pos.max m
  | Ibuiltin _ args res _ =>
      (params_of_builtin_args args).foldl PArith.BinPos.Pos.max
        ((params_of_builtin_res res).foldl PArith.BinPos.Pos.max m)
  | Icond _ args _ _ => args.foldl PArith.BinPos.Pos.max m
  | Ijumptable arg _ => PArith.BinPos.Pos.max arg m
  | Ireturn none => m
  | Ireturn (some arg) => PArith.BinPos.Pos.max arg m

def max_reg_function (f : function) : positive :=
  PArith.BinPos.Pos.max
    (PTree.fold max_reg_instr f.fn_code .xH)
    (f.fn_params.foldl PArith.BinPos.Pos.max .xH)

def max_reg_instr_geStatement : Prop :=
  ∀ (m : positive) (pc : node) (i : instruction), Ple m (max_reg_instr m pc i)

def max_reg_instr_defStatement : Prop :=
  ∀ (m : positive) (pc : node) (i : instruction) (r : reg),
    instr_defs i = some r → Ple r (max_reg_instr m pc i)

def max_reg_function_defStatement : Prop :=
  ∀ (f : function) (pc : node) (i : instruction) (r : reg),
    PTree.get pc f.fn_code = some i →
    instr_defs i = some r →
    Ple r (max_reg_function f)

def max_reg_function_paramsStatement : Prop :=
  ∀ (f : function) (r : reg), r ∈ f.fn_params → Ple r (max_reg_function f)

def defmap : Type := PTree.t (globdef fundef Unit)

def is_known_runtime_function (dm : defmap) (ros : Sum reg ident) :
    Option builtin_function :=
  match ros with
  | .inl _ => none
  | .inr id =>
      match PTree.get id dm with
      | some (.Gfun (.External (.EF_runtime name sg))) =>
          lookup_builtin_function name sg
      | _ => none

def is_known_runtime_function_soundStatement : Prop :=
  ∀ (cu prog : program) (ros : Sum reg ident) (bf : builtin_function)
    (rs : regset) (fd : fundef),
    is_known_runtime_function (prog_defmap cu) ros = some bf →
    @linkorder program
      (@Linker_prog fundef Unit (@Linker_fundef function) Linker_unit)
      cu prog →
    find_function (Genv.globalenv prog) ros rs = some fd →
    ∃ name sg,
      fd = .External (.EF_runtime name sg) ∧
      lookup_builtin_function name sg = some bf

end CompCert4Lean.Backend.RTL
