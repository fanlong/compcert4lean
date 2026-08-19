import CompCert4Lean.Config
import CompCert4Lean.Driver.Compopts
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Backend.ValueDomain
import CompCert4Lean.Lib.Floats
import CompCert4Lean.Lib.Integers
import CompCert4Lean.X86.Op
import CompCert4Lean.X86.SelectOp
import CompCert4Lean.X86.ValueAOp
import CompCert4Lean.X86_64.Archi

/-!
# x86 constant-propagation operator reductions

Definition-bearing translation of `x86/ConstpropOp.v`.  The large dependent
case families are retained because they are part of the generated public
surface of the CompCert `.vp` input.
-/

namespace CompCert4Lean.X86.ConstpropOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Floats
open CompCert4Lean.X86.Op

private abbrev reg := CompCert4Lean.Backend.Registers.reg
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev float := CompCert4Lean.Lib.Floats.float
private abbrev float32 := CompCert4Lean.Lib.Floats.float32
private abbrev comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev typ := CompCert4Lean.Common.AST.typ
private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev RelocationContext := CompCert4Lean.X86.SelectOp.RelocationContext
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z

private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zOpp := ZArith.BinInt.Z.opp

private abbrev int64IsPower2 := CompCert4Lean.Lib.Integers.Int64.is_power2'

private def intIsPower2 (x : int) : Option int :=
  match CompCert4Lean.Lib.Zbits.Z_one_bits CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Lib.Integers.Int.unsigned x) Z0 with
  | [i] => some (CompCert4Lean.Lib.Integers.Int.repr i)
  | _ => none

private def defaultConfig : CompCert4Lean.Config.CompilerConfig :=
  { options :=
      { optimForSize := false
        propagateFloatConstants := false
        generateFloatConstants := false
        vaStrict := false
        optimTailcalls := false
        optimConstprop := false
        optimCSE := false
        optimRedundancy := false
        debug := false }
    x86_64ABI := .systemV }

def Olea_ptr (a : addressing) : operation :=
  if CompCert4Lean.X86_64.Archi.ptr64 then Oleal a else Olea a

def const_for_result (ctx : RelocationContext) (a : aval) : Option operation :=
  match a with
  | I n | IU n => some (Ointconst n)
  | L n => if CompCert4Lean.X86_64.Archi.ptr64 then some (Olongconst n) else none
  | F n => if CompCert4Lean.Driver.Compopts.generate_float_constants
      defaultConfig then some (Ofloatconst n) else none
  | FS n => if CompCert4Lean.Driver.Compopts.generate_float_constants
      defaultConfig then some (Osingleconst n) else none
  | Ptr (Gl id ofs) =>
      if CompCert4Lean.X86.SelectOp.symbol_is_relocatable ctx id then
        if CompCert4Lean.Lib.Integers.Ptrofs.eq ofs
            CompCert4Lean.Lib.Integers.Ptrofs.zero then some (Oindirectsymbol id) else none
      else some (Olea_ptr (Aglobal id ofs))
  | Ptr (Stk ofs) => some (Olea_ptr (Ainstack ofs))
  | _ => none

inductive cond_strength_reduction_cases : condition → List reg → List aval → Type where
  | cond_strength_reduction_case1 (c : comparison) (r1 r2 : reg) (n1 : int) (v2 : aval) :
      cond_strength_reduction_cases (.Ccomp c) [r1, r2] [I n1, v2]
  | cond_strength_reduction_case2 (c : comparison) (r1 r2 : reg) (v1 : aval) (n2 : int) :
      cond_strength_reduction_cases (.Ccomp c) [r1, r2] [v1, I n2]
  | cond_strength_reduction_case3 (c : comparison) (r1 r2 : reg) (n1 : int) (v2 : aval) :
      cond_strength_reduction_cases (.Ccompu c) [r1, r2] [I n1, v2]
  | cond_strength_reduction_case4 (c : comparison) (r1 r2 : reg) (v1 : aval) (n2 : int) :
      cond_strength_reduction_cases (.Ccompu c) [r1, r2] [v1, I n2]
  | cond_strength_reduction_case5 (c : comparison) (r1 r2 : reg) (n1 : int64) (v2 : aval) :
      cond_strength_reduction_cases (.Ccompl c) [r1, r2] [L n1, v2]
  | cond_strength_reduction_case6 (c : comparison) (r1 r2 : reg) (v1 : aval) (n2 : int64) :
      cond_strength_reduction_cases (.Ccompl c) [r1, r2] [v1, L n2]
  | cond_strength_reduction_case7 (c : comparison) (r1 r2 : reg) (n1 : int64) (v2 : aval) :
      cond_strength_reduction_cases (.Ccomplu c) [r1, r2] [L n1, v2]
  | cond_strength_reduction_case8 (c : comparison) (r1 r2 : reg) (v1 : aval) (n2 : int64) :
      cond_strength_reduction_cases (.Ccomplu c) [r1, r2] [v1, L n2]
  | cond_strength_reduction_default (cond : condition) (args : List reg) (vl : List aval) :
      cond_strength_reduction_cases cond args vl

export cond_strength_reduction_cases (cond_strength_reduction_case1
  cond_strength_reduction_case2 cond_strength_reduction_case3
  cond_strength_reduction_case4 cond_strength_reduction_case5
  cond_strength_reduction_case6 cond_strength_reduction_case7
  cond_strength_reduction_case8 cond_strength_reduction_default)

def cond_strength_reduction_match (cond : condition) (args : List reg) (vl : List aval) :
    cond_strength_reduction_cases cond args vl :=
  match cond, args, vl with
  | .Ccomp c, [r1, r2], [I n1, v2] => .cond_strength_reduction_case1 c r1 r2 n1 v2
  | .Ccomp c, [r1, r2], [v1, I n2] => .cond_strength_reduction_case2 c r1 r2 v1 n2
  | .Ccompu c, [r1, r2], [I n1, v2] => .cond_strength_reduction_case3 c r1 r2 n1 v2
  | .Ccompu c, [r1, r2], [v1, I n2] => .cond_strength_reduction_case4 c r1 r2 v1 n2
  | .Ccompl c, [r1, r2], [L n1, v2] => .cond_strength_reduction_case5 c r1 r2 n1 v2
  | .Ccompl c, [r1, r2], [v1, L n2] => .cond_strength_reduction_case6 c r1 r2 v1 n2
  | .Ccomplu c, [r1, r2], [L n1, v2] => .cond_strength_reduction_case7 c r1 r2 n1 v2
  | .Ccomplu c, [r1, r2], [v1, L n2] => .cond_strength_reduction_case8 c r1 r2 v1 n2
  | cond, args, vl => .cond_strength_reduction_default cond args vl

def cond_strength_reduction (cond : condition) (args : List reg) (vl : List aval) :
    condition × List reg :=
  match cond_strength_reduction_match cond args vl with
  | .cond_strength_reduction_case1 c _ r2 n1 _ => (.Ccompimm (swap_comparison c) n1, [r2])
  | .cond_strength_reduction_case2 c r1 _ _ n2 => (.Ccompimm c n2, [r1])
  | .cond_strength_reduction_case3 c _ r2 n1 _ => (.Ccompuimm (swap_comparison c) n1, [r2])
  | .cond_strength_reduction_case4 c r1 _ _ n2 => (.Ccompuimm c n2, [r1])
  | .cond_strength_reduction_case5 c _ r2 n1 _ => (.Ccomplimm (swap_comparison c) n1, [r2])
  | .cond_strength_reduction_case6 c r1 _ _ n2 => (.Ccomplimm c n2, [r1])
  | .cond_strength_reduction_case7 c _ r2 n1 _ => (.Ccompluimm (swap_comparison c) n1, [r2])
  | .cond_strength_reduction_case8 c r1 _ _ n2 => (.Ccompluimm c n2, [r1])
  | .cond_strength_reduction_default cond args _ => (cond, args)

def make_cmp_base (c : condition) (args : List reg) (vl : List aval) : operation × List reg :=
  let (c', args') := cond_strength_reduction c args vl
  (Ocmp c', args')

def make_cmp_imm_eq (c : condition) (args : List reg) (vl : List aval)
    (n : int) (r1 : reg) (v1 : aval) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.one && vincl v1 (Uns Ptop (zOfNat 1)) then (Omove, [r1])
  else if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero && vincl v1 (Uns Ptop (zOfNat 1)) then
    (Oxorimm CompCert4Lean.Lib.Integers.Int.one, [r1])
  else make_cmp_base c args vl

def make_cmp_imm_ne (c : condition) (args : List reg) (vl : List aval)
    (n : int) (r1 : reg) (v1 : aval) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero && vincl v1 (Uns Ptop (zOfNat 1)) then (Omove, [r1])
  else if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.one && vincl v1 (Uns Ptop (zOfNat 1)) then
    (Oxorimm CompCert4Lean.Lib.Integers.Int.one, [r1])
  else make_cmp_base c args vl

inductive make_cmp_cases : condition → List reg → List aval → Type where
  | make_cmp_case1 (n : int) (r1 : reg) (v1 : aval) :
      make_cmp_cases (.Ccompimm .Ceq n) [r1] [v1]
  | make_cmp_case2 (n : int) (r1 : reg) (v1 : aval) :
      make_cmp_cases (.Ccompimm .Cne n) [r1] [v1]
  | make_cmp_case3 (n : int) (r1 : reg) (v1 : aval) :
      make_cmp_cases (.Ccompuimm .Ceq n) [r1] [v1]
  | make_cmp_case4 (n : int) (r1 : reg) (v1 : aval) :
      make_cmp_cases (.Ccompuimm .Cne n) [r1] [v1]
  | make_cmp_default (c : condition) (args : List reg) (vl : List aval) :
      make_cmp_cases c args vl

export make_cmp_cases (make_cmp_case1 make_cmp_case2 make_cmp_case3 make_cmp_case4
  make_cmp_default)

def make_cmp_match (c : condition) (args : List reg) (vl : List aval) :
    make_cmp_cases c args vl :=
  match c, args, vl with
  | .Ccompimm .Ceq n, [r1], [v1] => .make_cmp_case1 n r1 v1
  | .Ccompimm .Cne n, [r1], [v1] => .make_cmp_case2 n r1 v1
  | .Ccompuimm .Ceq n, [r1], [v1] => .make_cmp_case3 n r1 v1
  | .Ccompuimm .Cne n, [r1], [v1] => .make_cmp_case4 n r1 v1
  | c, args, vl => .make_cmp_default c args vl

def make_cmp (c : condition) (args : List reg) (vl : List aval) : operation × List reg :=
  match make_cmp_match c args vl with
  | .make_cmp_case1 n r1 v1 =>
      make_cmp_imm_eq (.Ccompimm .Ceq n) [r1] [v1] n r1 v1
  | .make_cmp_case2 n r1 v1 =>
      make_cmp_imm_ne (.Ccompimm .Cne n) [r1] [v1] n r1 v1
  | .make_cmp_case3 n r1 v1 =>
      make_cmp_imm_eq (.Ccompuimm .Ceq n) [r1] [v1] n r1 v1
  | .make_cmp_case4 n r1 v1 =>
      make_cmp_imm_ne (.Ccompuimm .Cne n) [r1] [v1] n r1 v1
  | .make_cmp_default c args vl => make_cmp_base c args vl

def make_select (c : condition) (ty : typ) (r1 r2 : reg)
    (args : List reg) (vl : List aval) : operation × List reg :=
  match resolve_branch (CompCert4Lean.X86.ValueAOp.eval_static_condition defaultConfig c vl) with
  | some b => (Omove, [if b then r1 else r2])
  | none =>
      let (c', args') := cond_strength_reduction c args vl
      (Osel c' ty, r1 :: r2 :: args')

inductive addr_strength_reduction_32_generic_cases : addressing → List reg → List aval → Type where
  | addr_strength_reduction_32_generic_case1 (ofs : Z) (r1 r2 : reg) (n1 : int) (v2 : aval) :
      addr_strength_reduction_32_generic_cases (Aindexed2 ofs) [r1, r2] [I n1, v2]
  | addr_strength_reduction_32_generic_case2 (ofs : Z) (r1 r2 : reg) (v1 : aval) (n2 : int) :
      addr_strength_reduction_32_generic_cases (Aindexed2 ofs) [r1, r2] [v1, I n2]
  | addr_strength_reduction_32_generic_case3 (sc ofs : Z) (r1 r2 : reg) (v1 : aval) (n2 : int) :
      addr_strength_reduction_32_generic_cases (Aindexed2scaled sc ofs) [r1, r2] [v1, I n2]
  | addr_strength_reduction_32_generic_case4 (sc ofs : Z) (r1 r2 : reg) (n1 : int) (v2 : aval) :
      addr_strength_reduction_32_generic_cases (Aindexed2scaled sc ofs) [r1, r2] [I n1, v2]
  | addr_strength_reduction_32_generic_default (addr : addressing) (args : List reg) (vl : List aval) :
      addr_strength_reduction_32_generic_cases addr args vl

export addr_strength_reduction_32_generic_cases (addr_strength_reduction_32_generic_case1
  addr_strength_reduction_32_generic_case2 addr_strength_reduction_32_generic_case3
  addr_strength_reduction_32_generic_case4 addr_strength_reduction_32_generic_default)

def addr_strength_reduction_32_generic_match (addr : addressing) (args : List reg) (vl : List aval) :
    addr_strength_reduction_32_generic_cases addr args vl :=
  match addr, args, vl with
  | .Aindexed2 ofs, [r1, r2], [I n1, v2] => .addr_strength_reduction_32_generic_case1 ofs r1 r2 n1 v2
  | .Aindexed2 ofs, [r1, r2], [v1, I n2] => .addr_strength_reduction_32_generic_case2 ofs r1 r2 v1 n2
  | .Aindexed2scaled sc ofs, [r1, r2], [v1, I n2] => .addr_strength_reduction_32_generic_case3 sc ofs r1 r2 v1 n2
  | .Aindexed2scaled sc ofs, [r1, r2], [I n1, v2] => .addr_strength_reduction_32_generic_case4 sc ofs r1 r2 n1 v2
  | addr, args, vl => .addr_strength_reduction_32_generic_default addr args vl

def addr_strength_reduction_32_generic (addr : addressing) (args : List reg) (vl : List aval) :
    addressing × List reg :=
  match addr_strength_reduction_32_generic_match addr args vl with
  | .addr_strength_reduction_32_generic_case1 ofs _ r2 n1 _ =>
      (.Aindexed (zAdd (CompCert4Lean.Lib.Integers.Int.signed n1) ofs), [r2])
  | .addr_strength_reduction_32_generic_case2 ofs r1 _ _ n2 =>
      (.Aindexed (zAdd (CompCert4Lean.Lib.Integers.Int.signed n2) ofs), [r1])
  | .addr_strength_reduction_32_generic_case3 sc ofs r1 _ _ n2 =>
      (.Aindexed (zAdd (zMul (CompCert4Lean.Lib.Integers.Int.signed n2) sc) ofs), [r1])
  | .addr_strength_reduction_32_generic_case4 sc ofs _ r2 n1 _ =>
      (.Ascaled sc (zAdd (CompCert4Lean.Lib.Integers.Int.signed n1) ofs), [r2])
  | .addr_strength_reduction_32_generic_default addr args _ => (addr, args)

inductive addr_strength_reduction_32_cases : addressing → List reg → List aval → Type where
  | addr_strength_reduction_32_case1 (ofs : Z) (r1 : reg) (symb : ident) (n : ptrofs) :
      addr_strength_reduction_32_cases (Aindexed ofs) [r1] [Ptr (Gl symb n)]
  | addr_strength_reduction_32_case2 (ofs : Z) (r1 : reg) (n : ptrofs) :
      addr_strength_reduction_32_cases (Aindexed ofs) [r1] [Ptr (Stk n)]
  | addr_strength_reduction_32_case3 (ofs : Z) (r1 r2 : reg) (symb : ident) (n1 : ptrofs) (n2 : int) :
      addr_strength_reduction_32_cases (Aindexed2 ofs) [r1, r2] [Ptr (Gl symb n1), I n2]
  | addr_strength_reduction_32_case4 (ofs : Z) (r1 r2 : reg) (n1 : int) (symb : ident) (n2 : ptrofs) :
      addr_strength_reduction_32_cases (Aindexed2 ofs) [r1, r2] [I n1, Ptr (Gl symb n2)]
  | addr_strength_reduction_32_case5 (ofs : Z) (r1 r2 : reg) (n1 : ptrofs) (n2 : int) :
      addr_strength_reduction_32_cases (Aindexed2 ofs) [r1, r2] [Ptr (Stk n1), I n2]
  | addr_strength_reduction_32_case6 (ofs : Z) (r1 r2 : reg) (n1 : int) (n2 : ptrofs) :
      addr_strength_reduction_32_cases (Aindexed2 ofs) [r1, r2] [I n1, Ptr (Stk n2)]
  | addr_strength_reduction_32_case7 (ofs : Z) (r1 r2 : reg) (symb : ident) (n1 : ptrofs) (v2 : aval) :
      addr_strength_reduction_32_cases (Aindexed2 ofs) [r1, r2] [Ptr (Gl symb n1), v2]
  | addr_strength_reduction_32_case8 (ofs : Z) (r1 r2 : reg) (v1 : aval) (symb : ident) (n2 : ptrofs) :
      addr_strength_reduction_32_cases (Aindexed2 ofs) [r1, r2] [v1, Ptr (Gl symb n2)]
  | addr_strength_reduction_32_case9 (sc ofs : Z) (r1 r2 : reg) (symb : ident) (n1 : ptrofs) (n2 : int) :
      addr_strength_reduction_32_cases (Aindexed2scaled sc ofs) [r1, r2] [Ptr (Gl symb n1), I n2]
  | addr_strength_reduction_32_case10 (sc ofs : Z) (r1 r2 : reg) (symb : ident) (n1 : ptrofs) (v2 : aval) :
      addr_strength_reduction_32_cases (Aindexed2scaled sc ofs) [r1, r2] [Ptr (Gl symb n1), v2]
  | addr_strength_reduction_32_case11 (id : ident) (ofs : ptrofs) (r1 : reg) (n1 : int) :
      addr_strength_reduction_32_cases (Abased id ofs) [r1] [I n1]
  | addr_strength_reduction_32_case12 (sc : Z) (id : ident) (ofs : ptrofs) (r1 : reg) (n1 : int) :
      addr_strength_reduction_32_cases (Abasedscaled sc id ofs) [r1] [I n1]
  | addr_strength_reduction_32_default (addr : addressing) (args : List reg) (vl : List aval) :
      addr_strength_reduction_32_cases addr args vl

export addr_strength_reduction_32_cases (addr_strength_reduction_32_case1 addr_strength_reduction_32_case2
  addr_strength_reduction_32_case3 addr_strength_reduction_32_case4 addr_strength_reduction_32_case5
  addr_strength_reduction_32_case6 addr_strength_reduction_32_case7 addr_strength_reduction_32_case8
  addr_strength_reduction_32_case9 addr_strength_reduction_32_case10 addr_strength_reduction_32_case11
  addr_strength_reduction_32_case12 addr_strength_reduction_32_default)

def addr_strength_reduction_32_match (addr : addressing) (args : List reg) (vl : List aval) :
    addr_strength_reduction_32_cases addr args vl :=
  match addr, args, vl with
  | .Aindexed ofs, [r1], [Ptr (Gl symb n)] => .addr_strength_reduction_32_case1 ofs r1 symb n
  | .Aindexed ofs, [r1], [Ptr (Stk n)] => .addr_strength_reduction_32_case2 ofs r1 n
  | .Aindexed2 ofs, [r1, r2], [Ptr (Gl symb n1), I n2] => .addr_strength_reduction_32_case3 ofs r1 r2 symb n1 n2
  | .Aindexed2 ofs, [r1, r2], [I n1, Ptr (Gl symb n2)] => .addr_strength_reduction_32_case4 ofs r1 r2 n1 symb n2
  | .Aindexed2 ofs, [r1, r2], [Ptr (Stk n1), I n2] => .addr_strength_reduction_32_case5 ofs r1 r2 n1 n2
  | .Aindexed2 ofs, [r1, r2], [I n1, Ptr (Stk n2)] => .addr_strength_reduction_32_case6 ofs r1 r2 n1 n2
  | .Aindexed2 ofs, [r1, r2], [Ptr (Gl symb n1), v2] => .addr_strength_reduction_32_case7 ofs r1 r2 symb n1 v2
  | .Aindexed2 ofs, [r1, r2], [v1, Ptr (Gl symb n2)] => .addr_strength_reduction_32_case8 ofs r1 r2 v1 symb n2
  | .Aindexed2scaled sc ofs, [r1, r2], [Ptr (Gl symb n1), I n2] => .addr_strength_reduction_32_case9 sc ofs r1 r2 symb n1 n2
  | .Aindexed2scaled sc ofs, [r1, r2], [Ptr (Gl symb n1), v2] => .addr_strength_reduction_32_case10 sc ofs r1 r2 symb n1 v2
  | .Abased id ofs, [r1], [I n1] => .addr_strength_reduction_32_case11 id ofs r1 n1
  | .Abasedscaled sc id ofs, [r1], [I n1] => .addr_strength_reduction_32_case12 sc id ofs r1 n1
  | addr, args, vl => .addr_strength_reduction_32_default addr args vl

def addr_strength_reduction_32 (addr : addressing) (args : List reg) (vl : List aval) :
    addressing × List reg :=
  if CompCert4Lean.X86_64.Archi.ptr64 then addr_strength_reduction_32_generic addr args vl
  else
    match addr_strength_reduction_32_match addr args vl with
    | .addr_strength_reduction_32_case1 ofs _ symb n =>
        (.Aglobal symb (Ptrofs.add n (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_32_case2 ofs _ n =>
        (.Ainstack (Ptrofs.add n (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_32_case3 ofs _ _ symb n1 n2 =>
        (.Aglobal symb (Ptrofs.add (Ptrofs.add n1 (Ptrofs.of_int n2)) (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_32_case4 ofs _ _ n1 symb n2 =>
        (.Aglobal symb (Ptrofs.add (Ptrofs.add n2 (Ptrofs.of_int n1)) (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_32_case5 ofs _ _ n1 n2 =>
        (.Ainstack (Ptrofs.add (Ptrofs.add n1 (Ptrofs.of_int n2)) (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_32_case6 ofs _ _ n1 n2 =>
        (.Ainstack (Ptrofs.add (Ptrofs.add (Ptrofs.of_int n1) n2) (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_32_case7 ofs _ r2 symb n1 _ =>
        (.Abased symb (Ptrofs.add n1 (Ptrofs.repr ofs)), [r2])
    | .addr_strength_reduction_32_case8 ofs r1 _ _ symb n2 =>
        (.Abased symb (Ptrofs.add n2 (Ptrofs.repr ofs)), [r1])
    | .addr_strength_reduction_32_case9 sc ofs _ _ symb n1 n2 =>
        (.Aglobal symb (Ptrofs.add (Ptrofs.add n1
          (Ptrofs.of_int (CompCert4Lean.Lib.Integers.Int.mul n2 (CompCert4Lean.Lib.Integers.Int.repr sc)))) (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_32_case10 sc ofs _ r2 symb n1 _ =>
        (.Abasedscaled sc symb (Ptrofs.add n1 (Ptrofs.repr ofs)), [r2])
    | .addr_strength_reduction_32_case11 id ofs _ n1 =>
        (.Aglobal id (Ptrofs.add ofs (Ptrofs.of_int n1)), [])
    | .addr_strength_reduction_32_case12 sc id ofs _ n1 =>
        (.Aglobal id (Ptrofs.add ofs (Ptrofs.of_int (CompCert4Lean.Lib.Integers.Int.mul n1 (CompCert4Lean.Lib.Integers.Int.repr sc)))), [])
    | .addr_strength_reduction_32_default addr args vl => addr_strength_reduction_32_generic addr args vl

inductive addr_strength_reduction_64_generic_cases : addressing → List reg → List aval → Type where
  | addr_strength_reduction_64_generic_case1 (ofs : Z) (r1 r2 : reg) (n1 : int64) (v2 : aval) :
      addr_strength_reduction_64_generic_cases (Aindexed2 ofs) [r1, r2] [L n1, v2]
  | addr_strength_reduction_64_generic_case2 (ofs : Z) (r1 r2 : reg) (v1 : aval) (n2 : int64) :
      addr_strength_reduction_64_generic_cases (Aindexed2 ofs) [r1, r2] [v1, L n2]
  | addr_strength_reduction_64_generic_case3 (sc ofs : Z) (r1 r2 : reg) (v1 : aval) (n2 : int64) :
      addr_strength_reduction_64_generic_cases (Aindexed2scaled sc ofs) [r1, r2] [v1, L n2]
  | addr_strength_reduction_64_generic_case4 (sc ofs : Z) (r1 r2 : reg) (n1 : int64) (v2 : aval) :
      addr_strength_reduction_64_generic_cases (Aindexed2scaled sc ofs) [r1, r2] [L n1, v2]
  | addr_strength_reduction_64_generic_default (addr : addressing) (args : List reg) (vl : List aval) :
      addr_strength_reduction_64_generic_cases addr args vl

export addr_strength_reduction_64_generic_cases (addr_strength_reduction_64_generic_case1
  addr_strength_reduction_64_generic_case2 addr_strength_reduction_64_generic_case3
  addr_strength_reduction_64_generic_case4 addr_strength_reduction_64_generic_default)

def addr_strength_reduction_64_generic_match (addr : addressing) (args : List reg) (vl : List aval) :
    addr_strength_reduction_64_generic_cases addr args vl :=
  match addr, args, vl with
  | .Aindexed2 ofs, [r1, r2], [L n1, v2] => .addr_strength_reduction_64_generic_case1 ofs r1 r2 n1 v2
  | .Aindexed2 ofs, [r1, r2], [v1, L n2] => .addr_strength_reduction_64_generic_case2 ofs r1 r2 v1 n2
  | .Aindexed2scaled sc ofs, [r1, r2], [v1, L n2] => .addr_strength_reduction_64_generic_case3 sc ofs r1 r2 v1 n2
  | .Aindexed2scaled sc ofs, [r1, r2], [L n1, v2] => .addr_strength_reduction_64_generic_case4 sc ofs r1 r2 n1 v2
  | addr, args, vl => .addr_strength_reduction_64_generic_default addr args vl

def addr_strength_reduction_64_generic (addr : addressing) (args : List reg) (vl : List aval) :
    addressing × List reg :=
  match addr_strength_reduction_64_generic_match addr args vl with
  | .addr_strength_reduction_64_generic_case1 ofs _ r2 n1 _ =>
      (.Aindexed (zAdd (CompCert4Lean.Lib.Integers.Int64.signed n1) ofs), [r2])
  | .addr_strength_reduction_64_generic_case2 ofs r1 _ _ n2 =>
      (.Aindexed (zAdd (CompCert4Lean.Lib.Integers.Int64.signed n2) ofs), [r1])
  | .addr_strength_reduction_64_generic_case3 sc ofs r1 _ _ n2 =>
      (.Aindexed (zAdd (zMul (CompCert4Lean.Lib.Integers.Int64.signed n2) sc) ofs), [r1])
  | .addr_strength_reduction_64_generic_case4 sc ofs _ r2 n1 _ =>
      (.Ascaled sc (zAdd (CompCert4Lean.Lib.Integers.Int64.signed n1) ofs), [r2])
  | .addr_strength_reduction_64_generic_default addr args _ => (addr, args)

inductive addr_strength_reduction_64_cases : addressing → List reg → List aval → Type where
  | addr_strength_reduction_64_case1 (ofs : Z) (r1 : reg) (symb : ident) (n : ptrofs) :
      addr_strength_reduction_64_cases (Aindexed ofs) [r1] [Ptr (Gl symb n)]
  | addr_strength_reduction_64_case2 (ofs : Z) (r1 : reg) (n : ptrofs) :
      addr_strength_reduction_64_cases (Aindexed ofs) [r1] [Ptr (Stk n)]
  | addr_strength_reduction_64_case3 (ofs : Z) (r1 r2 : reg) (symb : ident) (n1 : ptrofs) (n2 : int64) :
      addr_strength_reduction_64_cases (Aindexed2 ofs) [r1, r2] [Ptr (Gl symb n1), L n2]
  | addr_strength_reduction_64_case4 (ofs : Z) (r1 r2 : reg) (n1 : int64) (symb : ident) (n2 : ptrofs) :
      addr_strength_reduction_64_cases (Aindexed2 ofs) [r1, r2] [L n1, Ptr (Gl symb n2)]
  | addr_strength_reduction_64_case5 (ofs : Z) (r1 r2 : reg) (n1 : ptrofs) (n2 : int64) :
      addr_strength_reduction_64_cases (Aindexed2 ofs) [r1, r2] [Ptr (Stk n1), L n2]
  | addr_strength_reduction_64_case6 (ofs : Z) (r1 r2 : reg) (n1 : int64) (n2 : ptrofs) :
      addr_strength_reduction_64_cases (Aindexed2 ofs) [r1, r2] [L n1, Ptr (Stk n2)]
  | addr_strength_reduction_64_case7 (sc ofs : Z) (r1 r2 : reg) (symb : ident) (n1 : ptrofs) (n2 : int64) :
      addr_strength_reduction_64_cases (Aindexed2scaled sc ofs) [r1, r2] [Ptr (Gl symb n1), L n2]
  | addr_strength_reduction_64_default (addr : addressing) (args : List reg) (vl : List aval) :
      addr_strength_reduction_64_cases addr args vl

export addr_strength_reduction_64_cases (addr_strength_reduction_64_case1 addr_strength_reduction_64_case2
  addr_strength_reduction_64_case3 addr_strength_reduction_64_case4 addr_strength_reduction_64_case5
  addr_strength_reduction_64_case6 addr_strength_reduction_64_case7 addr_strength_reduction_64_default)

def addr_strength_reduction_64_match (addr : addressing) (args : List reg) (vl : List aval) :
    addr_strength_reduction_64_cases addr args vl :=
  match addr, args, vl with
  | .Aindexed ofs, [r1], [Ptr (Gl symb n)] => .addr_strength_reduction_64_case1 ofs r1 symb n
  | .Aindexed ofs, [r1], [Ptr (Stk n)] => .addr_strength_reduction_64_case2 ofs r1 n
  | .Aindexed2 ofs, [r1, r2], [Ptr (Gl symb n1), L n2] => .addr_strength_reduction_64_case3 ofs r1 r2 symb n1 n2
  | .Aindexed2 ofs, [r1, r2], [L n1, Ptr (Gl symb n2)] => .addr_strength_reduction_64_case4 ofs r1 r2 n1 symb n2
  | .Aindexed2 ofs, [r1, r2], [Ptr (Stk n1), L n2] => .addr_strength_reduction_64_case5 ofs r1 r2 n1 n2
  | .Aindexed2 ofs, [r1, r2], [L n1, Ptr (Stk n2)] => .addr_strength_reduction_64_case6 ofs r1 r2 n1 n2
  | .Aindexed2scaled sc ofs, [r1, r2], [Ptr (Gl symb n1), L n2] => .addr_strength_reduction_64_case7 sc ofs r1 r2 symb n1 n2
  | addr, args, vl => .addr_strength_reduction_64_default addr args vl

def addr_strength_reduction_64 (addr : addressing) (args : List reg) (vl : List aval) :
    addressing × List reg :=
  if !CompCert4Lean.X86_64.Archi.ptr64 then addr_strength_reduction_64_generic addr args vl
  else
    match addr_strength_reduction_64_match addr args vl with
    | .addr_strength_reduction_64_case1 ofs _ symb n =>
        (.Aglobal symb (Ptrofs.add n (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_64_case2 ofs _ n =>
        (.Ainstack (Ptrofs.add n (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_64_case3 ofs _ _ symb n1 n2 =>
        (.Aglobal symb (Ptrofs.add (Ptrofs.add n1 (Ptrofs.of_int64 n2)) (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_64_case4 ofs _ _ n1 symb n2 =>
        (.Aglobal symb (Ptrofs.add (Ptrofs.add n2 (Ptrofs.of_int64 n1)) (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_64_case5 ofs _ _ n1 n2 =>
        (.Ainstack (Ptrofs.add (Ptrofs.add n1 (Ptrofs.of_int64 n2)) (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_64_case6 ofs _ _ n1 n2 =>
        (.Ainstack (Ptrofs.add (Ptrofs.add (Ptrofs.of_int64 n1) n2) (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_64_case7 sc ofs _ _ symb n1 n2 =>
        (.Aglobal symb (Ptrofs.add (Ptrofs.add n1
          (Ptrofs.of_int64 (CompCert4Lean.Lib.Integers.Int64.mul n2 (CompCert4Lean.Lib.Integers.Int64.repr sc)))) (Ptrofs.repr ofs)), [])
    | .addr_strength_reduction_64_default addr args vl => addr_strength_reduction_64_generic addr args vl

def addr_strength_reduction (addr : addressing) (args : List reg) (vl : List aval) :
    addressing × List reg :=
  let addr_args' := if CompCert4Lean.X86_64.Archi.ptr64
    then addr_strength_reduction_64 addr args vl
    else addr_strength_reduction_32 addr args vl
  if CompCert4Lean.X86.Op.addressing_valid addr_args'.1 then addr_args' else (addr, args)

def make_addimm (n : int) (r : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Omove, [r])
  else (Olea (Aindexed (CompCert4Lean.Lib.Integers.Int.signed n)), [r])

def make_shlimm (n : int) (r1 r2 : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Omove, [r1])
  else if CompCert4Lean.Lib.Integers.Int.ltu n CompCert4Lean.Lib.Integers.Int.iwordsize then (Oshlimm n, [r1])
  else (Oshl, [r1, r2])

def make_shrimm (n : int) (r1 r2 : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Omove, [r1])
  else if CompCert4Lean.Lib.Integers.Int.ltu n CompCert4Lean.Lib.Integers.Int.iwordsize then (Oshrimm n, [r1])
  else (Oshr, [r1, r2])

def make_shruimm (n : int) (r1 r2 : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Omove, [r1])
  else if CompCert4Lean.Lib.Integers.Int.ltu n CompCert4Lean.Lib.Integers.Int.iwordsize then (Oshruimm n, [r1])
  else (Oshru, [r1, r2])

def make_mulimm (n : int) (r : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Ointconst CompCert4Lean.Lib.Integers.Int.zero, [])
  else if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.one then (Omove, [r])
  else match intIsPower2 n with
    | some l => (Oshlimm l, [r])
    | none => (Omulimm n, [r])

def make_andimm (n : int) (r : reg) (a : aval) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Ointconst CompCert4Lean.Lib.Integers.Int.zero, [])
  else if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.mone then (Omove, [r])
  else if match a with
    | Uns _ m => CompCert4Lean.Lib.Integers.Int.eq
        (CompCert4Lean.Lib.Integers.Int.zero_ext m
          (CompCert4Lean.Lib.Integers.Int.not n)) CompCert4Lean.Lib.Integers.Int.zero
    | _ => false
  then (Omove, [r])
  else (Oandimm n, [r])

def make_orimm (n : int) (r : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Omove, [r])
  else if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.mone then (Ointconst CompCert4Lean.Lib.Integers.Int.mone, [])
  else (Oorimm n, [r])

def make_xorimm (n : int) (r : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Omove, [r])
  else if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.mone then (Onot, [r])
  else (Oxorimm n, [r])

def make_divimm (n : int) (r1 r2 : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.one then (Omove, [r1])
  else match intIsPower2 n with
    | some l => if CompCert4Lean.Lib.Integers.Int.ltu l (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 31)) then (Oshrximm l, [r1])
      else (Odiv, [r1, r2])
    | none => (Odiv, [r1, r2])

def make_divuimm (n : int) (r1 r2 : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.one then (Omove, [r1])
  else match intIsPower2 n with
    | some l => (Oshruimm l, [r1])
    | none => (Odivu, [r1, r2])

def make_moduimm (n : int) (r1 r2 : reg) : operation × List reg :=
  match intIsPower2 n with
  | some _ => (Oandimm (CompCert4Lean.Lib.Integers.Int.sub n CompCert4Lean.Lib.Integers.Int.one), [r1])
  | none => (Omodu, [r1, r2])

def make_addlimm (n : int64) (r : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int64.eq n CompCert4Lean.Lib.Integers.Int64.zero then (Omove, [r])
  else (Oleal (Aindexed (CompCert4Lean.Lib.Integers.Int64.signed n)), [r])

def make_shllimm (n : int) (r1 r2 : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Omove, [r1])
  else if CompCert4Lean.Lib.Integers.Int.ltu n CompCert4Lean.Lib.Integers.Int64.iwordsize' then (Oshllimm n, [r1])
  else (Oshll, [r1, r2])

def make_shrlimm (n : int) (r1 r2 : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Omove, [r1])
  else if CompCert4Lean.Lib.Integers.Int.ltu n CompCert4Lean.Lib.Integers.Int64.iwordsize' then (Oshrlimm n, [r1])
  else (Oshrl, [r1, r2])

def make_shrluimm (n : int) (r1 r2 : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then (Omove, [r1])
  else if CompCert4Lean.Lib.Integers.Int.ltu n CompCert4Lean.Lib.Integers.Int64.iwordsize' then (Oshrluimm n, [r1])
  else (Oshrlu, [r1, r2])

def make_mullimm (n : int64) (r : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int64.eq n CompCert4Lean.Lib.Integers.Int64.zero then (Olongconst CompCert4Lean.Lib.Integers.Int64.zero, [])
  else if CompCert4Lean.Lib.Integers.Int64.eq n CompCert4Lean.Lib.Integers.Int64.one then (Omove, [r])
  else match int64IsPower2 n with
    | some l => (Oshllimm l, [r])
    | none => (Omullimm n, [r])

def make_andlimm (n : int64) (r : reg) (_a : aval) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int64.eq n CompCert4Lean.Lib.Integers.Int64.zero then (Olongconst CompCert4Lean.Lib.Integers.Int64.zero, [])
  else if CompCert4Lean.Lib.Integers.Int64.eq n CompCert4Lean.Lib.Integers.Int64.mone then (Omove, [r])
  else (Oandlimm n, [r])

def make_orlimm (n : int64) (r : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int64.eq n CompCert4Lean.Lib.Integers.Int64.zero then (Omove, [r])
  else if CompCert4Lean.Lib.Integers.Int64.eq n CompCert4Lean.Lib.Integers.Int64.mone then (Olongconst CompCert4Lean.Lib.Integers.Int64.mone, [])
  else (Oorlimm n, [r])

def make_xorlimm (n : int64) (r : reg) : operation × List reg :=
  if CompCert4Lean.Lib.Integers.Int64.eq n CompCert4Lean.Lib.Integers.Int64.zero then (Omove, [r])
  else if CompCert4Lean.Lib.Integers.Int64.eq n CompCert4Lean.Lib.Integers.Int64.mone then (Onotl, [r])
  else (Oxorlimm n, [r])

def make_divlimm (n : int64) (r1 r2 : reg) : operation × List reg :=
  match int64IsPower2 n with
  | some l => if CompCert4Lean.Lib.Integers.Int.ltu l (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 63)) then (Oshrxlimm l, [r1])
    else (Odivl, [r1, r2])
  | none => (Odivl, [r1, r2])

def make_divluimm (n : int64) (r1 r2 : reg) : operation × List reg :=
  match int64IsPower2 n with
  | some l => (Oshrluimm l, [r1])
  | none => (Odivlu, [r1, r2])

def make_modluimm (n : int64) (r1 r2 : reg) : operation × List reg :=
  match int64IsPower2 n with
  | some _ => (Oandlimm (CompCert4Lean.Lib.Integers.Int64.sub n CompCert4Lean.Lib.Integers.Int64.one), [r1])
  | none => (Omodlu, [r1, r2])

def make_mulfimm (n : float) (r r1 r2 : reg) : operation × List reg :=
  if n = CompCert4Lean.Lib.Floats.Float.of_int (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2)) then
    (Oaddf, [r, r]) else (Omulf, [r1, r2])

def make_mulfsimm (n : float32) (r r1 r2 : reg) : operation × List reg :=
  if n = CompCert4Lean.Lib.Floats.Float32.of_int (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2)) then
    (Oaddfs, [r, r]) else (Omulfs, [r1, r2])

def make_cast8signed (r : reg) (a : aval) : operation × List reg :=
  if vincl a (Sgn Ptop (zOfNat 8)) then (Omove, [r]) else (Ocast8signed, [r])

def make_cast8unsigned (r : reg) (a : aval) : operation × List reg :=
  if vincl a (Uns Ptop (zOfNat 8)) then (Omove, [r]) else (Ocast8unsigned, [r])

def make_cast16signed (r : reg) (a : aval) : operation × List reg :=
  if vincl a (Sgn Ptop (zOfNat 16)) then (Omove, [r]) else (Ocast16signed, [r])

def make_cast16unsigned (r : reg) (a : aval) : operation × List reg :=
  if vincl a (Uns Ptop (zOfNat 16)) then (Omove, [r]) else (Ocast16unsigned, [r])

inductive op_strength_reduction_cases : operation → List reg → List aval → Type where
  | op_strength_reduction_case1 (r1 : reg) (v1 : aval) : op_strength_reduction_cases Ocast8signed [r1] [v1]
  | op_strength_reduction_case2 (r1 : reg) (v1 : aval) : op_strength_reduction_cases Ocast8unsigned [r1] [v1]
  | op_strength_reduction_case3 (r1 : reg) (v1 : aval) : op_strength_reduction_cases Ocast16signed [r1] [v1]
  | op_strength_reduction_case4 (r1 : reg) (v1 : aval) : op_strength_reduction_cases Ocast16unsigned [r1] [v1]
  | op_strength_reduction_case5 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Osub [r1, r2] [v1, I n2]
  | op_strength_reduction_case6 (r1 r2 : reg) (n1 : int) (v2 : aval) : op_strength_reduction_cases Omul [r1, r2] [I n1, v2]
  | op_strength_reduction_case7 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Omul [r1, r2] [v1, I n2]
  | op_strength_reduction_case8 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Odiv [r1, r2] [v1, I n2]
  | op_strength_reduction_case9 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Odivu [r1, r2] [v1, I n2]
  | op_strength_reduction_case10 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Omodu [r1, r2] [v1, I n2]
  | op_strength_reduction_case11 (r1 r2 : reg) (n1 : int) (v2 : aval) : op_strength_reduction_cases Oand [r1, r2] [I n1, v2]
  | op_strength_reduction_case12 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Oand [r1, r2] [v1, I n2]
  | op_strength_reduction_case13 (n : int) (r1 : reg) (v1 : aval) : op_strength_reduction_cases (Oandimm n) [r1] [v1]
  | op_strength_reduction_case14 (r1 r2 : reg) (n1 : int) (v2 : aval) : op_strength_reduction_cases Oor [r1, r2] [I n1, v2]
  | op_strength_reduction_case15 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Oor [r1, r2] [v1, I n2]
  | op_strength_reduction_case16 (r1 r2 : reg) (n1 : int) (v2 : aval) : op_strength_reduction_cases Oxor [r1, r2] [I n1, v2]
  | op_strength_reduction_case17 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Oxor [r1, r2] [v1, I n2]
  | op_strength_reduction_case18 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Oshl [r1, r2] [v1, I n2]
  | op_strength_reduction_case19 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Oshr [r1, r2] [v1, I n2]
  | op_strength_reduction_case20 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Oshru [r1, r2] [v1, I n2]
  | op_strength_reduction_case21 (addr : addressing) (args : List reg) (vl : List aval) : op_strength_reduction_cases (Olea addr) args vl
  | op_strength_reduction_case22 (r1 r2 : reg) (v1 : aval) (n2 : int64) : op_strength_reduction_cases Osubl [r1, r2] [v1, L n2]
  | op_strength_reduction_case23 (r1 r2 : reg) (n1 : int64) (v2 : aval) : op_strength_reduction_cases Omull [r1, r2] [L n1, v2]
  | op_strength_reduction_case24 (r1 r2 : reg) (v1 : aval) (n2 : int64) : op_strength_reduction_cases Omull [r1, r2] [v1, L n2]
  | op_strength_reduction_case25 (r1 r2 : reg) (v1 : aval) (n2 : int64) : op_strength_reduction_cases Odivl [r1, r2] [v1, L n2]
  | op_strength_reduction_case26 (r1 r2 : reg) (v1 : aval) (n2 : int64) : op_strength_reduction_cases Odivlu [r1, r2] [v1, L n2]
  | op_strength_reduction_case27 (r1 r2 : reg) (v1 : aval) (n2 : int64) : op_strength_reduction_cases Omodlu [r1, r2] [v1, L n2]
  | op_strength_reduction_case28 (r1 r2 : reg) (n1 : int64) (v2 : aval) : op_strength_reduction_cases Oandl [r1, r2] [L n1, v2]
  | op_strength_reduction_case29 (r1 r2 : reg) (v1 : aval) (n2 : int64) : op_strength_reduction_cases Oandl [r1, r2] [v1, L n2]
  | op_strength_reduction_case30 (n : int64) (r1 : reg) (v1 : aval) : op_strength_reduction_cases (Oandlimm n) [r1] [v1]
  | op_strength_reduction_case31 (r1 r2 : reg) (n1 : int64) (v2 : aval) : op_strength_reduction_cases Oorl [r1, r2] [L n1, v2]
  | op_strength_reduction_case32 (r1 r2 : reg) (v1 : aval) (n2 : int64) : op_strength_reduction_cases Oorl [r1, r2] [v1, L n2]
  | op_strength_reduction_case33 (r1 r2 : reg) (n1 : int64) (v2 : aval) : op_strength_reduction_cases Oxorl [r1, r2] [L n1, v2]
  | op_strength_reduction_case34 (r1 r2 : reg) (v1 : aval) (n2 : int64) : op_strength_reduction_cases Oxorl [r1, r2] [v1, L n2]
  | op_strength_reduction_case35 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Oshll [r1, r2] [v1, I n2]
  | op_strength_reduction_case36 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Oshrl [r1, r2] [v1, I n2]
  | op_strength_reduction_case37 (r1 r2 : reg) (v1 : aval) (n2 : int) : op_strength_reduction_cases Oshrlu [r1, r2] [v1, I n2]
  | op_strength_reduction_case38 (addr : addressing) (args : List reg) (vl : List aval) : op_strength_reduction_cases (Oleal addr) args vl
  | op_strength_reduction_case39 (c : condition) (args : List reg) (vl : List aval) : op_strength_reduction_cases (Ocmp c) args vl
  | op_strength_reduction_case40 (c : condition) (ty : typ) (r1 r2 : reg) (args : List reg) (v1 v2 : aval) (vl : List aval) : op_strength_reduction_cases (Osel c ty) (r1 :: r2 :: args) (v1 :: v2 :: vl)
  | op_strength_reduction_case41 (r1 r2 : reg) (v1 : aval) (n2 : float) : op_strength_reduction_cases Omulf [r1, r2] [v1, F n2]
  | op_strength_reduction_case42 (r1 r2 : reg) (n1 : float) (v2 : aval) : op_strength_reduction_cases Omulf [r1, r2] [F n1, v2]
  | op_strength_reduction_case43 (r1 r2 : reg) (v1 : aval) (n2 : float32) : op_strength_reduction_cases Omulfs [r1, r2] [v1, FS n2]
  | op_strength_reduction_case44 (r1 r2 : reg) (n1 : float32) (v2 : aval) : op_strength_reduction_cases Omulfs [r1, r2] [FS n1, v2]
  | op_strength_reduction_default (op : operation) (args : List reg) (vl : List aval) : op_strength_reduction_cases op args vl

export op_strength_reduction_cases (op_strength_reduction_case1 op_strength_reduction_case2
  op_strength_reduction_case3 op_strength_reduction_case4 op_strength_reduction_case5
  op_strength_reduction_case6 op_strength_reduction_case7 op_strength_reduction_case8
  op_strength_reduction_case9 op_strength_reduction_case10 op_strength_reduction_case11
  op_strength_reduction_case12 op_strength_reduction_case13 op_strength_reduction_case14
  op_strength_reduction_case15 op_strength_reduction_case16 op_strength_reduction_case17
  op_strength_reduction_case18 op_strength_reduction_case19 op_strength_reduction_case20
  op_strength_reduction_case21 op_strength_reduction_case22 op_strength_reduction_case23
  op_strength_reduction_case24 op_strength_reduction_case25 op_strength_reduction_case26
  op_strength_reduction_case27 op_strength_reduction_case28 op_strength_reduction_case29
  op_strength_reduction_case30 op_strength_reduction_case31 op_strength_reduction_case32
  op_strength_reduction_case33 op_strength_reduction_case34 op_strength_reduction_case35
  op_strength_reduction_case36 op_strength_reduction_case37 op_strength_reduction_case38
  op_strength_reduction_case39 op_strength_reduction_case40 op_strength_reduction_case41
  op_strength_reduction_case42 op_strength_reduction_case43 op_strength_reduction_case44
  op_strength_reduction_default)

def op_strength_reduction_match (op : operation) (args : List reg) (vl : List aval) :
    op_strength_reduction_cases op args vl :=
  match op, args, vl with
  | Ocast8signed, [r1], [v1] => .op_strength_reduction_case1 r1 v1
  | Ocast8unsigned, [r1], [v1] => .op_strength_reduction_case2 r1 v1
  | Ocast16signed, [r1], [v1] => .op_strength_reduction_case3 r1 v1
  | Ocast16unsigned, [r1], [v1] => .op_strength_reduction_case4 r1 v1
  | Osub, [r1, r2], [v1, I n2] => .op_strength_reduction_case5 r1 r2 v1 n2
  | Omul, [r1, r2], [I n1, v2] => .op_strength_reduction_case6 r1 r2 n1 v2
  | Omul, [r1, r2], [v1, I n2] => .op_strength_reduction_case7 r1 r2 v1 n2
  | Odiv, [r1, r2], [v1, I n2] => .op_strength_reduction_case8 r1 r2 v1 n2
  | Odivu, [r1, r2], [v1, I n2] => .op_strength_reduction_case9 r1 r2 v1 n2
  | Omodu, [r1, r2], [v1, I n2] => .op_strength_reduction_case10 r1 r2 v1 n2
  | Oand, [r1, r2], [I n1, v2] => .op_strength_reduction_case11 r1 r2 n1 v2
  | Oand, [r1, r2], [v1, I n2] => .op_strength_reduction_case12 r1 r2 v1 n2
  | Oandimm n, [r1], [v1] => .op_strength_reduction_case13 n r1 v1
  | Oor, [r1, r2], [I n1, v2] => .op_strength_reduction_case14 r1 r2 n1 v2
  | Oor, [r1, r2], [v1, I n2] => .op_strength_reduction_case15 r1 r2 v1 n2
  | Oxor, [r1, r2], [I n1, v2] => .op_strength_reduction_case16 r1 r2 n1 v2
  | Oxor, [r1, r2], [v1, I n2] => .op_strength_reduction_case17 r1 r2 v1 n2
  | Oshl, [r1, r2], [v1, I n2] => .op_strength_reduction_case18 r1 r2 v1 n2
  | Oshr, [r1, r2], [v1, I n2] => .op_strength_reduction_case19 r1 r2 v1 n2
  | Oshru, [r1, r2], [v1, I n2] => .op_strength_reduction_case20 r1 r2 v1 n2
  | Olea addr, args, vl => .op_strength_reduction_case21 addr args vl
  | Osubl, [r1, r2], [v1, L n2] => .op_strength_reduction_case22 r1 r2 v1 n2
  | Omull, [r1, r2], [L n1, v2] => .op_strength_reduction_case23 r1 r2 n1 v2
  | Omull, [r1, r2], [v1, L n2] => .op_strength_reduction_case24 r1 r2 v1 n2
  | Odivl, [r1, r2], [v1, L n2] => .op_strength_reduction_case25 r1 r2 v1 n2
  | Odivlu, [r1, r2], [v1, L n2] => .op_strength_reduction_case26 r1 r2 v1 n2
  | Omodlu, [r1, r2], [v1, L n2] => .op_strength_reduction_case27 r1 r2 v1 n2
  | Oandl, [r1, r2], [L n1, v2] => .op_strength_reduction_case28 r1 r2 n1 v2
  | Oandl, [r1, r2], [v1, L n2] => .op_strength_reduction_case29 r1 r2 v1 n2
  | Oandlimm n, [r1], [v1] => .op_strength_reduction_case30 n r1 v1
  | Oorl, [r1, r2], [L n1, v2] => .op_strength_reduction_case31 r1 r2 n1 v2
  | Oorl, [r1, r2], [v1, L n2] => .op_strength_reduction_case32 r1 r2 v1 n2
  | Oxorl, [r1, r2], [L n1, v2] => .op_strength_reduction_case33 r1 r2 n1 v2
  | Oxorl, [r1, r2], [v1, L n2] => .op_strength_reduction_case34 r1 r2 v1 n2
  | Oshll, [r1, r2], [v1, I n2] => .op_strength_reduction_case35 r1 r2 v1 n2
  | Oshrl, [r1, r2], [v1, I n2] => .op_strength_reduction_case36 r1 r2 v1 n2
  | Oshrlu, [r1, r2], [v1, I n2] => .op_strength_reduction_case37 r1 r2 v1 n2
  | Oleal addr, args, vl => .op_strength_reduction_case38 addr args vl
  | Ocmp c, args, vl => .op_strength_reduction_case39 c args vl
  | Osel c ty, r1 :: r2 :: args, v1 :: v2 :: vl => .op_strength_reduction_case40 c ty r1 r2 args v1 v2 vl
  | Omulf, [r1, r2], [v1, F n2] => .op_strength_reduction_case41 r1 r2 v1 n2
  | Omulf, [r1, r2], [F n1, v2] => .op_strength_reduction_case42 r1 r2 n1 v2
  | Omulfs, [r1, r2], [v1, FS n2] => .op_strength_reduction_case43 r1 r2 v1 n2
  | Omulfs, [r1, r2], [FS n1, v2] => .op_strength_reduction_case44 r1 r2 n1 v2
  | op, args, vl => .op_strength_reduction_default op args vl

def op_strength_reduction (op : operation) (args : List reg) (vl : List aval) :
    operation × List reg :=
  match op_strength_reduction_match op args vl with
  | .op_strength_reduction_case1 r1 v1 => make_cast8signed r1 v1
  | .op_strength_reduction_case2 r1 v1 => make_cast8unsigned r1 v1
  | .op_strength_reduction_case3 r1 v1 => make_cast16signed r1 v1
  | .op_strength_reduction_case4 r1 v1 => make_cast16unsigned r1 v1
  | .op_strength_reduction_case5 r1 _ _ n2 => make_addimm (CompCert4Lean.Lib.Integers.Int.neg n2) r1
  | .op_strength_reduction_case6 _ r2 n1 _ => make_mulimm n1 r2
  | .op_strength_reduction_case7 r1 _ _ n2 => make_mulimm n2 r1
  | .op_strength_reduction_case8 r1 r2 _ n2 => make_divimm n2 r1 r2
  | .op_strength_reduction_case9 r1 r2 _ n2 => make_divuimm n2 r1 r2
  | .op_strength_reduction_case10 r1 r2 _ n2 => make_moduimm n2 r1 r2
  | .op_strength_reduction_case11 _ r2 n1 v2 => make_andimm n1 r2 v2
  | .op_strength_reduction_case12 r1 _ v1 n2 => make_andimm n2 r1 v1
  | .op_strength_reduction_case13 n r1 v1 => make_andimm n r1 v1
  | .op_strength_reduction_case14 _ r2 n1 _ => make_orimm n1 r2
  | .op_strength_reduction_case15 r1 _ _ n2 => make_orimm n2 r1
  | .op_strength_reduction_case16 _ r2 n1 _ => make_xorimm n1 r2
  | .op_strength_reduction_case17 r1 _ _ n2 => make_xorimm n2 r1
  | .op_strength_reduction_case18 r1 r2 _ n2 => make_shlimm n2 r1 r2
  | .op_strength_reduction_case19 r1 r2 _ n2 => make_shrimm n2 r1 r2
  | .op_strength_reduction_case20 r1 r2 _ n2 => make_shruimm n2 r1 r2
  | .op_strength_reduction_case21 addr args vl =>
      let (addr', args') := addr_strength_reduction_32 addr args vl
      (Olea addr', args')
  | .op_strength_reduction_case22 r1 _ _ n2 => make_addlimm (CompCert4Lean.Lib.Integers.Int64.neg n2) r1
  | .op_strength_reduction_case23 _ r2 n1 _ => make_mullimm n1 r2
  | .op_strength_reduction_case24 r1 _ _ n2 => make_mullimm n2 r1
  | .op_strength_reduction_case25 r1 r2 _ n2 => make_divlimm n2 r1 r2
  | .op_strength_reduction_case26 r1 r2 _ n2 => make_divluimm n2 r1 r2
  | .op_strength_reduction_case27 r1 r2 _ n2 => make_modluimm n2 r1 r2
  | .op_strength_reduction_case28 _ r2 n1 v2 => make_andlimm n1 r2 v2
  | .op_strength_reduction_case29 r1 _ v1 n2 => make_andlimm n2 r1 v1
  | .op_strength_reduction_case30 n r1 v1 => make_andlimm n r1 v1
  | .op_strength_reduction_case31 _ r2 n1 _ => make_orlimm n1 r2
  | .op_strength_reduction_case32 r1 _ _ n2 => make_orlimm n2 r1
  | .op_strength_reduction_case33 _ r2 n1 _ => make_xorlimm n1 r2
  | .op_strength_reduction_case34 r1 _ _ n2 => make_xorlimm n2 r1
  | .op_strength_reduction_case35 r1 r2 _ n2 => make_shllimm n2 r1 r2
  | .op_strength_reduction_case36 r1 r2 _ n2 => make_shrlimm n2 r1 r2
  | .op_strength_reduction_case37 r1 r2 _ n2 => make_shrluimm n2 r1 r2
  | .op_strength_reduction_case38 addr args vl =>
      let (addr', args') := addr_strength_reduction_64 addr args vl
      (Oleal addr', args')
  | .op_strength_reduction_case39 c args vl => make_cmp c args vl
  | .op_strength_reduction_case40 c ty r1 r2 args _ _ vl =>
      make_select c ty r1 r2 args vl
  | .op_strength_reduction_case41 r1 r2 _ n2 => make_mulfimm n2 r1 r1 r2
  | .op_strength_reduction_case42 r1 r2 n1 _ => make_mulfimm n1 r2 r1 r2
  | .op_strength_reduction_case43 r1 r2 _ n2 => make_mulfsimm n2 r1 r1 r2
  | .op_strength_reduction_case44 r1 r2 n1 _ => make_mulfsimm n1 r2 r1 r2
  | .op_strength_reduction_default op args _ => (op, args)

end CompCert4Lean.X86.ConstpropOp
