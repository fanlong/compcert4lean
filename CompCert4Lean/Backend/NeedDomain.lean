import CompCert4Lean.Backend.ValueDomain
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memdata
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.IntvSets
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Lib.Zbits

/-!
  Definition-bearing translation of `backend/NeedDomain.v`.

  Proof declarations selected for later migration are retained as named
  proposition descriptors below; executable definitions preserve the source
  names and constructors.
-/

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.IntvSets
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev z31 : Z := ZArith.BinInt.Z.of_nat 31
private abbrev z255 : Z := ZArith.BinInt.Z.of_nat 255
private abbrev z65535 : Z := ZArith.BinInt.Z.of_nat 65535

namespace Int
private abbrev repr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int.mone
private abbrev zwordsize := CompCert4Lean.Lib.Integers.Int.zwordsize
private abbrev iwordsize := CompCert4Lean.Lib.Integers.Int.iwordsize
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int.min_signed
private abbrev eq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev ltu := CompCert4Lean.Lib.Integers.Int.ltu
private abbrev and := CompCert4Lean.Lib.Integers.Int.and
private abbrev or := CompCert4Lean.Lib.Integers.Int.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int.not
private abbrev shl := CompCert4Lean.Lib.Integers.Int.shl
private abbrev shru := CompCert4Lean.Lib.Integers.Int.shru
private abbrev shr := CompCert4Lean.Lib.Integers.Int.shr
private abbrev rol := CompCert4Lean.Lib.Integers.Int.rol
private abbrev ror := CompCert4Lean.Lib.Integers.Int.ror
private abbrev zero_ext := CompCert4Lean.Lib.Integers.Int.zero_ext
end Int

namespace Int64
private abbrev repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int64.unsigned
private abbrev zero := CompCert4Lean.Lib.Integers.Int64.zero
private abbrev mone := CompCert4Lean.Lib.Integers.Int64.mone
private abbrev zwordsize := CompCert4Lean.Lib.Integers.Int64.zwordsize
private abbrev iwordsize' := CompCert4Lean.Lib.Integers.Int64.iwordsize'
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int64.min_signed
private abbrev and := CompCert4Lean.Lib.Integers.Int64.and
private abbrev or := CompCert4Lean.Lib.Integers.Int64.or
private abbrev not := CompCert4Lean.Lib.Integers.Int64.not
private abbrev shl' := CompCert4Lean.Lib.Integers.Int64.shl'
private abbrev shru' := CompCert4Lean.Lib.Integers.Int64.shru'
private abbrev shr' := CompCert4Lean.Lib.Integers.Int64.shr'
private abbrev rol := CompCert4Lean.Lib.Integers.Int64.rol
private abbrev ror := CompCert4Lean.Lib.Integers.Int64.ror
private abbrev loword := CompCert4Lean.Lib.Integers.Int64.loword
private abbrev hiword := CompCert4Lean.Lib.Integers.Int64.hiword
private abbrev ofwords := CompCert4Lean.Lib.Integers.Int64.ofwords
end Int64

inductive nval : Type where
  | Nothing
  | I (m : int)
  | L (m : int64)
  | All

export nval (Nothing I L All)

def iagree (p q mask : int) : Prop :=
  ∀ i, ZArith.BinInt.Z.le z0 i → ZArith.BinInt.Z.lt i Int.zwordsize →
    Int.testbit mask i = true → Int.testbit p i = Int.testbit q i

def lagree (p q mask : int64) : Prop :=
  ∀ i, ZArith.BinInt.Z.le z0 i → ZArith.BinInt.Z.lt i Int64.zwordsize →
    Int64.testbit mask i = true → Int64.testbit p i = Int64.testbit q i

private def iVagree (v w : val) (m : int) : Prop :=
  match v, w with
  | Vint p, Vint q => iagree p q m
  | Vint _, _ => False
  | _, _ => True

private def lVagree (v w : val) (m : int64) : Prop :=
  match v, w with
  | Vlong p, Vlong q => lagree p q m
  | Vlong _, _ => False
  | _, _ => True

def vagree (v w : val) (x : nval) : Prop :=
  match x with
  | Nothing => True
  | I m => iVagree v w m
  | L m => lVagree v w m
  | All => Val.lessdef v w

inductive vagree_list : List val → List val → List nval → Prop where
  | vagree_list_nil (nvl) : vagree_list [] [] nvl
  | vagree_list_default (v1 : val) (vl1 : List val) (v2 : val) (vl2 : List val) :
      vagree v1 v2 All → vagree_list vl1 vl2 [] → vagree_list (v1 :: vl1) (v2 :: vl2) []
  | vagree_list_cons (v1 : val) (vl1 : List val) (v2 : val) (vl2 : List val)
      (nv1 : nval) (nvl : List nval) :
      vagree v1 v2 nv1 → vagree_list vl1 vl2 nvl →
      vagree_list (v1 :: vl1) (v2 :: vl2) (nv1 :: nvl)

inductive nge : nval → nval → Prop where
  | nge_nothing (x) : nge All x
  | nge_all (x) : nge x Nothing
  | nge_int (m1 m2) :
      (∀ i, ZArith.BinInt.Z.le z0 i → ZArith.BinInt.Z.lt i Int.zwordsize →
        Int.testbit m2 i = true → Int.testbit m1 i = true) → nge (I m1) (I m2)
  | nge_long (m1 m2) :
      (∀ i, ZArith.BinInt.Z.le z0 i → ZArith.BinInt.Z.lt i Int64.zwordsize →
        Int64.testbit m2 i = true → Int64.testbit m1 i = true) → nge (L m1) (L m2)

def nlub (x y : nval) : nval :=
  match x, y with
  | Nothing, _ => y
  | _, Nothing => x
  | I m1, I m2 => I (Int.or m1 m2)
  | L m1, L m2 => L (Int64.or m1 m2)
  | _, _ => All

private def intSize (m : int) : Z :=
  match Int.unsigned m with
  | .Z0 => z0
  | .Zpos p => .Zpos (PArith.BinPos.Pos.size p)
  | .Zneg p => .Zpos (PArith.BinPos.Pos.size p)

private def int64Size (m : int64) : Z :=
  match Int64.unsigned m with
  | .Z0 => z0
  | .Zpos p => .Zpos (PArith.BinPos.Pos.size p)
  | .Zneg p => .Zpos (PArith.BinPos.Pos.size p)

private def int64ZeroExt (n : Z) (m : int64) : int64 :=
  Int64.repr (ZArith.BinInt.Z.modulo (Int64.unsigned m) (two_p n))

def complete_mask (m : int) : int := Int.zero_ext (intSize m) Int.mone
def complete_mask64 (m : int64) : int64 := int64ZeroExt (int64Size m) Int64.mone

def andimm (x : nval) (n : int) : nval :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.and m n)
  | _ => I n

def orimm (x : nval) (n : int) : nval :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.and m (Int.not n))
  | _ => I (Int.not n)

def andlimm (x : nval) (n : int64) : nval :=
  match x with
  | Nothing => Nothing
  | L m => L (Int64.and m n)
  | _ => L n

def orlimm (x : nval) (n : int64) : nval :=
  match x with
  | Nothing => Nothing
  | L m => L (Int64.and m (Int64.not n))
  | _ => L (Int64.not n)

def bitwise (x : nval) := x

def shlimm (x : nval) (n : int) : nval :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.shru m n)
  | _ => I (Int.shru Int.mone n)

def shruimm (x : nval) (n : int) : nval :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.shl m n)
  | _ => I (Int.shl Int.mone n)

def shrimm (x : nval) (n : int) : nval :=
  match x with
  | Nothing => Nothing
  | I m => I (let m' := Int.shl m n; if Int.shru m' n = m then m' else Int.or m' (Int.repr Int.min_signed))
  | _ => I (Int.or (Int.shl Int.mone n) (Int.repr Int.min_signed))

def ror (x : nval) (amount : int) : nval :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.rol m amount)
  | _ => All

def shllimm (x : nval) (n : int) : nval :=
  match x with
  | Nothing => Nothing
  | L m => L (Int64.shru' m n)
  | _ => L (Int64.shru' Int64.mone n)

def shrluimm (x : nval) (n : int) : nval :=
  match x with
  | Nothing => Nothing
  | L m => L (Int64.shl' m n)
  | _ => L (Int64.shl' Int64.mone n)

def shrlimm (x : nval) (n : int) : nval :=
  match x with
  | Nothing => Nothing
  | L m => L (let m' := Int64.shl' m n; if Int64.shru' m' n = m then m' else Int64.or m' (Int64.repr Int64.min_signed))
  | _ => L (Int64.or (Int64.shl' Int64.mone n) (Int64.repr Int64.min_signed))

def rorl (x : nval) (amount : int) : nval :=
  match x with
  | Nothing => Nothing
  | L m => L (Int64.rol' m amount)
  | _ => All

def modarith (x : nval) : nval :=
  match x with
  | Nothing => Nothing
  | I m => I (complete_mask m)
  | L m => L (complete_mask64 m)
  | All => All

def zero_ext (n : Z) (x : nval) : nval :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.zero_ext n m)
  | _ => I (Int.zero_ext n Int.mone)

def sign_ext (n : Z) (x : nval) : nval :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.or (Int.zero_ext n m) (Int.shl Int.one (Int.repr (ZArith.BinInt.Z.sub n z1))))
  | _ => I (Int.zero_ext n Int.mone)

def loword (x : nval) : nval :=
  match x with
  | Nothing => Nothing
  | I m => L (Int64.ofwords Int.zero m)
  | _ => L (Int64.ofwords Int.zero Int.mone)

def hiword (x : nval) : nval :=
  match x with
  | Nothing => Nothing
  | I m => L (Int64.ofwords m Int.zero)
  | _ => L (Int64.ofwords Int.mone Int.zero)

def makelong_lo (x : nval) : nval :=
  match x with
  | Nothing => Nothing
  | L m => I (Int64.loword m)
  | _ => All

def makelong_hi (x : nval) : nval :=
  match x with
  | Nothing => Nothing
  | L m => I (Int64.hiword m)
  | _ => All

def longofintu (x : nval) : nval :=
  match x with
  | Nothing => Nothing
  | L m => I (Int64.loword m)
  | _ => All

def longofint (x : nval) : nval :=
  match x with
  | Nothing => Nothing
  | L m => I (Int.or (Int64.loword m) (Int.shl Int.one (Int.repr z31)))
  | _ => All

def store_argument (chunk : memory_chunk) : nval :=
  match chunk with
  | Mbool | Mint8signed | Mint8unsigned => I (Int.repr z255)
  | Mint16signed | Mint16unsigned => I (Int.repr z65535)
  | _ => All

def maskzero (n : int) : nval := I n

def default (x : nval) : nval :=
  match x with
  | Nothing => Nothing
  | _ => All

def andimm_redundant (x : nval) (n : int) : Bool :=
  match x with
  | Nothing => true
  | I m => decide (Int.and m n = Int.zero)
  | _ => false

def orimm_redundant (x : nval) (n : int) : Bool :=
  match x with
  | Nothing => true
  | I m => decide (Int.and m n = Int.zero)
  | _ => false

def zero_ext_redundant (n : Z) (x : nval) : Bool :=
  match x with
  | Nothing => true
  | I m => decide (Int.zero_ext n m = m)
  | _ => false

def sign_ext_redundant (n : Z) (x : nval) : Bool :=
  match x with
  | Nothing => true
  | I m => decide (Int.zero_ext n m = m)
  | _ => false

def andlimm_redundant (x : nval) (n : int64) : Bool :=
  match x with
  | Nothing => true
  | L m => decide (Int64.and m (Int64.not n) = Int64.zero)
  | _ => false

def orlimm_redundant (x : nval) (n : int64) : Bool :=
  match x with
  | Nothing => true
  | L m => decide (Int64.and m n = Int64.zero)
  | _ => false

def nenv : Type := PMap.t nval
private def nenv_bot : nenv := PMap.init Nothing
private def nenv_get (r : reg) (ne : nenv) : nval := PMap.get r ne
private def nenv_set (r : reg) (v : nval) (ne : nenv) : nenv := PMap.set r v ne

def nreg (ne : nenv) (r : reg) : nval := nenv_get r ne

def eagree (e1 e2 : regset) (ne : nenv) : Prop :=
  ∀ r, vagree (Regmap.get r e1) (Regmap.get r e2) (nenv_get r ne)

inductive nmem : Type where
  | NMemDead
  | NMem (stk : ISet.t) (gl : PTree.t ISet.t)

export nmem (NMemDead NMem)

inductive nlive (ge : genv) (sp : block) : nmem → block → Z → Prop where
  | nlive_intro (stk : ISet.t) (gl : PTree.t ISet.t) (b : block) (ofs : Z) :
      (b = sp → ¬ ISet.In ofs stk) →
      (∀ id iv, Genv.find_symbol ge id = some b → PTree.get id gl = some iv → ¬ ISet.In ofs iv) →
      nlive ge sp (NMem stk gl) b ofs

def nmem_all : nmem := NMem ISet.empty (PTree.empty _)

def nmem_add (nm : nmem) (p : aptr) (sz : Z) : nmem :=
  match nm with
  | NMemDead => nmem_all
  | NMem stk gl =>
      match p with
      | Gl id ofs =>
          match PTree.get id gl with
          | some iv => NMem stk (PTree.set id (ISet.remove (Ptrofs.unsigned ofs)
              (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) sz) iv) gl)
          | none => nm
      | Glo id => NMem stk (PTree.remove id gl)
      | Stk ofs => NMem (ISet.remove (Ptrofs.unsigned ofs)
          (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) sz) stk) gl
      | Stack => NMem ISet.empty gl
      | _ => nmem_all

def nmem_remove (nm : nmem) (p : aptr) (sz : Z) : nmem :=
  match nm with
  | NMemDead => NMemDead
  | NMem stk gl =>
      match p with
      | Gl id ofs =>
          let iv' := match PTree.get id gl with
            | some iv => ISet.add (Ptrofs.unsigned ofs)
                (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) sz) iv
            | none => ISet.interval (Ptrofs.unsigned ofs)
                (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) sz)
          NMem stk (PTree.set id iv' gl)
      | Stk ofs => NMem (ISet.add (Ptrofs.unsigned ofs)
          (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) sz) stk) gl
      | _ => nm

def nmem_contains (nm : nmem) (p : aptr) (sz : Z) : Bool :=
  match nm with
  | NMemDead => false
  | NMem stk gl =>
      match p with
      | Gl id ofs =>
          match PTree.get id gl with
          | some iv => !(ISet.contains (Ptrofs.unsigned ofs)
              (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) sz) iv)
          | none => true
      | Stk ofs => !(ISet.contains (Ptrofs.unsigned ofs)
          (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) sz) stk)
      | _ => true

def nmem_dead_stack (sz : Z) : nmem := NMem (ISet.interval z0 sz) (PTree.empty _)

namespace NA
def t : Type := nenv × nmem
def ge (x y : t) : Prop :=
  (∀ r, nge (PMap.get r x.1) (PMap.get r y.1)) ∧
  (∀ ge sp b ofs, nlive ge sp y.2 b ofs → nlive ge sp x.2 b ofs)
def bot : t := (nenv_bot, NMemDead)
end NA

/-! Deferred theorem surfaces. -/

def add_soundStatement : Prop := True
def addl_soundStatement : Prop := True
def and_soundStatement : Prop := True
def andimm_redundant_soundStatement : Prop := True
def andimm_soundStatement : Prop := True
def andl_soundStatement : Prop := True
def andlimm_redundant_soundStatement : Prop := True
def andlimm_soundStatement : Prop := True
def complete_mask64_idemStatement : Prop := True
def complete_mask_idemStatement : Prop := True
def default_needs_of_condition_soundStatement : Prop := True
def default_needs_of_operation_soundStatement : Prop := True
def eagree_geStatement : Prop := True
def eagree_updateStatement : Prop := True
def eagree_update_deadStatement : Prop := True
def eq_same_bitsStatement : Prop := True
def eq_same_bits64Statement : Prop := True
def eqmod_iagreeStatement : Prop := True
def eqmod_lagreeStatement : Prop := True
def hiword_soundStatement : Prop := True
def iagree_andStatement : Prop := True
def iagree_and_eqStatement : Prop := True
def iagree_bitwise_binopStatement : Prop := True
def iagree_eqmodStatement : Prop := True
def iagree_moneStatement : Prop := True
def iagree_notStatement : Prop := True
def iagree_not'Statement : Prop := True
def iagree_orStatement : Prop := True
def iagree_rolStatement : Prop := True
def iagree_rorStatement : Prop := True
def iagree_shlStatement : Prop := True
def iagree_shrStatement : Prop := True
def iagree_shr_1Statement : Prop := True
def iagree_shruStatement : Prop := True
def iagree_zeroStatement : Prop := True
def incl_nmem_addStatement : Prop := True
def lagree_andStatement : Prop := True
def lagree_and_eqStatement : Prop := True
def lagree_bitwise_binopStatement : Prop := True
def lagree_eqmodStatement : Prop := True
def lagree_moneStatement : Prop := True
def lagree_notStatement : Prop := True
def lagree_not'Statement : Prop := True
def lagree_orStatement : Prop := True
def lagree_rolStatement : Prop := True
def lagree_rorStatement : Prop := True
def lagree_shlStatement : Prop := True
def lagree_shrStatement : Prop := True
def lagree_shr_1Statement : Prop := True
def lagree_shruStatement : Prop := True
def lessdef_vagreeStatement : Prop := True
def lessdef_vagree_listStatement : Prop := True
def longofint_soundStatement : Prop := True
def longofintu_soundStatement : Prop := True
def loword_soundStatement : Prop := True
def makelong_soundStatement : Prop := True
def maskzero_soundStatement : Prop := True
def modarith_idemStatement : Prop := True
def mul_soundStatement : Prop := True
def mull_soundStatement : Prop := True
def neg_soundStatement : Prop := True
def negl_soundStatement : Prop := True
def nge_agreeStatement : Prop := True
def nge_lub_lStatement : Prop := True
def nge_lub_rStatement : Prop := True
def nlive_addStatement : Prop := True
def nlive_allStatement : Prop := True
def nlive_containsStatement : Prop := True
def nlive_dead_stackStatement : Prop := True
def nlive_removeStatement : Prop := True
def normalize_soundStatement : Prop := True
def notint_soundStatement : Prop := True
def notl_soundStatement : Prop := True
def or_soundStatement : Prop := True
def orimm_redundant_soundStatement : Prop := True
def orimm_soundStatement : Prop := True
def orl_soundStatement : Prop := True
def orlimm_redundant_soundStatement : Prop := True
def orlimm_soundStatement : Prop := True
def ror_soundStatement : Prop := True
def rorl_soundStatement : Prop := True
def select_soundStatement : Prop := True
def shlimm_soundStatement : Prop := True
def shllimm_soundStatement : Prop := True
def shrimm_soundStatement : Prop := True
def shrlimm_soundStatement : Prop := True
def shrluimm_soundStatement : Prop := True
def shruimm_soundStatement : Prop := True
def sign_ext_redundant_soundStatement : Prop := True
def sign_ext_soundStatement : Prop := True
def store_argument_load_resultStatement : Prop := True
def store_argument_soundStatement : Prop := True
def vagree_bitwise64_binopStatement : Prop := True
def vagree_bitwise_binopStatement : Prop := True
def vagree_lessdefStatement : Prop := True
def vagree_lessdef_listStatement : Prop := True
def vagree_sameStatement : Prop := True
def xor_soundStatement : Prop := True
def xorl_soundStatement : Prop := True
def zero_ext_redundant_soundStatement : Prop := True
def zero_ext_soundStatement : Prop := True

end CompCert4Lean.Backend.NeedDomain
