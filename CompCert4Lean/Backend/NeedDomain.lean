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
open CompCert4Lean.X86.Op
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.IntvSets
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Zbits

private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
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
private abbrev size := CompCert4Lean.Lib.Integers.Int.size
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
private abbrev size := CompCert4Lean.Lib.Integers.Int64.size
private abbrev zero_ext := CompCert4Lean.Lib.Integers.Int64.zero_ext
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

def eq_nval : (x y : nval) →
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y)
  | Nothing, Nothing => .left rfl
  | Nothing, I _ => .right (by intro h; cases h)
  | Nothing, L _ => .right (by intro h; cases h)
  | Nothing, All => .right (by intro h; cases h)
  | I _, Nothing => .right (by intro h; cases h)
  | I m, I n =>
      match CompCert4Lean.Lib.Integers.Int.eq_dec m n with
      | .left h => .left (by cases h; rfl)
      | .right h => .right (by intro h'; cases h'; exact h rfl)
  | I _, L _ => .right (by intro h; cases h)
  | I _, All => .right (by intro h; cases h)
  | L _, Nothing => .right (by intro h; cases h)
  | L _, I _ => .right (by intro h; cases h)
  | L m, L n =>
      match CompCert4Lean.Lib.Integers.Int64.eq_dec m n with
      | .left h => .left (by cases h; rfl)
      | .right h => .right (by intro h'; cases h'; exact h rfl)
  | L _, All => .right (by intro h; cases h)
  | All, Nothing => .right (by intro h; cases h)
  | All, I _ => .right (by intro h; cases h)
  | All, L _ => .right (by intro h; cases h)
  | All, All => .left rfl

def iagree (p q mask : int) : Prop :=
  ∀ i, (ZArith.BinInt.Z.le z0 i ∧ ZArith.BinInt.Z.lt i Int.zwordsize) →
    Int.testbit mask i = true → Int.testbit p i = Int.testbit q i

def lagree (p q mask : int64) : Prop :=
  ∀ i, (ZArith.BinInt.Z.le z0 i ∧ ZArith.BinInt.Z.lt i Int64.zwordsize) →
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
      (∀ i, (ZArith.BinInt.Z.le z0 i ∧ ZArith.BinInt.Z.lt i Int.zwordsize) →
        Int.testbit m2 i = true → Int.testbit m1 i = true) → nge (I m1) (I m2)
  | nge_long (m1 m2) :
      (∀ i, (ZArith.BinInt.Z.le z0 i ∧ ZArith.BinInt.Z.lt i Int64.zwordsize) →
        Int64.testbit m2 i = true → Int64.testbit m1 i = true) → nge (L m1) (L m2)

def nlub (x y : nval) : nval :=
  match x, y with
  | Nothing, _ => y
  | _, Nothing => x
  | I m1, I m2 => I (Int.or m1 m2)
  | L m1, L m2 => L (Int64.or m1 m2)
  | _, _ => All

def complete_mask (m : int) : int := Int.zero_ext (Int.size m) Int.mone
def complete_mask64 (m : int64) : int64 := Int64.zero_ext (Int64.size m) Int64.mone

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
  | I m => decide (Int.and m (Int.not n) = Int.zero)
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

namespace NVal

def t : Type := nval
def eq (x y : t) : Prop := x = y
def beq (x y : t) : Bool := CompCert4Lean.Lib.Coqlib.proj_sumbool (eq_nval x y)
def ge : t → t → Prop := nge
def bot : t := Nothing
def lub : t → t → t := nlub

def eq_refl : Prop := ∀ x, eq x x
def eq_sym : Prop := ∀ x y, eq x y → eq y x
def eq_trans : Prop := ∀ x y z, eq x y → eq y z → eq x z
def beq_correct : Prop := ∀ x y, beq x y = true → eq x y
def ge_refl : Prop := ∀ x y, eq x y → ge x y
def ge_trans : Prop := ∀ x y z, ge x y → ge y z → ge x z
def ge_bot : Prop := ∀ x, ge x bot
def ge_lub_left : Prop := ∀ x y, ge (lub x y) x
def ge_lub_right : Prop := ∀ x y, ge (lub x y) y

end NVal

namespace NE

def t : Type := PTree.t NVal.t

def get (p : positive) (x : t) : NVal.t :=
  match PTree.get p x with
  | none => NVal.bot
  | some v => v

def set (p : positive) (v : NVal.t) (x : t) : t :=
  if NVal.beq v NVal.bot then PTree.remove p x else PTree.set p v x

def eq (x y : t) : Prop := ∀ p, NVal.eq (get p x) (get p y)

def beq (x y : t) : Bool := PTree.beq NVal.beq x y

def ge (x y : t) : Prop := ∀ p, NVal.ge (get p x) (get p y)

def bot : t := PTree.empty _

def lub (x y : t) : t :=
  PTree.combine
    (fun a b =>
      match a, b with
      | some u, some v => some (NVal.lub u v)
      | none, _ => b
      | _, none => a)
    x y

def gsspec : Prop :=
  ∀ p v x q,
    NVal.eq (get q (set p v x))
      (match peq q p with | .left _ => v | .right _ => get q x)

def eq_refl : Prop := ∀ x, eq x x

def eq_sym : Prop := ∀ x y, eq x y → eq y x

def eq_trans : Prop := ∀ x y z, eq x y → eq y z → eq x z

def beq_correct : Prop := ∀ x y, beq x y = true → eq x y

def ge_refl : Prop := ∀ x y, eq x y → ge x y

def ge_trans : Prop := ∀ x y z, ge x y → ge y z → ge x z

def get_bot : Prop := ∀ p, get p bot = NVal.bot

def ge_bot : Prop := ∀ x, ge x bot

def ge_lub_left : Prop := ∀ x y, ge (lub x y) x

def ge_lub_right : Prop := ∀ x y, ge (lub x y) y

end NE

def nenv : Type := NE.t

def nreg (ne : nenv) (r : reg) : nval := NE.get r ne

def eagree (e1 e2 : regset) (ne : nenv) : Prop :=
  ∀ r, vagree (Regmap.get r e1) (Regmap.get r e2) (NE.get r ne)

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

def nmem_lub : nmem → nmem → nmem
  | NMemDead, nm => nm
  | nm, NMemDead => nm
  | NMem stk1 gl1, NMem stk2 gl2 =>
      NMem (ISet.inter stk1 stk2)
        (PTree.combine
          (fun o1 o2 =>
            match o1, o2 with
            | some iv1, some iv2 => some (ISet.inter iv1 iv2)
            | _, _ => none)
          gl1 gl2)

def nmem_beq : nmem → nmem → Bool
  | NMemDead, NMemDead => true
  | NMem stk1 gl1, NMem stk2 gl2 =>
      ISet.beq stk1 stk2 && PTree.beq ISet.beq gl1 gl2
  | _, _ => false

namespace NA
def t : Type := nenv × nmem
def eq (x y : t) : Prop :=
  NE.eq x.1 y.1 ∧
    ∀ ge sp b ofs, nlive ge sp x.2 b ofs ↔ nlive ge sp y.2 b ofs
def beq (x y : t) : Bool := NE.beq x.1 y.1 && nmem_beq x.2 y.2
def ge (x y : t) : Prop :=
  NE.ge x.1 y.1 ∧
  (∀ ge sp b ofs, nlive ge sp y.2 b ofs → nlive ge sp x.2 b ofs)
def bot : t := (NE.bot, NMemDead)
def lub (x y : t) : t := (NE.lub x.1 y.1, nmem_lub x.2 y.2)
end NA

/-! Exact source-shaped theorem surfaces. -/

def add_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (modarith x) → vagree v2 w2 (modarith x) →
    vagree (Val.add v1 v2) (Val.add w1 w2) x

def addl_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (modarith x) → vagree v2 w2 (modarith x) →
    vagree (Val.addl v1 v2) (Val.addl w1 w2) x

def and_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (bitwise x) → vagree v2 w2 (bitwise x) →
    vagree (Val.and v1 v2) (Val.and w1 w2) x

def andimm_redundant_soundStatement : Prop :=
  ∀ v w x n,
    andimm_redundant x n = true → vagree v w (andimm x n) →
    vagree (Val.and v (Vint n)) w x

def andimm_soundStatement : Prop :=
  ∀ v w x n,
    vagree v w (andimm x n) →
    vagree (Val.and v (Vint n)) (Val.and w (Vint n)) x

def andl_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (bitwise x) → vagree v2 w2 (bitwise x) →
    vagree (Val.andl v1 v2) (Val.andl w1 w2) x

def andlimm_redundant_soundStatement : Prop :=
  ∀ v w x n,
    andlimm_redundant x n = true → vagree v w (andlimm x n) →
    vagree (Val.andl v (Vlong n)) w x

def andlimm_soundStatement : Prop :=
  ∀ v w x n,
    vagree v w (andlimm x n) →
    vagree (Val.andl v (Vlong n)) (Val.andl w (Vlong n)) x

def complete_mask64_idemStatement : Prop :=
  ∀ m, complete_mask64 (complete_mask64 m) = complete_mask64 m

def complete_mask_idemStatement : Prop :=
  ∀ m, complete_mask (complete_mask m) = complete_mask m

def default_needs_of_condition_soundStatement : Prop :=
  ∀ (m1 m2 : mem),
    (∀ b ofs k p, Mem.perm m1 b ofs k p → Mem.perm m2 b ofs k p) →
    ∀ cond args1 b args2,
      eval_condition cond args1 m1 = some b →
      vagree_list args1 args2 [] →
      eval_condition cond args2 m2 = some b

def default_needs_of_operation_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (m1 m2 : mem),
    (∀ b ofs k p, Mem.perm m1 b ofs k p → Mem.perm m2 b ofs k p) →
    ∀ op args1 v1 args2 nv,
      eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge (Vptr sp Ptrofs.zero) op args1 m1 = some v1 →
      (vagree_list args1 args2 [] ∨
       vagree_list args1 args2 (default nv :: []) ∨
       vagree_list args1 args2 (default nv :: default nv :: []) ∨
       vagree_list args1 args2 (default nv :: default nv :: default nv :: [])) →
      nv ≠ Nothing →
      ∃ v2, eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge (Vptr sp Ptrofs.zero) op args2 m2 = some v2 ∧
        vagree v1 v2 nv

def eagree_geStatement : Prop :=
  ∀ e1 e2 ne ne', eagree e1 e2 ne → NE.ge ne ne' → eagree e1 e2 ne'

def eagree_updateStatement : Prop :=
  ∀ e1 e2 ne v1 v2 r,
    vagree v1 v2 (nreg ne r) →
    eagree e1 e2 (NE.set r Nothing ne) →
    eagree (Regmap.set r v1 e1) (Regmap.set r v2 e2) ne

def eagree_update_deadStatement : Prop :=
  ∀ e1 e2 ne v1 r,
    nreg ne r = Nothing → eagree e1 e2 ne →
    eagree (Regmap.set r v1 e1) e2 ne

def eq_same_bitsStatement : Prop :=
  ∀ i x y, x = y → Int.testbit x i = Int.testbit y i

def eq_same_bits64Statement : Prop :=
  ∀ i x y, x = y → Int64.testbit x i = Int64.testbit y i

def eqmod_iagreeStatement : Prop :=
  ∀ m x y, eqmod (two_p (Int.size m)) x y → iagree (Int.repr x) (Int.repr y) m

def eqmod_lagreeStatement : Prop :=
  ∀ m x y, eqmod (two_p (Int64.size m)) x y →
    lagree (Int64.repr x) (Int64.repr y) m

def hiword_soundStatement : Prop :=
  ∀ v w x, vagree v w (hiword x) →
    vagree (Val.hiword v) (Val.hiword w) x

def iagree_andStatement : Prop :=
  ∀ x y n m, iagree x y (Int.and m n) →
    iagree (Int.and x n) (Int.and y n) m

def iagree_and_eqStatement : Prop :=
  ∀ x y mask, iagree x y mask ↔ Int.and x mask = Int.and y mask

def iagree_bitwise_binopStatement : Prop :=
  ∀ (sem : Bool → Bool → Bool) (f : int → int → int),
    (∀ x y i, (ZArith.BinInt.Z.le z0 i ∧ ZArith.BinInt.Z.lt i Int.zwordsize) →
      Int.testbit (f x y) i = sem (Int.testbit x i) (Int.testbit y i)) →
    ∀ x1 x2 y1 y2 m,
      iagree x1 y1 m → iagree x2 y2 m → iagree (f x1 x2) (f y1 y2) m

def iagree_eqmodStatement : Prop :=
  ∀ x y m, iagree x y (complete_mask m) →
    eqmod (two_p (Int.size m)) (Int.unsigned x) (Int.unsigned y)

def iagree_moneStatement : Prop :=
  ∀ p q, iagree p q Int.mone → p = q

def iagree_notStatement : Prop :=
  ∀ x y m, iagree x y m → iagree (Int.not x) (Int.not y) m

def iagree_not'Statement : Prop :=
  ∀ x y m, iagree (Int.not x) (Int.not y) m → iagree x y m

def iagree_orStatement : Prop :=
  ∀ x y n m, iagree x y (Int.and m (Int.not n)) →
    iagree (Int.or x n) (Int.or y n) m

def iagree_rolStatement : Prop :=
  ∀ p q m amount, iagree p q (Int.ror m amount) →
    iagree (Int.rol p amount) (Int.rol q amount) m

def iagree_rorStatement : Prop :=
  ∀ p q m amount, iagree p q (Int.rol m amount) →
    iagree (Int.ror p amount) (Int.ror q amount) m

def iagree_shlStatement : Prop :=
  ∀ x y m n, iagree x y (Int.shru m n) →
    iagree (Int.shl x n) (Int.shl y n) m

def iagree_shrStatement : Prop :=
  ∀ x y m n,
    iagree x y (Int.or (Int.shl m n) (Int.repr Int.min_signed)) →
    iagree (Int.shr x n) (Int.shr y n) m

def iagree_shr_1Statement : Prop :=
  ∀ x y m n, Int.shru (Int.shl m n) n = m →
    iagree x y (Int.shl m n) → iagree (Int.shr x n) (Int.shr y n) m

def iagree_shruStatement : Prop :=
  ∀ x y m n, iagree x y (Int.shl m n) →
    iagree (Int.shru x n) (Int.shru y n) m

def iagree_zeroStatement : Prop := ∀ p q, iagree p q Int.zero

def incl_nmem_addStatement : Prop :=
  ∀ (ge : genv) (sp : block) nm b i p sz,
    nlive ge sp nm b i → nlive ge sp (nmem_add nm p sz) b i

def lagree_andStatement : Prop :=
  ∀ x y n m, lagree x y (Int64.and m n) →
    lagree (Int64.and x n) (Int64.and y n) m

def lagree_and_eqStatement : Prop :=
  ∀ x y mask, lagree x y mask ↔ Int64.and x mask = Int64.and y mask

def lagree_bitwise_binopStatement : Prop :=
  ∀ (sem : Bool → Bool → Bool) (f : int64 → int64 → int64),
    (∀ x y i, (ZArith.BinInt.Z.le z0 i ∧ ZArith.BinInt.Z.lt i Int64.zwordsize) →
      Int64.testbit (f x y) i = sem (Int64.testbit x i) (Int64.testbit y i)) →
    ∀ x1 x2 y1 y2 m,
      lagree x1 y1 m → lagree x2 y2 m → lagree (f x1 x2) (f y1 y2) m

def lagree_eqmodStatement : Prop :=
  ∀ x y m, lagree x y (complete_mask64 m) →
    eqmod (two_p (Int64.size m)) (Int64.unsigned x) (Int64.unsigned y)

def lagree_moneStatement : Prop :=
  ∀ p q, lagree p q Int64.mone → p = q

def lagree_notStatement : Prop :=
  ∀ x y m, lagree x y m → lagree (Int64.not x) (Int64.not y) m

def lagree_not'Statement : Prop :=
  ∀ x y m, lagree (Int64.not x) (Int64.not y) m → lagree x y m

def lagree_orStatement : Prop :=
  ∀ x y n m, lagree x y (Int64.and m (Int64.not n)) →
    lagree (Int64.or x n) (Int64.or y n) m

def lagree_rolStatement : Prop :=
  ∀ p q m amount, lagree p q (Int64.ror m amount) →
    lagree (Int64.rol p amount) (Int64.rol q amount) m

def lagree_rorStatement : Prop :=
  ∀ p q m amount, lagree p q (Int64.rol' m amount) →
    lagree (Int64.ror' p amount) (Int64.ror' q amount) m

def lagree_shlStatement : Prop :=
  ∀ x y m n, lagree x y (Int64.shru' m n) →
    lagree (Int64.shl' x n) (Int64.shl' y n) m

def lagree_shrStatement : Prop :=
  ∀ x y m n,
    lagree x y (Int64.or (Int64.shl' m n) (Int64.repr Int64.min_signed)) →
    lagree (Int64.shr' x n) (Int64.shr' y n) m

def lagree_shr_1Statement : Prop :=
  ∀ x y m n, Int64.shru' (Int64.shl' m n) n = m →
    lagree x y (Int64.shl' m n) → lagree (Int64.shr' x n) (Int64.shr' y n) m

def lagree_shruStatement : Prop :=
  ∀ x y m n, lagree x y (Int64.shl' m n) →
    lagree (Int64.shru' x n) (Int64.shru' y n) m

def lessdef_vagreeStatement : Prop :=
  ∀ v w, vagree v w All → Val.lessdef v w

def lessdef_vagree_listStatement : Prop :=
  ∀ vl1 vl2, vagree_list vl1 vl2 [] → Val.lessdef_list vl1 vl2

def longofint_soundStatement : Prop :=
  ∀ v w x, vagree v w (longofint x) →
    vagree (Val.longofint v) (Val.longofint w) x

def longofintu_soundStatement : Prop :=
  ∀ v w x, vagree v w (longofintu x) →
    vagree (Val.longofintu v) (Val.longofintu w) x

def loword_soundStatement : Prop :=
  ∀ v w x, vagree v w (loword x) →
    vagree (Val.loword v) (Val.loword w) x

def makelong_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (makelong_hi x) → vagree v2 w2 (makelong_lo x) →
    vagree (Val.longofwords v1 v2) (Val.longofwords w1 w2) x

def maskzero_soundStatement : Prop :=
  ∀ v w n b, vagree v w (maskzero n) →
    Val.maskzero_bool v n = some b → Val.maskzero_bool w n = some b

def modarith_idemStatement : Prop := ∀ nv, modarith (modarith nv) = modarith nv

def mul_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (modarith x) → vagree v2 w2 (modarith x) →
    vagree (Val.mul v1 v2) (Val.mul w1 w2) x

def mull_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (modarith x) → vagree v2 w2 (modarith x) →
    vagree (Val.mull v1 v2) (Val.mull w1 w2) x

def neg_soundStatement : Prop :=
  ∀ v w x, vagree v w (modarith x) → vagree (Val.neg v) (Val.neg w) x

def negl_soundStatement : Prop :=
  ∀ v w x, vagree v w (modarith x) → vagree (Val.negl v) (Val.negl w) x

def nge_agreeStatement : Prop :=
  ∀ v w x y, nge x y → vagree v w x → vagree v w y

def nge_lub_lStatement : Prop := ∀ x y, nge (nlub x y) x

def nge_lub_rStatement : Prop := ∀ x y, nge (nlub x y) y

def nlive_addStatement : Prop :=
  ∀ (ge : genv) (sp : block) bc b ofs p nm sz i,
    genv_match bc ge → bc sp = BCstack → pmatch bc b ofs p →
    (ZArith.BinInt.Z.le (Ptrofs.unsigned ofs) i ∧
      ZArith.BinInt.Z.lt i (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) sz)) →
    nlive ge sp (nmem_add nm p sz) b i

def nlive_allStatement : Prop :=
  ∀ (ge : genv) (sp b : block) ofs, nlive ge sp nmem_all b ofs

def nlive_containsStatement : Prop :=
  ∀ (ge : genv) (sp : block) bc b ofs p nm sz i,
    genv_match bc ge → bc sp = BCstack → pmatch bc b ofs p →
    nmem_contains nm p sz = false →
    (ZArith.BinInt.Z.le (Ptrofs.unsigned ofs) i ∧
      ZArith.BinInt.Z.lt i (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) sz)) →
    ¬ nlive ge sp nm b i

def nlive_dead_stackStatement : Prop :=
  ∀ (ge : genv) (sp : block) sz b' i,
    b' ≠ sp ∨ ¬ (ZArith.BinInt.Z.le z0 i ∧ ZArith.BinInt.Z.lt i sz) →
    nlive ge sp (nmem_dead_stack sz) b' i

def nlive_removeStatement : Prop :=
  ∀ (ge : genv) (sp : block) bc b ofs p nm sz b' i,
    genv_match bc ge → bc sp = BCstack → pmatch bc b ofs p →
    nlive ge sp nm b' i →
    b' ≠ b ∨ ZArith.BinInt.Z.lt i (Ptrofs.unsigned ofs) ∨
      ZArith.BinInt.Z.le (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) sz) i →
    nlive ge sp (nmem_remove nm p sz) b' i

def normalize_soundStatement : Prop :=
  ∀ v w x ty, vagree v w x →
    vagree (Val.normalize v ty) (Val.normalize w ty) x

def notint_soundStatement : Prop :=
  ∀ v w x, vagree v w (bitwise x) →
    vagree (Val.notint v) (Val.notint w) x

def notl_soundStatement : Prop :=
  ∀ v w x, vagree v w (bitwise x) →
    vagree (Val.notl v) (Val.notl w) x

def or_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (bitwise x) → vagree v2 w2 (bitwise x) →
    vagree (Val.or v1 v2) (Val.or w1 w2) x

def orimm_redundant_soundStatement : Prop :=
  ∀ v w x n, orimm_redundant x n = true → vagree v w (orimm x n) →
    vagree (Val.or v (Vint n)) w x

def orimm_soundStatement : Prop :=
  ∀ v w x n, vagree v w (orimm x n) →
    vagree (Val.or v (Vint n)) (Val.or w (Vint n)) x

def orl_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (bitwise x) → vagree v2 w2 (bitwise x) →
    vagree (Val.orl v1 v2) (Val.orl w1 w2) x

def orlimm_redundant_soundStatement : Prop :=
  ∀ v w x n, orlimm_redundant x n = true → vagree v w (orlimm x n) →
    vagree (Val.orl v (Vlong n)) w x

def orlimm_soundStatement : Prop :=
  ∀ v w x n, vagree v w (orlimm x n) →
    vagree (Val.orl v (Vlong n)) (Val.orl w (Vlong n)) x

def ror_soundStatement : Prop :=
  ∀ v w x n, vagree v w (ror x n) →
    vagree (Val.ror v (Vint n)) (Val.ror w (Vint n)) x

def rorl_soundStatement : Prop :=
  ∀ v w x n, vagree v w (rorl x n) →
    vagree (Val.rorl v (Vint n)) (Val.rorl w (Vint n)) x

def select_soundStatement : Prop :=
  ∀ ob v1 v2 w1 w2 ty x,
    vagree v1 w1 x → vagree v2 w2 x →
    vagree (Val.select ob v1 v2 ty) (Val.select ob w1 w2 ty) x

def shlimm_soundStatement : Prop :=
  ∀ v w x n, vagree v w (shlimm x n) →
    vagree (Val.shl v (Vint n)) (Val.shl w (Vint n)) x

def shllimm_soundStatement : Prop :=
  ∀ v w x n, vagree v w (shllimm x n) →
    vagree (Val.shll v (Vint n)) (Val.shll w (Vint n)) x

def shrimm_soundStatement : Prop :=
  ∀ v w x n, vagree v w (shrimm x n) →
    vagree (Val.shr v (Vint n)) (Val.shr w (Vint n)) x

def shrlimm_soundStatement : Prop :=
  ∀ v w x n, vagree v w (shrlimm x n) →
    vagree (Val.shrl v (Vint n)) (Val.shrl w (Vint n)) x

def shrluimm_soundStatement : Prop :=
  ∀ v w x n, vagree v w (shrluimm x n) →
    vagree (Val.shrlu v (Vint n)) (Val.shrlu w (Vint n)) x

def shruimm_soundStatement : Prop :=
  ∀ v w x n, vagree v w (shruimm x n) →
    vagree (Val.shru v (Vint n)) (Val.shru w (Vint n)) x

def sign_ext_redundant_soundStatement : Prop :=
  ∀ v w x n, sign_ext_redundant n x = true → vagree v w (sign_ext n x) →
    ZArith.BinInt.Z.lt z0 n → vagree (Val.sign_ext n v) w x

def sign_ext_soundStatement : Prop :=
  ∀ v w x n, vagree v w (sign_ext n x) →
    ZArith.BinInt.Z.lt z0 n → vagree (Val.sign_ext n v) (Val.sign_ext n w) x

def store_argument_load_resultStatement : Prop :=
  ∀ chunk v w, vagree v w (store_argument chunk) →
    Val.lessdef (Val.load_result chunk v) (Val.load_result chunk w)

def store_argument_soundStatement : Prop :=
  ∀ chunk v w, vagree v w (store_argument chunk) →
    list_forall2 memval_lessdef (encode_val chunk v) (encode_val chunk w)

def vagree_bitwise64_binopStatement : Prop :=
  ∀ (f : int64 → int64 → int64),
    (∀ p1 p2 q1 q2 m, lagree p1 q1 m → lagree p2 q2 m →
      lagree (f p1 p2) (f q1 q2) m) →
    ∀ v1 w1 v2 w2 x,
      vagree v1 w1 (bitwise x) → vagree v2 w2 (bitwise x) →
      vagree
        (match v1, v2 with | Vlong i1, Vlong i2 => Vlong (f i1 i2) | _, _ => Vundef)
        (match w1, w2 with | Vlong i1, Vlong i2 => Vlong (f i1 i2) | _, _ => Vundef) x

def vagree_bitwise_binopStatement : Prop :=
  ∀ (f : int → int → int),
    (∀ p1 p2 q1 q2 m, iagree p1 q1 m → iagree p2 q2 m →
      iagree (f p1 p2) (f q1 q2) m) →
    ∀ v1 w1 v2 w2 x,
      vagree v1 w1 (bitwise x) → vagree v2 w2 (bitwise x) →
      vagree
        (match v1, v2 with | Vint i1, Vint i2 => Vint (f i1 i2) | _, _ => Vundef)
        (match w1, w2 with | Vint i1, Vint i2 => Vint (f i1 i2) | _, _ => Vundef) x

def vagree_lessdefStatement : Prop :=
  ∀ v w x, Val.lessdef v w → vagree v w x

def vagree_lessdef_listStatement : Prop :=
  ∀ vl1 vl2, Val.lessdef_list vl1 vl2 → ∀ nvl, vagree_list vl1 vl2 nvl

def vagree_sameStatement : Prop := ∀ v x, vagree v v x

def xor_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (bitwise x) → vagree v2 w2 (bitwise x) →
    vagree (Val.xor v1 v2) (Val.xor w1 w2) x

def xorl_soundStatement : Prop :=
  ∀ v1 w1 v2 w2 x,
    vagree v1 w1 (bitwise x) → vagree v2 w2 (bitwise x) →
    vagree (Val.xorl v1 v2) (Val.xorl w1 w2) x

def zero_ext_redundant_soundStatement : Prop :=
  ∀ v w x n, zero_ext_redundant n x = true → vagree v w (zero_ext n x) →
    ZArith.BinInt.Z.le z0 n → vagree (Val.zero_ext n v) w x

def zero_ext_soundStatement : Prop :=
  ∀ v w x n, vagree v w (zero_ext n x) →
    ZArith.BinInt.Z.le z0 n → vagree (Val.zero_ext n v) (Val.zero_ext n w) x

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

theorem vagree_same : vagree_sameStatement := by
  intro v x
  cases x with
  | Nothing => trivial
  | I m =>
    cases v with
    | Vint p => intro i _ _; rfl
    | Vundef => trivial
    | Vlong p => trivial
    | Vfloat p => trivial
    | Vsingle p => trivial
    | Vptr b ofs => trivial
  | L m =>
    cases v with
    | Vlong p => intro i _ _; rfl
    | Vundef => trivial
    | Vint p => trivial
    | Vfloat p => trivial
    | Vsingle p => trivial
    | Vptr b ofs => trivial
  | All => exact .lessdef_refl _

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

theorem vagree_lessdef : vagree_lessdefStatement := by
  intro v w x h
  cases h with
  | lessdef_refl v =>
      exact vagree_same v x
  | lessdef_undef v =>
      cases x <;> simp [vagree, iVagree, lVagree]
      exact CompCert4Lean.Common.Values.Val.lessdef_undef w

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

theorem lessdef_vagree : lessdef_vagreeStatement := by
  intro v w h
  exact h

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

theorem lessdef_vagree_list : lessdef_vagree_listStatement := by
  intro vl1 vl2 h
  induction vl1 generalizing vl2 with
  | nil =>
      cases vl2 with
      | nil => exact CompCert4Lean.Common.Values.Val.lessdef_list_nil
      | cons v2 vl2 => cases h
  | cons v1 vl1 ih =>
      cases vl2 with
      | nil => cases h
      | cons v2 vl2 =>
          cases h with
          | vagree_list_default _ _ _ _ hv htail =>
              exact CompCert4Lean.Common.Values.Val.lessdef_list_cons v1 v2 vl1 vl2
                (lessdef_vagree v1 v2 hv) (ih vl2 htail)

end CompCert4Lean.Backend.NeedDomain
