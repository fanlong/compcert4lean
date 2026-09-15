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

namespace CompCert4Lean.Backend.NeedDomain

theorem vagree_lessdef_list : vagree_lessdef_listStatement := by
  intro vl1 vl2 h
  induction h with
  | lessdef_list_nil =>
      intro nvl
      exact vagree_list.vagree_list_nil nvl
  | lessdef_list_cons v1 v2 vl1 vl2 hhead htail ih =>
      intro nvl
      cases nvl with
      | nil =>
          exact vagree_list.vagree_list_default v1 vl1 v2 vl2
            (vagree_lessdef v1 v2 All hhead) (ih [])
      | cons nv1 nvl =>
          exact vagree_list.vagree_list_cons v1 vl1 v2 vl2 nv1 nvl
            (vagree_lessdef v1 v2 nv1 hhead) (ih nvl)

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

theorem nge_agree : nge_agreeStatement := by
  intro v w x y hge hagree
  cases hge with
  | nge_nothing y =>
      exact vagree_lessdef v w y hagree
  | nge_all x =>
      trivial
  | nge_int m1 m2 hmask =>
      cases v <;> cases w <;> simp [vagree, iVagree] at *
      intro i hi hm2
      exact hagree i hi (hmask i hi.1 hi.2 hm2)
  | nge_long m1 m2 hmask =>
      cases v <;> cases w <;> simp [vagree, lVagree] at *
      intro i hi hm2
      exact hagree i hi (hmask i hi.1 hi.2 hm2)

end CompCert4Lean.Backend.NeedDomain
namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private def iagreePrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem iagreeValReprOfNat (bits n : Nat) :
    (WordCore.repr bits (ZArith.BinInt.Z.of_nat n)).val = n % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let nF := (lctx.findFromUserName? `n).get!
    let bitsE := mkFVar bitsF.fvarId
    let nE := mkFVar nF.fvarId
    let z := mkApp (mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat) nE
    let e1 := mkApp2 (mkConst (iagreePrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")) bitsE z
    let e2 := mkApp2 (mkConst (iagreePrivateName "CompCert4Lean.Lib.Integers.WordCore.residue_zOfNat")) bitsE nE
    let t1 ← inferType e1
    let t2 ← inferType e2
    let (α, lhs, mid) := match_expr t1 with
      | _root_.Eq α lhs mid => (α, lhs, mid)
      | _ => panic! "unexpected first equality"
    let (_, _, rhs) := match_expr t2 with
      | _root_.Eq _ middle rhs => (α, middle, rhs)
      | _ => panic! "unexpected second equality"
    let eqtrans := mkConst ``Eq.trans [.succ .zero]
    let e := mkAppN eqtrans #[α, lhs, mid, rhs, e1, e2]
    closeMainGoal Name.anonymous e

private theorem iagreeWordValLt (a : Int.int) : a.val < 2 ^ Int.wordsize := by
  run_tac
    let lctx ← getLCtx
    let aF := (lctx.findFromUserName? `a).get!
    let aE := mkFVar aF.fvarId
    let e ← mkAppM (iagreePrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt") #[aE]
    closeMainGoal Name.anonymous e

private theorem iagreeAndVal (a b : Int.int) :
    (Int.and a b).val = Nat.land a.val b.val := by
  change (WordCore.repr Int.wordsize (ZArith.BinInt.Z.of_nat (Nat.land a.val b.val))).val = _
  rw [iagreeValReprOfNat]
  change Nat.land a.val b.val % (2 ^ Int.wordsize) = Nat.land a.val b.val
  apply Nat.mod_eq_of_lt
  exact Nat.and_lt_two_pow _ (iagreeWordValLt b)

private theorem iagreeTestbitPos (a : Int.int) (p : positive) :
    Int.testbit a (.Zpos p) = a.val.testBit (posToNat p) := by
  simp only [Int.testbit, WordCore.testbit]
  run_tac
    let lctx ← getLCtx
    let aF := (lctx.findFromUserName? `a).get!
    let pF := (lctx.findFromUserName? `p).get!
    let aE := mkFVar aF.fvarId
    let pE := mkFVar pF.fvarId
    let e ← mkAppM (iagreePrivateName "CompCert4Lean.Lib.Integers.WordCore.positiveToNat_eq_posToNat") #[pE]
    let natTy := mkConst ``Nat
    let aval ← mkAppM ``CompCert4Lean.Lib.Integers.WordCore.Word.val #[aE]
    let f := mkLambda `k BinderInfo.default natTy
      (mkApp2 (mkConst ``Nat.testBit) aval (mkBVar 0))
    let ce ← mkAppM ``congrArg #[f, e]
    closeMainGoal Name.anonymous ce

private theorem iagreeTestbitZero (a : Int.int) :
    Int.testbit a .Z0 = a.val.testBit 0 := by
  rfl

private theorem iagreeNatLandTestbit (a b k : Nat) :
    (Nat.land a b).testBit k = (a.testBit k && b.testBit k) := by
  change (a &&& b).testBit k = _
  exact Nat.testBit_and a b k

theorem iagree_and_eq : iagree_and_eqStatement := by
  intro x y mask
  constructor
  · intro hagree
    apply WordCore.ext_of_val_eq
    apply Nat.eq_of_testBit_eq
    intro k
    rw [iagreeAndVal, iagreeAndVal, iagreeNatLandTestbit, iagreeNatLandTestbit]
    cases k with
    | zero =>
        by_cases hmask : mask.val.testBit 0 = true
        · have hxy := hagree (.Z0) (by
            constructor
            · change (0 : Int) ≤ 0
              omega
            · change (0 : Int) < 32
              omega) (by
                rw [iagreeTestbitZero]
                exact hmask)
          rw [iagreeTestbitZero, iagreeTestbitZero] at hxy
          simp [hmask, hxy]
        · have hmask' : mask.val.testBit 0 = false := Bool.eq_false_iff.mpr hmask
          simp [hmask']
    | succ k =>
        let p := posOfNat (Nat.succ k)
        have hp : posToNat p = Nat.succ k :=
          posToNat_posOfNat (Nat.succ_pos k)
        by_cases hlt : Nat.succ k < 32
        · by_cases hmask : mask.val.testBit (Nat.succ k) = true
          · have hxy := hagree (.Zpos p) (by
              constructor
              · change (0 : Int) ≤ Int.ofNat (posToNat p)
                exact Int.natCast_nonneg _
              · change (Int.ofNat (posToNat p) : Int) < Int.ofNat 32
                rw [hp]
                exact Int.ofNat_lt.mpr hlt) (by
                  rw [iagreeTestbitPos, hp]
                  exact hmask)
            rw [iagreeTestbitPos, iagreeTestbitPos, hp] at hxy
            simp [hmask, hxy]
          · have hmask' : mask.val.testBit (Nat.succ k) = false :=
              Bool.eq_false_iff.mpr hmask
            simp [hmask']
        · have hpow : 2 ^ Int.wordsize ≤ 2 ^ (Nat.succ k) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hlt)
          have hmasklt : mask.val < 2 ^ (Nat.succ k) :=
            Nat.lt_of_lt_of_le (iagreeWordValLt mask) hpow
          have hmask' : mask.val.testBit (Nat.succ k) = false :=
            Nat.testBit_lt_two_pow hmasklt
          simp [hmask']
  · intro hand i hirange hmask
    have hval := congrArg WordCore.Word.val hand
    rw [iagreeAndVal, iagreeAndVal] at hval
    cases i with
    | Zneg p =>
        cases hmask
    | Z0 =>
        have hm : mask.val.testBit 0 = true := by
          simpa [iagreeTestbitZero] using hmask
        have hbit := congrArg (fun n : Nat => n.testBit 0) hval
        rw [iagreeNatLandTestbit, iagreeNatLandTestbit] at hbit
        have hxy : x.val.testBit 0 = y.val.testBit 0 := by
          simpa [hm] using hbit
        simpa [iagreeTestbitZero] using hxy
    | Zpos p =>
        have hm : mask.val.testBit (posToNat p) = true := by
          simpa [iagreeTestbitPos] using hmask
        have hbit := congrArg (fun n : Nat => n.testBit (posToNat p)) hval
        rw [iagreeNatLandTestbit, iagreeNatLandTestbit] at hbit
        have hxy : x.val.testBit (posToNat p) = y.val.testBit (posToNat p) := by
          simpa [hm] using hbit
        simpa [iagreeTestbitPos] using hxy

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

theorem iagree_mone : iagree_moneStatement := by
  intro p q h
  have hand : CompCert4Lean.Lib.Integers.Int.and p
      CompCert4Lean.Lib.Integers.Int.mone =
      CompCert4Lean.Lib.Integers.Int.and q CompCert4Lean.Lib.Integers.Int.mone :=
    (iagree_and_eq p q CompCert4Lean.Lib.Integers.Int.mone).mp h
  have hval := congrArg (fun z => z.val) hand
  rw [iagreeAndVal, iagreeAndVal] at hval
  have hp : p.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize :=
    iagreeWordValLt p
  have hq : q.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize :=
    iagreeWordValLt q
  have hmone : CompCert4Lean.Lib.Integers.Int.mone.val =
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1 := by
    rfl
  rw [hmone, Nat.land_eq,
    Nat.and_two_pow_sub_one_of_lt_two_pow hp, Nat.land_eq,
    Nat.and_two_pow_sub_one_of_lt_two_pow hq] at hval
  exact CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq hval

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

theorem iagree_zero : iagree_zeroStatement := by
  intro p q i hirange hmask
  cases i with
  | Zneg p => cases hmask
  | Z0 =>
      have hz : CompCert4Lean.Lib.Integers.Int.testbit
          CompCert4Lean.Lib.Integers.Int.zero .Z0 = false := by rfl
      rw [hz] at hmask
      cases hmask
  | Zpos p =>
      have hz : CompCert4Lean.Lib.Integers.Int.testbit
          CompCert4Lean.Lib.Integers.Int.zero (.Zpos p) = false := by
        have hval : CompCert4Lean.Lib.Integers.Int.zero.val = 0 := by rfl
        change Nat.testBit CompCert4Lean.Lib.Integers.Int.zero.val _ = false
        rw [hval]
        exact Nat.zero_testBit _
      rw [hz] at hmask
      cases hmask

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

private theorem iagreeNotVal (a : Int.int) :
    (Int.not a).val = Nat.xor a.val (2 ^ Int.wordsize - 1) := by
  change (WordCore.repr Int.wordsize
    (ZArith.BinInt.Z.of_nat (Nat.xor a.val (2 ^ Int.wordsize - 1)))).val = _
  rw [iagreeValReprOfNat]
  apply Nat.mod_eq_of_lt
  apply Nat.xor_lt_two_pow
  · exact iagreeWordValLt a
  · have hp : 0 < 2 ^ Int.wordsize := Nat.two_pow_pos _
    omega

private theorem iagreeNotTestbit (a : Int.int) (i : Z)
    (hirange : ZArith.BinInt.Z.le z0 i ∧ ZArith.BinInt.Z.lt i Int.zwordsize) :
    Int.testbit (Int.not a) i = !(Int.testbit a i) := by
  cases i with
  | Zneg p =>
      exfalso
      have h := hirange.1
      change (0 : Int) ≤ -Int.ofNat (posToNat p) at h
      have hp : (0 : Int) < Int.ofNat (posToNat p) := by
        exact Int.natCast_pos.mpr (posToNat_positive p)
      omega
  | Z0 =>
      rw [iagreeTestbitZero (Int.not a), iagreeTestbitZero a]
      rw [iagreeNotVal]
      rw [Nat.xor_eq]
      rw [Nat.testBit_xor]
      have hmask : (2 ^ Int.wordsize - 1).testBit 0 = true := by
        rw [Nat.testBit_two_pow_sub_one]
        decide
      simp [hmask]
  | Zpos p =>
      rw [iagreeTestbitPos (Int.not a) p, iagreeTestbitPos a p]
      rw [iagreeNotVal]
      rw [Nat.xor_eq]
      rw [Nat.testBit_xor]
      have hkZ := hirange.2
      change Int.ofNat (posToNat p) < Int.ofNat Int.wordsize at hkZ
      have hk : posToNat p < Int.wordsize := Int.ofNat_lt.mp hkZ
      have hmask : (2 ^ Int.wordsize - 1).testBit (posToNat p) = true := by
        rw [Nat.testBit_two_pow_sub_one]
        simp [hk]
      simp [hmask]

theorem iagree_not : iagree_notStatement := by
  intro x y m h i hirange hmask
  rw [iagreeNotTestbit x i hirange, iagreeNotTestbit y i hirange]
  exact congrArg Bool.not (h i hirange hmask)

private theorem iagreeNotInvolutive (a : Int.int) :
    Int.not (Int.not a) = a := by
  apply WordCore.ext_of_val_eq
  rw [iagreeNotVal, iagreeNotVal]
  rw [Nat.xor_eq, Nat.xor_eq]
  rw [Nat.xor_assoc]
  simp

theorem iagree_not' : iagree_not'Statement := by
  intro x y m h i hirange hmask
  have h' : iagree (Int.not (Int.not x)) (Int.not (Int.not y)) m :=
    iagree_not (Int.not x) (Int.not y) m h
  have hbits := h' i hirange hmask
  rw [iagreeNotInvolutive, iagreeNotInvolutive] at hbits
  exact hbits

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

private theorem iagreeAndAssoc (a b c : Int.int) :
    Int.and (Int.and a b) c = Int.and a (Int.and b c) := by
  apply WordCore.ext_of_val_eq
  rw [iagreeAndVal, iagreeAndVal, iagreeAndVal, iagreeAndVal]
  rw [Nat.land_eq, Nat.land_eq, Nat.land_eq, Nat.land_eq]
  exact Nat.and_assoc _ _ _

private theorem iagreeAndComm (a b : Int.int) :
    Int.and a b = Int.and b a := by
  apply WordCore.ext_of_val_eq
  rw [iagreeAndVal, iagreeAndVal]
  rw [Nat.land_eq, Nat.land_eq]
  exact Nat.and_comm _ _

theorem iagree_and : iagree_andStatement := by
  intro x y n m h
  apply (iagree_and_eq (Int.and x n) (Int.and y n) m).mpr
  have hh : Int.and x (Int.and m n) = Int.and y (Int.and m n) :=
    (iagree_and_eq x y (Int.and m n)).mp h
  calc
    Int.and (Int.and x n) m = Int.and x (Int.and n m) :=
      iagreeAndAssoc x n m
    _ = Int.and x (Int.and m n) := by rw [iagreeAndComm n m]
    _ = Int.and y (Int.and m n) := hh
    _ = Int.and y (Int.and n m) := by rw [iagreeAndComm m n]
    _ = Int.and (Int.and y n) m := (iagreeAndAssoc y n m).symm

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

private theorem iagreeOrVal (a b : Int.int) :
    (Int.or a b).val = Nat.lor a.val b.val := by
  change (WordCore.repr Int.wordsize
    (ZArith.BinInt.Z.of_nat (Nat.lor a.val b.val))).val = _
  rw [iagreeValReprOfNat]
  apply Nat.mod_eq_of_lt
  exact Nat.or_lt_two_pow (iagreeWordValLt a) (iagreeWordValLt b)

private theorem iagreeAndTestbit (a b : Int.int) (i : Z) :
    Int.testbit (Int.and a b) i = (Int.testbit a i && Int.testbit b i) := by
  cases i with
  | Zneg p => rfl
  | Z0 =>
      rw [iagreeTestbitZero (Int.and a b), iagreeTestbitZero a,
        iagreeTestbitZero b]
      rw [iagreeAndVal, Nat.land_eq, Nat.testBit_and]
  | Zpos p =>
      rw [iagreeTestbitPos (Int.and a b) p, iagreeTestbitPos a p,
        iagreeTestbitPos b p]
      rw [iagreeAndVal, Nat.land_eq, Nat.testBit_and]

private theorem iagreeOrTestbit (a b : Int.int) (i : Z) :
    Int.testbit (Int.or a b) i = (Int.testbit a i || Int.testbit b i) := by
  cases i with
  | Zneg p => rfl
  | Z0 =>
      rw [iagreeTestbitZero (Int.or a b), iagreeTestbitZero a,
        iagreeTestbitZero b]
      rw [iagreeOrVal, Nat.lor_eq, Nat.testBit_or]
  | Zpos p =>
      rw [iagreeTestbitPos (Int.or a b) p, iagreeTestbitPos a p,
        iagreeTestbitPos b p]
      rw [iagreeOrVal, Nat.lor_eq, Nat.testBit_or]

theorem iagree_or : iagree_orStatement := by
  intro x y n m h i hirange hmask
  rw [iagreeOrTestbit, iagreeOrTestbit]
  by_cases hn : Int.testbit n i = true
  · simp [hn]
  · have hn' : Int.testbit n i = false := Bool.eq_false_iff.mpr hn
    have hmn : Int.testbit (Int.and m (Int.not n)) i = true := by
      rw [iagreeAndTestbit, iagreeNotTestbit n i hirange]
      simp [hmask, hn']
    have hxy := h i hirange hmn
    simp [hn', hxy]

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

theorem iagree_bitwise_binop : iagree_bitwise_binopStatement := by
  intro sem f hsem x1 x2 y1 y2 m h1 h2 i hi hm
  rw [hsem x1 x2 i hi, hsem y1 y2 i hi]
  simp [h1 i hi hm, h2 i hi hm]

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

private theorem test_posToNat_pos (p : positive) :
    0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
  induction p with
  | xH => simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
  | xI p ih => simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, ih]
  | xO p ih => simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, ih]

private theorem test_iagreeShlVal (a n : Int.int) :
    (Int.shl a n).val = (a.val * 2 ^ n.val) % (2 ^ Int.wordsize) := by
  change (WordCore.repr Int.wordsize
    (ZArith.BinInt.Z.shiftl (WordCore.unsigned a) (WordCore.unsigned n))).val = _
  have hunsigned (w : Int.int) :
      WordCore.unsigned w = ZArith.BinInt.Z.of_nat w.val := by
    have hw : ZArith.BinInt.Z.le z0 (WordCore.unsigned w) := by
      have h := w.intrange.1
      change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (WordCore.unsigned w) at h
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (WordCore.unsigned w)
      omega
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
      (WordCore.unsigned w) hw).symm
  have ha := hunsigned a
  have hn := hunsigned n
  rw [ha, hn]
  rw [show ZArith.BinInt.Z.shiftl (ZArith.BinInt.Z.of_nat a.val)
      (ZArith.BinInt.Z.of_nat n.val) =
      ZArith.BinInt.Z.of_nat (a.val * 2 ^ n.val) by
    unfold ZArith.BinInt.Z.shiftl
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte]
    rw [Int.natCast_mul, Int.natCast_pow]
    rfl]
  rw [iagreeValReprOfNat]

private theorem test_iagreeShlTestbit_low (a n : Int.int) (i : Z)
    (hirange : ZArith.BinInt.Z.le z0 i ∧
      ZArith.BinInt.Z.lt i Int.zwordsize) :
    ZArith.BinInt.Z.lt i (Int.unsigned n) →
      Int.testbit (Int.shl a n) i = false := by
  have hn : Int.unsigned n = ZArith.BinInt.Z.of_nat n.val := by
    have hw : ZArith.BinInt.Z.le z0 (WordCore.unsigned n) := by
      have h := n.intrange.1
      change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (WordCore.unsigned n) at h
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (WordCore.unsigned n)
      omega
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
      (WordCore.unsigned n) hw).symm
  intro hlt
  rw [hn] at hlt
  have hnval :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.of_nat n.val) = Int.ofNat n.val := by
    rw [ZArith.BinInt.Z.of_nat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  cases i with
  | Zneg p =>
      exfalso
      have h := hirange.1
      change 0 ≤ -(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) at h
      have hp := test_posToNat_pos p
      have hp' : 0 < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      rw [iagreeTestbitZero, test_iagreeShlVal]
      have hlt' : (0 : Int) < Int.ofNat n.val := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (ZArith.BinInt.Z.of_nat n.val) at hlt
        rw [hnval] at hlt
        simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] using hlt
      have hnpos : 0 < n.val :=
        Int.natCast_pos.mp (by simpa only [Int.ofNat_eq_natCast] using hlt')
      have hpowbit : (a.val * 2 ^ n.val).testBit 0 = false := by
        rw [Nat.testBit_mul_two_pow]
        have hnot : ¬ n.val ≤ 0 := Nat.not_le.mpr hnpos
        simp [hnot]
      rw [Nat.testBit_mod_two_pow]
      have hw : decide (0 < Int.wordsize) = true := by decide
      rw [hw, Bool.true_and, hpowbit]
  | Zpos p =>
      rw [iagreeTestbitPos, test_iagreeShlVal]
      have hklt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < 32 := by
        have h := hirange.2
        change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
          Int.ofNat 32 at h
        exact Int.ofNat_lt.mp h
      have hkn : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < n.val := by
        have h := hlt
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (.Zpos p) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (ZArith.BinInt.Z.of_nat n.val) at h
        rw [hnval] at h
        change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
          Int.ofNat n.val at h
        exact Int.ofNat_lt.mp h
      have hpowbit :
          (a.val * 2 ^ n.val).testBit
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = false := by
        rw [Nat.testBit_mul_two_pow]
        have hnot : ¬ n.val ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
          Nat.not_le.mpr hkn
        simp [hnot]
      rw [Nat.testBit_mod_two_pow]
      change (decide (
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < 32) &&
        (a.val * 2 ^ n.val).testBit
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) = false
      have hkdec : decide (
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < 32) = true := by
        exact decide_eq_true hklt
      rw [hkdec, Bool.true_and, hpowbit]

private theorem test_iagreeTestbitOfNat (a : Int.int) (k : Nat) :
    Int.testbit a (ZArith.BinInt.Z.of_nat k) = a.val.testBit k := by
  cases k with
  | zero =>
      have hz : ZArith.BinInt.Z.of_nat 0 = z0 := by rfl
      rw [hz, iagreeTestbitZero]
  | succ k =>
      have hp : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (k + 1)) = k + 1 :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
          (Nat.succ_pos k)
      have hz : ZArith.BinInt.Z.of_nat (Nat.succ k) =
          .Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (k + 1)) := by
        rfl
      rw [hz, iagreeTestbitPos, hp]

private theorem test_iagreeShruVal (a n : Int.int) :
    (Int.shru a n).val = a.val / 2 ^ n.val := by
  change (WordCore.repr Int.wordsize
    (ZArith.BinInt.Z.shiftr (WordCore.unsigned a) (WordCore.unsigned n))).val = _
  have hunsigned (w : Int.int) :
      WordCore.unsigned w = ZArith.BinInt.Z.of_nat w.val := by
    have hw : ZArith.BinInt.Z.le z0 (WordCore.unsigned w) := by
      have h := w.intrange.1
      change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (WordCore.unsigned w) at h
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (WordCore.unsigned w)
      omega
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
      (WordCore.unsigned w) hw).symm
  rw [hunsigned a, hunsigned n]
  rw [show ZArith.BinInt.Z.shiftr (ZArith.BinInt.Z.of_nat a.val)
      (ZArith.BinInt.Z.of_nat n.val) =
      ZArith.BinInt.Z.of_nat (a.val / 2 ^ n.val) by
    unfold ZArith.BinInt.Z.shiftr
    simp only [ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte]
    rw [Int.natCast_ediv, Int.natCast_pow]
    rfl]
  rw [iagreeValReprOfNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (iagreeWordValLt a)

private theorem test_iagreeShruTestbit (a n : Int.int) (j : Z)
    (hirange : ZArith.BinInt.Z.le z0 j ∧
      ZArith.BinInt.Z.lt j Int.zwordsize) :
    Int.testbit (Int.shru a n) j =
      Int.testbit a (ZArith.BinInt.Z.add j (Int.unsigned n)) := by
  have hn : Int.unsigned n = ZArith.BinInt.Z.of_nat n.val := by
    have hw : ZArith.BinInt.Z.le z0 (WordCore.unsigned n) := by
      have h := n.intrange.1
      change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (WordCore.unsigned n) at h
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (WordCore.unsigned n)
      omega
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
      (WordCore.unsigned n) hw).symm
  have hnval :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.of_nat n.val) = Int.ofNat n.val := by
    rw [ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [hn]
  cases j with
  | Zneg p =>
      exfalso
      have h := hirange.1
      change 0 ≤ -(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) at h
      have hp := test_posToNat_pos p
      have hp' : 0 < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      rw [iagreeTestbitZero, test_iagreeShruVal]
      have hzadd : ZArith.BinInt.Z.add z0
          (ZArith.BinInt.Z.of_nat n.val) =
          ZArith.BinInt.Z.of_nat n.val := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [ZArith.BinInt.Z.add,
          ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          Int.zero_add]
      rw [hzadd, test_iagreeTestbitOfNat]
      have hbit := Nat.testBit_add a.val 0 n.val
      simpa using hbit.symm
  | Zpos p =>
      rw [iagreeTestbitPos, test_iagreeShruVal]
      have hklt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < 32 := by
        have h := hirange.2
        change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
          Int.ofNat 32 at h
        exact Int.ofNat_lt.mp h
      have hzadd : ZArith.BinInt.Z.add (.Zpos p)
          (ZArith.BinInt.Z.of_nat n.val) =
          ZArith.BinInt.Z.of_nat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + n.val) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [ZArith.BinInt.Z.add,
          ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change (Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) +
            Int.ofNat n.val =
          Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + n.val)
        simpa only [Int.ofNat_eq_natCast] using
          (Int.natCast_add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) n.val).symm
      rw [hzadd, test_iagreeTestbitOfNat]
      have hbit := Nat.testBit_add a.val
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) n.val
      simpa using hbit.symm

private theorem test_iagreeShlTestbit_high (a n : Int.int) (i : Z)
    (hirange : ZArith.BinInt.Z.le z0 i ∧
      ZArith.BinInt.Z.lt i Int.zwordsize)
    (hnot : ¬ ZArith.BinInt.Z.lt i (Int.unsigned n)) :
    Int.testbit (Int.shl a n) i =
      Int.testbit a (ZArith.BinInt.Z.sub i (Int.unsigned n)) := by
  have hn : Int.unsigned n = ZArith.BinInt.Z.of_nat n.val := by
    have hw : ZArith.BinInt.Z.le z0 (WordCore.unsigned n) := by
      have h := n.intrange.1
      change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (WordCore.unsigned n) at h
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (WordCore.unsigned n)
      omega
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
      (WordCore.unsigned n) hw).symm
  have hnval :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.of_nat n.val) = Int.ofNat n.val := by
    rw [ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [hn] at hnot
  cases i with
  | Zneg p =>
      exfalso
      have h := hirange.1
      change 0 ≤ -(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) at h
      have hp := test_posToNat_pos p
      have hp' : 0 < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      have hnzero : n.val = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hnpos
        have hlt : ZArith.BinInt.Z.lt z0
            (ZArith.BinInt.Z.of_nat n.val) := by
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (ZArith.BinInt.Z.of_nat n.val)
          rw [hnval]
          simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] using
            (show (0 : Int) < Int.ofNat n.val from
              Int.natCast_pos.mpr hnpos)
        exact hnot hlt
      rw [hn]
      have hnzero' : ZArith.BinInt.Z.of_nat n.val = z0 := by
        rw [hnzero]
        rfl
      have hj : ZArith.BinInt.Z.sub z0
          (ZArith.BinInt.Z.of_nat n.val) = z0 := by
        rw [hnzero']
        rfl
      rw [iagreeTestbitZero, test_iagreeShlVal]
      rw [Nat.testBit_mod_two_pow]
      rw [hj, iagreeTestbitZero]
      have hw : decide (0 < Int.wordsize) = true := by decide
      rw [hw, Bool.true_and]
      simp [hnzero]
  | Zpos p =>
      rw [iagreeTestbitPos, test_iagreeShlVal]
      have hklt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < 32 := by
        have h := hirange.2
        change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
          Int.ofNat 32 at h
        exact Int.ofNat_lt.mp h
      have hnotNat : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < n.val := by
        intro hkn
        apply hnot
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (.Zpos p) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (ZArith.BinInt.Z.of_nat n.val)
        rw [hnval]
        change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
          Int.ofNat n.val
        exact Int.ofNat_lt.mpr hkn
      have hnk : n.val ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        Nat.le_of_not_gt hnotNat
      have hj : ZArith.BinInt.Z.sub (.Zpos p)
          (ZArith.BinInt.Z.of_nat n.val) =
          ZArith.BinInt.Z.of_nat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p - n.val) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
          ZArith.BinInt.Z.of_nat]
        change (Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) -
            Int.ofNat n.val =
          Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p - n.val)
        simpa only [Int.ofNat_eq_natCast] using
          (Int.natCast_sub hnk).symm
      have hpowbit :
          (a.val * 2 ^ n.val).testBit
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) =
            (a.val).testBit
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p - n.val) := by
        rw [Nat.testBit_mul_two_pow]
        have hdec : decide (n.val ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = true :=
          decide_eq_true hnk
        rw [hdec, Bool.true_and]
      rw [Nat.testBit_mod_two_pow]
      have hkdec : decide (
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < 32) = true :=
        decide_eq_true hklt
      change (decide (
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < 32) &&
        (a.val * 2 ^ n.val).testBit
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
        Int.testbit a
          (ZArith.BinInt.Z.sub (.Zpos p) (Int.unsigned n))
      rw [hkdec, Bool.true_and, hpowbit, hn, hj]
      exact (test_iagreeTestbitOfNat a
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p - n.val)).symm

theorem iagree_shl : iagree_shlStatement := by
  intro x y m n h i hirange hmask
  have hnnonneg :
      0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Int.unsigned n) := by
    have h := n.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Int.unsigned n) at h
    omega
  by_cases hlt : ZArith.BinInt.Z.lt i (Int.unsigned n)
  · rw [test_iagreeShlTestbit_low x n i hirange hlt,
      test_iagreeShlTestbit_low y n i hirange hlt]
  ·
    have hsub0 : ZArith.BinInt.Z.le z0
        (ZArith.BinInt.Z.sub i (Int.unsigned n)) := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.sub i (Int.unsigned n))
      have hi0 := hirange.1
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i at hi0
      change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Int.unsigned n) at hlt
      simp only [ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 = 0 by rfl]
      omega
    have hsublt : ZArith.BinInt.Z.lt
        (ZArith.BinInt.Z.sub i (Int.unsigned n)) Int.zwordsize := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.sub i (Int.unsigned n)) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize
      have hi_lt := hirange.2
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize at hi_lt
      simp only [ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hwsize :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize =
            Int.ofNat 32 := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.of_nat 32) = Int.ofNat 32
        rw [ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rw [hwsize]
      rw [hwsize] at hi_lt
      omega
    have hjrange :
        ZArith.BinInt.Z.le z0 (ZArith.BinInt.Z.sub i (Int.unsigned n)) ∧
        ZArith.BinInt.Z.lt (ZArith.BinInt.Z.sub i (Int.unsigned n))
          Int.zwordsize :=
      ⟨hsub0, hsublt⟩
    have hadd : ZArith.BinInt.Z.add
        (ZArith.BinInt.Z.sub i (Int.unsigned n)) (Int.unsigned n) = i := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      omega
    rw [test_iagreeShlTestbit_high x n i hirange hlt,
      test_iagreeShlTestbit_high y n i hirange hlt]
    apply h (ZArith.BinInt.Z.sub i (Int.unsigned n)) hjrange
    rw [test_iagreeShruTestbit m n
      (ZArith.BinInt.Z.sub i (Int.unsigned n)) hjrange, hadd]
    exact hmask

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

private theorem test_iagreeBitsAbove (a : Int.int) (k : Z)
    (hk : ZArith.BinInt.Z.le Int.zwordsize k) :
    Int.testbit a k = false := by
  cases k with
  | Zneg p =>
      exfalso
      have h := hk
      have h32 : (0 : Int) < Int.ofNat 32 := by decide
      change (Int.ofNat 32 : Int) ≤
        -(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) at h
      have hp := test_posToNat_pos p
      have hp' : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exfalso
      have h := hk
      have h32 : (0 : Int) < Int.ofNat 32 := by decide
      change (Int.ofNat 32 : Int) ≤ 0 at h
      omega
  | Zpos p =>
      rw [iagreeTestbitPos]
      have h := hk
      change (Int.ofNat 32 : Int) ≤ Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hk' : 32 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        Int.ofNat_le.mp h
      have hpow : 2 ^ Int.wordsize ≤
          2 ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
        exact Nat.pow_le_pow_right (by decide) hk'
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (iagreeWordValLt a) hpow)

theorem iagree_shru : iagree_shruStatement := by
  intro x y m n h i hirange hmask
  have hnnonneg :
      0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Int.unsigned n) := by
    have h := n.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Int.unsigned n) at h
    omega
  by_cases hlt : ZArith.BinInt.Z.lt
      (ZArith.BinInt.Z.add i (Int.unsigned n)) Int.zwordsize
  · have hkrange :
        ZArith.BinInt.Z.le z0
            (ZArith.BinInt.Z.add i (Int.unsigned n)) ∧
        ZArith.BinInt.Z.lt
            (ZArith.BinInt.Z.add i (Int.unsigned n)) Int.zwordsize := by
      constructor
      · change 0 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (ZArith.BinInt.Z.add i (Int.unsigned n))
        have hi0 := hirange.1
        change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i at hi0
        simp only [ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        omega
      · exact hlt
    have hknlt : ¬ ZArith.BinInt.Z.lt
        (ZArith.BinInt.Z.add i (Int.unsigned n)) (Int.unsigned n) := by
      intro hbad
      have hi0 := hirange.1
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i at hi0
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.add i (Int.unsigned n)) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Int.unsigned n) at hbad
      simp only [ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hbad
      omega
    have hsub : ZArith.BinInt.Z.sub
        (ZArith.BinInt.Z.add i (Int.unsigned n)) (Int.unsigned n) = i := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      omega
    have hmask' : Int.testbit (Int.shl m n)
        (ZArith.BinInt.Z.add i (Int.unsigned n)) = true := by
      rw [test_iagreeShlTestbit_high m n
        (ZArith.BinInt.Z.add i (Int.unsigned n)) hkrange hknlt, hsub]
      exact hmask
    have hxy := h (ZArith.BinInt.Z.add i (Int.unsigned n)) hkrange hmask'
    rw [test_iagreeShruTestbit x n i hirange,
      test_iagreeShruTestbit y n i hirange]
    exact hxy
  · have hkabove : ZArith.BinInt.Z.le Int.zwordsize
        (ZArith.BinInt.Z.add i (Int.unsigned n)) := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.add i (Int.unsigned n))
      have hnot := hlt
      change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.add i (Int.unsigned n)) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize at hnot
      have hwsize :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize =
            Int.ofNat 32 := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.of_nat 32) = Int.ofNat 32
        rw [ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rw [hwsize] at hnot ⊢
      simp only [ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hnot ⊢
      omega
    rw [test_iagreeShruTestbit x n i hirange,
      test_iagreeShruTestbit y n i hirange,
      test_iagreeBitsAbove x _ hkabove,
      test_iagreeBitsAbove y _ hkabove]

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

private theorem test_ror_val (a n : Int.int) :
    (Int.ror a n).val =
      Nat.lor (a.val >>> (n.val % Int.wordsize))
        (a.val <<< (Int.wordsize - (n.val % Int.wordsize))) %
        (2 ^ Int.wordsize) := by
  change (WordCore.repr Int.wordsize
    (ZArith.BinInt.Z.of_nat
      (Nat.lor (a.val >>> (n.val % Int.wordsize))
        (a.val <<< (Int.wordsize - (n.val % Int.wordsize)))))).val = _
  rw [iagreeValReprOfNat]

private theorem test_ror_bit_nat (a n : Int.int) (k : Nat) (hk : k < 32) :
    Int.testbit (Int.ror a n) (ZArith.BinInt.Z.of_nat k) =
      a.val.testBit ((k + n.val % 32) % 32) := by
  rw [test_iagreeTestbitOfNat, test_ror_val]
  rw [Nat.testBit_mod_two_pow]
  have hkdec : decide (k < Int.wordsize) = true := by
    exact decide_eq_true hk
  rw [hkdec, Bool.true_and]
  change ((a.val >>> (n.val % 32)) |||
      (a.val <<< (32 - (n.val % 32)))).testBit k = _
  rw [Nat.testBit_or,
    Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  have haval : a.val < 2 ^ 32 := iagreeWordValLt a
  have hamod : n.val % 32 < 32 := Nat.mod_lt _ (by decide)
  by_cases hsum : k + n.val % 32 < 32
  · have hleft : ¬ k ≥ 32 - n.val % 32 := by omega
    have hleft' : decide (k ≥ 32 - n.val % 32) = false := by
      exact decide_eq_false hleft
    rw [hleft', Bool.false_and, Bool.or_false]
    rw [Nat.mod_eq_of_lt hsum]
    simp [Nat.add_comm]
  · have hsum' : 32 ≤ k + n.val % 32 := Nat.le_of_not_gt hsum
    have hleft : 32 - n.val % 32 ≤ k := by omega
    have hleft' : decide (k ≥ 32 - n.val % 32) = true := by
      exact decide_eq_true hleft
    rw [hleft', Bool.true_and]
    have hsum'' : 32 ≤ n.val % 32 + k := by omega
    have hpow : 2 ^ 32 ≤ 2 ^ (n.val % 32 + k) :=
      Nat.pow_le_pow_right (by decide) hsum''
    have hright : a.val.testBit (n.val % 32 + k) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le haval hpow)
    rw [hright, Bool.false_or]
    have hsub : k - (32 - n.val % 32) =
        k + n.val % 32 - 32 := by omega
    rw [hsub]
    rw [Nat.mod_eq_sub_mod hsum']
    have hdiff : k + n.val % 32 - 32 < 32 := by omega
    rw [Nat.mod_eq_of_lt hdiff]

private theorem test_rol_val (a n : Int.int) :
    (Int.rol a n).val =
      Nat.lor (a.val <<< (n.val % Int.wordsize))
        (a.val >>> (Int.wordsize - (n.val % Int.wordsize))) %
        (2 ^ Int.wordsize) := by
  change (WordCore.repr Int.wordsize
    (ZArith.BinInt.Z.of_nat
      (Nat.lor (a.val <<< (n.val % Int.wordsize))
        (a.val >>> (Int.wordsize - (n.val % Int.wordsize)))))).val = _
  rw [iagreeValReprOfNat]

private theorem test_rol_bit_nat (a n : Int.int) (k : Nat) (hk : k < 32) :
    Int.testbit (Int.rol a n) (ZArith.BinInt.Z.of_nat k) =
      a.val.testBit ((k + 32 - n.val % 32) % 32) := by
  rw [test_iagreeTestbitOfNat, test_rol_val]
  rw [Nat.testBit_mod_two_pow]
  have hkdec : decide (k < Int.wordsize) = true := by
    exact decide_eq_true hk
  rw [hkdec, Bool.true_and]
  change ((a.val <<< (n.val % 32)) |||
      (a.val >>> (32 - (n.val % 32)))).testBit k = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have haval : a.val < 2 ^ 32 := iagreeWordValLt a
  have hamod : n.val % 32 < 32 := Nat.mod_lt _ (by decide)
  by_cases hge : n.val % 32 ≤ k
  · have hge' : decide (k ≥ n.val % 32) = true := by
      exact decide_eq_true hge
    rw [hge', Bool.true_and]
    have hright : a.val.testBit (32 - n.val % 32 + k) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le haval (by
        apply Nat.pow_le_pow_right (by decide)
        omega))
    rw [hright, Bool.or_false]
    have hidx : k + 32 - n.val % 32 =
        32 + (k - n.val % 32) := by omega
    have hsub_lt : k - n.val % 32 < 32 := by omega
    rw [hidx, Nat.add_mod, Nat.mod_eq_of_lt hsub_lt]
    simp
    rw [Nat.mod_eq_of_lt hsub_lt]
  · have hge' : decide (k ≥ n.val % 32) = false := by
      exact decide_eq_false hge
    rw [hge', Bool.false_and, Bool.false_or]
    have hidx_lt : k + 32 - n.val % 32 < 32 := by omega
    rw [Nat.mod_eq_of_lt hidx_lt]
    have hidx : 32 - n.val % 32 + k =
        k + 32 - n.val % 32 := by omega
    rw [hidx]

private theorem test_rot_index_back (k a : Nat) (hk : k < 32) (ha : a < 32) :
    (((k + 32 - a) % 32 + a) % 32) = k := by
  by_cases hge : a ≤ k
  · have hidx : k + 32 - a = 32 + (k - a) := by omega
    have hsub_lt : k - a < 32 := by omega
    have hinner : (32 + (k - a)) % 32 = k - a := by
      rw [Nat.add_mod]
      simp
      exact hsub_lt
    rw [hidx, hinner, Nat.sub_add_cancel hge,
      Nat.mod_eq_of_lt hk]
  · have hidx_lt : k + 32 - a < 32 := by omega
    rw [Nat.mod_eq_of_lt hidx_lt]
    have hidx : k + 32 - a + a = 32 + k := by omega
    rw [hidx, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hk]

private theorem test_iagree_rol_at (p q m amount : Int.int)
    (h : iagree p q (Int.ror m amount)) (k : Nat) (hk : k < 32)
    (hmask : m.val.testBit k = true) :
    Int.testbit (Int.rol p amount) (ZArith.BinInt.Z.of_nat k) =
      Int.testbit (Int.rol q amount) (ZArith.BinInt.Z.of_nat k) := by
  let a := amount.val % 32
  let j := (k + 32 - a) % 32
  have ha : a < 32 := by
    exact Nat.mod_lt _ (by decide)
  have hj : j < 32 := by
    exact Nat.mod_lt _ (by decide)
  have hback : (j + a) % 32 = k := by
    dsimp [j]
    exact test_rot_index_back k a hk ha
  have hmask' : Int.testbit (Int.ror m amount)
      (ZArith.BinInt.Z.of_nat j) = true := by
    rw [test_ror_bit_nat m amount j hj]
    change m.val.testBit ((j + amount.val % 32) % 32) = true
    rw [show amount.val % 32 = a by rfl, hback]
    exact hmask
  have hjrange :
      ZArith.BinInt.Z.le z0 (ZArith.BinInt.Z.of_nat j) ∧
      ZArith.BinInt.Z.lt (ZArith.BinInt.Z.of_nat j) Int.zwordsize := by
    constructor
    · change 0 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (ZArith.BinInt.Z.of_nat j)
      simp only [ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.natCast_nonneg _
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.of_nat j) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize
      have hwsize :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize =
            Int.ofNat 32 := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.of_nat 32) = Int.ofNat 32
        rw [ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rw [hwsize]
      simp only [ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.ofNat_lt.mpr hj
  have hsrc := h (ZArith.BinInt.Z.of_nat j) hjrange hmask'
  rw [test_iagreeTestbitOfNat p j, test_iagreeTestbitOfNat q j] at hsrc
  rw [test_rol_bit_nat p amount k hk, test_rol_bit_nat q amount k hk]
  change p.val.testBit j = q.val.testBit j
  exact hsrc

private theorem test_iagree_rol : iagree_rolStatement := by
  intro p q m amount h i hirange hmask
  cases i with
  | Zneg r =>
      exfalso
      have h0 := hirange.1
      change 0 ≤
        -(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r)) at h0
      have hr : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r) := by
        exact Int.natCast_pos.mpr
          (test_posToNat_pos r)
      omega
  | Z0 =>
      have hm : m.val.testBit 0 = true := by
        simpa [iagreeTestbitZero] using hmask
      rw [iagreeTestbitZero, iagreeTestbitZero]
      have ht := test_iagree_rol_at p q m amount h 0 (by decide) hm
      rw [test_iagreeTestbitOfNat (Int.rol p amount) 0,
        test_iagreeTestbitOfNat (Int.rol q amount) 0] at ht
      exact ht
  | Zpos r =>
      have hkZ := hirange.2
      change (Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r) : Int) <
        Int.ofNat 32 at hkZ
      have hk : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r < 32 :=
        Int.ofNat_lt.mp hkZ
      have hm : m.val.testBit
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r) = true := by
        simpa [iagreeTestbitPos] using hmask
      rw [iagreeTestbitPos, iagreeTestbitPos]
      have ht := test_iagree_rol_at p q m amount h
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r) hk hm
      rw [test_iagreeTestbitOfNat (Int.rol p amount)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r),
        test_iagreeTestbitOfNat (Int.rol q amount)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r)] at ht
      exact ht

private theorem test_rot_index_forward (k a : Nat) (hk : k < 32) (ha : a < 32) :
    (((k + a) % 32 + 32 - a) % 32) = k := by
  by_cases hsum : k + a < 32
  · rw [Nat.mod_eq_of_lt hsum]
    have hidx : k + a + 32 - a = 32 + k := by omega
    rw [hidx, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hk]
  · have hsum' : 32 ≤ k + a := Nat.le_of_not_gt hsum
    have hsub_lt : k + a - 32 < 32 := by omega
    rw [Nat.mod_eq_sub_mod hsum', Nat.mod_eq_of_lt hsub_lt]
    have hidx : k + a - 32 + 32 - a = k := by omega
    rw [hidx, Nat.mod_eq_of_lt hk]

private theorem test_iagree_ror_at (p q m amount : Int.int)
    (h : iagree p q (Int.rol m amount)) (k : Nat) (hk : k < 32)
    (hmask : m.val.testBit k = true) :
    Int.testbit (Int.ror p amount) (ZArith.BinInt.Z.of_nat k) =
      Int.testbit (Int.ror q amount) (ZArith.BinInt.Z.of_nat k) := by
  let a := amount.val % 32
  let j := (k + a) % 32
  have ha : a < 32 := by
    exact Nat.mod_lt _ (by decide)
  have hj : j < 32 := by
    exact Nat.mod_lt _ (by decide)
  have hback : (j + 32 - a) % 32 = k := by
    dsimp [j]
    exact test_rot_index_forward k a hk ha
  have hmask' : Int.testbit (Int.rol m amount)
      (ZArith.BinInt.Z.of_nat j) = true := by
    rw [test_rol_bit_nat m amount j hj]
    change m.val.testBit ((j + 32 - amount.val % 32) % 32) = true
    rw [show amount.val % 32 = a by rfl, hback]
    exact hmask
  have hjrange :
      ZArith.BinInt.Z.le z0 (ZArith.BinInt.Z.of_nat j) ∧
      ZArith.BinInt.Z.lt (ZArith.BinInt.Z.of_nat j) Int.zwordsize := by
    constructor
    · change 0 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (ZArith.BinInt.Z.of_nat j)
      simp only [ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.natCast_nonneg _
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.of_nat j) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize
      have hwsize :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Int.zwordsize =
            Int.ofNat 32 := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (ZArith.BinInt.Z.of_nat 32) = Int.ofNat 32
        rw [ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rw [hwsize]
      simp only [ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.ofNat_lt.mpr hj
  have hsrc := h (ZArith.BinInt.Z.of_nat j) hjrange hmask'
  rw [test_iagreeTestbitOfNat p j, test_iagreeTestbitOfNat q j] at hsrc
  rw [test_ror_bit_nat p amount k hk, test_ror_bit_nat q amount k hk]
  change p.val.testBit j = q.val.testBit j
  exact hsrc

theorem iagree_ror : iagree_rorStatement := by
  intro p q m amount h i hirange hmask
  cases i with
  | Zneg r =>
      exfalso
      have h0 := hirange.1
      change 0 ≤
        -(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r)) at h0
      have hr : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r) := by
        exact Int.natCast_pos.mpr
          (test_posToNat_pos r)
      omega
  | Z0 =>
      have hm : m.val.testBit 0 = true := by
        simpa [iagreeTestbitZero] using hmask
      rw [iagreeTestbitZero, iagreeTestbitZero]
      have ht := test_iagree_ror_at p q m amount h 0 (by decide) hm
      rw [test_iagreeTestbitOfNat (Int.ror p amount) 0,
        test_iagreeTestbitOfNat (Int.ror q amount) 0] at ht
      exact ht
  | Zpos r =>
      have hkZ := hirange.2
      change (Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r) : Int) <
        Int.ofNat 32 at hkZ
      have hk : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r < 32 :=
        Int.ofNat_lt.mp hkZ
      have hm : m.val.testBit
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r) = true := by
        simpa [iagreeTestbitPos] using hmask
      rw [iagreeTestbitPos, iagreeTestbitPos]
      have ht := test_iagree_ror_at p q m amount h
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r) hk hm
      rw [test_iagreeTestbitOfNat (Int.ror p amount)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r),
        test_iagreeTestbitOfNat (Int.ror q amount)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r)] at ht
      exact ht

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private theorem local_unsigned_intOfZ_eqmod (a : Int.int) :
    intOfZ (Int.unsigned a) = Int.ofNat a.val := by
  have ha0 : ZArith.BinInt.Z.le Z0 (Int.unsigned a) := by
    change 0 ≤ intOfZ a.intval
    have h := a.intrange.1
    change (-1 : Int) < intOfZ a.intval at h
    omega
  have hz := ZArith.Znat.Z2Nat.id (Int.unsigned a) ha0
  have hz' := congrArg intOfZ hz
  simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hz'
  symm
  exact hz'

private theorem local_size_range_eqmod (m : Int.int) :
    ZArith.BinInt.Z.le Z0 (Int.size m) ∧
      ZArith.BinInt.Z.le (Int.size m) Int.zwordsize := by
  have hval : m.val < 2 ^ Int.wordsize := by
    exact iagreeWordValLt m
  have hwz : intOfZ Int.zwordsize = Int.ofNat 32 := by
    change intOfZ (ZArith.BinInt.Z.of_nat 32) = Int.ofNat 32
    rw [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  constructor
  · change ZArith.BinInt.Z.le Z0
      (CompCert4Lean.Lib.Zbits.Zsize (Int.unsigned m))
    cases hu : CompCert4Lean.Lib.Integers.Int.unsigned m with
    | Z0 =>
        simp only [CompCert4Lean.Lib.Zbits.Zsize, hu]
        change 0 ≤ intOfZ Z0
        simp only [intOfZ]
        omega
    | Zpos p =>
        simp only [CompCert4Lean.Lib.Zbits.Zsize, hu]
        change 0 ≤ intOfZ (Zpos (PArith.BinPos.Pos.size p))
        simp only [intOfZ]
        exact Int.natCast_nonneg _
    | Zneg p =>
        simp only [CompCert4Lean.Lib.Zbits.Zsize, hu]
        change 0 ≤ intOfZ Z0
        simp only [intOfZ]
        omega
  · change ZArith.BinInt.Z.le (CompCert4Lean.Lib.Zbits.Zsize (Int.unsigned m))
      Int.zwordsize
    cases hu : CompCert4Lean.Lib.Integers.Int.unsigned m with
    | Z0 =>
        simp only [CompCert4Lean.Lib.Zbits.Zsize, hu]
        change 0 ≤ Int.ofNat 32
        exact Int.natCast_nonneg _
    | Zpos p =>
        simp only [CompCert4Lean.Lib.Zbits.Zsize, hu]
        have hup := congrArg intOfZ hu
        rw [local_unsigned_intOfZ_eqmod m] at hup
        simp only [intOfZ] at hup
        have hpval : posToNat p = m.val := Int.ofNat.inj hup.symm
        have hpbound : posToNat p < 2 ^ Int.wordsize := by
          simpa [hpval] using hval
        have hpne : posToNat p ≠ 0 :=
          Nat.ne_of_gt (posToNat_positive p)
        have hlog : Nat.log2 (posToNat p) < Int.wordsize :=
          (Nat.log2_lt hpne).2 hpbound
        have hw : Int.wordsize = 32 := by rfl
        rw [hw] at hlog
        change intOfZ (Zpos (PArith.BinPos.Pos.size p)) ≤ intOfZ Int.zwordsize
        have hsizepos :
            posToNat (PArith.BinPos.Pos.size p) =
              Nat.log2 (posToNat p) + 1 := by
          unfold PArith.BinPos.Pos.size
          exact posToNat_posOfNat (by omega)
        change Int.ofNat (posToNat (PArith.BinPos.Pos.size p)) ≤ Int.ofNat 32
        rw [hsizepos]
        change Int.ofNat (Nat.log2 (posToNat p) + 1) ≤ Int.ofNat 32
        apply (Int.ofNat_le).2
        omega
    | Zneg p =>
        simp only [CompCert4Lean.Lib.Zbits.Zsize, hu]
        change 0 ≤ Int.ofNat 32
        exact Int.natCast_nonneg _

private theorem local_zero_ext_val_eqmod (n : Z) (a : Int.int)
    (hn : ZArith.BinInt.Z.le Z0 n) :
    (Int.zero_ext n a).val =
      (a.val % (2 ^ ZArith.BinInt.Z.to_nat n)) % (2 ^ Int.wordsize) := by
  run_tac
    let lctx ← getLCtx
    let nF := (lctx.findFromUserName? `n).get!
    let aF := (lctx.findFromUserName? `a).get!
    let hnF := (lctx.findFromUserName? `hn).get!
    let nE := mkFVar nF.fvarId
    let aE := mkFVar aF.fvarId
    let hnE := mkFVar hnF.fvarId
    let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
    let base := Name.num p 0
    let nm := "CompCert4Lean.Lib.Integers.Int.zero_ext_val" |>.splitOn "." |>.foldl Name.str base
    let e ← mkAppM nm #[nE, aE, hnE]
    closeMainGoal Name.anonymous e

private theorem local_mone_testbit (i : Z)
    (hi : ZArith.BinInt.Z.le Z0 i ∧
      ZArith.BinInt.Z.lt i Int.zwordsize) :
    Int.testbit Int.mone i = true := by
  cases i with
  | Zneg p =>
      exfalso
      have h0 := hi.1
      change 0 ≤ -(Int.ofNat (posToNat p)) at h0
      have hp : (0 : Int) < Int.ofNat (posToNat p) :=
        Int.natCast_pos.mpr (posToNat_positive p)
      omega
  | Z0 =>
      rfl
  | Zpos p =>
      rw [iagreeTestbitPos]
      change (2 ^ Int.wordsize - 1).testBit (posToNat p) = true
      rw [Nat.testBit_two_pow_sub_one]
      have hpz := hi.2
      change (Int.ofNat (posToNat p) : Int) < Int.ofNat 32 at hpz
      have hp : posToNat p < Int.wordsize := Int.ofNat_lt.mp hpz
      simp [hp]

private theorem local_complete_mask_testbit (m : Int.int) (i : Z)
    (hi : ZArith.BinInt.Z.le Z0 i ∧
      ZArith.BinInt.Z.lt i (Int.size m)) :
    Int.testbit (complete_mask m) i = true := by
  have hs := local_size_range_eqmod m
  have hv := local_zero_ext_val_eqmod (Int.size m) Int.mone hs.1
  unfold complete_mask
  cases i with
  | Zneg p =>
      exfalso
      have h0 := hi.1
      change 0 ≤ -(Int.ofNat (posToNat p)) at h0
      have hp : (0 : Int) < Int.ofNat (posToNat p) :=
        Int.natCast_pos.mpr (posToNat_positive p)
      omega
  | Z0 =>
      rw [iagreeTestbitZero]
      rw [hv]
      change (((2 ^ Int.wordsize - 1) %
        (2 ^ ZArith.BinInt.Z.to_nat (Int.size m))) %
          (2 ^ Int.wordsize)).testBit 0 = true
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      have hpos : ZArith.BinInt.Z.lt Z0 (Int.size m) := hi.2
      change 0 < intOfZ (Int.size m) at hpos
      have hnat := ZArith.Znat.Z2Nat.id (Int.size m) hs.1
      have hnat' := congrArg intOfZ hnat
      simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hnat'
      have hkpos : 0 < ZArith.BinInt.Z.to_nat (Int.size m) := by
        have hkpos' : (0 : Int) < Int.ofNat
            (ZArith.BinInt.Z.to_nat (Int.size m)) := by
          rw [hnat']
          exact hpos
        exact Int.ofNat_lt.mp hkpos'
      simp [Int.wordsize, hkpos]
  | Zpos p =>
      have hpz := hi.2
      have hsize := hs.1
      rw [iagreeTestbitPos]
      rw [hv]
      change (((2 ^ Int.wordsize - 1) %
        (2 ^ ZArith.BinInt.Z.to_nat (Int.size m))) %
          (2 ^ Int.wordsize)).testBit (posToNat p) = true
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      have hk : posToNat p < ZArith.BinInt.Z.to_nat (Int.size m) := by
        change (Int.ofNat (posToNat p) : Int) < intOfZ (Int.size m) at hpz
        have hnat := ZArith.Znat.Z2Nat.id (Int.size m) hsize
        have hnat' := congrArg intOfZ hnat
        simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hnat'
        have hpz' : (Int.ofNat (posToNat p) : Int) <
            Int.ofNat (ZArith.BinInt.Z.to_nat (Int.size m)) := by
          rw [hnat']
          exact hpz
        exact Int.ofNat_lt.mp hpz'
      have hword : posToNat p < Int.wordsize := by
        have hpword := Int.lt_of_lt_of_le hpz hs.2
        change (Int.ofNat (posToNat p) : Int) < Int.ofNat 32 at hpword
        exact Int.ofNat_lt.mp hpword
      simp [hk, hword]

private theorem local_unsigned_testbit (a : Int.int) (i : Z)
    (hi : ZArith.BinInt.Z.le Z0 i) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.testbit
        (Int.unsigned a) i = Int.testbit a i := by
  have hu := local_unsigned_intOfZ_eqmod a
  have huZ : Int.unsigned a =
      ZArith.BinInt.Z.of_nat a.val := by
    apply intOfZ_injective
    rw [hu]
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  have hpar (k : Nat) : decide (k % 2 = 0) = !decide (k % 2 = 1) := by
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> simp [hk]
  cases i with
  | Zneg p =>
      have h0 := hi
      change 0 ≤ -(Int.ofNat (posToNat p)) at h0
      have hp : (0 : Int) < Int.ofNat (posToNat p) :=
        Int.natCast_pos.mpr (posToNat_positive p)
      omega
  | Z0 =>
      rw [huZ]
      rw [iagreeTestbitZero]
      cases h : a.val with
      | zero =>
          rw [show ZArith.BinInt.Z.of_nat 0 = Z0 by rfl]
          simp [ZArith.BinInt.Z.testbit, ZArith.BinInt.Z.odd,
            ZArith.BinInt.Z.even, ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, h]
      | succ n =>
          rw [show ZArith.BinInt.Z.of_nat (n + 1) =
            Zpos (posOfNat (n + 1)) by rfl]
          simp only [ZArith.BinInt.Z.testbit, ZArith.BinInt.Z.odd,
            ZArith.BinInt.Z.even,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
          have hpnat : posToNat (posOfNat (n + 1)) = n + 1 :=
            posToNat_posOfNat (Nat.succ_pos n)
          have habs :
              (Int.ofNat (posToNat (posOfNat (n + 1)))).natAbs = n + 1 := by
            rw [hpnat]
            rfl
          simp only [habs]
          have hpar' := congrArg Bool.not (hpar (n + 1))
          simpa [Nat.testBit_zero] using hpar'
  | Zpos p =>
      rw [huZ]
      rw [iagreeTestbitPos]
      cases h : a.val with
      | zero =>
          simp [ZArith.BinInt.Z.testbit, ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt, h]
      | succ n =>
          simp [ZArith.BinInt.Z.testbit, ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt, h,
            posToNat_posOfNat]

theorem iagree_eqmod : iagree_eqmodStatement := by
  intro x y m hxy
  have hs := local_size_range_eqmod m
  let n := ZArith.BinInt.Z.to_nat (Int.size m)
  have hsize : ZArith.BinInt.Z.of_nat n = Int.size m := by
    dsimp [n]
    exact ZArith.Znat.Z2Nat.id (Int.size m) hs.1
  have hpow : CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_power_nat n =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_p (Int.size m) := by
    rw [CompCert4Lean.Lib.Coqlib.two_power_nat_two_p, hsize]
  rw [← hpow]
  apply CompCert4Lean.Lib.Zbits.eqmod_same_bits n
  intro i hi
  have hiSize : ZArith.BinInt.Z.lt i (Int.size m) := by
    rw [← hsize]
    exact hi.2
  have hiWord : ZArith.BinInt.Z.lt i Int.zwordsize := by
    change intOfZ i < intOfZ (Int.size m) at hiSize
    have hs2 := hs.2
    change intOfZ (Int.size m) ≤ intOfZ Int.zwordsize at hs2
    change intOfZ i < intOfZ Int.zwordsize
    omega
  have hmask := local_complete_mask_testbit m i ⟨hi.1, hiSize⟩
  have hbits := hxy i ⟨hi.1, hiWord⟩ hmask
  rw [← local_unsigned_testbit x i hi.1,
    ← local_unsigned_testbit y i hi.1] at hbits
  exact hbits

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

theorem eq_same_bits64 : eq_same_bits64Statement := by
  intro i x y h
  subst y
  rfl

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private def lagreePrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem lagreeValReprOfNat (bits n : Nat) :
    (WordCore.repr bits (ZArith.BinInt.Z.of_nat n)).val = n % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let nF := (lctx.findFromUserName? `n).get!
    let bitsE := mkFVar bitsF.fvarId
    let nE := mkFVar nF.fvarId
    let z := mkApp (mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat) nE
    let e1 := mkApp2 (mkConst (lagreePrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")) bitsE z
    let e2 := mkApp2 (mkConst (lagreePrivateName "CompCert4Lean.Lib.Integers.WordCore.residue_zOfNat")) bitsE nE
    let t1 ← inferType e1
    let t2 ← inferType e2
    let (α, lhs, mid) := match_expr t1 with
      | _root_.Eq α lhs mid => (α, lhs, mid)
      | _ => panic! "unexpected first equality"
    let (_, _, rhs) := match_expr t2 with
      | _root_.Eq _ middle rhs => (α, middle, rhs)
      | _ => panic! "unexpected second equality"
    let eqtrans := mkConst ``Eq.trans [.succ .zero]
    let e := mkAppN eqtrans #[α, lhs, mid, rhs, e1, e2]
    closeMainGoal Name.anonymous e

private theorem lagreeWordValLt (a : Int64.int) :
    a.val < 2 ^ Int64.wordsize := by
  run_tac
    let lctx ← getLCtx
    let aF := (lctx.findFromUserName? `a).get!
    let aE := mkFVar aF.fvarId
    let e ← mkAppM (lagreePrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt") #[aE]
    closeMainGoal Name.anonymous e

private theorem lagreeAndVal (a b : Int64.int) :
    (Int64.and a b).val = Nat.land a.val b.val := by
  change (WordCore.repr Int64.wordsize
    (ZArith.BinInt.Z.of_nat (Nat.land a.val b.val))).val = _
  rw [lagreeValReprOfNat]
  change Nat.land a.val b.val % (2 ^ Int64.wordsize) = Nat.land a.val b.val
  apply Nat.mod_eq_of_lt
  exact Nat.and_lt_two_pow _ (lagreeWordValLt b)

private theorem lagreeTestbitPos (a : Int64.int) (p : positive) :
    Int64.testbit a (.Zpos p) = a.val.testBit (posToNat p) := by
  simp only [Int64.testbit, WordCore.testbit]
  run_tac
    let lctx ← getLCtx
    let aF := (lctx.findFromUserName? `a).get!
    let pF := (lctx.findFromUserName? `p).get!
    let aE := mkFVar aF.fvarId
    let pE := mkFVar pF.fvarId
    let e ← mkAppM
      (lagreePrivateName "CompCert4Lean.Lib.Integers.WordCore.positiveToNat_eq_posToNat") #[pE]
    let natTy := mkConst ``Nat
    let aval ← mkAppM ``CompCert4Lean.Lib.Integers.WordCore.Word.val #[aE]
    let f := mkLambda `k BinderInfo.default natTy
      (mkApp2 (mkConst ``Nat.testBit) aval (mkBVar 0))
    let ce ← mkAppM ``congrArg #[f, e]
    closeMainGoal Name.anonymous ce

private theorem lagreeTestbitZero (a : Int64.int) :
    Int64.testbit a .Z0 = a.val.testBit 0 := by
  rfl

private theorem lagreeNatLandTestbit (a b k : Nat) :
    (Nat.land a b).testBit k = (a.testBit k && b.testBit k) := by
  change (a &&& b).testBit k = _
  exact Nat.testBit_and a b k

theorem lagree_and_eq : lagree_and_eqStatement := by
  intro x y mask
  constructor
  · intro hagree
    apply WordCore.ext_of_val_eq
    apply Nat.eq_of_testBit_eq
    intro k
    rw [lagreeAndVal, lagreeAndVal, lagreeNatLandTestbit, lagreeNatLandTestbit]
    cases k with
    | zero =>
        by_cases hmask : mask.val.testBit 0 = true
        · have hxy := hagree (.Z0) (by
            constructor
            · change (0 : Int) ≤ 0
              omega
            · change (0 : Int) < 64
              omega) (by
                rw [lagreeTestbitZero]
                exact hmask)
          rw [lagreeTestbitZero, lagreeTestbitZero] at hxy
          simp [hmask, hxy]
        · have hmask' : mask.val.testBit 0 = false := Bool.eq_false_iff.mpr hmask
          simp [hmask']
    | succ k =>
        let p := posOfNat (Nat.succ k)
        have hp : posToNat p = Nat.succ k :=
          posToNat_posOfNat (Nat.succ_pos k)
        by_cases hlt : Nat.succ k < 64
        · by_cases hmask : mask.val.testBit (Nat.succ k) = true
          · have hxy := hagree (.Zpos p) (by
              constructor
              · change (0 : Int) ≤ Int.ofNat (posToNat p)
                exact Int.natCast_nonneg _
              · change (Int.ofNat (posToNat p) : Int) < Int.ofNat 64
                rw [hp]
                exact Int.ofNat_lt.mpr hlt) (by
                  rw [lagreeTestbitPos, hp]
                  exact hmask)
            rw [lagreeTestbitPos, lagreeTestbitPos, hp] at hxy
            simp [hmask, hxy]
          · have hmask' : mask.val.testBit (Nat.succ k) = false :=
              Bool.eq_false_iff.mpr hmask
            simp [hmask']
        · have hpow : 2 ^ Int64.wordsize ≤ 2 ^ (Nat.succ k) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hlt)
          have hmasklt : mask.val < 2 ^ (Nat.succ k) :=
            Nat.lt_of_lt_of_le (lagreeWordValLt mask) hpow
          have hmask' : mask.val.testBit (Nat.succ k) = false :=
            Nat.testBit_lt_two_pow hmasklt
          simp [hmask']
  · intro hand i hirange hmask
    have hval := congrArg WordCore.Word.val hand
    rw [lagreeAndVal, lagreeAndVal] at hval
    cases i with
    | Zneg p =>
        cases hmask
    | Z0 =>
        have hm : mask.val.testBit 0 = true := by
          simpa [lagreeTestbitZero] using hmask
        have hbit := congrArg (fun n : Nat => n.testBit 0) hval
        rw [lagreeNatLandTestbit, lagreeNatLandTestbit] at hbit
        have hxy : x.val.testBit 0 = y.val.testBit 0 := by
          simpa [hm] using hbit
        simpa [lagreeTestbitZero] using hxy
    | Zpos p =>
        have hm : mask.val.testBit (posToNat p) = true := by
          simpa [lagreeTestbitPos] using hmask
        have hbit := congrArg (fun n : Nat => n.testBit (posToNat p)) hval
        rw [lagreeNatLandTestbit, lagreeNatLandTestbit] at hbit
        have hxy : x.val.testBit (posToNat p) = y.val.testBit (posToNat p) := by
          simpa [hm] using hbit
        simpa [lagreeTestbitPos] using hxy

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Lib.Integers

theorem lagree_mone : lagree_moneStatement := by
  intro p q h
  have hand : Int64.and p Int64.mone = Int64.and q Int64.mone :=
    (lagree_and_eq p q Int64.mone).mp h
  have hval := congrArg (fun z => z.val) hand
  rw [lagreeAndVal, lagreeAndVal] at hval
  have hp : p.val < 2 ^ Int64.wordsize := lagreeWordValLt p
  have hq : q.val < 2 ^ Int64.wordsize := lagreeWordValLt q
  have hmone : Int64.mone.val = 2 ^ Int64.wordsize - 1 := by
    rfl
  rw [hmone, Nat.land_eq,
    Nat.and_two_pow_sub_one_of_lt_two_pow hp,
    Nat.land_eq,
    Nat.and_two_pow_sub_one_of_lt_two_pow hq] at hval
  exact WordCore.ext_of_val_eq hval

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Lib.Integers

private theorem lagreeAndAssocFinal (a b c : Int64.int) :
    Int64.and (Int64.and a b) c = Int64.and a (Int64.and b c) := by
  apply WordCore.ext_of_val_eq
  rw [lagreeAndVal, lagreeAndVal, lagreeAndVal, lagreeAndVal]
  rw [Nat.land_eq, Nat.land_eq, Nat.land_eq, Nat.land_eq]
  exact Nat.and_assoc _ _ _

private theorem lagreeAndCommFinal (a b : Int64.int) :
    Int64.and a b = Int64.and b a := by
  apply WordCore.ext_of_val_eq
  rw [lagreeAndVal, lagreeAndVal]
  rw [Nat.land_eq, Nat.land_eq]
  exact Nat.and_comm _ _

theorem lagree_and : lagree_andStatement := by
  intro x y n m h
  apply (lagree_and_eq (Int64.and x n) (Int64.and y n) m).mpr
  have hh : Int64.and x (Int64.and m n) = Int64.and y (Int64.and m n) :=
    (lagree_and_eq x y (Int64.and m n)).mp h
  calc
    Int64.and (Int64.and x n) m = Int64.and x (Int64.and n m) :=
      lagreeAndAssocFinal x n m
    _ = Int64.and x (Int64.and m n) := by rw [lagreeAndCommFinal n m]
    _ = Int64.and y (Int64.and m n) := hh
    _ = Int64.and y (Int64.and n m) := by rw [lagreeAndCommFinal m n]
    _ = Int64.and (Int64.and y n) m := (lagreeAndAssocFinal y n m).symm

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

open CompCert4Lean.Lib.Integers
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem lagreeNotValFinal (a : Int64.int) :
    (Int64.not a).val = Nat.xor a.val (2 ^ Int64.wordsize - 1) := by
  change (WordCore.repr Int64.wordsize
    (ZArith.BinInt.Z.of_nat (Nat.xor a.val (2 ^ Int64.wordsize - 1)))).val = _
  rw [lagreeValReprOfNat]
  apply Nat.mod_eq_of_lt
  apply Nat.xor_lt_two_pow
  · exact lagreeWordValLt a
  · have hp : 0 < 2 ^ Int64.wordsize := Nat.two_pow_pos _
    omega

private theorem lagreeNotTestbitFinal (a : Int64.int) (i : Z)
    (hirange : ZArith.BinInt.Z.le z0 i ∧
      ZArith.BinInt.Z.lt i Int64.zwordsize) :
    Int64.testbit (Int64.not a) i = !(Int64.testbit a i) := by
  cases i with
  | Zneg p =>
      exfalso
      have h := hirange.1
      change (0 : Int) ≤ -Int.ofNat (posToNat p) at h
      have hp : (0 : Int) < Int.ofNat (posToNat p) := by
        exact Int.natCast_pos.mpr (posToNat_positive p)
      omega
  | Z0 =>
      rw [lagreeTestbitZero (Int64.not a), lagreeTestbitZero a]
      rw [lagreeNotValFinal]
      rw [Nat.xor_eq]
      rw [Nat.testBit_xor]
      have hmask : (2 ^ Int64.wordsize - 1).testBit 0 = true := by
        rw [Nat.testBit_two_pow_sub_one]
        decide
      simp [hmask]
  | Zpos p =>
      rw [lagreeTestbitPos (Int64.not a) p, lagreeTestbitPos a p]
      rw [lagreeNotValFinal]
      rw [Nat.xor_eq]
      rw [Nat.testBit_xor]
      have hkZ := hirange.2
      change Int.ofNat (posToNat p) < Int.ofNat Int64.wordsize at hkZ
      have hk : posToNat p < Int64.wordsize := Int.ofNat_lt.mp hkZ
      have hmask : (2 ^ Int64.wordsize - 1).testBit (posToNat p) = true := by
        rw [Nat.testBit_two_pow_sub_one]
        simp [hk]
      simp [hmask]

theorem lagree_not : lagree_notStatement := by
  intro x y m h i hirange hmask
  rw [lagreeNotTestbitFinal x i hirange, lagreeNotTestbitFinal y i hirange]
  exact congrArg Bool.not (h i hirange hmask)

private theorem lagreeNotInvolutiveFinal (a : Int64.int) :
    Int64.not (Int64.not a) = a := by
  apply WordCore.ext_of_val_eq
  rw [lagreeNotValFinal, lagreeNotValFinal]
  rw [Nat.xor_eq, Nat.xor_eq]
  rw [Nat.xor_assoc]
  simp

theorem lagree_not' : lagree_not'Statement := by
  intro x y m h i hirange hmask
  have h' : lagree (Int64.not (Int64.not x)) (Int64.not (Int64.not y)) m :=
    lagree_not (Int64.not x) (Int64.not y) m h
  have hbits := h' i hirange hmask
  rw [lagreeNotInvolutiveFinal, lagreeNotInvolutiveFinal] at hbits
  exact hbits

end CompCert4Lean.Backend.NeedDomain

namespace CompCert4Lean.Backend.NeedDomain

theorem lagree_bitwise_binop : lagree_bitwise_binopStatement := by
  intro sem f hsem x1 x2 y1 y2 m h1 h2 i hi hm
  rw [hsem x1 x2 i hi, hsem y1 y2 i hi]
  simp [h1 i hi hm, h2 i hi hm]

end CompCert4Lean.Backend.NeedDomain
