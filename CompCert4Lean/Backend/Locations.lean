import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Ordered
import CompCert4Lean.X86.Machregs

/-!
# Machine locations

Definition-bearing translation of CompCert's `backend/Locations.v`.  Proofs
assigned to the later proof-migration phase are represented by exact
transparent proposition descriptors.  The two packet-owned applications of
`OrderedIndexed` are exposed through their generated public surfaces without
reintroducing the excluded source functor-argument modules.
-/

namespace CompCert4Lean.Backend.Locations

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Machregs

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev OrderedCompare {X : Type} (lt eq : X → X → Prop) (x y : X) :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
    lt eq x y
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z

private abbrev z0 : Z := .Z0
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev pLt := CompCert4Lean.Lib.Coqlib.Plt

private def decEqSumbool {A : Type} [DecidableEq A] (x y : A) :
    Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

private def mregDecEq : DecidableEq mreg := by
  intro x y
  cases x <;> cases y <;>
    first
    | exact isTrue rfl
    | exact isFalse (by intro h; cases h)

/-! ## Stack slots and locations -/

inductive slot : Type where
  | Local
  | Incoming
  | Outgoing

export slot (Local Incoming Outgoing)

def slot_eqStatement : Type :=
  ∀ p q : slot, Sumbool (p = q) (p ≠ q)

def slot_eq (p q : slot) : Sumbool (p = q) (p ≠ q) := by
  cases p <;> cases q <;>
    first
    | exact .left rfl
    | exact .right (by intro h; cases h)

def typesize : typ → Z
  | .Tint => zOfNat 1
  | .Tlong => zOfNat 2
  | .Tfloat => zOfNat 2
  | .Tsingle => zOfNat 1
  | .Tany32 => zOfNat 1
  | .Tany64 => zOfNat 2

def typesize_posStatement : Prop :=
  ∀ ty : typ, zLt z0 (typesize ty)

def typealign : typ → Z
  | .Tint => zOfNat 1
  | .Tlong => zOfNat 2
  | .Tfloat => zOfNat 1
  | .Tsingle => zOfNat 1
  | .Tany32 => zOfNat 1
  | .Tany64 => zOfNat 1

inductive loc : Type where
  | R (r : mreg)
  | S (sl : slot) (pos : Z) (ty : typ)

export loc (R S)

namespace Loc

def type : loc → typ
  | .R r => mreg_type r
  | .S _ _ ty => ty

def eqStatement : Type :=
  ∀ p q : loc, Sumbool (p = q) (p ≠ q)

def eq (p q : loc) : Sumbool (p = q) (p ≠ q) := by
  cases p with
  | R r1 =>
      cases q with
      | R r2 =>
          cases mregDecEq r1 r2 with
          | isTrue h => exact .left (congrArg R h)
          | isFalse h => exact .right (by
              intro heq
              cases heq
              exact h rfl)
      | S _ _ _ => exact .right (by intro h; cases h)
  | S s1 d1 t1 =>
      cases q with
      | R _ => exact .right (by intro h; cases h)
      | S s2 d2 t2 =>
          cases slot_eq s1 s2 with
          | right h => exact .right (by
              intro heq
              cases heq
              exact h rfl)
          | left hs =>
              match (inferInstance : Decidable (d1 = d2)) with
              | isFalse h => exact .right (by
                  intro heq
                  cases heq
                  exact h rfl)
              | isTrue hd =>
                  match (inferInstance : Decidable (t1 = t2)) with
                  | isFalse h => exact .right (by
                      intro heq
                      cases heq
                      exact h rfl)
                  | isTrue ht => exact .left (by
                      subst s2
                      subst d2
                      subst t2
                      rfl)

def diff : loc → loc → Prop
  | .R r1, .R r2 => r1 ≠ r2
  | .S s1 d1 t1, .S s2 d2 t2 =>
      s1 ≠ s2 ∨ zLe (zAdd d1 (typesize t1)) d2 ∨
        zLe (zAdd d2 (typesize t2)) d1
  | _, _ => True

def same_not_diffStatement : Prop :=
  ∀ l : loc, ¬ diff l l

def diff_not_eqStatement : Prop :=
  ∀ l1 l2 : loc, diff l1 l2 → l1 ≠ l2

def diff_symStatement : Prop :=
  ∀ l1 l2 : loc, diff l1 l2 → diff l2 l1

def diff_dec (l1 l2 : loc) : Sumbool (diff l1 l2) (¬ diff l1 l2) := by
  cases l1 with
  | R r1 =>
      cases l2 with
      | R r2 =>
          cases mregDecEq r1 r2 with
          | isTrue h =>
              exact .right (by
                intro hne
                exact hne h)
          | isFalse h => exact .left h
      | S _ _ _ => exact .left trivial
  | S s1 d1 t1 =>
      cases l2 with
      | R _ => exact .left trivial
      | S s2 d2 t2 =>
          cases slot_eq s1 s2 with
          | right h => exact .left (Or.inl h)
          | left hs =>
              match CompCert4Lean.Lib.Coqlib.zle
                  (zAdd d1 (typesize t1)) d2 with
              | .left h12 => exact .left (Or.inr (Or.inl h12))
              | .right h12 =>
                  match CompCert4Lean.Lib.Coqlib.zle
                      (zAdd d2 (typesize t2)) d1 with
                  | .left h21 => exact .left (Or.inr (Or.inr h21))
                  | .right h21 => exact .right (by
                      intro h
                      rcases h with h | h | h
                      · exact h hs
                      · change intOfZ d2 <
                          intOfZ (zAdd d1 (typesize t1)) at h12
                        change intOfZ (zAdd d1 (typesize t1)) ≤
                          intOfZ d2 at h
                        omega
                      · change intOfZ d1 <
                          intOfZ (zAdd d2 (typesize t2)) at h21
                        change intOfZ (zAdd d2 (typesize t2)) ≤
                          intOfZ d1 at h
                        omega)

def notin (l : loc) : List loc → Prop
  | [] => True
  | l1 :: rest => diff l l1 ∧ notin l rest

end Loc

/-! ## Location maps -/

namespace Locmap

def t : Type := loc → val

def init (x : val) : t :=
  fun _ => x

def set (l : loc) (v : val) (m : t) : t :=
  fun p =>
    match Loc.eq l p with
    | .left _ =>
        match l with
        | .R _ => v
        | .S _ _ ty => Val.load_result (chunk_of_type ty) v
    | .right _ =>
        match Loc.diff_dec l p with
        | .left _ => m p
        | .right _ => Vundef

def gssStatement : Prop :=
  ∀ (l : loc) (v : val) (m : t),
    set l v m l =
      match l with
      | .R _ => v
      | .S _ _ ty => Val.load_result (chunk_of_type ty) v

def gsoStatement : Prop :=
  ∀ (l : loc) (v : val) (m : t) (p : loc),
    Loc.diff l p → set l v m p = m p

def getpair (p : rpair loc) (m : t) : val :=
  match p with
  | .One l => m l
  | .Twolong l1 l2 => Val.longofwords (m l1) (m l2)

def setpair (p : rpair mreg) (v : val) (m : t) : t :=
  match p with
  | .One r => set (R r) v m
  | .Twolong hi lo =>
      set (R lo) (Val.loword v) (set (R hi) (Val.hiword v) m)

def getpair_extenStatement : Prop :=
  ∀ (p : rpair loc) (ls1 ls2 : t),
    (∀ l, l ∈ regs_of_rpair p → ls2 l = ls1 l) →
      getpair p ls2 = getpair p ls1

def gpoStatement : Prop :=
  ∀ (p : rpair mreg) (v : val) (m : t) (l : loc),
    forall_rpair (fun r => Loc.diff l (R r)) p →
      setpair p v m l = m l

def setres : builtin_res mreg → val → t → t
  | .BR r, v, m => set (R r) v m
  | .BR_none, _, m => m
  | .BR_splitlong hi lo, v, m =>
      setres lo (Val.loword v) (setres hi (Val.hiword v) m)

end Locmap

/-! ## Generated ordered-type surfaces -/

namespace OrderedTyp

def OrderedTyp : Type := Unit

def t : Type := typ

def eq (x y : t) : Prop :=
  x = y

private def index : t → positive
  | .Tany32 => PArith.BinPos.Pos.of_nat 1
  | .Tint => PArith.BinPos.Pos.of_nat 2
  | .Tsingle => PArith.BinPos.Pos.of_nat 3
  | .Tany64 => PArith.BinPos.Pos.of_nat 4
  | .Tfloat => PArith.BinPos.Pos.of_nat 5
  | .Tlong => PArith.BinPos.Pos.of_nat 6

def lt (x y : t) : Prop :=
  pLt (index x) (index y)

def eq_refl : Prop :=
  ∀ x : t, eq x x

def eq_sym : Prop :=
  ∀ x y : t, eq x y → eq y x

def eq_trans : Prop :=
  ∀ x y z : t, eq x y → eq y z → eq x z

def lt_trans : Prop :=
  ∀ x y z : t, lt x y → lt y z → lt x z

def lt_not_eq : Prop :=
  ∀ x y : t, lt x y → ¬ eq x y

def compare (x y : t) : OrderedCompare lt eq x y := by
  cases x <;> cases y <;>
    first
    | exact .LT (by
        unfold lt pLt CompCert4Lean.Lib.Coqlib.Plt
          PArith.BinPos.Pos.lt index
        decide)
    | exact .EQ rfl
    | exact .GT (by
        unfold lt pLt CompCert4Lean.Lib.Coqlib.Plt
          PArith.BinPos.Pos.lt index
        decide)

def eq_dec (x y : t) : Sumbool (eq x y) (¬ eq x y) := by
  change Sumbool (x = y) (x ≠ y)
  exact decEqSumbool (A := typ) x y

end OrderedTyp

namespace OrderedSlot

def OrderedSlot : Type := Unit

def t : Type := slot

def eq (x y : t) : Prop :=
  x = y

private def index : t → positive
  | .Local => PArith.BinPos.Pos.of_nat 1
  | .Incoming => PArith.BinPos.Pos.of_nat 2
  | .Outgoing => PArith.BinPos.Pos.of_nat 3

def lt (x y : t) : Prop :=
  pLt (index x) (index y)

def eq_refl : Prop :=
  ∀ x : t, eq x x

def eq_sym : Prop :=
  ∀ x y : t, eq x y → eq y x

def eq_trans : Prop :=
  ∀ x y z : t, eq x y → eq y z → eq x z

def lt_trans : Prop :=
  ∀ x y z : t, lt x y → lt y z → lt x z

def lt_not_eq : Prop :=
  ∀ x y : t, lt x y → ¬ eq x y

def compare (x y : t) : OrderedCompare lt eq x y := by
  cases x <;> cases y <;>
    first
    | exact .LT (by
        unfold lt pLt CompCert4Lean.Lib.Coqlib.Plt
          PArith.BinPos.Pos.lt index
        decide)
    | exact .EQ rfl
    | exact .GT (by
        unfold lt pLt CompCert4Lean.Lib.Coqlib.Plt
          PArith.BinPos.Pos.lt index
        decide)

def eq_dec (x y : t) : Sumbool (eq x y) (¬ eq x y) :=
  slot_eq x y

end OrderedSlot

/-! ## Total ordering of locations -/

namespace OrderedLoc

def t : Type := loc

def eq (x y : t) : Prop :=
  x = y

def lt : t → t → Prop
  | .R r1, .R r2 =>
      pLt (IndexedMreg.index r1) (IndexedMreg.index r2)
  | .R _, .S _ _ _ => True
  | .S _ _ _, .R _ => False
  | .S sl1 ofs1 ty1, .S sl2 ofs2 ty2 =>
      OrderedSlot.lt sl1 sl2 ∨
        (sl1 = sl2 ∧
          (zLt ofs1 ofs2 ∨ (ofs1 = ofs2 ∧ OrderedTyp.lt ty1 ty2)))

def eq_symStatement : Prop :=
  ∀ x y : t, eq x y → eq y x

def lt_transStatement : Prop :=
  ∀ x y z : t, lt x y → lt y z → lt x z

def lt_not_eqStatement : Prop :=
  ∀ x y : t, lt x y → ¬ eq x y

private theorem mregIndex_inj (x y : mreg)
    (h : IndexedMreg.index x = IndexedMreg.index y) : x = y := by
  cases x <;> cases y <;> try rfl
  all_goals
    exfalso
    have hnat := congrArg PArith.BinPos.Pos.to_nat h
    change posToNat (posOfNat _) = posToNat (posOfNat _) at hnat
    rw [posToNat_posOfNat (by omega)] at hnat
    rw [posToNat_posOfNat (by omega)] at hnat
    omega

def compare (x y : t) : OrderedCompare lt eq x y := by
  cases x with
  | R r1 =>
      cases y with
      | R r2 =>
          cases CompCert4Lean.Lib.Ordered.OrderedPositive.compare
              (IndexedMreg.index r1) (IndexedMreg.index r2) with
          | LT h => exact .LT h
          | GT h => exact .GT h
          | EQ h =>
              change IndexedMreg.index r1 = IndexedMreg.index r2 at h
              exact .EQ (congrArg R (mregIndex_inj r1 r2 h))
      | S _ _ _ => exact .LT trivial
  | S sl1 ofs1 ty1 =>
      cases y with
      | R _ => exact .GT trivial
      | S sl2 ofs2 ty2 =>
          cases OrderedSlot.compare sl1 sl2 with
          | LT h => exact .LT (Or.inl h)
          | GT h => exact .GT (Or.inl h)
          | EQ hsl =>
              cases CompCert4Lean.Lib.Ordered.OrderedZ.compare ofs1 ofs2 with
              | LT h => exact .LT (Or.inr ⟨hsl, Or.inl h⟩)
              | GT h => exact .GT (Or.inr ⟨hsl.symm, Or.inl h⟩)
              | EQ hofs =>
                  cases OrderedTyp.compare ty1 ty2 with
                  | LT h =>
                      exact .LT (Or.inr ⟨hsl, Or.inr ⟨hofs, h⟩⟩)
                  | GT h =>
                      exact .GT (Or.inr ⟨hsl.symm, Or.inr ⟨hofs.symm, h⟩⟩)
                  | EQ hty =>
                      subst sl2
                      subst ofs2
                      subst ty2
                      exact .EQ rfl

def diff_low_bound : loc → loc
  | l@(.R _) => l
  | .S sl ofs _ => .S sl (zSub ofs (zOfNat 1)) Tany64

def diff_high_bound : loc → loc
  | l@(.R _) => l
  | .S sl ofs ty =>
      .S sl (zSub (zAdd ofs (typesize ty)) (zOfNat 1)) Tlong

def outside_interval_diffStatement : Prop :=
  ∀ l l' : loc,
    lt l' (diff_low_bound l) ∨ lt (diff_high_bound l) l' → Loc.diff l l'

def diff_outside_intervalStatement : Prop :=
  ∀ l l' : loc,
    Loc.diff l l' → lt l' (diff_low_bound l) ∨ lt (diff_high_bound l) l'

end OrderedLoc

end CompCert4Lean.Backend.Locations

namespace CompCert4Lean.Backend.Locations

theorem typesize_pos : typesize_posStatement := by
  intro ty
  cases ty <;>
    simp [typesize, zLt, z0, zOfNat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat]

end CompCert4Lean.Backend.Locations

namespace CompCert4Lean.Backend.Locations

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Loc.same_not_diff : Loc.same_not_diffStatement := by
  intro l h
  cases l with
  | R r => exact h rfl
  | S sl ofs ty =>
      rcases h with h | h | h
      · exact h rfl
      · have hp := typesize_pos ty
        change 0 < intOfZ (typesize ty) at hp
        change intOfZ (zAdd ofs (typesize ty)) ≤ intOfZ ofs at h
        simp only [zAdd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at h
        omega
      · have hp := typesize_pos ty
        change 0 < intOfZ (typesize ty) at hp
        change intOfZ (zAdd ofs (typesize ty)) ≤ intOfZ ofs at h
        simp only [zAdd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at h
        omega

theorem Loc.diff_sym : Loc.diff_symStatement := by
  intro l1 l2 h
  cases l1 with
  | R r1 =>
      cases l2 with
      | R r2 => exact fun heq => h heq.symm
      | S sl ofs ty => exact trivial
  | S sl1 ofs1 ty1 =>
      cases l2 with
      | R r => exact trivial
      | S sl2 ofs2 ty2 =>
          rcases h with h | h | h
          · exact Or.inl fun heq => h heq.symm
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)

theorem OrderedSlot.lt_not_eq_proof : OrderedSlot.lt_not_eq := by
  intro x y h heq
  subst y
  cases x <;>
    simp [OrderedSlot.lt, CompCert4Lean.Lib.Coqlib.Plt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.lt] at h

theorem OrderedTyp.lt_trans_proof : OrderedTyp.lt_trans := by
  intro x y z hxy hyz
  cases x <;> cases y <;> cases z <;>
    simp_all [OrderedTyp.lt, CompCert4Lean.Lib.Coqlib.Plt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.lt] <;> omega

end CompCert4Lean.Backend.Locations

namespace CompCert4Lean.Backend.Locations

theorem Locmap.gso : Locmap.gsoStatement := by
  intro l v m p h
  unfold Locmap.set
  cases Loc.eq l p with
  | left heq =>
      subst p
      exact (Loc.same_not_diff l h).elim
  | right hne =>
      cases Loc.diff_dec l p with
      | left hdiff => rfl
      | right hnotdiff => exact (hnotdiff h).elim

theorem OrderedTyp.lt_not_eq_proof : OrderedTyp.lt_not_eq := by
  intro x y h heq
  subst y
  cases x <;>
    simp [OrderedTyp.lt, CompCert4Lean.Lib.Coqlib.Plt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.lt] at h

theorem OrderedSlot.lt_trans_proof : OrderedSlot.lt_trans := by
  intro x y z hxy hyz
  cases x <;> cases y <;> cases z <;>
    simp_all [OrderedSlot.lt, CompCert4Lean.Lib.Coqlib.Plt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.lt] <;> omega

theorem Loc.diff_not_eq : Loc.diff_not_eqStatement := by
  intro l1 l2 h heq
  subst l2
  exact Loc.same_not_diff l1 h

end CompCert4Lean.Backend.Locations

namespace CompCert4Lean.Backend.Locations

theorem Locmap.gss : Locmap.gssStatement := by
  intro l v m
  unfold Locmap.set
  cases Loc.eq l l with
  | left h => cases l <;> rfl
  | right h => exact (h rfl).elim

theorem Locmap.getpair_exten : Locmap.getpair_extenStatement := by
  intro p ls1 ls2 h
  cases p with
  | One l =>
      exact h l (by simp [CompCert4Lean.Common.AST.regs_of_rpair])
  | Twolong l1 l2 =>
      unfold Locmap.getpair
      change CompCert4Lean.Common.Values.Val.longofwords (ls2 l1) (ls2 l2) =
        CompCert4Lean.Common.Values.Val.longofwords (ls1 l1) (ls1 l2)
      rw [h l1 (by simp [CompCert4Lean.Common.AST.regs_of_rpair]),
        h l2 (by simp [CompCert4Lean.Common.AST.regs_of_rpair])]

theorem Locmap.gpo : Locmap.gpoStatement := by
  intro p v m l h
  cases p with
  | One r =>
      change Locmap.set (R r) v m l = m l
      exact Locmap.gso _ _ _ _ (Loc.diff_sym _ _ h)
  | Twolong hi lo =>
      rcases h with ⟨hhi, hlo⟩
      change Locmap.set (R lo) (CompCert4Lean.Common.Values.Val.loword v)
          (Locmap.set (R hi) (CompCert4Lean.Common.Values.Val.hiword v) m) l = m l
      calc
        Locmap.set (R lo) (CompCert4Lean.Common.Values.Val.loword v)
            (Locmap.set (R hi) (CompCert4Lean.Common.Values.Val.hiword v) m) l =
            Locmap.set (R hi) (CompCert4Lean.Common.Values.Val.hiword v) m l :=
          Locmap.gso _ _ _ _ (Loc.diff_sym _ _ hlo)
        _ = m l := Locmap.gso _ _ _ _ (Loc.diff_sym _ _ hhi)

theorem OrderedLoc.eq_sym : OrderedLoc.eq_symStatement := by
  intro x y h
  exact h.symm

end CompCert4Lean.Backend.Locations

namespace CompCert4Lean.Backend.Locations

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem OrderedLoc.lt_trans : OrderedLoc.lt_transStatement := by
  have zlt_trans : ∀ a b c : Z, zLt a b → zLt b c → zLt a c := by
    intro a b c hab hbc
    change intOfZ a < intOfZ b at hab
    change intOfZ b < intOfZ c at hbc
    change intOfZ a < intOfZ c
    exact Int.lt_trans hab hbc
  intro x y z hxy hyz
  cases x with
  | R r1 =>
      cases y with
      | R r2 =>
          cases z with
          | R r3 =>
              exact CompCert4Lean.Lib.Coqlib.Plt_trans _ _ _ hxy hyz
          | S sl3 ofs3 ty3 =>
              exact trivial
      | S sl2 ofs2 ty2 =>
          cases z with
          | R r3 =>
              exact hyz.elim
          | S sl3 ofs3 ty3 =>
              exact trivial
  | S sl1 ofs1 ty1 =>
      cases y with
      | R r2 =>
          exact hxy.elim
      | S sl2 ofs2 ty2 =>
          cases z with
          | R r3 =>
              exact hyz.elim
          | S sl3 ofs3 ty3 =>
              rcases hxy with hxy | ⟨hsl12, hxy⟩
              · rcases hyz with hyz | ⟨hsl23, hyz⟩
                · exact Or.inl (OrderedSlot.lt_trans_proof _ _ _ hxy hyz)
                · exact Or.inl (by simpa [hsl23] using hxy)
              · rcases hyz with hyz | ⟨hsl23, hyz⟩
                · exact Or.inl (by simpa [hsl12] using hyz)
                · right
                  constructor
                  · exact hsl12.trans hsl23
                  · rcases hxy with hxy | ⟨hofs12, hxy⟩
                    · rcases hyz with hyz | ⟨hofs23, hyz⟩
                      · exact Or.inl (zlt_trans _ _ _ hxy hyz)
                      · exact Or.inl (by simpa [hofs23] using hxy)
                    · rcases hyz with hyz | ⟨hofs23, hyz⟩
                      · exact Or.inl (by simpa [hofs12] using hyz)
                      · right
                        constructor
                        · exact hofs12.trans hofs23
                        · exact OrderedTyp.lt_trans_proof _ _ _ hxy hyz

end CompCert4Lean.Backend.Locations
