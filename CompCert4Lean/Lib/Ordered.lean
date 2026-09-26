import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Lib.Coqlib

/-!
# Ordered instances for positive numbers and integers

This module translates the definition-bearing surface of CompCert's
`lib/Ordered.v`.  The constructive comparison declarations retain their exact
source identities and result types, alongside exact type descriptors for the
later proof-migration phase.
-/

namespace CompCert4Lean.Lib.Ordered

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace OrderedPositive

def t : Type := positive

def eq (x y : t) : Prop :=
  x = y

def lt : t → t → Prop :=
  CompCert4Lean.Lib.Coqlib.Plt

def compareStatement : Type :=
  ∀ x y : t,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq x y

def compare (x y : t) :
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq x y := by
  cases CompCert4Lean.Lib.Coqlib.plt x y with
  | left hlt => exact .LT hlt
  | right hlt =>
      cases CompCert4Lean.Lib.Coqlib.peq x y with
      | left heq => exact .EQ heq
      | right heq =>
          refine .GT ?_
          change PArith.BinPos.Pos.to_nat y < PArith.BinPos.Pos.to_nat x
          change ¬ PArith.BinPos.Pos.to_nat x < PArith.BinPos.Pos.to_nat y at hlt
          have hne :
              PArith.BinPos.Pos.to_nat x ≠ PArith.BinPos.Pos.to_nat y := by
            intro h
            exact heq (posToNat_injective h)
          omega

end OrderedPositive

namespace OrderedZ

def t : Type := Z

def eq (x y : t) : Prop :=
  x = y

def lt : t → t → Prop :=
  ZArith.BinInt.Z.lt

def compareStatement : Type :=
  ∀ x y : t,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq x y

def compare (x y : t) :
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq x y := by
  cases CompCert4Lean.Lib.Coqlib.zlt x y with
  | left hlt => exact .LT hlt
  | right hlt =>
      cases CompCert4Lean.Lib.Coqlib.zeq x y with
      | left heq => exact .EQ heq
      | right heq =>
          refine .GT ?_
          change intOfZ y ≤ intOfZ x at hlt
          change intOfZ y < intOfZ x
          have hne : intOfZ x ≠ intOfZ y := by
            intro h
            exact heq (intOfZ_injective h)
          omega

end OrderedZ

end CompCert4Lean.Lib.Ordered

/-! Proven runtime alternatives; original declarations above remain unchanged. -/

namespace CompCert4Lean.Lib.Ordered.OrderedPositive

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

def compareOnce (left right : t) :
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq left right := by
  have h := compareDirect_spec left right
  cases hc : compareDirect left right with
  | Lt =>
      rw [hc] at h
      exact .LT h
  | Eq =>
      rw [hc] at h
      exact .EQ (posToNat_injective h)
  | Gt =>
      rw [hc] at h
      exact .GT h

@[csimp] theorem compare_eq_compareOnce : compare = compareOnce := by
  funext left right
  have hleft := posToNat_positive left
  have hright := posToNat_positive right
  cases compare left right <;> cases compareOnce left right <;>
    first | rfl | (rename_i h1 h2; change posToNat _ < posToNat _ at h1 h2; omega) |
      (rename_i h1 h2; change _ = _ at h1; subst h1; change posToNat _ < posToNat _ at h2; omega) |
      (rename_i h1 h2; change _ = _ at h2; subst h2; change posToNat _ < posToNat _ at h1; omega)


end CompCert4Lean.Lib.Ordered.OrderedPositive
