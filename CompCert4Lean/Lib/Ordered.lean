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
