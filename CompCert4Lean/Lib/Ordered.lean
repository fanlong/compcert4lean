import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Lib.Coqlib

/-!
# Ordered instances for positive numbers and integers

This module translates the definition-bearing surface of CompCert's
`lib/Ordered.v`.  The constructive comparison declarations are retained as
exact type descriptors for the later proof-migration phase.
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

end OrderedZ

end CompCert4Lean.Lib.Ordered
