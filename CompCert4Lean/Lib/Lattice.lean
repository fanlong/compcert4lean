import CompCert4Lean.Foundation.Logic

/-!
# Semi-lattice translation surface

This module translates the selected executable definitions from
`lib/Lattice.v`.  The surrounding module applications are represented by
checked marker identities; excluded source declarations are not reintroduced.
-/

namespace CompCert4Lean.Lib.Lattice

namespace LBoolean

def t : Type := Bool

def eq (x y : t) : Prop := x = y

def beq (x y : t) : Bool :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb x y

def ge (x y : t) : Prop := x = y ∨ x = true

def bot : t := false

def lub (x y : t) : t := x || y

end LBoolean

namespace SEMILATTICE_WITH_TOP

def ImportMarker : Type := Unit

end SEMILATTICE_WITH_TOP

namespace LPMap

def LM : Type := Unit

end LPMap

end CompCert4Lean.Lib.Lattice
