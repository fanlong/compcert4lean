/-!
# Semi-lattice translation surface

This module translates the selected executable definitions from
`lib/Lattice.v`.  The surrounding module applications are represented by
checked marker identities; excluded source declarations are not reintroduced.
-/

namespace CompCert4Lean.Lib.Lattice

namespace LBoolean

def t : Type := Bool

def ge (x y : t) : Prop := x = y ∨ x = true

end LBoolean

namespace SEMILATTICE_WITH_TOP

def ImportMarker : Type := Unit

end SEMILATTICE_WITH_TOP

namespace LPMap

def LM : Type := Unit

end LPMap

end CompCert4Lean.Lib.Lattice
