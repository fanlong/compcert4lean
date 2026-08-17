import CompCert4Lean.Foundation.Logic

/-!
# Rocq byte-string compatibility surface

Rocq strings are finite sequences of eight-bit characters.  The character
cell is represented directly by `UInt8`, so structural equality observes every
byte value, including embedded NUL and bytes above `0x7f`.  Unicode conversion
is intentionally outside this theorem-facing representation.
-/

namespace CompCert4Lean.Foundation.RocqString
namespace Rocq.Coq.Strings.String

inductive string : Type where
  | EmptyString
  | String (head : UInt8) (tail : string)
deriving DecidableEq

export string (EmptyString String)

def string_dec (s1 s2 : string) :
    _root_.CompCert4Lean.Foundation.Logic.Support.Sumbool
      (s1 = s2) (¬ s1 = s2) := by
  by_cases h : s1 = s2
  · exact .left h
  · exact .right h

end Rocq.Coq.Strings.String
end CompCert4Lean.Foundation.RocqString
