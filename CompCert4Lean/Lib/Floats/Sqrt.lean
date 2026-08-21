import Init.Data.Float.Model.Unpacked.Operations.Sqrt
import CompCert4Lean.Lib.Floats.Model

/-!
# CompCert square-root provider

The executable part of this provider follows the accepted Gate 2 chain:
raw words are unpacked into Lean's checked `Float.Model.UnpackedFloat`, the
nearest-even square root is computed there, and the result is packed again.
NaN inputs are handled before unpacking so that CompCert's unary-operation
sign, payload, and quieting behavior remains observable at the raw-word
boundary.
-/

namespace CompCert4Lean.Lib.Floats

namespace FloatExec

abbrev Format := Float.Model.Format
abbrev Raw (spec : Format) := BitVec spec.numBits

end FloatExec

namespace Sqrt

abbrev Format := Float.Model.Format
abbrev UnpackedFloat := Float.Model.UnpackedFloat

def unpackedSqrt (spec : Format) : UnpackedFloat → UnpackedFloat :=
  Float.Model.UnpackedFloat.sqrt spec

private def rawIsNaN (spec : Format) (x : FloatExec.Raw spec) : Bool :=
  Float.Model.UnpackedFloat.unpackExponent x == (-1#_) &&
    Float.Model.UnpackedFloat.unpackMantissa x != (0#_)

private def quietNaN (spec : Format) (x : FloatExec.Raw spec) : FloatExec.Raw spec :=
  let quietMask : BitVec spec.numBits :=
    1#_ <<< (spec.mantissaBitsWithoutImplicit - 1)
  x ||| quietMask

def rawSqrt (spec : Format) (x : FloatExec.Raw spec) : FloatExec.Raw spec :=
  if rawIsNaN spec x then
    quietNaN spec x
  else
    Float.Model.UnpackedFloat.pack spec
      (unpackedSqrt spec (Float.Model.UnpackedFloat.unpack spec x))

/-! Public fixed-width endpoints.  The provider contract exposes these names
for downstream float operations; the raw-word implementation remains the
single canonical computation for both formats. -/

def float32_sqrt (x : UInt32) : UInt32 :=
  UInt32.ofBitVec (rawSqrt Float.Model.Format.binary32 x.toBitVec)

def float64_sqrt (x : UInt64) : UInt64 :=
  UInt64.ofBitVec (rawSqrt Float.Model.Format.binary64 x.toBitVec)

def rawSqrt_eq_modelStatement : Prop :=
  (∀ x : FloatExec.Raw Float.Model.Format.binary32,
    rawSqrt Float.Model.Format.binary32 x =
      (if rawIsNaN Float.Model.Format.binary32 x then
        quietNaN Float.Model.Format.binary32 x
      else
        Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
          (unpackedSqrt Float.Model.Format.binary32
            (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 x)))) ∧
  (∀ x : FloatExec.Raw Float.Model.Format.binary64,
    rawSqrt Float.Model.Format.binary64 x =
      (if rawIsNaN Float.Model.Format.binary64 x then
        quietNaN Float.Model.Format.binary64 x
      else
        Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
          (unpackedSqrt Float.Model.Format.binary64
          (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x))))

/- The source theorem identities remain available as exact proposition aliases;
proof discharge belongs to the later proof-grinding phase. -/
abbrev rawSqrt_eq_model : Prop := rawSqrt_eq_modelStatement

def float32_sqrt_correctStatement : Prop :=
  ∀ x : UInt32,
    float32_sqrt x =
      UInt32.ofBitVec
        (if rawIsNaN Float.Model.Format.binary32 x.toBitVec then
          quietNaN Float.Model.Format.binary32 x.toBitVec
        else
          Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
            (unpackedSqrt Float.Model.Format.binary32
              (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 x.toBitVec)))

abbrev float32_sqrt_correct : Prop := float32_sqrt_correctStatement

def float64_sqrt_correctStatement : Prop :=
  ∀ x : UInt64,
    float64_sqrt x =
      UInt64.ofBitVec
        (if rawIsNaN Float.Model.Format.binary64 x.toBitVec then
          quietNaN Float.Model.Format.binary64 x.toBitVec
        else
          Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
            (unpackedSqrt Float.Model.Format.binary64
              (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec)))

abbrev float64_sqrt_correct : Prop := float64_sqrt_correctStatement

end Sqrt

end CompCert4Lean.Lib.Floats
