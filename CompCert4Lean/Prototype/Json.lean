import CompCert4Lean.Driver.Diagnostics
import Lean

namespace CompCert4Lean.Prototype

open Lean
open Foundation.Numbers.Rocq.Coq

abbrev CodecResult := Except String
abbrev RocqString := Foundation.RocqString.Rocq.Coq.Strings.String.string

def node (tag : String) (fields : List Json) : Json := .arr ((.str tag :: fields).toArray)

def fields (value : Json) : CodecResult (List Json) := do
  return (← value.getArr?).toList

def encList {α : Type} (encode : α → CodecResult Json) (values : List α) : CodecResult Json := do
  return .arr (← values.mapM encode).toArray

def decList {α : Type} (decode : Json → CodecResult α) (value : Json) : CodecResult (List α) := do
  (← fields value).mapM decode

def encOption {α : Type} (encode : α → CodecResult Json) : Option α → CodecResult Json
  | none => pure .null
  | some value => encode value

def decOption {α : Type} (decode : Json → CodecResult α) : Json → CodecResult (Option α)
  | .null => pure none
  | value => some <$> decode value

def encPair {α β : Type} (first : α → CodecResult Json) (second : β → CodecResult Json)
    (value : α × β) : CodecResult Json := do
  return .arr #[← first value.1, ← second value.2]

def decPair {α β : Type} (first : Json → CodecResult α) (second : Json → CodecResult β)
    (value : Json) : CodecResult (α × β) := do
  match ← fields value with
  | [left, right] => return (← first left, ← second right)
  | _ => throw "expected a pair"

def encSum {α β : Type} (left : α → CodecResult Json) (right : β → CodecResult Json)
    : Sum α β → CodecResult Json
  | .inl value => do return node "inl" [← left value]
  | .inr value => do return node "inr" [← right value]

def decSum {α β : Type} (left : Json → CodecResult α) (right : Json → CodecResult β)
    (value : Json) : CodecResult (Sum α β) := do
  match ← fields value with
  | [.str "inl", value] => .inl <$> left value
  | [.str "inr", value] => .inr <$> right value
  | _ => throw "expected a tagged sum"

def enc_bool (_ : Nat) (value : Bool) : CodecResult Json := pure (.bool value)
def dec_bool (_ : Nat) (value : Json) : CodecResult Bool := value.getBool?
def enc_unit (_ : Nat) (_ : Unit) : CodecResult Json := pure .null
def dec_unit (_ : Nat) : Json → CodecResult Unit
  | .null => pure ()
  | _ => throw "expected null unit"

def decimal (value : Json) : CodecResult Int := do
  let text ← value.getStr?
  let some number := text.toInt? | throw "expected decimal integer string"
  unless toString number == text do throw "noncanonical integer string"
  return number

def enc_z (_ : Nat) (value : Z) : CodecResult Json :=
  pure (.str (toString (intOfZ value)))
def dec_z (_ : Nat) (value : Json) : CodecResult Z :=
  zOfInt <$> decimal value
def enc_pos (_ : Nat) (value : positive) : CodecResult Json :=
  pure (.str (toString (PArith.BinPos.Pos.to_nat value)))
def dec_pos (_ : Nat) (value : Json) : CodecResult positive := do
  let number ← decimal value
  unless number > 0 do throw "identifier must be positive"
  return PArith.BinPos.Pos.of_nat number.toNat
def enc_n (_ : Nat) (value : N) : CodecResult Json :=
  pure (.str (toString (NArith.BinNat.N.to_nat value)))
def dec_n (_ : Nat) (value : Json) : CodecResult N := do
  let number ← decimal value
  unless number >= 0 do throw "expected nonnegative integer"
  return if number == 0 then .N0 else .Npos (PArith.BinPos.Pos.of_nat number.toNat)

def bounded (bits : Nat) (value : Json) : CodecResult Z := do
  let number ← decimal value
  unless number >= 0 && number < (2 : Int)^bits do throw s!"expected {bits}-bit unsigned bits"
  return zOfInt number

def enc_int (fuel : Nat) (value : Lib.Integers.int) : CodecResult Json :=
  enc_z fuel (Lib.Integers.Int.unsigned value)
def dec_int (_ : Nat) (value : Json) : CodecResult Lib.Integers.int :=
  Lib.Integers.Int.repr <$> bounded 32 value
def enc_long (fuel : Nat) (value : Lib.Integers.int64) : CodecResult Json :=
  enc_z fuel (Lib.Integers.Int64.unsigned value)
def dec_long (_ : Nat) (value : Json) : CodecResult Lib.Integers.int64 :=
  Lib.Integers.Int64.repr <$> bounded 64 value
def enc_ptr (fuel : Nat) (value : Lib.Integers.ptrofs) : CodecResult Json :=
  enc_z fuel (Lib.Integers.Ptrofs.unsigned value)
def dec_ptr (_ : Nat) (value : Json) : CodecResult Lib.Integers.ptrofs :=
  Lib.Integers.Ptrofs.repr <$> bounded 64 value
def enc_float (fuel : Nat) (value : Lib.Floats.float) : CodecResult Json :=
  enc_long fuel (Lib.Floats.Float.to_bits value)
def dec_float (fuel : Nat) (value : Json) : CodecResult Lib.Floats.float :=
  Lib.Floats.Float.of_bits <$> dec_long fuel value
def enc_single (fuel : Nat) (value : Lib.Floats.float32) : CodecResult Json :=
  enc_int fuel (Lib.Floats.Float32.to_bits value)
def dec_single (fuel : Nat) (value : Json) : CodecResult Lib.Floats.float32 :=
  Lib.Floats.Float32.of_bits <$> dec_int fuel value

def stringBytes : RocqString → List UInt8
  | .EmptyString => []
  | .String byte rest => byte :: stringBytes rest
def enc_string (_ : Nat) (value : RocqString) : CodecResult Json :=
  pure (.arr ((stringBytes value).map (fun byte => toJson byte.toNat)).toArray)
def dec_string (_ : Nat) (value : Json) : CodecResult RocqString := do
  let bytes ← (← fields value).mapM fun item => do
    let number ← item.getNat?
    unless number < 256 do throw "invalid byte"
    return UInt8.ofNat number
  return bytes.foldr .String .EmptyString

def errorText (errors : Common.Errors.errmsg) : String :=
  String.intercalate " " (errors.map fun error => match error with
    | .MSG message => String.fromUTF8! (ByteArray.mk (stringBytes message).toArray)
    | .CTX identifier => s!"context:{PArith.BinPos.Pos.to_nat identifier}"
    | .POS identifier => s!"position:{PArith.BinPos.Pos.to_nat identifier}")

end CompCert4Lean.Prototype
