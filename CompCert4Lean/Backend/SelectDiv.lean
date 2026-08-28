import CompCert4Lean.Config
import CompCert4Lean.Driver.Compopts
import CompCert4Lean.Backend.CminorSel
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Floats
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Zbits
import CompCert4Lean.X86.SelectLong
import CompCert4Lean.X86.SelectOp

/-!
# Division and modulus instruction selection

Definition-bearing translation of CompCert's `backend/SelectDiv.v`.  Compiler
options are supplied explicitly through the immutable configuration.
-/

namespace CompCert4Lean.Backend.SelectDiv

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Lib.Floats
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong
open CompCert4Lean.X86.SelectOp

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev float := CompCert4Lean.Lib.Floats.float
private abbrev float32 := CompCert4Lean.Lib.Floats.float32
private abbrev BexactInverseCertificate :=
  CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev intRepr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev intUnsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev intSigned := CompCert4Lean.Lib.Integers.Int.signed
private abbrev intEq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev intLtu := CompCert4Lean.Lib.Integers.Int.ltu
private abbrev intSub := CompCert4Lean.Lib.Integers.Int.sub
private abbrev intDivu := CompCert4Lean.Lib.Integers.Int.divu
private abbrev intDivs := CompCert4Lean.Lib.Integers.Int.divs
private abbrev int64Repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev int64Unsigned := CompCert4Lean.Lib.Integers.Int64.unsigned
private abbrev int64Signed := CompCert4Lean.Lib.Integers.Int64.signed
private abbrev int64Eq := CompCert4Lean.Lib.Integers.Int64.eq
private abbrev int64Ltu := CompCert4Lean.Lib.Integers.Int64.ltu
private abbrev int64Sub := CompCert4Lean.Lib.Integers.Int64.sub
private abbrev int64Mul := CompCert4Lean.Lib.Integers.Int64.mul
private abbrev int64Divu := CompCert4Lean.Lib.Integers.Int64.divu
private abbrev int64Divs := CompCert4Lean.Lib.Integers.Int64.divs
private abbrev intWordsize := CompCert4Lean.Lib.Integers.Int.wordsize
private abbrev intModulus := CompCert4Lean.Lib.Integers.Int.modulus
private abbrev intHalfModulus := CompCert4Lean.Lib.Integers.Int.half_modulus
private abbrev intZwordsize := CompCert4Lean.Lib.Integers.Int.zwordsize
private abbrev int64Wordsize := CompCert4Lean.Lib.Integers.Int64.wordsize
private abbrev int64Modulus := CompCert4Lean.Lib.Integers.Int64.modulus
private abbrev int64HalfModulus := CompCert4Lean.Lib.Integers.Int64.half_modulus
private abbrev int64Zwordsize := CompCert4Lean.Lib.Integers.Int64.zwordsize

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := ZArith.BinInt.Z.of_nat 1
private abbrev z24 : Z := ZArith.BinInt.Z.of_nat 24
private abbrev z32 : Z := ZArith.BinInt.Z.of_nat 32
private abbrev z53 : Z := ZArith.BinInt.Z.of_nat 53
private abbrev z64 : Z := ZArith.BinInt.Z.of_nat 64
private abbrev z128 : Z := ZArith.BinInt.Z.of_nat 128
private abbrev z1024 : Z := ZArith.BinInt.Z.of_nat 1024
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zDiv := ZArith.BinInt.Z.div
private abbrev zMod := ZArith.BinInt.Z.modulo
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

private def boolOfSumbool {P Q : Prop} :
    CompCert4Lean.Foundation.Logic.Support.Sumbool P Q → Bool
  | .left _ => true
  | .right _ => false

private def zltBool (x y : Z) : Bool :=
  boolOfSumbool (CompCert4Lean.Lib.Coqlib.zlt x y)

private def zleBool (x y : Z) : Bool :=
  boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle x y)

private def optimForSize (cfg : CompilerConfig) : Bool :=
  CompCert4Lean.Driver.Compopts.optim_for_size cfg

def is_intconst (e : expr) : Option int :=
  match e with
  | Eop (Ointconst n) _ => some n
  | _ => none

def find_div_mul_params : Nat → Z → Z → Z → Option (Z × Z)
  | 0, _, _, _ => none
  | fuel + 1, nc, d, p =>
      let twp := two_p p
      if zltBool (zMul nc (zSub d (zMod twp d))) twp then
        some (p, zDiv (zSub (zAdd twp d) (zMod twp d)) d)
      else
        find_div_mul_params fuel nc d (zAdd p z1)

def divs_mul_params (d : Z) : Option (Z × Z) :=
  match find_div_mul_params
      intWordsize
      (zSub (zSub intHalfModulus (zMod intHalfModulus d)) z1)
      d z32 with
  | none => none
  | some (p, m) =>
      let p := zSub p z32
      if zltBool z0 d &&
          zltBool (two_p (zAdd z32 p)) (zMul m d) &&
          zleBool (zMul m d) (zAdd (two_p (zAdd z32 p)) (two_p (zAdd p z1))) &&
          zleBool z0 m && zltBool m intModulus &&
          zleBool z0 p && zltBool p z32 then
        some (p, m)
      else none

def divu_mul_params (d : Z) : Option (Z × Z) :=
  match find_div_mul_params
      intWordsize
      (zSub (zSub intModulus (zMod intModulus d)) z1)
      d z32 with
  | none => none
  | some (p, m) =>
      let p := zSub p z32
      if zltBool z0 d &&
          zleBool (two_p (zAdd z32 p)) (zMul m d) &&
          zleBool (zMul m d) (zAdd (two_p (zAdd z32 p)) (two_p p)) &&
          zleBool z0 m && zltBool m intModulus &&
          zleBool z0 p && zltBool p z32 then
        some (p, m)
      else none

def divls_mul_params (d : Z) : Option (Z × Z) :=
  match find_div_mul_params
      int64Wordsize
      (zSub (zSub int64HalfModulus (zMod int64HalfModulus d)) z1)
      d z64 with
  | none => none
  | some (p, m) =>
      let p := zSub p z64
      if zltBool z0 d &&
          zltBool (two_p (zAdd z64 p)) (zMul m d) &&
          zleBool (zMul m d) (zAdd (two_p (zAdd z64 p)) (two_p (zAdd p z1))) &&
          zleBool z0 m && zltBool m int64Modulus &&
          zleBool z0 p && zltBool p z64 then
        some (p, m)
      else none

def divlu_mul_params (d : Z) : Option (Z × Z) :=
  match find_div_mul_params
      int64Wordsize
      (zSub (zSub int64Modulus (zMod int64Modulus d)) z1)
      d z64 with
  | none => none
  | some (p, m) =>
      let p := zSub p z64
      if zltBool z0 d &&
          zleBool (two_p (zAdd z64 p)) (zMul m d) &&
          zleBool (zMul m d) (zAdd (two_p (zAdd z64 p)) (two_p p)) &&
          zleBool z0 m && zltBool m int64Modulus &&
          zleBool z0 p && zltBool p z64 then
        some (p, m)
      else none

def divu_mul (p m : Z) : expr :=
  shruimm
    (mulhu (Eletvar 0) (Eop (Ointconst (intRepr m)) Enil))
    (intRepr p)

def divuimm (cfg : CompilerConfig) (e1 : expr) (n2 : int) : expr :=
  match CompCert4Lean.Lib.Integers.Int.is_power2 n2 with
  | some l => shruimm e1 l
  | none =>
      if optimForSize cfg then
        divu_base e1 (Eop (Ointconst n2) Enil)
      else
        match divu_mul_params (intUnsigned n2) with
        | none => divu_base e1 (Eop (Ointconst n2) Enil)
        | some (p, m) => Elet e1 (divu_mul p m)

def divu (cfg : CompilerConfig) (e1 e2 : expr) : expr :=
  match is_intconst e2, is_intconst e1 with
  | some n2, some n1 =>
      if intEq n2 (CompCert4Lean.Lib.Integers.Int.zero) then
        divu_base e1 e2
      else
        Eop (Ointconst (intDivu n1 n2)) Enil
  | some n2, _ => divuimm cfg e1 n2
  | _, _ => divu_base e1 e2

def mod_from_div (equo : expr) (n : int) : expr :=
  Eop Osub (Econs (Eletvar 0) (Econs (mulimm n equo) Enil))

def moduimm (cfg : CompilerConfig) (e1 : expr) (n2 : int) : expr :=
  match CompCert4Lean.Lib.Integers.Int.is_power2 n2 with
  | some l => andimm (intSub n2 (CompCert4Lean.Lib.Integers.Int.one)) e1
  | none =>
      if optimForSize cfg then
        modu_base e1 (Eop (Ointconst n2) Enil)
      else
        match divu_mul_params (intUnsigned n2) with
        | none => modu_base e1 (Eop (Ointconst n2) Enil)
        | some (p, m) => Elet e1 (mod_from_div (divu_mul p m) n2)

def modu (cfg : CompilerConfig) (e1 e2 : expr) : expr :=
  match is_intconst e2, is_intconst e1 with
  | some n2, some n1 =>
      if intEq n2 (CompCert4Lean.Lib.Integers.Int.zero) then
        modu_base e1 e2
      else
        Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.modu n1 n2)) Enil
  | some n2, _ => moduimm cfg e1 n2
  | _, _ => modu_base e1 e2

def divs_mul (p m : Z) : expr :=
  let e2 := mulhs (Eletvar 0) (Eop (Ointconst (intRepr m)) Enil)
  let e3 := if zltBool m intHalfModulus then e2 else add e2 (Eletvar 0)
  add (shrimm e3 (intRepr p))
    (shruimm (Eletvar 0) (intRepr (zSub intZwordsize z1)))

def divsimm (cfg : CompilerConfig) (e1 : expr) (n2 : int) : expr :=
  match CompCert4Lean.Lib.Integers.Int.is_power2 n2 with
  | some l =>
      if intLtu l (intRepr (zOfNat 31)) then
        shrximm e1 l
      else
        divs_base e1 (Eop (Ointconst n2) Enil)
  | none =>
      if optimForSize cfg then
        divs_base e1 (Eop (Ointconst n2) Enil)
      else
        match divs_mul_params (intSigned n2) with
        | none => divs_base e1 (Eop (Ointconst n2) Enil)
        | some (p, m) => Elet e1 (divs_mul p m)

def divs (cfg : CompilerConfig) (e1 e2 : expr) : expr :=
  match is_intconst e2, is_intconst e1 with
  | some n2, some n1 =>
      if intEq n2 (CompCert4Lean.Lib.Integers.Int.zero) then
        divs_base e1 e2
      else
        Eop (Ointconst (intDivs n1 n2)) Enil
  | some n2, _ => divsimm cfg e1 n2
  | _, _ => divs_base e1 e2

def modsimm (cfg : CompilerConfig) (e1 : expr) (n2 : int) : expr :=
  match CompCert4Lean.Lib.Integers.Int.is_power2 n2 with
  | some l =>
      if intLtu l (intRepr (zOfNat 31)) then
        Elet e1 (mod_from_div (shrximm (Eletvar 0) l) n2)
      else
        mods_base e1 (Eop (Ointconst n2) Enil)
  | none =>
      if optimForSize cfg then
        mods_base e1 (Eop (Ointconst n2) Enil)
      else
        match divs_mul_params (intSigned n2) with
        | none => mods_base e1 (Eop (Ointconst n2) Enil)
        | some (p, m) => Elet e1 (mod_from_div (divs_mul p m) n2)

def mods (cfg : CompilerConfig) (e1 e2 : expr) : expr :=
  match is_intconst e2, is_intconst e1 with
  | some n2, some n1 =>
      if intEq n2 (CompCert4Lean.Lib.Integers.Int.zero) then
        mods_base e1 e2
      else
        Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.mods n1 n2)) Enil
  | some n2, _ => modsimm cfg e1 n2
  | _, _ => mods_base e1 e2

def modl_from_divl (equo : expr) (n : int64) : expr :=
  subl (Eletvar 0) (mullimm n equo)

def divlu_mull (p m : Z) : expr :=
  shrluimm (mullhu (Eletvar 0) (int64Repr m)) (intRepr p)

def divlu (cfg : CompilerConfig) (e1 e2 : expr) : expr :=
  match is_longconst e2, is_longconst e1 with
  | some n2, some n1 => longconst (int64Divu n1 n2)
  | some n2, _ =>
      match CompCert4Lean.Lib.Integers.Int64.is_power2' n2 with
      | some l => shrluimm e1 l
      | none =>
          if optimForSize cfg then
            divlu_base e1 e2
          else
            match divlu_mul_params (int64Unsigned n2) with
            | none => divlu_base e1 e2
            | some (p, m) => Elet e1 (divlu_mull p m)
  | _, _ => divlu_base e1 e2

def modlu (cfg : CompilerConfig) (e1 e2 : expr) : expr :=
  match is_longconst e2, is_longconst e1 with
  | some n2, some n1 =>
      longconst (CompCert4Lean.Lib.Integers.Int64.modu n1 n2)
  | some n2, _ =>
      match CompCert4Lean.Lib.Integers.Int64.is_power2 n2 with
      | some l => andl e1 (longconst (int64Sub n2 (CompCert4Lean.Lib.Integers.Int64.one)))
      | none =>
          if optimForSize cfg then
            modlu_base e1 e2
          else
            match divlu_mul_params (int64Unsigned n2) with
            | none => modlu_base e1 e2
            | some (p, m) =>
                Elet e1 (modl_from_divl (divlu_mull p m) n2)
  | _, _ => modlu_base e1 e2

def divls_mull (p m : Z) : expr :=
  let e2 := mullhs (Eletvar 0) (int64Repr m)
  let e3 := if zltBool m int64HalfModulus then e2 else addl e2 (Eletvar 0)
  addl (shrlimm e3 (intRepr p))
    (shrluimm (Eletvar 0) (intRepr (zSub int64Zwordsize z1)))

def divls (cfg : CompilerConfig) (e1 e2 : expr) : expr :=
  match is_longconst e2, is_longconst e1 with
  | some n2, some n1 => longconst (int64Divs n1 n2)
  | some n2, _ =>
      match CompCert4Lean.Lib.Integers.Int64.is_power2' n2 with
      | some l =>
          if intLtu l (intRepr (zOfNat 63)) then
            shrxlimm e1 l
          else
            divls_base e1 e2
      | none =>
          if optimForSize cfg then
            divls_base e1 e2
          else
            match divls_mul_params (int64Signed n2) with
            | none => divls_base e1 e2
            | some (p, m) => Elet e1 (divls_mull p m)
  | _, _ => divls_base e1 e2

def modls (cfg : CompilerConfig) (e1 e2 : expr) : expr :=
  match is_longconst e2, is_longconst e1 with
  | some n2, some n1 =>
      longconst (CompCert4Lean.Lib.Integers.Int64.mods n1 n2)
  | some n2, _ =>
      match CompCert4Lean.Lib.Integers.Int64.is_power2' n2 with
      | some l =>
          if intLtu l (intRepr (zOfNat 63)) then
            Elet e1 (modl_from_divl (shrxlimm (Eletvar 0) l) n2)
          else
            modls_base e1 e2
      | none =>
          if optimForSize cfg then
            modls_base e1 e2
          else
            match divls_mul_params (int64Signed n2) with
            | none => modls_base e1 e2
            | some (p, m) =>
                Elet e1 (modl_from_divl (divls_mull p m) n2)
  | _, _ => modls_base e1 e2

def divfimm [certificate : BexactInverseCertificate z53 z1024] (e : expr) (n : float) : expr :=
  match Float.exact_inverse (certificate := certificate) n with
  | some n' => Eop Omulf (Econs e (Econs (Eop (Ofloatconst n') Enil) Enil))
  | none => Eop Odivf (Econs e (Econs (Eop (Ofloatconst n) Enil) Enil))

inductive divf_cases : expr → Type where
  | divf_case1 (n2 : float) : divf_cases (Eop (Ofloatconst n2) Enil)
  | divf_default (e2 : expr) : divf_cases e2

export divf_cases (divf_case1 divf_default)

def divf_match (e2 : expr) : divf_cases e2 :=
  match e2 with
  | Eop (Ofloatconst n2) Enil => .divf_case1 n2
  | e2 => .divf_default e2

def divf [certificate : BexactInverseCertificate z53 z1024] (e1 e2 : expr) : expr :=
  match divf_match e2 with
  | .divf_case1 n2 => divfimm (certificate := certificate) e1 n2
  | .divf_default e2 => Eop Odivf (Econs e1 (Econs e2 Enil))

def divfsimm [certificate : BexactInverseCertificate z24 z128] (e : expr) (n : float32) : expr :=
  match Float32.exact_inverse (certificate := certificate) n with
  | some n' => Eop Omulfs (Econs e (Econs (Eop (Osingleconst n') Enil) Enil))
  | none => Eop Odivfs (Econs e (Econs (Eop (Osingleconst n) Enil) Enil))

inductive divfs_cases : expr → Type where
  | divfs_case1 (n2 : float32) : divfs_cases (Eop (Osingleconst n2) Enil)
  | divfs_default (e2 : expr) : divfs_cases e2

export divfs_cases (divfs_case1 divfs_default)

def divfs_match (e2 : expr) : divfs_cases e2 :=
  match e2 with
  | Eop (Osingleconst n2) Enil => .divfs_case1 n2
  | e2 => .divfs_default e2

def divfs [certificate : BexactInverseCertificate z24 z128] (e1 e2 : expr) : expr :=
  match divfs_match e2 with
  | .divfs_case1 n2 => divfsimm (certificate := certificate) e1 n2
  | .divfs_default e2 => Eop Odivfs (Econs e1 (Econs e2 Enil))

end CompCert4Lean.Backend.SelectDiv
