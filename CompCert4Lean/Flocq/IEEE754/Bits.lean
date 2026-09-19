import CompCert4Lean.Flocq.IEEE754.Binary

/-!
# IEEE-754 bit encodings

This is the definition-translation surface for `Flocq.IEEE754.Bits`.
Proof-bearing source declarations in this packet are represented by exact
source-shaped proposition descriptors below.
-/

namespace CompCert4Lean.Flocq.IEEE754.Bits

open CompCert4Lean.Flocq.Core

abbrev Z := Zaux.Z
abbrev positive := Zaux.positive
abbrev Z0 : Z := Zaux.Z0
abbrev Zone : Z := Zaux.Zone
abbrev Ztwo : Z := Zaux.Ztwo
abbrev Zpos := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
abbrev Zadd := Zaux.Zadd
abbrev Zsub := Zaux.Zsub
abbrev Zmul := Zaux.Zmul
abbrev Zdiv := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
abbrev Zmod := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
abbrev Zshiftl := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
abbrev Zeq_bool := Zaux.Zeq_bool
abbrev Zle := Zaux.Zle
abbrev Zlt := Zaux.Zlt
abbrev Zle_bool := Zaux.Zle_bool
abbrev Zpower := Zaux.Zpower
abbrev Z_of_nat := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat

abbrev prec (mw : Z) : Z := Zadd mw Zone
abbrev emax (ew : Z) : Z := Zpower Ztwo (Zsub ew Zone)

abbrev emin (mw ew : Z) : Z :=
  BinarySingleNaN.emin0 (prec mw) (emax ew)

abbrev binary_float (mw ew : Z) : Type := Binary.binary_float (prec mw) (emax ew)

def join_bits (mw ew : Z) (s : Bool) (m e : Z) : Z :=
  Zadd (Zshiftl (Zadd (if s then Zpower Ztwo ew else Z0) e) mw) m

def split_bits (mw ew x : Z) : (Bool × Z) × Z :=
  let mm := Zpower Ztwo mw
  let em := Zpower Ztwo ew
  ((Zle_bool (Zmul mm em) x, Zmod x mm), Zmod (Zdiv x mm) em)

def bits_of_binary_float (mw ew : Z) (x : binary_float mw ew) : Z :=
  match x with
  | .B754_zero sx => join_bits mw ew sx Z0 Z0
  | .B754_infinity sx =>
      join_bits mw ew sx Z0 (Zsub (Zpower Ztwo ew) Zone)
  | .B754_nan sx plx =>
      join_bits mw ew sx (Zpos plx) (Zsub (Zpower Ztwo ew) Zone)
  | .B754_finite sx mx ex =>
      let m := Zsub (Zpos mx) (Zpower Ztwo mw)
      if Zle_bool Z0 m then
        join_bits mw ew sx m (Zadd (Zsub ex (emin mw ew)) Zone)
      else
        join_bits mw ew sx (Zpos mx) Z0

def split_bits_of_binary_float (mw ew : Z)
    (x : binary_float mw ew) : (Bool × Z) × Z :=
  match x with
  | .B754_zero sx => ((sx, Z0), Z0)
  | .B754_infinity sx =>
      ((sx, Z0), Zsub (Zpower Ztwo ew) Zone)
  | .B754_nan sx plx =>
      ((sx, Zpos plx), Zsub (Zpower Ztwo ew) Zone)
  | .B754_finite sx mx ex =>
      let m := Zsub (Zpos mx) (Zpower Ztwo mw)
      if Zle_bool Z0 m then
        ((sx, m), Zadd (Zsub ex (emin mw ew)) Zone)
      else
        ((sx, Zpos mx), Z0)

def binary_float_of_bits_aux (mw ew x : Z) :=
  let ((sx, mx), ex) := split_bits mw ew x
  if Zeq_bool ex Z0 then
    match mx with
    | .Z0 => Binary.F754_zero sx
    | .Zpos px => Binary.F754_finite sx px (emin mw ew)
    | .Zneg _ => Binary.F754_nan false .xH
  else if Zeq_bool ex (Zsub (Zpower Ztwo ew) Zone) then
    match mx with
    | .Z0 => Binary.F754_infinity sx
    | .Zpos plx => Binary.F754_nan sx plx
    | .Zneg _ => Binary.F754_nan false .xH
  else
    match Zadd mx (Zpower Ztwo mw) with
    | .Zpos px => Binary.F754_finite sx px (Zsub (Zadd ex (emin mw ew)) Zone)
    | _ => Binary.F754_nan false .xH

def binary_float_of_bits_unchecked (mw ew : Z)
    (_Hmw : Zlt Z0 mw) (_Hew : Zlt Z0 ew)
    (_Hmax : Zlt (prec mw) (emax ew))
    (x : Z) : binary_float mw ew :=
  Binary.FF2B_unchecked (binary_float_of_bits_aux mw ew x)

def binary_float_of_bits (mw ew : Z)
    (_Hmw : Zlt Z0 mw) (_Hew : Zlt Z0 ew)
    (_Hmax : Zlt (prec mw) (emax ew))
    (x : Z)
    (Hx : Binary.FF2BObligation
      (prec := prec mw) (emax := emax ew) (binary_float_of_bits_aux mw ew x)) :
    Binary.CertifiedBinaryFloat (prec mw) (emax ew) :=
  Binary.FF2B (binary_float_of_bits_aux mw ew x) Hx

def binary_float_of_bits_result_obligation : Prop :=
  ∀ (mw ew : Z) (_Hmw : Zlt Z0 mw) (_Hew : Zlt Z0 ew)
    (_Hmax : Zlt (prec mw) (emax ew)) (x : Z)
    (Hx : Binary.FF2BObligation
      (prec := prec mw) (emax := emax ew) (binary_float_of_bits_aux mw ew x)),
    Binary.BinaryFloatCertificate
      (binary_float_of_bits mw ew _Hmw _Hew _Hmax x Hx).1

/-! Exact source proposition descriptors for later proof migration. -/

def join_bits_rangeStatement : Prop :=
  ∀ (mw ew : Z) (s : Bool) (m e : Z),
    (Zle Z0 m ∧ Zlt m (Zpower Ztwo mw)) →
    (Zle Z0 e ∧ Zlt e (Zpower Ztwo ew)) →
    Zle Z0 (join_bits mw ew s m e) ∧
      Zlt (join_bits mw ew s m e)
        (Zpower Ztwo (Zadd (Zadd mw ew) Zone))

def split_join_bitsStatement : Prop :=
  ∀ (mw ew : Z) (s : Bool) (m e : Z),
    (Zle Z0 m ∧ Zlt m (Zpower Ztwo mw)) →
    (Zle Z0 e ∧ Zlt e (Zpower Ztwo ew)) →
    split_bits mw ew (join_bits mw ew s m e) = ((s, m), e)

def split_bits_of_binary_float_correctStatement : Prop :=
  ∀ (mw ew : Z), Zlt Z0 mw → Zlt Z0 ew →
    ∀ x : Binary.CertifiedBinaryFloat (prec mw) (emax ew),
    split_bits mw ew (bits_of_binary_float mw ew x.1) =
      split_bits_of_binary_float mw ew x.1

def bits_of_binary_float_rangeStatement : Prop :=
  ∀ (mw ew : Z), Zlt Z0 mw → Zlt Z0 ew →
    ∀ x : Binary.CertifiedBinaryFloat (prec mw) (emax ew),
    Zle Z0 (bits_of_binary_float mw ew x.1) ∧
      Zlt (bits_of_binary_float mw ew x.1)
        (Zpower Ztwo (Zadd (Zadd mw ew) Zone))

def binary_float_of_bits_aux_correctStatement : Prop :=
  ∀ (mw ew : Z), Zlt Z0 mw → Zlt Z0 ew →
    Zlt (prec mw) (emax ew) → ∀ x : Z,
    Binary.valid_binary (prec := prec mw) (emax := emax ew)
      (binary_float_of_bits_aux mw ew x) = true

def binary_float_of_bits_of_binary_floatStatement : Prop :=
  ∀ (mw ew : Z) (Hmw : Zlt Z0 mw) (Hew : Zlt Z0 ew)
    (Hmax : Zlt (prec mw) (emax ew))
    (x : Binary.CertifiedBinaryFloat (prec mw) (emax ew)),
    (binary_float_of_bits_unchecked mw ew Hmw Hew Hmax
      (bits_of_binary_float mw ew x.1)) = x.1

private abbrev z8 : Z := Z_of_nat 8
private abbrev z11 : Z := Z_of_nat 11
private abbrev z23 : Z := Z_of_nat 23
private abbrev z52 : Z := Z_of_nat 52

private def z23_gt_0 : Zlt Z0 z23 := by
  change (0 : Int) < 23
  decide

private def z8_gt_0 : Zlt Z0 z8 := by
  change (0 : Int) < 8
  decide

private def z23_format : Zlt (prec z23) (emax z8) := by
  change (24 : Int) < 128
  decide

private def z52_gt_0 : Zlt Z0 z52 := by
  change (0 : Int) < 52
  decide

private def z11_gt_0 : Zlt Z0 z11 := by
  change (0 : Int) < 11
  decide

private def z52_format : Zlt (prec z52) (emax z11) := by
  change (53 : Int) < 1024
  decide

def binary32 : Type := binary_float z23 z8

def b32_of_bits_unchecked (x : Z) : binary32 :=
  binary_float_of_bits_unchecked z23 z8 z23_gt_0 z8_gt_0 z23_format x

/- Certified construction requires the exact `FF2B` validity witness. -/
def b32_of_bits (x : Z)
    (Hx : Binary.FF2BObligation
      (prec := prec z23) (emax := emax z8) (binary_float_of_bits_aux z23 z8 x)) :
    Binary.CertifiedBinaryFloat (prec z23) (emax z8) :=
  binary_float_of_bits z23 z8 z23_gt_0 z8_gt_0 z23_format x Hx

def bits_of_b32 (x : binary32) : Z :=
  bits_of_binary_float z23 z8 x

def binary64 : Type := binary_float z52 z11

def b64_of_bits_unchecked (x : Z) : binary64 :=
  binary_float_of_bits_unchecked z52 z11 z52_gt_0 z11_gt_0 z52_format x

/- Certified construction requires the exact `FF2B` validity witness. -/
def b64_of_bits (x : Z)
    (Hx : Binary.FF2BObligation
      (prec := prec z52) (emax := emax z11) (binary_float_of_bits_aux z52 z11 x)) :
    Binary.CertifiedBinaryFloat (prec z52) (emax z11) :=
  binary_float_of_bits z52 z11 z52_gt_0 z11_gt_0 z52_format x Hx

def bits_of_b64 (x : binary64) : Z :=
  bits_of_binary_float z52 z11 x

end CompCert4Lean.Flocq.IEEE754.Bits

namespace CompCert4Lean.Flocq.IEEE754.Bits

theorem binary_float_of_bits_result_obligation_proof :
    binary_float_of_bits_result_obligation := by
  intro mw ew Hmw Hew Hmax x Hx
  exact (binary_float_of_bits mw ew Hmw Hew Hmax x Hx).2

end CompCert4Lean.Flocq.IEEE754.Bits

namespace CompCert4Lean.Flocq.IEEE754.Bits

open CompCert4Lean.Flocq.Core

private abbrev bits_intOfZ :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ

private theorem bits_zadd_int (a b : Z) :
    bits_intOfZ (Zadd a b) = bits_intOfZ a + bits_intOfZ b := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _

private theorem bits_zpow_int (a n : Z) (hn : 0 ≤ bits_intOfZ n) :
    bits_intOfZ (Zpower a n) =
      (bits_intOfZ a) ^ (Int.toNat (bits_intOfZ n)) := by
  change bits_intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow a n) = _
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
  split
  · rename_i h
    have hn' : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n := hn
    omega
  · rename_i h
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt _) = _
    rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    rfl

private theorem bits_zshift_int (a n : Z) (hn : 0 ≤ bits_intOfZ n) :
    bits_intOfZ (Zshiftl a n) =
      bits_intOfZ a * 2 ^ (Int.toNat (bits_intOfZ n)) := by
  change bits_intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl a n) = _
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
  split
  · rename_i h
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt _) = _
    rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    rfl
  · rename_i h
    have hn' : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n := hn
    omega

private theorem bits_zpow_two_int (n : Z) (hn : 0 ≤ bits_intOfZ n) :
    bits_intOfZ (Zpower Ztwo n) = 2 ^ (Int.toNat (bits_intOfZ n)) := by
  rw [bits_zpow_int Ztwo n hn]
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]

private theorem bits_zjoin_int (mw ew : Z) (s : Bool) (m e : Z)
    (hmw : 0 ≤ bits_intOfZ mw) :
    bits_intOfZ (join_bits mw ew s m e) =
      ((if s then bits_intOfZ (Zpower Ztwo ew) else 0) + bits_intOfZ e) *
        2 ^ Int.toNat (bits_intOfZ mw) + bits_intOfZ m := by
  rw [show join_bits mw ew s m e =
      Zadd (Zshiftl (Zadd (if s then Zpower Ztwo ew else Z0) e) mw) m by rfl]
  rw [bits_zadd_int, bits_zshift_int _ _ hmw, bits_zadd_int]
  by_cases hs : s = true
  · simp [hs]
  · simp [hs, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

theorem join_bits_range : join_bits_rangeStatement := by
  intro mw ew s m e Hm He
  change 0 ≤ bits_intOfZ m ∧
    bits_intOfZ m < bits_intOfZ (Zpower Ztwo mw) at Hm
  change 0 ≤ bits_intOfZ e ∧
    bits_intOfZ e < bits_intOfZ (Zpower Ztwo ew) at He
  have hmw : 0 ≤ bits_intOfZ mw := by
    cases mw with
    | Z0 => simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
    | Zpos p => simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
    | Zneg p =>
      have hpow : bits_intOfZ (Zpower Ztwo (.Zneg p)) = 0 := by
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive]
      rw [hpow] at Hm
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at *
      omega
  have hew : 0 ≤ bits_intOfZ ew := by
    cases ew with
    | Z0 => simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
    | Zpos p => simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
    | Zneg p =>
      have hpow : bits_intOfZ (Zpower Ztwo (.Zneg p)) = 0 := by
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive]
      rw [hpow] at He
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at *
      omega
  rw [bits_zpow_two_int mw hmw] at Hm
  rw [bits_zpow_two_int ew hew] at He
  have hpe : bits_intOfZ (Zpower Ztwo ew) =
      2 ^ Int.toNat (bits_intOfZ ew) := bits_zpow_two_int ew hew
  change 0 ≤ bits_intOfZ (join_bits mw ew s m e) ∧
    bits_intOfZ (join_bits mw ew s m e) <
      bits_intOfZ (Zpower Ztwo (Zadd (Zadd mw ew) Zone))
  rw [bits_zjoin_int mw ew s m e hmw]
  simp only [hpe]
  have hsumadd :
      bits_intOfZ (Zadd (Zadd mw ew) Zone) =
        bits_intOfZ mw + bits_intOfZ ew + 1 := by
    rw [bits_zadd_int, bits_zadd_int]
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
  have hMcast :
      (Int.ofNat (Int.toNat (bits_intOfZ mw)) : Int) = bits_intOfZ mw :=
    Int.toNat_of_nonneg hmw
  have hEcast :
      (Int.ofNat (Int.toNat (bits_intOfZ ew)) : Int) = bits_intOfZ ew :=
    Int.toNat_of_nonneg hew
  have hsum : 0 ≤ bits_intOfZ (Zadd (Zadd mw ew) Zone) := by
    rw [hsumadd]
    omega
  rw [bits_zpow_two_int (Zadd (Zadd mw ew) Zone) hsum]
  have hsumcast :
      (Int.ofNat (Int.toNat
        (bits_intOfZ (Zadd (Zadd mw ew) Zone))) : Int) =
        bits_intOfZ (Zadd (Zadd mw ew) Zone) :=
    Int.toNat_of_nonneg hsum
  have hexp :
      Int.toNat (bits_intOfZ (Zadd (Zadd mw ew) Zone)) =
        Int.toNat (bits_intOfZ mw) + Int.toNat (bits_intOfZ ew) + 1 := by
    apply Int.ofNat_inj.mp
    calc
      (Int.ofNat (Int.toNat
        (bits_intOfZ (Zadd (Zadd mw ew) Zone))) : Int) =
          bits_intOfZ (Zadd (Zadd mw ew) Zone) := hsumcast
      _ = bits_intOfZ mw + bits_intOfZ ew + 1 := hsumadd
      _ = (Int.ofNat (Int.toNat (bits_intOfZ mw)) : Int) +
          (Int.ofNat (Int.toNat (bits_intOfZ ew)) : Int) + 1 := by
            rw [hMcast, hEcast]
      _ = Int.ofNat (Int.toNat (bits_intOfZ mw) +
          Int.toNat (bits_intOfZ ew) + 1) := by simp
  rw [hexp]
  have hApos : 0 < (2 : Int) ^ Int.toNat (bits_intOfZ mw) :=
    Int.pow_pos (by omega)
  have hBpos : 0 < (2 : Int) ^ Int.toNat (bits_intOfZ ew) :=
    Int.pow_pos (by omega)
  have hA0 : 0 ≤ (2 : Int) ^ Int.toNat (bits_intOfZ mw) :=
    Int.le_of_lt hApos
  have hB0 : 0 ≤ (2 : Int) ^ Int.toNat (bits_intOfZ ew) :=
    Int.le_of_lt hBpos
  have htarget :
      2 ^ (Int.toNat (bits_intOfZ mw) + Int.toNat (bits_intOfZ ew) + 1) =
        (2 * (2 : Int) ^ Int.toNat (bits_intOfZ ew)) *
          (2 : Int) ^ Int.toNat (bits_intOfZ mw) := by
    rw [Int.pow_add, Int.pow_add]
    simp [Int.pow_succ, Int.mul_comm, Int.mul_left_comm]
  rw [htarget]
  cases s with
  | false =>
      simp
      constructor
      · exact Int.add_nonneg (Int.mul_nonneg He.1 hA0) Hm.1
      · have h1 : bits_intOfZ e * (2 : Int) ^ Int.toNat (bits_intOfZ mw) ≤
              ((2 : Int) ^ Int.toNat (bits_intOfZ ew) - 1) *
                (2 : Int) ^ Int.toNat (bits_intOfZ mw) := by
          apply Int.mul_le_mul_of_nonneg_right
          omega
          exact hA0
        have hmle : bits_intOfZ m ≤
            (2 : Int) ^ Int.toNat (bits_intOfZ mw) - 1 := by omega
        have h2 : ((2 : Int) ^ Int.toNat (bits_intOfZ ew) - 1) *
              (2 : Int) ^ Int.toNat (bits_intOfZ mw) + bits_intOfZ m <
            ((2 : Int) ^ Int.toNat (bits_intOfZ ew) + 1) *
              (2 : Int) ^ Int.toNat (bits_intOfZ mw) := by
          have hident : ((2 : Int) ^ Int.toNat (bits_intOfZ ew) - 1) *
                (2 : Int) ^ Int.toNat (bits_intOfZ mw) +
                ((2 : Int) ^ Int.toNat (bits_intOfZ mw) - 1) =
              (2 : Int) ^ Int.toNat (bits_intOfZ ew) *
                (2 : Int) ^ Int.toNat (bits_intOfZ mw) - 1 := by
            rw [Int.sub_mul, Int.one_mul]
            omega
          have htarget2 : ((2 : Int) ^ Int.toNat (bits_intOfZ ew) + 1) *
                (2 : Int) ^ Int.toNat (bits_intOfZ mw) =
              (2 : Int) ^ Int.toNat (bits_intOfZ ew) *
                (2 : Int) ^ Int.toNat (bits_intOfZ mw) +
                (2 : Int) ^ Int.toNat (bits_intOfZ mw) := by
            rw [Int.add_mul, Int.one_mul]
          omega
        have hsumlt : bits_intOfZ e *
              (2 : Int) ^ Int.toNat (bits_intOfZ mw) + bits_intOfZ m <
            ((2 : Int) ^ Int.toNat (bits_intOfZ ew) + 1) *
              (2 : Int) ^ Int.toNat (bits_intOfZ mw) := by omega
        have hBone : (1 : Int) ≤
            (2 : Int) ^ Int.toNat (bits_intOfZ ew) := by omega
        have hbound : ((2 : Int) ^ Int.toNat (bits_intOfZ ew) + 1) *
              (2 : Int) ^ Int.toNat (bits_intOfZ mw) ≤
            (2 * (2 : Int) ^ Int.toNat (bits_intOfZ ew)) *
              (2 : Int) ^ Int.toNat (bits_intOfZ mw) := by
          apply Int.mul_le_mul_of_nonneg_right
          omega
          exact hA0
        exact Int.lt_of_lt_of_le hsumlt hbound
  | true =>
      simp
      constructor
      · exact Int.add_nonneg
          (Int.mul_nonneg (Int.add_nonneg hB0 He.1) hA0) Hm.1
      · have h1 : ((2 : Int) ^ Int.toNat (bits_intOfZ ew) + bits_intOfZ e) *
              (2 : Int) ^ Int.toNat (bits_intOfZ mw) ≤
            (2 * (2 : Int) ^ Int.toNat (bits_intOfZ ew) - 1) *
              (2 : Int) ^ Int.toNat (bits_intOfZ mw) := by
          apply Int.mul_le_mul_of_nonneg_right
          omega
          exact hA0
        have hmle : bits_intOfZ m ≤
            (2 : Int) ^ Int.toNat (bits_intOfZ mw) - 1 := by omega
        have hident : (2 * (2 : Int) ^ Int.toNat (bits_intOfZ ew) - 1) *
              (2 : Int) ^ Int.toNat (bits_intOfZ mw) +
              ((2 : Int) ^ Int.toNat (bits_intOfZ mw) - 1) =
            (2 * (2 : Int) ^ Int.toNat (bits_intOfZ ew)) *
              (2 : Int) ^ Int.toNat (bits_intOfZ mw) - 1 := by
          rw [Int.sub_mul, Int.one_mul]
          omega
        omega

end CompCert4Lean.Flocq.IEEE754.Bits

namespace CompCert4Lean.Flocq.IEEE754.Bits

open CompCert4Lean.Flocq.Core

private abbrev bits_intOfZ2 :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ

theorem split_join_bits : split_join_bitsStatement := by
  intro mw ew s m e Hm He
  change 0 ≤ bits_intOfZ2 m ∧ bits_intOfZ2 m < bits_intOfZ2 (Zpower Ztwo mw) at Hm
  change 0 ≤ bits_intOfZ2 e ∧ bits_intOfZ2 e < bits_intOfZ2 (Zpower Ztwo ew) at He
  have hmw : Zle Z0 mw := by
    change 0 ≤ bits_intOfZ2 mw
    cases mw with
    | Z0 => simp [bits_intOfZ2, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
    | Zpos p => simp [bits_intOfZ2, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
    | Zneg p =>
      have hpow : bits_intOfZ2 (Zpower Ztwo (.Zneg p)) = 0 := by
        simp [bits_intOfZ2, Zpower,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive]
      rw [hpow] at Hm
      simp [bits_intOfZ2, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at *
      omega
  have hew : Zle Z0 ew := by
    change 0 ≤ bits_intOfZ2 ew
    cases ew with
    | Z0 => simp [bits_intOfZ2, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
    | Zpos p => simp [bits_intOfZ2, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
    | Zneg p =>
      have hpow : bits_intOfZ2 (Zpower Ztwo (.Zneg p)) = 0 := by
        simp [bits_intOfZ2, Zpower,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive]
      rw [hpow] at He
      simp [bits_intOfZ2, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at *
      omega
  have hmmpos : Zlt Z0 (Zpower Ztwo mw) := by
    exact CompCert4Lean.Flocq.Core.Zaux.Zpower_gt_0
      CompCert4Lean.Flocq.Core.Zaux.radix2 mw hmw
  have hempos : Zlt Z0 (Zpower Ztwo ew) := by
    exact CompCert4Lean.Flocq.Core.Zaux.Zpower_gt_0
      CompCert4Lean.Flocq.Core.Zaux.radix2 ew hew
  dsimp [split_bits, join_bits]
  have hshift : Zshiftl (Zadd (if s then Zpower Ztwo ew else Z0) e) mw =
      Zmul (Zadd (if s then Zpower Ztwo ew else Z0) e) (Zpower Ztwo mw) := by
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl_mul_pow2
      _ _ hmw
  rw [hshift]
  cases s with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hmodm : Zmod (Zadd (Zmul (Zadd Z0 e) (Zpower Ztwo mw)) m)
          (Zpower Ztwo mw) = m := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add Z0 e)
              (Zpower Ztwo mw)) m) (Zpower Ztwo mw) = m
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add_comm
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add Z0 e)
            (Zpower Ztwo mw)) m]
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_mod_plus_full]
        exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zmod_small m
          (Zpower Ztwo mw) Hm
      have hbool : Zlt
          (Zadd (Zmul (Zadd Z0 e) (Zpower Ztwo mw)) m)
          (Zmul (Zpower Ztwo mw) (Zpower Ztwo ew)) := by
        change bits_intOfZ2 (Zadd (Zmul (Zadd Z0 e) (Zpower Ztwo mw)) m) <
          bits_intOfZ2 (Zmul (Zpower Ztwo mw) (Zpower Ztwo ew))
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
          Int.zero_add]
        have hzero : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = 0 := by decide
        rw [hzero]
        have hM0 : 0 ≤ bits_intOfZ2 (Zpower Ztwo mw) := Int.le_of_lt hmmpos
        have hE1 : (1 : Int) ≤ bits_intOfZ2 (Zpower Ztwo ew) := by
          have hEpos : 0 < bits_intOfZ2 (Zpower Ztwo ew) := hempos
          omega
        have hcoef : bits_intOfZ2 e + 1 ≤ bits_intOfZ2 (Zpower Ztwo ew) := by
          omega
        have hmul :
            (bits_intOfZ2 e + 1) * bits_intOfZ2 (Zpower Ztwo mw) ≤
              bits_intOfZ2 (Zpower Ztwo ew) * bits_intOfZ2 (Zpower Ztwo mw) :=
          Int.mul_le_mul_of_nonneg_right hcoef hM0
        have hstep :
            bits_intOfZ2 e * bits_intOfZ2 (Zpower Ztwo mw) + bits_intOfZ2 m <
              (bits_intOfZ2 e + 1) * bits_intOfZ2 (Zpower Ztwo mw) := by
          calc
            bits_intOfZ2 e * bits_intOfZ2 (Zpower Ztwo mw) + bits_intOfZ2 m <
                bits_intOfZ2 e * bits_intOfZ2 (Zpower Ztwo mw) +
                  bits_intOfZ2 (Zpower Ztwo mw) := by omega
            _ = (bits_intOfZ2 e + 1) * bits_intOfZ2 (Zpower Ztwo mw) := by
              rw [Int.add_mul, Int.one_mul]
        have hlt := Int.lt_of_lt_of_le hstep hmul
        simpa [Int.mul_comm] using hlt
      have hz : Zadd Z0 e = e := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hzero : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = 0 := by decide
        rw [hzero]
        simp
      have hdiv : Zdiv (Zadd (Zmul (Zadd Z0 e) (Zpower Ztwo mw)) m)
          (Zpower Ztwo mw) = e := by
        rw [hz]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul e
              (Zpower Ztwo mw)) m) (Zpower Ztwo mw) = e
        have hMne : Zpower Ztwo mw ≠ Z0 := by
          intro h
          have hp := hmmpos
          rw [h] at hp
          change (0 : Int) < 0 at hp
          omega
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_plus_full_l
          e (Zpower Ztwo mw) m hMne]
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zdiv_small m
          (Zpower Ztwo mw) Hm]
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hzero : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = 0 := by decide
        rw [hzero, Int.add_zero]
      have hmod_e : Zmod (Zdiv (Zadd (Zmul (Zadd Z0 e) (Zpower Ztwo mw)) m)
          (Zpower Ztwo mw)) (Zpower Ztwo ew) = e := by
        rw [hdiv]
        exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zmod_small e
          (Zpower Ztwo ew) He
      apply Prod.ext
      · apply Prod.ext
        · exact CompCert4Lean.Flocq.Core.Zaux.Zle_bool_false _ _ hbool
        · exact hmodm
      · exact hmod_e
  | true =>
      simp only [↓reduceIte]
      have hmodm : Zmod (Zadd (Zmul (Zadd (Zpower Ztwo ew) e) (Zpower Ztwo mw)) m)
          (Zpower Ztwo mw) = m := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                (Zpower Ztwo ew) e) (Zpower Ztwo mw)) m) (Zpower Ztwo mw) = m
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add_comm
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
              (Zpower Ztwo ew) e) (Zpower Ztwo mw)) m]
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_mod_plus_full]
        exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zmod_small m
          (Zpower Ztwo mw) Hm
      have hbool : Zle (Zmul (Zpower Ztwo mw) (Zpower Ztwo ew))
          (Zadd (Zmul (Zadd (Zpower Ztwo ew) e) (Zpower Ztwo mw)) m) := by
        change bits_intOfZ2 (Zmul (Zpower Ztwo mw) (Zpower Ztwo ew)) ≤
          bits_intOfZ2 (Zadd (Zmul (Zadd (Zpower Ztwo ew) e) (Zpower Ztwo mw)) m)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hM0 : 0 ≤ bits_intOfZ2 (Zpower Ztwo mw) := Int.le_of_lt hmmpos
        have hcoef : bits_intOfZ2 (Zpower Ztwo ew) ≤
            bits_intOfZ2 (Zpower Ztwo ew) + bits_intOfZ2 e := by omega
        have hmul : bits_intOfZ2 (Zpower Ztwo ew) * bits_intOfZ2 (Zpower Ztwo mw) ≤
            (bits_intOfZ2 (Zpower Ztwo ew) + bits_intOfZ2 e) *
              bits_intOfZ2 (Zpower Ztwo mw) :=
          Int.mul_le_mul_of_nonneg_right hcoef hM0
        have hmul' : bits_intOfZ2 (Zpower Ztwo mw) * bits_intOfZ2 (Zpower Ztwo ew) ≤
            (bits_intOfZ2 (Zpower Ztwo ew) + bits_intOfZ2 e) *
              bits_intOfZ2 (Zpower Ztwo mw) := by
          simpa [Int.mul_comm] using hmul
        have hplus :
            (bits_intOfZ2 (Zpower Ztwo ew) + bits_intOfZ2 e) *
                bits_intOfZ2 (Zpower Ztwo mw) ≤
              (bits_intOfZ2 (Zpower Ztwo ew) + bits_intOfZ2 e) *
                bits_intOfZ2 (Zpower Ztwo mw) + bits_intOfZ2 m := by omega
        exact Int.le_trans hmul' hplus
      have hdiv : Zdiv (Zadd (Zmul (Zadd (Zpower Ztwo ew) e) (Zpower Ztwo mw)) m)
          (Zpower Ztwo mw) = Zadd (Zpower Ztwo ew) e := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
              (Zadd (Zpower Ztwo ew) e) (Zpower Ztwo mw)) m)
            (Zpower Ztwo mw) = Zadd (Zpower Ztwo ew) e
        have hMne : Zpower Ztwo mw ≠ Z0 := by
          intro h
          have hp := hmmpos
          rw [h] at hp
          change (0 : Int) < 0 at hp
          omega
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_plus_full_l
          (Zadd (Zpower Ztwo ew) e) (Zpower Ztwo mw) m hMne]
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zdiv_small m
          (Zpower Ztwo mw) Hm]
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hzero : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = 0 := by decide
        rw [hzero, Int.add_zero]
      have hadd : Zadd (Zpower Ztwo ew) e =
          Zadd e (Zmul Zone (Zpower Ztwo ew)) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hzone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 := by decide
        rw [hzone, Int.one_mul, Int.add_comm]
      have hmod_e : Zmod (Zdiv (Zadd (Zmul (Zadd (Zpower Ztwo ew) e)
          (Zpower Ztwo mw)) m) (Zpower Ztwo mw)) (Zpower Ztwo ew) = e := by
        rw [hdiv, hadd]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add e
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul Zone
              (Zpower Ztwo ew))) (Zpower Ztwo ew) = e
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_mod_plus_full]
        exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zmod_small e
          (Zpower Ztwo ew) He
      apply Prod.ext
      · apply Prod.ext
        · exact CompCert4Lean.Flocq.Core.Zaux.Zle_bool_true _ _ hbool
        · exact hmodm
      · exact hmod_e

end CompCert4Lean.Flocq.IEEE754.Bits


namespace CompCert4Lean.Flocq.IEEE754.Bits

open CompCert4Lean.Flocq.Core

private abbrev I := CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
private theorem bits_exp_bounds (mw ew e : Z) (Hmw : Zlt Z0 mw) (Hew : Zlt Z0 ew)
    (hemin : Zle (emin mw ew) e)
    (hexp : Zle e (Zsub (emax ew) (prec mw))) :
    Zle Z0 (Zadd (Zsub e (emin mw ew)) Zone) ∧
      Zlt (Zadd (Zsub e (emin mw ew)) Zone) (Zpower Ztwo ew) := by
  have zadd_int : ∀ a b : Z, I (Zadd a b) = I a + I b := by
    intro a b; change I (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (I a + I b)) = _
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
  have zsub_int : ∀ a b : Z, I (Zsub a b) = I a - I b := by
    intro a b; change I (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (I a - I b)) = _
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
  have hone : I Zone = 1 := by decide
  have hthree : I (Zsub (Zsub (Z_of_nat 3) (emax ew)) (prec mw)) =
      3 - I (emax ew) - I (prec mw) := by
    rw [zsub_int, zsub_int]
    have h3 : I (Z_of_nat 3) = 3 := by decide
    rw [h3]
  have hemin_formula : I (emin mw ew) = 3 - I (emax ew) - I (prec mw) := by
    change I (BinarySingleNaN.emin0 (prec mw) (emax ew)) = _
    simp [BinarySingleNaN.emin0,
      CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.emin]
    exact hthree
  have hew0 : Zle Z0 (Zsub ew Zone) := by
    change (0 : Int) ≤ I (Zsub ew Zone)
    rw [zsub_int, hone]
    change 0 < I ew at Hew
    omega
  have hzone0 : Zle Z0 Zone := by
    change (0 : Int) ≤ I Zone
    rw [hone]
    omega
  have hp := Zaux.Zpower_plus Ztwo (Zsub ew Zone) Zone hew0 hzone0
  have harg : Zadd (Zsub ew Zone) Zone = ew := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    change I (Zadd (Zsub ew Zone) Zone) = I ew
    rw [zadd_int, zsub_int, hone]
    change 0 < I ew at Hew
    omega
  have hpI := congrArg I hp
  change I (Zpower Ztwo (Zadd (Zsub ew Zone) Zone)) =
      I (Zmul (Zpower Ztwo (Zsub ew Zone)) (Zpower Ztwo Zone)) at hpI
  have hzmul : ∀ a b : Z, I (Zmul a b) = I a * I b := by
    intro a b; change I (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (I a * I b)) = _
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
  have htwo : I (Zpower Ztwo Zone) = 2 := by decide
  rw [hzmul, htwo] at hpI
  have hpowrel : I (Zpower Ztwo ew) = 2 * I (emax ew) := by
    have this := hpI
    rw [harg] at this
    simpa [emax, Int.mul_comm] using this
  change 0 ≤ I (Zadd (Zsub e (emin mw ew)) Zone) ∧
    I (Zadd (Zsub e (emin mw ew)) Zone) < I (Zpower Ztwo ew)
  rw [zadd_int, zsub_int, hone]
  change I e ≤ I (Zsub (emax ew) (prec mw)) at hexp
  rw [zsub_int] at hexp
  change I (emin mw ew) ≤ I e at hemin
  rw [hemin_formula] at hemin
  rw [hpowrel]
  omega


theorem split_bits_of_binary_float_correct : split_bits_of_binary_float_correctStatement := by
  intro mw ew Hmw Hew x
  cases x with
  | mk x hx =>
    cases x with
    | B754_zero s =>
      apply split_join_bits
      · change 0 ≤ I Z0 ∧ I Z0 < I (Zpower Ztwo mw)
        have hp := Zaux.Zpower_gt_0 Zaux.radix2 mw (Int.le_of_lt Hmw)
        change 0 < I (Zpower Ztwo mw) at hp
        have hz : I Z0 = 0 := by decide
        rw [hz]
        constructor <;> omega
      · change 0 ≤ I Z0 ∧ I Z0 < I (Zpower Ztwo ew)
        have hp := Zaux.Zpower_gt_0 Zaux.radix2 ew (Int.le_of_lt Hew)
        change 0 < I (Zpower Ztwo ew) at hp
        have hz : I Z0 = 0 := by decide
        rw [hz]
        constructor <;> omega
    | B754_infinity s =>
      apply split_join_bits
      · change 0 ≤ I Z0 ∧ I Z0 < I (Zpower Ztwo mw)
        have hp := Zaux.Zpower_gt_0 Zaux.radix2 mw (Int.le_of_lt Hmw)
        change 0 < I (Zpower Ztwo mw) at hp
        have hz : I Z0 = 0 := by decide
        rw [hz]
        constructor <;> omega
      · have zsub_int : ∀ a b : Z, I (Zsub a b) = I a - I b := by
          intro a b
          change I (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (I a - I b)) = _
          exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
        change 0 ≤ I (Zsub (Zpower Ztwo ew) Zone) ∧ I (Zsub (Zpower Ztwo ew) Zone) < I (Zpower Ztwo ew)
        have hp := Zaux.Zpower_gt_0 Zaux.radix2 ew (Int.le_of_lt Hew)
        change 0 < I (Zpower Ztwo ew) at hp
        have hone : I Zone = 1 := by decide
        rw [zsub_int, hone]
        constructor <;> omega
    | B754_nan s pl =>
      simp [bits_of_binary_float, split_bits_of_binary_float]
      simp [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary, Binary.nan_pl] at hx
      have hspec := Zaux.Zlt_bool_spec (Zpos (BinarySingleNaN.digits2_pos pl)) (prec mw)
      have hspec' : Zaux.Zlt_bool_prop (Zpos (BinarySingleNaN.digits2_pos pl)) (prec mw) true := by
        simpa [hx] using hspec
      have hdigits : Zlt (Zpos (BinarySingleNaN.digits2_pos pl)) (prec mw) := by
        cases hspec' with
        | Zlt_bool_true_ h => exact h
      have hd := CompCert4Lean.Flocq.Core.Digits.digits2_Pnat_correct pl
      have hupper0' := hd.2
      have hpow_eq : CompCert4Lean.Flocq.Core.Digits.Zpower_nat
            CompCert4Lean.Flocq.Core.Digits.Ztwo
            (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat pl)) =
          Zpower Ztwo (Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat pl))) := by
        rfl
      rw [hpow_eq] at hupper0'
      have hupper0 : Zlt (Zpos pl)
          (Zpower Ztwo (Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat pl)))) := hupper0'
      have zadd_int : ∀ a b : Z, I (Zadd a b) = I a + I b := by
        intro a b
        change I (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (I a + I b)) = _
        exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
      have hexp : Zle (Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat pl))) mw := by
        change I (Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat pl))) ≤ I mw
        change I (Zpos (BinarySingleNaN.digits2_pos pl)) < I (Zadd mw Zone) at hdigits
        have heq : I (Zpos (BinarySingleNaN.digits2_pos pl)) =
            I (Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat pl))) := by
          have hh := CompCert4Lean.Flocq.Core.Digits.Z_of_nat_S_digits2_Pnat pl
          have hp := CompCert4Lean.Flocq.Core.Digits.Zpos_digits2_pos pl
          have heqD : Zpos (BinarySingleNaN.digits2_pos pl) =
              Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat pl)) := by
            calc
              Zpos (BinarySingleNaN.digits2_pos pl) =
                  CompCert4Lean.Flocq.Core.Digits.Zdigits
                    CompCert4Lean.Flocq.Core.Digits.radix2 (Zpos pl) := by simpa using hp
              _ = Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat pl)) := by
                simpa using hh.symm
          exact congrArg I heqD
        rw [heq, zadd_int] at hdigits
        have hone : I Zone = 1 := by decide
        rw [hone] at hdigits
        omega
      have hpowle := Zaux.Zpower_le Zaux.radix2
        (Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat pl))) mw hexp
      have hmupper : Zlt (Zpos pl) (Zpower Ztwo mw) :=
        Int.lt_of_lt_of_le hupper0 hpowle
      apply split_join_bits
      · have hp := Zaux.Zpower_gt_0 Zaux.radix2 mw (Int.le_of_lt Hmw)
        change 0 < I (Zpower Ztwo mw) at hp
        change 0 ≤ I (Zpos pl) ∧ I (Zpos pl) < I (Zpower Ztwo mw)
        exact ⟨by simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ], hmupper⟩
      · have hp := Zaux.Zpower_gt_0 Zaux.radix2 ew (Int.le_of_lt Hew)
        change 0 < I (Zpower Ztwo ew) at hp
        have zsub_int : ∀ a b : Z, I (Zsub a b) = I a - I b := by
          intro a b
          change I (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (I a - I b)) = _
          exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
        change 0 ≤ I (Zsub (Zpower Ztwo ew) Zone) ∧ I (Zsub (Zpower Ztwo ew) Zone) < I (Zpower Ztwo ew)
        rw [zsub_int]
        have hone : I Zone = 1 := by decide
        rw [hone]
        constructor <;> omega
    | B754_finite s m e =>
      simp [bits_of_binary_float, split_bits_of_binary_float]
      simp [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary] at hx
      change (BinarySingleNaN.canonical_mantissa0 (prec mw) (emax ew) m e &&
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zle_bool e
          (Zsub (emax ew) (prec mw))) = true at hx
      have Hparts := Bool.and_eq_true_iff.mp hx
      have Hcan := Hparts.1
      have Hexp := Hparts.2
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool
          (Binary.fexp0 (prec mw) (emax ew)
            (Zadd (Zpos (BinarySingleNaN.digits2_pos m)) e)) e = true at Hcan
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool] at Hcan
      simp at Hcan
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zle_bool] at Hexp
      have Hexp' : Zle e (Zsub (emax ew) (prec mw)) := by
        have hs := Zaux.Zle_bool_spec e (Zsub (emax ew) (prec mw))
        have hs' : Zaux.Zle_bool_prop e (Zsub (emax ew) (prec mw)) true := by
          simpa [Hexp] using hs
        cases hs' with
        | Zle_bool_true_ h => exact h
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
          (Zsub (Zadd (Zpos (BinarySingleNaN.digits2_pos m)) e) (prec mw))
          (emin mw ew) = e at Hcan
      have zadd_int : ∀ a b : Z, I (Zadd a b) = I a + I b := by
        intro a b
        change I (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (I a + I b)) = _
        exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
      have zsub_int : ∀ a b : Z, I (Zsub a b) = I a - I b := by
        intro a b
        change I (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (I a - I b)) = _
        exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
      have hmaxa0 := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_max_l
        (Zsub (Zadd (Zpos (BinarySingleNaN.digits2_pos m)) e) (prec mw)) (emin mw ew)
      have hmaxb0 := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_max_r
        (Zsub (Zadd (Zpos (BinarySingleNaN.digits2_pos m)) e) (prec mw)) (emin mw ew)
      rw [Hcan] at hmaxa0 hmaxb0
      have hdigits0 : Zle (Zpos (BinarySingleNaN.digits2_pos m)) (prec mw) := by
        change I (Zpos (BinarySingleNaN.digits2_pos m)) ≤ I (prec mw)
        change I (Zsub (Zadd (Zpos (BinarySingleNaN.digits2_pos m)) e) (prec mw)) ≤ I e at hmaxa0
        rw [zsub_int, zadd_int] at hmaxa0
        omega
      have hdigits : Zle (CompCert4Lean.Flocq.Core.Digits.Zdigits
          CompCert4Lean.Flocq.Core.Digits.radix2 (Zpos m)) (prec mw) := by
        have hp := CompCert4Lean.Flocq.Core.Digits.Zpos_digits2_pos m
        rw [← hp]
        exact hdigits0
      have hemin : Zle (emin mw ew) e := hmaxb0
      have hmlt_prec : Zlt (Zpos m) (Zpower Ztwo (prec mw)) := by
        have hd := CompCert4Lean.Flocq.Core.Digits.digits2_Pnat_correct m
        have hupper0' := hd.2
        have hpow_eq : CompCert4Lean.Flocq.Core.Digits.Zpower_nat
              CompCert4Lean.Flocq.Core.Digits.Ztwo
              (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat m)) =
            Zpower Ztwo (Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat m))) := by
          rfl
        rw [hpow_eq] at hupper0'
        have hp := CompCert4Lean.Flocq.Core.Digits.Zpos_digits2_pos m
        have heqD : Zpos (BinarySingleNaN.digits2_pos m) =
            Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat m)) := by
          calc
            Zpos (BinarySingleNaN.digits2_pos m) =
                CompCert4Lean.Flocq.Core.Digits.Zdigits
                  CompCert4Lean.Flocq.Core.Digits.radix2 (Zpos m) := by simpa using hp
            _ = Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat m)) := by
              have hh := CompCert4Lean.Flocq.Core.Digits.Z_of_nat_S_digits2_Pnat m
              simpa using hh.symm
        have hexp : Zle (Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat m))) (prec mw) := by
          change I (Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat m))) ≤ I (prec mw)
          rw [← heqD]
          exact hdigits0
        have hpowle := Zaux.Zpower_le Zaux.radix2
          (Z_of_nat (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat m))) (prec mw) hexp
        exact Int.lt_of_lt_of_le hupper0' hpowle
      by_cases hb : Zle_bool Z0 (Zsub (Zpos m) (Zpower Ztwo mw)) = true
      · simp [hb]
        apply split_join_bits
        · have hnon : Zle Z0 (Zsub (Zpos m) (Zpower Ztwo mw)) := by
            have hs := Zaux.Zle_bool_spec Z0 (Zsub (Zpos m) (Zpower Ztwo mw))
            have hs' : Zaux.Zle_bool_prop Z0 (Zsub (Zpos m) (Zpower Ztwo mw)) true := by
              simpa [hb] using hs
            cases hs' with
            | Zle_bool_true_ h => exact h
          change 0 ≤ I (Zsub (Zpos m) (Zpower Ztwo mw)) ∧
            I (Zsub (Zpos m) (Zpower Ztwo mw)) < I (Zpower Ztwo mw)
          rw [zsub_int]
          have hmI : I (Zpos m) < I (Zpower Ztwo (prec mw)) := hmlt_prec
          have hmI' : I (Zpos m) < 2 * I (Zpower Ztwo mw) := by
            have zpow_prec : I (Zpower Ztwo (prec mw)) =
                2 * I (Zpower Ztwo mw) := by
              have hmw0 : Zle Z0 mw := Int.le_of_lt Hmw
              have hzone0 : Zle Z0 Zone := by
                change (0 : Int) ≤ I Zone
                have hone : I Zone = 1 := by decide
                rw [hone]
                omega
              have hp := Zaux.Zpower_plus Ztwo mw Zone hmw0 hzone0
              have hone : I Zone = 1 := by decide
              have htwo : I (Zpower Ztwo Zone) = 2 := by decide
              have hzmul : ∀ a b : Z, I (Zmul a b) = I a * I b := by
                intro a b
                change I (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (I a * I b)) = _
                exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
              have harg : Zadd mw Zone = prec mw := by rfl
              have hpI := congrArg I hp
              rw [hzmul, htwo] at hpI
              simpa [prec, Int.mul_comm] using hpI
            exact lt_of_lt_of_eq hmI zpow_prec
          change 0 ≤ I (Zsub (Zpos m) (Zpower Ztwo mw)) at hnon
          rw [zsub_int] at hnon
          constructor <;> omega
        · exact bits_exp_bounds mw ew e Hmw Hew hemin Hexp'
      · simp [hb]
        apply split_join_bits
        · change 0 ≤ I (Zpos m) ∧ I (Zpos m) < I (Zpower Ztwo mw)
          have hmpos : 0 < I (Zpos m) := by
            change 0 < Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            exact Int.natCast_pos.mpr
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m)
          have hltbranch : Zlt (Zsub (Zpos m) (Zpower Ztwo mw)) Z0 := by
            have hs := Zaux.Zle_bool_spec Z0 (Zsub (Zpos m) (Zpower Ztwo mw))
            have hs' : Zaux.Zle_bool_prop Z0 (Zsub (Zpos m) (Zpower Ztwo mw)) false := by
              simpa [hb] using hs
            cases hs' with
            | Zle_bool_false_ h => exact h
          have hmlt : Zlt (Zpos m) (Zpower Ztwo mw) := by
            change I (Zpos m) < I (Zpower Ztwo mw)
            change I (Zsub (Zpos m) (Zpower Ztwo mw)) < I Z0 at hltbranch
            rw [zsub_int] at hltbranch
            have hz : I Z0 = 0 := by decide
            rw [hz] at hltbranch
            omega
          exact ⟨by omega, hmlt⟩
        · change 0 ≤ I Z0 ∧ I Z0 < I (Zpower Ztwo ew)
          have hp := Zaux.Zpower_gt_0 Zaux.radix2 ew (Int.le_of_lt Hew)
          change 0 < I (Zpower Ztwo ew) at hp
          have hz : I Z0 = 0 := by decide
          rw [hz]
          constructor <;> omega
end CompCert4Lean.Flocq.IEEE754.Bits
