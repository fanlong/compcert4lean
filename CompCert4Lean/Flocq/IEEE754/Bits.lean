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
