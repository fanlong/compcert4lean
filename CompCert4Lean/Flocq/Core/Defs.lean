import CompCert4Lean.Flocq.Core.Raux

/-!
# Basic Flocq definitions

This module contains the executable definition surfaces selected from
`Flocq.Core.Defs`.  The source-facing names are retained while the numerical
operations are supplied by the checked Flocq real and Rocq standard-library
facades.
-/

namespace CompCert4Lean.Flocq.Core.Defs

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Raux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Raux.radix
abbrev IZR := CompCert4Lean.Flocq.Core.Raux.IZR
abbrev bpow := CompCert4Lean.Flocq.Core.Raux.bpow
abbrev Rmult := CompCert4Lean.Flocq.Core.Raux.Rmult
abbrev Rle := CompCert4Lean.Flocq.Core.Raux.Rle
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Rabs
abbrev Rminus := CompCert4Lean.Flocq.Core.Raux.Rminus

/-! The source record is indexed by its radix, and Rocq exposes its
    constructor with that radix as an explicit first argument. An indexed
    inductive retains the same carrier while making the constructor
    source-facing. -/
inductive float : radix → Type where
  | Float (beta : radix) (Fnum : Z) (Fexp : Z) : float beta

/-! Source projections retain the implicit radix parameter of Rocq. -/
def Fnum {beta : radix} (f : float beta) : Z :=
  match f with
  | .Float _ m _ => m

def Fexp {beta : radix} (f : float beta) : Z :=
  match f with
  | .Float _ _ e => e

/-! Export the genuine indexed constructor under the source-facing name. -/
export float (Float)

/-! Compatibility for target consumers that used Lean's former default
    structure-constructor spelling. The canonical source constructor is
    `Float`, whose radix is explicit. -/
namespace float

abbrev mk {beta : radix} (m e : Z) : float beta :=
  Float beta m e

end float

def F2R {beta : radix} (f : float beta) : R :=
  Rmult (IZR (Fnum f)) (bpow beta (Fexp f))

def round_pred_total (P : R → R → Prop) : Prop :=
  ∀ x, ∃ f, P x f

def round_pred_monotone (P : R → R → Prop) : Prop :=
  ∀ x y f g, P x f → P y g → Rle x y → Rle f g

def Rnd_DN_pt (F : R → Prop) (x f : R) : Prop :=
  F f ∧ Rle f x ∧ ∀ g : R, F g → Rle g x → Rle g f

def Rnd_UP_pt (F : R → Prop) (x f : R) : Prop :=
  F f ∧ Rle x f ∧ ∀ g : R, F g → Rle x g → Rle f g

def Rnd_N_pt (F : R → Prop) (x f : R) : Prop :=
  F f ∧ ∀ g : R, F g → Rle (Rabs (Rminus f x)) (Rabs (Rminus g x))

/-! The theorem-facing definitions range over an explicitly injected exact-real
    context.  The executable definitions above retain the runtime carrier. -/
namespace Exact

abbrev Context := CompCert4Lean.Flocq.Core.Raux.Exact.Context
abbrev R (ctx : Context) := CompCert4Lean.Flocq.Core.Raux.Exact.R ctx

def F2R (ctx : Context) {beta : radix} (f : float beta) : R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rmult ctx
    (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Fnum f))
    (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Fexp f))

def round_pred_total (ctx : Context) (P : R ctx → R ctx → Prop) : Prop :=
  ∀ x, ∃ f, P x f

def round_pred_monotone (ctx : Context) (P : R ctx → R ctx → Prop) : Prop :=
  ∀ x y f g, P x f → P y g →
    CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx x y →
      CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx f g

def Rnd_DN_pt (ctx : Context) (F : R ctx → Prop) (x f : R ctx) : Prop :=
  F f ∧ CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx f x ∧
    ∀ g : R ctx, F g →
      CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx g x →
        CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx g f

def Rnd_UP_pt (ctx : Context) (F : R ctx → Prop) (x f : R ctx) : Prop :=
  F f ∧ CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx x f ∧
    ∀ g : R ctx, F g →
      CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx x g →
        CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx f g

def Rnd_N_pt (ctx : Context) (F : R ctx → Prop) (x f : R ctx) : Prop :=
  F f ∧ ∀ g : R ctx, F g →
    CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.Rminus ctx f x))
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.Rminus ctx g x))

end Exact

/-! The exact theorem carrier is related to the executable Raux carrier only
    through an explicit adapter obligation.  The runtime side deliberately
    spells out the operations used by `F2R`; theorem consumers therefore never
    obtain an implicit identification with the rational carrier. -/
def F2R_runtime_exact_correspondence (ctx : Exact.Context) : Prop :=
  ∀ (beta : radix) (m e : Z),
    ∃ h : ctx.adapter.represented
      (CompCert4Lean.Flocq.Core.Raux.Rmult
        (CompCert4Lean.Flocq.Core.Raux.IZR m)
        (CompCert4Lean.Flocq.Core.Raux.bpow beta e)),
      ctx.adapter.embed
        (CompCert4Lean.Flocq.Core.Raux.Rmult
          (CompCert4Lean.Flocq.Core.Raux.IZR m)
          (CompCert4Lean.Flocq.Core.Raux.bpow beta e)) h =
        Exact.F2R ctx (Float beta m e)

end CompCert4Lean.Flocq.Core.Defs

namespace CompCert4Lean.Flocq.Core.Defs

private theorem f2r_adapter_injective (ctx : Exact.Context)
    {x y : CompCert4Lean.Flocq.Core.Raux.R}
    (hx : ctx.adapter.represented x) (hy : ctx.adapter.represented y)
    (h : ctx.adapter.embed x hx = ctx.adapter.embed y hy) : x = y := by
  cases x with
  | mk xv =>
    cases y with
    | mk yv =>
      congr
      apply Rat.le_antisymm
      · exact (ctx.adapter.le_preserved ⟨xv⟩ hx ⟨yv⟩ hy).mp (by
          simpa only [h] using ctx.certificate.orderedField.le_refl (ctx.adapter.embed ⟨xv⟩ hx))
      · exact (ctx.adapter.le_preserved ⟨yv⟩ hy ⟨xv⟩ hx).mp (by
          simpa only [h] using ctx.certificate.orderedField.le_refl (ctx.adapter.embed ⟨yv⟩ hy))

private theorem f2r_adapter_zero (ctx : Exact.Context) :
    ∃ h : ctx.adapter.represented CompCert4Lean.Flocq.Core.Raux.R0,
      ctx.adapter.embed CompCert4Lean.Flocq.Core.Raux.R0 h = ctx.spec.zero := by
  have hzero : ctx.adapter.embed ctx.adapter.runtime_zero ctx.adapter.zero_represents = ctx.spec.zero :=
    ctx.adapter.zero_preserved
  let zsum : CompCert4Lean.Flocq.Core.Raux.R :=
    ⟨ctx.adapter.runtime_zero.value + ctx.adapter.runtime_zero.value⟩
  have hsum : ctx.adapter.represented zsum := by
    exact ctx.adapter.add_closed ctx.adapter.runtime_zero ctx.adapter.zero_represents
      ctx.adapter.runtime_zero ctx.adapter.zero_represents
  have hsum_value : ctx.adapter.embed zsum hsum = ctx.spec.zero := by
    calc
      ctx.adapter.embed zsum hsum =
          ctx.adapter.embed
            ⟨ctx.adapter.runtime_zero.value + ctx.adapter.runtime_zero.value⟩
            (ctx.adapter.add_closed ctx.adapter.runtime_zero ctx.adapter.zero_represents
              ctx.adapter.runtime_zero ctx.adapter.zero_represents) := by congr
      _ = ctx.spec.add
          (ctx.adapter.embed ctx.adapter.runtime_zero ctx.adapter.zero_represents)
          (ctx.adapter.embed ctx.adapter.runtime_zero ctx.adapter.zero_represents) :=
        ctx.adapter.add_preserved ctx.adapter.runtime_zero ctx.adapter.zero_represents
          ctx.adapter.runtime_zero ctx.adapter.zero_represents
      _ = ctx.spec.zero := by
        rw [hzero]
        exact ctx.certificate.orderedField.add_zero _
  have heq : zsum = ctx.adapter.runtime_zero := by
    exact f2r_adapter_injective ctx hsum ctx.adapter.zero_represents
      (hsum_value.trans hzero.symm)
  have heq_value : ctx.adapter.runtime_zero.value + ctx.adapter.runtime_zero.value = ctx.adapter.runtime_zero.value :=
    congrArg (fun z => z.value) heq
  have hx_zero : ctx.adapter.runtime_zero.value = 0 := by
    apply Rat.add_left_cancel ctx.adapter.runtime_zero.value
    simpa only [Rat.add_zero] using heq_value
  have hcanonical : ctx.adapter.runtime_zero = CompCert4Lean.Flocq.Core.Raux.R0 := by
    exact congrArg CompCert4Lean.Foundation.FlocqReal.OrderedReal.mk hx_zero
  refine ⟨?_, ?_⟩
  · simpa only [← hcanonical] using ctx.adapter.zero_represents
  · simpa only [← hcanonical] using hzero

private theorem f2r_adapter_one (ctx : Exact.Context) :
    ∃ h : ctx.adapter.represented CompCert4Lean.Flocq.Core.Raux.Rone,
      ctx.adapter.embed CompCert4Lean.Flocq.Core.Raux.Rone h = ctx.spec.one := by
  have hone : ctx.adapter.embed ctx.adapter.runtime_one ctx.adapter.one_represents = ctx.spec.one :=
    ctx.adapter.one_preserved
  let zprod : CompCert4Lean.Flocq.Core.Raux.R :=
    ⟨ctx.adapter.runtime_one.value * ctx.adapter.runtime_one.value⟩
  have hprod : ctx.adapter.represented zprod := by
    exact ctx.adapter.mul_closed ctx.adapter.runtime_one ctx.adapter.one_represents
      ctx.adapter.runtime_one ctx.adapter.one_represents
  have hprod_value : ctx.adapter.embed zprod hprod = ctx.spec.one := by
    calc
      ctx.adapter.embed zprod hprod =
          ctx.adapter.embed
            ⟨ctx.adapter.runtime_one.value * ctx.adapter.runtime_one.value⟩
            (ctx.adapter.mul_closed ctx.adapter.runtime_one ctx.adapter.one_represents
              ctx.adapter.runtime_one ctx.adapter.one_represents) := by congr
      _ = ctx.spec.mul
          (ctx.adapter.embed ctx.adapter.runtime_one ctx.adapter.one_represents)
          (ctx.adapter.embed ctx.adapter.runtime_one ctx.adapter.one_represents) :=
        ctx.adapter.mul_preserved ctx.adapter.runtime_one ctx.adapter.one_represents
          ctx.adapter.runtime_one ctx.adapter.one_represents
      _ = ctx.spec.one := by
        rw [hone]
        exact ctx.certificate.orderedField.mul_one _
  have heq : zprod = ctx.adapter.runtime_one := by
    exact f2r_adapter_injective ctx hprod ctx.adapter.one_represents
      (hprod_value.trans hone.symm)
  have heq_value : ctx.adapter.runtime_one.value * ctx.adapter.runtime_one.value =
      ctx.adapter.runtime_one.value := congrArg (fun z => z.value) heq
  have hfactor : ctx.adapter.runtime_one.value * (ctx.adapter.runtime_one.value - 1) = 0 := by
    rw [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.mul_one, heq_value, Rat.add_neg_cancel]
  rcases Rat.mul_eq_zero.mp hfactor with hzero | hsub
  · obtain ⟨hz, hzero_embed⟩ := f2r_adapter_zero ctx
    have hcanonical : ctx.adapter.runtime_one = CompCert4Lean.Flocq.Core.Raux.R0 := by
      exact congrArg CompCert4Lean.Foundation.FlocqReal.OrderedReal.mk hzero
    let hrep : ctx.adapter.represented CompCert4Lean.Flocq.Core.Raux.R0 :=
      Eq.ndrec ctx.adapter.one_represents hcanonical
    have honeR0 : ctx.adapter.embed CompCert4Lean.Flocq.Core.Raux.R0 hrep = ctx.spec.one := by
      exact Eq.rec (motive := fun y h =>
        ctx.adapter.embed y (Eq.ndrec ctx.adapter.one_represents h) = ctx.spec.one)
        ctx.adapter.one_preserved hcanonical
    apply (ctx.certificate.orderedField.zero_ne_one ?_).elim
    calc
      ctx.spec.zero = ctx.adapter.embed CompCert4Lean.Flocq.Core.Raux.R0 hz := hzero_embed.symm
      _ = ctx.adapter.embed CompCert4Lean.Flocq.Core.Raux.R0 hrep := by congr
      _ = ctx.spec.one := honeR0
  · have hone_value : ctx.adapter.runtime_one.value = 1 := by
      calc
        ctx.adapter.runtime_one.value = ctx.adapter.runtime_one.value - 1 + 1 := Rat.sub_add_cancel.symm
        _ = 0 + 1 := congrArg (fun z => z + 1) hsub
        _ = 1 := Rat.zero_add _
    have hcanonical : ctx.adapter.runtime_one = CompCert4Lean.Flocq.Core.Raux.Rone := by
      exact congrArg CompCert4Lean.Foundation.FlocqReal.OrderedReal.mk hone_value
    refine ⟨?_, ?_⟩
    · simpa only [← hcanonical] using ctx.adapter.one_represents
    · simpa only [← hcanonical] using hone

private theorem f2r_izr_add (x y : Z) :
    CompCert4Lean.Flocq.Core.Raux.IZR
        (CompCert4Lean.Flocq.Core.Raux.Zadd x y) =
      CompCert4Lean.Flocq.Core.Raux.Rplus
        (CompCert4Lean.Flocq.Core.Raux.IZR x)
        (CompCert4Lean.Flocq.Core.Raux.IZR y) := by
  apply congrArg CompCert4Lean.Foundation.FlocqReal.OrderedReal.mk
  change Rat.ofInt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x +
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y))) =
    Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x) +
      Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y)
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  exact Rat.intCast_add _ _

private theorem f2r_z_succ (n : Nat) :
    CompCert4Lean.Flocq.Core.Raux.Zadd
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n))
      (CompCert4Lean.Flocq.Core.Raux.Zpos CompCert4Lean.Flocq.Core.Raux.xH) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat (n + 1)) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n)) +
       CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Flocq.Core.Raux.Zpos CompCert4Lean.Flocq.Core.Raux.xH))) = _
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rfl

private theorem f2r_izr_neg (x : Z) :
    CompCert4Lean.Flocq.Core.Raux.IZR
        (CompCert4Lean.Flocq.Core.Raux.Zopp x) =
      CompCert4Lean.Flocq.Core.Raux.Ropp
        (CompCert4Lean.Flocq.Core.Raux.IZR x) := by
  apply congrArg CompCert4Lean.Foundation.FlocqReal.OrderedReal.mk
  change Rat.ofInt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (-CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x))) =
    -Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x)
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  exact Rat.intCast_neg _

private theorem f2r_adapter_izr (ctx : Exact.Context) (z : Z) :
    ∃ h : ctx.adapter.represented (CompCert4Lean.Flocq.Core.Raux.IZR z),
      ctx.adapter.embed (CompCert4Lean.Flocq.Core.Raux.IZR z) h =
        CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx z := by
  have hnat : ∀ n : Nat,
      ∃ h : ctx.adapter.represented
        (CompCert4Lean.Flocq.Core.Raux.IZR
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n))),
        ctx.adapter.embed
          (CompCert4Lean.Flocq.Core.Raux.IZR
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n))) h =
          CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n)) := by
    intro n
    induction n with
    | zero =>
        obtain ⟨hz, hzero⟩ := f2r_adapter_zero ctx
        refine ⟨hz, ?_⟩
        calc
          ctx.adapter.embed
              (CompCert4Lean.Flocq.Core.Raux.IZR
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat 0))) hz =
              ctx.spec.zero := hzero
          _ = CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat 0)) := by
            exact ctx.certificate.sourceLaws.ofZ_zero.symm
    | succ n ih =>
        obtain ⟨h1, hone⟩ := f2r_adapter_one ctx
        let zn := CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n)
        let zn1 := CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat (n + 1))
        have hsucc : CompCert4Lean.Flocq.Core.Raux.Zadd zn
            (CompCert4Lean.Flocq.Core.Raux.Zpos CompCert4Lean.Flocq.Core.Raux.xH) = zn1 :=
          f2r_z_succ n
        have hplus : ctx.adapter.represented
            (CompCert4Lean.Flocq.Core.Raux.Rplus
              (CompCert4Lean.Flocq.Core.Raux.IZR zn)
              (CompCert4Lean.Flocq.Core.Raux.IZR
                (CompCert4Lean.Flocq.Core.Raux.Zpos CompCert4Lean.Flocq.Core.Raux.xH))) := by
          change ctx.adapter.represented
            (CompCert4Lean.Flocq.Core.Raux.Rplus
              (CompCert4Lean.Flocq.Core.Raux.IZR zn)
              CompCert4Lean.Flocq.Core.Raux.Rone)
          exact ctx.adapter.add_closed _ ih.choose _ h1
        have hplus_value : ctx.adapter.embed _ hplus =
            ctx.spec.add (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx zn)
              (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
                (CompCert4Lean.Flocq.Core.Raux.Zpos CompCert4Lean.Flocq.Core.Raux.xH)) := by
          calc
            ctx.adapter.embed _ hplus = ctx.adapter.embed _
                (ctx.adapter.add_closed _ ih.choose _ h1) := by congr
            _ = ctx.spec.add
                (ctx.adapter.embed _ ih.choose) (ctx.adapter.embed _ h1) :=
              ctx.adapter.add_preserved _ ih.choose _ h1
            _ = ctx.spec.add (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx zn)
                (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
                  (CompCert4Lean.Flocq.Core.Raux.Zpos CompCert4Lean.Flocq.Core.Raux.xH)) := by
              rw [ih.choose_spec]
              change ctx.spec.add (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx zn)
                (ctx.adapter.embed CompCert4Lean.Flocq.Core.Raux.Rone h1) = _
              rw [hone]
              exact congrArg (ctx.spec.add (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx zn))
                ctx.certificate.sourceLaws.ofZ_one.symm
        have hruntime : CompCert4Lean.Flocq.Core.Raux.IZR zn1 =
            CompCert4Lean.Flocq.Core.Raux.Rplus
              (CompCert4Lean.Flocq.Core.Raux.IZR zn)
              (CompCert4Lean.Flocq.Core.Raux.IZR
                (CompCert4Lean.Flocq.Core.Raux.Zpos CompCert4Lean.Flocq.Core.Raux.xH)) := by
          calc
            CompCert4Lean.Flocq.Core.Raux.IZR zn1 =
                CompCert4Lean.Flocq.Core.Raux.IZR
                  (CompCert4Lean.Flocq.Core.Raux.Zadd zn
                    (CompCert4Lean.Flocq.Core.Raux.Zpos CompCert4Lean.Flocq.Core.Raux.xH)) :=
              congrArg CompCert4Lean.Flocq.Core.Raux.IZR hsucc.symm
            _ = _ := f2r_izr_add _ _
        let htarget : ctx.adapter.represented (CompCert4Lean.Flocq.Core.Raux.IZR zn1) :=
          Eq.ndrec hplus hruntime.symm
        refine ⟨htarget, ?_⟩
        calc
          ctx.adapter.embed _ htarget = ctx.adapter.embed _ hplus := by congr
          _ = ctx.spec.add (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx zn)
              (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
                (CompCert4Lean.Flocq.Core.Raux.Zpos CompCert4Lean.Flocq.Core.Raux.xH)) := hplus_value
          _ = CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
              (CompCert4Lean.Flocq.Core.Raux.Zadd zn
                (CompCert4Lean.Flocq.Core.Raux.Zpos CompCert4Lean.Flocq.Core.Raux.xH)) :=
            ctx.certificate.sourceLaws.ofZ_add _ _ |>.symm
          _ = CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx zn1 := congrArg _ hsucc
  cases z with
  | Z0 =>
      simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt]
        using hnat 0
  | Zpos p =>
      have hpos : CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
          CompCert4Lean.Flocq.Core.Raux.Zpos p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ
          (CompCert4Lean.Flocq.Core.Raux.Zpos p)
      simpa only [hpos]
        using hnat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
  | Zneg p =>
      have hpos : CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
          CompCert4Lean.Flocq.Core.Raux.Zpos p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ
          (CompCert4Lean.Flocq.Core.Raux.Zpos p)
      obtain ⟨hp, hpvalue⟩ := by
        simpa only [hpos]
          using hnat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
      have hneg : CompCert4Lean.Flocq.Core.Raux.Zopp
          (CompCert4Lean.Flocq.Core.Raux.Zpos p) =
          CompCert4Lean.Flocq.Core.Raux.Zneg p := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
            (-CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Flocq.Core.Raux.Zpos p))) = _
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rfl
      have hrep : ctx.adapter.represented
          (CompCert4Lean.Flocq.Core.Raux.Ropp
            (CompCert4Lean.Flocq.Core.Raux.IZR (CompCert4Lean.Flocq.Core.Raux.Zpos p))) :=
        ctx.adapter.neg_closed _ hp
      have hrun : CompCert4Lean.Flocq.Core.Raux.IZR
          (CompCert4Lean.Flocq.Core.Raux.Zneg p) =
          CompCert4Lean.Flocq.Core.Raux.Ropp
            (CompCert4Lean.Flocq.Core.Raux.IZR (CompCert4Lean.Flocq.Core.Raux.Zpos p)) := by
        rw [← hneg]
        exact f2r_izr_neg _
      let htarget : ctx.adapter.represented
          (CompCert4Lean.Flocq.Core.Raux.IZR (CompCert4Lean.Flocq.Core.Raux.Zneg p)) :=
        Eq.ndrec hrep hrun.symm
      refine ⟨htarget, ?_⟩
      calc
        ctx.adapter.embed _ htarget = ctx.adapter.embed _ hrep := by congr
        _ = ctx.spec.neg (ctx.adapter.embed _ hp) := ctx.adapter.neg_preserved _ hp
        _ = ctx.spec.neg (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
          (CompCert4Lean.Flocq.Core.Raux.Zpos p)) := congrArg ctx.spec.neg hpvalue
        _ = CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
          (CompCert4Lean.Flocq.Core.Raux.Zopp
            (CompCert4Lean.Flocq.Core.Raux.Zpos p)) :=
          (ctx.certificate.sourceLaws.ofZ_neg _).symm
        _ = CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
          (CompCert4Lean.Flocq.Core.Raux.Zneg p) := congrArg _ hneg

private theorem f2r_adapter_bpow (ctx : Exact.Context) (beta : radix) (e : Z) :
    ∃ h : ctx.adapter.represented (CompCert4Lean.Flocq.Core.Raux.bpow beta e),
      ctx.adapter.embed (CompCert4Lean.Flocq.Core.Raux.bpow beta e) h =
        CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e := by
  cases e with
  | Z0 =>
      exact f2r_adapter_one ctx
  | Zpos p =>
      exact f2r_adapter_izr ctx (CompCert4Lean.Flocq.Core.Raux.Zpower_pos beta p)
  | Zneg p =>
      obtain ⟨h, hvalue⟩ := f2r_adapter_izr ctx
        (CompCert4Lean.Flocq.Core.Raux.Zpower_pos beta p)
      let hinv : ctx.adapter.represented
          (CompCert4Lean.Flocq.Core.Raux.Rinv
            (CompCert4Lean.Flocq.Core.Raux.IZR
              (CompCert4Lean.Flocq.Core.Raux.Zpower_pos beta p))) :=
        ctx.adapter.inv_closed _ h
      refine ⟨hinv, ?_⟩
      calc
        ctx.adapter.embed _ hinv = ctx.adapter.embed _ (ctx.adapter.inv_closed _ h) := by congr
        _ = ctx.spec.inv (ctx.adapter.embed _ h) := ctx.adapter.inv_preserved _ h
        _ = ctx.spec.inv (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
          (CompCert4Lean.Flocq.Core.Raux.Zpower_pos beta p)) := congrArg ctx.spec.inv hvalue

theorem F2R_runtime_exact_correspondence_proof :
    ∀ ctx : Exact.Context, F2R_runtime_exact_correspondence ctx := by
  intro ctx beta m e
  obtain ⟨hm, hmvalue⟩ := f2r_adapter_izr ctx m
  obtain ⟨hb, hbvalue⟩ := f2r_adapter_bpow ctx beta e
  let hmul : ctx.adapter.represented
      (CompCert4Lean.Flocq.Core.Raux.Rmult
        (CompCert4Lean.Flocq.Core.Raux.IZR m)
        (CompCert4Lean.Flocq.Core.Raux.bpow beta e)) :=
    ctx.adapter.mul_closed _ hm _ hb
  refine ⟨hmul, ?_⟩
  calc
    ctx.adapter.embed _ hmul = ctx.adapter.embed _ (ctx.adapter.mul_closed _ hm _ hb) := by congr
    _ = ctx.spec.mul (ctx.adapter.embed _ hm) (ctx.adapter.embed _ hb) :=
      ctx.adapter.mul_preserved _ hm _ hb
    _ = ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx m)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) := by
      rw [hmvalue, hbvalue]

end CompCert4Lean.Flocq.Core.Defs
