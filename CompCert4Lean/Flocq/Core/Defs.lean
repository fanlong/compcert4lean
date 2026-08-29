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

structure float (beta : radix) where
  Float ::
  Fnum : Z
  Fexp : Z

export float (Float Fnum Fexp)

/-! Compatibility for existing target modules that used Lean's default
    structure-constructor name before the source-shaped constructor was
    restored.  The actual computational constructor is `Float`. -/
namespace float

abbrev mk {beta : radix} (m e : Z) : float beta :=
  Float m e

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
        Exact.F2R ctx (Float (beta := beta) m e)

end CompCert4Lean.Flocq.Core.Defs
