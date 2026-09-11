import CompCert4Lean.Config
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Recursion

/-!
# x86-64 architecture parameters

Architecture-dependent constants for CompCert's x86 backend in 64-bit mode.
The target ABI parameter is represented by an observation of the immutable
compiler configuration shared by executable and theorem-facing consumers.
-/

namespace CompCert4Lean.X86_64.Archi

private abbrev positive :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive

private abbrev Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z

private abbrev iterNat :=
  CompCert4Lean.Foundation.Recursion.Rocq.Coq.Arith.Wf_nat.iter_nat

def ptr64 : Bool :=
  true

def big_endian : Bool :=
  false

def align_int64 : Z :=
  .Zpos (.xO (.xO (.xO .xH)))

def align_float64 : Z :=
  .Zpos (.xO (.xO (.xO .xH)))

def splitlong : Bool :=
  !ptr64

def splitlong_ptr32Statement : Prop :=
  splitlong = true → ptr64 = false

def default_nan_64 : Bool × positive :=
  (true, iterNat 51 positive (.xO) .xH)

def default_nan_32 : Bool × positive :=
  (true, iterNat 22 positive (.xO) .xH)

def choose_nan_64 (l : List (Bool × positive)) : Bool × positive :=
  match l with
  | [] => default_nan_64
  | n :: _ => n

def choose_nan_32 (l : List (Bool × positive)) : Bool × positive :=
  match l with
  | [] => default_nan_32
  | n :: _ => n

def choose_nan_64_idemStatement : Prop :=
  ∀ n : Bool × positive,
    choose_nan_64 [n, n] = choose_nan_64 [n]

def choose_nan_32_idemStatement : Prop :=
  ∀ n : Bool × positive,
    choose_nan_32 [n, n] = choose_nan_32 [n]

universe u

def fma_order {A : Type u} (x y z : A) : (A × A) × A :=
  ((x, y), z)

def fma_invalid_mul_is_nan : Bool :=
  false

def float_of_single_preserves_sNaN : Bool :=
  false

def float_conversion_default_nan : Bool :=
  false

def win64 (cfg : Config.CompilerConfig) : Bool :=
  match cfg.x86_64ABI with
  | .systemV => false
  | .windows => true

end CompCert4Lean.X86_64.Archi

namespace CompCert4Lean.X86_64.Archi

theorem splitlong_ptr32 : splitlong_ptr32Statement := by
  unfold splitlong_ptr32Statement splitlong ptr64
  decide

theorem choose_nan_64_idem : choose_nan_64_idemStatement := by
  intro n
  rfl

theorem choose_nan_32_idem : choose_nan_32_idemStatement := by
  intro n
  rfl

end CompCert4Lean.X86_64.Archi
