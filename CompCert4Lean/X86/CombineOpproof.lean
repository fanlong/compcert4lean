import CompCert4Lean.X86.CombineOp
import CompCert4Lean.Backend.RTL

/-!
# Correctness surface for combined x86 operations

The source proofs in `x86/CombineOpproof.v` are migrated in a later proof
phase.  This module records their exact proposition statements against the
canonical combinators from `CombineOp`.
-/

namespace CompCert4Lean.X86.CombineOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.CombineOp

private abbrev valnum := CompCert4Lean.X86.CombineOp.valnum
private abbrev rhs := CompCert4Lean.Backend.CSEdomain.rhs
private abbrev condition := CompCert4Lean.X86.Op.condition
private abbrev addressing := CompCert4Lean.X86.Op.addressing
private abbrev operation := CompCert4Lean.X86.Op.operation
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

def get_op_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu ge sp m rh (valu v)) →
    ∀ (v : valnum) (op : operation) (vl : List valnum),
      get v = some (.Op op vl) →
      eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge sp op (List.map valu vl) m = some (valu v)

def combine_compimm_ne_0_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu ge sp m rh (valu v)) →
    ∀ (x : valnum) (cond : condition) (args : List valnum),
    combine_compimm_ne_0 get x = some (cond, args) →
    eval_condition cond (List.map valu args) m =
        Val.cmp_bool .Cne (valu x) (.Vint Int.zero) ∧
    eval_condition cond (List.map valu args) m =
        Val.cmpu_bool (Mem.valid_pointer m) .Cne (valu x) (.Vint Int.zero)

def combine_compimm_eq_0_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu ge sp m rh (valu v)) →
    ∀ (x : valnum) (cond : condition) (args : List valnum),
    combine_compimm_eq_0 get x = some (cond, args) →
    eval_condition cond (List.map valu args) m =
        Val.cmp_bool .Ceq (valu x) (.Vint Int.zero) ∧
    eval_condition cond (List.map valu args) m =
        Val.cmpu_bool (Mem.valid_pointer m) .Ceq (valu x) (.Vint Int.zero)

def combine_compimm_eq_1_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu ge sp m rh (valu v)) →
    ∀ (x : valnum) (cond : condition) (args : List valnum),
    combine_compimm_eq_1 get x = some (cond, args) →
    eval_condition cond (List.map valu args) m =
        Val.cmp_bool .Ceq (valu x) (.Vint Int.one) ∧
    eval_condition cond (List.map valu args) m =
        Val.cmpu_bool (Mem.valid_pointer m) .Ceq (valu x) (.Vint Int.one)

def combine_compimm_ne_1_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu ge sp m rh (valu v)) →
    ∀ (x : valnum) (cond : condition) (args : List valnum),
    combine_compimm_ne_1 get x = some (cond, args) →
    eval_condition cond (List.map valu args) m =
        Val.cmp_bool .Cne (valu x) (.Vint Int.one) ∧
    eval_condition cond (List.map valu args) m =
        Val.cmpu_bool (Mem.valid_pointer m) .Cne (valu x) (.Vint Int.one)

def combine_cond_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu ge sp m rh (valu v)) →
    ∀ (cond : condition) (args : List valnum) (cond' : condition)
      (args' : List valnum),
    combine_cond get cond args = some (cond', args') →
    eval_condition cond' (List.map valu args') m =
      eval_condition cond (List.map valu args) m

def combine_cond'_soundStatement : Prop :=
  ∀ (m : mem) (valu : valnum → val) (cond : condition)
    (args : List valnum) (res res' : Bool),
    combine_cond' cond args = some res' →
    eval_condition cond (List.map valu args) m = some res →
    res = res'

def combine_addr_32_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu ge sp m rh (valu v)) →
    ∀ (addr : addressing) (args : List valnum) (addr' : addressing)
      (args' : List valnum),
    combine_addr_32 get addr args = some (addr', args') →
    eval_addressing32 ge sp addr' (List.map valu args') =
      eval_addressing32 ge sp addr (List.map valu args)

def combine_addr_64_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu ge sp m rh (valu v)) →
    ∀ (addr : addressing) (args : List valnum) (addr' : addressing)
      (args' : List valnum),
    combine_addr_64 get addr args = some (addr', args') →
    eval_addressing64 ge sp addr' (List.map valu args') =
      eval_addressing64 ge sp addr (List.map valu args)

def combine_addr_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu ge sp m rh (valu v)) →
    ∀ (addr : addressing) (args : List valnum) (addr' : addressing)
      (args' : List valnum),
    combine_addr get addr args = some (addr', args') →
    eval_addressing ge sp addr' (List.map valu args') =
      eval_addressing ge sp addr (List.map valu args)

def combine_op_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu ge sp m rh (valu v)) →
    ∀ (op : operation) (args : List valnum) (op' : operation)
      (args' : List valnum) (r : val),
    combine_op get op args = some (op', args') →
    eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge sp op (List.map valu args) m = some r →
    ∃ r', eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge sp op' (List.map valu args') m = some r' ∧
      Val.lessdef r r'

end CompCert4Lean.X86.CombineOpproof

namespace CompCert4Lean.X86.CombineOpproof

theorem get_op_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    get_op_soundStatement := by
  intro ge sp m get valu get_sound v op vl hget
  have h_eval := get_sound v (.Op op vl) hget
  cases h_eval with
  | op_eval_to _ => assumption

end CompCert4Lean.X86.CombineOpproof

namespace CompCert4Lean.X86.CombineOpproof

open CompCert4Lean.X86.CombineOp
open CompCert4Lean.Backend.RTL
open CompCert4Lean.X86.Op
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values

theorem combine_compimm_eq_1_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    combine_compimm_eq_1_soundStatement := by
  intro ge sp m get valu get_sound x cond args hcombine
  cases hget : get x with
  | none =>
      simp [combine_compimm_eq_1, hget] at hcombine
  | some r =>
      cases r with
      | Load chunk addr vl p =>
          simp [combine_compimm_eq_1, hget] at hcombine
      | Builtin bf args0 =>
          simp [combine_compimm_eq_1, hget] at hcombine
      | Op op ys =>
          cases op with
          | Ocmp c =>
              simp [combine_compimm_eq_1, hget] at hcombine
              have hcond : c = cond := congrArg Prod.fst hcombine
              have hargs : ys = args := congrArg Prod.snd hcombine
              rw [← hcond, ← hargs]
              have hev := get_op_sound ge sp m get valu get_sound x (.Ocmp c) ys hget
              change some (Val.of_optbool (eval_condition c (List.map valu ys) m)) =
                some (valu x) at hev
              cases he : eval_condition c (List.map valu ys) m with
              | none =>
                  rw [he] at hev
                  change some Vundef = some (valu x) at hev
                  have hx : Vundef = valu x := Option.some.inj hev
                  rw [← hx]
                  simp [Val.cmp_bool, Val.cmpu_bool]
              | some b =>
                  rw [he] at hev
                  cases b
                  · change some Vfalse = some (valu x) at hev
                    have hx : Vfalse = valu x := Option.some.inj hev
                    rw [← hx]
                    have hzeroone : CompCert4Lean.Lib.Integers.Int.cmp
                        .Ceq CompCert4Lean.Lib.Integers.Int.zero
                        CompCert4Lean.Lib.Integers.Int.one = false := by decide
                    have hzerooneu : CompCert4Lean.Lib.Integers.Int.cmpu
                        .Ceq CompCert4Lean.Lib.Integers.Int.zero
                        CompCert4Lean.Lib.Integers.Int.one = false := by decide
                    simp [Vfalse, Val.cmp_bool, Val.cmpu_bool, hzeroone, hzerooneu]
                  · change some Vtrue = some (valu x) at hev
                    have hx : Vtrue = valu x := Option.some.inj hev
                    rw [← hx]
                    have honeone : CompCert4Lean.Lib.Integers.Int.cmp
                        .Ceq CompCert4Lean.Lib.Integers.Int.one
                        CompCert4Lean.Lib.Integers.Int.one = true := by decide
                    have honeoneu : CompCert4Lean.Lib.Integers.Int.cmpu
                        .Ceq CompCert4Lean.Lib.Integers.Int.one
                        CompCert4Lean.Lib.Integers.Int.one = true := by decide
                    simp [Vtrue, Val.cmp_bool, Val.cmpu_bool, honeone, honeoneu]
          | _ =>
              simp [combine_compimm_eq_1, hget] at hcombine

end CompCert4Lean.X86.CombineOpproof

namespace CompCert4Lean.X86.CombineOpproof

open CompCert4Lean.X86.CombineOp
open CompCert4Lean.Backend.RTL
open CompCert4Lean.X86.Op
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values

theorem combine_compimm_ne_1_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    combine_compimm_ne_1_soundStatement := by
  intro ge sp m get valu get_sound x cond args hcombine
  cases hget : get x with
  | none =>
      simp [combine_compimm_ne_1, hget] at hcombine
  | some r =>
      cases r with
      | Load chunk addr vl p =>
          simp [combine_compimm_ne_1, hget] at hcombine
      | Builtin bf args0 =>
          simp [combine_compimm_ne_1, hget] at hcombine
      | Op op ys =>
          cases op with
          | Ocmp c =>
              simp [combine_compimm_ne_1, hget] at hcombine
              have hcond : negate_condition c = cond := congrArg Prod.fst hcombine
              have hargs : ys = args := congrArg Prod.snd hcombine
              rw [← hcond, ← hargs]
              have hev := get_op_sound ge sp m get valu get_sound x (.Ocmp c) ys hget
              change some (Val.of_optbool (eval_condition c (List.map valu ys) m)) =
                some (valu x) at hev
              rw [eval_negate_condition]
              cases he : eval_condition c (List.map valu ys) m with
              | none =>
                  rw [he] at hev
                  change some Vundef = some (valu x) at hev
                  have hx : Vundef = valu x := Option.some.inj hev
                  rw [← hx]
                  simp [Val.cmp_bool, Val.cmpu_bool]
              | some b =>
                  rw [he] at hev
                  cases b
                  · change some Vfalse = some (valu x) at hev
                    have hx : Vfalse = valu x := Option.some.inj hev
                    rw [← hx]
                    have hzeroone : CompCert4Lean.Lib.Integers.Int.cmp
                        .Cne CompCert4Lean.Lib.Integers.Int.zero
                        CompCert4Lean.Lib.Integers.Int.one = true := by decide
                    have hzerooneu : CompCert4Lean.Lib.Integers.Int.cmpu
                        .Cne CompCert4Lean.Lib.Integers.Int.zero
                        CompCert4Lean.Lib.Integers.Int.one = true := by decide
                    simp [Vfalse, Val.cmp_bool, Val.cmpu_bool, hzeroone, hzerooneu]
                  · change some Vtrue = some (valu x) at hev
                    have hx : Vtrue = valu x := Option.some.inj hev
                    rw [← hx]
                    have honeone : CompCert4Lean.Lib.Integers.Int.cmp
                        .Cne CompCert4Lean.Lib.Integers.Int.one
                        CompCert4Lean.Lib.Integers.Int.one = false := by decide
                    have honeoneu : CompCert4Lean.Lib.Integers.Int.cmpu
                        .Cne CompCert4Lean.Lib.Integers.Int.one
                        CompCert4Lean.Lib.Integers.Int.one = false := by decide
                    simp [Vtrue, Val.cmp_bool, Val.cmpu_bool, honeone, honeoneu]
          | _ =>
              simp [combine_compimm_ne_1, hget] at hcombine

end CompCert4Lean.X86.CombineOpproof

namespace CompCert4Lean.X86.CombineOpproof

open CompCert4Lean.X86.CombineOp
open CompCert4Lean.Backend.RTL
open CompCert4Lean.X86.Op
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values

 theorem combine_compimm_ne_0_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    combine_compimm_ne_0_soundStatement := by
  intro ge sp m get valu get_sound x cond args hcombine
  cases hget : get x with
  | none =>
      simp [combine_compimm_ne_0, hget] at hcombine
  | some r =>
      cases r with
      | Load chunk addr vl p =>
          simp [combine_compimm_ne_0, hget] at hcombine
      | Builtin bf args0 =>
          simp [combine_compimm_ne_0, hget] at hcombine
      | Op op ys =>
          cases op with
          | Ocmp c =>
              simp [combine_compimm_ne_0, hget] at hcombine
              have hcond : c = cond := congrArg Prod.fst hcombine
              have hargs : ys = args := congrArg Prod.snd hcombine
              rw [← hcond, ← hargs]
              have hev := get_op_sound ge sp m get valu get_sound x (.Ocmp c) ys hget
              change some (Val.of_optbool (eval_condition c (List.map valu ys) m)) =
                some (valu x) at hev
              cases he : eval_condition c (List.map valu ys) m with
              | none =>
                  rw [he] at hev
                  change some Vundef = some (valu x) at hev
                  have hx : Vundef = valu x := Option.some.inj hev
                  rw [← hx]
                  simp [Val.cmp_bool, Val.cmpu_bool]
              | some b =>
                  rw [he] at hev
                  cases b
                  · change some Vfalse = some (valu x) at hev
                    have hx : Vfalse = valu x := Option.some.inj hev
                    rw [← hx]
                    have hzerozero : CompCert4Lean.Lib.Integers.Int.cmp
                        .Cne CompCert4Lean.Lib.Integers.Int.zero
                        CompCert4Lean.Lib.Integers.Int.zero = false := by decide
                    have hzerozerou : CompCert4Lean.Lib.Integers.Int.cmpu
                        .Cne CompCert4Lean.Lib.Integers.Int.zero
                        CompCert4Lean.Lib.Integers.Int.zero = false := by decide
                    simp [Vfalse, Val.cmp_bool, Val.cmpu_bool, hzerozero, hzerozerou]
                  · change some Vtrue = some (valu x) at hev
                    have hx : Vtrue = valu x := Option.some.inj hev
                    rw [← hx]
                    have honezero : CompCert4Lean.Lib.Integers.Int.cmp
                        .Cne CompCert4Lean.Lib.Integers.Int.one
                        CompCert4Lean.Lib.Integers.Int.zero = true := by decide
                    have honezerou : CompCert4Lean.Lib.Integers.Int.cmpu
                        .Cne CompCert4Lean.Lib.Integers.Int.one
                        CompCert4Lean.Lib.Integers.Int.zero = true := by decide
                    simp [Vtrue, Val.cmp_bool, Val.cmpu_bool, honezero, honezerou]
          | Oandimm n =>
              simp [combine_compimm_ne_0, hget] at hcombine
              have hcond : .Cmasknotzero n = cond := congrArg Prod.fst hcombine
              have hargs : ys = args := congrArg Prod.snd hcombine
              rw [← hcond, ← hargs]
              have hev := get_op_sound ge sp m get valu get_sound x (.Oandimm n) ys hget
              cases ys with
              | nil =>
                  change none = some (valu x) at hev
                  cases hev
              | cons y ys =>
                  cases ys with
                  | nil =>
                      change some (Val.and (valu y) (.Vint n)) = some (valu x) at hev
                      have hx : Val.and (valu y) (.Vint n) = valu x := Option.some.inj hev
                      rw [← hx]
                      simp only [List.map]
                      have hcmp_ne : ∀ p q,
                          CompCert4Lean.Lib.Integers.Int.cmp .Cne p q =
                            !(CompCert4Lean.Lib.Integers.Int.eq p q) := by
                        intro p q
                        simp [CompCert4Lean.Lib.Integers.Int.cmp,
                          CompCert4Lean.Lib.Integers.WordCore.cmp,
                          CompCert4Lean.Lib.Integers.Int.eq,
                          CompCert4Lean.Lib.Integers.WordCore.eq]
                      have hcmpu_ne : ∀ p q,
                          CompCert4Lean.Lib.Integers.Int.cmpu .Cne p q =
                            !(CompCert4Lean.Lib.Integers.Int.eq p q) := by
                        intro p q
                        simp [CompCert4Lean.Lib.Integers.Int.cmpu,
                          CompCert4Lean.Lib.Integers.WordCore.cmpu,
                          CompCert4Lean.Lib.Integers.Int.eq,
                          CompCert4Lean.Lib.Integers.WordCore.eq]
                      cases hy : valu y <;>
                        simp [hy, eval_condition, Val.maskzero_bool, Val.cmp_bool,
                          Val.cmpu_bool, Val.and, hcmp_ne, hcmpu_ne]
                  | cons y' ys' =>
                      change none = some (valu x) at hev
                      cases hev
          | Oxorimm n =>
              simp [combine_compimm_ne_0, hget] at hcombine
              have hcond : .Ccompimm .Cne n = cond := congrArg Prod.fst hcombine
              have hargs : ys = args := congrArg Prod.snd hcombine
              rw [← hcond, ← hargs]
              have hev := get_op_sound ge sp m get valu get_sound x (.Oxorimm n) ys hget
              cases ys with
              | nil =>
                  change none = some (valu x) at hev
                  cases hev
              | cons y ys =>
                  cases ys with
                  | nil =>
                      change some (Val.xor (valu y) (.Vint n)) = some (valu x) at hev
                      have hx : Val.xor (valu y) (.Vint n) = valu x := Option.some.inj hev
                      rw [← hx]
                      simp only [List.map]
                      cases hy : valu y <;>
                        simp [hy, eval_condition, Val.cmp_bool, Val.cmpu_bool, Val.xor]
                      · have hcmp_ne : ∀ p q,
                            CompCert4Lean.Lib.Integers.Int.cmp .Cne p q =
                              !(CompCert4Lean.Lib.Integers.Int.eq p q) := by
                          intro p q
                          simp [CompCert4Lean.Lib.Integers.Int.cmp,
                            CompCert4Lean.Lib.Integers.WordCore.cmp,
                            CompCert4Lean.Lib.Integers.Int.eq,
                            CompCert4Lean.Lib.Integers.WordCore.eq]
                        have hcmpu_ne : ∀ p q,
                            CompCert4Lean.Lib.Integers.Int.cmpu .Cne p q =
                              !(CompCert4Lean.Lib.Integers.Int.eq p q) := by
                          intro p q
                          simp [CompCert4Lean.Lib.Integers.Int.cmpu,
                            CompCert4Lean.Lib.Integers.WordCore.cmpu,
                            CompCert4Lean.Lib.Integers.Int.eq,
                            CompCert4Lean.Lib.Integers.WordCore.eq]
                        rw [hcmp_ne, hcmp_ne, hcmpu_ne]
                        rw [CompCert4Lean.Lib.Integers.Int.xor_is_zero_proof]
                        constructor <;> rfl
                  | cons y' ys' =>
                      change none = some (valu x) at hev
                      cases hev
          | _ =>
              simp [combine_compimm_ne_0, hget] at hcombine

end CompCert4Lean.X86.CombineOpproof

namespace CompCert4Lean.X86.CombineOpproof

open CompCert4Lean.X86.CombineOp
open CompCert4Lean.X86.Op
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

private theorem combine_compimm_eq_0_map_negate_aux
    (get : valnum → Option rhs) (x : valnum) :
    combine_compimm_eq_0 get x =
      (combine_compimm_ne_0 get x).map (fun p => (negate_condition p.1, p.2)) := by
  unfold combine_compimm_eq_0 combine_compimm_ne_0
  cases get x with
  | none => rfl
  | some r =>
      cases r with
      | Op op ys => cases op <;> rfl
      | Load _ _ _ _ => rfl
      | Builtin _ _ => rfl

theorem combine_compimm_eq_0_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    combine_compimm_eq_0_soundStatement := by
  intro ge sp m get valu get_sound x cond args hcombine
  have hmap (b : Option Bool) :
      CompCert4Lean.Lib.Coqlib.option_map Bool.not b = b.map Bool.not := by
    cases b <;> rfl
  rw [combine_compimm_eq_0_map_negate_aux] at hcombine
  cases hne : combine_compimm_ne_0 get x with
  | none => simp [hne] at hcombine
  | some p =>
      rcases p with ⟨c, ys⟩
      simp only [hne, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcombine
      rcases hcombine with ⟨rfl, rfl⟩
      have h := combine_compimm_ne_0_sound ge sp m get valu get_sound x c ys hne
      rw [eval_negate_condition]
      constructor
      · rw [h.1]
        simpa only [hmap, negate_comparison] using
          (Val.negate_cmp_bool .Cne (valu x) (.Vint Int.zero)).symm
      · rw [h.2]
        simpa only [hmap, negate_comparison] using
          (Val.negate_cmpu_bool (Mem.valid_pointer m) .Cne
            (valu x) (.Vint Int.zero)).symm

end CompCert4Lean.X86.CombineOpproof

namespace CompCert4Lean.X86.CombineOpproof

open CompCert4Lean.X86.CombineOp
open CompCert4Lean.X86.Op
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

private theorem combine_offset_some_aux (a a' : addressing)
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (h : offset_addressing a n = some a') :
    offset_addressing_total a n = a' := by
  unfold offset_addressing at h
  dsimp only at h
  split at h
  · exact Option.some.inj h
  · cases h

theorem combine_addr_32_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    combine_addr_32_soundStatement := by
  intro ge sp m get valu get_sound addr args addr' args' h
  unfold combine_addr_32 at h
  split at h
  next n x =>
    split at h
    next a ys hget =>
      split at h
      next a' hoff =>
        have hev := get_op_sound ge sp m get valu get_sound x (.Olea a) ys hget
        change eval_addressing32 ge sp a (List.map valu ys) = some (valu x) at hev
        have hp := Option.some.inj h
        cases hp
        rw [← combine_offset_some_aux a addr' n hoff]
        exact eval_offset_addressing_total_32 _ _ ge sp a (List.map valu args') n (valu x) hev
      next => cases h
    next => cases h
  next => cases h

end CompCert4Lean.X86.CombineOpproof

namespace CompCert4Lean.X86.CombineOpproof

open CompCert4Lean.X86.CombineOp
open CompCert4Lean.X86.Op

theorem combine_addr_64_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    combine_addr_64_soundStatement := by
  intro ge sp m get valu get_sound addr args addr' args' h
  unfold combine_addr_64 at h
  split at h
  next n x =>
    split at h
    next a ys hget =>
      split at h
      next a' hoff =>
        have hev := get_op_sound ge sp m get valu get_sound x (.Oleal a) ys hget
        change eval_addressing64 ge sp a (List.map valu ys) = some (valu x) at hev
        have hp := Option.some.inj h
        cases hp
        rw [← combine_offset_some_aux a addr' n hoff]
        exact eval_offset_addressing_total_64 _ _ ge sp a (List.map valu args') n (valu x) hev
      next => cases h
    next => cases h
  next => cases h

end CompCert4Lean.X86.CombineOpproof

namespace CompCert4Lean.X86.CombineOpproof

open CompCert4Lean.X86.CombineOp
open CompCert4Lean.X86.Op

theorem combine_cond_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    combine_cond_soundStatement := by
  intro ge sp m get valu get_sound cond args cond' args' h
  unfold combine_cond at h
  split at h
  next n x =>
    split at h
    next hn =>
      subst n
      exact (combine_compimm_ne_0_sound ge sp m get valu get_sound x cond' args' h).1
    next =>
      split at h
      next hn =>
        subst n
        exact (combine_compimm_ne_1_sound ge sp m get valu get_sound x cond' args' h).1
      next => cases h
  next n x =>
    split at h
    next hn =>
      subst n
      exact (combine_compimm_eq_0_sound ge sp m get valu get_sound x cond' args' h).1
    next =>
      split at h
      next hn =>
        subst n
        exact (combine_compimm_eq_1_sound ge sp m get valu get_sound x cond' args' h).1
      next => cases h
  next n x =>
    split at h
    next hn =>
      subst n
      exact (combine_compimm_ne_0_sound ge sp m get valu get_sound x cond' args' h).2
    next =>
      split at h
      next hn =>
        subst n
        exact (combine_compimm_ne_1_sound ge sp m get valu get_sound x cond' args' h).2
      next => cases h
  next n x =>
    split at h
    next hn =>
      subst n
      exact (combine_compimm_eq_0_sound ge sp m get valu get_sound x cond' args' h).2
    next =>
      split at h
      next hn =>
        subst n
        exact (combine_compimm_eq_1_sound ge sp m get valu get_sound x cond' args' h).2
      next => cases h
  next => cases h

end CompCert4Lean.X86.CombineOpproof

namespace CompCert4Lean.X86.CombineOpproof

open CompCert4Lean.X86.CombineOp
open CompCert4Lean.X86.Op

theorem combine_addr_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    combine_addr_soundStatement := by
  intro ge sp m get valu get_sound addr args addr' args' h
  by_cases hp : CompCert4Lean.X86_64.Archi.ptr64
  · simp [combine_addr, eval_addressing, hp] at h ⊢
    exact combine_addr_64_sound ge sp m get valu get_sound addr args addr' args' h
  · simp [combine_addr, eval_addressing, hp] at h ⊢
    exact combine_addr_32_sound ge sp m get valu get_sound addr args addr' args' h

end CompCert4Lean.X86.CombineOpproof
