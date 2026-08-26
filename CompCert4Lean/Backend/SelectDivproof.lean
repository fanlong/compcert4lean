import CompCert4Lean.Backend.SelectDiv
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Values
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Floats
import CompCert4Lean.Lib.Integers

/-!
# Correctness surface for integer and floating-point division selection

The source file is proof-heavy.  This migration pass records the exact
propositions assigned to the later proof-migration phase as transparent
statement descriptors.
-/

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.SelectDiv
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Floats
open CompCert4Lean.Lib.Integers

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev BexactInverseCertificate :=
  CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
private abbrev CCZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev env := CompCert4Lean.Backend.Cminor.env
private abbrev zLe := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
private abbrev zLt := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt
private abbrev zGe := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.ge
private abbrev zAdd := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
private abbrev zSub := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
private abbrev zMul := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
private abbrev zOpp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
private abbrev zDiv := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
private abbrev zQuot := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.quot
private abbrev zShiftr := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr
private abbrev z0 : CCZ := .Z0
private abbrev z1 : CCZ := .Zpos .xH
private abbrev z32 : CCZ := ZArith.BinInt.Z.of_nat 32
private abbrev z64 : CCZ := ZArith.BinInt.Z.of_nat 64
private abbrev intRepr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev intUnsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev intSigned := CompCert4Lean.Lib.Integers.Int.signed
private abbrev intDivs := CompCert4Lean.Lib.Integers.Int.divs
private abbrev intDivu := CompCert4Lean.Lib.Integers.Int.divu
private abbrev intAdd := CompCert4Lean.Lib.Integers.Int.add
private abbrev intSub := CompCert4Lean.Lib.Integers.Int.sub
private abbrev intShr := CompCert4Lean.Lib.Integers.Int.shr
private abbrev intShru := CompCert4Lean.Lib.Integers.Int.shru
private abbrev intMul := CompCert4Lean.Lib.Integers.Int.mul
private abbrev int64Repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev int64Unsigned := CompCert4Lean.Lib.Integers.Int64.unsigned
private abbrev int64Signed := CompCert4Lean.Lib.Integers.Int64.signed
private abbrev int64Divs := CompCert4Lean.Lib.Integers.Int64.divs
private abbrev int64Divu := CompCert4Lean.Lib.Integers.Int64.divu
private abbrev int64Add := CompCert4Lean.Lib.Integers.Int64.add
private abbrev int64Sub := CompCert4Lean.Lib.Integers.Int64.sub
private abbrev int64Mul := CompCert4Lean.Lib.Integers.Int64.mul
private abbrev int64Shru := CompCert4Lean.Lib.Integers.Int64.shru
private abbrev int64Shr' := CompCert4Lean.Lib.Integers.Int64.shr'
private abbrev int64Shru' := CompCert4Lean.Lib.Integers.Int64.shru'
private abbrev int64Mulhs := fun (x y : CCInt64) =>
  int64Repr (zShiftr (zMul (int64Signed x) (int64Signed y)) Int64.zwordsize)
private abbrev int64Mulhu := fun (x y : CCInt64) =>
  int64Repr (zShiftr (zMul (int64Unsigned x) (int64Unsigned y)) Int64.zwordsize)
private abbrev intMulhs := fun (x y : CCInt) =>
  intRepr (zShiftr (zMul (intSigned x) (intSigned y)) Int.zwordsize)
private abbrev intMulhu := fun (x y : CCInt) =>
  intRepr (zShiftr (zMul (intUnsigned x) (intUnsigned y)) Int.zwordsize)

private def boolOfSumbool {P Q : Prop} :
    CompCert4Lean.Foundation.Logic.Support.Sumbool P Q → Bool
  | .left _ => true
  | .right _ => false

private def zltBool (x y : CCZ) : Bool := boolOfSumbool (CompCert4Lean.Lib.Coqlib.zlt x y)

def Zdiv_mul_posStatement : Prop :=
  ∀ N : CCZ,
    zLe z0 N →
    ∀ d : CCZ,
      zLt z0 d →
      ∀ (m l : CCZ),
      zLe z0 l →
      (zLe (two_p (zAdd N l)) (zMul m d) ∧
        zLe (zMul m d) (zAdd (two_p (zAdd N l)) (two_p l))) →
      ∀ n : CCZ,
        (zLe z0 n ∧ zLt n (two_p N)) →
        zDiv n d = zDiv (zMul m n) (two_p (zAdd N l))

def Zdiv_unique_2Statement : Prop :=
  ∀ (x y q : CCZ),
    zLt z0 y →
    (zLt z0 (zSub (zMul y q) x) ∧
      zLe (zSub (zMul y q) x) y) →
    zDiv x y = zSub q z1

def Zdiv_mul_oppStatement : Prop :=
  ∀ N : CCZ,
    zLe z0 N →
    ∀ d : CCZ,
      zLt z0 d →
      ∀ (m l : CCZ),
      zLe z0 l →
      (zLt (two_p (zAdd N l)) (zMul m d) ∧
        zLe (zMul m d) (zAdd (two_p (zAdd N l)) (two_p l))) →
      ∀ n : CCZ,
        (zLt z0 n ∧ zLe n (two_p N)) →
        zDiv n d = zSub (zOpp (zDiv (zMul m (zOpp n)) (two_p (zAdd N l)))) z1

def Zquot_mulStatement : Prop :=
  ∀ N : CCZ,
    zLe z0 N →
    ∀ d : CCZ,
      zLt z0 d →
      ∀ (m l : CCZ),
      zLe z0 l →
      (zLt (two_p (zAdd N l)) (zMul m d) ∧
        zLe (zMul m d) (zAdd (two_p (zAdd N l)) (two_p l))) →
      ∀ n : CCZ,
        (zLe (zOpp (two_p N)) n ∧ zLt n (two_p N)) →
        zQuot n d =
          zAdd (zDiv (zMul m n) (two_p (zAdd N l)))
            (if zltBool n z0 then z1 else z0)

def divs_mul_params_soundStatement : Prop :=
  ∀ (d m p : CCZ),
    divs_mul_params d = some (p, m) →
    (zLe z0 m ∧ zLt m Int.modulus) ∧
      (zLe z0 p ∧ zLt p z32) ∧
      ∀ n : CCZ,
        (zLe Int.min_signed n ∧ zLe n Int.max_signed) →
        zQuot n d =
          zAdd (zDiv (zMul m n) (two_p (zAdd z32 p)))
            (if zltBool n z0 then z1 else z0)

def divu_mul_params_soundStatement : Prop :=
  ∀ (d m p : CCZ),
    divu_mul_params d = some (p, m) →
    (zLe z0 m ∧ zLt m Int.modulus) ∧
      (zLe z0 p ∧ zLt p z32) ∧
      ∀ n : CCZ,
        (zLe z0 n ∧ zLt n Int.modulus) →
        zDiv n d = zDiv (zMul m n) (two_p (zAdd z32 p))

def divs_mul_shift_genStatement : Prop :=
  ∀ (x y : CCInt) (m p : CCZ),
    divs_mul_params (intSigned y) = some (p, m) →
    (zLe z0 m ∧ zLt m Int.modulus) ∧ (zLe z0 p ∧ zLt p z32) ∧
      intDivs x y =
        intAdd (intShr (intRepr (zDiv (zMul (intSigned x) m) Int.modulus))
          (intRepr p))
          (intShru x (intRepr (zSub Int.zwordsize z1)))

def divs_mul_shift_1Statement : Prop :=
  ∀ (x y : CCInt) (m p : CCZ),
    divs_mul_params (intSigned y) = some (p, m) →
    zLt m Int.half_modulus →
    (zLe z0 p ∧ zLt p z32) ∧
      intDivs x y =
        intAdd (intShr (intMulhs x (intRepr m)) (intRepr p))
          (intShru x (intRepr (zSub Int.zwordsize z1)))

def divs_mul_shift_2Statement : Prop :=
  ∀ (x y : CCInt) (m p : CCZ),
    divs_mul_params (intSigned y) = some (p, m) →
    zGe m Int.half_modulus →
    (zLe z0 p ∧ zLt p z32) ∧
      intDivs x y =
        intAdd
          (intShr (intAdd (intMulhs x (intRepr m)) x) (intRepr p))
          (intShru x (intRepr (zSub Int.zwordsize z1)))

def divu_mul_shiftStatement : Prop :=
  ∀ (x y : CCInt) (m p : CCZ),
    divu_mul_params (intUnsigned y) = some (p, m) →
    (zLe z0 p ∧ zLt p z32) ∧
      intDivu x y = intShru (intMulhu x (intRepr m)) (intRepr p)

def divls_mul_params_soundStatement : Prop :=
  ∀ (d m p : CCZ),
    divls_mul_params d = some (p, m) →
    (zLe z0 m ∧ zLt m Int64.modulus) ∧
      (zLe z0 p ∧ zLt p z64) ∧
      ∀ n : CCZ,
        (zLe Int64.min_signed n ∧ zLe n Int64.max_signed) →
        zQuot n d =
          zAdd (zDiv (zMul m n) (two_p (zAdd z64 p)))
            (if zltBool n z0 then z1 else z0)

def divlu_mul_params_soundStatement : Prop :=
  ∀ (d m p : CCZ),
    divlu_mul_params d = some (p, m) →
    (zLe z0 m ∧ zLt m Int64.modulus) ∧
      (zLe z0 p ∧ zLt p z64) ∧
      ∀ n : CCZ,
        (zLe z0 n ∧ zLt n Int64.modulus) →
        zDiv n d = zDiv (zMul m n) (two_p (zAdd z64 p))

def int64_shr'_div_two_pStatement : Prop :=
  ∀ (x : CCInt64) (y : CCInt),
    int64Shr' x y = int64Repr (zDiv (int64Signed x) (two_p (intUnsigned y)))

def divls_mul_shift_genStatement : Prop :=
  ∀ (x y : CCInt64) (m p : CCZ),
    divls_mul_params (int64Signed y) = some (p, m) →
    (zLe z0 m ∧ zLt m Int64.modulus) ∧ (zLe z0 p ∧ zLt p z64) ∧
      int64Divs x y =
        int64Add
          (int64Shr'
            (int64Repr (zDiv (zMul (int64Signed x) m) Int64.modulus))
            (intRepr p))
          (int64Shru x (int64Repr (zSub Int64.zwordsize z1)))

def divls_mul_shift_1Statement : Prop :=
  ∀ (x y : CCInt64) (m p : CCZ),
    divls_mul_params (int64Signed y) = some (p, m) →
    zLt m Int64.half_modulus →
    (zLe z0 p ∧ zLt p z64) ∧
      int64Divs x y =
        int64Add (int64Shr' (int64Mulhs x (int64Repr m)) (intRepr p))
          (int64Shru' x (intRepr (zSub Int64.zwordsize z1)))

def divls_mul_shift_2Statement : Prop :=
  ∀ (x y : CCInt64) (m p : CCZ),
    divls_mul_params (int64Signed y) = some (p, m) →
    zGe m Int64.half_modulus →
    (zLe z0 p ∧ zLt p z64) ∧
      int64Divs x y =
        int64Add
          (int64Shr' (int64Add (int64Mulhs x (int64Repr m)) x) (intRepr p))
          (int64Shru' x (intRepr (zSub Int64.zwordsize z1)))

def int64_shru'_div_two_pStatement : Prop :=
  ∀ (x : CCInt64) (y : CCInt),
    int64Shru' x y = int64Repr (zDiv (int64Unsigned x) (two_p (intUnsigned y)))

def divlu_mul_shiftStatement : Prop :=
  ∀ (x y : CCInt64) (m p : CCZ),
    divlu_mul_params (int64Unsigned y) = some (p, m) →
    (zLe z0 p ∧ zLt p z64) ∧
      int64Divu x y = int64Shru' (int64Mulhu x (int64Repr m)) (intRepr p)

def is_intconst_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (v : val) (a : expr) (n : CCInt) (le : letenv),
      is_intconst a = some n →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a v →
      v = .Vint n

def eval_divu_mulStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (x y : CCInt) (p M : CCZ),
      divu_mul_params (intUnsigned y) = some (p, M) →
      nth_error le 0 = some (.Vint x) →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divu_mul p M)
        (.Vint (intDivu x y))

def eval_divuimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (e1 : expr) (x : val) (n2 : CCInt) (z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le e1 x →
      Val.divu x (.Vint n2) = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divuimm cfg e1 n2) v ∧
        Val.lessdef z v

def eval_divuStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le b y →
      Val.divu x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divu cfg a b) v ∧
        Val.lessdef z v

def eval_mod_from_divStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (n : CCInt) (x y : CCInt),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a (.Vint y) →
      nth_error le 0 = some (.Vint x) →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (mod_from_div a n)
        (.Vint (intSub x (intMul y n)))

def eval_moduimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (e1 : expr) (x : val) (n2 : CCInt) (z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le e1 x →
      Val.modu x (.Vint n2) = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (moduimm cfg e1 n2) v ∧
        Val.lessdef z v

def eval_moduStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le b y →
      Val.modu x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (modu cfg a b) v ∧
        Val.lessdef z v

def eval_divs_mulStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (x y : CCInt) (p M : CCZ),
      divs_mul_params (intSigned y) = some (p, M) →
      nth_error le 0 = some (.Vint x) →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divs_mul p M)
        (.Vint (intDivs x y))

def eval_divsimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (e1 : expr) (x : val) (n2 : CCInt) (z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le e1 x →
      Val.divs x (.Vint n2) = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divsimm cfg e1 n2) v ∧
        Val.lessdef z v

def eval_divsStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le b y →
      Val.divs x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divs cfg a b) v ∧
        Val.lessdef z v

def eval_modsimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (e1 : expr) (x : val) (n2 : CCInt) (z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le e1 x →
      Val.mods x (.Vint n2) = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (modsimm cfg e1 n2) v ∧
        Val.lessdef z v

def eval_modsStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le b y →
      Val.mods x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (mods cfg a b) v ∧
        Val.lessdef z v

def eval_modl_from_divlStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (n : CCInt64) (x y : CCInt64),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a (.Vlong y) →
      nth_error le 0 = some (.Vlong x) →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (modl_from_divl a n)
        (.Vlong (int64Sub x (int64Mul y n)))

def eval_divlu_mullStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (x y : CCInt64) (p M : CCZ),
      divlu_mul_params (int64Unsigned y) = some (p, M) →
      nth_error le 0 = some (.Vlong x) →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divlu_mull p M)
        (.Vlong (int64Divu x y))

def eval_divluStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le b y →
      Val.divlu x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divlu cfg a b) v ∧
        Val.lessdef z v

def eval_modluStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le b y →
      Val.modlu x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (modlu cfg a b) v ∧
        Val.lessdef z v

def eval_divls_mullStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (x y : CCInt64) (p M : CCZ),
      divls_mul_params (int64Signed y) = some (p, M) →
      nth_error le 0 = some (.Vlong x) →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divls_mull p M)
        (.Vlong (int64Divs x y))

def eval_divlsStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le b y →
      Val.divls x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divls cfg a b) v ∧
        Val.lessdef z v

def eval_modlsStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le b y →
      Val.modls x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (modls cfg a b) v ∧
        Val.lessdef z v

def eval_divfStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    [certificate : BexactInverseCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le b y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le
        (divf (certificate := certificate) a b) v ∧
        Val.lessdef (Val.divf x y) v

def eval_divfsStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    [certificate : BexactInverseCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le b y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le
        (divfs (certificate := certificate) a b) v ∧
        Val.lessdef (Val.divfs x y) v

end CompCert4Lean.Backend.SelectDivproof
