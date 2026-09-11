import CompCert4Lean.Backend.SelectDiv
import CompCert4Lean.Backend.SplitLongproof
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
open CompCert4Lean.Backend.SplitLong
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
      CompCert4Lean.Backend.SelectDiv.is_intconst a = some n →
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
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (n : CCInt64) (x y : CCInt64),
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le a (.Vlong y) →
      nth_error le 0 = some (.Vlong x) →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (modl_from_divl (hf := hf) a n)
        (.Vlong (int64Sub x (int64Mul y n)))

def eval_divlu_mullStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (x y : CCInt64) (p M : CCZ),
      divlu_mul_params (int64Unsigned y) = some (p, M) →
      nth_error le 0 = some (.Vlong x) →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divlu_mull (hf := hf) p M)
        (.Vlong (int64Divu x y))

def eval_divluStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (hf : helper_functions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
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
        xi (Genv.globalenv prog) sp e m le (divlu (hf := hf) cfg a b) v ∧
        Val.lessdef z v

def eval_modluStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (hf : helper_functions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
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
        xi (Genv.globalenv prog) sp e m le (modlu (hf := hf) cfg a b) v ∧
        Val.lessdef z v

def eval_divls_mullStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (x y : CCInt64) (p M : CCZ),
      divls_mul_params (int64Signed y) = some (p, M) →
      nth_error le 0 = some (.Vlong x) →
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (divls_mull (hf := hf) p M)
        (.Vlong (int64Divs x y))

def eval_divlsStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (hf : helper_functions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
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
        xi (Genv.globalenv prog) sp e m le (divls (hf := hf) cfg a b) v ∧
        Val.lessdef z v

def eval_modlsStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (hf : helper_functions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
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
        xi (Genv.globalenv prog) sp e m le (modls (hf := hf) cfg a b) v ∧
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

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Zdiv_unique_2 : Zdiv_unique_2Statement := by
  intro x y q hy h
  have hdiv : zDiv x y = zOfInt
      (if intOfZ y = 0 then 0 else if 0 < intOfZ y then Int.ediv (intOfZ x) (intOfZ y) else
        let d := -intOfZ y
        let q' := Int.ediv (intOfZ x) d
        let r := Int.emod (intOfZ x) d
        if r = 0 then -q' else -(q' + 1)) := by
    cases x <;> cases y <;> rfl
  rw [hdiv]
  apply intOfZ_injective
  simp only [intOfZ_zOfInt]
  have hyInt : 0 < intOfZ y := hy
  have hy0 : intOfZ y ≠ 0 := Int.ne_of_gt hyInt
  simp only [hy0, if_false, if_pos hyInt]
  have hsub : intOfZ (zSub (zMul y q) x) = intOfZ y * intOfZ q - intOfZ x := by
    change intOfZ (zOfInt (intOfZ (zOfInt (intOfZ y * intOfZ q)) - intOfZ x)) = _
    simp only [intOfZ_zOfInt]
  have hqsub : intOfZ (zSub q z1) = intOfZ q - 1 := by
    change intOfZ (zOfInt (intOfZ q - intOfZ z1)) = _
    rw [intOfZ_zOfInt]
    rfl
  have hR : 0 < intOfZ y * intOfZ q - intOfZ x ∧
      intOfZ y * intOfZ q - intOfZ x ≤ intOfZ y := by
    have h1 : intOfZ z0 < intOfZ (zSub (zMul y q) x) := h.1
    have h2 : intOfZ (zSub (zMul y q) x) ≤ intOfZ y := h.2
    rw [show intOfZ z0 = 0 by rfl, hsub] at h1
    rw [hsub] at h2
    exact ⟨h1, h2⟩
  rw [hqsub]
  let r : Int := intOfZ y * intOfZ q - intOfZ x
  have hrpos : 0 < r := hR.1
  have hrle : r ≤ intOfZ y := hR.2
  have hrnonneg : 0 ≤ intOfZ y - r := by omega
  have hrlt : intOfZ y - r < intOfZ y := by omega
  have hrepr : intOfZ x = (intOfZ q - 1) * intOfZ y + (intOfZ y - r) := by
    calc
      intOfZ x = intOfZ y * intOfZ q - r := by dsimp [r]; omega
      _ = intOfZ y * (intOfZ q - 1) + (intOfZ y - r) := by
        rw [Int.mul_sub, Int.mul_one]
        omega
      _ = (intOfZ q - 1) * intOfZ y + (intOfZ y - r) := by
        rw [Int.mul_comm]
  have hu := (Int.ediv_emod_unique (a := intOfZ x) (b := intOfZ y)
    (q := intOfZ q - 1) (r := intOfZ y - r) hyInt).mpr ?_
  · exact hu.1
  exact ⟨by
    rw [Int.add_comm]
    rw [Int.mul_comm (intOfZ y) (intOfZ q - 1)]
    exact hrepr.symm, hrnonneg, hrlt⟩

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem zdiv_pos_int (a b : CCZ) (hb : 0 < intOfZ b) :
    zDiv a b = zOfInt (Int.ediv (intOfZ a) (intOfZ b)) := by
  change zOfInt (if intOfZ b = 0 then 0 else if 0 < intOfZ b then
    Int.ediv (intOfZ a) (intOfZ b) else
      let d := -intOfZ b
      let q := Int.ediv (intOfZ a) d
      let r := Int.emod (intOfZ a) d
      if r = 0 then -q else -(q + 1)) = _
  simp [Int.ne_of_gt hb, hb]

theorem Zdiv_mul_opp : Zdiv_mul_oppStatement := by
  intro N hN d hd m l hl hbounds n hn
  have hN' : 0 ≤ intOfZ N := hN
  have hl' : 0 ≤ intOfZ l := hl
  have hd' : 0 < intOfZ d := hd
  have hE : 0 ≤ intOfZ (zAdd N l) := by
    change 0 ≤ intOfZ (zOfInt (intOfZ N + intOfZ l))
    rw [intOfZ_zOfInt]
    omega
  have hT : 0 < intOfZ (two_p (zAdd N l)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hE)]
    simp only [intOfZ_zOfInt]
    exact Int.pow_pos (by decide)
  have hLO : intOfZ (two_p (zAdd N l)) < intOfZ m * intOfZ d := by
    have h := hbounds.1
    change intOfZ (two_p (zAdd N l)) <
      intOfZ (zOfInt (intOfZ m * intOfZ d)) at h
    simpa only [intOfZ_zOfInt] using h
  have hHI : intOfZ m * intOfZ d ≤
      intOfZ (two_p (zAdd N l)) + intOfZ (two_p l) := by
    have h := hbounds.2
    change intOfZ (zOfInt (intOfZ m * intOfZ d)) ≤
      intOfZ (zOfInt (intOfZ (two_p (zAdd N l)) + intOfZ (two_p l))) at h
    simpa only [intOfZ_zOfInt] using h
  have hM : 0 ≤ intOfZ m := by
    by_cases hm : 0 ≤ intOfZ m
    · exact hm
    · have hm' : intOfZ m < 0 := Int.lt_of_not_ge hm
      have hprod : intOfZ m * intOfZ d ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg (Int.le_of_lt hm') (Int.le_of_lt hd')
      omega
  have hX : 0 < intOfZ n := hn.1
  have hXN : intOfZ n ≤ intOfZ (two_p N) := hn.2
  have hdivn := zdiv_pos_int n d hd'
  have hdivneg := zdiv_pos_int (zMul m (zOpp n)) (two_p (zAdd N l)) hT
  rw [hdivn, hdivneg]
  apply intOfZ_injective
  simp only [intOfZ_zOfInt]
  simp only [zSub, zOpp, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.opp, intOfZ_zOfInt]
  change Int.ediv (intOfZ n) (intOfZ d) =
    -(Int.ediv (intOfZ (zMul m (zOpp n))) (intOfZ (two_p (zAdd N l)))) - 1
  have hnum : intOfZ (zMul m (zOpp n)) = -(intOfZ m * intOfZ n) := by
    simp only [zMul, zOpp, ZArith.BinInt.Z.mul, ZArith.BinInt.Z.opp,
      intOfZ_zOfInt]
    exact Int.mul_neg _ _
  rw [hnum]
  let q : Int := Int.ediv (intOfZ n) (intOfZ d)
  let r : Int := Int.emod (intOfZ n) (intOfZ d)
  have hrnonneg : 0 ≤ r := by
    dsimp [r]
    exact Int.emod_nonneg _ (Int.ne_of_gt hd')
  have hrlt : r < intOfZ d := by
    dsimp [r]
    exact Int.emod_lt_of_pos _ hd'
  have hdecomp : intOfZ n = q * intOfZ d + r := by
    dsimp [q, r]
    exact (Int.ediv_mul_add_emod (intOfZ n) (intOfZ d)).symm
  have hkpos : 0 < intOfZ m * intOfZ d - intOfZ (two_p (zAdd N l)) := by
    omega
  have hkle : intOfZ m * intOfZ d - intOfZ (two_p (zAdd N l)) ≤ intOfZ (two_p l) := by
    omega
  have hEq :
      (intOfZ m * intOfZ n - intOfZ (two_p (zAdd N l)) * q) * intOfZ d =
        (intOfZ m * intOfZ d - intOfZ (two_p (zAdd N l))) * intOfZ n +
    intOfZ (two_p (zAdd N l)) * r := by
    rw [hdecomp]
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
      Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
      Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.sub_eq_add_neg,
      Int.mul_neg, Int.neg_mul]
    omega
  have htwoN : intOfZ (two_p N) = Int.pow 2 (Int.toNat (intOfZ N)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hN')]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  have htwoL : intOfZ (two_p l) = Int.pow 2 (Int.toNat (intOfZ l)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hl')]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  have htwoE : intOfZ (two_p (zAdd N l)) =
      Int.pow 2 (Int.toNat (intOfZ (zAdd N l))) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hE)]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  have hEl : intOfZ (zAdd N l) = intOfZ N + intOfZ l := by
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  have hpow : intOfZ (two_p (zAdd N l)) =
      intOfZ (two_p l) * intOfZ (two_p N) := by
    rw [htwoE, hEl, htwoL, htwoN, Int.toNat_add hN' hl']
    calc
      Int.pow 2 ((intOfZ N).toNat + (intOfZ l).toNat) =
          Int.pow 2 (intOfZ N).toNat * Int.pow 2 (intOfZ l).toNat :=
        Int.pow_add 2 _ _
      _ = Int.pow 2 (intOfZ l).toNat * Int.pow 2 (intOfZ N).toNat := by
        rw [Int.mul_comm]
  have hPpos : 0 < intOfZ (two_p l) := by
    rw [htwoL]
    exact Int.pow_pos (by decide)
  have hPNnonneg : 0 ≤ intOfZ (two_p N) := by
    rw [htwoN]
    exact Int.pow_nonneg (by decide)
  have hkn_le :
      (intOfZ m * intOfZ d - intOfZ (two_p (zAdd N l))) * intOfZ n ≤
        intOfZ (two_p (zAdd N l)) := by
    have h1 := Int.mul_le_mul_of_nonneg_right hkle (Int.le_of_lt hX)
    have h2 := Int.mul_le_mul_of_nonneg_left hXN (Int.le_of_lt hPpos)
    calc
      (intOfZ m * intOfZ d - intOfZ (two_p (zAdd N l))) * intOfZ n ≤
          intOfZ (two_p l) * intOfZ n := h1
      _ ≤ intOfZ (two_p l) * intOfZ (two_p N) := h2
      _ = intOfZ (two_p (zAdd N l)) := hpow.symm
  have hrle : r ≤ intOfZ d - 1 := by omega
  have htr_le : intOfZ (two_p (zAdd N l)) * r ≤
      intOfZ (two_p (zAdd N l)) * intOfZ d - intOfZ (two_p (zAdd N l)) := by
    have h := Int.mul_le_mul_of_nonneg_left hrle (Int.le_of_lt hT)
    rw [Int.mul_sub, Int.mul_one] at h
    exact h
  have hsum_le :
      (intOfZ m * intOfZ d - intOfZ (two_p (zAdd N l))) * intOfZ n +
          intOfZ (two_p (zAdd N l)) * r ≤
        intOfZ (two_p (zAdd N l)) * intOfZ d := by
    omega
  have hApos : 0 < intOfZ m * intOfZ n -
      intOfZ (two_p (zAdd N l)) * q := by
    have hprod : 0 <
        (intOfZ m * intOfZ n - intOfZ (two_p (zAdd N l)) * q) * intOfZ d := by
      rw [hEq]
      have hkx : 0 <
          (intOfZ m * intOfZ d - intOfZ (two_p (zAdd N l))) * intOfZ n :=
        Int.mul_pos hkpos hX
      have htr : 0 ≤ intOfZ (two_p (zAdd N l)) * r :=
        Int.mul_nonneg (Int.le_of_lt hT) hrnonneg
      omega
    have hnonpos : ¬ (intOfZ m * intOfZ n -
        intOfZ (two_p (zAdd N l)) * q ≤ 0) := by
      intro hbad
      have hbad' := Int.mul_nonpos_of_nonpos_of_nonneg hbad (Int.le_of_lt hd')
      omega
    exact Int.lt_of_not_ge hnonpos
  have hAle : intOfZ m * intOfZ n -
      intOfZ (two_p (zAdd N l)) * q ≤ intOfZ (two_p (zAdd N l)) := by
    have hmul :
        (intOfZ m * intOfZ n - intOfZ (two_p (zAdd N l)) * q) * intOfZ d ≤
          intOfZ (two_p (zAdd N l)) * intOfZ d := by
      rw [hEq]
      exact hsum_le
    exact Int.le_of_mul_le_mul_right hmul hd'
  have hnegdecomp :
      -(intOfZ m * intOfZ n) =
        (-q - 1) * intOfZ (two_p (zAdd N l)) +
          (intOfZ (two_p (zAdd N l)) -
            (intOfZ m * intOfZ n - intOfZ (two_p (zAdd N l)) * q)) := by
    simp only [Int.mul_sub, Int.mul_add, Int.add_mul, Int.sub_mul,
      Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
      Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.sub_eq_add_neg,
      Int.mul_neg, Int.neg_mul]
    omega
  have hnegquot := (Int.ediv_emod_unique
      (a := -(intOfZ m * intOfZ n))
      (b := intOfZ (two_p (zAdd N l)))
      (q := -q - 1)
      (r := intOfZ (two_p (zAdd N l)) -
        (intOfZ m * intOfZ n - intOfZ (two_p (zAdd N l)) * q)) hT).mpr ?_
  · change q = -((-(intOfZ m * intOfZ n)).ediv
      (intOfZ (two_p (zAdd N l)))) - 1
    have hqneg : Int.ediv (-(intOfZ m * intOfZ n))
        (intOfZ (two_p (zAdd N l))) = -q - 1 := hnegquot.1
    rw [hqneg]
    omega
  · refine ⟨?_, ?_, ?_⟩
    · rw [Int.add_comm, Int.mul_comm]
      exact hnegdecomp.symm
    · omega
    · omega

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem zdiv_pos_int_local (a b : CCZ) (hb : 0 < intOfZ b) :
    zDiv a b = zOfInt (Int.ediv (intOfZ a) (intOfZ b)) := by
  change zOfInt (if intOfZ b = 0 then 0 else if 0 < intOfZ b then
    Int.ediv (intOfZ a) (intOfZ b) else
      let d := -intOfZ b
      let q := Int.ediv (intOfZ a) d
      let r := Int.emod (intOfZ a) d
      if r = 0 then -q else -(q + 1)) = _
  simp [Int.ne_of_gt hb, hb]

private theorem zdiv_mul_pos_local :
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
          zDiv n d = zDiv (zMul m n) (two_p (zAdd N l)) := by
  intro N hN d hd m l hl hbounds n hn
  have hN' : 0 ≤ intOfZ N := hN
  have hl' : 0 ≤ intOfZ l := hl
  have hd' : 0 < intOfZ d := hd
  have hE : 0 ≤ intOfZ (zAdd N l) := by
    change 0 ≤ intOfZ (zOfInt (intOfZ N + intOfZ l))
    rw [intOfZ_zOfInt]
    omega
  have hT : 0 < intOfZ (two_p (zAdd N l)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hE)]
    simp only [intOfZ_zOfInt]
    exact Int.pow_pos (by decide)
  have hLO : intOfZ (two_p (zAdd N l)) ≤ intOfZ m * intOfZ d := by
    have h := hbounds.1
    change intOfZ (two_p (zAdd N l)) ≤ intOfZ (zMul m d) at h
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt] at h
    exact h
  have hHI : intOfZ m * intOfZ d ≤
      intOfZ (two_p (zAdd N l)) + intOfZ (two_p l) := by
    have h := hbounds.2
    change intOfZ (zMul m d) ≤ intOfZ (zAdd (two_p (zAdd N l)) (two_p l)) at h
    simp only [zMul, ZArith.BinInt.Z.mul, zAdd, ZArith.BinInt.Z.add,
      intOfZ_zOfInt] at h
    exact h
  have hM : 0 ≤ intOfZ m := by
    by_cases hm : 0 ≤ intOfZ m
    · exact hm
    · have hm' : intOfZ m < 0 := Int.lt_of_not_ge hm
      have hprod : intOfZ m * intOfZ d ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg (Int.le_of_lt hm') (Int.le_of_lt hd')
      omega
  have hX : 0 ≤ intOfZ n := hn.1
  have hXN : intOfZ n < intOfZ (two_p N) := hn.2
  have hdivn := zdiv_pos_int_local n d hd'
  have hdivmn := zdiv_pos_int_local (zMul m n) (two_p (zAdd N l)) hT
  rw [hdivn, hdivmn]
  apply intOfZ_injective
  simp only [intOfZ_zOfInt]
  let q : Int := Int.ediv (intOfZ n) (intOfZ d)
  let r : Int := Int.emod (intOfZ n) (intOfZ d)
  have hrnonneg : 0 ≤ r := by
    dsimp [r]
    exact Int.emod_nonneg _ (Int.ne_of_gt hd')
  have hrlt : r < intOfZ d := by
    dsimp [r]
    exact Int.emod_lt_of_pos _ hd'
  have hdecomp : intOfZ n = q * intOfZ d + r := by
    dsimp [q, r]
    exact (Int.ediv_mul_add_emod (intOfZ n) (intOfZ d)).symm
  let k : Int := intOfZ m * intOfZ d - intOfZ (two_p (zAdd N l))
  have hkpos : 0 ≤ k := by
    dsimp [k]
    omega
  have hkle : k ≤ intOfZ (two_p l) := by
    dsimp [k]
    omega
  have hEq :
      (intOfZ m * intOfZ n - intOfZ (two_p (zAdd N l)) * q) * intOfZ d =
        k * intOfZ n + intOfZ (two_p (zAdd N l)) * r := by
    rw [hdecomp]
    dsimp [k]
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
      Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
      Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.sub_eq_add_neg,
      Int.mul_neg, Int.neg_mul]
    omega
  have htwoN : intOfZ (two_p N) = Int.pow 2 (Int.toNat (intOfZ N)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hN')]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  have htwoL : intOfZ (two_p l) = Int.pow 2 (Int.toNat (intOfZ l)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hl')]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  have htwoE : intOfZ (two_p (zAdd N l)) =
      Int.pow 2 (Int.toNat (intOfZ (zAdd N l))) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hE)]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  have hEl : intOfZ (zAdd N l) = intOfZ N + intOfZ l := by
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  have hpow : intOfZ (two_p (zAdd N l)) =
      intOfZ (two_p l) * intOfZ (two_p N) := by
    rw [htwoE, hEl, htwoL, htwoN, Int.toNat_add hN' hl']
    calc
      Int.pow 2 ((intOfZ N).toNat + (intOfZ l).toNat) =
          Int.pow 2 (intOfZ N).toNat * Int.pow 2 (intOfZ l).toNat :=
        Int.pow_add 2 _ _
      _ = Int.pow 2 (intOfZ l).toNat * Int.pow 2 (intOfZ N).toNat := by
        rw [Int.mul_comm]
  have hPpos : 0 < intOfZ (two_p l) := by
    rw [htwoL]
    exact Int.pow_pos (by decide)
  have hkn_le : k * intOfZ n ≤ intOfZ (two_p (zAdd N l)) - intOfZ (two_p l) := by
    have h1 := Int.mul_le_mul_of_nonneg_right hkle hX
    have hn_le : intOfZ n ≤ intOfZ (two_p N) - 1 := by omega
    have h2 := Int.mul_le_mul_of_nonneg_left hn_le (Int.le_of_lt hPpos)
    calc
      k * intOfZ n ≤ intOfZ (two_p l) * intOfZ n := h1
      _ ≤ intOfZ (two_p l) * (intOfZ (two_p N) - 1) := by omega
      _ = intOfZ (two_p (zAdd N l)) - intOfZ (two_p l) := by
        rw [Int.mul_sub, Int.mul_one, hpow]
  have htr_le : intOfZ (two_p (zAdd N l)) * r ≤
      intOfZ (two_p (zAdd N l)) * intOfZ d - intOfZ (two_p (zAdd N l)) := by
    have h := Int.mul_le_mul_of_nonneg_left (show r ≤ intOfZ d - 1 by omega)
      (Int.le_of_lt hT)
    rw [Int.mul_sub, Int.mul_one] at h
    exact h
  have hApos : 0 ≤ intOfZ m * intOfZ n -
      intOfZ (two_p (zAdd N l)) * q := by
    have hprod : 0 ≤
        (intOfZ m * intOfZ n - intOfZ (two_p (zAdd N l)) * q) * intOfZ d := by
      rw [hEq]
      have hkx : 0 ≤ k * intOfZ n := Int.mul_nonneg hkpos hX
      have htr : 0 ≤ intOfZ (two_p (zAdd N l)) * r :=
        Int.mul_nonneg (Int.le_of_lt hT) hrnonneg
      omega
    exact Int.le_of_not_gt (fun hbad => by
      have := Int.mul_neg_of_neg_of_pos hbad hd'
      omega)
  have hAle : intOfZ m * intOfZ n -
      intOfZ (two_p (zAdd N l)) * q < intOfZ (two_p (zAdd N l)) := by
    have hmul :
        (intOfZ m * intOfZ n - intOfZ (two_p (zAdd N l)) * q) * intOfZ d <
          intOfZ (two_p (zAdd N l)) * intOfZ d := by
      rw [hEq]
      omega
    exact (Int.mul_lt_mul_right hd').mp hmul
  have hrepr : intOfZ (zMul m n) = q * intOfZ (two_p (zAdd N l)) +
      (intOfZ m * intOfZ n - intOfZ (two_p (zAdd N l)) * q) := by
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    rw [Int.mul_comm (intOfZ (two_p (zAdd N l))) q]
    omega
  have hu := (Int.ediv_emod_unique
      (a := intOfZ (zMul m n))
      (b := intOfZ (two_p (zAdd N l)))
      (q := q)
      (r := intOfZ m * intOfZ n - intOfZ (two_p (zAdd N l)) * q) hT).mpr ?_
  · dsimp [q] at hu ⊢
    exact hu.1.symm
  exact ⟨by
    simpa [Int.mul_comm, Int.add_comm, Int.add_left_comm] using hrepr.symm,
    hApos, hAle⟩

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Zquot_mul : Zquot_mulStatement := by
  intro N hN d hd m l hl hbounds n hn
  have hN' : 0 ≤ intOfZ N := hN
  have hl' : 0 ≤ intOfZ l := hl
  have hd' : 0 < intOfZ d := hd
  have hE : 0 ≤ intOfZ (zAdd N l) := by
    change 0 ≤ intOfZ (zOfInt (intOfZ N + intOfZ l))
    rw [intOfZ_zOfInt]
    omega
  have hT : 0 < intOfZ (two_p (zAdd N l)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hE)]
    simp only [intOfZ_zOfInt]
    exact Int.pow_pos (by decide)
  by_cases hnneg : intOfZ n < 0
  · have hnopp : intOfZ (zOpp n) = -intOfZ n := by
      simp only [zOpp, ZArith.BinInt.Z.opp, intOfZ_zOfInt]
    have hnpos : 0 < intOfZ (zOpp n) := by
      rw [hnopp]
      omega
    have hlow : -intOfZ (two_p N) ≤ intOfZ n := by
      have h := hn.1
      change intOfZ (zOpp (two_p N)) ≤ intOfZ n at h
      simp only [zOpp, ZArith.BinInt.Z.opp, intOfZ_zOfInt] at h
      exact h
    have hnupper : intOfZ (zOpp n) ≤ intOfZ (two_p N) := by
      rw [hnopp]
      omega
    have hopp := Zdiv_mul_opp N hN d hd m l hl hbounds (zOpp n)
      ⟨hnpos, hnupper⟩
    have hnum : intOfZ (zMul m (zOpp (zOpp n))) = intOfZ (zMul m n) := by
      simp only [zMul, zOpp, ZArith.BinInt.Z.mul, ZArith.BinInt.Z.opp,
        intOfZ_zOfInt]
      simp only [Int.neg_neg]
    rw [zdiv_pos_int_local (zOpp n) d hd',
      zdiv_pos_int_local (zMul m (zOpp (zOpp n)))
        (two_p (zAdd N l)) hT] at hopp
    have hopp := congrArg intOfZ hopp
    simp only [intOfZ_zOfInt, zSub, ZArith.BinInt.Z.sub,
      zOpp, ZArith.BinInt.Z.opp, Int.neg_neg, zOfInt_intOfZ] at hopp
    have hquot : Int.tdiv (intOfZ n) (intOfZ d) =
        -(Int.ediv (intOfZ (zOpp n)) (intOfZ d)) := by
      rw [show intOfZ n = -intOfZ (zOpp n) by omega, Int.neg_tdiv,
        Int.tdiv_eq_ediv_of_nonneg (Int.le_of_lt hnpos)]
      rfl
    have hbool : zltBool n z0 = true := by
      unfold zltBool boolOfSumbool
      cases hz : CompCert4Lean.Lib.Coqlib.zlt n z0 with
      | left hp => rfl
      | right hp =>
          exfalso
          change 0 ≤ intOfZ n at hp
          omega
    simp [hbool]
    apply intOfZ_injective
    simp only [zQuot, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
    rw [hquot]
    have hopp2 := hopp
    rw [← hnopp] at hopp2
    rw [zdiv_pos_int_local (zMul m n) (two_p (zAdd N l)) hT]
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hopp2
    have hz1 : intOfZ z1 = 1 := by rfl
    rw [hz1] at hopp2
    omega
  · have hnnonneg : 0 ≤ intOfZ n := by omega
    have hpos := zdiv_mul_pos_local N hN d hd m l hl
      ⟨Int.le_of_lt hbounds.1, hbounds.2⟩ n
      ⟨hnnonneg, hn.2⟩
    have hquotn : zQuot n d = zDiv n d := by
      change zOfInt (Int.tdiv (intOfZ n) (intOfZ d)) = zDiv n d
      rw [Int.tdiv_eq_ediv_of_nonneg hnnonneg,
        zdiv_pos_int_local n d hd']
      rfl
    have hbool : zltBool n z0 = false := by
      unfold zltBool boolOfSumbool
      cases hz : CompCert4Lean.Lib.Coqlib.zlt n z0 with
      | left hp =>
          exfalso
          change intOfZ n < 0 at hp
          omega
      | right hp => rfl
    rw [hquotn, hpos]
    simp [hbool, zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    rw [show intOfZ z0 = 0 by rfl, Int.add_zero, zOfInt_intOfZ]

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.SelectDiv

theorem divu_mul_params_sound : divu_mul_params_soundStatement := by
  unfold divu_mul_params_soundStatement divu_mul_params
  intro d m' p'
  have zlt_true_local : ∀ a b : CCZ,
      boolOfSumbool (CompCert4Lean.Lib.Coqlib.zlt a b) = true → zLt a b := by
    intro a b h
    cases hz : CompCert4Lean.Lib.Coqlib.zlt a b with
    | left hp => exact hp
    | right hn => simp [boolOfSumbool, hz] at h
  have zle_true_local : ∀ a b : CCZ,
      boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle a b) = true → zLe a b := by
    intro a b h
    cases hz : CompCert4Lean.Lib.Coqlib.zle a b with
    | left hp => exact hp
    | right hn => simp [boolOfSumbool, hz] at h
  generalize hfind : find_div_mul_params _ _ d _ = r
  cases r with
  | none => simp_all
  | some q =>
    cases q with
    | mk p m =>
      dsimp
      split
      case isFalse => simp_all
      case isTrue hcond =>
        simp only [Bool.and_eq_true] at hcond
        rcases hcond with ⟨hcond, hP32⟩
        rcases hcond with ⟨hcond, hP0⟩
        rcases hcond with ⟨hcond, hML⟩
        rcases hcond with ⟨hcond, hM⟩
        rcases hcond with ⟨hcond, hHI⟩
        rcases hcond with ⟨hD, hLO⟩
        intro hp
        cases hp
        have hD' := zlt_true_local _ _ hD
        have hLO' := zle_true_local _ _ hLO
        have hHI' := zle_true_local _ _ hHI
        have hM' := zle_true_local _ _ hM
        have hML' := zlt_true_local _ _ hML
        have hP0' := zle_true_local _ _ hP0
        have hP32' := zlt_true_local _ _ hP32
        refine ⟨⟨hM', hML'⟩, ⟨hP0', hP32'⟩, ?_⟩
        intro n hn
        apply zdiv_mul_pos_local z32 (by
          change (0 : Int) ≤ 32
          omega) d hD' _ _ hP0'
          ⟨hLO', hHI'⟩ n hn

theorem divs_mul_params_sound : divs_mul_params_soundStatement := by
  unfold divs_mul_params_soundStatement divs_mul_params
  intro d m' p'
  have zlt_true_local : ∀ a b : CCZ,
      boolOfSumbool (CompCert4Lean.Lib.Coqlib.zlt a b) = true → zLt a b := by
    intro a b h
    cases hz : CompCert4Lean.Lib.Coqlib.zlt a b with
    | left hp => exact hp
    | right hn => simp [boolOfSumbool, hz] at h
  have zle_true_local : ∀ a b : CCZ,
      boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle a b) = true → zLe a b := by
    intro a b h
    cases hz : CompCert4Lean.Lib.Coqlib.zle a b with
    | left hp => exact hp
    | right hn => simp [boolOfSumbool, hz] at h
  generalize hfind : find_div_mul_params _ _ d _ = r
  cases r with
  | none => simp_all
  | some q =>
    cases q with
    | mk p m =>
      dsimp
      split
      case isFalse => simp_all
      case isTrue hcond =>
        simp only [Bool.and_eq_true] at hcond
        rcases hcond with ⟨hcond, hP32⟩
        rcases hcond with ⟨hcond, hP0⟩
        rcases hcond with ⟨hcond, hML⟩
        rcases hcond with ⟨hcond, hM⟩
        rcases hcond with ⟨hcond, hHI⟩
        rcases hcond with ⟨hD, hLO⟩
        intro hp
        cases hp
        have hD' := zlt_true_local _ _ hD
        have hLO' := zlt_true_local _ _ hLO
        have hHI' := zle_true_local _ _ hHI
        have hM' := zle_true_local _ _ hM
        have hML' := zlt_true_local _ _ hML
        have hP0' := zle_true_local _ _ hP0
        have hP32' := zlt_true_local _ _ hP32
        refine ⟨⟨hM', hML'⟩, ⟨hP0', hP32'⟩, ?_⟩
        intro n hn
        have hN : zLe z0 (zSub z32 z1) := by
          change (0 : Int) ≤ 31
          omega
        have hL : zLe z0 (zAdd (zSub p z32) z1) := by
          change 0 ≤ intOfZ (zAdd (zSub p z32) z1)
          simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
            intOfZ_zOfInt]
          change 0 ≤ intOfZ (zSub p z32) at hP0'
          simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hP0'
          have hz1 : intOfZ z1 = 1 := by rfl
          rw [hz1]
          omega
        have harg :
            zAdd (zSub z32 z1) (zAdd (zSub p z32) z1) =
              zAdd z32 (zSub p z32) := by
          apply intOfZ_injective
          simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
            intOfZ_zOfInt]
          omega
        have hLO2 : zLt
            (two_p (zAdd (zSub z32 z1)
              (zAdd (zSub p z32) z1))) (zMul m' d) := by
          simpa [harg] using hLO'
        have hHI2 : zLe (zMul m' d)
            (zAdd (two_p (zAdd (zSub z32 z1)
              (zAdd (zSub p z32) z1)))
              (two_p (zAdd (zSub p z32) z1))) := by
          rw [harg]
          exact hHI'
        have hnupper : zLt n (two_p (zSub z32 z1)) := by
          change intOfZ n < intOfZ (two_p (zSub z32 z1))
          have hz : intOfZ (zSub z32 z1) = 31 := by
            simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
            rfl
          have heq : intOfZ (two_p (zSub z32 z1)) =
              intOfZ (CompCert4Lean.Lib.Integers.Int.half_modulus) := by
            rfl
          have hmax := hn.2
          change intOfZ n ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.max_signed) at hmax
          unfold CompCert4Lean.Lib.Integers.Int.max_signed
            CompCert4Lean.Lib.Integers.Int.half_modulus at hmax
          simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hmax
          change intOfZ n ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.half_modulus) - 1 at hmax
          rw [heq]
          omega
        have hz := Zquot_mul (zSub z32 z1) hN d hD' _
          (zAdd (zSub p z32) z1) hL ⟨hLO2, hHI2⟩ n ⟨hn.1, hnupper⟩
        simpa [harg] using hz

end CompCert4Lean.Backend.SelectDivproof
