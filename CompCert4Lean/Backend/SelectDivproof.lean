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

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem zdiv_zdiv_pos_local (a b c : CCZ)
    (hb : 0 < intOfZ b) (hc : 0 < intOfZ c) :
    zDiv (zDiv a b) c = zDiv a (zMul b c) := by
  have hbc : 0 < intOfZ (zMul b c) := by
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    exact Int.mul_pos (by exact hb) (by exact hc)
  rw [zdiv_pos_int_local a b hb]
  rw [zdiv_pos_int_local (zOfInt (Int.ediv (intOfZ a) (intOfZ b))) c hc]
  rw [zdiv_pos_int_local a (zMul b c) hbc]
  simp only [intOfZ_zOfInt]
  have hmul : intOfZ (zMul b c) = intOfZ b * intOfZ c := by
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  rw [hmul]
  exact congrArg zOfInt
    (Int.ediv_ediv_of_nonneg (x := intOfZ a) (y := intOfZ b)
      (z := intOfZ c) (Int.le_of_lt hb))

private theorem two_p_add_local (a b : CCZ)
    (ha : 0 ≤ intOfZ a) (hb : 0 ≤ intOfZ b) :
    two_p (zAdd a b) = zMul (two_p a) (two_p b) := by
  have hA : intOfZ (two_p a) = Int.pow 2 (Int.toNat (intOfZ a)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge ha)]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  have hB : intOfZ (two_p b) = Int.pow 2 (Int.toNat (intOfZ b)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hb)]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  have hAB : intOfZ (zAdd a b) = intOfZ a + intOfZ b := by
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  have hC : intOfZ (two_p (zAdd a b)) =
      Int.pow 2 (Int.toNat (intOfZ a + intOfZ b)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (by rw [hAB]; omega)]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
    rw [hAB]
  apply intOfZ_injective
  rw [hC]
  rw [Int.toNat_add ha hb]
  calc
    Int.pow 2 ((intOfZ a).toNat + (intOfZ b).toNat) =
        Int.pow 2 (intOfZ a).toNat * Int.pow 2 (intOfZ b).toNat :=
      Int.pow_add 2 _ _
    _ = intOfZ (zMul (two_p a) (two_p b)) := by
      simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
      rw [hA, hB]

theorem divu_mul_shift : divu_mul_shiftStatement := by
  intro x y m p hparams
  have hs := divu_mul_params_sound (intUnsigned y) m p hparams
  rcases hs with ⟨hm, hp, hdiv⟩
  refine ⟨hp, ?_⟩
  change CompCert4Lean.Lib.Integers.Int.divu x y =
    CompCert4Lean.Lib.Integers.Int.shru
      (CompCert4Lean.Lib.Integers.Int.mulhu x
        (CompCert4Lean.Lib.Integers.Int.repr m))
      (CompCert4Lean.Lib.Integers.Int.repr p)
  rw [CompCert4Lean.Lib.Integers.Int.shru_div_two_p_proof]
  unfold CompCert4Lean.Lib.Integers.Int.divu CompCert4Lean.Lib.Integers.WordCore.divu
    CompCert4Lean.Lib.Integers.Int.mulhu
  change CompCert4Lean.Lib.Integers.Int.repr
      (zDiv (intUnsigned x) (intUnsigned y)) =
    CompCert4Lean.Lib.Integers.Int.repr
      (zDiv
        (intUnsigned
          (intRepr
            (zDiv (zMul (intUnsigned x) (intUnsigned (intRepr m)))
              CompCert4Lean.Lib.Integers.Int.modulus)))
        (two_p (intUnsigned (intRepr p))))
  have hm0 : zLe z0 m := hm.1
  have hm_lt : zLt m CompCert4Lean.Lib.Integers.Int.modulus := hm.2
  have hmmax : zLe m CompCert4Lean.Lib.Integers.Int.max_unsigned := by
    change intOfZ m ≤ intOfZ CompCert4Lean.Lib.Integers.Int.max_unsigned
    change intOfZ m ≤ intOfZ CompCert4Lean.Lib.Integers.Int.modulus - 1
    change intOfZ m < intOfZ CompCert4Lean.Lib.Integers.Int.modulus at hm_lt
    omega
  have hmrepr : intUnsigned (intRepr m) = m := by
    exact CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api m ⟨hm0, hmmax⟩
  have hp0 : zLe z0 p := hp.1
  have hp_lt : zLt p z32 := hp.2
  have hpmax : zLe p CompCert4Lean.Lib.Integers.Int.max_unsigned := by
    change intOfZ p ≤ intOfZ CompCert4Lean.Lib.Integers.Int.max_unsigned
    change intOfZ p ≤ intOfZ CompCert4Lean.Lib.Integers.Int.modulus - 1
    change intOfZ p < intOfZ z32 at hp_lt
    have hz32 : intOfZ z32 = (32 : Int) := by rfl
    have hmodpow : intOfZ CompCert4Lean.Lib.Integers.Int.modulus =
        (2 ^ 32 : Int) := by rfl
    rw [hz32] at hp_lt
    rw [hmodpow]
    have hconst : (32 : Int) ≤ (2 ^ 32 : Int) - 1 := by decide
    omega
  have hprepr : intUnsigned (intRepr p) = p := by
    exact CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api p ⟨hp0, hpmax⟩
  rw [hmrepr, hprepr]
  have hx0 : zLe z0 (intUnsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ (intUnsigned x) at h
    change 0 ≤ intOfZ (intUnsigned x)
    omega
  have hxlt : zLt (intUnsigned x) CompCert4Lean.Lib.Integers.Int.modulus :=
    x.intrange.2
  have hmodpow : intOfZ CompCert4Lean.Lib.Integers.Int.modulus =
      (2 ^ 32 : Int) := by rfl
  have hmodpos : 0 < intOfZ CompCert4Lean.Lib.Integers.Int.modulus := by
    rw [hmodpow]
    exact Int.pow_pos (by decide)
  have hnum0 : 0 ≤ intOfZ (zMul (intUnsigned x) m) := by
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    exact Int.mul_nonneg hx0 hm0
  have hnum_lt : intOfZ (zMul (intUnsigned x) m) <
      intOfZ CompCert4Lean.Lib.Integers.Int.modulus *
        intOfZ CompCert4Lean.Lib.Integers.Int.modulus := by
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    have hA : intOfZ (intUnsigned x) * intOfZ m ≤
        intOfZ CompCert4Lean.Lib.Integers.Int.modulus * intOfZ m :=
      Int.mul_le_mul_of_nonneg_right (Int.le_of_lt hxlt) hm0
    have hB : intOfZ CompCert4Lean.Lib.Integers.Int.modulus * intOfZ m <
        intOfZ CompCert4Lean.Lib.Integers.Int.modulus *
          intOfZ CompCert4Lean.Lib.Integers.Int.modulus :=
      Int.mul_lt_mul_of_pos_left hm_lt hmodpos
    exact Int.lt_of_le_of_lt hA hB
  have hq0 : zLe z0
      (zDiv (zMul (intUnsigned x) m) CompCert4Lean.Lib.Integers.Int.modulus) := by
    rw [zdiv_pos_int_local (zMul (intUnsigned x) m)
      CompCert4Lean.Lib.Integers.Int.modulus hmodpos]
    change 0 ≤ intOfZ (zOfInt _)
    simp only [intOfZ_zOfInt]
    exact Int.ediv_nonneg hnum0 (Int.le_of_lt hmodpos)
  have hq_lt : zLt
      (zDiv (zMul (intUnsigned x) m) CompCert4Lean.Lib.Integers.Int.modulus)
      CompCert4Lean.Lib.Integers.Int.modulus := by
    rw [zdiv_pos_int_local (zMul (intUnsigned x) m)
      CompCert4Lean.Lib.Integers.Int.modulus hmodpos]
    change intOfZ (zOfInt _) < intOfZ CompCert4Lean.Lib.Integers.Int.modulus
    simp only [intOfZ_zOfInt]
    exact Int.ediv_lt_of_lt_mul hmodpos hnum_lt
  have hqmax : zLe
      (zDiv (zMul (intUnsigned x) m) CompCert4Lean.Lib.Integers.Int.modulus)
      CompCert4Lean.Lib.Integers.Int.max_unsigned := by
    change intOfZ
        (zDiv (zMul (intUnsigned x) m) CompCert4Lean.Lib.Integers.Int.modulus) ≤
      intOfZ CompCert4Lean.Lib.Integers.Int.max_unsigned
    change intOfZ
        (zDiv (zMul (intUnsigned x) m) CompCert4Lean.Lib.Integers.Int.modulus) ≤
      intOfZ CompCert4Lean.Lib.Integers.Int.modulus - 1
    change intOfZ
        (zDiv (zMul (intUnsigned x) m) CompCert4Lean.Lib.Integers.Int.modulus) <
      intOfZ CompCert4Lean.Lib.Integers.Int.modulus at hq_lt
    omega
  have hqrepr : intUnsigned
      (intRepr (zDiv (zMul (intUnsigned x) m)
        CompCert4Lean.Lib.Integers.Int.modulus)) =
      zDiv (zMul (intUnsigned x) m) CompCert4Lean.Lib.Integers.Int.modulus := by
    exact CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api _ ⟨hq0, hqmax⟩
  rw [hqrepr]
  have hp0i : 0 ≤ intOfZ p := hp0
  have htp : 0 < intOfZ (two_p p) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hp0i)]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
    exact Int.pow_pos (by decide)
  have hnest := zdiv_zdiv_pos_local (zMul (intUnsigned x) m)
    CompCert4Lean.Lib.Integers.Int.modulus (two_p p) hmodpos htp
  rw [hnest]
  have hmodz32 : two_p z32 = CompCert4Lean.Lib.Integers.Int.modulus := by rfl
  have hden : zMul CompCert4Lean.Lib.Integers.Int.modulus (two_p p) =
      two_p (zAdd z32 p) := by
    rw [← hmodz32]
    have hz320 : 0 ≤ intOfZ z32 := by
      change 0 ≤ (32 : Int)
      omega
    exact (two_p_add_local z32 p hz320 hp0i).symm
  rw [hden]
  have hdivx := hdiv (intUnsigned x) ⟨hx0, hxlt⟩
  have hmulcomm : zMul (intUnsigned x) m = zMul m (intUnsigned x) := by
    apply intOfZ_injective
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt, Int.mul_comm]
  rw [hdivx, hmulcomm]

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.SelectDiv

theorem divls_mul_params_sound : divls_mul_params_soundStatement := by
  unfold divls_mul_params_soundStatement divls_mul_params
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
        rcases hcond with ⟨hcond, hP64⟩
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
        have hP64' := zlt_true_local _ _ hP64
        refine ⟨⟨hM', hML'⟩, ⟨hP0', hP64'⟩, ?_⟩
        intro n hn
        have hN : zLe z0 (zSub z64 z1) := by
          change (0 : Int) ≤ 63
          omega
        have hL : zLe z0 (zAdd (zSub p z64) z1) := by
          change 0 ≤ intOfZ (zAdd (zSub p z64) z1)
          simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
            intOfZ_zOfInt]
          change 0 ≤ intOfZ (zSub p z64) at hP0'
          simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hP0'
          have hz1 : intOfZ z1 = 1 := by rfl
          rw [hz1]
          omega
        have harg :
            zAdd (zSub z64 z1) (zAdd (zSub p z64) z1) =
              zAdd z64 (zSub p z64) := by
          apply intOfZ_injective
          simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
            intOfZ_zOfInt]
          omega
        have hLO2 : zLt
            (two_p (zAdd (zSub z64 z1)
              (zAdd (zSub p z64) z1))) (zMul m' d) := by
          simpa [harg] using hLO'
        have hHI2 : zLe (zMul m' d)
            (zAdd (two_p (zAdd (zSub z64 z1)
              (zAdd (zSub p z64) z1)))
              (two_p (zAdd (zSub p z64) z1))) := by
          rw [harg]
          exact hHI'
        have hnupper : zLt n (two_p (zSub z64 z1)) := by
          change intOfZ n < intOfZ (two_p (zSub z64 z1))
          have hz : intOfZ (zSub z64 z1) = 63 := by
            simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
            rfl
          have heq : intOfZ (two_p (zSub z64 z1)) =
              intOfZ (CompCert4Lean.Lib.Integers.Int64.half_modulus) := by
            rfl
          have hmax := hn.2
          change intOfZ n ≤ intOfZ (CompCert4Lean.Lib.Integers.Int64.max_signed) at hmax
          unfold CompCert4Lean.Lib.Integers.Int64.max_signed
            CompCert4Lean.Lib.Integers.Int64.half_modulus at hmax
          simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hmax
          change intOfZ n ≤ intOfZ (CompCert4Lean.Lib.Integers.Int64.half_modulus) - 1 at hmax
          rw [heq]
          omega
        have hz := Zquot_mul (zSub z64 z1) hN d hD' _
          (zAdd (zSub p z64) z1) hL ⟨hLO2, hHI2⟩ n ⟨hn.1, hnupper⟩
        simpa [harg] using hz

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.SelectDiv

theorem divlu_mul_params_sound : divlu_mul_params_soundStatement := by
  unfold divlu_mul_params_soundStatement divlu_mul_params
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
        rcases hcond with ⟨hcond, hP64⟩
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
        have hP64' := zlt_true_local _ _ hP64
        refine ⟨⟨hM', hML'⟩, ⟨hP0', hP64'⟩, ?_⟩
        intro n hn
        apply zdiv_mul_pos_local z64 (by
          change (0 : Int) ≤ 64
          omega) d hD' _ _ hP0'
          ⟨hLO', hHI'⟩ n hn

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem zshiftr_div_two_p_local (x y : CCZ) (hy : zLe z0 y) :
    zShiftr x y = zDiv x (two_p y) := by
  change 0 ≤ intOfZ y at hy
  have hpow : intOfZ (two_p y) =
      Int.pow 2 (Int.toNat (intOfZ y)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (by omega)]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  apply intOfZ_injective
  simp [zShiftr, zDiv,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div, hy]
  rw [intOfZ_zOfInt, intOfZ_zOfInt, hpow]
  change Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y))) =
    (if Int.pow 2 (Int.toNat (intOfZ y)) = 0 then 0
      else if 0 < Int.pow 2 (Int.toNat (intOfZ y)) then
        Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y)))
      else
        let d := -(Int.pow 2 (Int.toNat (intOfZ y)))
        let q := Int.ediv (intOfZ x) d
        let r := Int.emod (intOfZ x) d
        if r = 0 then -q else -(q + 1))
  have hp : 0 < Int.pow 2 (Int.toNat (intOfZ y)) := by
    exact Int.pow_pos (by omega)
  simp [hp, Int.ne_of_gt hp]

theorem int64_shr'_div_two_p : int64_shr'_div_two_pStatement := by
  intro x y
  unfold int64Shr' CompCert4Lean.Lib.Integers.Int64.shr'
  change int64Repr (zShiftr (int64Signed x) (intUnsigned y)) = _
  rw [zshiftr_div_two_p_local (int64Signed x) (intUnsigned y)]
  exact (show zLe z0 (intUnsigned y) from by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    change 0 ≤ intOfZ y.intval
    omega)

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem int64_shru'_div_two_p : int64_shru'_div_two_pStatement := by
  intro x y
  unfold int64Shru' CompCert4Lean.Lib.Integers.Int64.shru'
  change int64Repr (zShiftr (int64Unsigned x) (intUnsigned y)) = _
  rw [zshiftr_div_two_p_local (int64Unsigned x) (intUnsigned y)]
  exact (show zLe z0 (intUnsigned y) from by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    change 0 ≤ intOfZ y.intval
    omega)

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CminorSel

theorem is_intconst_sound
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] :
    is_intconst_soundStatement := by
  intro xi prog sp e m v a n le hconst hev
  unfold CompCert4Lean.Backend.SelectDiv.is_intconst at hconst
  cases a with
  | Evar id => simp at hconst
  | Eop op al =>
      cases op with
      | Ointconst n' =>
          cases hconst
          cases hev with
          | eval_Eop le' op' al' vl v' hargs hop =>
              cases hargs with
              | nil _ =>
                  change some (.Vint n) = some v at hop
                  cases hop
                  rfl
              | cons _ _ _ _ _ _ _ =>
                  change (none : Option CompCert4Lean.Common.Values.val) = some v at hop
                  contradiction
      | _ => simp at hconst
  | Eload chunk addr al => simp at hconst
  | Econdition a b c => simp at hconst
  | Elet a b => simp at hconst
  | Eletvar n' => simp at hconst
  | Ebuiltin ef al => simp at hconst
  | Eexternal id sg al => simp at hconst

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open Lean Elab Tactic Meta
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem int64_unsigned_repr_local (z : CCZ)
    (hz : zLe z0 z ∧ zLe z CompCert4Lean.Lib.Integers.Int64.max_unsigned) :
    int64Unsigned (int64Repr z) = z := by
  have hzi : z = zOfInt (intOfZ z) := (zOfInt_intOfZ z).symm
  rw [hzi]
  change (CompCert4Lean.Lib.Integers.WordCore.repr 64 (zOfInt (intOfZ z))).intval =
    zOfInt (intOfZ z)
  let w := CompCert4Lean.Lib.Integers.WordCore.repr 64 (zOfInt (intOfZ z))
  have hi : w.val = (intOfZ z % ((2 ^ 64 : Nat) : Int)).toNat := by
    dsimp [w]
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "WordCore.val_repr")
        | throwError "frozen WordCore.val_repr helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `z
      evalTactic
        (← `(tactic| exact $stx 64
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ $arg)))
  have hwi : w.intval = ZArith.BinInt.Z.of_nat w.val := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "WordCore.intval_eq_zOfNat_val")
        | throwError "frozen WordCore.intval_eq_zOfNat_val helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `w
      evalTactic (← `(tactic| exact $stx $arg))
  change w.intval = _
  rw [hwi, hi]
  have hznonneg : 0 ≤ intOfZ z := hz.1
  have hzmax := hz.2
  have hzlt : intOfZ z < ((2 ^ 64 : Nat) : Int) := by
    change intOfZ z ≤ intOfZ CompCert4Lean.Lib.Integers.Int64.max_unsigned at hzmax
    change intOfZ z ≤ (2 ^ 64 : Int) - 1 at hzmax
    omega
  rw [Int.emod_eq_of_lt hznonneg hzlt]
  change zOfInt (↑(Int.toNat (intOfZ z)) : Int) = _
  rw [Int.toNat_of_nonneg hznonneg]

theorem divlu_mul_shift : divlu_mul_shiftStatement := by
  intro x y m p hparams
  have hs := divlu_mul_params_sound (int64Unsigned y) m p hparams
  rcases hs with ⟨hm, hp, hdiv⟩
  refine ⟨hp, ?_⟩
  change CompCert4Lean.Lib.Integers.Int64.divu x y =
    CompCert4Lean.Lib.Integers.Int64.shru'
      (CompCert4Lean.Lib.Integers.Int64.mulhu x
        (CompCert4Lean.Lib.Integers.Int64.repr m))
      (CompCert4Lean.Lib.Integers.Int.repr p)
  have hshift := int64_shru'_div_two_p
    (CompCert4Lean.Lib.Integers.Int64.mulhu x
      (CompCert4Lean.Lib.Integers.Int64.repr m))
    (CompCert4Lean.Lib.Integers.Int.repr p)
  change CompCert4Lean.Lib.Integers.Int64.shru'
      (CompCert4Lean.Lib.Integers.Int64.mulhu x
        (CompCert4Lean.Lib.Integers.Int64.repr m))
      (CompCert4Lean.Lib.Integers.Int.repr p) =
    CompCert4Lean.Lib.Integers.Int64.repr
      (zDiv
        (CompCert4Lean.Lib.Integers.Int64.unsigned
          (CompCert4Lean.Lib.Integers.Int64.mulhu x
            (CompCert4Lean.Lib.Integers.Int64.repr m)))
        (two_p
          (CompCert4Lean.Lib.Integers.Int.unsigned
            (CompCert4Lean.Lib.Integers.Int.repr p)))) at hshift
  rw [hshift]
  unfold CompCert4Lean.Lib.Integers.Int64.divu
    CompCert4Lean.Lib.Integers.WordCore.divu
    CompCert4Lean.Lib.Integers.Int64.mulhu
  change CompCert4Lean.Lib.Integers.Int64.repr
      (zDiv (int64Unsigned x) (int64Unsigned y)) =
    CompCert4Lean.Lib.Integers.Int64.repr
      (zDiv
        (int64Unsigned
          (int64Repr
            (zDiv (zMul (int64Unsigned x) (int64Unsigned (int64Repr m)))
              CompCert4Lean.Lib.Integers.Int64.modulus)))
        (two_p (intUnsigned (intRepr p))))
  have hm0 : zLe z0 m := hm.1
  have hm_lt : zLt m CompCert4Lean.Lib.Integers.Int64.modulus := hm.2
  have hmmax : zLe m CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
    change intOfZ m ≤ intOfZ CompCert4Lean.Lib.Integers.Int64.max_unsigned
    change intOfZ m ≤ intOfZ CompCert4Lean.Lib.Integers.Int64.modulus - 1
    change intOfZ m < intOfZ CompCert4Lean.Lib.Integers.Int64.modulus at hm_lt
    omega
  have hmrepr : int64Unsigned (int64Repr m) = m := by
    exact int64_unsigned_repr_local m ⟨hm0, hmmax⟩
  have hp0 : zLe z0 p := hp.1
  have hp_lt : zLt p z64 := hp.2
  have hpmax : zLe p CompCert4Lean.Lib.Integers.Int.max_unsigned := by
    change intOfZ p ≤ intOfZ CompCert4Lean.Lib.Integers.Int.max_unsigned
    change intOfZ p ≤ intOfZ CompCert4Lean.Lib.Integers.Int.modulus - 1
    change intOfZ p < intOfZ z64 at hp_lt
    have hz64 : intOfZ z64 = (64 : Int) := by rfl
    have hmodpow : intOfZ CompCert4Lean.Lib.Integers.Int.modulus =
        (2 ^ 32 : Int) := by rfl
    rw [hz64] at hp_lt
    rw [hmodpow]
    have hconst : (64 : Int) ≤ (2 ^ 32 : Int) - 1 := by decide
    omega
  have hprepr : intUnsigned (intRepr p) = p := by
    exact CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api p ⟨hp0, hpmax⟩
  rw [hmrepr, hprepr]
  have hx0 : zLe z0 (int64Unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ (int64Unsigned x) at h
    change 0 ≤ intOfZ (int64Unsigned x)
    omega
  have hxlt : zLt (int64Unsigned x) CompCert4Lean.Lib.Integers.Int64.modulus :=
    x.intrange.2
  have hmodpow : intOfZ CompCert4Lean.Lib.Integers.Int64.modulus =
      (2 ^ 64 : Int) := by rfl
  have hmodpos : 0 < intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := by
    rw [hmodpow]
    exact Int.pow_pos (by decide)
  have hnum0 : 0 ≤ intOfZ (zMul (int64Unsigned x) m) := by
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    exact Int.mul_nonneg hx0 hm0
  have hnum_lt : intOfZ (zMul (int64Unsigned x) m) <
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus *
        intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := by
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    have hA : intOfZ (int64Unsigned x) * intOfZ m ≤
        intOfZ CompCert4Lean.Lib.Integers.Int64.modulus * intOfZ m :=
      Int.mul_le_mul_of_nonneg_right (Int.le_of_lt hxlt) hm0
    have hB : intOfZ CompCert4Lean.Lib.Integers.Int64.modulus * intOfZ m <
        intOfZ CompCert4Lean.Lib.Integers.Int64.modulus *
          intOfZ CompCert4Lean.Lib.Integers.Int64.modulus :=
      Int.mul_lt_mul_of_pos_left hm_lt hmodpos
    exact Int.lt_of_le_of_lt hA hB
  have hq0 : zLe z0
      (zDiv (zMul (int64Unsigned x) m)
        CompCert4Lean.Lib.Integers.Int64.modulus) := by
    rw [zdiv_pos_int_local (zMul (int64Unsigned x) m)
      CompCert4Lean.Lib.Integers.Int64.modulus hmodpos]
    change 0 ≤ intOfZ (zOfInt _)
    simp only [intOfZ_zOfInt]
    exact Int.ediv_nonneg hnum0 (Int.le_of_lt hmodpos)
  have hq_lt : zLt
      (zDiv (zMul (int64Unsigned x) m)
        CompCert4Lean.Lib.Integers.Int64.modulus)
      CompCert4Lean.Lib.Integers.Int64.modulus := by
    rw [zdiv_pos_int_local (zMul (int64Unsigned x) m)
      CompCert4Lean.Lib.Integers.Int64.modulus hmodpos]
    change intOfZ (zOfInt _) < intOfZ CompCert4Lean.Lib.Integers.Int64.modulus
    simp only [intOfZ_zOfInt]
    exact Int.ediv_lt_of_lt_mul hmodpos hnum_lt
  have hqmax : zLe
      (zDiv (zMul (int64Unsigned x) m)
        CompCert4Lean.Lib.Integers.Int64.modulus)
      CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
    change intOfZ
        (zDiv (zMul (int64Unsigned x) m)
          CompCert4Lean.Lib.Integers.Int64.modulus) ≤
      intOfZ CompCert4Lean.Lib.Integers.Int64.max_unsigned
    change intOfZ
        (zDiv (zMul (int64Unsigned x) m)
          CompCert4Lean.Lib.Integers.Int64.modulus) ≤
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus - 1
    change intOfZ
        (zDiv (zMul (int64Unsigned x) m)
          CompCert4Lean.Lib.Integers.Int64.modulus) <
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus at hq_lt
    omega
  have hqrepr : int64Unsigned
      (int64Repr (zDiv (zMul (int64Unsigned x) m)
        CompCert4Lean.Lib.Integers.Int64.modulus)) =
      zDiv (zMul (int64Unsigned x) m)
        CompCert4Lean.Lib.Integers.Int64.modulus := by
    exact int64_unsigned_repr_local _ ⟨hq0, hqmax⟩
  rw [hqrepr]
  have hp0i : 0 ≤ intOfZ p := hp0
  have htp : 0 < intOfZ (two_p p) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (Int.not_lt_of_ge hp0i)]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
    exact Int.pow_pos (by decide)
  have hnest := zdiv_zdiv_pos_local (zMul (int64Unsigned x) m)
    CompCert4Lean.Lib.Integers.Int64.modulus (two_p p) hmodpos htp
  rw [hnest]
  have hmodz64 : two_p z64 = CompCert4Lean.Lib.Integers.Int64.modulus := by rfl
  have hden : zMul CompCert4Lean.Lib.Integers.Int64.modulus (two_p p) =
      two_p (zAdd z64 p) := by
    rw [← hmodz64]
    have hz640 : 0 ≤ intOfZ z64 := by
      change 0 ≤ (64 : Int)
      omega
    exact (two_p_add_local z64 p hz640 hp0i).symm
  rw [hden]
  have hdivx := hdiv (int64Unsigned x) ⟨hx0, hxlt⟩
  have hmulcomm : zMul (int64Unsigned x) m = zMul m (int64Unsigned x) := by
    apply intOfZ_injective
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt, Int.mul_comm]
  rw [hdivx, hmulcomm]

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.SelectDiv
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

private theorem eval_longconst_local
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (n : CCInt64) :
    eval_expr xi ge sp e m le (longconst n) (.Vlong n) := by
  exact eval_expr.eval_Eop le (.Olongconst n) .Enil [] (.Vlong n)
    (eval_exprlist.nil le) rfl

private theorem is_longconst_sound_local
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (a : expr) (x : val) (n : CCInt64)
    (hc : is_longconst a = some n) (he : eval_expr xi ge sp e m le a x) :
    x = .Vlong n := by
  have ha : a = Eop (Olongconst n) Enil := by
    cases a with
    | Evar id => simp [is_longconst] at hc
    | Eop op args =>
        cases op <;> cases args <;> simp [is_longconst] at hc ⊢ <;>
          cases hc <;> rfl
    | Eload chunk addr args => simp [is_longconst] at hc
    | Econdition c b d => simp [is_longconst] at hc
    | Elet b d => simp [is_longconst] at hc
    | Eletvar i => simp [is_longconst] at hc
    | Ebuiltin ef args => simp [is_longconst] at hc
    | Eexternal id sg args => simp [is_longconst] at hc
  subst a
  cases he with
  | eval_Eop _ _ _ vl _ hargs hop =>
      cases hargs
      change some (.Vlong n) = some x at hop
      cases hop
      rfl

private theorem eval_binary_op_local
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (op : operation) (a b : expr) (x y z : val)
    (ha : eval_expr xi ge sp e m le a x)
    (hb : eval_expr xi ge sp e m le b y)
    (hop : eval_operation ge sp op [x, y] m = some z) :
    eval_expr xi ge sp e m le (Eop op (Econs a (Econs b Enil))) z := by
  exact eval_expr.eval_Eop le op (Econs a (Econs b Enil)) [x, y] z
    (eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))) hop

private theorem eval_unary_op_local
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (op : operation) (a : expr) (x z : val)
    (ha : eval_expr xi ge sp e m le a x)
    (hop : eval_operation ge sp op [x] m = some z) :
    eval_expr xi ge sp e m le (Eop op (Econs a Enil)) z := by
  exact eval_expr.eval_Eop le op (Econs a Enil) [x] z
    (eval_exprlist.cons le a Enil x [] ha (eval_exprlist.nil le)) hop

private theorem eval_intconst_local
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (n : CCInt) :
    eval_expr xi ge sp e m le (Eop (Ointconst n) Enil) (.Vint n) := by
  exact eval_expr.eval_Eop le (.Ointconst n) .Enil [] (.Vint n)
    (eval_exprlist.nil le) rfl

private theorem eval_divlu_base_local
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (a b : expr) (x y z : val)
    (ha : eval_expr xi ge sp e m le a x)
    (hb : eval_expr xi ge sp e m le b y)
    (hz : Val.divlu x y = some z) :
    eval_expr xi ge sp e m le (divlu_base a b) z := by
  exact eval_binary_op_local xi ge sp e m le Odivlu a b x y z ha hb hz

private theorem eval_modlu_base_local
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (a b : expr) (x y z : val)
    (ha : eval_expr xi ge sp e m le a x)
    (hb : eval_expr xi ge sp e m le b y)
    (hz : Val.modlu x y = some z) :
    eval_expr xi ge sp e m le (modlu_base a b) z := by
  exact eval_binary_op_local xi ge sp e m le Omodlu a b x y z ha hb hz

private theorem eval_divls_base_local
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (a b : expr) (x y z : val)
    (ha : eval_expr xi ge sp e m le a x)
    (hb : eval_expr xi ge sp e m le b y)
    (hz : Val.divls x y = some z) :
    eval_expr xi ge sp e m le (divls_base a b) z := by
  exact eval_binary_op_local xi ge sp e m le Odivl a b x y z ha hb hz

private theorem int_eq_true_zero_local (n : CCInt)
    (h : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true) :
    n = CompCert4Lean.Lib.Integers.Int.zero := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (n.intval =
      CompCert4Lean.Lib.Integers.Int.zero.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem int_add_commut_local (a b : CCInt) :
    CompCert4Lean.Lib.Integers.Int.add a b =
      CompCert4Lean.Lib.Integers.Int.add b a := by
  unfold CompCert4Lean.Lib.Integers.Int.add
    CompCert4Lean.Lib.Integers.WordCore.add
  apply congrArg (CompCert4Lean.Lib.Integers.WordCore.repr 32)
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt, Int.add_comm]

private theorem int64_repr_unsigned_local (x : CCInt64) :
    int64Repr (int64Unsigned x) = x := by
  have hx0 : zLe z0 (int64Unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  have hxlt : zLt (int64Unsigned x)
      CompCert4Lean.Lib.Integers.Int64.modulus := x.intrange.2
  have hxmax : zLe (int64Unsigned x)
      CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
    change intOfZ x.intval ≤
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus - 1
    change intOfZ x.intval <
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus at hxlt
    omega
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  exact int64_unsigned_repr_local (int64Unsigned x) ⟨hx0, hxmax⟩

private theorem two_p_pos_local (p : CCZ) (hp : zLe z0 p) :
    0 < intOfZ (two_p p) := by
  change 0 ≤ intOfZ p at hp
  unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
  rw [if_neg (Int.not_lt_of_ge hp)]
  simp only [intOfZ_zOfInt]
  have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
  rw [hbase]
  exact Int.pow_pos (by decide)

private theorem int64_unsigned_repr_div_two_p_local
    (x : CCInt64) (p : CCZ) (hp : zLe z0 p) :
    int64Unsigned (int64Repr (zDiv (int64Unsigned x) (two_p p))) =
      zDiv (int64Unsigned x) (two_p p) := by
  have hden : 0 < intOfZ (two_p p) := two_p_pos_local p hp
  have hx0 : 0 ≤ intOfZ (int64Unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  have hxlt : intOfZ (int64Unsigned x) <
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := x.intrange.2
  have hmodpos : 0 < intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := by
    change (0 : Int) < 2 ^ 64
    decide
  have hq0 : zLe z0 (zDiv (int64Unsigned x) (two_p p)) := by
    rw [zdiv_pos_int_local (int64Unsigned x) (two_p p) hden]
    change 0 ≤ intOfZ (zOfInt _)
    simp only [intOfZ_zOfInt]
    exact Int.ediv_nonneg hx0 (Int.le_of_lt hden)
  have hden1 : 1 ≤ intOfZ (two_p p) := by omega
  have hnumlt : intOfZ (int64Unsigned x) <
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus * intOfZ (two_p p) := by
    have hmul : intOfZ CompCert4Lean.Lib.Integers.Int64.modulus ≤
        intOfZ CompCert4Lean.Lib.Integers.Int64.modulus * intOfZ (two_p p) := by
      have h := Int.mul_le_mul_of_nonneg_left hden1 (Int.le_of_lt hmodpos)
      simpa only [Int.mul_one] using h
    exact Int.lt_of_lt_of_le hxlt hmul
  have hqlt : zLt (zDiv (int64Unsigned x) (two_p p))
      CompCert4Lean.Lib.Integers.Int64.modulus := by
    rw [zdiv_pos_int_local (int64Unsigned x) (two_p p) hden]
    change intOfZ (zOfInt _) <
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus
    simp only [intOfZ_zOfInt]
    exact Int.ediv_lt_of_lt_mul hden hnumlt
  have hqmax : zLe (zDiv (int64Unsigned x) (two_p p))
      CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
    change intOfZ (zDiv (int64Unsigned x) (two_p p)) ≤
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus - 1
    change intOfZ (zDiv (int64Unsigned x) (two_p p)) <
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus at hqlt
    omega
  exact int64_unsigned_repr_local _ ⟨hq0, hqmax⟩

private theorem int64_shru'_zero_local (x : CCInt64) :
    int64Shru' x CompCert4Lean.Lib.Integers.Int.zero = x := by
  rw [int64_shru'_div_two_p]
  change int64Repr (zDiv (int64Unsigned x) (two_p z0)) = x
  have hdiv : zDiv (int64Unsigned x) (two_p z0) = int64Unsigned x := by
    apply intOfZ_injective
    rw [zdiv_pos_int_local (int64Unsigned x) (two_p z0) (by decide)]
    simp only [intOfZ_zOfInt]
    exact Int.ediv_one _
  rw [hdiv]
  exact int64_repr_unsigned_local x

private theorem int_unsigned_nonneg_local (n : CCInt) :
    zLe z0 (intUnsigned n) := by
  have h := n.intrange.1
  change (-1 : Int) < intOfZ n.intval at h
  change 0 ≤ intOfZ n.intval
  omega

private theorem int64_shru'_shru'_local (x : CCInt64) (y z : CCInt)
    (hy : CompCert4Lean.Lib.Integers.Int.ltu y
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true)
    (hz : CompCert4Lean.Lib.Integers.Int.ltu z
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true)
    (hs : CompCert4Lean.Lib.Integers.Int.ltu
      (CompCert4Lean.Lib.Integers.Int.add y z)
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true) :
    int64Shru' (int64Shru' x y) z =
      int64Shru' x (CompCert4Lean.Lib.Integers.Int.add y z) := by
  have hyb := CompCert4Lean.Lib.Integers.Int.ltu_inv_proof y
    CompCert4Lean.Lib.Integers.Int64.iwordsize' hy
  have hzb := CompCert4Lean.Lib.Integers.Int.ltu_inv_proof z
    CompCert4Lean.Lib.Integers.Int64.iwordsize' hz
  have hy0 := int_unsigned_nonneg_local y
  have hz0 := int_unsigned_nonneg_local z
  have hadd : intUnsigned (CompCert4Lean.Lib.Integers.Int.add y z) =
      zAdd (intUnsigned y) (intUnsigned z) := by
    unfold CompCert4Lean.Lib.Integers.Int.add
      CompCert4Lean.Lib.Integers.WordCore.add
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · have hnonneg : zLe z0 (zAdd (intUnsigned y) (intUnsigned z)) := by
        change intOfZ z0 ≤ intOfZ (zAdd (intUnsigned y) (intUnsigned z))
        rw [show intOfZ z0 = 0 by rfl]
        simpa only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] using
          (Int.add_nonneg hy0 hz0)
      exact hnonneg
    · have hylt : intOfZ (intUnsigned y) < 64 := by
        have h := hyb.2
        change intOfZ (intUnsigned y) < 64 at h
        exact h
      have hzlt : intOfZ (intUnsigned z) < 64 := by
        have h := hzb.2
        change intOfZ (intUnsigned z) < 64 at h
        exact h
      have hmax : zLe (zAdd (intUnsigned y) (intUnsigned z))
          CompCert4Lean.Lib.Integers.Int.max_unsigned := by
        change intOfZ (zAdd (intUnsigned y) (intUnsigned z)) ≤
          intOfZ CompCert4Lean.Lib.Integers.Int.max_unsigned
        have hi : intOfZ (intUnsigned y) + intOfZ (intUnsigned z) ≤
            intOfZ CompCert4Lean.Lib.Integers.Int.max_unsigned := by
          change intOfZ (intUnsigned y) + intOfZ (intUnsigned z) ≤ 2 ^ 32 - 1
          omega
        simpa only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] using hi
      exact hmax
  rw [int64_shru'_div_two_p, int64_shru'_div_two_p,
    int64_shru'_div_two_p]
  rw [int64_unsigned_repr_div_two_p_local x (intUnsigned y) hy0]
  rw [hadd]
  have hpy : 0 < intOfZ (two_p (intUnsigned y)) :=
    two_p_pos_local _ hy0
  have hpz : 0 < intOfZ (two_p (intUnsigned z)) :=
    two_p_pos_local _ hz0
  rw [zdiv_zdiv_pos_local (int64Unsigned x) (two_p (intUnsigned y))
    (two_p (intUnsigned z)) hpy hpz]
  rw [two_p_add_local (intUnsigned y) (intUnsigned z) hy0 hz0]

private theorem eval_shrluimm_local
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (a : expr) (x : val) (n : CCInt)
    (ha : eval_expr xi ge sp e m le a x) :
    ∃ v, eval_expr xi ge sp e m le (shrluimm a n) v ∧
      Val.lessdef (Val.shrlu x (.Vint n)) v := by
  unfold shrluimm
  by_cases hn0 : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · have hn := int_eq_true_zero_local n hn0
    subst n
    refine ⟨x, ?_, ?_⟩
    · simpa [hn0] using ha
    · cases x with
      | Vundef => exact Val.lessdef_refl _
      | Vint i => exact Val.lessdef_undef _
      | Vlong i =>
          have hlt0 : CompCert4Lean.Lib.Integers.Int.ltu
              CompCert4Lean.Lib.Integers.Int.zero
              CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by rfl
          simp only [Val.shrlu, hlt0, if_true, int64_shru'_zero_local]
          exact Val.lessdef_refl _
      | Vfloat f => exact Val.lessdef_undef _
      | Vsingle f => exact Val.lessdef_undef _
      | Vptr b ofs => exact Val.lessdef_undef _
  · rw [if_neg hn0]
    by_cases hlt : CompCert4Lean.Lib.Integers.Int.ltu n
        CompCert4Lean.Lib.Integers.Int64.iwordsize' = true
    · simp only [hlt, Bool.not_true, Bool.false_eq_true, if_false]
      cases hmatch : shrluimm_match a with
      | shrluimm_case1 n1 =>
          have hx : x = .Vlong n1 :=
            is_longconst_sound_local xi ge sp e m le
              (Eop (Olongconst n1) Enil) x n1 rfl ha
          subst x
          refine ⟨.Vlong (int64Shru' n1 n), ?_, ?_⟩
          · change eval_expr xi ge sp e m le (longconst (int64Shru' n1 n))
              (.Vlong (int64Shru' n1 n))
            exact eval_longconst_local xi ge sp e m le (int64Shru' n1 n)
          · simp only [Val.shrlu, hlt, if_true]
            exact Val.lessdef_refl _
      | shrluimm_case2 n1 t1 =>
          have ha0 := ha
          cases ha with
          | eval_Eop _ _ _ vl _ hargs hop =>
              cases hargs with
              | cons _ _ _ v1 _ hhead htail =>
                  cases htail with
                  | nil _ =>
                      change some (Val.shrlu v1 (.Vint n1)) = some x at hop
                      cases hop
                      by_cases hs : CompCert4Lean.Lib.Integers.Int.ltu
                          (CompCert4Lean.Lib.Integers.Int.add n n1)
                          CompCert4Lean.Lib.Integers.Int64.iwordsize' = true
                      · let out := Val.shrlu v1
                            (.Vint (CompCert4Lean.Lib.Integers.Int.add n n1))
                        refine ⟨out, ?_, ?_⟩
                        · simpa [hmatch, hs, out] using
                            (eval_unary_op_local xi ge sp e m le
                              (Oshrluimm (CompCert4Lean.Lib.Integers.Int.add n n1))
                              t1 v1 out hhead rfl)
                        · cases v1 with
                          | Vlong i =>
                              by_cases hlt1 : CompCert4Lean.Lib.Integers.Int.ltu n1
                                  CompCert4Lean.Lib.Integers.Int64.iwordsize' = true
                              · have hs' : CompCert4Lean.Lib.Integers.Int.ltu
                                    (CompCert4Lean.Lib.Integers.Int.add n1 n)
                                    CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
                                    rw [int_add_commut_local n1 n]
                                    exact hs
                                have heq : int64Shru' (int64Shru' i n1) n =
                                    int64Shru' i
                                      (CompCert4Lean.Lib.Integers.Int.add n n1) := by
                                  rw [int64_shru'_shru'_local i n1 n hlt1 hlt hs']
                                  rw [int_add_commut_local n1 n]
                                simp only [Val.shrlu, hlt1, hlt, hs, if_true, out]
                                change Val.lessdef (.Vlong (int64Shru' (int64Shru' i n1) n))
                                  (.Vlong (int64Shru' i
                                    (CompCert4Lean.Lib.Integers.Int.add n n1)))
                                rw [heq]
                                exact Val.lessdef_refl _
                              · simp only [Val.shrlu, hlt1, if_false, out]
                                exact Val.lessdef_undef _
                          | Vundef => exact Val.lessdef_refl _
                          | Vint i => exact Val.lessdef_refl _
                          | Vfloat f => exact Val.lessdef_refl _
                          | Vsingle f => exact Val.lessdef_refl _
                          | Vptr b ofs => exact Val.lessdef_refl _
                      · let out := Val.shrlu (Val.shrlu v1 (.Vint n1)) (.Vint n)
                        refine ⟨out, ?_, Val.lessdef_refl out⟩
                        simpa [hmatch, hs, out] using
                          (eval_unary_op_local xi ge sp e m le (Oshrluimm n)
                            (Eop (Oshrluimm n1) (Econs t1 Enil))
                            (Val.shrlu v1 (.Vint n1)) out ha0 rfl)
      | shrluimm_default e1 =>
          let out := Val.shrlu x (.Vint n)
          refine ⟨out, ?_, Val.lessdef_refl out⟩
          simpa [hmatch, out] using
            (eval_unary_op_local xi ge sp e m le (Oshrluimm n) a x out ha rfl)
    · simp only [hlt, Bool.not_false, if_true]
      let en := Eop (Ointconst n) Enil
      let out := Val.shrlu x (.Vint n)
      refine ⟨out, ?_, Val.lessdef_refl out⟩
      simpa [en, out] using
        (eval_binary_op_local xi ge sp e m le Oshrlu a en x (.Vint n) out
          ha (eval_intconst_local xi ge sp e m le n) rfl)

private theorem int_ltu_repr_64_local (p : CCZ)
    (hp : zLe z0 p ∧ zLt p z64) :
    CompCert4Lean.Lib.Integers.Int.ltu (intRepr p)
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
  have hpmax : zLe p CompCert4Lean.Lib.Integers.Int.max_unsigned := by
    change intOfZ p ≤ 2 ^ 32 - 1
    have h := hp.2
    change intOfZ p < 64 at h
    omega
  have hu : CompCert4Lean.Lib.Integers.Int.unsigned (intRepr p) = p :=
    CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api p ⟨hp.1, hpmax⟩
  have hi : CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = z64 := by
    unfold CompCert4Lean.Lib.Integers.Int64.iwordsize'
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · change (0 : Int) ≤ 64
      omega
    · change (64 : Int) ≤ 2 ^ 32 - 1
      omega
  have hrev : CompCert4Lean.Lib.Integers.Int.ltu
      CompCert4Lean.Lib.Integers.Int64.iwordsize' (intRepr p) = false := by
    cases hval : CompCert4Lean.Lib.Integers.Int.ltu
        CompCert4Lean.Lib.Integers.Int64.iwordsize' (intRepr p) with
    | false => rfl
    | true =>
        have hr := CompCert4Lean.Lib.Integers.Int.ltu_inv_proof
          CompCert4Lean.Lib.Integers.Int64.iwordsize' (intRepr p) hval
        rw [hi, hu] at hr
        have hge := hr.2
        have hlt := hp.2
        change intOfZ z64 < intOfZ p at hge
        change intOfZ p < intOfZ z64 at hlt
        omega
  have hneq : intRepr p ≠ CompCert4Lean.Lib.Integers.Int64.iwordsize' := by
    intro h
    have he := congrArg CompCert4Lean.Lib.Integers.Int.unsigned h
    rw [hu, hi] at he
    have hlt := hp.2
    change intOfZ p < intOfZ z64 at hlt
    rw [he] at hlt
    exact (Int.lt_irrefl _ hlt).elim
  have hvalneq : (intRepr p).intval ≠
      CompCert4Lean.Lib.Integers.Int64.iwordsize'.intval := by
    intro h
    exact hneq (CompCert4Lean.Lib.Integers.WordCore.ext h)
  have heq : CompCert4Lean.Lib.Integers.Int.eq (intRepr p)
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = false := by
    unfold CompCert4Lean.Lib.Integers.Int.eq
      CompCert4Lean.Lib.Integers.WordCore.eq
    simp [hvalneq]
  have hnot := CompCert4Lean.Lib.Integers.Int.not_ltu_proof
    (intRepr p) CompCert4Lean.Lib.Integers.Int64.iwordsize'
  rw [hrev, heq] at hnot
  simpa using hnot.symm

private theorem int64_mulhu_eq_local (x y : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.mulhu x y = int64Mulhu x y := by
  unfold CompCert4Lean.Lib.Integers.Int64.mulhu int64Mulhu
  change int64Repr (zDiv (zMul (int64Unsigned x) (int64Unsigned y))
      CompCert4Lean.Lib.Integers.Int64.modulus) =
    int64Repr (zShiftr (zMul (int64Unsigned x) (int64Unsigned y)) z64)
  rw [zshiftr_div_two_p_local (zMul (int64Unsigned x) (int64Unsigned y)) z64
    (by change (0 : Int) ≤ 64; omega)]
  rfl

private theorem eval_divlu_mull_local
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (hf : CompCert4Lean.Backend.SplitLong.helper_functions)
    (le : letenv) (x y : CCInt64) (p M : CCZ)
    (hparams : divlu_mul_params (int64Unsigned y) = some (p, M))
    (hnth : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.nth_error le 0 =
      some (.Vlong x)) :
    eval_expr xi ge sp e m le (divlu_mull (hf := hf) p M)
      (.Vlong (int64Divu x y)) := by
  obtain ⟨hp, hshift⟩ := divlu_mul_shift x y M p hparams
  have hlet : eval_expr xi ge sp e m le (Eletvar 0) (.Vlong x) :=
    eval_expr.eval_Eletvar le 0 (.Vlong x) hnth
  have hc : eval_expr xi ge sp e m le (longconst (int64Repr M))
      (.Vlong (int64Repr M)) := eval_longconst_local xi ge sp e m le _
  have hmul0 : eval_expr xi ge sp e m le
      (mullhu (Eletvar 0) (int64Repr M))
      (.Vlong (CompCert4Lean.Lib.Integers.Int64.mulhu x (int64Repr M))) := by
    exact eval_binary_op_local xi ge sp e m le Omullhu
      (Eletvar 0) (longconst (int64Repr M)) (.Vlong x) (.Vlong (int64Repr M))
      (.Vlong (CompCert4Lean.Lib.Integers.Int64.mulhu x (int64Repr M))) hlet hc rfl
  have hmul : eval_expr xi ge sp e m le
      (mullhu (Eletvar 0) (int64Repr M))
      (.Vlong (int64Mulhu x (int64Repr M))) := by
    rw [← int64_mulhu_eq_local x (int64Repr M)]
    exact hmul0
  obtain ⟨v, hv, hd⟩ := eval_shrluimm_local xi ge sp e m le
    (mullhu (Eletvar 0) (int64Repr M))
    (.Vlong (int64Mulhu x (int64Repr M))) (intRepr p) hmul
  have hlt := int_ltu_repr_64_local p hp
  have hd' : Val.lessdef (.Vlong (int64Divu x y)) v := by
    rw [hshift]
    simpa only [Val.shrlu, hlt, if_true] using hd
  have hv' : eval_expr xi ge sp e m le (divlu_mull (hf := hf) p M) v := by
    simpa [divlu_mull] using hv
  cases hd'
  exact hv'

private theorem int64_is_power2'_correct_local (n : CCInt64) (logn : CCInt)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    int64Unsigned n = two_p (intUnsigned logn) := by
  unfold CompCert4Lean.Lib.Integers.Int64.is_power2' at hpow
  generalize hbits : CompCert4Lean.Lib.Zbits.Z_one_bits
      CompCert4Lean.Lib.Integers.Int64.wordsize (int64Unsigned n) z0 = bits at hpow
  cases bits with
  | nil => simp at hpow
  | cons i rest =>
      cases rest with
      | nil =>
          simp only at hpow
          cases hpow
          have hirange := CompCert4Lean.Lib.Zbits.Z_one_bits_range
            CompCert4Lean.Lib.Integers.Int64.wordsize (int64Unsigned n) i
            (by rw [hbits]; simp)
          have himax : zLe i CompCert4Lean.Lib.Integers.Int.max_unsigned := by
            have hlt := hirange.2
            change intOfZ i < 64 at hlt
            change intOfZ i ≤ 2 ^ 32 - 1
            omega
          have hi : intUnsigned (intRepr i) = i :=
            CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api i
              ⟨hirange.1, himax⟩
          rw [hi]
          have hn0 : zLe z0 (int64Unsigned n) := by
            have h := n.intrange.1
            change (-1 : Int) < intOfZ n.intval at h
            change 0 ≤ intOfZ n.intval
            omega
          have hnrange : zLe z0 (int64Unsigned n) ∧
              zLt (int64Unsigned n) CompCert4Lean.Lib.Integers.Int64.modulus :=
            ⟨hn0, n.intrange.2⟩
          have hseries := CompCert4Lean.Lib.Zbits.Z_one_bits_powerserie
            CompCert4Lean.Lib.Integers.Int64.wordsize (int64Unsigned n) hnrange
          rw [hbits] at hseries
          rw [hseries]
          apply intOfZ_injective
          simp only [CompCert4Lean.Lib.Zbits.powerserie,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            intOfZ_zOfInt]
          change intOfZ (two_p i) + 0 = intOfZ (two_p i)
          omega
      | cons j rest => simp at hpow

private theorem int64_divu_pow2_local (x n : CCInt64) (logn : CCInt)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    int64Divu x n = int64Shru' x logn := by
  have hc := int64_is_power2'_correct_local n logn hpow
  unfold int64Divu CompCert4Lean.Lib.Integers.Int64.divu
    CompCert4Lean.Lib.Integers.WordCore.divu
  change CompCert4Lean.Lib.Integers.WordCore.unsigned n =
    two_p (intUnsigned logn) at hc
  rw [hc, int64_shru'_div_two_p]
  rfl

private theorem int64_is_power2'_range_local (n : CCInt64) (logn : CCInt)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int.ltu logn
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
  unfold CompCert4Lean.Lib.Integers.Int64.is_power2' at hpow
  generalize hbits : CompCert4Lean.Lib.Zbits.Z_one_bits
      CompCert4Lean.Lib.Integers.Int64.wordsize (int64Unsigned n) z0 = bits at hpow
  cases bits with
  | nil => simp at hpow
  | cons i rest =>
      cases rest with
      | nil =>
          simp only at hpow
          cases hpow
          apply int_ltu_repr_64_local
          exact CompCert4Lean.Lib.Zbits.Z_one_bits_range
            CompCert4Lean.Lib.Integers.Int64.wordsize (int64Unsigned n) i
            (by rw [hbits]; simp)
      | cons j rest => simp at hpow

theorem eval_divlu
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
      (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
      (ZArith.BinInt.Z.of_nat 128)] : eval_divluStatement := by
  intro cfg xi prog hf hhelpers sp e m le a b x y z ha hb hz
  cases hbconst : is_longconst b with
  | none =>
      refine ⟨z, ?_, Val.lessdef_refl z⟩
      simpa [divlu, hbconst] using
        (eval_divlu_base_local xi (Genv.globalenv prog) sp e m le
          a b x y z ha hb hz)
  | some n2 =>
      have hy := is_longconst_sound_local xi (Genv.globalenv prog) sp e m le
        b y n2 hbconst hb
      subst y
      cases haconst : is_longconst a with
      | some n1 =>
          have hx := is_longconst_sound_local xi (Genv.globalenv prog) sp e m le
            a x n1 haconst ha
          subst x
          cases hzero : CompCert4Lean.Lib.Integers.Int64.eq n2
              CompCert4Lean.Lib.Integers.Int64.zero with
          | false =>
              simp [Val.divlu, hzero] at hz
              cases hz
              refine ⟨.Vlong (int64Divu n1 n2), ?_, Val.lessdef_refl _⟩
              simpa [divlu, hbconst, haconst] using
                (eval_longconst_local xi (Genv.globalenv prog) sp e m le
                  (int64Divu n1 n2))
          | true => simp [Val.divlu, hzero] at hz
      | none =>
          cases hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n2 with
          | some l =>
              cases x with
              | Vlong x1 =>
                  cases hzero : CompCert4Lean.Lib.Integers.Int64.eq n2
                      CompCert4Lean.Lib.Integers.Int64.zero with
                  | false =>
                      simp [Val.divlu, hzero] at hz
                      cases hz
                      obtain ⟨v, hv, hd⟩ := eval_shrluimm_local xi
                        (Genv.globalenv prog) sp e m le a (.Vlong x1) l ha
                      refine ⟨v, ?_, ?_⟩
                      · simpa [divlu, hbconst, haconst, hpow] using hv
                      · have hlt := int64_is_power2'_range_local n2 l hpow
                        have hdiv := int64_divu_pow2_local x1 n2 l hpow
                        simpa [Val.shrlu, hlt, hdiv] using hd
                  | true => simp [Val.divlu, hzero] at hz
              | Vundef => simp [Val.divlu] at hz
              | Vint i => simp [Val.divlu] at hz
              | Vfloat f => simp [Val.divlu] at hz
              | Vsingle f => simp [Val.divlu] at hz
              | Vptr b ofs => simp [Val.divlu] at hz
          | none =>
              simp only [divlu, hbconst, haconst, hpow]
              split
              · refine ⟨z, ?_, Val.lessdef_refl z⟩
                exact eval_divlu_base_local xi (Genv.globalenv prog) sp e m le
                  a b x (.Vlong n2) z ha hb hz
              · cases hparams : divlu_mul_params (int64Unsigned n2) with
                | none =>
                    refine ⟨z, ?_, Val.lessdef_refl z⟩
                    exact eval_divlu_base_local xi (Genv.globalenv prog) sp e m le
                      a b x (.Vlong n2) z ha hb hz
                | some pm =>
                    rcases pm with ⟨p, M⟩
                    cases x with
                    | Vlong x1 =>
                        cases hzero : CompCert4Lean.Lib.Integers.Int64.eq n2
                            CompCert4Lean.Lib.Integers.Int64.zero with
                        | false =>
                            simp [Val.divlu, hzero] at hz
                            cases hz
                            have hbody := eval_divlu_mull_local xi
                              (Genv.globalenv prog) sp e m hf
                              (.Vlong x1 :: le) x1 n2 p M hparams rfl
                            refine ⟨.Vlong (int64Divu x1 n2), ?_,
                              Val.lessdef_refl _⟩
                            exact eval_expr.eval_Elet le a
                              (divlu_mull (hf := hf) p M) (.Vlong x1)
                              (.Vlong (int64Divu x1 n2)) ha hbody
                        | true => simp [Val.divlu, hzero] at hz
                    | Vundef => simp [Val.divlu] at hz
                    | Vint i => simp [Val.divlu] at hz
                    | Vfloat f => simp [Val.divlu] at hz
                    | Vsingle f => simp [Val.divlu] at hz
                    | Vptr b ofs => simp [Val.divlu] at hz

end CompCert4Lean.Backend.SelectDivproof

namespace CompCert4Lean.Backend.SelectDivproof

/-- Kernel-checked evidence for the positive division multiplication theorem. -/
theorem Zdiv_mul_pos : Zdiv_mul_posStatement := by
  exact zdiv_mul_pos_local

end CompCert4Lean.Backend.SelectDivproof
