import CompCert4Lean.Backend.Asmgenproof0
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Values
import CompCert4Lean.X86.Asmgen
import CompCert4Lean.X86.Op

/-!
# Auxiliary correctness surface for x86-64 generation

The executable definitions in this module are the direct translations of
`x86/Asmgenproof1.v`.  Proof-bearing source declarations remain transparent
proposition descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Asm
open CompCert4Lean.X86.Asmgen
open CompCert4Lean.X86.Op

private abbrev comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev Val := CompCert4Lean.Common.Values.val
private abbrev Int32 := CompCert4Lean.Lib.Integers.int
private abbrev Int64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev Preg := CompCert4Lean.X86.Asm.preg
private abbrev Ireg := CompCert4Lean.X86.Asm.ireg
private abbrev Mreg := CompCert4Lean.X86.Machregs.mreg
private abbrev Mem := CompCert4Lean.Common.Memory.mem
private abbrev AsmGenv := CompCert4Lean.X86.Asm.genv
private abbrev AsmFunction := CompCert4Lean.X86.Asm.function
private abbrev AsmCode := CompCert4Lean.X86.Asm.code
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

def eval_extcond (xc : extcond) (rs : regset) : Option Bool :=
  match xc with
  | .Cond_base c => eval_testcond c rs
  | .Cond_and c1 c2 =>
      match eval_testcond c1 rs, eval_testcond c2 rs with
      | some b1, some b2 => some (b1 && b2)
      | _, _ => none
  | .Cond_or c1 c2 =>
      match eval_testcond c1 rs, eval_testcond c2 rs with
      | some b1, some b2 => some (b1 || b2)
      | _, _ => none

def swap_floats {A : Type} (c : comparison) (n1 n2 : A) : A :=
  match c with
  | .Clt | .Cle => n2
  | .Ceq | .Cne | .Cgt | .Cge => n1

def negate_extcond (xc : extcond) : extcond :=
  match xc with
  | .Cond_base c => .Cond_base (negate_testcond c)
  | .Cond_and c1 c2 => .Cond_or (negate_testcond c1) (negate_testcond c2)
  | .Cond_or c1 c2 => .Cond_and (negate_testcond c1) (negate_testcond c2)

/-! Exact statement descriptors for the later proof-migration phase. -/

def addressing_mentions_correctStatement : Prop :=
  ∀ (ge : AsmGenv) (a : addrmode) (r : Ireg) (rs1 rs2 : regset),
    (∀ r', r' ≠ r → rs1 (.IR r') = rs2 (.IR r')) →
    addressing_mentions a r = false →
    eval_addrmode32 ge a rs1 = eval_addrmode32 ge a rs2

def agree_nextinstr_nfStatement : Prop :=
  ∀ (ms : CompCert4Lean.Backend.Mach.regset) (sp : Val) (rs : regset),
    agree ms sp rs → agree ms sp (nextinstr_nf rs)

def compare_floats32_invStatement : Prop :=
  ∀ (vx vy : Val) (rs : regset) (r : Preg),
    r ≠ .CR .ZF → r ≠ .CR .CF → r ≠ .CR .PF →
    r ≠ .CR .SF → r ≠ .CR .OF →
    compare_floats32 vx vy rs r = rs r

def compare_floats32_specStatement : Prop :=
  ∀ (rs : regset) (n1 n2 : CompCert4Lean.Lib.Floats.float32),
    let rs' := nextinstr (compare_floats32 (.Vsingle n1) (.Vsingle n2) rs)
    rs' (.CR .ZF) = Val.of_bool (CompCert4Lean.Lib.Floats.Float32.cmp .Ceq n1 n2 ||
        !(CompCert4Lean.Lib.Floats.Float32.ordered n1 n2)) ∧
    rs' (.CR .CF) = Val.of_bool (!(CompCert4Lean.Lib.Floats.Float32.cmp .Cge n1 n2)) ∧
    rs' (.CR .PF) = Val.of_bool (!(CompCert4Lean.Lib.Floats.Float32.ordered n1 n2)) ∧
    (∀ r, data_preg r = true → rs' r = rs r)

def compare_floats_invStatement : Prop :=
  ∀ (vx vy : Val) (rs : regset) (r : Preg),
    r ≠ .CR .ZF → r ≠ .CR .CF → r ≠ .CR .PF →
    r ≠ .CR .SF → r ≠ .CR .OF →
    compare_floats vx vy rs r = rs r

def compare_floats_specStatement : Prop :=
  ∀ (rs : regset) (n1 n2 : CompCert4Lean.Lib.Floats.float),
    let rs' := nextinstr (compare_floats (.Vfloat n1) (.Vfloat n2) rs)
    rs' (.CR .ZF) = Val.of_bool (CompCert4Lean.Lib.Floats.Float.cmp .Ceq n1 n2 ||
        !(CompCert4Lean.Lib.Floats.Float.ordered n1 n2)) ∧
    rs' (.CR .CF) = Val.of_bool (!(CompCert4Lean.Lib.Floats.Float.cmp .Cge n1 n2)) ∧
    rs' (.CR .PF) = Val.of_bool (!(CompCert4Lean.Lib.Floats.Float.ordered n1 n2)) ∧
    (∀ r, data_preg r = true → rs' r = rs r)

def compare_ints_specStatement : Prop :=
  ∀ (rs : regset) (v1 v2 : Val) (m : Mem),
    let rs' := nextinstr (compare_ints v1 v2 rs m)
    rs' (.CR .ZF) = Val.cmpu (Mem.valid_pointer m) .Ceq v1 v2 ∧
    rs' (.CR .CF) = Val.cmpu (Mem.valid_pointer m) .Clt v1 v2 ∧
    rs' (.CR .SF) = Val.negative (Val.sub v1 v2) ∧
    rs' (.CR .OF) = Val.sub_overflow v1 v2 ∧
    (∀ r, data_preg r = true → rs' r = rs r)

def compare_longs_specStatement : Prop :=
  ∀ (rs : regset) (v1 v2 : Val) (m : Mem),
    let rs' := nextinstr (compare_longs v1 v2 rs m)
    rs' (.CR .ZF) = Val.maketotal (Val.cmplu (Mem.valid_pointer m) .Ceq v1 v2) ∧
    rs' (.CR .CF) = Val.maketotal (Val.cmplu (Mem.valid_pointer m) .Clt v1 v2) ∧
    rs' (.CR .SF) = Val.negativel (Val.subl v1 v2) ∧
    rs' (.CR .OF) = Val.subl_overflow v1 v2 ∧
    (∀ r, data_preg r = true → rs' r = rs r)

def divu_modu_existsStatement : Prop :=
  let divmodu2 : Int32 → Int32 → Int32 → Option (Int32 × Int32) :=
    fun nhi nlo d =>
      if CompCert4Lean.Lib.Integers.Int.eq d CompCert4Lean.Lib.Integers.Int.zero then none
      else
        let qr := ZArith.BinInt.Z.div_eucl
          (ZArith.BinInt.Z.add
            (ZArith.BinInt.Z.mul
              (CompCert4Lean.Lib.Integers.Int.unsigned nhi)
              CompCert4Lean.Lib.Integers.Int.modulus)
            (CompCert4Lean.Lib.Integers.Int.unsigned nlo))
          (CompCert4Lean.Lib.Integers.Int.unsigned d)
        match CompCert4Lean.Lib.Coqlib.zle qr.1
          CompCert4Lean.Lib.Integers.Int.max_unsigned with
        | .left _ => some (CompCert4Lean.Lib.Integers.Int.repr qr.1,
            CompCert4Lean.Lib.Integers.Int.repr qr.2)
        | .right _ => none
  ∀ (v1 v2 : Val),
    Val.divu v1 v2 ≠ none ∨ Val.modu v1 v2 ≠ none →
    ∃ (n d q r : Int32),
      v1 = .Vint n ∧ v2 = .Vint d ∧
      divmodu2 CompCert4Lean.Lib.Integers.Int.zero n d = some (q, r) ∧
      Val.divu v1 v2 = some (.Vint q) ∧ Val.modu v1 v2 = some (.Vint r)

def divs_mods_existsStatement : Prop :=
  let divmods2 : Int32 → Int32 → Int32 → Option (Int32 × Int32) :=
    fun nhi nlo d =>
      if CompCert4Lean.Lib.Integers.Int.eq d CompCert4Lean.Lib.Integers.Int.zero then none
      else
        let n := ZArith.BinInt.Z.add
          (ZArith.BinInt.Z.mul
            (CompCert4Lean.Lib.Integers.Int.signed nhi)
            CompCert4Lean.Lib.Integers.Int.modulus)
          (CompCert4Lean.Lib.Integers.Int.unsigned nlo)
        let sd := CompCert4Lean.Lib.Integers.Int.signed d
        let q := ZArith.BinInt.Z.quot n sd
        let r := ZArith.BinInt.Z.sub n (ZArith.BinInt.Z.mul q sd)
        match CompCert4Lean.Lib.Coqlib.zle
            CompCert4Lean.Lib.Integers.Int.min_signed q,
          CompCert4Lean.Lib.Coqlib.zle q
            CompCert4Lean.Lib.Integers.Int.max_signed with
        | .left _, .left _ => some (CompCert4Lean.Lib.Integers.Int.repr q,
            CompCert4Lean.Lib.Integers.Int.repr r)
        | _, _ => none
  ∀ (v1 v2 : Val),
    Val.divs v1 v2 ≠ none ∨ Val.mods v1 v2 ≠ none →
    ∃ (nh nl d q r : Int32),
      Val.shr v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr
        (ZArith.BinInt.Z.of_nat 31))) = .Vint nh ∧
      v1 = .Vint nl ∧ v2 = .Vint d ∧
      divmods2 nh nl d = some (q, r) ∧
      Val.divs v1 v2 = some (.Vint q) ∧ Val.mods v1 v2 = some (.Vint r)

def divlu_modlu_existsStatement : Prop :=
  let divmodu2 : Int64 → Int64 → Int64 → Option (Int64 × Int64) :=
    fun nhi nlo d =>
      if CompCert4Lean.Lib.Integers.Int64.eq d
          CompCert4Lean.Lib.Integers.Int64.zero then none
      else
        let qr := ZArith.BinInt.Z.div_eucl
          (ZArith.BinInt.Z.add
            (ZArith.BinInt.Z.mul
              (CompCert4Lean.Lib.Integers.Int64.unsigned nhi)
              CompCert4Lean.Lib.Integers.Int64.modulus)
            (CompCert4Lean.Lib.Integers.Int64.unsigned nlo))
          (CompCert4Lean.Lib.Integers.Int64.unsigned d)
        match CompCert4Lean.Lib.Coqlib.zle qr.1
          CompCert4Lean.Lib.Integers.Int64.max_unsigned with
        | .left _ => some (CompCert4Lean.Lib.Integers.Int64.repr qr.1,
            CompCert4Lean.Lib.Integers.Int64.repr qr.2)
        | .right _ => none
  ∀ (v1 v2 : Val),
    Val.divlu v1 v2 ≠ none ∨ Val.modlu v1 v2 ≠ none →
    ∃ (n d q r : Int64),
      v1 = .Vlong n ∧ v2 = .Vlong d ∧
      divmodu2 CompCert4Lean.Lib.Integers.Int64.zero n d = some (q, r) ∧
      Val.divlu v1 v2 = some (.Vlong q) ∧ Val.modlu v1 v2 = some (.Vlong r)

def divls_modls_existsStatement : Prop :=
  let divmods2 : Int64 → Int64 → Int64 → Option (Int64 × Int64) :=
    fun nhi nlo d =>
      if CompCert4Lean.Lib.Integers.Int64.eq d
          CompCert4Lean.Lib.Integers.Int64.zero then none
      else
        let n := ZArith.BinInt.Z.add
          (ZArith.BinInt.Z.mul
            (CompCert4Lean.Lib.Integers.Int64.signed nhi)
            CompCert4Lean.Lib.Integers.Int64.modulus)
          (CompCert4Lean.Lib.Integers.Int64.unsigned nlo)
        let sd := CompCert4Lean.Lib.Integers.Int64.signed d
        let q := ZArith.BinInt.Z.quot n sd
        let r := ZArith.BinInt.Z.sub n (ZArith.BinInt.Z.mul q sd)
        match CompCert4Lean.Lib.Coqlib.zle
            CompCert4Lean.Lib.Integers.Int64.min_signed q,
          CompCert4Lean.Lib.Coqlib.zle q
            CompCert4Lean.Lib.Integers.Int64.max_signed with
        | .left _, .left _ => some (CompCert4Lean.Lib.Integers.Int64.repr q,
            CompCert4Lean.Lib.Integers.Int64.repr r)
        | _, _ => none
  ∀ (v1 v2 : Val),
    Val.divls v1 v2 ≠ none ∨ Val.modls v1 v2 ≠ none →
    ∃ (nh nl d q r : Int64),
      Val.shrl v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr
        (ZArith.BinInt.Z.of_nat 63))) = .Vlong nh ∧
      v1 = .Vlong nl ∧ v2 = .Vlong d ∧
      divmods2 nh nl d = some (q, r) ∧
      Val.divls v1 v2 = some (.Vlong q) ∧ Val.modls v1 v2 = some (.Vlong r)

def mk_shrximm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (n : Int32) (k c : AsmCode)
    (rs1 : regset) (v : Val) (m : Mem),
    mk_shrximm n k = .OK c →
    Val.shrx (rs1 (.IR .RAX)) (.Vint n) = some v →
    ∃ rs2, exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs1 m k rs2 m ∧
      rs2 (.IR .RAX) = v ∧
      (∀ r, data_preg r = true → r ≠ .IR .RAX → r ≠ .IR .RCX → rs2 r = rs1 r)

def mk_shrxlimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (n : Int32) (k c : AsmCode)
    (rs1 : regset) (v : Val) (m : Mem),
    mk_shrxlimm n k = .OK c →
    Val.shrxl (rs1 (.IR .RAX)) (.Vint n) = some v →
    ∃ rs2, exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs1 m k rs2 m ∧
      rs2 (.IR .RAX) = v ∧
      (∀ r, data_preg r = true → r ≠ .IR .RAX → r ≠ .IR .RDX → rs2 r = rs1 r)

def mk_storebyte_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (addr : addrmode) (r : Ireg)
    (k c : AsmCode) (rs1 : regset) (m1 m2 : Mem),
    mk_storebyte addr r k = .OK c →
    Mem.storev .Mint8unsigned m1 (eval_addrmode ge addr rs1) (rs1 (.IR r)) = some m2 →
    ∃ rs2, exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs1 m1 k rs2 m2 ∧
      (∀ r, data_preg r = true →
        preg_notin r (if CompCert4Lean.X86_64.Archi.ptr64 then [] else
          [CompCert4Lean.X86.Machregs.AX, CompCert4Lean.X86.Machregs.CX]) →
        rs2 r = rs1 r)

def negate_testcond_for_conditionStatement : Prop :=
  ∀ cond : condition,
    negate_extcond (testcond_for_condition cond) =
      testcond_for_condition (negate_condition cond)

def nextinstr_nf_invStatement : Prop :=
  ∀ (r : Preg) (rs : regset),
    (match r with | .PC | .CR _ => False | _ => True) →
    nextinstr_nf rs r = rs r

def nextinstr_nf_inv1Statement : Prop :=
  ∀ (r : Preg) (rs : regset), data_preg r = true → nextinstr_nf rs r = rs r

def normalize_addrmode_32_correctStatement : Prop :=
  ∀ (ge : AsmGenv) (am : addrmode) (rs : regset),
    eval_addrmode32 ge (normalize_addrmode_32 am) rs = eval_addrmode32 ge am rs

def normalize_addrmode_64_correctStatement : Prop :=
  ∀ (ge : AsmGenv) (am : addrmode) (rs : regset),
    eval_addrmode64 ge am rs =
      match normalize_addrmode_64 am with
      | (am', none) => eval_addrmode64 ge am' rs
      | (am', some delta) =>
          Val.addl (eval_addrmode64 ge am' rs) (.Vlong delta)

def storeind_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (base : Ireg) (ofs : Ptrofs)
    (ty : typ) (src : Mreg) (k : AsmCode) (rs : regset) (c : AsmCode)
    (m m' : Mem),
    storeind src base ofs ty k = .OK c →
    Mem.storev (chunk_of_type ty) m (Val.offset_ptr (rs (.IR base)) ofs)
      (rs (preg_of src)) = some m' →
    ∃ rs', exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs m k rs' m' ∧
      (∀ r, data_preg r = true →
        preg_notin r (CompCert4Lean.X86.Machregs.destroyed_by_setstack ty) →
        rs' r = rs r)

def swap_floats_commutStatement : Prop :=
  ∀ (A B : Type) (c : comparison) (f : A → B) (x y : A),
    swap_floats c (f x) (f y) = f (swap_floats c x y)

def testcond_for_float_comparison_correctStatement : Prop :=
  ∀ (c : comparison) (n1 n2 : CompCert4Lean.Lib.Floats.float) (rs : regset),
    eval_extcond (testcond_for_condition (.Ccompf c))
      (nextinstr (compare_floats
        (.Vfloat (swap_floats c n1 n2))
        (.Vfloat (swap_floats c n2 n1)) rs)) =
      some (CompCert4Lean.Lib.Floats.Float.cmp c n1 n2)

def testcond_for_neg_float_comparison_correctStatement : Prop :=
  ∀ (c : comparison) (n1 n2 : CompCert4Lean.Lib.Floats.float) (rs : regset),
    eval_extcond (testcond_for_condition (.Cnotcompf c))
      (nextinstr (compare_floats
        (.Vfloat (swap_floats c n1 n2))
        (.Vfloat (swap_floats c n2 n1)) rs)) =
      some (!(CompCert4Lean.Lib.Floats.Float.cmp c n1 n2))

def testcond_for_float32_comparison_correctStatement : Prop :=
  ∀ (c : comparison) (n1 n2 : CompCert4Lean.Lib.Floats.float32) (rs : regset),
    eval_extcond (testcond_for_condition (.Ccompfs c))
      (nextinstr (compare_floats32
        (.Vsingle (swap_floats c n1 n2))
        (.Vsingle (swap_floats c n2 n1)) rs)) =
      some (CompCert4Lean.Lib.Floats.Float32.cmp c n1 n2)

def testcond_for_neg_float32_comparison_correctStatement : Prop :=
  ∀ (c : comparison) (n1 n2 : CompCert4Lean.Lib.Floats.float32) (rs : regset),
    eval_extcond (testcond_for_condition (.Cnotcompfs c))
      (nextinstr (compare_floats32
        (.Vsingle (swap_floats c n1 n2))
        (.Vsingle (swap_floats c n2 n1)) rs)) =
      some (!(CompCert4Lean.Lib.Floats.Float32.cmp c n1 n2))

def testcond_for_signed_comparison_32_correctStatement : Prop :=
  ∀ (c : comparison) (v1 v2 : Val) (rs : regset) (m : Mem) (b : Bool),
    Val.cmp_bool c v1 v2 = some b →
    eval_testcond (testcond_for_signed_comparison c)
      (nextinstr (compare_ints v1 v2 rs m)) = some b

def testcond_for_unsigned_comparison_32_correctStatement : Prop :=
  ∀ (c : comparison) (v1 v2 : Val) (rs : regset) (m : Mem) (b : Bool),
    Val.cmpu_bool (Mem.valid_pointer m) c v1 v2 = some b →
    eval_testcond (testcond_for_unsigned_comparison c)
      (nextinstr (compare_ints v1 v2 rs m)) = some b

def testcond_for_signed_comparison_64_correctStatement : Prop :=
  ∀ (c : comparison) (v1 v2 : Val) (rs : regset) (m : Mem) (b : Bool),
    Val.cmpl_bool c v1 v2 = some b →
    eval_testcond (testcond_for_signed_comparison c)
      (nextinstr (compare_longs v1 v2 rs m)) = some b

def testcond_for_unsigned_comparison_64_correctStatement : Prop :=
  ∀ (c : comparison) (v1 v2 : Val) (rs : regset) (m : Mem) (b : Bool),
    Val.cmplu_bool (Mem.valid_pointer m) c v1 v2 = some b →
    eval_testcond (testcond_for_unsigned_comparison c)
      (nextinstr (compare_longs v1 v2 rs m)) = some b

def transl_addressing_mode_32_correctStatement : Prop :=
  ∀ (ge : AsmGenv) (addr : addressing) (args : List Mreg) (am : addrmode)
    (rs : regset) (v : Val),
    transl_addressing addr args = .OK am →
    eval_addressing32 ge (rs (.IR .RSP)) addr (args.map (fun r => rs (preg_of r))) = some v →
    Val.lessdef v (eval_addrmode32 ge am rs)

def transl_addressing_mode_64_correctStatement : Prop :=
  ∀ (ge : AsmGenv) (addr : addressing) (args : List Mreg) (am : addrmode)
    (rs : regset) (v : Val),
    transl_addressing addr args = .OK am →
    eval_addressing64 ge (rs (.IR .RSP)) addr (args.map (fun r => rs (preg_of r))) = some v →
    Val.lessdef v (eval_addrmode64 ge am rs)

def transl_addressing_mode_correctStatement : Prop :=
  ∀ (ge : AsmGenv) (addr : addressing) (args : List Mreg) (am : addrmode)
    (rs : regset) (v : Val),
    transl_addressing addr args = .OK am →
    eval_addressing ge (rs (.IR .RSP)) addr (args.map (fun r => rs (preg_of r))) = some v →
    Val.lessdef v (eval_addrmode ge am rs)

def eval_addrmode_indexedStatement : Prop :=
  ∀ (ge : AsmGenv) (base : Ireg) (ofs : Ptrofs) (rs : regset),
    (match rs (.IR base) with | .Vptr _ _ => True | _ => False) →
    eval_addrmode ge (.Addrmode (some base) none
      (Sum.inl (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs))) rs =
      Val.offset_ptr (rs (.IR base)) ofs

def eval_testcond_nextinstrStatement : Prop :=
  ∀ (c : testcond) (rs : regset), eval_testcond c (nextinstr rs) = eval_testcond c rs

def eval_testcond_set_iregStatement : Prop :=
  ∀ (c : testcond) (rs : regset) (r : Ireg) (v : Val),
    eval_testcond c (Pregmap.set (.IR r) v rs) = eval_testcond c rs

def loadind_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (base : Ireg) (ofs : Ptrofs)
    (ty : typ) (dst : Mreg) (k : AsmCode) (rs : regset) (c : AsmCode)
    (m : Mem) (v : Val),
    loadind base ofs ty dst k = .OK c →
    Mem.loadv (chunk_of_type ty) m (Val.offset_ptr (rs (.IR base)) ofs) = some v →
    ∃ rs', exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs m k rs' m ∧
      rs' (preg_of dst) = v ∧
      (∀ r, data_preg r = true → r ≠ preg_of dst → rs' r = rs r)

def mk_intconv_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction)
    (mk : Ireg → Ireg → instruction) (sem : Val → Val)
    (rd rs : Ireg) (k c : AsmCode) (rs1 : regset) (m : Mem),
    mk_intconv mk rd rs k = .OK c →
    (∀ (fn' : AsmFunction) (rd rs : Ireg) (r : regset) (m : Mem),
      exec_instr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge fn' (mk rd rs) r m = .Next (nextinstr
        (Pregmap.set (.IR rd) (sem (r (.IR rs))) r)) m) →
    ∃ rs2, exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs1 m k rs2 m ∧
      rs2 (.IR rd) = sem (rs1 (.IR rs)) ∧
      (∀ r, data_preg r = true → r ≠ .IR rd → r ≠ .IR .RAX → rs2 r = rs1 r)

def mk_mov_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (rd rs : Preg) (k c : AsmCode)
    (rs1 : regset) (m : Mem),
    mk_mov rd rs k = .OK c →
    ∃ rs2, exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs1 m k rs2 m ∧
      rs2 rd = rs1 rs ∧
      (∀ r, data_preg r = true → r ≠ rd → rs2 r = rs1 r)

def mk_setcc_base_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (cond : extcond) (rd : Ireg)
    (k : AsmCode) (rs1 : regset) (m : Mem),
    ∃ rs2, exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn (mk_setcc_base cond rd k) rs1 m k rs2 m ∧
      rs2 (.IR rd) = Val.of_optbool (eval_extcond cond rs1) ∧
      (∀ r, data_preg r = true → r ≠ .IR .RAX ∧ r ≠ .IR .RCX →
        r ≠ .IR rd → rs2 r = rs1 r)

def mk_setcc_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (cond : extcond) (rd : Ireg)
    (k : AsmCode) (rs1 : regset) (m : Mem),
    ∃ rs2, exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn (mk_setcc cond rd k) rs1 m k rs2 m ∧
      rs2 (.IR rd) = Val.of_optbool (eval_extcond cond rs1) ∧
      (∀ r, data_preg r = true → r ≠ .IR .RAX ∧ r ≠ .IR .RCX →
        r ≠ .IR rd → rs2 r = rs1 r)

def mk_sel_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (xc : extcond) (ty : typ)
    (rd r2 : Ireg) (k c : AsmCode) (ob : Option Bool) (rs : regset) (m : Mem),
    mk_sel xc rd r2 k = .OK c → rd ≠ r2 →
    (match ob with
    | some b => eval_extcond xc rs = some b ∧
        eval_extcond (negate_extcond xc) rs = some (!b)
    | none => True) →
    ∃ rs', exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs m k rs' m ∧
      Val.lessdef (Val.select ob (rs (.IR rd)) (rs (.IR r2)) ty) (rs' (.IR rd)) ∧
      (∀ r, data_preg r = true → r ≠ .IR rd → rs' r = rs r)

def transl_cond_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (cond : condition) (args : List Mreg)
    (k c : AsmCode) (rs : regset) (m : Mem),
    transl_cond cond args k = .OK c →
    ∃ rs', exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs m k rs' m ∧
      (match eval_condition cond (args.map (fun r => rs (preg_of r))) m with
      | none => True
      | some b => eval_extcond (testcond_for_condition cond) rs' = some b ∧
          eval_extcond (testcond_for_condition (negate_condition cond)) rs' = some (!b)) ∧
      (∀ r, data_preg r = true → rs' r = rs r)

def transl_sel_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (ty : typ) (cond : condition)
    (args : List Mreg) (rd r2 : Ireg) (k c : AsmCode) (rs : regset) (m : Mem),
    transl_sel cond args rd r2 k = .OK c →
    ∃ rs', exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs m k rs' m ∧
      Val.lessdef
        (Val.select (eval_condition cond (args.map (fun r => rs (preg_of r))) m)
          (rs (.IR rd)) (rs (.IR r2)) ty) (rs' (.IR rd)) ∧
      (∀ r, data_preg r = true → r ≠ .IR rd → rs' r = rs r)

def transl_op_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (op : operation) (args : List Mreg)
    (res : Mreg) (k c : AsmCode) (rs : regset) (m : Mem) (v : Val),
    transl_op op args res k = .OK c →
    eval_operation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge (rs (.IR .RSP)) op
      (args.map (fun r => rs (preg_of r))) m = some v →
    ∃ rs', exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs m k rs' m ∧
      Val.lessdef v (rs' (preg_of res)) ∧
      (∀ r, data_preg r = true → r ≠ preg_of res →
        preg_notin r (CompCert4Lean.X86.Machregs.destroyed_by_op op) → rs' r = rs r)

def transl_load_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (chunk : memory_chunk)
    (addr : addressing) (args : List Mreg) (dest : Mreg) (k c : AsmCode)
    (rs : regset) (m : Mem) (a v : Val),
    transl_load chunk addr args dest k = .OK c →
    eval_addressing ge (rs (.IR .RSP)) addr
      (args.map (fun r => rs (preg_of r))) = some a →
    Mem.loadv chunk m a = some v →
    ∃ rs', exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs m k rs' m ∧
      rs' (preg_of dest) = v ∧
      (∀ r, data_preg r = true → r ≠ preg_of dest → rs' r = rs r)

def transl_store_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (chunk : memory_chunk)
    (addr : addressing) (args : List Mreg) (src : Mreg) (k c : AsmCode)
    (rs : regset) (m : Mem) (a : Val) (m' : Mem),
    transl_store chunk addr args src k = .OK c →
    eval_addressing ge (rs (.IR .RSP)) addr
      (args.map (fun r => rs (preg_of r))) = some a →
    Mem.storev chunk m a (rs (preg_of src)) = some m' →
    ∃ rs', exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs m k rs' m' ∧
      (∀ r, data_preg r = true →
        preg_notin r (CompCert4Lean.X86.Machregs.destroyed_by_store chunk addr) →
        rs' r = rs r)

def int64_sub_overflowStatement : Prop :=
  let sub_overflow : Int64 → Int64 → Int64 → Int64 :=
    fun x y bin =>
      let s := ZArith.BinInt.Z.sub
        (ZArith.BinInt.Z.sub
          (CompCert4Lean.Lib.Integers.Int64.signed x)
          (CompCert4Lean.Lib.Integers.Int64.signed y))
        (CompCert4Lean.Lib.Integers.Int64.signed bin)
      match CompCert4Lean.Lib.Coqlib.zle
          CompCert4Lean.Lib.Integers.Int64.min_signed s,
        CompCert4Lean.Lib.Coqlib.zle s
          CompCert4Lean.Lib.Integers.Int64.max_signed with
      | .left _, .left _ => CompCert4Lean.Lib.Integers.Int64.zero
      | _, _ => CompCert4Lean.Lib.Integers.Int64.one
  let negative : Int64 → Int64 := fun x =>
    if CompCert4Lean.Lib.Integers.Int64.lt x
        CompCert4Lean.Lib.Integers.Int64.zero then
      CompCert4Lean.Lib.Integers.Int64.one
    else
      CompCert4Lean.Lib.Integers.Int64.zero
  ∀ (x y : Int64),
    CompCert4Lean.Lib.Integers.Int.xor
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned
          (sub_overflow x y CompCert4Lean.Lib.Integers.Int64.zero)))
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned
          (negative (CompCert4Lean.Lib.Integers.Int64.sub x y)))) =
      (if CompCert4Lean.Lib.Integers.Int64.lt x y then
        CompCert4Lean.Lib.Integers.Int.one
       else CompCert4Lean.Lib.Integers.Int.zero)

end CompCert4Lean.X86.Asmgenproof1
