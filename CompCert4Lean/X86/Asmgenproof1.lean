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
  ∀ (v1 v2 : Val),
    Val.divu v1 v2 ≠ none ∨ Val.modu v1 v2 ≠ none →
    ∃ (n d q r : Int32),
      v1 = .Vint n ∧ v2 = .Vint d ∧
      CompCert4Lean.Lib.Integers.Int.divmodu2
        CompCert4Lean.Lib.Integers.Int.zero n d = some (q, r) ∧
      Val.divu v1 v2 = some (.Vint q) ∧ Val.modu v1 v2 = some (.Vint r)

def divs_mods_existsStatement : Prop :=
  ∀ (v1 v2 : Val),
    Val.divs v1 v2 ≠ none ∨ Val.mods v1 v2 ≠ none →
    ∃ (nh nl d q r : Int32),
      Val.shr v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr
        (ZArith.BinInt.Z.of_nat 31))) = .Vint nh ∧
      v1 = .Vint nl ∧ v2 = .Vint d ∧
      CompCert4Lean.Lib.Integers.Int.divmods2 nh nl d = some (q, r) ∧
      Val.divs v1 v2 = some (.Vint q) ∧ Val.mods v1 v2 = some (.Vint r)

def divlu_modlu_existsStatement : Prop :=
  ∀ (v1 v2 : Val),
    Val.divlu v1 v2 ≠ none ∨ Val.modlu v1 v2 ≠ none →
    ∃ (n d q r : Int64),
      v1 = .Vlong n ∧ v2 = .Vlong d ∧
      CompCert4Lean.Lib.Integers.Int64.divmodu2
        CompCert4Lean.Lib.Integers.Int64.zero n d = some (q, r) ∧
      Val.divlu v1 v2 = some (.Vlong q) ∧ Val.modlu v1 v2 = some (.Vlong r)

def divls_modls_existsStatement : Prop :=
  ∀ (v1 v2 : Val),
    Val.divls v1 v2 ≠ none ∨ Val.modls v1 v2 ≠ none →
    ∃ (nh nl d q r : Int64),
      Val.shrl v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr
        (ZArith.BinInt.Z.of_nat 63))) = .Vlong nh ∧
      v1 = .Vlong nl ∧ v2 = .Vlong d ∧
      CompCert4Lean.Lib.Integers.Int64.divmods2 nh nl d = some (q, r) ∧
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
  ∀ (x y : Int64),
    CompCert4Lean.Lib.Integers.Int.xor
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned
          (CompCert4Lean.Lib.Integers.Int64.sub_overflow
            x y CompCert4Lean.Lib.Integers.Int64.zero)))
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned
          (CompCert4Lean.Lib.Integers.Int64.negative
            (CompCert4Lean.Lib.Integers.Int64.sub x y)))) =
      (if CompCert4Lean.Lib.Integers.Int64.lt x y then
        CompCert4Lean.Lib.Integers.Int.one
       else CompCert4Lean.Lib.Integers.Int.zero)

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

theorem nextinstr_nf_inv : nextinstr_nf_invStatement := by
  intro r rs h
  unfold CompCert4Lean.X86.Asm.nextinstr_nf
  rw [CompCert4Lean.Backend.Asmgenproof0.nextinstr_inv]
  · apply CompCert4Lean.Backend.Asmgenproof0.undef_regs_other
    intro r' hr' hne
    cases r <;> cases r' <;> simp_all
  · cases r <;> simp_all

theorem nextinstr_nf_inv1 : nextinstr_nf_inv1Statement := by
  intro r rs hr
  apply nextinstr_nf_inv r rs
  cases r <;> simp_all [CompCert4Lean.X86.Asm.data_preg]

theorem agree_nextinstr_nf : agree_nextinstr_nfStatement := by
  intro ms sp rs h
  constructor
  · have hp : CompCert4Lean.X86.Asm.nextinstr_nf rs (.IR .RSP) = rs (.IR .RSP) :=
      nextinstr_nf_inv (.IR .RSP) rs (by simp)
    exact hp.trans h.agree_sp
  · exact h.agree_sp_def
  · intro mr
    have hm := h.agree_mregs mr
    rw [nextinstr_nf_inv1 (CompCert4Lean.X86.Asm.preg_of mr) rs
      (CompCert4Lean.Backend.Asmgenproof0.preg_of_data mr)]
    exact hm

theorem mk_mov_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    mk_mov_correctStatement := by
  intro ge fn rd rs k c rs1 m h
  cases rd <;> cases rs <;> simp [CompCert4Lean.X86.Asmgen.mk_mov] at h
  all_goals try { cases h }
  all_goals injection h with hc
  all_goals subst c
  case IR.IR rd rs =>
    refine ⟨CompCert4Lean.X86.Asm.nextinstr
      (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd)
        (CompCert4Lean.X86.Asm.Pregmap.get (.IR rs) rs1) rs1), ?_, ?_, ?_⟩
    · constructor <;> rfl
    · simp [CompCert4Lean.X86.Asm.nextinstr, CompCert4Lean.X86.Asm.Pregmap.set]
      change rs1 (.IR rs) = rs1 (.IR rs)
      rfl
    · intro r hr hne
      cases r <;> simp_all [CompCert4Lean.X86.Asm.nextinstr,
        CompCert4Lean.X86.Asm.Pregmap.set, CompCert4Lean.X86.Asm.Pregmap.get,
        CompCert4Lean.X86.Asm.data_preg]
  case FR.FR rd rs =>
    refine ⟨CompCert4Lean.X86.Asm.nextinstr
      (CompCert4Lean.X86.Asm.Pregmap.set (.FR rd)
        (CompCert4Lean.X86.Asm.Pregmap.get (.FR rs) rs1) rs1), ?_, ?_, ?_⟩
    · constructor <;> rfl
    · simp [CompCert4Lean.X86.Asm.nextinstr, CompCert4Lean.X86.Asm.Pregmap.set]
      change rs1 (.FR rs) = rs1 (.FR rs)
      rfl
    · intro r hr hne
      cases r <;> simp_all [CompCert4Lean.X86.Asm.nextinstr,
        CompCert4Lean.X86.Asm.Pregmap.set, CompCert4Lean.X86.Asm.Pregmap.get,
        CompCert4Lean.X86.Asm.data_preg]

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1
theorem divu_modu_exists : divu_modu_existsStatement := by
  intro v1 v2 h
  cases v1 <;> cases v2 <;>
    simp [CompCert4Lean.Common.Values.Val.divu,
      CompCert4Lean.Common.Values.Val.modu] at h ⊢
  case Vint.Vint n d =>
    have hd : d ≠ CompCert4Lean.Lib.Integers.Int.zero := by
      intro hd
      subst d
      simp [CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq] at h
    refine ⟨CompCert4Lean.Lib.Integers.Int.divu n d,
      CompCert4Lean.Lib.Integers.Int.modu n d, ?_, ⟨h, rfl⟩, h, rfl⟩
    have hn0 : (0 : Int) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int.unsigned n) := by
      have hn := n.intrange.1
      change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval at hn
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval
      omega
    have hnmax :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int.unsigned n) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            CompCert4Lean.Lib.Integers.Int.max_unsigned := by
      have hn := n.intrange.2
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int.modulus at hn
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int.modulus - 1
      omega
    have hd0 : (0 : Int) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int.unsigned d) := by
      have hd' := d.intrange.1
      change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d.intval at hd'
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d.intval
      omega
    have hdpos : (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int.unsigned d) := by
      have hdne :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int.unsigned d) ≠ 0 := by
        intro hzero
        apply hd
        apply CompCert4Lean.Lib.Integers.WordCore.ext
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d.intval = 0 at hzero
        have hz0 :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                CompCert4Lean.Lib.Integers.Int.zero.intval = 0 := by
          rfl
        exact hzero.trans hz0.symm
      omega
    have hqint :
        Int.ediv
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int.unsigned n))
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int.unsigned d)) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            CompCert4Lean.Lib.Integers.Int.max_unsigned := by
      apply Int.ediv_le_of_le_mul hdpos
      have hnd := Int.mul_le_mul_of_nonneg_left
        (show (1 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int.unsigned d) by omega) hn0
      have hmaxd := Int.mul_le_mul_of_nonneg_right hnmax (Int.le_of_lt hdpos)
      have hnd' :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int.unsigned n) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int.unsigned n) *
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Lib.Integers.Int.unsigned d) := by
        simpa using hnd
      exact Int.le_trans hnd' hmaxd
    have hqz :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
                (CompCert4Lean.Lib.Integers.Int.unsigned
                  CompCert4Lean.Lib.Integers.Int.zero)
                CompCert4Lean.Lib.Integers.Int.modulus)
              (CompCert4Lean.Lib.Integers.Int.unsigned n))
            (CompCert4Lean.Lib.Integers.Int.unsigned d)).1
          CompCert4Lean.Lib.Integers.Int.max_unsigned := by
      let a : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
            (CompCert4Lean.Lib.Integers.Int.unsigned
              CompCert4Lean.Lib.Integers.Int.zero)
            CompCert4Lean.Lib.Integers.Int.modulus)
          (CompCert4Lean.Lib.Integers.Int.unsigned n)
      let b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
        CompCert4Lean.Lib.Integers.Int.unsigned d
      let q : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl a b).1
      let r : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl a b).2
      have hzzero :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int.unsigned
                CompCert4Lean.Lib.Integers.Int.zero) = 0 := by
        rfl
      have hz0 :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 = 0 := by
        rfl
      have ha0 : (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a := by
        dsimp [a]
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hzzero]
        omega
      have hamax :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Lib.Integers.Int.max_unsigned := by
        dsimp [a]
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hzzero]
        omega
      have hbpos : (0 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
        dsimp [b]
        exact hdpos
      have hrem :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo_range
          a b (by exact hbpos)
      have hr0 : (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r := by
        simpa [r,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, hz0] using hrem.1
      have hrlt :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
        simpa [r,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt] using hrem.2
      have heq :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_mod_eq_full
          a b
      have heq' :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a =
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q +
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r := by
        have heq0 :
            a =
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
                  b (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div a b))
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo a b) := by
          simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl] using heq
        have hi := congrArg
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ heq0
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul] at hi
        repeat rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hi
        simpa [q, r,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl] using hi
      have hq0 : (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q := by
        by_cases hq : (0 : Int) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q
        · exact hq
        · exfalso
          have hqneg' :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤ -1 := by omega
          have hprod :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤
                -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
            have hh := Int.mul_le_mul_of_nonneg_left hqneg' (Int.le_of_lt hbpos)
            simpa using hh
          have hsum :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q +
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r < 0 := by
            omega
          omega
      have hqmul :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a := by
        omega
      have hb1 : (1 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by omega
      have hqle_mul :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q := by
        have hh := Int.mul_le_mul_of_nonneg_left hb1 hq0
        simpa [Int.mul_comm] using hh
      have hqle :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Lib.Integers.Int.max_unsigned :=
        Int.le_trans hqle_mul (Int.le_trans hqmul hamax)
      simpa [a, b, q,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le] using hqle
    have hzle :
        CompCert4Lean.Lib.Coqlib.zle
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
                  (CompCert4Lean.Lib.Integers.Int.unsigned
                    CompCert4Lean.Lib.Integers.Int.zero)
                  CompCert4Lean.Lib.Integers.Int.modulus)
                (CompCert4Lean.Lib.Integers.Int.unsigned n))
              (CompCert4Lean.Lib.Integers.Int.unsigned d)).1
            CompCert4Lean.Lib.Integers.Int.max_unsigned =
          .left hqz := by
      cases he : CompCert4Lean.Lib.Coqlib.zle
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
                (CompCert4Lean.Lib.Integers.Int.unsigned
                  CompCert4Lean.Lib.Integers.Int.zero)
                CompCert4Lean.Lib.Integers.Int.modulus)
              (CompCert4Lean.Lib.Integers.Int.unsigned n))
            (CompCert4Lean.Lib.Integers.Int.unsigned d)).1
          CompCert4Lean.Lib.Integers.Int.max_unsigned with
      | left hp => rfl
      | right hp =>
          exact (Int.not_lt_of_ge hqz hp).elim
    have hsumz :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
              (CompCert4Lean.Lib.Integers.Int.unsigned
                CompCert4Lean.Lib.Integers.Int.zero)
              CompCert4Lean.Lib.Integers.Int.modulus)
            (CompCert4Lean.Lib.Integers.Int.unsigned n) =
          CompCert4Lean.Lib.Integers.Int.unsigned n := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hzero_u :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int.unsigned
                CompCert4Lean.Lib.Integers.Int.zero) = 0 := by rfl
      rw [hzero_u]
      omega
    unfold CompCert4Lean.Lib.Integers.Int.divmodu2
    simp [CompCert4Lean.Lib.Integers.Int.eq_dec, hd, hqz]
    rw [hzle]
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl,
      CompCert4Lean.Lib.Integers.Int.divu,
      CompCert4Lean.Lib.Integers.Int.modu, hsumz]
    constructor <;> rfl

end CompCert4Lean.X86.Asmgenproof1
namespace CompCert4Lean.X86.Asmgenproof1

theorem divlu_modlu_exists : divlu_modlu_existsStatement := by
  intro v1 v2 h
  cases v1 <;> cases v2 <;>
    simp [CompCert4Lean.Common.Values.Val.divlu,
      CompCert4Lean.Common.Values.Val.modlu] at h ⊢
  case Vlong.Vlong n d =>
    have hd : d ≠ CompCert4Lean.Lib.Integers.Int64.zero := by
      intro hd
      subst d
      simp [CompCert4Lean.Lib.Integers.Int64.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq] at h
    refine ⟨CompCert4Lean.Lib.Integers.Int64.divu n d,
      CompCert4Lean.Lib.Integers.Int64.modu n d, ?_, ⟨h, rfl⟩, h, rfl⟩
    have hn0 : (0 : Int) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned n) := by
      have hn := n.intrange.1
      change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval at hn
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval
      omega
    have hnmax :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int64.unsigned n) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
      have hn := n.intrange.2
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int64.modulus at hn
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int64.modulus - 1
      omega
    have hd0 : (0 : Int) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned d) := by
      have hd' := d.intrange.1
      change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d.intval at hd'
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d.intval
      omega
    have hdpos : (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned d) := by
      have hdne :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int64.unsigned d) ≠ 0 := by
        intro hzero
        apply hd
        apply CompCert4Lean.Lib.Integers.WordCore.ext
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d.intval = 0 at hzero
        have hz0 :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                CompCert4Lean.Lib.Integers.Int64.zero.intval = 0 := by
          rfl
        exact hzero.trans hz0.symm
      omega
    have hqint :
        Int.ediv
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int64.unsigned n))
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int64.unsigned d)) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
      apply Int.ediv_le_of_le_mul hdpos
      have hnd := Int.mul_le_mul_of_nonneg_left
        (show (1 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int64.unsigned d) by omega) hn0
      have hmaxd := Int.mul_le_mul_of_nonneg_right hnmax (Int.le_of_lt hdpos)
      have hnd' :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int64.unsigned n) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int64.unsigned n) *
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Lib.Integers.Int64.unsigned d) := by
        simpa using hnd
      exact Int.le_trans hnd' hmaxd
    have hqz :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
                (CompCert4Lean.Lib.Integers.Int64.unsigned
                  CompCert4Lean.Lib.Integers.Int64.zero)
                CompCert4Lean.Lib.Integers.Int64.modulus)
              (CompCert4Lean.Lib.Integers.Int64.unsigned n))
            (CompCert4Lean.Lib.Integers.Int64.unsigned d)).1
          CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
      let a : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
            (CompCert4Lean.Lib.Integers.Int64.unsigned
              CompCert4Lean.Lib.Integers.Int64.zero)
            CompCert4Lean.Lib.Integers.Int64.modulus)
          (CompCert4Lean.Lib.Integers.Int64.unsigned n)
      let b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
        CompCert4Lean.Lib.Integers.Int64.unsigned d
      let q : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl a b).1
      let r : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl a b).2
      have hzzero :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int64.unsigned
                CompCert4Lean.Lib.Integers.Int64.zero) = 0 := by
        rfl
      have hz0 :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 = 0 := by
        rfl
      have ha0 : (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a := by
        dsimp [a]
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hzzero]
        omega
      have hamax :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
        dsimp [a]
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hzzero]
        omega
      have hbpos : (0 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
        dsimp [b]
        exact hdpos
      have hrem :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo_range
          a b (by exact hbpos)
      have hr0 : (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r := by
        simpa [r,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, hz0] using hrem.1
      have hrlt :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
        simpa [r,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt] using hrem.2
      have heq :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_mod_eq_full
          a b
      have heq' :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a =
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q +
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r := by
        have heq0 :
            a =
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
                  b (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div a b))
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo a b) := by
          simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl] using heq
        have hi := congrArg
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ heq0
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul] at hi
        repeat rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hi
        simpa [q, r,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl] using hi
      have hq0 : (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q := by
        by_cases hq : (0 : Int) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q
        · exact hq
        · exfalso
          have hqneg' :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤ -1 := by omega
          have hprod :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤
                -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
            have hh := Int.mul_le_mul_of_nonneg_left hqneg' (Int.le_of_lt hbpos)
            simpa using hh
          have hsum :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q +
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r < 0 := by
            omega
          omega
      have hqmul :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a := by
        omega
      have hb1 : (1 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by omega
      have hqle_mul :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q := by
        have hh := Int.mul_le_mul_of_nonneg_left hb1 hq0
        simpa [Int.mul_comm] using hh
      have hqle :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Lib.Integers.Int64.max_unsigned :=
        Int.le_trans hqle_mul (Int.le_trans hqmul hamax)
      simpa [a, b, q,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le] using hqle
    have hzle :
        CompCert4Lean.Lib.Coqlib.zle
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
                  (CompCert4Lean.Lib.Integers.Int64.unsigned
                    CompCert4Lean.Lib.Integers.Int64.zero)
                  CompCert4Lean.Lib.Integers.Int64.modulus)
                (CompCert4Lean.Lib.Integers.Int64.unsigned n))
              (CompCert4Lean.Lib.Integers.Int64.unsigned d)).1
            CompCert4Lean.Lib.Integers.Int64.max_unsigned =
          .left hqz := by
      cases he : CompCert4Lean.Lib.Coqlib.zle
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
                (CompCert4Lean.Lib.Integers.Int64.unsigned
                  CompCert4Lean.Lib.Integers.Int64.zero)
                CompCert4Lean.Lib.Integers.Int64.modulus)
              (CompCert4Lean.Lib.Integers.Int64.unsigned n))
            (CompCert4Lean.Lib.Integers.Int64.unsigned d)).1
          CompCert4Lean.Lib.Integers.Int64.max_unsigned with
      | left hp => rfl
      | right hp =>
          exact (Int.not_lt_of_ge hqz hp).elim
    have hsumz :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
              (CompCert4Lean.Lib.Integers.Int64.unsigned
                CompCert4Lean.Lib.Integers.Int64.zero)
              CompCert4Lean.Lib.Integers.Int64.modulus)
            (CompCert4Lean.Lib.Integers.Int64.unsigned n) =
          CompCert4Lean.Lib.Integers.Int64.unsigned n := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hzero_u :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int64.unsigned
                CompCert4Lean.Lib.Integers.Int64.zero) = 0 := by rfl
      rw [hzero_u]
      omega
    unfold CompCert4Lean.Lib.Integers.Int64.divmodu2
    simp [CompCert4Lean.Lib.Integers.Int64.eq_dec, hd, hqz]
    rw [hzle]
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl,
      CompCert4Lean.Lib.Integers.Int64.divu,
      CompCert4Lean.Lib.Integers.Int64.modu, hsumz]
    constructor <;> rfl
end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.X86.Asm

theorem mk_intconv_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    mk_intconv_correctStatement := by
  intro ge fn mk sem rd rs k c rs1 m hmk hstep
  unfold CompCert4Lean.X86.Asmgen.mk_intconv at hmk
  split at hmk
  · injection hmk with hc
    subst c
    refine ⟨CompCert4Lean.X86.Asm.nextinstr
      (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd) (sem (rs1 (.IR rs))) rs1), ?_, ?_, ?_⟩
    · apply exec_straight_one
      · exact hstep fn rd rs rs1 m
      · rfl
    · simp [CompCert4Lean.X86.Asm.nextinstr, CompCert4Lean.X86.Asm.Pregmap.set]
    · intro r hr hrd hrax
      cases r <;> simp_all [CompCert4Lean.X86.Asm.nextinstr,
        CompCert4Lean.X86.Asm.Pregmap.set, CompCert4Lean.X86.Asm.Pregmap.get,
        CompCert4Lean.X86.Asm.data_preg]
  · injection hmk with hc
    subst c
    let rs_mid := CompCert4Lean.X86.Asm.nextinstr
      (CompCert4Lean.X86.Asm.Pregmap.set (.IR .RAX) (rs1 (.IR rs)) rs1)
    let rs_final := CompCert4Lean.X86.Asm.nextinstr
      (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd) (sem (rs_mid (.IR .RAX))) rs_mid)
    refine ⟨rs_final, ?_, ?_, ?_⟩
    · apply exec_straight_step (rs2 := rs_mid) (m2 := m)
      · rfl
      · rfl
      · apply exec_straight_one
        · exact hstep fn rd .RAX rs_mid m
        · rfl
    · dsimp [rs_final, rs_mid]
      simp [CompCert4Lean.X86.Asm.nextinstr, CompCert4Lean.X86.Asm.Pregmap.set]
    · intro r hr hrd hrax
      dsimp [rs_final, rs_mid]
      cases r <;> simp_all [CompCert4Lean.X86.Asm.nextinstr,
        CompCert4Lean.X86.Asm.Pregmap.set, CompCert4Lean.X86.Asm.Pregmap.get,
        CompCert4Lean.X86.Asm.data_preg]

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

theorem addressing_mentions_correct : addressing_mentions_correctStatement := by
  intro ge a r rs1 rs2 hag hm
  cases a with
  | Addrmode base ofs c =>
    cases base with
    | none =>
      cases ofs with
      | none => rfl
      | some p =>
        rcases p with ⟨r', sc⟩
        simp [CompCert4Lean.X86.Asmgen.addressing_mentions] at hm
        have hne : r' ≠ r := by
          intro heq
          subst r'
          change decide (r = r) = false at hm
          simp at hm
        unfold CompCert4Lean.X86.Asm.eval_addrmode32
        simp only [CompCert4Lean.X86.Asm.Pregmap.get]
        rw [hag r' hne]
    | some b =>
      cases ofs with
      | none =>
        simp [CompCert4Lean.X86.Asmgen.addressing_mentions] at hm
        have hne : b ≠ r := by
          intro heq
          subst b
          change decide (r = r) = false at hm
          simp at hm
        unfold CompCert4Lean.X86.Asm.eval_addrmode32
        simp only [CompCert4Lean.X86.Asm.Pregmap.get]
        rw [hag b hne]
      | some p =>
        rcases p with ⟨r', sc⟩
        simp [CompCert4Lean.X86.Asmgen.addressing_mentions] at hm
        have hbne : b ≠ r := by
          intro heq
          subst b
          have hfalse := hm.1
          change decide (r = r) = false at hfalse
          simp at hfalse
        have hone : r' ≠ r := by
          intro heq
          subst r'
          have hfalse := hm.2
          change decide (r = r) = false at hfalse
          simp at hfalse
        unfold CompCert4Lean.X86.Asm.eval_addrmode32
        simp only [CompCert4Lean.X86.Asm.Pregmap.get]
        rw [hag b hbne, hag r' hone]

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.AST
open CompCert4Lean.X86.Asm

theorem mk_storebyte_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    mk_storebyte_correctStatement := by
  intro ge fn addr r k c rs1 m1 m2 hmk hstore
  unfold CompCert4Lean.X86.Asmgen.mk_storebyte at hmk
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hmk
  injection hmk with hc
  subst c
  refine ⟨CompCert4Lean.X86.Asm.nextinstr_nf rs1, ?_, ?_⟩
  · apply exec_straight_one
    · change (match CompCert4Lean.Common.Memory.Mem.storev Mint8unsigned m1
          (eval_addrmode ge addr rs1)
          (rs1 (.IR r)) with
        | some m' => CompCert4Lean.X86.Asm.Next
            (nextinstr_nf (undef_regs [] rs1)) m'
        | none => CompCert4Lean.X86.Asm.Stuck) =
          CompCert4Lean.X86.Asm.Next (nextinstr_nf rs1) m2
      simp only [CompCert4Lean.X86.Asm.undef_regs]
      rw [hstore]
    · rfl
  · intro r' hr' hnotin
    exact nextinstr_nf_inv1 r' rs1 hr'

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open Lean Elab Tactic Meta

private def asmgenproof1PrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem asmgenproof1WordValRepr (bits : Nat) (i : Int) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let iF := (lctx.findFromUserName? `i).get!
    let e ← mkAppM
      (asmgenproof1PrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr")
      #[mkFVar bitsF.fvarId, mkFVar iF.fvarId]
    closeMainGoal Name.anonymous e

private theorem asmgenproof1PtrofsReprUnsigned (x : Ptrofs) :
    CompCert4Lean.Lib.Integers.Ptrofs.repr
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) = x := by
  have hx0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z0
      (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  have hxlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      (Int.ofNat (2 ^ CompCert4Lean.Lib.Integers.Ptrofs.wordsize)) := by
    have h := x.intrange.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Ptrofs.modulus at h
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      (Int.ofNat (2 ^ CompCert4Lean.Lib.Integers.Ptrofs.wordsize)) at h
    exact h
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Ptrofs.wordsize x.intval).val = x.val
  have hz :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval) = x.intval :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ _
  rw [← hz, asmgenproof1WordValRepr]
  have hmod :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval %
          ((2 ^ CompCert4Lean.Lib.Integers.Ptrofs.wordsize : Nat) : Int) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval :=
    Int.emod_eq_of_lt (show 0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval by exact hx0) hxlt
  rw [hmod]
  have hvalz :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat x.intval) =
        x.intval :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id x.intval (by
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
      exact hx0)
  have hint :
      Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat x.intval) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval := by
    have h := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hvalz
    simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using h
  have hnat :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat x.intval =
        Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval) := by
    rw [← Int.toNat_of_nonneg (show 0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval by exact hx0)] at hint
    exact Int.ofNat.inj hint
  change Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat x.intval
  exact hnat.symm

private theorem asmgenproof1WordCoreAddVal {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.add x y).val =
      (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (asmgenproof1PrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem asmgenproof1WordCoreZeroVal (bits : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.zero bits).val = 0 := by
  unfold CompCert4Lean.Lib.Integers.WordCore.zero
  change (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (0 : Int))).val = 0
  simpa using (asmgenproof1WordValRepr bits (0 : Int))

private theorem asmgenproof1WordCoreValLt
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) : x.val < 2 ^ bits := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (asmgenproof1PrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e

private theorem asmgenproof1Int64AddZero (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.add
        CompCert4Lean.Lib.Integers.Int64.zero x = x := by
  change CompCert4Lean.Lib.Integers.WordCore.add
    (CompCert4Lean.Lib.Integers.WordCore.zero
      CompCert4Lean.Lib.Integers.Int64.wordsize) x = x
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [asmgenproof1WordCoreAddVal, asmgenproof1WordCoreZeroVal]
  simpa only [Nat.zero_add] using
    (Nat.mod_eq_of_lt (asmgenproof1WordCoreValLt x))

theorem eval_addrmode_indexed : eval_addrmode_indexedStatement := by
  intro ge base ofs rs h
  unfold CompCert4Lean.X86.Asm.eval_addrmode
  unfold CompCert4Lean.X86.Asm.eval_addrmode64
  cases hv : rs (.IR base) with
  | Vptr b o =>
      have hconv :
          CompCert4Lean.Lib.Integers.Ptrofs.of_int64
              (CompCert4Lean.Lib.Integers.Int64.repr
                (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)) = ofs := by
        have hrepr := asmgenproof1PtrofsReprUnsigned ofs
        have hu0 := congrArg CompCert4Lean.Lib.Integers.WordCore.unsigned hrepr
        have hu :
            CompCert4Lean.Lib.Integers.Int64.unsigned
                (CompCert4Lean.Lib.Integers.Int64.repr
                  (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)) =
              CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs := by
          simpa [CompCert4Lean.Lib.Integers.Int64.unsigned,
            CompCert4Lean.Lib.Integers.Int64.repr,
            CompCert4Lean.Lib.Integers.Int64.wordsize,
            CompCert4Lean.Lib.Integers.Ptrofs.repr,
            CompCert4Lean.Lib.Integers.Ptrofs.unsigned,
            CompCert4Lean.Lib.Integers.Ptrofs.wordsize,
            CompCert4Lean.Lib.Integers.Wordsize_Ptrofs.wordsize,
            CompCert4Lean.X86_64.Archi.ptr64] using hu0
        unfold CompCert4Lean.Lib.Integers.Ptrofs.of_int64
        rw [hu]
        exact hrepr
      simp [CompCert4Lean.X86.Asm.Pregmap.get, CompCert4Lean.X86_64.Archi.ptr64, hv,
        CompCert4Lean.Common.Values.Val.offset_ptr,
        CompCert4Lean.Common.Values.Val.addl,
        asmgenproof1Int64AddZero, hconv]
  | Vundef => simp [hv] at h
  | Vint n => simp [hv] at h
  | Vlong n => simp [hv] at h
  | Vfloat n => simp [hv] at h
  | Vsingle n => simp [hv] at h

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

private def asmgenproof1Destroyed
    (ty : CompCert4Lean.Common.AST.typ)
    (p : CompCert4Lean.X86.Asm.preg) : List CompCert4Lean.X86.Asm.preg :=
  match ty, p with
  | .Tsingle, .ST0 | .Tfloat, .ST0 => [.ST0]
  | _, _ => []

theorem storeind_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    storeind_correctStatement := by
  intro ge fn base ofs ty src k rs c m m' hmk hstore
  let addr : CompCert4Lean.X86.Asm.addrmode :=
    .Addrmode (some base) none
      (Sum.inl (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs))
  have haddr :
      CompCert4Lean.X86.Asm.eval_addrmode ge addr rs =
        CompCert4Lean.Common.Values.Val.offset_ptr
          (rs (.IR base)) ofs := by
    apply CompCert4Lean.X86.Asmgenproof1.eval_addrmode_indexed
    cases h : rs (.IR base) <;>
      simp_all [CompCert4Lean.Common.Values.Val.offset_ptr,
        CompCert4Lean.Common.Memory.Mem.storev]
  have hstore' :
      CompCert4Lean.Common.Memory.Mem.storev
          (CompCert4Lean.Common.AST.chunk_of_type ty) m
          (CompCert4Lean.X86.Asm.eval_addrmode ge addr rs)
          (rs (CompCert4Lean.X86.Asm.preg_of src)) = some m' := by
    rw [haddr]
    exact hstore
  let destroyed : List CompCert4Lean.X86.Asm.preg :=
    asmgenproof1Destroyed ty (CompCert4Lean.X86.Asm.preg_of src)
  unfold CompCert4Lean.X86.Asmgen.storeind at hmk
  cases ty <;> cases src <;>
    simp [CompCert4Lean.X86.Asmgen.storeind,
      CompCert4Lean.X86.Asm.preg_of,
      CompCert4Lean.X86_64.Archi.ptr64] at hmk
  all_goals try { contradiction }
  all_goals injection hmk with hc; subst c
  all_goals
    refine ⟨CompCert4Lean.X86.Asm.nextinstr_nf
      (CompCert4Lean.X86.Asm.undef_regs
        destroyed rs), ?_, ?_⟩
    · apply CompCert4Lean.Backend.Asmgenproof0.exec_straight_one
      · change (match CompCert4Lean.Common.Memory.Mem.storev _ m
          (CompCert4Lean.X86.Asm.eval_addrmode ge addr rs) _ with
        | some m' => CompCert4Lean.X86.Asm.Next
            (CompCert4Lean.X86.Asm.nextinstr_nf
              (CompCert4Lean.X86.Asm.undef_regs destroyed rs)) m'
        | none => CompCert4Lean.X86.Asm.Stuck) =
          CompCert4Lean.X86.Asm.Next
            (CompCert4Lean.X86.Asm.nextinstr_nf
              (CompCert4Lean.X86.Asm.undef_regs destroyed rs)) m'
        simp only [CompCert4Lean.X86.Asm.Pregmap.get]
        dsimp [addr, destroyed, asmgenproof1Destroyed,
          CompCert4Lean.X86.Asm.preg_of,
          CompCert4Lean.Common.AST.chunk_of_type] at hstore' ⊢
        try simp [CompCert4Lean.X86_64.Archi.ptr64] at ⊢
        rw [hstore']
      · rfl
    · intro r hr hnotin
      rw [nextinstr_nf_inv1 r _ hr]
      apply CompCert4Lean.Backend.Asmgenproof0.undef_regs_other
      intro r' hr'
      simp_all [destroyed, asmgenproof1Destroyed,
        CompCert4Lean.X86.Machregs.destroyed_by_setstack,
        CompCert4Lean.Backend.Asmgenproof0.preg_notin,
        CompCert4Lean.X86.Asm.preg_of]

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

theorem compare_ints_spec : compare_ints_specStatement := by
  intro rs v1 v2 m
  dsimp
  unfold CompCert4Lean.X86.Asm.nextinstr
  unfold CompCert4Lean.X86.Asm.compare_ints
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  · intro r hr
    cases r <;>
      simp [CompCert4Lean.X86.Asm.Pregmap.set,
        CompCert4Lean.X86.Asm.data_preg] at hr ⊢

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

theorem compare_longs_spec : compare_longs_specStatement := by
  intro rs v1 v2 m
  dsimp
  unfold CompCert4Lean.X86.Asm.nextinstr
  unfold CompCert4Lean.X86.Asm.compare_longs
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  · intro r hr
    cases r <;>
      simp [CompCert4Lean.X86.Asm.Pregmap.set,
        CompCert4Lean.X86.Asm.data_preg] at hr ⊢

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

theorem compare_floats_spec : compare_floats_specStatement := by
  intro rs n1 n2
  dsimp
  unfold CompCert4Lean.X86.Asm.nextinstr
  unfold CompCert4Lean.X86.Asm.compare_floats
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  · intro r hr
    cases r <;>
      simp [CompCert4Lean.X86.Asm.Pregmap.set,
        CompCert4Lean.X86.Asm.data_preg] at hr ⊢

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

theorem compare_floats32_spec : compare_floats32_specStatement := by
  intro rs n1 n2
  dsimp
  unfold CompCert4Lean.X86.Asm.nextinstr
  unfold CompCert4Lean.X86.Asm.compare_floats32
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  constructor
  · simp [CompCert4Lean.X86.Asm.Pregmap.set]
  · intro r hr
    cases r <;>
      simp [CompCert4Lean.X86.Asm.Pregmap.set,
        CompCert4Lean.X86.Asm.data_preg] at hr ⊢

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.X86.Asmgen
open CompCert4Lean.X86.Asm
open Lean Elab Tactic Meta

private def asmgenproof1AsmPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "X86") "Asm"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

theorem testcond_for_neg_float_comparison_correct :
    testcond_for_neg_float_comparison_correctStatement := by
  intro c n1 n2 rs
  have h := compare_floats_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)
  rcases h with ⟨A, B, C, D⟩
  have hof (b : Bool) :
      (match CompCert4Lean.Common.Values.Val.of_bool b with
       | .Vint v => some v
       | _ => none) =
        some (if b then CompCert4Lean.Lib.Integers.Int.one
          else CompCert4Lean.Lib.Integers.Int.zero) := by
    cases b <;> rfl
  have honezero :
      CompCert4Lean.Lib.Integers.Int.one.intval ≠
        CompCert4Lean.Lib.Integers.Int.zero.intval := by
    decide
  cases c <;> simp only [swap_floats, testcond_for_condition] at A B C ⊢
  all_goals
    simp only [eval_extcond, eval_testcond]
    run_tac
      let g ← getMainGoal
      let t ← g.getType
      let flagName := asmgenproof1AsmPrivateName "CompCert4Lean.X86.Asm.flagValue"
      let t ← Lean.Meta.transform t (post := fun e => do
        if e.isAppOf flagName then
          return .visit (← Lean.Meta.unfoldDefinition e)
        else
          return .continue)
      let g ← g.replaceTargetDefEq t
      Lean.Elab.Tactic.replaceMainGoal [g]
    simp only [CompCert4Lean.X86.Asm.Pregmap.get, A, B, C]
    try simp [CompCert4Lean.Common.Values.Val.of_bool,
      CompCert4Lean.Common.Values.Vtrue, CompCert4Lean.Common.Values.Vfalse]
  case Ceq =>
    unfold CompCert4Lean.Lib.Floats.Float.cmp
    unfold CompCert4Lean.Lib.Floats.Float.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cne =>
    unfold CompCert4Lean.Lib.Floats.Float.cmp
    unfold CompCert4Lean.Lib.Floats.Float.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Clt =>
    rw [← CompCert4Lean.Lib.Floats.Float.cmp_swap
      CompCert4Lean.Lib.Integers.Clt n2 n1]
    simp only [CompCert4Lean.Lib.Integers.swap_comparison]
    unfold CompCert4Lean.Lib.Floats.Float.cmp
    unfold CompCert4Lean.Lib.Floats.Float.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float.compare n2 n1 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cle =>
    rw [← CompCert4Lean.Lib.Floats.Float.cmp_swap
      CompCert4Lean.Lib.Integers.Cge n1 n2]
    simp only [CompCert4Lean.Lib.Integers.swap_comparison]
    unfold CompCert4Lean.Lib.Floats.Float.cmp
    cases hcmp : CompCert4Lean.Lib.Floats.Float.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cgt =>
    unfold CompCert4Lean.Lib.Floats.Float.cmp
    unfold CompCert4Lean.Lib.Floats.Float.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cge =>
    unfold CompCert4Lean.Lib.Floats.Float.cmp
    cases hcmp : CompCert4Lean.Lib.Floats.Float.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

theorem swap_floats_commut : swap_floats_commutStatement := by
  intro A B c f x y
  cases c <;> rfl

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

theorem compare_floats_inv : compare_floats_invStatement := by
  intro vx vy rs r hzf hcf hpf hsf hof
  unfold CompCert4Lean.X86.Asm.compare_floats
  cases vx <;> cases vy <;>
    simp [CompCert4Lean.X86.Asm.undef_regs,
      CompCert4Lean.X86.Asm.Pregmap.get, CompCert4Lean.X86.Asm.Pregmap.set,
      hzf, hcf, hpf, hsf, hof]

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.X86.Asmgen
open CompCert4Lean.X86.Asm
open Lean Elab Tactic Meta

theorem testcond_for_float32_comparison_correct :
    testcond_for_float32_comparison_correctStatement := by
  intro c n1 n2 rs
  have h := compare_floats32_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)
  rcases h with ⟨A, B, C, D⟩
  have hof (b : Bool) :
      (match CompCert4Lean.Common.Values.Val.of_bool b with
       | .Vint v => some v
       | _ => none) =
        some (if b then CompCert4Lean.Lib.Integers.Int.one
          else CompCert4Lean.Lib.Integers.Int.zero) := by
    cases b <;> rfl
  have honezero :
      CompCert4Lean.Lib.Integers.Int.one.intval ≠
        CompCert4Lean.Lib.Integers.Int.zero.intval := by
    decide
  cases c <;> simp only [swap_floats, testcond_for_condition] at A B C ⊢
  all_goals
    simp only [eval_extcond, eval_testcond]
    run_tac
      let g ← getMainGoal
      let t ← g.getType
      let flagName := asmgenproof1AsmPrivateName "CompCert4Lean.X86.Asm.flagValue"
      let t ← Lean.Meta.transform t (post := fun e => do
        if e.isAppOf flagName then
          return .visit (← Lean.Meta.unfoldDefinition e)
        else
          return .continue)
      let g ← g.replaceTargetDefEq t
      Lean.Elab.Tactic.replaceMainGoal [g]
    simp only [CompCert4Lean.X86.Asm.Pregmap.get, A, B, C]
    try simp [CompCert4Lean.Common.Values.Val.of_bool,
      CompCert4Lean.Common.Values.Vtrue, CompCert4Lean.Common.Values.Vfalse]
  case Ceq =>
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    unfold CompCert4Lean.Lib.Floats.Float32.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cne =>
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    unfold CompCert4Lean.Lib.Floats.Float32.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Clt =>
    rw [← CompCert4Lean.Lib.Floats.Float32.cmp_swap
      CompCert4Lean.Lib.Integers.Clt n2 n1]
    simp only [CompCert4Lean.Lib.Integers.swap_comparison]
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    unfold CompCert4Lean.Lib.Floats.Float32.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n2 n1 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cle =>
    rw [← CompCert4Lean.Lib.Floats.Float32.cmp_swap
      CompCert4Lean.Lib.Integers.Cge n1 n2]
    simp only [CompCert4Lean.Lib.Integers.swap_comparison]
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cgt =>
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    unfold CompCert4Lean.Lib.Floats.Float32.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cge =>
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.X86.Asmgen
open CompCert4Lean.X86.Asm
open Lean Elab Tactic Meta

theorem testcond_for_neg_float32_comparison_correct :
    testcond_for_neg_float32_comparison_correctStatement := by
  intro c n1 n2 rs
  have h := compare_floats32_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)
  rcases h with ⟨A, B, C, D⟩
  have hof (b : Bool) :
      (match CompCert4Lean.Common.Values.Val.of_bool b with
       | .Vint v => some v
       | _ => none) =
        some (if b then CompCert4Lean.Lib.Integers.Int.one
          else CompCert4Lean.Lib.Integers.Int.zero) := by
    cases b <;> rfl
  have honezero :
      CompCert4Lean.Lib.Integers.Int.one.intval ≠
        CompCert4Lean.Lib.Integers.Int.zero.intval := by
    decide
  cases c <;> simp only [swap_floats, testcond_for_condition] at A B C ⊢
  all_goals
    simp only [eval_extcond, eval_testcond]
    run_tac
      let g ← getMainGoal
      let t ← g.getType
      let flagName := asmgenproof1AsmPrivateName "CompCert4Lean.X86.Asm.flagValue"
      let t ← Lean.Meta.transform t (post := fun e => do
        if e.isAppOf flagName then
          return .visit (← Lean.Meta.unfoldDefinition e)
        else
          return .continue)
      let g ← g.replaceTargetDefEq t
      Lean.Elab.Tactic.replaceMainGoal [g]
    simp only [CompCert4Lean.X86.Asm.Pregmap.get, A, B, C]
    try simp [CompCert4Lean.Common.Values.Val.of_bool,
      CompCert4Lean.Common.Values.Vtrue, CompCert4Lean.Common.Values.Vfalse]
  case Ceq =>
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    unfold CompCert4Lean.Lib.Floats.Float32.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cne =>
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    unfold CompCert4Lean.Lib.Floats.Float32.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Clt =>
    rw [← CompCert4Lean.Lib.Floats.Float32.cmp_swap
      CompCert4Lean.Lib.Integers.Clt n2 n1]
    simp only [CompCert4Lean.Lib.Integers.swap_comparison]
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    unfold CompCert4Lean.Lib.Floats.Float32.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n2 n1 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cle =>
    rw [← CompCert4Lean.Lib.Floats.Float32.cmp_swap
      CompCert4Lean.Lib.Integers.Cge n1 n2]
    simp only [CompCert4Lean.Lib.Integers.swap_comparison]
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cgt =>
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    unfold CompCert4Lean.Lib.Floats.Float32.ordered
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Floats.ordered_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
  case Cge =>
    unfold CompCert4Lean.Lib.Floats.Float32.cmp
    cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare n1 n2 with
    | none => simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]
    | some v => cases v <;> simp [hcmp, CompCert4Lean.Lib.Floats.cmp_of_comparison,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, honezero, Ne.symm honezero]

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open Lean Elab Tactic Meta

theorem compare_floats32_inv : compare_floats32_invStatement := by
  intro vx vy rs r hzf hcf hpf hsf hof
  unfold CompCert4Lean.X86.Asm.compare_floats32
  cases vx <;> cases vy <;>
    simp [CompCert4Lean.X86.Asm.undef_regs,
      CompCert4Lean.X86.Asm.Pregmap.get, CompCert4Lean.X86.Asm.Pregmap.set,
      hzf, hcf, hpf, hsf, hof]

theorem eval_testcond_nextinstr : eval_testcond_nextinstrStatement := by
  intro c rs
  cases c <;>
    simp only [CompCert4Lean.X86.Asm.eval_testcond]
  all_goals
    run_tac
      let g ← getMainGoal
      let t ← g.getType
      let flagName := asmgenproof1AsmPrivateName "CompCert4Lean.X86.Asm.flagValue"
      let t ← Lean.Meta.transform t (post := fun e => do
        if e.isAppOf flagName then
          return .visit (← Lean.Meta.unfoldDefinition e)
        else
          return .continue)
      let g ← g.replaceTargetDefEq t
      Lean.Elab.Tactic.replaceMainGoal [g]
    simp [CompCert4Lean.X86.Asm.nextinstr,
      CompCert4Lean.X86.Asm.Pregmap.get,
      CompCert4Lean.X86.Asm.Pregmap.set]

theorem eval_testcond_set_ireg : eval_testcond_set_iregStatement := by
  intro c rs r v
  cases c <;>
    simp only [CompCert4Lean.X86.Asm.eval_testcond]
  all_goals
    run_tac
      let g ← getMainGoal
      let t ← g.getType
      let flagName := asmgenproof1AsmPrivateName "CompCert4Lean.X86.Asm.flagValue"
      let t ← Lean.Meta.transform t (post := fun e => do
        if e.isAppOf flagName then
          return .visit (← Lean.Meta.unfoldDefinition e)
        else
          return .continue)
      let g ← g.replaceTargetDefEq t
      Lean.Elab.Tactic.replaceMainGoal [g]
    simp [CompCert4Lean.X86.Asm.Pregmap.get,
      CompCert4Lean.X86.Asm.Pregmap.set]

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

theorem negate_testcond_for_condition : negate_testcond_for_conditionStatement := by
  intro cond
  cases cond with
  | Ccomp c => cases c <;> rfl
  | Ccompu c => cases c <;> rfl
  | Ccompimm c n => cases c <;> rfl
  | Ccompuimm c n => cases c <;> rfl
  | Ccompl c => cases c <;> rfl
  | Ccomplu c => cases c <;> rfl
  | Ccomplimm c n => cases c <;> rfl
  | Ccompluimm c n => cases c <;> rfl
  | Ccompf c => cases c <;> rfl
  | Cnotcompf c => cases c <;> rfl
  | Ccompfs c => cases c <;> rfl
  | Cnotcompfs c => cases c <;> rfl
  | Cmaskzero n => rfl
  | Cmasknotzero n => rfl

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Asm

private theorem mk_sel_lessdef_normalize (v : Val)
    (ty : CompCert4Lean.Common.AST.typ) :
    Val.lessdef (Val.normalize v ty) v := by
  cases v <;> cases ty <;>
    simp [Val.normalize, CompCert4Lean.X86_64.Archi.ptr64] <;>
    first | exact Val.lessdef_refl _ | exact Val.lessdef_undef _

theorem mk_sel_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    mk_sel_correctStatement := by
  intro ge fn xc ty rd r2 k c ob rs m hmk hne hob
  cases xc with
  | Cond_base c0 =>
      simp only [CompCert4Lean.X86.Asmgen.mk_sel] at hmk
      change CompCert4Lean.Common.Errors.OK
          (.Pcmov (CompCert4Lean.X86.Asmgen.negate_testcond c0) rd r2 :: k) =
        CompCert4Lean.Common.Errors.OK c at hmk
      injection hmk with hc
      subst c
      let v := match eval_testcond
          (CompCert4Lean.X86.Asmgen.negate_testcond c0) rs with
        | some b => if b then rs (.IR r2) else rs (.IR rd)
        | none => Vundef
      refine ⟨CompCert4Lean.X86.Asm.nextinstr
        (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd) v rs), ?_, ?_, ?_⟩
      · apply exec_straight_one
        · change CompCert4Lean.X86.Asm.outcome.Next
            (CompCert4Lean.X86.Asm.nextinstr
              (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd) v rs)) m = _
          rfl
        · rfl
      · simp [v, CompCert4Lean.X86.Asm.nextinstr,
          CompCert4Lean.X86.Asm.Pregmap.set,
          CompCert4Lean.X86.Asm.Pregmap.get]
        cases ob with
        | none => exact Val.lessdef_undef _
        | some b =>
            rcases hob with ⟨_, hneg⟩
            have hneg' : eval_testcond
                (CompCert4Lean.X86.Asmgen.negate_testcond c0) rs = some (!b) := by
              simpa [eval_extcond, negate_extcond] using hneg
            cases hval : eval_testcond
                (CompCert4Lean.X86.Asmgen.negate_testcond c0) rs with
            | none => simp [hval] at hneg'
            | some bneg =>
                simp [hval] at hneg'
                cases b <;> cases bneg
                · contradiction
                · simp [Val.select, v, hval]
                  exact mk_sel_lessdef_normalize (rs (.IR r2)) ty
                · simp [Val.select, v, hval]
                  exact mk_sel_lessdef_normalize (rs (.IR rd)) ty
                · contradiction
      · intro r hr hrd
        cases r <;>
          simp_all [CompCert4Lean.X86.Asm.nextinstr,
            CompCert4Lean.X86.Asm.Pregmap.set,
            CompCert4Lean.X86.Asm.Pregmap.get,
            CompCert4Lean.X86.Asm.data_preg]
  | Cond_and c1 c2 =>
      simp only [CompCert4Lean.X86.Asmgen.mk_sel] at hmk
      change CompCert4Lean.Common.Errors.OK
          (.Pcmov (CompCert4Lean.X86.Asmgen.negate_testcond c1) rd r2 ::
            .Pcmov (CompCert4Lean.X86.Asmgen.negate_testcond c2) rd r2 :: k) =
        CompCert4Lean.Common.Errors.OK c at hmk
      injection hmk with hc
      subst c
      let v1 := match eval_testcond
          (CompCert4Lean.X86.Asmgen.negate_testcond c1) rs with
        | some b => if b then rs (.IR r2) else rs (.IR rd)
        | none => Vundef
      let rs_mid := CompCert4Lean.X86.Asm.nextinstr
        (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd) v1 rs)
      let v2 := match eval_testcond
          (CompCert4Lean.X86.Asmgen.negate_testcond c2) rs with
        | some b => if b then rs (.IR r2) else v1
        | none => Vundef
      let rs_final := CompCert4Lean.X86.Asm.nextinstr
        (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd) v2 rs_mid)
      refine ⟨rs_final, ?_, ?_, ?_⟩
      · apply exec_straight_step (rs2 := rs_mid) (m2 := m)
        · change CompCert4Lean.X86.Asm.outcome.Next
            (CompCert4Lean.X86.Asm.nextinstr
              (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd) v1 rs)) m = _
          rfl
        · rfl
        · apply exec_straight_one
          · have hmid_eval : eval_testcond
                (CompCert4Lean.X86.Asmgen.negate_testcond c2) rs_mid =
                eval_testcond
                  (CompCert4Lean.X86.Asmgen.negate_testcond c2) rs := by
              change eval_testcond
                  (CompCert4Lean.X86.Asmgen.negate_testcond c2)
                  (CompCert4Lean.X86.Asm.nextinstr
                    (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd) v1 rs)) = _
              have hnext := eval_testcond_nextinstr
                (CompCert4Lean.X86.Asmgen.negate_testcond c2)
                (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd) v1 rs)
              have hset := eval_testcond_set_ireg
                (CompCert4Lean.X86.Asmgen.negate_testcond c2) rs rd v1
              exact hnext.trans hset
            change CompCert4Lean.X86.Asm.outcome.Next
                (CompCert4Lean.X86.Asm.nextinstr
                  (CompCert4Lean.X86.Asm.Pregmap.set (.IR rd)
                    (match eval_testcond
                        (CompCert4Lean.X86.Asmgen.negate_testcond c2) rs_mid with
                    | some b => if b then rs_mid (.IR r2) else rs_mid (.IR rd)
                    | none => Vundef) rs_mid)) m = _
            rw [hmid_eval]
            simp [rs_mid, v1, CompCert4Lean.X86.Asm.nextinstr,
              CompCert4Lean.X86.Asm.Pregmap.set, rs_final, v2,
              hne, Ne.symm hne]
          · rfl
      · dsimp [rs_final, rs_mid]
        simp [CompCert4Lean.X86.Asm.nextinstr,
          CompCert4Lean.X86.Asm.Pregmap.set,
          CompCert4Lean.X86.Asm.Pregmap.get]
        cases ob with
        | none => exact Val.lessdef_undef _
        | some b =>
            rcases hob with ⟨_, hneg⟩
            cases h1 : eval_testcond
                (CompCert4Lean.X86.Asmgen.negate_testcond c1) rs with
            | none =>
                simp [eval_extcond, negate_extcond, h1] at hneg
            | some b1 =>
                cases h2 : eval_testcond
                    (CompCert4Lean.X86.Asmgen.negate_testcond c2) rs with
                | none =>
                    simp [eval_extcond, negate_extcond, h1, h2] at hneg
                | some b2 =>
                    simp [eval_extcond, negate_extcond, h1, h2] at hneg
                    cases b <;> cases b1 <;> cases b2 <;>
                      simp_all [Val.select, v1, v2, h1, h2]
                    all_goals first
                      | simpa [Val.select, v1, v2, h1, h2] using
                          (mk_sel_lessdef_normalize (rs (.IR rd)) ty)
                      | simpa [Val.select, v1, v2, h1, h2] using
                          (mk_sel_lessdef_normalize (rs (.IR r2)) ty)
      · intro r hr hrd
        dsimp [rs_final, rs_mid]
        cases r <;>
          simp_all [CompCert4Lean.X86.Asm.nextinstr,
            CompCert4Lean.X86.Asm.Pregmap.set,
            CompCert4Lean.X86.Asm.Pregmap.get,
            CompCert4Lean.X86.Asm.data_preg]
  | Cond_or c1 c2 =>
      simp only [CompCert4Lean.X86.Asmgen.mk_sel] at hmk
      cases hmk

end CompCert4Lean.X86.Asmgenproof1


namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

theorem divs_mods_exists : divs_mods_existsStatement := by
  intro v1 v2 h
  cases v1 <;> cases v2 <;>
    simp only [CompCert4Lean.Common.Values.Val.divs,
      CompCert4Lean.Common.Values.Val.mods] at h ⊢
  all_goals try { simp at h }
  case Vint.Vint n d =>
    have hd : d ≠ CompCert4Lean.Lib.Integers.Int.zero := by
      intro hd
      subst d
      simp [CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq] at h
    have hcond : n ≠ CompCert4Lean.Lib.Integers.Int.repr
          CompCert4Lean.Lib.Integers.Int.min_signed ∨
        d ≠ CompCert4Lean.Lib.Integers.Int.mone := by
      by_cases hn : n = CompCert4Lean.Lib.Integers.Int.repr
          CompCert4Lean.Lib.Integers.Int.min_signed
      · right
        intro hdm
        subst n
        subst d
        simp [CompCert4Lean.Lib.Integers.Int.eq,
          CompCert4Lean.Lib.Integers.WordCore.eq] at h
      · exact Or.inl hn
    let c := CompCert4Lean.Lib.Integers.Int.eq d
          CompCert4Lean.Lib.Integers.Int.zero ||
        CompCert4Lean.Lib.Integers.Int.eq n
          (CompCert4Lean.Lib.Integers.Int.repr
            CompCert4Lean.Lib.Integers.Int.min_signed) &&
        CompCert4Lean.Lib.Integers.Int.eq d
          CompCert4Lean.Lib.Integers.Int.mone
    have hc : c = false := by
      apply (Bool.eq_false_iff).2
      intro hc'
      dsimp [c] at hc'
      simp [hc'] at h
    have hdiv := CompCert4Lean.Lib.Integers.Int.divmods2_divs_mods_proof
      n d hd hcond
    have hshr : CompCert4Lean.Common.Values.Val.shr (Vint n)
        (Vint (CompCert4Lean.Lib.Integers.Int.repr
          (ZArith.BinInt.Z.of_nat 31))) =
      Vint (if CompCert4Lean.Lib.Integers.Int.lt n
          CompCert4Lean.Lib.Integers.Int.zero then
        CompCert4Lean.Lib.Integers.Int.mone else
        CompCert4Lean.Lib.Integers.Int.zero) := by
      change (if CompCert4Lean.Lib.Integers.Int.ltu
          (CompCert4Lean.Lib.Integers.Int.repr
            (ZArith.BinInt.Z.of_nat 31))
          CompCert4Lean.Lib.Integers.Int.iwordsize = true then
          Vint (CompCert4Lean.Lib.Integers.Int.shr n
            (CompCert4Lean.Lib.Integers.Int.repr
              (ZArith.BinInt.Z.of_nat 31))) else Vundef) = _
      have hlt : CompCert4Lean.Lib.Integers.Int.ltu
          (CompCert4Lean.Lib.Integers.Int.repr
            (ZArith.BinInt.Z.of_nat 31))
          CompCert4Lean.Lib.Integers.Int.iwordsize = true := by decide
      simp [hlt]
      congr 1
      have hz : (ZArith.BinInt.Z.of_nat 31) =
          ZArith.BinInt.Z.sub
            CompCert4Lean.Lib.Integers.Int.zwordsize
            (ZArith.BinInt.Z.Zpos xH) := by decide
      change CompCert4Lean.Lib.Integers.Int.shr n
          (CompCert4Lean.Lib.Integers.Int.repr
            (ZArith.BinInt.Z.of_nat 31)) = _
      rw [hz]
      exact CompCert4Lean.Lib.Integers.Int.shr_lt_zero_proof n
    have hc_actual : (CompCert4Lean.Lib.Integers.Int.eq d
          CompCert4Lean.Lib.Integers.Int.zero ||
        CompCert4Lean.Lib.Integers.Int.eq n
          (CompCert4Lean.Lib.Integers.Int.repr
            CompCert4Lean.Lib.Integers.Int.min_signed) &&
        CompCert4Lean.Lib.Integers.Int.eq d
          CompCert4Lean.Lib.Integers.Int.mone) = false := by
      change (CompCert4Lean.Lib.Integers.Int.eq d
          CompCert4Lean.Lib.Integers.Int.zero ||
        CompCert4Lean.Lib.Integers.Int.eq n
          (CompCert4Lean.Lib.Integers.Int.repr
            CompCert4Lean.Lib.Integers.Int.min_signed) &&
        CompCert4Lean.Lib.Integers.Int.eq d
          CompCert4Lean.Lib.Integers.Int.mone) = false at hc
      exact hc
    simp [hc_actual]
    have hshr' : CompCert4Lean.Common.Values.Val.shr (Vint n)
        (Vint (CompCert4Lean.Lib.Integers.Int.repr
          (ZArith.BinInt.Z.of_nat 31))) =
      Vint (CompCert4Lean.Lib.Integers.Int.shr n
        (CompCert4Lean.Lib.Integers.Int.repr
          (ZArith.BinInt.Z.of_nat 31))) := by
      change (if CompCert4Lean.Lib.Integers.Int.ltu
          (CompCert4Lean.Lib.Integers.Int.repr
            (ZArith.BinInt.Z.of_nat 31))
          CompCert4Lean.Lib.Integers.Int.iwordsize = true then
          Vint (CompCert4Lean.Lib.Integers.Int.shr n
            (CompCert4Lean.Lib.Integers.Int.repr
              (ZArith.BinInt.Z.of_nat 31))) else Vundef) = _
      have hlt : CompCert4Lean.Lib.Integers.Int.ltu
          (CompCert4Lean.Lib.Integers.Int.repr
            (ZArith.BinInt.Z.of_nat 31))
          CompCert4Lean.Lib.Integers.Int.iwordsize = true := by decide
      simp [hlt]
    refine ⟨CompCert4Lean.Lib.Integers.Int.shr n
          (CompCert4Lean.Lib.Integers.Int.repr
            (ZArith.BinInt.Z.of_nat 31)), hshr', ?_⟩
    rw [show CompCert4Lean.Lib.Integers.Int.shr n
          (CompCert4Lean.Lib.Integers.Int.repr
            (ZArith.BinInt.Z.of_nat 31)) =
          (if CompCert4Lean.Lib.Integers.Int.lt n
            CompCert4Lean.Lib.Integers.Int.zero then
            CompCert4Lean.Lib.Integers.Int.mone else
            CompCert4Lean.Lib.Integers.Int.zero) by
      have hz : (ZArith.BinInt.Z.of_nat 31) =
          ZArith.BinInt.Z.sub
            CompCert4Lean.Lib.Integers.Int.zwordsize
            (ZArith.BinInt.Z.Zpos xH) := by decide
      rw [hz]
      exact CompCert4Lean.Lib.Integers.Int.shr_lt_zero_proof n]
    exact hdiv

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Asm
open CompCert4Lean.X86.Asmgen

private theorem shrximm_sub_zero (x : int) :
    CompCert4Lean.Lib.Integers.Int.sub x CompCert4Lean.Lib.Integers.Int.zero = x := by
  change WordCore.repr 32 (ZArith.BinInt.Z.sub
    (CompCert4Lean.Lib.Integers.Int.unsigned x) Z0) = x
  have hz (z : Z) : ZArith.BinInt.Z.sub z Z0 = z := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
      show intOfZ Z0 = 0 from rfl, _root_.Int.sub_zero]
  rw [hz]
  exact CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof x

private theorem shrximm_overflow_zero (x : int) :
    CompCert4Lean.Lib.Integers.Int.sub_overflow x
      CompCert4Lean.Lib.Integers.Int.zero CompCert4Lean.Lib.Integers.Int.zero =
      CompCert4Lean.Lib.Integers.Int.zero := by
  have hr := CompCert4Lean.Lib.Integers.Int.signed_range_proof x
  change -2147483648 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.signed x) ∧
    intOfZ (CompCert4Lean.Lib.Integers.Int.signed x) ≤ 2147483647 at hr
  unfold CompCert4Lean.Lib.Integers.Int.sub_overflow WordCore.sub_overflow
  have hz (z : Z) : ZArith.BinInt.Z.sub z Z0 = z := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
      show intOfZ Z0 = 0 from rfl, _root_.Int.sub_zero]
  rw [show WordCore.signed CompCert4Lean.Lib.Integers.Int.zero = Z0 from
    CompCert4Lean.Lib.Integers.Int.signed_zero_proof]
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.Meta.transform (← g.getType) (post := fun e => do
      if e.getAppFn.constName?.any (fun n =>
          n.toString.startsWith "_private.CompCert4Lean.Lib.Integers.") then
        return .visit (← Lean.Meta.unfoldDefinition e)
      else return .continue)
    Lean.Elab.Tactic.replaceMainGoal [← g.replaceTargetDefEq t]
  dsimp only
  rw [hz, hz]
  cases CompCert4Lean.Lib.Coqlib.zlt (WordCore.signed x)
      (ZArith.BinInt.Z.opp (two_power_nat (CompCert4Lean.Lib.Integers.Int.wordsize - 1))) with
  | left h =>
      change intOfZ (CompCert4Lean.Lib.Integers.Int.signed x) < -2147483648 at h
      omega
  | right _ =>
      cases CompCert4Lean.Lib.Coqlib.zlt
          (ZArith.BinInt.Z.sub (two_power_nat (CompCert4Lean.Lib.Integers.Int.wordsize - 1))
            (Zpos xH)) (WordCore.signed x) with
      | left h =>
          change 2147483647 < intOfZ (CompCert4Lean.Lib.Integers.Int.signed x) at h
          omega
      | right _ => rfl

private theorem shrximm_sign_condition (rs : regset) (x : int) (m : Mem) :
    eval_testcond .Cond_l (compare_ints (.Vint x)
      (.Vint CompCert4Lean.Lib.Integers.Int.zero) rs m) =
      some (CompCert4Lean.Lib.Integers.Int.lt x CompCert4Lean.Lib.Integers.Int.zero) := by
  change some (CompCert4Lean.Lib.Integers.Int.eq
    (CompCert4Lean.Lib.Integers.Int.xor
      (CompCert4Lean.Lib.Integers.Int.sub_overflow x
        CompCert4Lean.Lib.Integers.Int.zero CompCert4Lean.Lib.Integers.Int.zero)
      (CompCert4Lean.Lib.Integers.Int.negative
        (CompCert4Lean.Lib.Integers.Int.sub x CompCert4Lean.Lib.Integers.Int.zero)))
    CompCert4Lean.Lib.Integers.Int.one) = _
  rw [shrximm_overflow_zero, shrximm_sub_zero]
  change some (CompCert4Lean.Lib.Integers.Int.eq
    (CompCert4Lean.Lib.Integers.Int.xor CompCert4Lean.Lib.Integers.Int.zero
      (if CompCert4Lean.Lib.Integers.Int.lt x CompCert4Lean.Lib.Integers.Int.zero
        then CompCert4Lean.Lib.Integers.Int.one else CompCert4Lean.Lib.Integers.Int.zero))
    CompCert4Lean.Lib.Integers.Int.one) = _
  cases h : CompCert4Lean.Lib.Integers.Int.lt x CompCert4Lean.Lib.Integers.Int.zero <;>
    simp only [h, Bool.false_eq_true, if_false, if_true] <;> rfl


private theorem shrximm_value (x n : int) (v : Val)
    (h : Val.shrx (.Vint x) (.Vint n) = some v) :
    Val.shr
      (if CompCert4Lean.Lib.Integers.Int.lt x CompCert4Lean.Lib.Integers.Int.zero then
        .Vint (CompCert4Lean.Lib.Integers.Int.add x
          (CompCert4Lean.Lib.Integers.Int.sub
            (CompCert4Lean.Lib.Integers.Int.shl CompCert4Lean.Lib.Integers.Int.one n)
            CompCert4Lean.Lib.Integers.Int.one))
      else .Vint x) (.Vint n) = v := by
  have hn : CompCert4Lean.Lib.Integers.Int.ltu n
      (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 31)) = true := by
    cases hc : CompCert4Lean.Lib.Integers.Int.ltu n
        (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 31))
    · simp [Val.shrx, hc] at h
    · rfl
  have hlt := (CompCert4Lean.Lib.Integers.Int.ltu_inv_proof n
    (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 31)) hn).2
  change intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned n) < 31 at hlt
  have hn32 : CompCert4Lean.Lib.Integers.Int.ltu n
      CompCert4Lean.Lib.Integers.Int.iwordsize = true := by
    unfold CompCert4Lean.Lib.Integers.Int.ltu WordCore.ltu
    run_tac
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← Lean.Meta.transform (← g.getType) (post := fun e => do
        if e.getAppFn.constName?.any (fun n =>
            n.toString.startsWith "_private.CompCert4Lean.Lib.Integers.") then
          return .visit (← Lean.Meta.unfoldDefinition e)
        else return .continue)
      Lean.Elab.Tactic.replaceMainGoal [← g.replaceTargetDefEq t]
    dsimp only
    cases CompCert4Lean.Lib.Coqlib.zlt (WordCore.unsigned n)
        (WordCore.unsigned CompCert4Lean.Lib.Integers.Int.iwordsize) with
    | left _ => rfl
    | right hge =>
        change 32 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned n) at hge
        omega
  have heq := CompCert4Lean.Lib.Integers.Int.shrx_shr_proof x n hn
  simp only [Val.shrx, hn, if_true, Option.some.injEq] at h
  change Vint (CompCert4Lean.Lib.Integers.Int.shrx x n) = v at h
  rw [← h, heq]
  cases hs : CompCert4Lean.Lib.Integers.Int.lt x CompCert4Lean.Lib.Integers.Int.zero <;>
    simp [hs, Val.shr, hn32]


theorem mk_shrximm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    mk_shrximm_correctStatement := by
  intro ge fn n k c rs1 v m hmk hv
  obtain ⟨x, hx⟩ : ∃ x, rs1 (.IR .RAX) = Vint x := by
    cases he : rs1 (.IR .RAX) <;> try { simp [Val.shrx, he] at hv }
    exact ⟨_, rfl⟩
  have hvalue := shrximm_value x n v (by simpa only [hx] using hv)
  let p := CompCert4Lean.Lib.Integers.Int.sub
    (CompCert4Lean.Lib.Integers.Int.shl CompCert4Lean.Lib.Integers.Int.one n)
    CompCert4Lean.Lib.Integers.Int.one
  let x' := CompCert4Lean.Lib.Integers.Int.add x p
  let rs2 := nextinstr (compare_ints (.Vint x)
    (.Vint CompCert4Lean.Lib.Integers.Int.zero) rs1 m)
  let rs3 := nextinstr (Pregmap.set (.IR .RCX) (.Vint x') rs2)
  let v' : Val := if CompCert4Lean.Lib.Integers.Int.lt x
    CompCert4Lean.Lib.Integers.Int.zero then .Vint x' else .Vint x
  let rs4 := nextinstr (Pregmap.set (.IR .RAX) v' rs3)
  let rs5 := nextinstr_nf (Pregmap.set (.IR .RAX)
    (Val.shr (rs4 (.IR .RAX)) (.Vint n)) rs4)
  have h2rax : rs2 (.IR .RAX) = Vint x := by
    simp [rs2, nextinstr, compare_ints, Pregmap.set, hx]
  have h3rax : rs3 (.IR .RAX) = Vint x := by
    simp [rs3, nextinstr, Pregmap.set, h2rax]
  have h3rcx : rs3 (.IR .RCX) = Vint x' := by
    simp [rs3, nextinstr, Pregmap.set]
  have h4rax : rs4 (.IR .RAX) = v' := by
    simp [rs4, nextinstr, Pregmap.set]
  have hcond : eval_testcond .Cond_l rs3 =
      some (CompCert4Lean.Lib.Integers.Int.lt x CompCert4Lean.Lib.Integers.Int.zero) := by
    exact (eval_testcond_nextinstr .Cond_l
      (Pregmap.set (.IR .RCX) (.Vint x') rs2)).trans
      ((eval_testcond_set_ireg .Cond_l rs2 .RCX (.Vint x')).trans
        ((eval_testcond_nextinstr .Cond_l
          (compare_ints (.Vint x) (.Vint CompCert4Lean.Lib.Integers.Int.zero) rs1 m)).trans
          (shrximm_sign_condition rs1 x m)))
  unfold mk_shrximm at hmk
  injection hmk with hc
  subst c
  refine ⟨rs5, ?_, ?_, ?_⟩
  · apply exec_straight_step (rs2 := rs2) (m2 := m)
    · change Next (nextinstr (compare_ints
        (Val.and (rs1 (.IR .RAX)) (rs1 (.IR .RAX))) Vzero rs1 m)) m = _
      rw [hx]
      change Next (nextinstr (compare_ints
        (Vint (CompCert4Lean.Lib.Integers.Int.and x x)) Vzero rs1 m)) m = _
      rw [CompCert4Lean.Lib.Integers.Int.and_idem_proof]
      rfl
    · rfl
    · apply exec_straight_step (rs2 := rs3) (m2 := m)
      · change Next (nextinstr (Pregmap.set (.IR .RCX)
          (eval_addrmode32 ge (.Addrmode (some .RAX) none
            (.inl (CompCert4Lean.Lib.Integers.Int.unsigned p))) rs2) rs2)) m = _
        have ha : eval_addrmode32 ge (.Addrmode (some .RAX) none
            (.inl (CompCert4Lean.Lib.Integers.Int.unsigned p))) rs2 = Vint x' := by
          change Val.add (rs2 (.IR .RAX))
            (Val.add (Vint CompCert4Lean.Lib.Integers.Int.zero)
              (Vint (CompCert4Lean.Lib.Integers.Int.repr
                (CompCert4Lean.Lib.Integers.Int.unsigned p)))) = _
          rw [h2rax, CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof]
          change Vint (CompCert4Lean.Lib.Integers.Int.add x
            (CompCert4Lean.Lib.Integers.Int.add CompCert4Lean.Lib.Integers.Int.zero p)) = _
          rw [CompCert4Lean.Lib.Integers.Int.add_zero_l_proof]
        rw [ha]
      · rfl
      · apply exec_straight_step (rs2 := rs4) (m2 := m)
        · change Next (nextinstr (Pregmap.set (.IR .RAX)
            (match eval_testcond .Cond_l rs3 with
              | some b => if b then rs3 (.IR .RCX) else rs3 (.IR .RAX)
              | none => Vundef) rs3)) m = _
          rw [hcond, h3rax, h3rcx]
        · rfl
        · apply exec_straight_one
          · rfl
          · rfl
  · change Val.shr (rs4 (.IR .RAX)) (.Vint n) = v
    rw [h4rax]
    exact hvalue
  · intro r hr hrax hrcx
    cases r <;>
      simp_all [rs5, rs4, rs3, rs2, nextinstr_nf, nextinstr,
        undef_regs, compare_ints, Pregmap.set, data_preg]

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Asm
open CompCert4Lean.X86.Asmgen

private theorem shrxlimm_uint_val {bits : Nat} (x : WordCore.Word bits) :
    intOfZ (WordCore.unsigned x) = (x.val : _root_.Int) := by
  have h := x.intrange.1
  change (-1 : _root_.Int) < intOfZ x.intval at h
  change intOfZ x.intval = _root_.Int.ofNat (_root_.Int.toNat (intOfZ x.intval))
  exact (_root_.Int.toNat_of_nonneg (by omega)).symm

private theorem shrxlimm_repr_val (bits : Nat) (i : _root_.Int) :
    (WordCore.repr bits (zOfInt i)).val =
      _root_.Int.toNat (i % ((2 ^ bits : Nat) : _root_.Int)) := by
  run_tac
    let env ← Lean.getEnv
    let ns := env.constants.toList.filterMap fun (n, _) =>
      if n.toString.endsWith ".WordCore.val_repr" then some n else none
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent ns.head!) _ _))

private theorem shrxlimm_uint_repr (bits : Nat) (z : Z) :
    intOfZ (WordCore.unsigned (WordCore.repr bits z)) =
      intOfZ z % ((2 ^ bits : Nat) : _root_.Int) := by
  rw [shrxlimm_uint_val]
  have h := shrxlimm_repr_val bits (intOfZ z)
  rw [zOfInt_intOfZ] at h
  rw [h]
  exact _root_.Int.toNat_of_nonneg
    (_root_.Int.emod_nonneg _ (_root_.Int.ne_of_gt
      (_root_.Int.natCast_pos.mpr (Nat.two_pow_pos bits))))

private theorem shrxlimm_signed (x : int64) :
    intOfZ (CompCert4Lean.Lib.Integers.Int64.signed x) =
      if intOfZ x.intval < 9223372036854775808 then intOfZ x.intval
      else intOfZ x.intval - 18446744073709551616 := by
  unfold CompCert4Lean.Lib.Integers.Int64.signed WordCore.signed
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.Meta.transform (← g.getType) (post := fun e => do
      if e.getAppFn.constName?.any (fun n =>
          n.toString.startsWith "_private.CompCert4Lean.Lib.Integers.") then
        return .visit (← Lean.Meta.unfoldDefinition e)
      else return .continue)
    Lean.Elab.Tactic.replaceMainGoal [← g.replaceTargetDefEq t]
  dsimp only
  cases CompCert4Lean.Lib.Coqlib.zlt (WordCore.unsigned x) (two_power_nat (CompCert4Lean.Lib.Integers.Int64.wordsize - 1)) with
  | left h =>
      change intOfZ x.intval < 9223372036854775808 at h
      simp [h]
      rfl
  | right h =>
      change 9223372036854775808 ≤ intOfZ x.intval at h
      simp [show ¬intOfZ x.intval < 9223372036854775808 by omega,
        ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      rfl

private theorem shrxlimm_ltu (x y : int) :
    CompCert4Lean.Lib.Integers.Int.ltu x y =
      decide (intOfZ x.intval < intOfZ y.intval) := by
  unfold CompCert4Lean.Lib.Integers.Int.ltu WordCore.ltu
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.Meta.transform (← g.getType) (post := fun e => do
      if e.getAppFn.constName?.any (fun n =>
          n.toString.startsWith "_private.CompCert4Lean.Lib.Integers.") then
        return .visit (← Lean.Meta.unfoldDefinition e)
      else return .continue)
    Lean.Elab.Tactic.replaceMainGoal [← g.replaceTargetDefEq t]
  dsimp only
  cases CompCert4Lean.Lib.Coqlib.zlt (WordCore.unsigned x) (WordCore.unsigned y) with
  | left h => simp [show intOfZ x.intval < intOfZ y.intval from h]
  | right h => simp [show ¬intOfZ x.intval < intOfZ y.intval by exact _root_.Int.not_lt.mpr h]

private theorem shrxlimm_repr_intval (bits : Nat) (z : Z) :
    intOfZ (WordCore.repr bits z).intval =
      intOfZ z % ((2 ^ bits : Nat) : _root_.Int) := shrxlimm_uint_repr bits z

private theorem shrxlimm_signed_core (x : WordCore.Word 64) :
    intOfZ (WordCore.signed x) =
      if intOfZ x.intval < 9223372036854775808 then intOfZ x.intval
      else intOfZ x.intval - 18446744073709551616 := shrxlimm_signed x

set_option maxHeartbeats 16000000 in
private theorem shrxlimm_word (x : int64) (n : int)
    (hrange : 0 < intOfZ n.intval ∧ intOfZ n.intval < 63) :
    CompCert4Lean.Lib.Integers.Int64.shrx' x n =
      CompCert4Lean.Lib.Integers.Int64.shr'
        (CompCert4Lean.Lib.Integers.Int64.add x
          (CompCert4Lean.Lib.Integers.Int64.shru'
            (CompCert4Lean.Lib.Integers.Int64.shr' x
              (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 63)))
            (CompCert4Lean.Lib.Integers.Int.sub
              (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 64)) n))) n := by
  change WordCore.Word 64 at x
  change WordCore.Word 32 at n
  have hx := x.intrange
  change (-1 : _root_.Int) < intOfZ x.intval ∧
    intOfZ x.intval < 18446744073709551616 at hx
  have hcases : intOfZ n.intval = 1 ∨
      intOfZ n.intval = 2 ∨
      intOfZ n.intval = 3 ∨
      intOfZ n.intval = 4 ∨
      intOfZ n.intval = 5 ∨
      intOfZ n.intval = 6 ∨
      intOfZ n.intval = 7 ∨
      intOfZ n.intval = 8 ∨
      intOfZ n.intval = 9 ∨
      intOfZ n.intval = 10 ∨
      intOfZ n.intval = 11 ∨
      intOfZ n.intval = 12 ∨
      intOfZ n.intval = 13 ∨
      intOfZ n.intval = 14 ∨
      intOfZ n.intval = 15 ∨
      intOfZ n.intval = 16 ∨
      intOfZ n.intval = 17 ∨
      intOfZ n.intval = 18 ∨
      intOfZ n.intval = 19 ∨
      intOfZ n.intval = 20 ∨
      intOfZ n.intval = 21 ∨
      intOfZ n.intval = 22 ∨
      intOfZ n.intval = 23 ∨
      intOfZ n.intval = 24 ∨
      intOfZ n.intval = 25 ∨
      intOfZ n.intval = 26 ∨
      intOfZ n.intval = 27 ∨
      intOfZ n.intval = 28 ∨
      intOfZ n.intval = 29 ∨
      intOfZ n.intval = 30 ∨
      intOfZ n.intval = 31 ∨
      intOfZ n.intval = 32 ∨
      intOfZ n.intval = 33 ∨
      intOfZ n.intval = 34 ∨
      intOfZ n.intval = 35 ∨
      intOfZ n.intval = 36 ∨
      intOfZ n.intval = 37 ∨
      intOfZ n.intval = 38 ∨
      intOfZ n.intval = 39 ∨
      intOfZ n.intval = 40 ∨
      intOfZ n.intval = 41 ∨
      intOfZ n.intval = 42 ∨
      intOfZ n.intval = 43 ∨
      intOfZ n.intval = 44 ∨
      intOfZ n.intval = 45 ∨
      intOfZ n.intval = 46 ∨
      intOfZ n.intval = 47 ∨
      intOfZ n.intval = 48 ∨
      intOfZ n.intval = 49 ∨
      intOfZ n.intval = 50 ∨
      intOfZ n.intval = 51 ∨
      intOfZ n.intval = 52 ∨
      intOfZ n.intval = 53 ∨
      intOfZ n.intval = 54 ∨
      intOfZ n.intval = 55 ∨
      intOfZ n.intval = 56 ∨
      intOfZ n.intval = 57 ∨
      intOfZ n.intval = 58 ∨
      intOfZ n.intval = 59 ∨
      intOfZ n.intval = 60 ∨
      intOfZ n.intval = 61 ∨
      intOfZ n.intval = 62 := by omega
  rcases hcases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  all_goals
    apply WordCore.ext
    apply intOfZ_injective
    simp [CompCert4Lean.Lib.Integers.Int64.shrx',
      CompCert4Lean.Lib.Integers.Int64.divs, WordCore.divs,
      CompCert4Lean.Lib.Integers.Int64.signed,
      CompCert4Lean.Lib.Integers.Int64.shr',
      CompCert4Lean.Lib.Integers.Int64.shru',
      CompCert4Lean.Lib.Integers.Int64.shl',
      CompCert4Lean.Lib.Integers.Int64.add, WordCore.add,
      CompCert4Lean.Lib.Integers.Int64.repr,
      CompCert4Lean.Lib.Integers.Int.sub, WordCore.sub,
      CompCert4Lean.Lib.Integers.Int.repr, shrxlimm_repr_intval,
      shrxlimm_signed, shrxlimm_signed_core,
      CompCert4Lean.Lib.Integers.Int.unsigned,
      CompCert4Lean.Lib.Integers.Int64.unsigned,
      CompCert4Lean.Lib.Integers.Int.wordsize,
      CompCert4Lean.Lib.Integers.Int64.wordsize,
      show CompCert4Lean.Lib.Integers.Int64.one =
        WordCore.repr 64 (zOfInt 1) from rfl,
      WordCore.unsigned, ZArith.BinInt.Z.add,
      ZArith.BinInt.Z.sub, ZArith.BinInt.Z.shiftr,
      ZArith.BinInt.Z.shiftl, ZArith.BinInt.Z.quot, intOfZ_zOfInt,
      hn]
    simp [shrxlimm_signed_core, shrxlimm_signed, shrxlimm_repr_intval,
      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, _root_.Int.pow,
      show intOfZ (WordCore.unsigned (WordCore.one 64)) = 1 from rfl]
    simp only [_root_.Int.tdiv_cases, ← _root_.Int.div_def]
    omega

private theorem shrxlimm_word_zero (x : int64) (n : int)
    (hn : intOfZ n.intval = 0) :
    CompCert4Lean.Lib.Integers.Int64.shrx' x n = x := by
  change WordCore.Word 64 at x
  change WordCore.Word 32 at n
  have hx := x.intrange
  change (-1 : _root_.Int) < intOfZ x.intval ∧
    intOfZ x.intval < 18446744073709551616 at hx
  apply WordCore.ext
  apply intOfZ_injective
  simp [CompCert4Lean.Lib.Integers.Int64.shrx',
    CompCert4Lean.Lib.Integers.Int64.divs, WordCore.divs,
    CompCert4Lean.Lib.Integers.Int64.signed,
    CompCert4Lean.Lib.Integers.Int64.shl',
    CompCert4Lean.Lib.Integers.Int64.repr,
    CompCert4Lean.Lib.Integers.Int.unsigned,
    CompCert4Lean.Lib.Integers.Int64.unsigned, WordCore.unsigned,
    CompCert4Lean.Lib.Integers.Int64.wordsize,
    show CompCert4Lean.Lib.Integers.Int64.one =
      WordCore.repr 64 (zOfInt 1) from rfl,
    shrxlimm_repr_intval, shrxlimm_signed_core,
    ZArith.BinInt.Z.shiftl, ZArith.BinInt.Z.quot, intOfZ_zOfInt, hn]
  simp [shrxlimm_signed_core, shrxlimm_repr_intval, intOfZ_zOfInt,
    _root_.Int.pow]
  omega

private theorem shrxlimm_eq_zero (n : int) :
    CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero =
      decide (intOfZ n.intval = 0) := by
  change decide (n.intval = Z0) = decide (intOfZ n.intval = 0)
  congr 1
  apply propext
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    apply intOfZ_injective
    exact h

private theorem shrxlimm_value : Val.shrxl_shrl_2Statement := by
  intro n x z h
  cases x <;> try { simp [Val.shrxl] at h }
  rename_i x
  have hn : CompCert4Lean.Lib.Integers.Int.ltu n
      (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 63)) = true := by
    cases hc : CompCert4Lean.Lib.Integers.Int.ltu n
        (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 63))
    · simp [Val.shrxl, hc] at h
    · rfl
  simp only [Val.shrxl, hn, if_true, Option.some.injEq] at h
  subst z
  have hlt : intOfZ n.intval < 63 := by
    rw [shrxlimm_ltu] at hn
    change decide (intOfZ n.intval < 63) = true at hn
    exact of_decide_eq_true hn
  by_cases hz : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · rw [if_pos hz]
    have hz0 : intOfZ n.intval = 0 := by
      rw [shrxlimm_eq_zero] at hz
      exact of_decide_eq_true hz
    exact congrArg Vlong (shrxlimm_word_zero x n hz0)
  · rw [if_neg hz]
    have hn0 : intOfZ n.intval ≠ 0 := by
      rw [shrxlimm_eq_zero] at hz
      simpa only [decide_eq_true_eq] using hz
    have hr := n.intrange.1
    change (-1 : _root_.Int) < intOfZ n.intval at hr
    have hrange : 0 < intOfZ n.intval ∧ intOfZ n.intval < 63 := by omega
    have hn64 : CompCert4Lean.Lib.Integers.Int.ltu n
        CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
      rw [shrxlimm_ltu]
      change decide (intOfZ n.intval < 64) = true
      exact decide_eq_true (by omega)
    have hs64 : CompCert4Lean.Lib.Integers.Int.ltu
        (CompCert4Lean.Lib.Integers.Int.sub
          (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 64)) n)
        CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
      rw [shrxlimm_ltu]
      change decide (intOfZ (WordCore.repr 32
        (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 64) n.intval)).intval < 64) = true
      rw [shrxlimm_repr_intval]
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      change decide ((64 - intOfZ n.intval) % 4294967296 < 64) = true
      exact decide_eq_true (by omega)
    have h63 : CompCert4Lean.Lib.Integers.Int.ltu
        (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 63))
        CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by decide
    simp only [Val.shrl, Val.shrlu, Val.addl, hn64, hs64, h63, if_true]
    exact congrArg Vlong (shrxlimm_word x n hrange)

private theorem shrxlimm_add_zero (x : int64) :
    CompCert4Lean.Lib.Integers.Int64.add x
      CompCert4Lean.Lib.Integers.Int64.zero = x := by
  change WordCore.Word 64 at x
  have hx := x.intrange
  change (-1 : _root_.Int) < intOfZ x.intval ∧
    intOfZ x.intval < 18446744073709551616 at hx
  apply WordCore.ext
  apply intOfZ_injective
  change intOfZ (WordCore.repr 64
    (ZArith.BinInt.Z.add x.intval Z0)).intval = intOfZ x.intval
  rw [shrxlimm_repr_intval]
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  change (intOfZ x.intval + 0) % 18446744073709551616 = intOfZ x.intval
  omega

private theorem shrxlimm_addl_zero (v w : val) :
    Val.addl v (Val.addl w (.Vlong CompCert4Lean.Lib.Integers.Int64.zero)) =
      Val.addl v w := by
  have hp (x : ptrofs) : CompCert4Lean.Lib.Integers.Ptrofs.add x
      (CompCert4Lean.Lib.Integers.Ptrofs.of_int64
        CompCert4Lean.Lib.Integers.Int64.zero) = x := shrxlimm_add_zero x
  cases v <;> cases w <;>
    simp [Val.addl, CompCert4Lean.X86_64.Archi.ptr64, shrxlimm_add_zero, hp]

open CompCert4Lean.Backend.Asmgenproof0

private theorem shrxlimm_trace
    [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (value_rule : Val.shrxl_shrl_2Statement) :
    mk_shrxlimm_correctStatement := by
  intro ge fn n k c rs1 v m hmk hv
  change List instruction at k c
  change WordCore.Word 32 at n
  change val at v
  have heq := value_rule n (rs1 (.IR .RAX)) v hv
  change v = if CompCert4Lean.Lib.Integers.Int.eq n
    CompCert4Lean.Lib.Integers.Int.zero then _ else _ at heq
  unfold mk_shrxlimm at hmk
  change CompCert4Lean.Common.Errors.res.OK
    (if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero
      then _ else _) = .OK c at hmk
  by_cases hn : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · rw [if_pos hn] at hmk heq
    injection hmk with hc
    subst c
    let rs2 := nextinstr (Pregmap.set (.IR .RAX) (rs1 (.IR .RAX)) rs1)
    refine ⟨rs2, ?_, ?_, ?_⟩
    · apply exec_straight_one <;> rfl
    · simp [rs2, nextinstr, Pregmap.set, heq]
    · intro r hr hrax hrdx
      cases r <;> simp_all [rs2, nextinstr, Pregmap.set, data_preg]
  · rw [if_neg hn] at hmk heq
    injection hmk with hc
    subst c
    let v1 := Val.shrl (rs1 (.IR .RAX))
      (.Vint (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 63)))
    let v2 := Val.shrlu v1 (.Vint (CompCert4Lean.Lib.Integers.Int.sub
      (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 64)) n))
    let v3 := Val.addl (rs1 (.IR .RAX)) v2
    let v4 := Val.shrl v3 (.Vint n)
    let rs2 := nextinstr_nf (Pregmap.set (.IR .RDX) v1 rs1)
    let rs3 := nextinstr_nf (Pregmap.set (.IR .RDX) v2 rs2)
    let rs4 := nextinstr (Pregmap.set (.IR .RAX) v3 rs3)
    let rs5 := nextinstr_nf (Pregmap.set (.IR .RAX) v4 rs4)
    have h3rax : rs3 (.IR .RAX) = rs1 (.IR .RAX) := by
      simp [rs3, rs2, nextinstr_nf, nextinstr, undef_regs, Pregmap.set]
    have h3rdx : rs3 (.IR .RDX) = v2 := by
      simp [rs3, nextinstr_nf, nextinstr, undef_regs, Pregmap.set]
    refine ⟨rs5, ?_, ?_, ?_⟩
    · apply exec_straight_step (rs2 := rs2) (m2 := m)
      · rfl
      · rfl
      · apply exec_straight_step (rs2 := rs3) (m2 := m)
        · rfl
        · rfl
        · apply exec_straight_step (rs2 := rs4) (m2 := m)
          · change Next (nextinstr (Pregmap.set (.IR .RAX)
              (Val.addl (rs3 (.IR .RAX))
                (Val.addl (rs3 (.IR .RDX))
                  (.Vlong CompCert4Lean.Lib.Integers.Int64.zero))) rs3)) m = _
            rw [shrxlimm_addl_zero, h3rax, h3rdx]
          · rfl
          · apply exec_straight_one <;> rfl
    · change v4 = v
      exact heq.symm
    · intro r hr hrax hrdx
      cases r <;> simp_all [rs5, rs4, rs3, rs2, nextinstr_nf, nextinstr,
        undef_regs, Pregmap.set, data_preg]

theorem mk_shrxlimm_correct
    [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    mk_shrxlimm_correctStatement := shrxlimm_trace shrxlimm_value

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Asm
open CompCert4Lean.X86.Asmgen

set_option maxHeartbeats 16000000

theorem loadind_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    loadind_correctStatement := by
  intro ge fn base ofs ty dst k rs c m v hmk hload
  let addr : addrmode := .Addrmode (some base) none
    (Sum.inl (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs))
  have haddr : eval_addrmode ge addr rs = Val.offset_ptr (rs (.IR base)) ofs := by
    apply eval_addrmode_indexed
    cases h : rs (.IR base) <;> simp_all [Val.offset_ptr, Mem.loadv]
  have hload' : Mem.loadv (chunk_of_type ty) m (eval_addrmode ge addr rs) = some v := by
    rw [haddr]
    exact hload
  refine ⟨nextinstr_nf (Pregmap.set (A := CompCert4Lean.Common.Values.val) (preg_of dst) v rs), ?_, ?_, ?_⟩
  · unfold loadind at hmk
    cases ty <;> cases dst <;>
      simp [preg_of, CompCert4Lean.X86_64.Archi.ptr64] at hmk
    all_goals try contradiction
    all_goals injection hmk with hc; subst c
    all_goals simp only [chunk_of_type] at hload'
    all_goals apply exec_straight_one
    all_goals first
      | (unfold CompCert4Lean.X86.Asm.exec_instr
         simp only [CompCert4Lean.X86_64.Archi.ptr64, if_true]
         change (match Mem.loadv _ m (eval_addrmode ge addr rs) with
           | some w => Next (nextinstr_nf
               (Pregmap.set (A := CompCert4Lean.Common.Values.val) _ w rs)) m
           | none => Stuck) =
           Next (nextinstr_nf
             (Pregmap.set (A := CompCert4Lean.Common.Values.val) _ v rs)) m
         rw [hload']
         simp [preg_of])
      | rfl
  · have hn := nextinstr_nf_inv1 (preg_of dst)
      (CompCert4Lean.X86.Asm.Pregmap.set (A := CompCert4Lean.Common.Values.val) (preg_of dst) v rs)
      (preg_of_data dst)
    simpa [CompCert4Lean.X86.Asm.Pregmap.set] using hn
  · intro r hr hne
    have hn := nextinstr_nf_inv1 r
      (CompCert4Lean.X86.Asm.Pregmap.set (A := CompCert4Lean.Common.Values.val) (preg_of dst) v rs) hr
    simpa [CompCert4Lean.X86.Asm.Pregmap.set, hne] using hn

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Asm
open CompCert4Lean.X86.Asmgen
open CompCert4Lean.X86.Op

private theorem addressing_mul_one_aux (x : int64) :
    CompCert4Lean.Lib.Integers.Int64.mul x
      (CompCert4Lean.Lib.Integers.Int64.repr (zOfNat 1)) = x := by
  change WordCore.repr 64 (ZArith.BinInt.Z.mul x.intval (.Zpos .xH)) = x
  have hm : ZArith.BinInt.Z.mul x.intval (.Zpos .xH) = x.intval := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    change intOfZ x.intval * 1 = intOfZ x.intval
    omega
  rw [hm]
  exact asmgenproof1PtrofsReprUnsigned x

private theorem addressing_scale_aux (v : val) (sc : Z) :
    Val.lessdef (Val.mull v (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr sc)))
      (match CompCert4Lean.Lib.Coqlib.zeq sc (zOfNat 1) with
       | .left _ => v
       | .right _ => Val.mull v (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr sc))) := by
  cases CompCert4Lean.Lib.Coqlib.zeq sc (zOfNat 1) with
  | left h =>
      subst sc
      cases v with
      | Vlong n =>
          change Val.lessdef (.Vlong (CompCert4Lean.Lib.Integers.Int64.mul n
            (CompCert4Lean.Lib.Integers.Int64.repr (zOfNat 1)))) (.Vlong n)
          rw [addressing_mul_one_aux]
          exact Val.lessdef_refl _
      | _ => exact Val.lessdef_undef _
  | right h => exact Val.lessdef_refl _

private theorem addressing_signed_repr_aux (x : ptrofs) :
    CompCert4Lean.Lib.Integers.Int64.repr
      (CompCert4Lean.Lib.Integers.Ptrofs.signed x) = x := by
  change WordCore.Word 64 at x
  have hx := x.intrange
  change (-1 : _root_.Int) < intOfZ x.intval ∧
    intOfZ x.intval < 18446744073709551616 at hx
  apply WordCore.ext
  apply intOfZ_injective
  change intOfZ (WordCore.repr 64 (WordCore.signed x)).intval = intOfZ x.intval
  rw [shrxlimm_repr_intval]
  change intOfZ (@WordCore.signed 64 x) % ((2 ^ 64 : Nat) : _root_.Int) = _
  rw [shrxlimm_signed_core]
  change (if intOfZ x.intval < 9223372036854775808 then intOfZ x.intval
    else intOfZ x.intval - 18446744073709551616) % 18446744073709551616 = _
  split <;> omega

private theorem addressing_zero_symbol_aux (ge : genv)
    (id : CompCert4Lean.Common.AST.ident) (ofs : ptrofs) :
    Val.addl (.Vlong CompCert4Lean.Lib.Integers.Int64.zero)
      (Genv.symbol_address ge id ofs) = Genv.symbol_address ge id ofs := by
  have hp (x : ptrofs) : CompCert4Lean.Lib.Integers.Ptrofs.add x
      (CompCert4Lean.Lib.Integers.Ptrofs.of_int64
        CompCert4Lean.Lib.Integers.Int64.zero) = x := shrxlimm_add_zero x
  unfold Genv.symbol_address
  cases Genv.find_symbol ge id <;>
    simp [Val.addl, CompCert4Lean.X86_64.Archi.ptr64, hp]

theorem transl_addressing_mode_correct : transl_addressing_mode_correctStatement := by
  intro ge addr args am rs v htrans heval
  change eval_addressing64 ge (rs (.IR .RSP)) addr
    (args.map (fun r => rs (preg_of r))) = some v at heval
  change Val.lessdef v (eval_addrmode64 ge am rs)
  cases addr with
  | Aindexed ofs =>
      rcases args with _ | ⟨a, _ | ⟨b, tail⟩⟩ <;>
        simp [eval_addressing64] at heval
      obtain ⟨r, hr, hm⟩ := bind_inversion _ _ _ _ _ htrans
      have hreg := ireg_of_eq a r hr
      change res.OK (.Addrmode (some r) none (.inl ofs)) = .OK am at hm
      cases hm
      rw [hreg] at heval
      subst v
      change Val.lessdef _ (Val.addl (rs (.IR r))
        (.Vlong (CompCert4Lean.Lib.Integers.Int64.add
          CompCert4Lean.Lib.Integers.Int64.zero
          (CompCert4Lean.Lib.Integers.Int64.repr ofs))))
      rw [asmgenproof1Int64AddZero]
      exact Val.lessdef_refl _
  | Aindexed2 ofs =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩ <;>
        simp [eval_addressing64] at heval
      obtain ⟨r1, hr1, hm⟩ := bind_inversion _ _ _ _ _ htrans
      obtain ⟨r2, hr2, hm⟩ := bind_inversion _ _ _ _ _ hm
      have hreg1 := ireg_of_eq a r1 hr1
      have hreg2 := ireg_of_eq b r2 hr2
      change res.OK (.Addrmode (some r1) (some (r2, zOfNat 1)) (.inl ofs)) = .OK am at hm
      cases hm
      rw [hreg1, hreg2] at heval
      subst v
      change Val.lessdef (Val.addl (Val.addl (rs (.IR r1)) (rs (.IR r2)))
          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs)))
        (Val.addl (rs (.IR r1)) (Val.addl (rs (.IR r2))
          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))))
      rw [Val.addl_assoc]
      exact Val.lessdef_refl _
  | Ascaled sc ofs =>
      rcases args with _ | ⟨a, _ | ⟨b, tail⟩⟩ <;>
        simp [eval_addressing64] at heval
      obtain ⟨r, hr, hm⟩ := bind_inversion _ _ _ _ _ htrans
      have hreg := ireg_of_eq a r hr
      change res.OK (.Addrmode none (some (r, sc)) (.inl ofs)) = .OK am at hm
      cases hm
      rw [hreg] at heval
      subst v
      change Val.lessdef _ (Val.addl (.Vlong CompCert4Lean.Lib.Integers.Int64.zero)
        (Val.addl
          (match CompCert4Lean.Lib.Coqlib.zeq sc (zOfNat 1) with
           | .left _ => rs (.IR r)
           | .right _ => Val.mull (rs (.IR r)) (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr sc)))
          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))))
      rw [Val.addl_permut]
      change Val.lessdef _ (Val.addl _ (.Vlong
        (CompCert4Lean.Lib.Integers.Int64.add CompCert4Lean.Lib.Integers.Int64.zero
          (CompCert4Lean.Lib.Integers.Int64.repr ofs))))
      rw [asmgenproof1Int64AddZero]
      exact Val.addl_lessdef _ _ _ _ (addressing_scale_aux _ _) (Val.lessdef_refl _)
  | Aindexed2scaled sc ofs =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩ <;>
        simp [eval_addressing64] at heval
      obtain ⟨r1, hr1, hm⟩ := bind_inversion _ _ _ _ _ htrans
      obtain ⟨r2, hr2, hm⟩ := bind_inversion _ _ _ _ _ hm
      have hreg1 := ireg_of_eq a r1 hr1
      have hreg2 := ireg_of_eq b r2 hr2
      change res.OK (.Addrmode (some r1) (some (r2, sc)) (.inl ofs)) = .OK am at hm
      cases hm
      rw [hreg1, hreg2] at heval
      subst v
      apply Val.addl_lessdef _ _ _ _ (Val.lessdef_refl _)
      exact Val.addl_lessdef _ _ _ _ (addressing_scale_aux _ _) (Val.lessdef_refl _)
  | Aglobal id ofs =>
      cases args with
      | cons a tail => simp [eval_addressing64] at heval
      | nil =>
          change res.OK (.Addrmode none none (.inr (id, ofs))) = .OK am at htrans
          cases htrans
          simp only [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64, if_true,
            List.map_nil, Option.some.injEq] at heval
          subst v
          change Val.lessdef _ (Val.addl (.Vlong CompCert4Lean.Lib.Integers.Int64.zero)
            (Val.addl (.Vlong CompCert4Lean.Lib.Integers.Int64.zero) (Genv.symbol_address ge id ofs)))
          rw [addressing_zero_symbol_aux, addressing_zero_symbol_aux]
          exact Val.lessdef_refl _
  | Abased id ofs =>
      rcases args with _ | ⟨a, _ | ⟨b, tail⟩⟩ <;> simp [eval_addressing64] at heval
  | Abasedscaled sc id ofs =>
      rcases args with _ | ⟨a, _ | ⟨b, tail⟩⟩ <;> simp [eval_addressing64] at heval
  | Ainstack ofs =>
      cases args with
      | cons a tail => simp [eval_addressing64] at heval
      | nil =>
          change res.OK (.Addrmode (some .RSP) none
            (.inl (CompCert4Lean.Lib.Integers.Ptrofs.signed ofs))) = .OK am at htrans
          cases htrans
          simp only [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64, if_true,
            List.map_nil, Option.some.injEq] at heval
          subst v
          change Val.lessdef (Val.offset_ptr (rs (.IR .RSP)) ofs)
            (Val.addl (rs (.IR .RSP)) (.Vlong
              (CompCert4Lean.Lib.Integers.Int64.add CompCert4Lean.Lib.Integers.Int64.zero
                (CompCert4Lean.Lib.Integers.Int64.repr
                  (CompCert4Lean.Lib.Integers.Ptrofs.signed ofs)))))
          rw [asmgenproof1Int64AddZero, addressing_signed_repr_aux]
          have hof : CompCert4Lean.Lib.Integers.Ptrofs.of_int64 ofs = ofs :=
            asmgenproof1PtrofsReprUnsigned ofs
          cases rs (.IR .RSP) <;>
            simp [Val.offset_ptr, Val.addl, CompCert4Lean.X86_64.Archi.ptr64, hof]
          all_goals first | exact Val.lessdef_refl _ | exact Val.lessdef_undef _

end CompCert4Lean.X86.Asmgenproof1
