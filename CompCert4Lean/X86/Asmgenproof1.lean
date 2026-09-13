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
