import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Separation
import CompCert4Lean.Cfrontend.Cminorgen

/-!
# Correctness interface for Cminor generation

Definition-bearing translation of the required surface of CompCert's
`cfrontend/Cminorgenproof.v`.  Proof obligations assigned to the later proof
phase are recorded as proposition descriptors.
-/

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Switch
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Cfrontend.Cminorgen

private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

namespace CS

private abbrev program := CompCert4Lean.Cfrontend.Csharpminor.program
private abbrev genv := CompCert4Lean.Cfrontend.Csharpminor.genv
private abbrev temp_env := CompCert4Lean.Cfrontend.Csharpminor.temp_env
private abbrev env := CompCert4Lean.Cfrontend.Csharpminor.env
private abbrev fundef := CompCert4Lean.Cfrontend.Csharpminor.fundef
private abbrev function := CompCert4Lean.Cfrontend.Csharpminor.function
private abbrev cont := CompCert4Lean.Cfrontend.Csharpminor.cont
private abbrev state := CompCert4Lean.Cfrontend.Csharpminor.state
private abbrev lbl_stmt := CompCert4Lean.Cfrontend.Csharpminor.lbl_stmt
private abbrev stmt := CompCert4Lean.Cfrontend.Csharpminor.stmt
private abbrev funsig := CompCert4Lean.Cfrontend.Csharpminor.funsig
private abbrev blocks_of_env := CompCert4Lean.Cfrontend.Csharpminor.blocks_of_env
private abbrev empty_env := CompCert4Lean.Cfrontend.Csharpminor.empty_env
private abbrev is_call_cont := CompCert4Lean.Cfrontend.Csharpminor.is_call_cont
private abbrev create_undef_temps :=
  CompCert4Lean.Cfrontend.Csharpminor.create_undef_temps
private abbrev bind_parameters := CompCert4Lean.Cfrontend.Csharpminor.bind_parameters
private abbrev alloc_variables := CompCert4Lean.Cfrontend.Csharpminor.alloc_variables
private abbrev eval_constant := CompCert4Lean.Cfrontend.Csharpminor.eval_constant
private abbrev eval_expr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  CompCert4Lean.Cfrontend.Csharpminor.eval_expr
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev eval_exprlist
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  CompCert4Lean.Cfrontend.Csharpminor.eval_exprlist
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev eval_var_addr := CompCert4Lean.Cfrontend.Csharpminor.eval_var_addr
private abbrev call_cont := CompCert4Lean.Cfrontend.Csharpminor.call_cont
private abbrev step
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  CompCert4Lean.Cfrontend.Csharpminor.step
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev initial_state := CompCert4Lean.Cfrontend.Csharpminor.initial_state
private abbrev final_state := CompCert4Lean.Cfrontend.Csharpminor.final_state
private abbrev semantics
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  CompCert4Lean.Cfrontend.Csharpminor.semantics
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev find_label := CompCert4Lean.Cfrontend.Csharpminor.find_label
private abbrev select_switch_default :=
  CompCert4Lean.Cfrontend.Csharpminor.select_switch_default
private abbrev select_switch_case :=
  CompCert4Lean.Cfrontend.Csharpminor.select_switch_case
private abbrev select_switch := CompCert4Lean.Cfrontend.Csharpminor.select_switch
private abbrev seq_of_lbl_stmt := CompCert4Lean.Cfrontend.Csharpminor.seq_of_lbl_stmt

end CS

namespace CM

private abbrev program := CompCert4Lean.Backend.Cminor.program
private abbrev genv := CompCert4Lean.Backend.Cminor.genv
private abbrev env := CompCert4Lean.Backend.Cminor.env
private abbrev function := CompCert4Lean.Backend.Cminor.function
private abbrev cont := CompCert4Lean.Backend.Cminor.cont
private abbrev state := CompCert4Lean.Backend.Cminor.state
private abbrev funsig := CompCert4Lean.Backend.Cminor.funsig
private abbrev set_params := CompCert4Lean.Backend.Cminor.set_params
private abbrev set_locals := CompCert4Lean.Backend.Cminor.set_locals
private abbrev eval_unop
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  CompCert4Lean.Backend.Cminor.eval_unop
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev eval_binop := CompCert4Lean.Backend.Cminor.eval_binop
private abbrev eval_constant := CompCert4Lean.Backend.Cminor.eval_constant
private abbrev eval_expr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  CompCert4Lean.Backend.Cminor.eval_expr
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev eval_exprlist
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  CompCert4Lean.Backend.Cminor.eval_exprlist
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev call_cont := CompCert4Lean.Backend.Cminor.call_cont
private abbrev is_call_cont := CompCert4Lean.Backend.Cminor.is_call_cont
private abbrev step
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  CompCert4Lean.Backend.Cminor.step
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev initial_state := CompCert4Lean.Backend.Cminor.initial_state
private abbrev final_state := CompCert4Lean.Backend.Cminor.final_state
private abbrev semantics
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  CompCert4Lean.Backend.Cminor.semantics
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev find_label := CompCert4Lean.Backend.Cminor.find_label

end CM
private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev ExternalCalls := CompCert4Lean.Common.ExternalCalls.ExternalCalls
private abbrev Permutation {A : Type} :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation (A := A)
private abbrev In {A : Type} :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In (A := A)
private abbrev zMax := ZArith.BinInt.Z.max
private abbrev z0 : Z := .Z0

local instance : OfNat Z 0 := ⟨z0⟩
local instance : HAdd Z Z Z := ⟨ZArith.BinInt.Z.add⟩
local instance : LE Z := ⟨ZArith.BinInt.Z.le⟩
local instance : LT Z := ⟨ZArith.BinInt.Z.lt⟩

/-! ## Programs and global environments -/

def match_prog (p : CS.program) (tp : CM.program) : Prop :=
  @CompCert4Lean.Common.Linking.match_program
    CS.fundef Unit CompCert4Lean.Backend.Cminor.fundef Unit
    (CompCert4Lean.Common.Linking.Linker_fundef CS.function)
    CompCert4Lean.Common.Linking.Linker_unit
    (fun _ f tf => transl_fundef f = .OK tf) Eq p tp

private abbrev sourceGenv (p : CS.program) : CS.genv := Genv.globalenv p
private abbrev targetGenv (p : CM.program) : CM.genv := Genv.globalenv p

/-! ## Environment and memory matching -/

def match_temps (f : meminj) (le : CS.temp_env) (te : CM.env) : Prop :=
  ∀ id v, PTree.get id le = some v →
    ∃ v', PTree.get id te = some v' ∧ Val.inject f v v'

inductive match_var (f : meminj) (sp : block) :
    Option (block × Z) → Option Z → Prop where
  | local {b sz ofs} :
      Val.inject f (.Vptr b Ptrofs.zero) (.Vptr sp (Ptrofs.repr ofs)) →
      match_var f sp (some (b, sz)) (some ofs)
  | global : match_var f sp none none

structure match_env (f : meminj) (cenv : compilenv) (e : CS.env)
    (sp lo hi : block) : Prop where
  me_vars : ∀ id, match_var f sp (PTree.get id e) (PTree.get id cenv)
  me_low_high : Ple lo hi
  me_bounded : ∀ id b sz, PTree.get id e = some (b, sz) → Ple lo b ∧ Plt b hi
  me_inv : ∀ b delta, f b = some (sp, delta) →
    ∃ id sz, PTree.get id e = some (b, sz)
  me_incr : ∀ b tb delta, f b = some (tb, delta) → Plt b lo → Plt tb sp

export match_env (me_vars me_low_high me_bounded me_inv me_incr)

def match_bounds (e : CS.env) (m : mem) : Prop :=
  ∀ id b sz ofs p,
    PTree.get id e = some (b, sz) → Mem.perm m b ofs .Max p → 0 ≤ ofs ∧ ofs < sz

inductive is_reachable_from_env (f : meminj) (e : CS.env) (sp : block)
    (ofs : Z) : Prop where
  | is_reachable_intro {id b sz delta} :
      PTree.get id e = some (b, sz) →
      f b = some (sp, delta) →
      delta ≤ ofs ∧ ofs < delta + sz →
      is_reachable_from_env f e sp ofs

export is_reachable_from_env (is_reachable_intro)

def padding_freeable (f : meminj) (e : CS.env) (tm : mem) (sp : block)
    (sz : Z) : Prop :=
  ∀ ofs, 0 ≤ ofs ∧ ofs < sz →
    Mem.perm tm sp ofs .Cur .Freeable ∨ is_reachable_from_env f e sp ofs

inductive match_globalenvs (prog : CS.program) (f : meminj) (bound : block) : Prop where
  | mk
      (domain : ∀ b, Plt b bound → f b = some (b, 0))
      (image : ∀ b1 b2 delta, f b1 = some (b2, delta) → Plt b2 bound → b1 = b2)
      (symbols : ∀ id b, Genv.find_symbol (sourceGenv prog) id = some b → Plt b bound)
      (functions : ∀ b fd, Genv.find_funct_ptr (sourceGenv prog) b = some fd → Plt b bound)
      (varinfos : ∀ b gv, Genv.find_var_info (sourceGenv prog) b = some gv → Plt b bound) :
      match_globalenvs prog f bound

/-! ## Abstract call stacks -/

inductive frame : Type where
  | Frame (cenv : compilenv) (tf : CM.function) (e : CS.env)
      (le : CS.temp_env) (te : CM.env) (sp lo hi : block)

export frame (Frame)

def callstack : Type := List frame

inductive match_callstack (prog : CS.program) (f : meminj) (m tm : mem) :
    callstack → block → block → Prop where
  | mcs_nil {hi bound tbound} :
      match_globalenvs prog f hi → Ple hi bound → Ple hi tbound →
      match_callstack prog f m tm [] bound tbound
  | cons {cenv tf e le te sp lo hi cs bound tbound} :
      Ple hi bound →
      Plt sp tbound →
      match_temps f le te →
      match_env f cenv e sp lo hi →
      match_bounds e m →
      padding_freeable f e tm sp tf.fn_stackspace →
      match_callstack prog f m tm cs lo sp →
      match_callstack prog f m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound

export match_callstack (mcs_nil)

/-! ## Compilation-environment properties -/

def cenv_remove (cenv : compilenv) (vars : List (ident × Z)) : compilenv :=
  vars.foldr (fun idSize ce => PTree.remove idSize.1 ce) cenv

def cenv_compat (cenv : compilenv) (vars : List (ident × Z)) (tsz : Z) : Prop :=
  ∀ id sz, In (id, sz) vars →
    ∃ ofs, PTree.get id cenv = some ofs ∧
      Mem.inj_offset_aligned ofs sz ∧
      0 ≤ ofs ∧ ofs + zMax 0 sz ≤ tsz

def cenv_separated (cenv : compilenv) (vars : List (ident × Z)) : Prop :=
  ∀ id1 sz1 ofs1 id2 sz2 ofs2,
    In (id1, sz1) vars → In (id2, sz2) vars →
    PTree.get id1 cenv = some ofs1 → PTree.get id2 cenv = some ofs2 →
    id1 ≠ id2 →
    ofs1 + sz1 ≤ ofs2 ∨ ofs2 + sz2 ≤ ofs1

def cenv_mem_separated (cenv : compilenv) (vars : List (ident × Z))
    (f : meminj) (sp : block) (m : mem) : Prop :=
  ∀ id sz ofs b delta ofs' k p,
    In (id, sz) vars → PTree.get id cenv = some ofs →
    f b = some (sp, delta) →
    Mem.perm m b ofs' k p →
    ofs ≤ ofs' + delta ∧ ofs' + delta < sz + ofs → False

def set_params' : List val → List ident → CM.env → CM.env
  | v :: vl, id :: il, te => set_params' vl il (PTree.set id v te)
  | [], id :: il, te => set_params' [] il (PTree.set id .Vundef te)
  | _, _, te => te

/-! ## Continuation and state matching -/

inductive match_cont : CS.cont → CM.cont → compilenv → exit_env → callstack → Prop where
  | stop {cenv xenv} : match_cont .Kstop .Kstop cenv xenv []
  | seq {s k ts tk cenv xenv cs} :
      transl_stmt cenv xenv s = .OK ts →
      match_cont k tk cenv xenv cs →
      match_cont (.Kseq s k) (.Kseq ts tk) cenv xenv cs
  | match_Kseq2 {s1 s2 k ts1 tk cenv xenv cs} :
      transl_stmt cenv xenv s1 = .OK ts1 →
      match_cont (.Kseq s2 k) tk cenv xenv cs →
      match_cont (.Kseq (.Sseq s1 s2) k) (.Kseq ts1 tk) cenv xenv cs
  | block {k tk cenv xenv cs} :
      match_cont k tk cenv xenv cs →
      match_cont (.Kblock k) (.Kblock tk) cenv (true :: xenv) cs
  | match_Kblock2 {k tk cenv xenv cs} :
      match_cont k tk cenv xenv cs →
      match_cont k (.Kblock tk) cenv (false :: xenv) cs
  | match_Kcall {optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv'} :
      transl_funbody cenv sz fn = .OK tfn →
      match_cont k tk cenv xenv cs →
      match_cont (.Kcall optid fn e le k)
        (.Kcall optid tfn (.Vptr sp Ptrofs.zero) te tk)
        cenv' [] (Frame cenv tfn e le te sp lo hi :: cs)

export match_cont (match_Kseq2 match_Kblock2 match_Kcall)

inductive match_states (prog : CS.program) : CS.state → CM.state → Prop where
  | match_state {fn s k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz} :
      transl_funbody cenv sz fn = .OK tfn →
      transl_stmt cenv xenv s = .OK ts →
      Mem.inject f m tm →
      match_callstack prog f m tm
        (Frame cenv tfn e le te sp lo hi :: cs) m.nextblock tm.nextblock →
      match_cont k tk cenv xenv cs →
      match_states prog (.State fn s k e le m)
        (.State tfn ts tk (.Vptr sp Ptrofs.zero) te tm)
  | match_state_seq {fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv f lo hi cs sz} :
      transl_funbody cenv sz fn = .OK tfn →
      transl_stmt cenv xenv s1 = .OK ts1 →
      Mem.inject f m tm →
      match_callstack prog f m tm
        (Frame cenv tfn e le te sp lo hi :: cs) m.nextblock tm.nextblock →
      match_cont (.Kseq s2 k) tk cenv xenv cs →
      match_states prog (.State fn (.Sseq s1 s2) k e le m)
        (.State tfn ts1 tk (.Vptr sp Ptrofs.zero) te tm)
  | match_callstate {fd args k m tfd targs tk tm f cs cenv} :
      transl_fundef fd = .OK tfd →
      Mem.inject f m tm →
      match_callstack prog f m tm cs m.nextblock tm.nextblock →
      match_cont k tk cenv [] cs →
      CS.is_call_cont k →
      Val.inject_list f args targs →
      match_states prog (.Callstate fd args k m) (.Callstate tfd targs tk tm)
  | returnstate {v k m tv tk tm f cs cenv} :
      Mem.inject f m tm →
      match_callstack prog f m tm cs m.nextblock tm.nextblock →
      match_cont k tk cenv [] cs →
      Val.inject f v tv →
      match_states prog (.Returnstate v k m) (.Returnstate tv tk tm)

export match_states (match_state match_state_seq match_callstate)

inductive lbl_stmt_tail : CS.lbl_stmt → Nat → CS.lbl_stmt → Prop where
  | zero {sl} : lbl_stmt_tail sl 0 sl
  | succ {c s sl n sl'} :
      lbl_stmt_tail sl n sl' →
      lbl_stmt_tail (.LScons c s sl) (Nat.succ n) sl'

inductive transl_lblstmt_cont (cenv : compilenv) (xenv : exit_env) :
    CS.lbl_stmt → CM.cont → CM.cont → Prop where
  | default {k} :
      transl_lblstmt_cont cenv xenv .LSnil k (.Kblock (.Kseq .Sskip k))
  | case {i s ls k ts k'} :
      transl_stmt cenv (switch_env (.LScons i s ls) xenv) s = .OK ts →
      transl_lblstmt_cont cenv xenv ls k k' →
      transl_lblstmt_cont cenv xenv (.LScons i s ls) k (.Kblock (.Kseq ts k'))

def seq_left_depth : CS.stmt → Nat
  | .Sseq s1 _ => Nat.succ (seq_left_depth s1)
  | _ => 0

def measure : CS.state → Nat
  | .State _ s _ _ _ _ => seq_left_depth s
  | _ => 0

/-! ## Exact statement descriptors for later proof migration -/

def transf_program_matchStatement : Prop :=
  ∀ p tp, transl_program p = .OK tp → match_prog p tp

def symbols_preservedStatement : Prop :=
  ∀ prog tprog, match_prog prog tprog →
    ∀ s : ident,
      Genv.find_symbol (targetGenv tprog) s = Genv.find_symbol (sourceGenv prog) s

def senv_preservedStatement : Prop :=
  ∀ prog tprog, match_prog prog tprog →
    Senv.equiv (Genv.to_senv (sourceGenv prog)) (Genv.to_senv (targetGenv tprog))

def function_ptr_translatedStatement : Prop :=
  ∀ prog tprog, match_prog prog tprog →
    ∀ (b : block) (f : CS.fundef),
      Genv.find_funct_ptr (sourceGenv prog) b = some f →
      ∃ tf, Genv.find_funct_ptr (targetGenv tprog) b = some tf ∧
        transl_fundef f = .OK tf

def functions_translatedStatement : Prop :=
  ∀ prog tprog, match_prog prog tprog →
    ∀ (v : val) (f : CS.fundef),
      Genv.find_funct (sourceGenv prog) v = some f →
      ∃ tf, Genv.find_funct (targetGenv tprog) v = some tf ∧
        transl_fundef f = .OK tf

def sig_preserved_bodyStatement : Prop :=
  ∀ f tf cenv size,
    transl_funbody cenv size f = .OK tf → tf.fn_sig = f.fn_sig

def sig_preservedStatement : Prop :=
  ∀ f tf, transl_fundef f = .OK tf → CM.funsig tf = CS.funsig f

def perm_freelistStatement : Prop :=
  ∀ fbl m m' b ofs k p,
    Mem.free_list m fbl = some m' →
    Mem.perm m' b ofs k p → Mem.perm m b ofs k p

def nextblock_freelistStatement : Prop :=
  ∀ fbl m m', Mem.free_list m fbl = some m' →
    m'.nextblock = m.nextblock

def free_list_freeableStatement : Prop :=
  ∀ l m m', Mem.free_list m l = some m' →
    ∀ b lo hi, In (b, lo, hi) l → Mem.range_perm m b lo hi .Cur .Freeable

def match_temps_invariantStatement : Prop :=
  ∀ f f' le te, match_temps f le te → inject_incr f f' →
    match_temps f' le te

def match_temps_assignStatement : Prop :=
  ∀ f le te id v tv, match_temps f le te → Val.inject f v tv →
    match_temps f (PTree.set id v le) (PTree.set id tv te)

def match_env_invariantStatement : Prop :=
  ∀ f1 cenv e sp lo hi f2,
    match_env f1 cenv e sp lo hi →
    inject_incr f1 f2 →
    (∀ b delta, f2 b = some (sp, delta) → f1 b = some (sp, delta)) →
    (∀ b, Plt b lo → f2 b = f1 b) →
    match_env f2 cenv e sp lo hi

def match_env_allocStatement : Prop :=
  ∀ f1 id cenv e sp lo m1 sz m2 b ofs f2,
    match_env f1 (PTree.remove id cenv) e sp lo m1.nextblock →
    Mem.alloc m1 0 sz = (m2, b) →
    PTree.get id cenv = some ofs →
    inject_incr f1 f2 →
    f2 b = some (sp, ofs) →
    (∀ b', b' ≠ b → f2 b' = f1 b') →
    PTree.get id e = none →
    match_env f2 cenv (PTree.set id (b, sz) e) sp lo m2.nextblock

def match_bounds_invariantStatement : Prop :=
  ∀ e m1 m2, match_bounds e m1 →
    (∀ id b sz ofs p,
      PTree.get id e = some (b, sz) →
      Mem.perm m2 b ofs .Max p → Mem.perm m1 b ofs .Max p) →
    match_bounds e m2

def padding_freeable_invariantStatement : Prop :=
  ∀ f1 e tm1 sp sz cenv lo hi f2 tm2,
    padding_freeable f1 e tm1 sp sz →
    match_env f1 cenv e sp lo hi →
    (∀ ofs, Mem.perm tm1 sp ofs .Cur .Freeable →
      Mem.perm tm2 sp ofs .Cur .Freeable) →
    (∀ b, Plt b hi → f2 b = f1 b) →
    padding_freeable f2 e tm2 sp sz

def is_reachable_from_env_decStatement : Prop :=
  ∀ f e sp ofs,
    is_reachable_from_env f e sp ofs ∨ ¬ is_reachable_from_env f e sp ofs

def inj_preserves_globalsStatement : Prop :=
  ∀ prog f hi, match_globalenvs prog f hi →
    meminj_preserves_globals CS.fundef Unit (sourceGenv prog) f

def match_callstack_match_globalenvsStatement : Prop :=
  ∀ prog f m tm cs bound tbound,
    match_callstack prog f m tm cs bound tbound →
    ∃ hi, match_globalenvs prog f hi

def match_callstack_invariantStatement : Prop :=
  ∀ prog f1 m1 tm1 f2 m2 tm2 cs bound tbound,
    match_callstack prog f1 m1 tm1 cs bound tbound →
    inject_incr f1 f2 →
    (∀ b ofs p, Plt b bound → Mem.perm m2 b ofs .Max p →
      Mem.perm m1 b ofs .Max p) →
    (∀ sp ofs, Plt sp tbound → Mem.perm tm1 sp ofs .Cur .Freeable →
      Mem.perm tm2 sp ofs .Cur .Freeable) →
    (∀ b, Plt b bound → f2 b = f1 b) →
    (∀ b b' delta, f2 b = some (b', delta) → Plt b' tbound →
      f1 b = some (b', delta)) →
    match_callstack prog f2 m2 tm2 cs bound tbound

def match_callstack_incr_boundStatement : Prop :=
  ∀ prog f m tm cs bound tbound bound' tbound',
    match_callstack prog f m tm cs bound tbound →
    Ple bound bound' → Ple tbound tbound' →
    match_callstack prog f m tm cs bound' tbound'

def match_callstack_set_tempStatement : Prop :=
  ∀ prog f cenv e le te sp lo hi cs bound tbound m tm tf id v tv,
    Val.inject f v tv →
    match_callstack prog f m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound →
    match_callstack prog f m tm
      (Frame cenv tf e (PTree.set id v le) (PTree.set id tv te) sp lo hi :: cs)
      bound tbound

def in_blocks_of_envStatement : Prop :=
  ∀ e id b sz, PTree.get id e = some (b, sz) →
    In (b, 0, sz) (CS.blocks_of_env e)

def match_callstack_freelistStatement : Prop :=
  ∀ prog f cenv tf e le te sp lo hi cs m m' tm,
    Mem.inject f m tm →
    Mem.free_list m (CS.blocks_of_env e) = some m' →
    match_callstack prog f m tm (Frame cenv tf e le te sp lo hi :: cs)
      m.nextblock tm.nextblock →
    ∃ tm', Mem.free tm sp 0 tf.fn_stackspace = some tm' ∧
      match_callstack prog f m' tm' cs m'.nextblock tm'.nextblock ∧
      Mem.inject f m' tm'

def match_callstack_external_callStatement : Prop :=
  ∀ prog f1 f2 m1 m2 m1' m2',
    Mem.unchanged_on (loc_unmapped f1) m1 m2 →
    Mem.unchanged_on (loc_out_of_reach f1 m1) m1' m2' →
    inject_incr f1 f2 →
    inject_separated f1 f2 m1 m1' →
    (∀ b ofs p, Mem.valid_block m1 b → Mem.perm m2 b ofs .Max p →
      Mem.perm m1 b ofs .Max p) →
    ∀ cs bound tbound,
      match_callstack prog f1 m1 m1' cs bound tbound →
      Ple bound m1.nextblock → Ple tbound m1'.nextblock →
      match_callstack prog f2 m2 m2' cs bound tbound

def match_callstack_alloc_rightStatement : Prop :=
  ∀ prog f m tm cs tf tm' sp le te cenv,
    match_callstack prog f m tm cs m.nextblock tm.nextblock →
    Mem.alloc tm 0 tf.fn_stackspace = (tm', sp) →
    Mem.inject f m tm →
    match_temps f le te →
    (∀ id, PTree.get id cenv = none) →
    match_callstack prog f m tm'
      (Frame cenv tf CS.empty_env le te sp m.nextblock m.nextblock :: cs)
      m.nextblock tm'.nextblock

def match_callstack_alloc_leftStatement : Prop :=
    ∀ prog f1 m1 tm id cenv tf e le te sp lo cs sz m2 b f2 ofs,
    match_callstack prog f1 m1 tm
      (Frame (PTree.remove id cenv) tf e le te sp lo m1.nextblock :: cs)
      m1.nextblock tm.nextblock →
    Mem.alloc m1 0 sz = (m2, b) →
    PTree.get id cenv = some ofs →
    inject_incr f1 f2 →
    f2 b = some (sp, ofs) →
    (∀ b', b' ≠ b → f2 b' = f1 b') →
    PTree.get id e = none →
    match_callstack prog f2 m2 tm
      (Frame cenv tf (PTree.set id (b, sz) e) le te sp lo m2.nextblock :: cs)
      m2.nextblock tm.nextblock

def cenv_remove_gsoStatement : Prop :=
  ∀ id vars cenv,
    ¬ In id (List.map Prod.fst vars) →
    PTree.get id (cenv_remove cenv vars) = PTree.get id cenv

def cenv_remove_gssStatement : Prop :=
  ∀ id vars cenv,
    In id (List.map Prod.fst vars) →
    PTree.get id (cenv_remove cenv vars) = none

def match_callstack_alloc_variables_recStatement : Prop :=
  ∀ prog tm sp tf cenv le te lo cs,
    Mem.valid_block tm sp →
    tf.fn_stackspace ≤ Ptrofs.max_unsigned →
    (∀ ofs k p, Mem.perm tm sp ofs k p → 0 ≤ ofs ∧ ofs < tf.fn_stackspace) →
    (∀ ofs k p, 0 ≤ ofs ∧ ofs < tf.fn_stackspace → Mem.perm tm sp ofs k p) →
    ∀ e1 m1 vars e2 m2,
      CS.alloc_variables e1 m1 vars e2 m2 →
      ∀ f1,
        CompCert4Lean.Lib.Coqlib.list_norepet (List.map Prod.fst vars) →
        cenv_compat cenv vars tf.fn_stackspace →
        cenv_separated cenv vars →
        cenv_mem_separated cenv vars f1 sp m1 →
        (∀ id sz, In (id, sz) vars → PTree.get id e1 = none) →
        match_callstack prog f1 m1 tm
          (Frame (cenv_remove cenv vars) tf e1 le te sp lo m1.nextblock :: cs)
          m1.nextblock tm.nextblock →
        Mem.inject f1 m1 tm →
        ∃ f2,
          match_callstack prog f2 m2 tm
            (Frame cenv tf e2 le te sp lo m2.nextblock :: cs)
            m2.nextblock tm.nextblock ∧
          Mem.inject f2 m2 tm

def match_callstack_alloc_variablesStatement : Prop :=
  ∀ prog tm1 sp tm2 m1 vars e m2 cenv f1 cs fn le te,
    Mem.alloc tm1 0 fn.fn_stackspace = (tm2, sp) →
    fn.fn_stackspace ≤ Ptrofs.max_unsigned →
    CS.alloc_variables CS.empty_env m1 vars e m2 →
    CompCert4Lean.Lib.Coqlib.list_norepet (List.map Prod.fst vars) →
    cenv_compat cenv vars fn.fn_stackspace →
    cenv_separated cenv vars →
    (∀ id ofs, PTree.get id cenv = some ofs → In id (List.map Prod.fst vars)) →
    Mem.inject f1 m1 tm1 →
    match_callstack prog f1 m1 tm1 cs m1.nextblock tm1.nextblock →
    match_temps f1 le te →
    ∃ f2,
      match_callstack prog f2 m2 tm2
        (Frame cenv fn e le te sp m1.nextblock m2.nextblock :: cs)
        m2.nextblock tm2.nextblock ∧
      Mem.inject f2 m2 tm2

def block_alignment_posStatement : Prop :=
  ∀ sz, 0 < block_alignment sz

def assign_variable_incrStatement : Prop :=
  ∀ id sz cenv stksz cenv' stksz',
    assign_variable (cenv, stksz) (id, sz) = (cenv', stksz') →
    stksz ≤ stksz'

def inj_offset_aligned_blockStatement : Prop :=
  ∀ stacksize sz,
    Mem.inj_offset_aligned (align stacksize (block_alignment sz)) sz

def assign_variable_soundStatement : Prop :=
  ∀ cenv1 sz1 id sz cenv2 sz2 vars,
    assign_variable (cenv1, sz1) (id, sz) = (cenv2, sz2) →
    ¬ In id (List.map Prod.fst vars) →
    0 ≤ sz1 →
    cenv_compat cenv1 vars sz1 →
    cenv_separated cenv1 vars →
    cenv_compat cenv2 (vars ++ [(id, sz)]) sz2 ∧
      cenv_separated cenv2 (vars ++ [(id, sz)])

def assign_variables_soundStatement : Prop :=
  ∀ vars' cenv1 sz1 cenv2 sz2 vars,
    assign_variables (cenv1, sz1) vars' = (cenv2, sz2) →
    CompCert4Lean.Lib.Coqlib.list_norepet
      (List.map Prod.fst vars' ++ List.map Prod.fst vars) →
    0 ≤ sz1 →
    cenv_compat cenv1 vars sz1 →
    cenv_separated cenv1 vars →
    cenv_compat cenv2 (vars ++ vars') sz2 ∧ cenv_separated cenv2 (vars ++ vars')

def permutation_norepetStatement : Prop :=
  ∀ (A : Type) (l l' : List A),
    Permutation l l' →
    CompCert4Lean.Lib.Coqlib.list_norepet l →
    CompCert4Lean.Lib.Coqlib.list_norepet l'

def build_compilenv_soundStatement : Prop :=
  ∀ f cenv sz,
    build_compilenv f = (cenv, sz) →
    CompCert4Lean.Lib.Coqlib.list_norepet (List.map Prod.fst f.fn_vars) →
    cenv_compat cenv f.fn_vars sz ∧ cenv_separated cenv f.fn_vars

def assign_variables_domainStatement : Prop :=
  ∀ id vars cesz,
    PTree.get id (assign_variables cesz vars).1 ≠ none →
    PTree.get id cesz.1 ≠ none ∨ In id (List.map Prod.fst vars)

def build_compilenv_domainStatement : Prop :=
  ∀ f cenv sz id ofs,
    build_compilenv f = (cenv, sz) →
    PTree.get id cenv = some ofs → In id (List.map Prod.fst f.fn_vars)

def create_undef_temps_valStatement : Prop :=
  ∀ id v temps,
    PTree.get id (CS.create_undef_temps temps) = some v →
    In id temps ∧ v = .Vundef

def bind_parameters_agree_recStatement : Prop :=
  ∀ f vars vals tvals le1 le2 te,
    CS.bind_parameters vars vals le1 = some le2 →
    Val.inject_list f vals tvals →
    match_temps f le1 te →
    match_temps f le2 (set_params' tvals vars te)

def set_params'_outsideStatement : Prop :=
  ∀ id il vl te, ¬ In id il →
    PTree.get id (set_params' vl il te) = PTree.get id te

def set_params'_insideStatement : Prop :=
  ∀ id il vl te1 te2, In id il →
    PTree.get id (set_params' vl il te1) = PTree.get id (set_params' vl il te2)

def set_params_set_params'Statement : Prop :=
  ∀ il vl id,
    CompCert4Lean.Lib.Coqlib.list_norepet il →
    PTree.get id (CM.set_params vl il) =
      PTree.get id (set_params' vl il (PTree.empty val))

def set_locals_outsideStatement : Prop :=
  ∀ e id il, ¬ In id il →
    PTree.get id (CM.set_locals il e) = PTree.get id e

def set_locals_insideStatement : Prop :=
  ∀ e id il, In id il →
    PTree.get id (CM.set_locals il e) = some .Vundef

def set_locals_set_params'Statement : Prop :=
  ∀ vars vals params id,
    CompCert4Lean.Lib.Coqlib.list_norepet params →
    list_disjoint params vars →
    PTree.get id (CM.set_locals vars (CM.set_params vals params)) =
      PTree.get id (set_params' vals params (CM.set_locals vars (PTree.empty val)))

def bind_parameters_agreeStatement : Prop :=
  ∀ f params temps vals tvals le,
    CS.bind_parameters params vals (CS.create_undef_temps temps) = some le →
    Val.inject_list f vals tvals →
    CompCert4Lean.Lib.Coqlib.list_norepet params →
    list_disjoint params temps →
    match_temps f le (CM.set_locals temps (CM.set_params tvals params))

def match_callstack_function_entryStatement : Prop :=
  ∀ prog fn cenv tf m e m' tm tm' sp f cs args targs le,
    build_compilenv fn = (cenv, tf.fn_stackspace) →
    tf.fn_stackspace ≤ Ptrofs.max_unsigned →
    CompCert4Lean.Lib.Coqlib.list_norepet (List.map Prod.fst fn.fn_vars) →
    CompCert4Lean.Lib.Coqlib.list_norepet fn.fn_params →
    list_disjoint fn.fn_params fn.fn_temps →
    CS.alloc_variables CS.empty_env m fn.fn_vars e m' →
    CS.bind_parameters fn.fn_params args (CS.create_undef_temps fn.fn_temps) = some le →
    Val.inject_list f args targs →
    Mem.alloc tm 0 tf.fn_stackspace = (tm', sp) →
    match_callstack prog f m tm cs m.nextblock tm.nextblock →
    Mem.inject f m tm →
    let te := CM.set_locals fn.fn_temps (CM.set_params targs fn.fn_params)
    ∃ f',
      match_callstack prog f' m' tm'
        (Frame cenv tf e le te sp m.nextblock m'.nextblock :: cs)
        m'.nextblock tm'.nextblock ∧
      Mem.inject f' m' tm'

def val_inject_val_of_boolStatement : Prop :=
  ∀ f b, Val.inject f (Val.of_bool b) (Val.of_bool b)

def val_inject_val_of_optboolStatement : Prop :=
  ∀ f ob, Val.inject f (Val.of_optbool ob) (Val.of_optbool ob)

def eval_unop_compatStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ f op v1 tv1 v,
    CM.eval_unop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) op v1 = some v →
    Val.inject f v1 tv1 →
    ∃ tv, CM.eval_unop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) op tv1 = some tv ∧ Val.inject f v tv

def eval_binop_compatStatement : Prop :=
  ∀ f op v1 tv1 v2 tv2 v m tm,
    CM.eval_binop op v1 v2 m = some v →
    Val.inject f v1 tv1 →
    Val.inject f v2 tv2 →
    Mem.inject f m tm →
    ∃ tv, CM.eval_binop op tv1 tv2 tm = some tv ∧ Val.inject f v tv

def var_addr_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ prog tprog, match_prog prog tprog →
    ∀ cenv id f tf e le te sp lo hi m cs tm b,
      match_callstack prog f m tm (Frame cenv tf e le te sp lo hi :: cs)
        m.nextblock tm.nextblock →
      CS.eval_var_addr (sourceGenv prog) e id b →
      ∃ tv,
        CM.eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (targetGenv tprog) (.Vptr sp Ptrofs.zero) te tm (var_addr cenv id) tv ∧
        Val.inject f (.Vptr b Ptrofs.zero) tv

def bool_of_val_injectStatement : Prop :=
  ∀ f v tv b,
    Val.bool_of_val v b → Val.inject f v tv → Val.bool_of_val tv b

def transl_constant_correctStatement : Prop :=
  ∀ tprog f sp cst v,
    CS.eval_constant cst = some v →
    ∃ tv,
      CM.eval_constant (targetGenv tprog) sp (transl_constant cst) = some tv ∧
      Val.inject f v tv

def transl_expr_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ prog tprog, match_prog prog tprog →
    ∀ f m tm cenv tf e le te sp lo hi cs,
      Mem.inject f m tm →
      match_callstack prog f m tm (Frame cenv tf e le te sp lo hi :: cs)
        m.nextblock tm.nextblock →
      ∀ a v,
        CS.eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (sourceGenv prog) e le m a v →
        ∀ ta, transl_expr cenv a = .OK ta →
          ∃ tv,
            CM.eval_expr
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              (targetGenv tprog) (.Vptr sp Ptrofs.zero) te tm ta tv ∧
            Val.inject f v tv

def transl_exprlist_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ prog tprog, match_prog prog tprog →
    ∀ f m tm cenv tf e le te sp lo hi cs,
      Mem.inject f m tm →
      match_callstack prog f m tm (Frame cenv tf e le te sp lo hi :: cs)
        m.nextblock tm.nextblock →
      ∀ a v,
        CS.eval_exprlist
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (sourceGenv prog) e le m a v →
        ∀ ta, transl_exprlist cenv a = .OK ta →
          ∃ tv,
            CM.eval_exprlist
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              (targetGenv tprog) (.Vptr sp Ptrofs.zero) te tm ta tv ∧
            Val.inject_list f v tv

def val_inject_function_pointerStatement : Prop :=
  ∀ prog bound v fd f tv,
    Genv.find_funct (sourceGenv prog) v = some fd →
    match_globalenvs prog f bound →
    Val.inject f v tv → tv = v

def match_call_contStatement : Prop :=
  ∀ k tk cenv xenv cs,
    match_cont k tk cenv xenv cs →
    match_cont (CS.call_cont k) (CM.call_cont tk) cenv [] cs

def match_is_call_contStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) tprog tfn te sp tm k tk cenv xenv cs,
    match_cont k tk cenv xenv cs →
    CS.is_call_cont k →
    ∃ tk',
      star (CM.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi) (targetGenv tprog)
        (.State tfn .Sskip tk sp te tm) E0
        (.State tfn .Sskip tk' sp te tm) ∧
      CM.is_call_cont tk' ∧
      match_cont k tk' cenv [] cs

def switch_table_defaultStatement : Prop :=
  ∀ sl base,
    ∃ n, lbl_stmt_tail sl n (CS.select_switch_default sl) ∧
      (switch_table sl base).2 = n + base

def switch_table_caseStatement : Prop :=
  ∀ i sl base dfl,
    match CS.select_switch_case i sl with
    | none => switch_target i dfl (switch_table sl base).1 = dfl
    | some sl' =>
        ∃ n, lbl_stmt_tail sl n sl' ∧
          switch_target i dfl (switch_table sl base).1 = n + base

def switch_table_selectStatement : Prop :=
  ∀ i sl,
    lbl_stmt_tail sl
      (switch_target i (switch_table sl 0).2 (switch_table sl 0).1)
      (CS.select_switch i sl)

def switch_descentStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) tprog cenv xenv k ls body s,
    transl_lblstmt cenv (switch_env ls xenv) ls body = .OK s →
    ∃ k', transl_lblstmt_cont cenv xenv ls k k' ∧
      ∀ f sp e m,
        plus (CM.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) (targetGenv tprog)
          (.State f s k sp e m) E0 (.State f body k' sp e m)

def switch_ascentStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) tprog f sp e m cenv xenv ls n ls',
    lbl_stmt_tail ls n ls' →
    ∀ k k1, transl_lblstmt_cont cenv xenv ls k k1 →
      ∃ k2,
        star (CM.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) (targetGenv tprog)
          (.State f (.Sexit n) k1 sp e m) E0
          (.State f (.Sexit 0) k2 sp e m) ∧
        transl_lblstmt_cont cenv xenv ls' k k2

def switch_match_contStatement : Prop :=
  ∀ cenv xenv k cs tk ls tk',
    match_cont k tk cenv xenv cs →
    transl_lblstmt_cont cenv xenv ls tk tk' →
    match_cont (.Kseq (CS.seq_of_lbl_stmt ls) k) tk' cenv
      (false :: switch_env ls xenv) cs

def switch_match_statesStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) prog tprog
      fn k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz ls body tk',
    transl_funbody cenv sz fn = .OK tfn →
    transl_lblstmt cenv (switch_env ls xenv) ls body = .OK ts →
    Mem.inject f m tm →
    match_callstack prog f m tm (Frame cenv tfn e le te sp lo hi :: cs)
      m.nextblock tm.nextblock →
    match_cont k tk cenv xenv cs →
    transl_lblstmt_cont cenv xenv ls tk tk' →
    ∃ S,
      plus (CM.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi) (targetGenv tprog)
        (.State tfn (.Sexit 0) tk' (.Vptr sp Ptrofs.zero) te tm) E0 S ∧
      match_states prog (.State fn (CS.seq_of_lbl_stmt ls) k e le m) S

def transl_lblstmt_suffixStatement : Prop :=
  ∀ cenv xenv ls n ls',
    lbl_stmt_tail ls n ls' →
    ∀ body ts, transl_lblstmt cenv (switch_env ls xenv) ls body = .OK ts →
      ∃ body' ts', transl_lblstmt cenv (switch_env ls' xenv) ls' body' = .OK ts'

def transl_find_labelStatement : Prop :=
  ∀ (_tprog : CM.program) lbl cenv cs s k xenv ts tk,
    transl_stmt cenv xenv s = .OK ts →
    match_cont k tk cenv xenv cs →
    match CS.find_label lbl s k with
    | none => CM.find_label lbl ts tk = none
    | some (s', k') =>
        ∃ ts' tk' xenv',
          CM.find_label lbl ts tk = some (ts', tk') ∧
          transl_stmt cenv xenv' s' = .OK ts' ∧
          match_cont k' tk' cenv xenv' cs

def transl_find_label_bodyStatement : Prop :=
  ∀ (_tprog : CM.program) cenv xenv size f tf k tk cs lbl s' k',
    transl_funbody cenv size f = .OK tf →
    match_cont k tk cenv xenv cs →
    CS.find_label lbl f.fn_body (CS.call_cont k) = some (s', k') →
    ∃ ts' tk' xenv',
      CM.find_label lbl tf.fn_body (CM.call_cont tk) = some (ts', tk') ∧
      transl_stmt cenv xenv' s' = .OK ts' ∧
      match_cont k' tk' cenv xenv' cs

def transl_step_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) prog tprog, match_prog prog tprog →
    ∀ S1 t S2,
      CS.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (sourceGenv prog) S1 t S2 →
      ∀ T1, match_states prog S1 T1 →
        (∃ T2,
          plus (CM.step
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi) (targetGenv tprog)
            T1 t T2 ∧ match_states prog S2 T2) ∨
        (measure S2 < measure S1 ∧ t = E0 ∧ match_states prog S2 T1)

def match_globalenvs_initStatement : Prop :=
  ∀ prog m, Genv.init_mem prog = some m →
    match_globalenvs prog (Mem.flat_inj m.nextblock) m.nextblock

def transl_initial_statesStatement : Prop :=
  ∀ prog tprog, match_prog prog tprog →
    ∀ S, CS.initial_state prog S →
      ∃ R, CM.initial_state tprog R ∧ match_states prog S R

def transl_final_statesStatement : Prop :=
  ∀ prog S R r,
    match_states prog S R → CS.final_state S r → CM.final_state R r

def transl_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) prog tprog, match_prog prog tprog →
    forward_simulation
      (CS.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog)
      (CM.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tprog)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

theorem sig_preserved_body : sig_preserved_bodyStatement := by
  intro f tf cenv size h
  unfold CompCert4Lean.Cfrontend.Cminorgen.transl_funbody at h
  cases htrans : CompCert4Lean.Cfrontend.Cminorgen.transl_stmt cenv [] f.fn_body with
  | Error msg => simp [htrans] at h
  | OK body =>
      simp [htrans] at h
      cases h
      rfl

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

theorem transf_program_match : transf_program_matchStatement := by
  intro p tp h
  letI : CompCert4Lean.Common.Linking.Linker CS.fundef :=
    @CompCert4Lean.Common.Linking.Linker_fundef CS.function
  letI : CompCert4Lean.Common.Linking.Linker CS.program :=
    @CompCert4Lean.Common.Linking.Linker_prog CS.fundef Unit _ _
  have aux : ∀ (defs : List (ident × CompCert4Lean.Common.AST.globdef CS.fundef Unit))
      (tdefs : List (ident × CompCert4Lean.Common.AST.globdef
        CompCert4Lean.Backend.Cminor.fundef Unit)),
      CompCert4Lean.Common.AST.transf_globdefs
          (fun _ f => CompCert4Lean.Cfrontend.Cminorgen.transl_fundef f)
          (fun _ v => .OK v) defs = .OK tdefs →
      CompCert4Lean.Lib.Coqlib.list_forall2
        (CompCert4Lean.Common.Linking.match_ident_globdef
          (fun _ f tf => CompCert4Lean.Cfrontend.Cminorgen.transl_fundef f = .OK tf)
          Eq p) defs tdefs := by
    intro defs
    induction defs with
    | nil =>
        intro tdefs hdefs
        simp [CompCert4Lean.Common.AST.transf_globdefs] at hdefs
        cases hdefs
        exact CompCert4Lean.Lib.Coqlib.list_forall2.nil _
    | cons d ds ih =>
        intro tdefs hdefs
        cases d with
        | mk id gd =>
            cases gd with
            | Gfun f =>
                unfold CompCert4Lean.Common.AST.transf_globdefs at hdefs
                cases htf : CompCert4Lean.Cfrontend.Cminorgen.transl_fundef f with
                | Error msg => simp [htf] at hdefs
                | OK tf =>
                    cases hrest : CompCert4Lean.Common.AST.transf_globdefs
                      (fun _ f => CompCert4Lean.Cfrontend.Cminorgen.transl_fundef f)
                      (fun _ v => .OK v) ds with
                    | Error msg => simp [htf, hrest] at hdefs
                    | OK rest =>
                        simp [htf, hrest] at hdefs
                        cases hdefs
                        apply CompCert4Lean.Lib.Coqlib.list_forall2.cons
                        · constructor
                          · rfl
                          · exact CompCert4Lean.Common.Linking.match_globdef_fun _ _ _ _ _ _
                              (CompCert4Lean.Common.Linking.Linker.linkorder_refl p) htf
                        · exact ih rest hrest
            | Gvar v =>
                unfold CompCert4Lean.Common.AST.transf_globdefs at hdefs
                simp [CompCert4Lean.Common.AST.transf_globvar] at hdefs
                cases hrest : CompCert4Lean.Common.AST.transf_globdefs
                  (fun _ f => CompCert4Lean.Cfrontend.Cminorgen.transl_fundef f)
                  (fun _ v => .OK v) ds with
                | Error msg => simp [hrest] at hdefs
                | OK rest =>
                    simp [hrest] at hdefs
                    cases hdefs
                    apply CompCert4Lean.Lib.Coqlib.list_forall2.cons
                    · constructor
                      · rfl
                      · apply CompCert4Lean.Common.Linking.match_globdef_var
                        apply CompCert4Lean.Common.Linking.match_globvar_intro
                        rfl
                    · exact ih rest hrest
  unfold CompCert4Lean.Cfrontend.Cminorgen.transl_program at h
  unfold match_prog
  unfold CompCert4Lean.Common.AST.transform_partial_program
    CompCert4Lean.Common.AST.transform_partial_program2 at h
  cases hdefs : CompCert4Lean.Common.AST.transf_globdefs
      (fun _ f => CompCert4Lean.Cfrontend.Cminorgen.transl_fundef f)
      (fun _ v => .OK v) p.prog_defs with
  | Error msg => simp [hdefs] at h
  | OK defs =>
      simp [hdefs] at h
      cases h
      exact ⟨aux _ _ hdefs, rfl, rfl⟩

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem cminorgenproof_add_global_match
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W)
    (h : Genv.match_genvs R ge1 ge2)
    (id : ident) (g1 : globdef A V) (g2 : globdef B W) (hr : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1)) (Genv.add_global ge2 (id, g2)) := by
  change positive at id
  constructor
  · simp only [Genv.add_global]
    change PArith.BinPos.Pos.succ ge2.genv_next = PArith.BinPos.Pos.succ ge1.genv_next
    exact congrArg _ h.mge_next
  · intro id'
    simp only [Genv.add_global]
    change PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb)
    have hx2 := @PTree.gsspec_proof _ id' id ge2.genv_next ge2.genv_symb
    have hx1 := @PTree.gsspec_proof _ id' id ge1.genv_next ge1.genv_symb
    cases heq : peq id' id with
    | left hij =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            some ge2.genv_next := by
          simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            some ge1.genv_next := by
          simpa [heq] using hx1
        rw [hx2', hx1', h.mge_next]
    | right hne =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            PTree.get id' ge2.genv_symb := by
          simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            PTree.get id' ge1.genv_symb := by
          simpa [heq] using hx1
        rw [hx2', hx1', h.mge_symb]
  · intro b
    simp only [Genv.add_global]
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have hx1 := @PTree.gsspec_proof _ b ge1.genv_next g1 ge1.genv_defs
    have hx2 := @PTree.gsspec_proof _ b ge2.genv_next g2 ge2.genv_defs
    cases heq : peq b ge1.genv_next with
    | left hb =>
        have heq' : b = ge2.genv_next := hb.trans h.mge_next.symm
        cases hpeq2 : peq b ge2.genv_next with
        | left hb2 =>
            have hx1' : PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs) =
                some g1 := by
              simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                some g2 := by
              simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact option_rel.some g1 g2 hr
        | right hb2 => exact False.elim (hb2 heq')
    | right hb =>
        have hb2 : b ≠ ge2.genv_next := by
          intro hbeq
          apply hb
          exact hbeq.trans h.mge_next
        cases hpeq2 : peq b ge2.genv_next with
        | left hb2' => exact False.elim (hb (hb2'.trans h.mge_next))
        | right hb2' =>
            have hx1' : PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs) =
                PTree.get b ge1.genv_defs := by
              simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                PTree.get b ge2.genv_defs := by
              simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact h.mge_defs b

private theorem cminorgenproof_add_globals_match
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (gl1 : List (ident × globdef A V)) (gl2 : List (ident × globdef B W))
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) :
    list_forall2 (fun x y => x.1 = y.1 ∧ R x.2 y.2) gl1 gl2 →
    Genv.match_genvs R ge1 ge2 →
    Genv.match_genvs R (Genv.add_globals ge1 gl1) (Genv.add_globals ge2 gl2) := by
  intro hlist hge
  induction hlist generalizing ge1 ge2 with
  | nil => exact hge
  | cons hd1 hd2 hhd htl ih =>
      rcases hhd with ⟨hid, hrel⟩
      cases hd1 with
      | mk id1 gd1 =>
          cases hd2 with
          | mk id2 gd2 =>
              simp only [Genv.add_globals, List.foldl]
              change id1 = id2 at hid
              subst id2
              exact ih
                (Genv.add_global ge1 (id1, gd1))
                (Genv.add_global ge2 (id1, gd2))
                (cminorgenproof_add_global_match R ge1 ge2 hge id1 gd1 gd2 hrel)

private theorem cminorgenproof_globalenvs_match
    {A B V : Type} [Linker A] [Linker V]
    (transf : A → CompCert4Lean.Common.Errors.res B) (p : program A V) (tp : program B V)
    (hmatch : match_program (fun _ f tf => transf f = .OK tf) Eq p tp) :
    Genv.match_genvs
      (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
      (Genv.globalenv p) (Genv.globalenv tp) := by
  have hempty : Genv.match_genvs
      (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
      (Genv.empty_genv A V p.prog_public) (Genv.empty_genv B V tp.prog_public) := by
    constructor
    · rfl
    · intro id
      rfl
    · intro b
      exact option_rel.none _
  exact cminorgenproof_add_globals_match
    (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
    p.prog_defs tp.prog_defs
    (Genv.empty_genv A V p.prog_public) (Genv.empty_genv B V tp.prog_public)
    hmatch.1 hempty
theorem symbols_preserved : symbols_preservedStatement := by
  intro prog tprog hmatch s
  letI : CompCert4Lean.Common.Linking.Linker CS.fundef :=
    @CompCert4Lean.Common.Linking.Linker_fundef CS.function
  letI : CompCert4Lean.Common.Linking.Linker CS.program :=
    @CompCert4Lean.Common.Linking.Linker_prog CS.fundef Unit _ _
  have hgenv := cminorgenproof_globalenvs_match
    (A := CS.fundef) (B := CompCert4Lean.Backend.Cminor.fundef) (V := Unit)
    (transf := fun f => CompCert4Lean.Cfrontend.Cminorgen.transl_fundef f)
    (p := prog) (tp := tprog) hmatch
  exact hgenv.mge_symb s

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem senv_preserved : senv_preservedStatement := by
  intro prog tprog hmatch
  letI : CompCert4Lean.Common.Linking.Linker CS.fundef :=
    @CompCert4Lean.Common.Linking.Linker_fundef CS.function
  letI : CompCert4Lean.Common.Linking.Linker CS.program :=
    @CompCert4Lean.Common.Linking.Linker_prog CS.fundef Unit _ _
  have hgenv := cminorgenproof_globalenvs_match
    (A := CS.fundef) (B := CompCert4Lean.Backend.Cminor.fundef) (V := Unit)
    (transf := fun f => CompCert4Lean.Cfrontend.Cminorgen.transl_fundef f)
    (p := prog) (tp := tprog) hmatch
  constructor
  · intro id
    exact hgenv.mge_symb id
  constructor
  · intro id
    have hpub_general : ∀ (F V : Type) (gl : List (ident × globdef F V))
        (ge : Genv.t F V),
        (Genv.add_globals ge gl).genv_public = ge.genv_public := by
      intro F V gl ge
      induction gl generalizing ge with
      | nil => rfl
      | cons hd tl ih =>
          simp only [Genv.add_globals, List.foldl]
          exact ih (Genv.add_global ge hd)
    have hpub : (Genv.globalenv tprog).genv_public =
        (Genv.globalenv prog).genv_public := by
      have htpub : (Genv.globalenv tprog).genv_public = tprog.prog_public := by
        simpa [Genv.globalenv] using
          hpub_general _ _ tprog.prog_defs (Genv.empty_genv _ _ tprog.prog_public)
            |>.trans (by rfl)
      have hspub : (Genv.globalenv prog).genv_public = prog.prog_public := by
        simpa [Genv.globalenv] using
          hpub_general _ _ prog.prog_defs (Genv.empty_genv _ _ prog.prog_public)
            |>.trans (by rfl)
      exact htpub.trans (hmatch.2.2.trans hspub.symm)
    have hsymb : PTree.get id (Genv.globalenv tprog).genv_symb =
        PTree.get id (Genv.globalenv prog).genv_symb := hgenv.mge_symb id
    simp only [Genv.to_senv, Genv.public_symbol, Genv.find_symbol]
    rw [hsymb, hpub]
  · intro b
    have hrel := hgenv.mge_defs b
    simp only [Genv.to_senv, Genv.block_is_volatile, Genv.find_var_info,
      Genv.find_def]
    cases hs : PTree.get b (Genv.globalenv prog).genv_defs with
    | none =>
        have ht : PTree.get b (Genv.globalenv tprog).genv_defs = none := by
          cases ht' : PTree.get b (Genv.globalenv tprog).genv_defs with
          | none => rfl
          | some gd =>
              have hh := hrel
              rw [hs, ht'] at hh
              cases hh
        simp [hs, ht]
    | some gd =>
        cases gd with
        | Gfun f =>
            cases ht : PTree.get b (Genv.globalenv tprog).genv_defs with
            | none =>
                have hh := hrel
                rw [hs, ht] at hh
            | some gd2 =>
                have hh := hrel
                rw [hs, ht] at hh
                cases hh with
                | some _ _ hgd =>
                    cases gd2 with
                    | Gfun tf => simp [hs, ht]
                    | Gvar gv => cases hgd
        | Gvar gv =>
            cases ht : PTree.get b (Genv.globalenv tprog).genv_defs with
            | none =>
                have hh := hrel
                rw [hs, ht] at hh
                cases hh
            | some gd2 =>
                have hh := hrel
                rw [hs, ht] at hh
                cases hh with
                | some _ _ hgd =>
                    cases gd2 with
                    | Gfun tf => cases hgd
                    | Gvar gv2 =>
                        cases hgd with
                        | match_globdef_var _ _ hvar =>
                            cases hvar
                            rfl

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem function_ptr_translated : function_ptr_translatedStatement := by
  intro prog tprog hmatch b f hfind
  letI : CompCert4Lean.Common.Linking.Linker CS.fundef :=
    @CompCert4Lean.Common.Linking.Linker_fundef CS.function
  letI : CompCert4Lean.Common.Linking.Linker CS.program :=
    @CompCert4Lean.Common.Linking.Linker_prog CS.fundef Unit _ _
  have hgenv := cminorgenproof_globalenvs_match
    (A := CS.fundef) (B := CompCert4Lean.Backend.Cminor.fundef) (V := Unit)
    (transf := fun f => CompCert4Lean.Cfrontend.Cminorgen.transl_fundef f)
    (p := prog) (tp := tprog) hmatch
  unfold Genv.find_funct_ptr Genv.find_def at hfind ⊢
  cases hs : PTree.get b (Genv.globalenv prog).genv_defs with
  | none => simp [hs] at hfind
  | some gd =>
      cases hg : gd with
      | Gfun f0 =>
          simp [hs, hg] at hfind
          subst f0
          cases hg
          have hrel := hgenv.mge_defs b
          rw [hs] at hrel
          cases ht : PTree.get b (Genv.globalenv tprog).genv_defs with
          | none =>
              rw [ht] at hrel
              cases hrel
          | some gd2 =>
              rw [ht] at hrel
              cases hrel with
              | some gd1 gd2 hgd =>
                  cases hgd with
                  | match_globdef_fun ctx' f1 f2 horder htrans =>
                      exact ⟨f2, by simp [ht], htrans⟩
      | Gvar gv => simp [hs, hg] at hfind

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem functions_translated : functions_translatedStatement := by
  intro prog tprog hmatch v f hfind
  cases v with
  | Vptr b ofs =>
      simp only [Genv.find_funct] at hfind ⊢
      split at hfind <;> rename_i heq
      · have hptr : Genv.find_funct_ptr (Genv.globalenv prog) b = some f := by
          simpa [heq] using hfind
        obtain ⟨tf, hptrt, htrans⟩ :=
          function_ptr_translated prog tprog hmatch b f hptr
        simp [heq, hptrt]
        exact htrans
      · cases hfind
  | Vundef => simp [Genv.find_funct] at hfind
  | Vint n => simp [Genv.find_funct] at hfind
  | Vlong n => simp [Genv.find_funct] at hfind
  | Vfloat n => simp [Genv.find_funct] at hfind
  | Vsingle n => simp [Genv.find_funct] at hfind

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

private theorem sig_preserved_transl_function :
    ∀ f tf, CompCert4Lean.Cfrontend.Cminorgen.transl_function f =
      CompCert4Lean.Common.Errors.OK tf → tf.fn_sig = f.fn_sig := by
  intro f tf h
  unfold CompCert4Lean.Cfrontend.Cminorgen.transl_function at h
  cases hbuild : CompCert4Lean.Cfrontend.Cminorgen.build_compilenv f with
  | mk cenv stacksize =>
      rw [hbuild] at h
      dsimp at h
      split at h
      next hle => exact sig_preserved_body f tf cenv stacksize h
      next hgt => cases h

theorem sig_preserved : sig_preservedStatement := by
  intro f tf h
  cases f with
  | Internal f =>
      unfold CompCert4Lean.Cfrontend.Cminorgen.transl_fundef at h
      unfold CompCert4Lean.Common.AST.transf_partial_fundef at h
      dsimp at h
      cases htf : CompCert4Lean.Cfrontend.Cminorgen.transl_function f with
      | Error msg => rw [htf] at h; cases h
      | OK tf' =>
          rw [htf] at h
          cases h
          change tf'.fn_sig = f.fn_sig
          exact sig_preserved_transl_function f tf' htf
  | External ef =>
      change CompCert4Lean.Common.Errors.OK
          (CompCert4Lean.Common.AST.External ef) =
        CompCert4Lean.Common.Errors.OK tf at h
      cases h
      rfl

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

private abbrev proofBlock := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
private abbrev proofZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z

private theorem pmap_get_set_same_local {A : Type} (i : proofBlock) (x : A)
    (m : PMap.t A) : PMap.get i (PMap.set i x m) = x := by
  change (match PTree.get i (PTree.set i x m.2) with
    | some y => y | none => m.1) = x
  rw [PTree.gsspec_proof]
  cases hpeq : peq i i with
  | left h => simp [hpeq]
  | right h => exact False.elim (h rfl)

private theorem pmap_get_set_other_local {A : Type} (i j : proofBlock) (x : A)
    (m : PMap.t A) (h : i ≠ j) : PMap.get i (PMap.set j x m) = PMap.get i m := by
  change (match PTree.get i (PTree.set j x m.2) with
    | some y => y | none => m.1) =
    (match PTree.get i m.2 with | some y => y | none => m.1)
  rw [PTree.gsspec_proof]
  cases hpeq : peq i j with
  | left hij => exact False.elim (h hij)
  | right hne => simp [hpeq]

private theorem perm_of_free (m m1 : Mem.mem) (b' : proofBlock) (lo hi : proofZ)
    (hfree : Mem.free m b' lo hi = some m1) :
    ∀ (b : proofBlock) (ofs : proofZ)
      (k : CompCert4Lean.Common.Memtype.perm_kind)
      (p : CompCert4Lean.Common.Memtype.permission),
      Mem.perm m1 b ofs k p → Mem.perm m b ofs k p := by
  intro b ofs k p hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm1
    subst m1
    unfold Mem.perm at hp ⊢
    by_cases hb : b = b'
    · subst b
      change Mem.perm_order' ((PMap.get b' (PMap.set b'
        (fun (ofs : proofZ) (k : CompCert4Lean.Common.Memtype.perm_kind) => _)
        m.mem_access)) ofs k) p at hp
      rw [pmap_get_set_same_local] at hp
      split at hp
      · change False at hp
        exact False.elim hp
      · exact hp
    · dsimp [Mem.unchecked_free] at hp
      change Mem.perm_order' ((PMap.get b (PMap.set b'
        (fun (ofs : proofZ) (k : CompCert4Lean.Common.Memtype.perm_kind) => _)
        m.mem_access)) ofs k) p at hp
      rw [pmap_get_set_other_local _ _ _ _ hb] at hp
      exact hp
  next hcond => cases hfree

theorem perm_freelist : perm_freelistStatement := by
  intro fbl
  induction fbl with
  | nil =>
      intro m m' b ofs k p hfree hp
      simp [Mem.free_list] at hfree
      cases hfree
      exact hp
  | cons x rest ih =>
      intro m m' b ofs k p hfree hp
      change (match Mem.free m x.1 x.2.1 x.2.2 with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m' at hfree
      cases hfm : Mem.free m x.1 x.2.1 x.2.2 with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m1 =>
          rw [hfm] at hfree
          have hrest : Mem.free_list m1 rest = some m' := hfree
          have hp1 : Mem.perm m1 b ofs k p := ih m1 m' b ofs k p hrest hp
          exact perm_of_free m m1 x.1 x.2.1 x.2.2 hfm b ofs k p hp1

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory

private theorem nextblock_free_local (m : Mem.mem) (b : proofBlock) (lo hi : proofZ)
    (m' : Mem.mem) (hfree : Mem.free m b lo hi = some m') :
    m'.nextblock = m.nextblock := by
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    subst m'
    rfl
  next hcond =>
    cases hfree

theorem nextblock_freelist : nextblock_freelistStatement := by
  intro fbl
  induction fbl with
  | nil =>
      intro m m' hfree
      simp [Mem.free_list] at hfree
      cases hfree
      rfl
  | cons x rest ih =>
      intro m m' hfree
      change (match Mem.free m x.1 x.2.1 x.2.2 with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m' at hfree
      cases hfm : Mem.free m x.1 x.2.1 x.2.2 with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m1 =>
          rw [hfm] at hfree
          have hrest : Mem.free_list m1 rest = some m' := hfree
          have hnext : m'.nextblock = m1.nextblock := ih m1 m' hrest
          exact hnext.trans (nextblock_free_local m x.1 x.2.1 x.2.2 m1 hfm)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory

private theorem free_range_perm_local (m : Mem.mem) (b : proofBlock) (lo hi : proofZ)
    (m' : Mem.mem) (hfree : Mem.free m b lo hi = some m') :
    Mem.range_perm m b lo hi CompCert4Lean.Common.Memtype.Cur
      CompCert4Lean.Common.Memtype.Freeable := by
  unfold Mem.free at hfree
  cases hr : Mem.range_perm_dec m b lo hi
      CompCert4Lean.Common.Memtype.Cur CompCert4Lean.Common.Memtype.Freeable with
  | left hp =>
      simp [hr] at hfree
      cases hfree
      exact hp
  | right hn =>
      simp [hr] at hfree
      cases hfree.1

theorem free_list_freeable : free_list_freeableStatement := by
  intro l m m' hfree b lo hi hin
  induction l generalizing m m' with
  | nil =>
      cases hin
  | cons a rest ih =>
      cases a with
      | mk b0 zpair =>
          cases zpair with
          | mk lo0 hi0 =>
              change (match Mem.free m b0 lo0 hi0 with
                | none => none
                | some m1 => Mem.free_list m1 rest) = some m' at hfree
              cases hfm : Mem.free m b0 lo0 hi0 with
              | none =>
                  rw [hfm] at hfree
                  cases hfree
              | some m1 =>
                  rw [hfm] at hfree
                  cases (_root_.List.mem_cons.mp hin) with
                  | inl heq =>
                      injection heq with hb hlo
                      subst b
                      cases hlo
                      exact free_range_perm_local m b0 lo hi m1 hfm
                  | inr htail =>
                      have hrest : Mem.free_list m1 rest = some m' := hfree
                      have hrange : Mem.range_perm m1 b lo hi
                          CompCert4Lean.Common.Memtype.Cur
                          CompCert4Lean.Common.Memtype.Freeable :=
                        ih m1 m' hrest htail
                      intro ofs hof
                      exact perm_of_free m m1 b0 lo0 hi0 hfm b ofs
                        CompCert4Lean.Common.Memtype.Cur CompCert4Lean.Common.Memtype.Freeable
                        (hrange ofs hof)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

theorem match_temps_invariant : match_temps_invariantStatement := by
  intro f f' le te hmatch hincr id v hget
  rcases hmatch id v hget with ⟨v', hget', hinject⟩
  refine ⟨v', hget', ?_⟩
  cases hinject with
  | inject_int i => exact .inject_int i
  | inject_long i => exact .inject_long i
  | inject_float x => exact .inject_float x
  | inject_single x => exact .inject_single x
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hoff =>
      exact .inject_ptr b1 ofs1 b2 ofs2 delta (hincr b1 b2 delta hmap) hoff
  | val_inject_undef => exact .val_inject_undef _

end CompCert4Lean.Cfrontend.Cminorgenproof
