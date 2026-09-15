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

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Lib.Maps

theorem match_temps_assign : match_temps_assignStatement := by
  intro f le te id v tv hmatch hinj id' v' hget
  have hgs_le := CompCert4Lean.Lib.Maps.PTree.gsspec_proof (A := val) id' id v le
  have hgs_te := CompCert4Lean.Lib.Maps.PTree.gsspec_proof (A := val) id' id tv te
  cases hp : CompCert4Lean.Lib.Coqlib.peq id' id with
  | left hEq =>
      subst id'
      have hsource : PTree.get id (PTree.set id v le) = some v := by
        simpa [hp] using hgs_le
      rw [hsource] at hget
      cases hget
      refine ⟨tv, ?_, hinj⟩
      simpa [hp] using hgs_te
  | right hNe =>
      rw [hgs_le] at hget
      have hget' : PTree.get id' le = some v' := by
        simpa [hp] using hget
      rcases hmatch id' v' hget' with ⟨v'', hte, hinj'⟩
      refine ⟨v'', ?_, hinj'⟩
      rw [hgs_te]
      simp [hp, hte]

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

theorem match_bounds_invariant : match_bounds_invariantStatement := by
  intro e m1 m2 h hm id b sz ofs p he hp
  exact h id b sz ofs p he (hm id b sz ofs p he hp)

theorem is_reachable_from_env_dec : is_reachable_from_env_decStatement := by
  intro f e sp ofs
  exact Classical.em (is_reachable_from_env f e sp ofs)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

theorem padding_freeable_invariant : padding_freeable_invariantStatement := by
  intro f1 e tm1 sp sz cenv lo hi f2 tm2 hfree henv htm hmap ofs hof
  rcases hfree ofs hof with hperm | hreach
  · exact Or.inl (htm ofs hperm)
  · cases hreach with
    | @is_reachable_intro id b bsz delta hget hf1 hdelta =>
      have hb := henv.me_bounded id b bsz hget
      have hf2 : f2 b = some (sp, delta) := by
        rw [hmap b hb.2]
        exact hf1
      exact Or.inr (is_reachable_intro hget hf2 hdelta)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

theorem inj_preserves_globals : inj_preserves_globalsStatement := by
  intro prog f hi hmatch
  cases hmatch with
  | mk domain image symbols functions varinfos =>
      refine ⟨?_, ?_, ?_⟩
      · intro id b hsym
        exact domain b (symbols id b hsym)
      · intro b gv hvar
        exact domain b (varinfos b gv hvar)
      · intro b1 b2 delta gv hvar hinj
        exact (image b1 b2 delta hinj (varinfos b2 gv hvar)).symm

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

theorem match_callstack_match_globalenvs : match_callstack_match_globalenvsStatement := by
  intro prog f m tm cs bound tbound hmatch
  induction hmatch with
  | mcs_nil hglobal _ _ =>
      exact ⟨_, hglobal⟩
  | cons _ _ _ _ _ _ _ ih =>
      exact ih

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Values

theorem match_callstack_invariant : match_callstack_invariantStatement := by
  intro prog f1 m1 tm1 f2 m2 tm2 cs bound tbound hmatch
  induction hmatch with
  | mcs_nil hglobal hlo htl =>
      intro hincr hmem hfree hsame himage
      cases hglobal with
      | mk domain image symbols functions varinfos =>
          apply match_callstack.mcs_nil
          · apply match_globalenvs.mk
            · intro b hb
              rw [hsame b (CompCert4Lean.Lib.Coqlib.Plt_Ple_trans _ _ _ hb hlo)]
              exact domain b hb
            · intro b1 b2 delta hmap hb
              apply image b1 b2 delta
              · exact himage b1 b2 delta hmap
                  (CompCert4Lean.Lib.Coqlib.Plt_Ple_trans _ _ _ hb htl)
              · exact hb
            · exact symbols
            · exact functions
            · exact varinfos
          · exact hlo
          · exact htl
  | @cons cenv tf e le te sp lo hi cs bound tbound hbound hsp htemps henv hbounds hfree htail ih =>
      intro hincr hmem hfree' hsame himage
      have henv' : match_env f2 cenv e sp lo hi := by
        refine {
          me_vars := ?_,
          me_low_high := henv.me_low_high,
          me_bounded := henv.me_bounded,
          me_inv := ?_,
          me_incr := ?_ }
        · intro id
          have hvar := henv.me_vars id
          cases he : CompCert4Lean.Lib.Maps.PTree.get id e with
          | none =>
              cases hc : CompCert4Lean.Lib.Maps.PTree.get id cenv with
              | none =>
                  rw [he, hc] at hvar
                  exact .global
              | some ofs =>
                  rw [he, hc] at hvar
                  cases hvar
          | some bs =>
              cases bs with
              | mk b sz =>
                  cases hc : CompCert4Lean.Lib.Maps.PTree.get id cenv with
                  | none =>
                      rw [he, hc] at hvar
                      cases hvar
                  | some ofs =>
                      rw [he, hc] at hvar
                      cases hvar with
                      | «local» hptr =>
                          cases hptr with
                          | inject_ptr =>
                              rename_i delta hmap hofs
                              exact .local (.inject_ptr b
                                CompCert4Lean.Lib.Integers.Ptrofs.zero
                                sp
                                (CompCert4Lean.Lib.Integers.Ptrofs.repr ofs)
                                delta
                                (hincr b sp delta hmap) hofs)
        · intro b delta hmap
          exact henv.me_inv b delta
            (himage b sp delta hmap hsp)
        · intro b tb delta hmap hlt
          have hlt' : CompCert4Lean.Lib.Coqlib.Plt b bound :=
            CompCert4Lean.Lib.Coqlib.Plt_Ple_trans _ _ _ hlt
              (CompCert4Lean.Lib.Coqlib.Ple_trans _ _ _ henv.me_low_high hbound)
          apply henv.me_incr b tb delta
          · rw [← hsame b hlt']
            exact hmap
          · exact hlt
      apply match_callstack.cons hbound hsp
      · exact match_temps_invariant f1 f2 le te htemps hincr
      · exact henv'
      · apply match_bounds_invariant e m1 m2 hbounds
        intro id b sz ofs p hget hperm
        apply hmem b ofs p
          (CompCert4Lean.Lib.Coqlib.Plt_Ple_trans _ _ _
            (henv.me_bounded _ _ _ hget).2 hbound)
          hperm
      · apply padding_freeable_invariant f1 e tm1 sp tf.fn_stackspace cenv lo hi f2 tm2
          hfree henv
        · intro ofs hperm
          exact hfree' sp ofs hsp hperm
        · intro b hb
          exact hsame b (CompCert4Lean.Lib.Coqlib.Plt_Ple_trans _ _ _ hb hbound)
      · apply ih hincr
        · intro b ofs p hlt hperm
          exact hmem b ofs p
            (CompCert4Lean.Lib.Coqlib.Plt_Ple_trans _ _ _ hlt
              (CompCert4Lean.Lib.Coqlib.Ple_trans _ _ _ henv.me_low_high hbound)) hperm
        · intro sp' ofs hlt hperm
          exact hfree' sp' ofs
            (CompCert4Lean.Lib.Coqlib.Plt_trans _ _ _ hlt hsp) hperm
        · intro b hlt
          exact hsame b
            (CompCert4Lean.Lib.Coqlib.Plt_Ple_trans _ _ _ hlt
              (CompCert4Lean.Lib.Coqlib.Ple_trans _ _ _ henv.me_low_high hbound))
        · intro b b' delta hmap hlt
          exact himage b b' delta hmap
            (CompCert4Lean.Lib.Coqlib.Plt_trans _ _ _ hlt hsp)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

theorem match_callstack_incr_bound : match_callstack_incr_boundStatement := by
  intro prog f m tm cs bound tbound bound' tbound' hstack hbound htbound
  cases hstack with
  | mcs_nil hglobal hlo htl =>
      exact match_callstack.mcs_nil hglobal
        (CompCert4Lean.Lib.Coqlib.Ple_trans _ _ _ hlo hbound)
        (CompCert4Lean.Lib.Coqlib.Ple_trans _ _ _ htl htbound)
  | cons hhi hsp htemps henv hbounds hfree htail =>
      exact match_callstack.cons
        (CompCert4Lean.Lib.Coqlib.Ple_trans _ _ _ hhi hbound)
        (CompCert4Lean.Lib.Coqlib.Plt_Ple_trans _ _ _ hsp htbound)
        htemps henv hbounds hfree htail

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

theorem match_callstack_set_temp : match_callstack_set_tempStatement := by
  intro prog f cenv e le te sp lo hi cs bound tbound m tm tf id v tv hinj hstack
  cases hstack with
  | cons hbound hsp htemps henv hbounds hfree hcs =>
      exact .cons hbound hsp (match_temps_assign f le te id v tv htemps hinj)
        henv hbounds hfree hcs

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

theorem in_blocks_of_env : in_blocks_of_envStatement := by
  intro e id b sz hget
  unfold CS.blocks_of_env
  apply _root_.List.mem_map.mpr
  refine ⟨(id, (b, sz)), ?_, ?_⟩
  · exact CompCert4Lean.Lib.Maps.PTree.elements_correct_proof e id hget
  · rfl

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

private theorem alloc_nextblock_local (m : mem) (lo hi : Z) (m' : mem)
    (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (halloc : Mem.alloc m lo hi = (m', b)) :
    m'.nextblock = CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ m.nextblock := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have hnext := congrArg Mem.nextblock hfirst
  exact hnext.symm

private theorem alloc_result_local (m : mem) (lo hi : Z) (m' : mem)
    (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (halloc : Mem.alloc m lo hi = (m', b)) : b = m.nextblock := by
  unfold Mem.alloc at halloc
  exact (congrArg Prod.snd halloc).symm

private theorem perm_alloc_1_local (m : mem) (lo hi : Z) (m' : mem)
    (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (halloc : Mem.alloc m lo hi = (m', b))
    (b' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) (ofs : Z)
    (k : CompCert4Lean.Common.Memtype.perm_kind)
    (p : CompCert4Lean.Common.Memtype.permission)
    (hperm : Mem.perm m b' ofs k p) : Mem.perm m' b' ofs k p := by
  unfold Mem.alloc at halloc
  cases halloc
  unfold Mem.perm at hperm ⊢
  by_cases hblock : b' = m.nextblock
  · subst b'
    have hnot : ¬ CompCert4Lean.Lib.Coqlib.Plt m.nextblock m.nextblock :=
      CompCert4Lean.Lib.Coqlib.Plt_strict _
    rw [m.nextblock_noaccess _ _ _ hnot] at hperm
    exact False.elim hperm
  · rw [pmap_get_set_other_local _ _ _ _ hblock]
    exact hperm

private theorem alloc_contents_old_local (m : mem) (lo hi : Z) (m' : mem)
    (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (halloc : Mem.alloc m lo hi = (m', b))
    (b' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (hblock : b' ≠ m.nextblock) :
    PMap.get b' m'.mem_contents = PMap.get b' m.mem_contents := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have hcontents := congrArg (fun x : mem => x.mem_contents) hfirst
  rw [← hcontents]
  exact pmap_get_set_other_local _ _ _ _ hblock

private theorem alloc_access_old_local (m : mem) (lo hi : Z) (m' : mem)
    (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (halloc : Mem.alloc m lo hi = (m', b))
    (b' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (hblock : b' ≠ m.nextblock) :
    PMap.get b' m'.mem_access = PMap.get b' m.mem_access := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have haccess := congrArg (fun x : mem => x.mem_access) hfirst
  rw [← haccess]
  exact pmap_get_set_other_local _ _ _ _ hblock

private theorem perm_alloc_old_local (m : mem) (lo hi : Z) (m' : mem)
    (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (halloc : Mem.alloc m lo hi = (m', b))
    (b' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) (ofs : Z)
    (k : CompCert4Lean.Common.Memtype.perm_kind)
    (p : CompCert4Lean.Common.Memtype.permission) (hblock : b' ≠ m.nextblock)
    (hperm : Mem.perm m' b' ofs k p) : Mem.perm m b' ofs k p := by
  unfold Mem.perm at hperm ⊢
  rw [alloc_access_old_local m lo hi m' b halloc b' hblock] at hperm
  exact hperm

private theorem alloc_right_inject_local (f : meminj) (m tm : mem) (size : Z)
    (tm' : mem) (sp : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (halloc : Mem.alloc tm z0 size = (tm', sp))
    (hinj : Mem.inject f m tm) : Mem.inject f m tm' := by
  refine {
    mi_inj := ?_,
    mi_freeblocks := hinj.mi_freeblocks,
    mi_mappedblocks := ?_,
    mi_no_overlap := hinj.mi_no_overlap,
    mi_representable := hinj.mi_representable,
    mi_perm_inv := ?_ }
  · refine {
      mi_perm := ?_,
      mi_align := hinj.mi_inj.mi_align,
      mi_memval := ?_ }
    · intro b1 b2 delta ofs k p hmap hperm
      exact perm_alloc_1_local tm z0 size tm' sp halloc b2
        (ZArith.BinInt.Z.add ofs delta) k p
        (hinj.mi_inj.mi_perm b1 b2 delta ofs k p hmap hperm)
    · intro b1 ofs b2 delta hmap hperm
      have hvalid := hinj.mi_mappedblocks b1 b2 delta hmap
      have hneq : b2 ≠ tm.nextblock := by
        intro heq
        subst b2
        exact CompCert4Lean.Lib.Coqlib.Plt_strict _ hvalid
      rw [alloc_contents_old_local tm z0 size tm' sp halloc b2 hneq]
      exact hinj.mi_inj.mi_memval b1 ofs b2 delta hmap hperm
  · intro b1 b2 delta hmap
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.lt
      (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from b2) tm'.nextblock
    rw [alloc_nextblock_local tm z0 size tm' sp halloc]
    have hvalid : CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.lt
        (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from b2) tm.nextblock := by
      exact hinj.mi_mappedblocks b1 b2 delta hmap
    exact CompCert4Lean.Lib.Coqlib.Plt_trans_succ _ _ hvalid
  · intro b1 ofs b2 delta k p hmap hperm
    by_cases hnew : b2 = tm.nextblock
    · have hvalid := hinj.mi_mappedblocks b1 b2 delta hmap
      exact False.elim (CompCert4Lean.Lib.Coqlib.Plt_strict _ (hnew ▸ hvalid))
    · exact hinj.mi_perm_inv b1 ofs b2 delta k p hmap
        (perm_alloc_old_local tm z0 size tm' sp halloc b2
          (ZArith.BinInt.Z.add ofs delta) k p hnew hperm)

private theorem perm_alloc_2_local (m : mem) (lo hi : Z) (m' : mem)
    (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (halloc : Mem.alloc m lo hi = (m', b))
    (ofs : Z) (k : CompCert4Lean.Common.Memtype.perm_kind)
    (hof : ZArith.BinInt.Z.le lo ofs ∧ ZArith.BinInt.Z.lt ofs hi) :
    Mem.perm m' b ofs k CompCert4Lean.Common.Memtype.Freeable := by
  unfold Mem.alloc at halloc
  cases halloc
  unfold Mem.perm
  rw [pmap_get_set_same_local]
  change (Mem.perm_order'
    (if ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi then
      some CompCert4Lean.Common.Memtype.Freeable else none)
    CompCert4Lean.Common.Memtype.Freeable)
  have hle := hof.1
  have hlt := hof.2
  change intOfZ lo ≤ intOfZ ofs at hle
  change intOfZ ofs < intOfZ hi at hlt
  have hleB : ZArith.BinInt.Z.leb lo ofs = true := by
    simp [ZArith.BinInt.Z.leb, hle]
  have hltB : ZArith.BinInt.Z.ltb ofs hi = true := by
    simp [ZArith.BinInt.Z.ltb, hlt]
  simp [hleB, hltB]
  exact CompCert4Lean.Common.Memtype.perm_refl _

theorem match_callstack_alloc_right : match_callstack_alloc_rightStatement := by
  intro prog f m tm cs tf tm' sp le te cenv hstack halloc hinj htemps hcenv
  have halloc' : Mem.alloc tm z0 tf.fn_stackspace = (tm', sp) := halloc
  have hinj' : Mem.inject f m tm' :=
    alloc_right_inject_local f m tm tf.fn_stackspace tm' sp halloc' hinj
  have hsp_eq : sp = tm.nextblock :=
    alloc_result_local tm z0 tf.fn_stackspace tm' sp halloc'
  have henv : match_env f cenv CS.empty_env sp m.nextblock m.nextblock := by
    refine {
      me_vars := ?_,
      me_low_high := CompCert4Lean.Lib.Coqlib.Ple_refl _,
      me_bounded := ?_,
      me_inv := ?_,
      me_incr := ?_ }
    · intro id
      change match_var f (show CompCert4Lean.Common.Values.block from sp)
        (PTree.get id (PTree.empty (CompCert4Lean.Common.Values.block × Z)))
        (PTree.get id cenv)
      rw [PTree.gempty, hcenv id]
      exact .global
    · intro id b sz hget
      change PTree.get id (PTree.empty (CompCert4Lean.Common.Values.block × Z)) =
        some (b, sz) at hget
      rw [PTree.gempty] at hget
      cases hget
    · intro b delta hmap
      have hv := hinj.mi_mappedblocks b sp delta hmap
      have hnot : ¬ CompCert4Lean.Lib.Coqlib.Plt
          (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from sp)
          tm.nextblock := by
        rw [hsp_eq]
        exact CompCert4Lean.Lib.Coqlib.Plt_strict _
      exact False.elim (hnot hv)
    · intro b tb delta hmap hlt
      have hv := hinj.mi_mappedblocks b tb delta hmap
      change CompCert4Lean.Lib.Coqlib.Plt
        (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from tb) sp
      rw [hsp_eq]
      exact hv
  have hbounds : match_bounds CS.empty_env m := by
    intro id b sz ofs p hget
    change PTree.get id (PTree.empty (CompCert4Lean.Common.Values.block × Z)) =
      some (b, sz) at hget
    rw [PTree.gempty] at hget
    cases hget
  have hpad : padding_freeable f CS.empty_env tm' sp tf.fn_stackspace := by
    intro ofs hof
    left
    exact perm_alloc_2_local tm z0 tf.fn_stackspace tm' sp halloc' ofs
      CompCert4Lean.Common.Memtype.Cur hof
  have htail0 : match_callstack prog f m tm' cs m.nextblock tm.nextblock := by
    apply match_callstack_invariant prog f m tm f m tm' cs m.nextblock tm.nextblock hstack
    · intro b b' delta hmap
      exact hmap
    · intro b ofs p hlt hperm
      exact hperm
    · intro sp' ofs hlt hperm
      exact perm_alloc_1_local tm z0 tf.fn_stackspace tm' sp halloc' sp' ofs
        CompCert4Lean.Common.Memtype.Cur CompCert4Lean.Common.Memtype.Freeable hperm
    · intro b hlt
      rfl
    · intro b b' delta hmap hlt
      exact hmap
  have htail : match_callstack prog f m tm' cs m.nextblock sp := by
    rw [hsp_eq]
    exact htail0
  apply match_callstack.cons
    (CompCert4Lean.Lib.Coqlib.Ple_refl _)
  · rw [alloc_nextblock_local tm z0 tf.fn_stackspace tm' sp halloc']
    rw [hsp_eq]
    exact CompCert4Lean.Lib.Coqlib.Plt_succ _
  · exact htemps
  · exact henv
  · exact hbounds
  · exact hpad
  · exact htail

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem range_perm_free_local (m : Mem.mem) (b : proofBlock) (lo hi : proofZ)
    (hperm : Mem.range_perm m b lo hi Cur Freeable) :
    ∃ m', Mem.free m b lo hi = some m' := by
  cases hr : Mem.range_perm_dec m b lo hi Cur Freeable with
  | left hp =>
      refine ⟨Mem.unchecked_free m b lo hi, ?_⟩
      unfold Mem.free
      rw [hr]
      rfl
  | right hn =>
      exact False.elim (hn hperm)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

private theorem perm_free_1_local (m m' : Mem.mem) (b' : proofBlock) (lo hi : proofZ)
    (hfree : Mem.free m b' lo hi = some m') :
    ∀ b ofs (k : CompCert4Lean.Common.Memtype.perm_kind)
      (p : CompCert4Lean.Common.Memtype.permission),
      (b ≠ b' ∨ ZArith.BinInt.Z.lt ofs lo ∨ ZArith.BinInt.Z.le hi ofs) →
      Mem.perm m b ofs k p → Mem.perm m' b ofs k p := by
  intro b ofs k p hout hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    rw [← hm']
    unfold Mem.perm at hp ⊢
    dsimp [Mem.unchecked_free] at ⊢
    by_cases hb : b = b'
    · subst b
      change Mem.perm_order' (PMap.get b' m.mem_access ofs k) p at hp
      change Mem.perm_order'
        ((PMap.get b' (PMap.set b'
          (fun (ofs : proofZ) (k : CompCert4Lean.Common.Memtype.perm_kind) => _) m.mem_access))
          ofs k) p
      rw [pmap_get_set_same_local]
      split
      · rename_i hin
        exfalso
        rcases hout with hne | hlt | hge
        · exact hne rfl
        · change (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true at hin
          have hin' := Bool.and_eq_true_iff.mp hin
          have hlo' : intOfZ lo ≤ intOfZ ofs := by
            simpa [ZArith.BinInt.Z.leb] using hin'.1
          change intOfZ ofs < intOfZ lo at hlt
          omega
        · change (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true at hin
          have hin' := Bool.and_eq_true_iff.mp hin
          have hhi' : intOfZ ofs < intOfZ hi := by
            simpa [ZArith.BinInt.Z.ltb] using hin'.2
          change intOfZ hi ≤ intOfZ ofs at hge
          omega
      · exact hp
    · change Mem.perm_order' (PMap.get b m.mem_access ofs k) p at hp
      change Mem.perm_order'
        ((PMap.get b (PMap.set b'
          (fun (ofs : proofZ) (k : CompCert4Lean.Common.Memtype.perm_kind) => _) m.mem_access))
          ofs k) p
      rw [pmap_get_set_other_local _ _ _ _ hb]
      exact hp
  next hcond => cases hfree

private theorem perm_free_2_local (m m' : Mem.mem) (b : proofBlock) (lo hi : proofZ)
    (hfree : Mem.free m b lo hi = some m') :
    ∀ ofs (k : CompCert4Lean.Common.Memtype.perm_kind)
      (p : CompCert4Lean.Common.Memtype.permission),
      ZArith.BinInt.Z.le lo ofs → ZArith.BinInt.Z.lt ofs hi →
      ¬ Mem.perm m' b ofs k p := by
  intro ofs k p hlo hhi hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    rw [← hm'] at hp
    unfold Mem.perm at hp
    dsimp [Mem.unchecked_free] at hp
    change Mem.perm_order'
      ((PMap.get b (PMap.set b
        (fun (ofs : proofZ) (k : CompCert4Lean.Common.Memtype.perm_kind) => _) m.mem_access)) ofs k) p at hp
    rw [pmap_get_set_same_local] at hp
    split at hp
    · exact hp
    · rename_i hnot
      exfalso
      apply hnot
      change (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true
      have hlo' : intOfZ lo ≤ intOfZ ofs := by
        change intOfZ lo ≤ intOfZ ofs
        exact hlo
      have hhi' : intOfZ ofs < intOfZ hi := by
        change intOfZ ofs < intOfZ hi
        exact hhi
      simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb, hlo', hhi']
  next hcond => cases hfree

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

private theorem free_contents_local (m m' : Mem.mem) (b : proofBlock) (lo hi : proofZ)
    (hfree : Mem.free m b lo hi = some m') :
    m'.mem_contents = m.mem_contents := by
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    rw [← hm']
    rfl
  next hcond => cases hfree

private theorem free_list_contents_local (l : List (proofBlock × proofZ × proofZ))
    (m m' : Mem.mem) (hfree : Mem.free_list m l = some m') :
    m'.mem_contents = m.mem_contents := by
  induction l generalizing m m' with
  | nil =>
      simp [Mem.free_list] at hfree
      cases hfree
      rfl
  | cons x rest ih =>
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
          have htail := ih m1 m' hrest
          have hhead := free_contents_local m m1 x.1 x.2.1 x.2.2 hfm
          exact htail.trans hhead

private theorem free_list_no_perm_local (l : List (proofBlock × proofZ × proofZ))
    (m m' : Mem.mem) (hfree : Mem.free_list m l = some m') :
    ∀ b lo hi, In (b, lo, hi) l →
      ∀ ofs (k : CompCert4Lean.Common.Memtype.perm_kind)
        (p : CompCert4Lean.Common.Memtype.permission),
      ZArith.BinInt.Z.le lo ofs → ZArith.BinInt.Z.lt ofs hi →
      ¬ Mem.perm m' b ofs k p := by
  induction l generalizing m m' with
  | nil =>
      intro b lo hi hin
      cases hin
  | cons x rest ih =>
      intro b lo hi hin ofs k p hlo hhi hp
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
          cases (_root_.List.mem_cons.mp hin) with
          | inl heq =>
              cases heq
              have hp1 : Mem.perm m1 b ofs k p :=
                perm_freelist rest m1 m' b ofs k p hrest hp
              exact perm_free_2_local m m1 b lo hi hfm ofs k p hlo hhi hp1
          | inr htail =>
              exact ih m1 m' hrest b lo hi htail ofs k p hlo hhi hp

private theorem free_list_perm_outside_local (l : List (proofBlock × proofZ × proofZ))
    (m m' : Mem.mem) (hfree : Mem.free_list m l = some m') :
    ∀ b ofs (k : CompCert4Lean.Common.Memtype.perm_kind)
      (p : CompCert4Lean.Common.Memtype.permission),
      Mem.perm m b ofs k p →
      (∀ b' lo hi, In (b', lo, hi) l →
        ZArith.BinInt.Z.lt ofs lo ∨ ZArith.BinInt.Z.le hi ofs ∨ b ≠ b') →
      Mem.perm m' b ofs k p := by
  induction l generalizing m m' with
  | nil =>
      intro b ofs k p hp hout
      simp [Mem.free_list] at hfree
      cases hfree
      exact hp
  | cons x rest ih =>
      intro b ofs k p hp hout
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
          have hout0 := hout x.1 x.2.1 x.2.2
            (_root_.List.mem_cons_self : x ∈ x :: rest)
          have hside : b ≠ x.1 ∨ ZArith.BinInt.Z.lt ofs x.2.1 ∨
              ZArith.BinInt.Z.le x.2.2 ofs := by
            rcases hout0 with h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
            · exact Or.inl h
          have hp1 : Mem.perm m1 b ofs k p :=
            perm_free_1_local m m1 x.1 x.2.1 x.2.2 hfm b ofs k p hside hp
          apply ih m1 m' hrest b ofs k p hp1
          intro b' lo hi hin
          exact hout b' lo hi (_root_.List.mem_cons.mpr (Or.inr hin))

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

private theorem outside_interval_local (x lo hi : proofZ) :
    ¬ (ZArith.BinInt.Z.le lo x ∧ ZArith.BinInt.Z.lt x hi) →
      ZArith.BinInt.Z.lt x lo ∨ ZArith.BinInt.Z.le hi x := by
  intro h
  by_cases hlt : ZArith.BinInt.Z.lt x lo
  · exact Or.inl hlt
  by_cases hge : ZArith.BinInt.Z.le hi x
  · exact Or.inr hge
  exfalso
  apply h
  constructor
  · change intOfZ lo ≤ intOfZ x
    change ¬ intOfZ x < intOfZ lo at hlt
    change ¬ intOfZ hi ≤ intOfZ x at hge
    omega
  · change intOfZ x < intOfZ hi
    change ¬ intOfZ hi ≤ intOfZ x at hge
    omega

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers

private theorem free_inject_local (f : meminj) (m m' tm tm' : Mem.mem)
    (l : List (proofBlock × proofZ × proofZ)) (bf : proofBlock × proofZ × proofZ)
    (hinj : Mem.inject f m tm)
    (hlist : Mem.free_list m l = some m')
    (hfree : Mem.free tm bf.1 bf.2.1 bf.2.2 = some tm')
    (hside : ∀ b1 delta ofs (k : CompCert4Lean.Common.Memtype.perm_kind)
        (p : CompCert4Lean.Common.Memtype.permission),
        f b1 = some (bf.1, delta) →
        Mem.perm m b1 ofs k p →
        ZArith.BinInt.Z.le bf.2.1 (ZArith.BinInt.Z.add ofs delta) →
        ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add ofs delta) bf.2.2 →
        ∃ lo1 hi1, In (b1, lo1, hi1) l ∧
          ZArith.BinInt.Z.le lo1 ofs ∧ ZArith.BinInt.Z.lt ofs hi1) :
    Mem.inject f m' tm' := by
  have hnexts : m'.nextblock = m.nextblock := nextblock_freelist l m m' hlist
  have hnextt : tm'.nextblock = tm.nextblock := nextblock_free_local tm bf.1 bf.2.1 bf.2.2 tm' hfree
  have hconts : m'.mem_contents = m.mem_contents := free_list_contents_local l m m' hlist
  have hcontt : tm'.mem_contents = tm.mem_contents := free_contents_local tm tm' bf.1 bf.2.1 bf.2.2 hfree
  refine {
    mi_inj := ?_,
    mi_freeblocks := ?_,
    mi_mappedblocks := ?_,
    mi_no_overlap := ?_,
    mi_representable := ?_,
    mi_perm_inv := ?_ }
  · refine { mi_perm := ?_, mi_align := ?_, mi_memval := ?_ }
    · intro b1 b2 delta ofs k p hmap hp'
      have hp : Mem.perm m b1 ofs k p := perm_freelist l m m' b1 ofs k p hlist hp'
      have htarget :
          b2 ≠ bf.1 ∨ ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add ofs delta) bf.2.1 ∨
            ZArith.BinInt.Z.le bf.2.2 (ZArith.BinInt.Z.add ofs delta) := by
        by_cases hb : b2 = bf.1
        · subst b2
          by_cases hinside :
              ZArith.BinInt.Z.le bf.2.1 (ZArith.BinInt.Z.add ofs delta) ∧
                ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add ofs delta) bf.2.2
          · rcases hside b1 delta ofs k p hmap hp hinside.1 hinside.2 with
              ⟨lo1, hi1, hin, hlo1, hhi1⟩
            exact False.elim
              (free_list_no_perm_local l m m' hlist b1 lo1 hi1 hin ofs k p hlo1 hhi1 hp')
          · exact Or.inr (outside_interval_local (ZArith.BinInt.Z.add ofs delta)
              bf.2.1 bf.2.2 hinside)
        · exact Or.inl hb
      exact perm_free_1_local tm tm' bf.1 bf.2.1 bf.2.2 hfree
        b2 (ZArith.BinInt.Z.add ofs delta) k p htarget
        (hinj.mi_inj.mi_perm b1 b2 delta ofs k p hmap hp)
    · intro b1 b2 delta chunk ofs p hmap hrange
      apply hinj.mi_inj.mi_align b1 b2 delta chunk ofs p hmap
      intro q hq
      exact perm_freelist l m m' b1 q Max p hlist (hrange q hq)
    · intro b1 ofs b2 delta hmap hp'
      have hp : Mem.perm m b1 ofs Cur Readable :=
        perm_freelist l m m' b1 ofs Cur Readable hlist hp'
      have hmv := hinj.mi_inj.mi_memval b1 ofs b2 delta hmap hp
      simpa [hconts, hcontt] using hmv
  · intro b hvalid
    apply hinj.mi_freeblocks b
    intro hb
    apply hvalid
    change Plt b m'.nextblock
    rw [hnexts]
    exact hb
  · intro b b2 delta hmap
    change Plt b2 tm'.nextblock
    rw [hnextt]
    exact hinj.mi_mappedblocks b b2 delta hmap
  · intro b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne hmap1 hmap2 hp1' hp2'
    apply hinj.mi_no_overlap b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne hmap1 hmap2
    · exact perm_freelist l m m' b1 ofs1 Max CompCert4Lean.Common.Memtype.Nonempty hlist hp1'
    · exact perm_freelist l m m' b2 ofs2 Max CompCert4Lean.Common.Memtype.Nonempty hlist hp2'
  · intro b1 b2 delta ofs hmap hperm
    apply hinj.mi_representable b1 b2 delta ofs hmap
    rcases hperm with h | h
    · left
      exact perm_freelist l m m' b1 (Ptrofs.unsigned ofs) Max CompCert4Lean.Common.Memtype.Nonempty hlist h
    · right
      exact perm_freelist l m m' b1
        (ZArith.BinInt.Z.sub (Ptrofs.unsigned ofs) (.Zpos .xH)) Max CompCert4Lean.Common.Memtype.Nonempty hlist h
  · intro b1 ofs b2 delta k p hmap hp2'
    have hp2 : Mem.perm tm b2 (ZArith.BinInt.Z.add ofs delta) k p :=
      perm_of_free tm tm' bf.1 bf.2.1 bf.2.2 hfree b2
        (ZArith.BinInt.Z.add ofs delta) k p hp2'
    rcases hinj.mi_perm_inv b1 ofs b2 delta k p hmap hp2 with hp1 | hnone
    · by_cases hmem : ∃ lo1 hi1, In (b1, lo1, hi1) l ∧
          ZArith.BinInt.Z.le lo1 ofs ∧ ZArith.BinInt.Z.lt ofs hi1
      · right
        rcases hmem with ⟨lo1, hi1, hin, hlo1, hhi1⟩
        intro hp1'
        exact free_list_no_perm_local l m m' hlist b1 lo1 hi1 hin ofs Max CompCert4Lean.Common.Memtype.Nonempty hlo1 hhi1 hp1'
      · left
        apply free_list_perm_outside_local l m m' hlist b1 ofs k p hp1
        intro b' lo1 hi1 hin
        by_cases hneq : b1 ≠ b'
        · exact Or.inr (Or.inr hneq)
        · have heq : b1 = b' := by
            by_cases heq : b1 = b'
            · exact heq
            · exact False.elim (hneq heq)
          subst b'
          rcases outside_interval_local ofs lo1 hi1 (by
            intro hinside
            apply hmem
            exact ⟨lo1, hi1, hin, hinside.1, hinside.2⟩) with hlt | hge
          · exact Or.inl hlt
          · exact Or.inr (Or.inl hge)
    · right
      intro hp1'
      apply hnone
      exact perm_freelist l m m' b1 ofs Max CompCert4Lean.Common.Memtype.Nonempty hlist hp1'

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

theorem match_callstack_freelist : match_callstack_freelistStatement := by
  intro prog f cenv tf e le te sp lo hi cs m m' tm hinj hlist hstack
  cases hstack with
  | cons hbound hsp htemps henv hbounds hpadding htail =>
      have htarget_range : Mem.range_perm tm sp z0 tf.fn_stackspace Cur Freeable := by
        intro ofs hof
        rcases hof with ⟨hof0, hof1⟩
        rcases hpadding ofs ⟨hof0, hof1⟩ with hperm | hreach
        · exact hperm
        · cases hreach with
          | @is_reachable_intro id b sz delta hget hmap hdelta =>
              rcases hdelta with ⟨hdelta_lo, hdelta_hi⟩
              have hrange : Mem.range_perm m _ z0 _ Cur Freeable :=
                free_list_freeable (CS.blocks_of_env e) m m' hlist _ z0 _
                  (in_blocks_of_env e _ _ _ hget)
              have hsub : intOfZ (ZArith.BinInt.Z.sub ofs delta) =
                  intOfZ ofs - intOfZ delta := by
                change intOfZ (zOfInt
                  (intOfZ ofs - intOfZ delta)) = intOfZ ofs - intOfZ delta
                rw [intOfZ_zOfInt]
              have hadd : intOfZ (ZArith.BinInt.Z.add delta sz) =
                  intOfZ delta + intOfZ sz := by
                change intOfZ (zOfInt (intOfZ delta + intOfZ sz)) = intOfZ delta + intOfZ sz
                rw [intOfZ_zOfInt]
              have hofs0 : ZArith.BinInt.Z.le z0
                  (ZArith.BinInt.Z.sub ofs delta) := by
                change (0 : Int) ≤ intOfZ (ZArith.BinInt.Z.sub ofs delta)
                change intOfZ z0 ≤ intOfZ ofs at hof0
                change intOfZ delta ≤ intOfZ ofs at hdelta_lo
                rw [hsub]
                omega
              have hofssz : ZArith.BinInt.Z.lt
                  (ZArith.BinInt.Z.sub ofs delta) sz := by
                change intOfZ (ZArith.BinInt.Z.sub ofs delta) < intOfZ sz
                change intOfZ ofs < intOfZ (ZArith.BinInt.Z.add delta sz) at hdelta_hi
                rw [hadd] at hdelta_hi
                rw [hsub]
                omega
              have hsrc := hrange (ZArith.BinInt.Z.sub ofs delta) ⟨hofs0, hofssz⟩
              have ht := hinj.mi_inj.mi_perm b sp delta
                (ZArith.BinInt.Z.sub ofs delta) Cur Freeable hmap hsrc
              have haddsub : ZArith.BinInt.Z.add
                  (ZArith.BinInt.Z.sub ofs delta) delta = ofs := by
                apply intOfZ_injective
                change intOfZ (zOfInt
                  (intOfZ (ZArith.BinInt.Z.sub ofs delta) + intOfZ delta)) = intOfZ ofs
                rw [intOfZ_zOfInt, hsub]
                omega
              simpa [haddsub] using ht
      rcases range_perm_free_local tm sp z0 tf.fn_stackspace htarget_range with
        ⟨tm2, hfree⟩
      have hside : ∀ b1 delta ofs (k : CompCert4Lean.Common.Memtype.perm_kind)
          (p : CompCert4Lean.Common.Memtype.permission),
          f b1 = some (sp, delta) → Mem.perm m b1 ofs k p →
          ZArith.BinInt.Z.le z0 (ZArith.BinInt.Z.add ofs delta) →
          ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add ofs delta) tf.fn_stackspace →
          ∃ lo1 hi1, In (b1, lo1, hi1) (CS.blocks_of_env e) ∧
            ZArith.BinInt.Z.le lo1 ofs ∧ ZArith.BinInt.Z.lt ofs hi1 := by
        intro b1 delta ofs k p hmap hp hlo hhi
        rcases henv.me_inv b1 delta hmap with ⟨id, sz, hget⟩
        have hboundofs := hbounds id b1 sz ofs p hget
          (Mem.perm_max m b1 ofs k p hp)
        refine ⟨z0, sz, in_blocks_of_env e id b1 sz hget, ?_, ?_⟩
        · exact hboundofs.1
        · exact hboundofs.2
      have hinj' : Mem.inject f m' tm2 :=
        free_inject_local f m m' tm tm2 (CS.blocks_of_env e)
          (sp, z0, tf.fn_stackspace) hinj hlist hfree hside
      have htail' : match_callstack prog f m' tm2 cs m'.nextblock tm2.nextblock := by
        have hincr : CompCert4Lean.Common.Values.inject_incr f f := by intro b b' delta h; exact h
        have hmem : ∀ b ofs p, Plt b lo → Mem.perm m' b ofs Max p →
            Mem.perm m b ofs Max p := by
          intro b ofs p _ hp
          exact perm_freelist (CS.blocks_of_env e) m m' b ofs Max p hlist hp
        have hfree' : ∀ sp' ofs, Plt sp' sp → Mem.perm tm sp' ofs Cur Freeable →
            Mem.perm tm2 sp' ofs Cur Freeable := by
          intro sp' ofs hlt hp
          apply perm_free_1_local tm tm2 sp z0 tf.fn_stackspace hfree sp' ofs Cur Freeable
          · exact Or.inl (by
              intro heq
              subst sp'
              exact Plt_strict sp hlt)
          · exact hp
        have hsame : ∀ b, Plt b lo → f b = f b := by intro b h; rfl
        have himage : ∀ b b' delta, f b = some (b', delta) → Plt b' sp →
            f b = some (b', delta) := by intro b b' delta hmap hlt; exact hmap
        have htail0 := match_callstack_invariant prog f m tm f m' tm2 cs lo sp htail
          hincr hmem hfree' hsame himage
        have hnexts : m'.nextblock = m.nextblock :=
          nextblock_freelist (CS.blocks_of_env e) m m' hlist
        have hnextt : tm2.nextblock = tm.nextblock :=
          nextblock_free_local tm sp z0 tf.fn_stackspace tm2 hfree
        have hbound' : Ple lo m'.nextblock := by
          rw [hnexts]
          exact Ple_trans _ _ _ henv.me_low_high hbound
        have htbound' : Ple sp tm2.nextblock := by
          rw [hnextt]
          exact Plt_Ple _ _ hsp
        apply match_callstack_incr_bound prog f m' tm2 cs lo sp m'.nextblock tm2.nextblock htail0
        · exact hbound'
        · exact htbound'
      refine ⟨tm2, hfree, htail', hinj'⟩

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Events
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem intOfZ_sub_external (x y : Z) :
    intOfZ (ZArith.BinInt.Z.sub x y) = intOfZ x - intOfZ y := by
  change intOfZ (zOfInt (intOfZ x - intOfZ y)) = intOfZ x - intOfZ y
  rw [intOfZ_zOfInt]

private theorem intOfZ_add_external (x y : Z) :
    intOfZ (ZArith.BinInt.Z.add x y) = intOfZ x + intOfZ y := by
  change intOfZ (zOfInt (intOfZ x + intOfZ y)) = intOfZ x + intOfZ y
  rw [intOfZ_zOfInt]

theorem match_callstack_external_call : match_callstack_external_callStatement := by
  intro prog f1 f2 m1 m2 m1' m2' hunmapped houtofreach hincr hseparated hmax
    cs bound tbound hstack hbound htbound
  induction hstack with
  | mcs_nil hglobal hlo htl =>
      cases hglobal with
      | mk domain image symbols functions varinfos =>
          apply match_callstack.mcs_nil
          · apply match_globalenvs.mk
            · intro b hb
              exact hincr b b z0 (domain b hb)
            · intro b1 b2 delta hmap hb2
              cases hf : f1 b1 with
              | some p =>
                  have hf2 : f2 b1 = some p := hincr b1 p.1 p.2 hf
                  have heq : p = (b2, delta) := Option.some.inj (hf2.symm.trans hmap)
                  rcases heq with ⟨rfl, rfl⟩
                  exact image b1 b2 delta hf hb2
              | none =>
                  have hs := hseparated b1 b2 delta hf hmap
                  have hbvalid_lt : Plt b2 m1'.nextblock := by
                    exact Plt_Ple_trans _ _ _ hb2 (Ple_trans _ _ _ htl htbound)
                  have hbvalid : Mem.valid_block m1' b2 := by
                    change Plt b2 m1'.nextblock
                    exact hbvalid_lt
                  exact False.elim (hs.2 hbvalid)
            · exact symbols
            · exact functions
            · exact varinfos
          · exact hlo
          · exact htl
  | @cons cenv tf e le te sp lo hi cs bound tbound hbound' hsp htemps henv hbounds hfree htail ih =>
      apply match_callstack.cons hbound' hsp
      · exact match_temps_invariant f1 f2 le te htemps hincr
      · refine {
          me_vars := ?_,
          me_low_high := henv.me_low_high,
          me_bounded := henv.me_bounded,
          me_inv := ?_,
          me_incr := ?_ }
        · intro id
          have hvar := henv.me_vars id
          cases he : PTree.get id e with
          | none =>
              cases hc : PTree.get id cenv with
              | none =>
                  rw [he, hc] at hvar
                  exact .global
              | some ofs =>
                  rw [he, hc] at hvar
                  cases hvar
          | some bs =>
              cases bs with
              | mk b sz =>
                  cases hc : PTree.get id cenv with
                  | none =>
                      rw [he, hc] at hvar
                      cases hvar
                  | some ofs =>
                      rw [he, hc] at hvar
                      cases hvar with
                      | «local» hptr =>
                          cases hptr with
                          | inject_ptr =>
                              rename_i delta hmap hofs
                              exact .local (.inject_ptr b
                                CompCert4Lean.Lib.Integers.Ptrofs.zero
                                sp
                                (CompCert4Lean.Lib.Integers.Ptrofs.repr ofs)
                                delta
                                (hincr b sp delta hmap) hofs)
        · intro b delta hmap
          cases hf : f1 b with
          | some pair =>
              rcases pair with ⟨b', delta'⟩
              have hf2 : f2 b = some (b', delta') := hincr b b' delta' hf
              rw [hf2] at hmap
              have hpairs : (b', delta') = (sp, delta) := Option.some.inj hmap
              rcases hpairs with ⟨rfl, rfl⟩
              exact henv.me_inv b delta hf
          | none =>
              have hs := hseparated b sp delta hf hmap
              have hbvalid_lt : Plt sp m1'.nextblock :=
                Plt_Ple_trans _ _ _ hsp htbound
              have hbvalid : Mem.valid_block m1' sp := by
                change Plt sp m1'.nextblock
                exact hbvalid_lt
              exact False.elim (hs.2 hbvalid)
        · intro b tb delta hmap hlt
          cases hf : f1 b with
          | some pair =>
              rcases pair with ⟨b', delta'⟩
              have hf2 : f2 b = some (b', delta') := hincr b b' delta' hf
              rw [hf2] at hmap
              have hpairs : (b', delta') = (tb, delta) := Option.some.inj hmap
              rcases hpairs with ⟨rfl, rfl⟩
              exact henv.me_incr b tb delta hf hlt
          | none =>
              have hs := hseparated b tb delta hf hmap
              have hbvalid : Mem.valid_block m1 b := by
                change Plt b m1.nextblock
                exact Plt_Ple_trans _ _ _ hlt
                  (Ple_trans _ _ _ henv.me_low_high (Ple_trans _ _ _ hbound' hbound))
              exact False.elim (hs.1 hbvalid)
      · apply match_bounds_invariant e m1 m2 hbounds
        intro id b sz ofs p hget hperm
        apply hmax b ofs p
        · change Plt b m1.nextblock
          exact Plt_Ple_trans _ _ _ (henv.me_bounded id b sz hget).2
            (Ple_trans _ _ _ hbound' hbound)
        · exact hperm
      · intro ofs hof
        by_cases hreach : is_reachable_from_env f1 e sp ofs
        · cases hreach with
          | @is_reachable_intro id b sz delta hget hf1 hdelta =>
              right
              have hf2 : f2 b = some (sp, delta) := hincr b sp delta hf1
              exact is_reachable_intro hget hf2 hdelta
        · have horig := hfree ofs hof
          cases horig with
          | inl hperm =>
              left
              have hloc : loc_out_of_reach f1 m1 sp ofs := by
                intro b delta hmap hp
                apply hreach
                rcases henv.me_inv b delta hmap with ⟨id, sz, hget⟩
                have hbounds' := hbounds id b sz
                  (ZArith.BinInt.Z.sub ofs delta) Nonempty hget hp
                have hsub := intOfZ_sub_external ofs delta
                have hlo := hbounds'.1
                have hhi := hbounds'.2
                have hle : intOfZ delta ≤ intOfZ ofs := by
                  change (0 : Int) ≤ intOfZ (ZArith.BinInt.Z.sub ofs delta) at hlo
                  rw [hsub] at hlo
                  omega
                have hlt : intOfZ ofs < intOfZ delta + intOfZ sz := by
                  change intOfZ (ZArith.BinInt.Z.sub ofs delta) < intOfZ sz at hhi
                  rw [hsub] at hhi
                  omega
                refine is_reachable_intro hget hmap ?_
                constructor
                · change intOfZ delta ≤ intOfZ ofs
                  exact hle
                · change intOfZ ofs < intOfZ (ZArith.BinInt.Z.add delta sz)
                  rw [intOfZ_add_external]
                  exact hlt
              have hvalid : Mem.valid_block m1' sp := by
                change Plt sp m1'.nextblock
                exact Plt_Ple_trans _ _ _ hsp htbound
              exact (houtofreach.unchanged_on_perm sp ofs Cur Freeable hloc hvalid).mp hperm
          | inr hreach' => exact False.elim (hreach hreach')
      · exact ih
          (Ple_trans _ _ _ henv.me_low_high (Ple_trans _ _ _ hbound' hbound))
          (Ple_trans _ _ _ (Plt_Ple _ _ hsp) htbound)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem cenv_remove_gso : cenv_remove_gsoStatement := by
  intro id vars cenv hnot
  induction vars with
  | nil => rfl
  | cons v vars ih =>
      change PTree.get id (PTree.remove v.1 (cenv_remove cenv vars)) = PTree.get id cenv
      apply Eq.trans (PTree.gro_proof (cenv_remove cenv vars) ?_) (ih ?_)
      · intro heq
        apply hnot
        simpa [heq] using (_root_.List.Mem.head (List.map Prod.fst vars))
      · intro h
        apply hnot
        exact _root_.List.Mem.tail v.1 h

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem cenv_remove_gss : cenv_remove_gssStatement := by
  intro id vars cenv hmem
  induction vars with
  | nil => cases hmem
  | cons v vars ih =>
      change PTree.get id (PTree.remove v.1 (cenv_remove cenv vars)) = none
      by_cases hhead : id = v.1
      · subst id
        exact PTree.grs_proof (cenv_remove cenv vars) (i := v.1)
      · apply Eq.trans (PTree.gro_proof (cenv_remove cenv vars) hhead) (ih ?_)
        rcases List.mem_cons.mp hmem with hhead' | htail
        · exact False.elim (hhead hhead')
        · exact htail

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Cfrontend.Cminorgen
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata

theorem block_alignment_pos : block_alignment_posStatement := by
  intro sz
  have hpos : ∀ n : Nat, 0 < n →
      ZArith.BinInt.Z.lt ZArith.BinInt.Z.Z0 (ZArith.BinInt.Z.of_nat n) := by
    intro n hn
    unfold ZArith.BinInt.Z.lt
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    change (0 : Int) < Int.ofNat n
    exact Int.natCast_pos.mpr hn
  unfold block_alignment
  cases h2 : zlt sz (ZArith.BinInt.Z.of_nat 2) with
  | left h2 =>
      simp [h2, ZArith.BinInt.Z.lt, z0,
        ZArith.BinInt.Z.of_nat, intOfZ, zOfInt]
      exact hpos 1 (by omega)
  | right h2 =>
      cases h4 : zlt sz (ZArith.BinInt.Z.of_nat 4) with
      | left h4 =>
          simp [h2, h4, ZArith.BinInt.Z.lt, z0,
            ZArith.BinInt.Z.of_nat, intOfZ, zOfInt]
          exact hpos 2 (by omega)
      | right h4 =>
          cases h8 : zlt sz (ZArith.BinInt.Z.of_nat 8) with
          | left h8 =>
              simp [h2, h4, h8, ZArith.BinInt.Z.lt, z0,
                ZArith.BinInt.Z.of_nat, intOfZ, zOfInt]
              exact hpos 4 (by omega)
          | right h8 =>
              simp [h2, h4, h8, ZArith.BinInt.Z.lt, z0,
                ZArith.BinInt.Z.of_nat, intOfZ, zOfInt]
              exact hpos 8 (by omega)

theorem assign_variable_incr : assign_variable_incrStatement := by
  intro id sz cenv stksz cenv' stksz' h
  have hstack := congrArg Prod.snd h
  dsimp [assign_variable] at hstack
  rw [← hstack]
  have halign := align_le stksz (block_alignment sz)
    (block_alignment_pos sz)
  change intOfZ stksz ≤
    intOfZ (align stksz (block_alignment sz)) at halign
  have hmax : ZArith.BinInt.Z.le z0 (zMax z0 sz) :=
    Zmax_bound_l z0 z0 sz (by
      change (0 : Int) ≤ 0
      omega)
  change intOfZ z0 ≤ intOfZ (zMax z0 sz) at hmax
  have hz0 : intOfZ z0 = 0 := rfl
  rw [hz0] at hmax
  change ZArith.BinInt.Z.le stksz
    (ZArith.BinInt.Z.add
      (align stksz (block_alignment sz)) (zMax z0 sz))
  change intOfZ stksz ≤ intOfZ
    (ZArith.BinInt.Z.add
      (align stksz (block_alignment sz)) (zMax z0 sz))
  have hsum : intOfZ (align stksz (block_alignment sz)) ≤
    intOfZ (ZArith.BinInt.Z.add
      (align stksz (block_alignment sz)) (zMax z0 sz)) := by
    unfold ZArith.BinInt.Z.add
    simp only [intOfZ_zOfInt]
    omega
  exact Int.le_trans halign hsum

theorem inj_offset_aligned_block : inj_offset_aligned_blockStatement := by
  have htrans : ∀ a b c : Z,
      ZArith.BinInt.Z.divide a b →
      ZArith.BinInt.Z.divide b c →
      ZArith.BinInt.Z.divide a c := by
    intro a b c hab hbc
    rcases hab with ⟨k, hk⟩
    rcases hbc with ⟨l, hl⟩
    refine ⟨ZArith.BinInt.Z.mul k l, ?_⟩
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt] at hk hl ⊢
    have hk' : intOfZ b = intOfZ a * intOfZ k := by
      rw [hk, intOfZ_zOfInt]
    have hl' : intOfZ c = intOfZ b * intOfZ l := by
      rw [hl, intOfZ_zOfInt]
    rw [hl', hk']
    simp [Int.mul_assoc]
  have hdiv_of : ∀ a k : Nat,
      ZArith.BinInt.Z.divide
        (ZArith.BinInt.Z.of_nat a)
        (ZArith.BinInt.Z.of_nat (a * k)) := by
    intro a k
    refine ⟨ZArith.BinInt.Z.of_nat k, ?_⟩
    apply intOfZ_injective
    simp [ZArith.BinInt.Z.mul, ZArith.BinInt.Z.of_nat,
      intOfZ_zOfInt]
  have hp1 : posToNat (posOfNat 1) = 1 :=
    posToNat_posOfNat (by omega)
  have hp2 : posToNat (posOfNat 2) = 2 :=
    posToNat_posOfNat (by omega)
  have hp4 : posToNat (posOfNat 4) = 4 :=
    posToNat_posOfNat (by omega)
  have hp8 : posToNat (posOfNat 8) = 8 :=
    posToNat_posOfNat (by omega)
  have hchunk_block : ∀ (sz : Z) chunk,
      ZArith.BinInt.Z.le (CompCert4Lean.Common.Memdata.size_chunk chunk) sz →
      ZArith.BinInt.Z.divide
        (CompCert4Lean.Common.Memdata.align_chunk chunk)
        (block_alignment sz) := by
    intro sz chunk hsize
    cases hz2 : zlt sz (ZArith.BinInt.Z.of_nat 2) with
    | left hlt2 =>
        have hlt2i : intOfZ sz < 2 := by
          change intOfZ sz < intOfZ (ZArith.BinInt.Z.of_nat 2) at hlt2
          simpa [ZArith.BinInt.Z.of_nat, intOfZ, zOfInt, hp2] using hlt2
        cases chunk <;>
          simp [CompCert4Lean.Common.Memdata.align_chunk,
            CompCert4Lean.Common.Memdata.size_chunk, block_alignment,
            hz2, hlt2, z0] at hsize ⊢
        all_goals first
        | simpa using hdiv_of 1 1
        | exfalso
          simp_all [ZArith.BinInt.Z.le, ZArith.BinInt.Z.lt,
            ZArith.BinInt.Z.of_nat, intOfZ, zOfInt, hp1, hp2, hp4, hp8,
            hlt2i]
          omega
    | right hge2 =>
        have hge2i : (2 : Int) ≤ intOfZ sz := by
          change intOfZ (ZArith.BinInt.Z.of_nat 2) ≤ intOfZ sz at hge2
          simpa [ZArith.BinInt.Z.of_nat, intOfZ, zOfInt, hp2] using hge2
        cases hz4 : zlt sz (ZArith.BinInt.Z.of_nat 4) with
        | left hlt4 =>
            have hlt4i : intOfZ sz < 4 := by
              change intOfZ sz < intOfZ (ZArith.BinInt.Z.of_nat 4) at hlt4
              simpa [ZArith.BinInt.Z.of_nat, intOfZ, zOfInt, hp4] using hlt4
            cases chunk <;>
              simp [CompCert4Lean.Common.Memdata.align_chunk,
                CompCert4Lean.Common.Memdata.size_chunk, block_alignment,
                hz2, hge2, hz4, hlt4, z0] at hsize ⊢
            all_goals first
            | simpa using hdiv_of 1 2
            | simpa using hdiv_of 2 1
            | exfalso
              simp_all [ZArith.BinInt.Z.le, ZArith.BinInt.Z.lt,
                ZArith.BinInt.Z.of_nat, intOfZ, zOfInt, hp1, hp2, hp4, hp8,
                hge2i, hlt4i]
              omega
        | right hge4 =>
            have hge4i : (4 : Int) ≤ intOfZ sz := by
              change intOfZ (ZArith.BinInt.Z.of_nat 4) ≤ intOfZ sz at hge4
              simpa [ZArith.BinInt.Z.of_nat, intOfZ, zOfInt, hp4] using hge4
            cases hz8 : zlt sz (ZArith.BinInt.Z.of_nat 8) with
            | left hlt8 =>
                have hlt8i : intOfZ sz < 8 := by
                  change intOfZ sz < intOfZ (ZArith.BinInt.Z.of_nat 8) at hlt8
                  simpa [ZArith.BinInt.Z.of_nat, intOfZ, zOfInt, hp8] using hlt8
                cases chunk <;>
                  simp [CompCert4Lean.Common.Memdata.align_chunk,
                    CompCert4Lean.Common.Memdata.size_chunk, block_alignment,
                    hz2, hge2, hz4, hge4, hz8, hlt8, z0] at hsize ⊢
                all_goals first
                | simpa using hdiv_of 1 4
                | simpa using hdiv_of 2 2
                | simpa using hdiv_of 4 1
                | exfalso
                  simp_all [ZArith.BinInt.Z.le, ZArith.BinInt.Z.lt,
                    ZArith.BinInt.Z.of_nat, intOfZ, zOfInt,
                    hp1, hp2, hp4, hp8, hge2i, hge4i, hlt8i]
                  omega
            | right hge8 =>
                have hge8i : (8 : Int) ≤ intOfZ sz := by
                  change intOfZ (ZArith.BinInt.Z.of_nat 8) ≤ intOfZ sz at hge8
                  simpa [ZArith.BinInt.Z.of_nat, intOfZ, zOfInt, hp8] using hge8
                cases chunk <;>
                  simp [CompCert4Lean.Common.Memdata.align_chunk,
                    CompCert4Lean.Common.Memdata.size_chunk, block_alignment,
                    hz2, hge2, hz4, hge4, hz8, hge8, z0] at hsize ⊢
                all_goals first
                | simpa using hdiv_of 1 8
                | simpa using hdiv_of 2 4
                | simpa using hdiv_of 4 2
                | simpa using hdiv_of 8 1
                | exfalso
                  simp_all [ZArith.BinInt.Z.le, ZArith.BinInt.Z.lt,
                    ZArith.BinInt.Z.of_nat, intOfZ, zOfInt,
                    hp1, hp2, hp4, hp8, hge2i, hge4i, hge8i]
                  omega
  intro stacksize sz chunk hsize
  apply htrans (CompCert4Lean.Common.Memdata.align_chunk chunk)
    (block_alignment sz) (align stacksize (block_alignment sz))
  · exact hchunk_block sz chunk hsize
  · exact align_divides stacksize (block_alignment sz) (block_alignment_pos sz)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Cfrontend.Cminorgen

theorem assign_variable_sound : assign_variable_soundStatement := by
  intro cenv1 sz1 id sz cenv2 sz2 vars hassign hnorepet hpos hcompat hsep
  unfold assign_variable at hassign
  cases hassign
  change positive at id
  change PTree.tree Z at cenv1
  change List (positive × Z) at vars
  unfold cenv_compat at hcompat ⊢
  unfold cenv_separated at hsep ⊢
  have halign : ZArith.BinInt.Z.le sz1
      (align sz1 (block_alignment sz)) :=
    align_le sz1 (block_alignment sz) (block_alignment_pos sz)
  have hmax : ZArith.BinInt.Z.le ZArith.BinInt.Z.Z0
      (ZArith.BinInt.Z.max ZArith.BinInt.Z.Z0 sz) :=
    Zmax_bound_l _ _ _ (ZArith.BinInt.Z.le_refl _)
  have hadd : ∀ a b c d : Z,
      ZArith.BinInt.Z.le a b → ZArith.BinInt.Z.le c d →
      ZArith.BinInt.Z.le
        (ZArith.BinInt.Z.add a c) (ZArith.BinInt.Z.add b d) := by
    intro a b c d hab hcd
    change intOfZ (ZArith.BinInt.Z.add a c) ≤
      intOfZ (ZArith.BinInt.Z.add b d)
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
    change intOfZ a + intOfZ c ≤ intOfZ b + intOfZ d
    exact Int.add_le_add (show intOfZ a ≤ intOfZ b from hab)
      (show intOfZ c ≤ intOfZ d from hcd)
  have hletrans : ∀ a b c : Z,
      ZArith.BinInt.Z.le a b → ZArith.BinInt.Z.le b c →
      ZArith.BinInt.Z.le a c := by
    intro a b c hab hbc
    exact Int.le_trans (show intOfZ a ≤ intOfZ b from hab)
      (show intOfZ b ≤ intOfZ c from hbc)
  have halign_nonneg : ZArith.BinInt.Z.le ZArith.BinInt.Z.Z0
      (align sz1 (block_alignment sz)) := by
    exact hletrans _ _ _ hpos halign
  constructor
  · intro id' sz' hin
    change positive at id'
    rcases List.mem_append.mp hin with hvar | hnew
    · rcases hcompat id' sz' hvar with ⟨ofs, hget, hinj, hofs, hbound⟩
      have hid : id' ≠ id := by
        intro heq
        apply hnorepet
        have hm : id' ∈ List.map Prod.fst vars :=
          List.mem_map.mpr ⟨(id', sz'), hvar, rfl⟩
        rw [heq] at hm
        exact hm
      refine ⟨ofs,
        ?_,
        hinj, hofs, ?_⟩
      · exact (PTree.gso (A := Z) (i := id') (j := id)
          (x := align sz1 (block_alignment sz)) (m := cenv1) hid).trans hget
      · have hright : ZArith.BinInt.Z.le
            (align sz1 (block_alignment sz))
            (ZArith.BinInt.Z.add
              (align sz1 (block_alignment sz))
              (ZArith.BinInt.Z.max ZArith.BinInt.Z.Z0 sz)) :=
          by
            change intOfZ (align sz1 (block_alignment sz)) ≤
              intOfZ (ZArith.BinInt.Z.add
                (align sz1 (block_alignment sz))
                (ZArith.BinInt.Z.max ZArith.BinInt.Z.Z0 sz))
            simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
            change intOfZ (align sz1 (block_alignment sz)) ≤
              intOfZ (align sz1 (block_alignment sz)) +
                intOfZ (ZArith.BinInt.Z.max ZArith.BinInt.Z.Z0 sz)
            exact Int.le_add_of_nonneg_right hmax
        exact hletrans _ _ _ hbound
          (hletrans _ _ _ halign
            hright)
    · have hpair := List.mem_singleton.mp hnew
      have hid' : id' = id := congrArg Prod.fst hpair
      have hsz' : sz' = sz := congrArg Prod.snd hpair
      subst id'
      subst sz'
      refine ⟨align sz1 (block_alignment sz), PTree.gss _ _ _,
        inj_offset_aligned_block sz1 sz, halign_nonneg, ?_⟩
      exact ZArith.BinInt.Z.le_refl _
  · intro id1 sz1' ofs1 id2 sz2' ofs2 h1 h2 hg1 hg2 hne
    change positive at id1 id2
    rcases List.mem_append.mp h1 with h1var | h1new
    · rcases List.mem_append.mp h2 with h2var | h2new
      · have hid1 : id1 ≠ id := by
          intro heq
          apply hnorepet
          subst id1
          exact List.mem_map.mpr ⟨(id, sz1'), h1var, rfl⟩
        have hid2 : id2 ≠ id := by
          intro heq
          apply hnorepet
          subst id2
          exact List.mem_map.mpr ⟨(id, sz2'), h2var, rfl⟩
        rw [PTree.gso (A := Z) (i := id1) (j := id)
          (x := align sz1 (block_alignment sz)) (m := cenv1) hid1] at hg1
        rw [PTree.gso (A := Z) (i := id2) (j := id)
          (x := align sz1 (block_alignment sz)) (m := cenv1) hid2] at hg2
        exact hsep id1 sz1' ofs1 id2 sz2' ofs2 h1var h2var hg1 hg2 hne
      · have hpair := List.mem_singleton.mp h2new
        have hid2eq : id2 = id := congrArg Prod.fst hpair
        have hsz2eq : sz2' = sz := congrArg Prod.snd hpair
        subst id2
        subst sz2'
        have hcompat' := hcompat id1 sz1' h1var
        rcases hcompat' with ⟨ofs, hget, _, _, hbound⟩
        have hid1 : id1 ≠ id := by
          intro heq
          apply hnorepet
          subst id1
          exact List.mem_map.mpr ⟨(id, sz1'), h1var, rfl⟩
        rw [PTree.gso (A := Z) (i := id1) (j := id)
          (x := align sz1 (block_alignment sz)) (m := cenv1) hid1] at hg1
        have heq : ofs = ofs1 := by simpa [hget] using hg1
        subst ofs1
        have heq2 : align sz1 (block_alignment sz) = ofs2 := by
          have hss : PTree.get id
              (PTree.set id (align sz1 (block_alignment sz)) cenv1) =
              some (align sz1 (block_alignment sz)) :=
            PTree.gss id (align sz1 (block_alignment sz)) cenv1
          rw [hss] at hg2
          exact Option.some.inj hg2
        subst ofs2
        left
        have hsmall := hadd ofs ofs sz1'
          (ZArith.BinInt.Z.max ZArith.BinInt.Z.Z0 sz1')
          (ZArith.BinInt.Z.le_refl _) (ZArith.BinInt.Z.le_max_r _ _)
        exact hletrans _ _ _ (hletrans _ _ _ hsmall hbound) halign
    · rcases List.mem_append.mp h2 with h2var | h2new
      · have hpair := List.mem_singleton.mp h1new
        have hid1eq : id1 = id := congrArg Prod.fst hpair
        have hsz1eq : sz1' = sz := congrArg Prod.snd hpair
        subst id1
        subst sz1'
        have hcompat' := hcompat id2 sz2' h2var
        rcases hcompat' with ⟨ofs, hget, _, _, hbound⟩
        have hid2 : id2 ≠ id := by
          intro heq
          apply hnorepet
          subst id2
          exact List.mem_map.mpr ⟨(id, sz2'), h2var, rfl⟩
        rw [PTree.gso (A := Z) (i := id2) (j := id)
          (x := align sz1 (block_alignment sz)) (m := cenv1) hid2] at hg2
        have heq : ofs = ofs2 := by simpa [hget] using hg2
        subst ofs2
        have heq1 : align sz1 (block_alignment sz) = ofs1 := by
          have hss : PTree.get id
              (PTree.set id (align sz1 (block_alignment sz)) cenv1) =
              some (align sz1 (block_alignment sz)) :=
            PTree.gss id (align sz1 (block_alignment sz)) cenv1
          rw [hss] at hg1
          exact Option.some.inj hg1
        subst ofs1
        right
        have hsmall := hadd ofs ofs sz2'
          (ZArith.BinInt.Z.max ZArith.BinInt.Z.Z0 sz2')
          (ZArith.BinInt.Z.le_refl _) (ZArith.BinInt.Z.le_max_r _ _)
        exact hletrans _ _ _ (hletrans _ _ _ hsmall hbound) halign
      · have hid1 : id1 = id := congrArg Prod.fst (List.mem_singleton.mp h1new)
        have hid2 : id2 = id := congrArg Prod.fst (List.mem_singleton.mp h2new)
        exact (hne (hid1.trans hid2.symm)).elim

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Cfrontend.Cminorgen

local instance : OfNat Z 0 := ⟨ZArith.BinInt.Z.Z0⟩
local instance : LE Z := ⟨ZArith.BinInt.Z.le⟩

theorem assign_variables_sound : assign_variables_soundStatement := by
  intro vars' cenv1 sz1 cenv2 sz2 vars
  induction vars' generalizing cenv1 sz1 cenv2 sz2 vars with
  | nil =>
      intro hassign hnorepet hpos hcompat hsep
      simp [assign_variables] at hassign
      have hc : cenv1 = cenv2 := hassign.1
      have hs : sz1 = sz2 := hassign.2
      subst cenv2
      subst sz2
      simpa [List.append_nil] using (And.intro hcompat hsep)
  | cons hd tl ih =>
      cases hd with
      | mk id sz =>
          intro hassign hnorepet hpos hcompat hsep
          have hsplit := (list_norepet_app _ _ _).mp hnorepet
          have hhead := hsplit.1
          have hvars := hsplit.2.1
          have hdisj := hsplit.2.2
          have hid_not_vars : ¬ In id (List.map Prod.fst vars) := by
            intro hid
            exact hdisj id id (by simp) hid rfl
          have hstep : ∃ cenv' sz',
              assign_variable (cenv1, sz1) (id, sz) = (cenv', sz') := by
            exact ⟨(assign_variable (cenv1, sz1) (id, sz)).1,
              (assign_variable (cenv1, sz1) (id, sz)).2, rfl⟩
          rcases hstep with ⟨cenv', sz', hstep⟩
          have hassign' : assign_variables (cenv', sz') tl = (cenv2, sz2) := by
            simpa [assign_variables, hstep] using hassign
          have hhead' : list_norepet (id :: List.map Prod.fst tl) := by
            simpa using hhead
          have hhead_tail : list_norepet (List.map Prod.fst tl) := by
            cases hhead' with
            | cons _ _ htail => exact htail
          have hid_not_tail : ¬ In id (List.map Prod.fst tl) := by
            cases hhead' with
            | cons _ hnot _ => exact hnot
          have hdisj_tail_vars : list_disjoint
              (List.map Prod.fst tl) (List.map Prod.fst vars) := by
            intro x y hx hy hxy
            exact hdisj x y (by simp [hx]) hy hxy
          have hdisj_tail_new : list_disjoint
              (List.map Prod.fst tl) (List.map Prod.fst vars ++ [id]) := by
            intro x y hx hy
            rcases List.mem_append.mp hy with hyvars | hyid
            · exact hdisj_tail_vars x y hx hyvars
            · have hyeq : y = id := List.mem_singleton.mp hyid
              subst y
              intro hxy
              apply hid_not_tail
              rw [← hxy]
              exact hx
          have hnorepet_ih : list_norepet
              (List.map Prod.fst tl ++
                List.map Prod.fst (vars ++ [(id, sz)])) := by
            apply (list_norepet_app _ _ _).2
            refine ⟨hhead_tail, ?_, ?_⟩
            · simpa using (list_norepet_append _ _ _ hvars
                (list_norepet.cons id (by simp) (list_norepet.nil _))
                (by
                  intro x y hx hy
                  have hyeq : y = id := List.mem_singleton.mp hy
                  subst y
                  intro hxy
                  apply hid_not_vars
                  rw [← hxy]
                  exact hx))
            · simpa [List.map_append] using hdisj_tail_new
          have hpos' : 0 ≤ sz' := by
            have hincr := assign_variable_incr id sz cenv1 sz1 cenv' sz' hstep
            exact Int.le_trans hpos hincr
          have hcompat_sep := assign_variable_sound cenv1 sz1 id sz cenv' sz'
            vars hstep hid_not_vars hpos hcompat hsep
          have hrec := ih cenv' sz' cenv2 sz2 (vars ++ [(id, sz)])
            hassign' hnorepet_ih hpos' hcompat_sep.1 hcompat_sep.2
          simpa [List.append_assoc] using hrec

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation

theorem permutation_norepet : permutation_norepetStatement := by
  intro A l l' hperm
  induction hperm with
  | perm_nil =>
      intro _
      exact CompCert4Lean.Lib.Coqlib.list_norepet.nil _
  | perm_skip x h ih =>
      intro hn
      cases hn with
      | cons _ hnot htail =>
          exact CompCert4Lean.Lib.Coqlib.list_norepet.cons x (by
            intro hx
            apply hnot
            exact CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation_in
              x
              (CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation_sym h)
              hx) (ih htail)
  | perm_swap x y l =>
      intro hn
      cases hn with
      | cons _ hxy htail =>
          cases htail with
          | cons _ hx hrest =>
              exact CompCert4Lean.Lib.Coqlib.list_norepet.cons x (by
                intro hxl
                rcases List.mem_cons.mp hxl with hxeq | hxin
                · apply hxy
                  simpa [hxeq] using (List.Mem.head x : x ∈ x :: l)
                · exact hx hxin) (CompCert4Lean.Lib.Coqlib.list_norepet.cons y (by
                intro hyl
                exact hxy (List.Mem.tail x hyl)) hrest)
  | perm_trans h₁ h₂ ih₁ ih₂ =>
      intro hn
      exact ih₂ (ih₁ hn)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Cfrontend.Cminorgen

local instance : OfNat Z 0 := ⟨z0⟩
local instance : LE Z := ⟨ZArith.BinInt.Z.le⟩

theorem build_compilenv_sound : build_compilenv_soundStatement := by
  intro f cenv sz hbuild hnr
  unfold build_compilenv at hbuild
  have hsort : Permutation f.fn_vars (VarSort.sort f.fn_vars) :=
    VarSort.Permuted_sort_proof f.fn_vars
  have hmap :
      Permutation (List.map Prod.fst f.fn_vars)
        (List.map Prod.fst (VarSort.sort f.fn_vars)) :=
    Permutation_map Prod.fst hsort
  have hnr_sort :
      list_norepet (List.map Prod.fst (VarSort.sort f.fn_vars)) :=
    permutation_norepet _ _ _ hmap hnr
  have hcompat0 : cenv_compat (PTree.empty Z) [] z0 := by
    intro id sz h
    cases h
  have hsep0 : cenv_separated (PTree.empty Z) [] := by
    intro id1 sz1 ofs1 id2 sz2 ofs2 h1 h2 hg1 hg2 hne
    cases h1
  have hsorted :
      cenv_compat cenv (VarSort.sort f.fn_vars) sz ∧
        cenv_separated cenv (VarSort.sort f.fn_vars) := by
    apply assign_variables_sound (vars' := VarSort.sort f.fn_vars)
      (cenv1 := PTree.empty Z) (sz1 := z0)
      (cenv2 := cenv) (sz2 := sz) (vars := [])
    · exact hbuild
    · simpa using hnr_sort
    · exact ZArith.BinInt.Z.le_refl z0
    · exact hcompat0
    · exact hsep0
  rcases hsorted with ⟨hcompat, hsep⟩
  constructor
  · intro id sz' hmem
    exact hcompat id sz' (Permutation_in (id, sz') hsort hmem)
  · intro id1 sz1 ofs1 id2 sz2' ofs2 h1 h2 hg1 hg2 hne
    exact hsep id1 sz1 ofs1 id2 sz2' ofs2
      (Permutation_in (id1, sz1) hsort h1)
      (Permutation_in (id2, sz2') hsort h2) hg1 hg2 hne

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Lib.Maps

theorem create_undef_temps_val : create_undef_temps_valStatement := by
  intro id v temps
  induction temps with
  | nil =>
      intro h
      change PTree.get id (PTree.empty val) = some v at h
      have hempty : PTree.get id (PTree.empty val) = none := PTree.gempty val id
      rw [hempty] at h
      cases h
  | cons hd tl ih =>
      intro h
      change PTree.get id (PTree.set hd .Vundef (CS.create_undef_temps tl)) = some v at h
      have hget := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
        (A := val) id hd .Vundef (CS.create_undef_temps tl)
      rw [hget] at h
      cases hp : CompCert4Lean.Lib.Coqlib.peq id hd with
      | left heq =>
          subst id
          simp [hp] at h
          exact ⟨CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_eq hd tl,
            h.symm⟩
      | right hne =>
          have htail : PTree.get id (CS.create_undef_temps tl) = some v := by
            simpa [hp] using h
          rcases ih htail with ⟨hin, hv⟩
          exact ⟨CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_cons hd id tl hin, hv⟩

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Cfrontend.Cminorgen

theorem assign_variables_domain : assign_variables_domainStatement := by
  intro id vars
  induction vars with
  | nil =>
      intro cesz hget
      exact Or.inl (by simpa [assign_variables] using hget)
  | cons hd tl ih =>
      intro cesz hget
      have htail :
          PTree.get id (assign_variable cesz hd).1 ≠ none ∨
            In id (List.map Prod.fst tl) := by
        apply ih
        simpa [assign_variables] using hget
      rcases htail with hstep | hmem
      · rcases hd with ⟨id', sz⟩
        rcases cesz with ⟨cenv, stksz⟩
        change PTree.get id
            (PTree.set id' (align stksz (block_alignment sz)) cenv) ≠ none at hstep
        have hspec := PTree.gsspec_proof
          (A := Z) id id' (align stksz (block_alignment sz)) cenv
        cases heq : peq id id' with
        | left hid =>
            subst id
            exact Or.inr (List.Mem.head _)
        | right hne =>
            left
            rw [hspec] at hstep
            simpa [heq] using hstep
      · exact Or.inr (in_cons hd.1 id (List.map Prod.fst tl) hmem)

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Cfrontend.Cminorgen

theorem build_compilenv_domain : build_compilenv_domainStatement := by
  intro f cenv sz id ofs hbuild hget
  unfold build_compilenv at hbuild
  have hsort : Permutation f.fn_vars (VarSort.sort f.fn_vars) :=
    VarSort.Permuted_sort_proof f.fn_vars
  have hdomain :=
    assign_variables_domain id (VarSort.sort f.fn_vars) (PTree.empty Z, z0)
  rw [hbuild] at hdomain
  have hne : PTree.get id cenv ≠ none := by
    intro hnone
    rw [hnone] at hget
    cases hget
  rcases hdomain hne with hbase | hsorted
  · rw [PTree.gempty] at hbase
    exact False.elim (hbase rfl)
  · have hmap :
        Permutation (List.map Prod.fst (VarSort.sort f.fn_vars))
          (List.map Prod.fst f.fn_vars) :=
      Permutation_map Prod.fst (Permutation_sym hsort)
    exact Permutation_in id hmap hsorted

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Lib.Maps

theorem bind_parameters_agree_rec : bind_parameters_agree_recStatement := by
  intro f vars
  induction vars with
  | nil =>
      intro vals tvals le1 le2 te hbind hinj hmatch
      cases vals with
      | nil =>
          simp [CS.bind_parameters] at hbind
          cases hbind
          simpa [set_params'] using hmatch
      | cons v vs =>
          simp [CS.bind_parameters] at hbind
          cases hbind
  | cons id vars ih =>
      intro vals tvals le1 le2 te hbind hinj hmatch
      cases vals with
      | nil =>
          simp [CS.bind_parameters] at hbind
          cases hbind
      | cons v vs =>
          cases hinj with
          | inject_list_cons v tv vs tvals hhead htail =>
              have hmatch' :
                  match_temps f (PTree.set id v le1) (PTree.set id tv te) :=
                match_temps_assign f le1 te id v tv hmatch hhead
              have hrest := ih vs tvals (PTree.set id v le1) le2
                (PTree.set id tv te) hbind htail hmatch'
              simpa [set_params'] using hrest

end CompCert4Lean.Cfrontend.Cminorgenproof

namespace CompCert4Lean.Cfrontend.Cminorgenproof

open CompCert4Lean.Lib.Maps

theorem set_params'_outside : set_params'_outsideStatement := by
  intro id il vl te hnot
  induction il generalizing vl te with
  | nil => cases vl <;> rfl
  | cons i il ih =>
      cases vl with
      | nil =>
          have htail : ¬In id il := by
            intro h
            apply hnot
            exact List.Mem.tail i h
          have hrec := ih (vl := [])
            (te := (PTree.set i (.Vundef : val) te)) htail
          calc
            PTree.get id (set_params' [] (i :: il) te) =
                PTree.get id (set_params' [] il (PTree.set i (.Vundef : val) te)) := by
              simp only [set_params']
            _ = PTree.get id (PTree.set i (.Vundef : val) te) := hrec
            _ = PTree.get id te := by
              exact PTree.gso (A := val) (i := id) (j := i)
                (.Vundef : val) (show PTree.tree val from te) (by
                  intro hie
                  exact hnot (hie ▸ (List.Mem.head il : In i (i :: il))))
      | cons v vl =>
          have htail : ¬In id il := by
            intro h
            apply hnot
            exact List.Mem.tail i h
          have hrec := ih vl (PTree.set i v te) htail
          calc
            PTree.get id (set_params' (v :: vl) (i :: il) te) =
                PTree.get id (set_params' vl il (PTree.set i v te)) := by
              simp only [set_params']
            _ = PTree.get id (PTree.set i v te) := hrec
            _ = PTree.get id te := by
              exact PTree.gso (A := val) (i := id) (j := i) v
                (show PTree.tree val from te) (by
                  intro hie
                  exact hnot (hie ▸ (List.Mem.head il : In i (i :: il))))

end CompCert4Lean.Cfrontend.Cminorgenproof
