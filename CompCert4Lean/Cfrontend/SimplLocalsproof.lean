import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Cfrontend.Clight
import CompCert4Lean.Cfrontend.Cop
import CompCert4Lean.Cfrontend.Ctypes
import CompCert4Lean.Cfrontend.SimplLocals
import CompCert4Lean.Driver.Compopts
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.FSetFacts
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps

/-!
# Semantic preservation surface for SimplLocals

Definition-bearing translation of CompCert's `cfrontend/SimplLocalsproof.v`.
The simulation relations and executable predicates are present now; proof
bodies scheduled for the later proof-migration phase are represented by exact
proposition descriptors.
-/

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev type := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev memory_chunk := CompCert4Lean.Common.AST.memory_chunk
private abbrev program := CompCert4Lean.Cfrontend.Clight.program
private abbrev function := CompCert4Lean.Cfrontend.Clight.function
private abbrev fundef := CompCert4Lean.Cfrontend.Clight.fundef
private abbrev genv := CompCert4Lean.Cfrontend.Clight.genv
private abbrev env := CompCert4Lean.Cfrontend.Clight.env
private abbrev temp_env := CompCert4Lean.Cfrontend.Clight.temp_env
private abbrev expr := CompCert4Lean.Cfrontend.Clight.expr
private abbrev statement := CompCert4Lean.Cfrontend.Clight.statement
private abbrev labeled_statements := CompCert4Lean.Cfrontend.Clight.labeled_statements
private abbrev cont := CompCert4Lean.Cfrontend.Clight.cont
private abbrev state := CompCert4Lean.Cfrontend.Clight.machine_state
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev compilenv := CompCert4Lean.Cfrontend.SimplLocals.compilenv
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

/-! ## Generated finite-set facts surface -/

namespace VSF

private abbrev F := CompCert4Lean.Cfrontend.SimplLocals.VSet.MFProvider

abbrev add_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_iff F
abbrev empty_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.empty_iff F
abbrev mem_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_iff F

end VSF

def match_prog (cfg : CompilerConfig) (p tp : program) : Prop :=
  @match_program
    (CompCert4Lean.Cfrontend.Ctypes.fundef function) type
    (CompCert4Lean.Cfrontend.Ctypes.fundef function) type
    (CompCert4Lean.Cfrontend.Ctypes.Linker_fundef function)
    CompCert4Lean.Cfrontend.Ctypes.Linker_types
    (fun _ f tf => transf_fundef cfg f = .OK tf) Eq
    (program_of_program p) (program_of_program tp) ∧
    tp.prog_types = p.prog_types

inductive match_var (f : meminj) (cenv : compilenv) (e : env) (m : mem)
    (te : env) (tle : temp_env) (id : ident) : Prop where
  | match_var_lifted (b : block) (ty : type) (chunk : memory_chunk)
      (v tv : val)
      (ENV : PTree.get id e = some (b, ty))
      (TENV : PTree.get id te = none)
      (LIFTED : VSet.mem id cenv = true)
      (MAPPED : f b = none)
      (MODE : access_mode ty = .By_value chunk)
      (LOAD : Mem.load chunk m b .Z0 = some v)
      (TLENV : PTree.get id tle = some tv)
      (VINJ : Val.inject f v tv) :
      match_var f cenv e m te tle id
  | match_var_not_lifted (b : block) (ty : type) (b' : block)
      (ENV : PTree.get id e = some (b, ty))
      (TENV : PTree.get id te = some (b', ty))
      (LIFTED : VSet.mem id cenv = false)
      (MAPPED : f b = some (b', .Z0)) :
      match_var f cenv e m te tle id
  | match_var_not_local
      (ENV : PTree.get id e = none)
      (TENV : PTree.get id te = none)
      (LIFTED : VSet.mem id cenv = false) :
      match_var f cenv e m te tle id

export match_var (match_var_lifted match_var_not_lifted match_var_not_local)

structure match_envs (f : meminj) (cenv : compilenv)
    (e : env) (le : temp_env) (m : mem) (lo hi : block)
    (te : env) (tle : temp_env) (tlo thi : block) : Prop where
  me_vars : ∀ id, match_var f cenv e m te tle id
  me_temps : ∀ id v, PTree.get id le = some v →
    (∃ tv, PTree.get id tle = some tv ∧ Val.inject f v tv) ∧
    (VSet.mem id cenv = true → v = .Vundef)
  me_inj : ∀ id1 b1 ty1 id2 b2 ty2,
    PTree.get id1 e = some (b1, ty1) →
    PTree.get id2 e = some (b2, ty2) → id1 ≠ id2 → b1 ≠ b2
  me_range : ∀ id b ty, PTree.get id e = some (b, ty) → Ple lo b ∧ Plt b hi
  me_trange : ∀ id b ty, PTree.get id te = some (b, ty) → Ple tlo b ∧ Plt b thi
  me_mapped : ∀ id b' ty, PTree.get id te = some (b', ty) →
    ∃ b, f b = some (b', .Z0) ∧ PTree.get id e = some (b, ty)
  me_flat : ∀ id b' ty b delta,
    PTree.get id te = some (b', ty) → f b = some (b', delta) →
    PTree.get id e = some (b, ty) ∧ delta = .Z0
  me_incr : Ple lo hi
  me_tincr : Ple tlo thi

export match_envs (me_vars me_temps me_inj me_range me_trange me_mapped
  me_flat me_incr me_tincr)

abbrev mk_match_envs := @match_envs.mk

inductive val_casted_list : List val → List type → Prop where
  | nil : val_casted_list [] []
  | cons (v : val) (vl : List val) (ty : type) (tyl : List type) :
      val_casted v ty → val_casted_list vl tyl →
      val_casted_list (v :: vl) (ty :: tyl)

abbrev vcl_nil := @val_casted_list.nil
abbrev vcl_cons := @val_casted_list.cons

def cenv_for_gen (atk : VSet.t) (vars : List (ident × type)) : compilenv :=
  vars.foldr (add_local_variable atk) VSet.empty

def compat_cenv (atk : VSet.t) (cenv : compilenv) : Prop :=
  ∀ id, VSet.In id atk → VSet.In id cenv → False

def env_initial_value (e : env) (m : mem) : Prop :=
  ∀ id b ty chunk,
    PTree.get id e = some (b, ty) →
    access_mode ty = .By_value chunk →
    Mem.load chunk m b .Z0 = some .Vundef

def freelist_no_overlap : List (block × Z × Z) → Prop
  | [] => True
  | (b, lo, hi) :: rest =>
      freelist_no_overlap rest ∧
      ∀ b' lo' hi', (b', lo', hi') ∈ rest →
        b' ≠ b ∨ ZArith.BinInt.Z.le hi' lo ∨ ZArith.BinInt.Z.le hi lo'

inductive match_globalenvs (prog : program) (f : meminj) (bound : block) : Prop where
  | intro
      (DOMAIN : ∀ b, Plt b bound → f b = some (b, .Z0))
      (IMAGE : ∀ b1 b2 delta,
        f b1 = some (b2, delta) → Plt b2 bound → b1 = b2)
      (SYMBOLS : ∀ id b,
        Genv.find_symbol (Genv.globalenv (program_of_program prog)) id = some b → Plt b bound)
      (FUNCTIONS : ∀ b fd,
        Genv.find_funct_ptr (Genv.globalenv (program_of_program prog)) b = some fd → Plt b bound)
      (VARINFOS : ∀ b gv,
        Genv.find_var_info (Genv.globalenv (program_of_program prog)) b = some gv → Plt b bound) :
      match_globalenvs prog f bound

abbrev mk_match_globalenvs := @match_globalenvs.intro

inductive match_cont (cfg : CompilerConfig) (prog : program) (f : meminj) :
    compilenv → cont → cont → mem → block → block → Prop where
  | stop (cenv : compilenv) (m : mem) (bound tbound hi : block) :
      match_globalenvs prog f hi → Ple hi bound → Ple hi tbound →
      match_cont cfg prog f cenv .Kstop .Kstop m bound tbound
  | seq (cenv : compilenv) (s : statement) (k : cont)
      (ts : statement) (tk : cont) (m : mem) (bound tbound : block) :
      simpl_stmt cfg cenv s = .OK ts →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (addr_taken_stmt s) cenv →
      match_cont cfg prog f cenv (.Kseq s k) (.Kseq ts tk) m bound tbound
  | loop1 (cenv : compilenv) (s1 s2 : statement) (k : cont)
      (ts1 ts2 : statement) (tk : cont) (m : mem) (bound tbound : block) :
      simpl_stmt cfg cenv s1 = .OK ts1 → simpl_stmt cfg cenv s2 = .OK ts2 →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv →
      match_cont cfg prog f cenv (.Kloop1 s1 s2 k) (.Kloop1 ts1 ts2 tk) m bound tbound
  | loop2 (cenv : compilenv) (s1 s2 : statement) (k : cont)
      (ts1 ts2 : statement) (tk : cont) (m : mem) (bound tbound : block) :
      simpl_stmt cfg cenv s1 = .OK ts1 → simpl_stmt cfg cenv s2 = .OK ts2 →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv →
      match_cont cfg prog f cenv (.Kloop2 s1 s2 k) (.Kloop2 ts1 ts2 tk) m bound tbound
  | switch (cenv : compilenv) (k tk : cont) (m : mem) (bound tbound : block) :
      match_cont cfg prog f cenv k tk m bound tbound →
      match_cont cfg prog f cenv (.Kswitch k) (.Kswitch tk) m bound tbound
  | match_Kcall (cenv : compilenv) (optid : Option ident) (fn : function)
      (e : env) (le : temp_env) (k : cont) (tfn : function)
      (te : env) (tle : temp_env) (tk : cont) (m : mem)
      (hi thi lo tlo bound tbound : block) (x : Unit) :
      transf_function cfg fn = .OK tfn →
      match_envs f (cenv_for fn) e le m lo hi te tle tlo thi →
      match_cont cfg prog f (cenv_for fn) k tk m lo tlo →
      check_opttemp (cenv_for fn) optid = .OK x →
      Ple hi bound → Ple thi tbound →
      match_cont cfg prog f cenv (.Kcall optid fn e le k)
        (.Kcall optid tfn te tle tk) m bound tbound

abbrev match_Kstop := @match_cont.stop
abbrev match_Kseq := @match_cont.seq
abbrev match_Kloop1 := @match_cont.loop1
abbrev match_Kloop2 := @match_cont.loop2
abbrev match_Kswitch := @match_cont.switch
export match_cont (match_Kcall)

inductive match_states (cfg : CompilerConfig) (prog : program) : state → state → Prop where
  | regular (f : function) (s : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) (tf : function) (ts : statement)
      (tk : cont) (te : env) (tle : temp_env) (tm : mem)
      (j : meminj) (lo hi tlo thi : block) :
      transf_function cfg f = .OK tf →
      simpl_stmt cfg (cenv_for f) s = .OK ts →
      match_envs j (cenv_for f) e le m lo hi te tle tlo thi →
      match_cont cfg prog j (cenv_for f) k tk m lo tlo →
      Mem.inject j m tm →
      compat_cenv (addr_taken_stmt s) (cenv_for f) →
      Ple hi m.nextblock → Ple thi tm.nextblock →
      match_states cfg prog (.State f s k e le m) (.State tf ts tk te tle tm)
  | call (fd : fundef) (vargs : List val) (k : cont) (m : mem)
      (tfd : fundef) (tvargs : List val) (tk : cont) (tm : mem)
      (j : meminj) (targs : List type) (tres : type) (cconv : calling_convention) :
      transf_fundef cfg fd = .OK tfd →
      (∀ cenv, match_cont cfg prog j cenv k tk m m.nextblock tm.nextblock) →
      Mem.inject j m tm → Val.inject_list j vargs tvargs →
      type_of_fundef fd = .Tfunction targs tres cconv →
      val_casted_list vargs targs →
      match_states cfg prog (.Callstate fd vargs k m) (.Callstate tfd tvargs tk tm)
  | return_ (v : val) (k : cont) (m : mem) (tv : val) (tk : cont)
      (tm : mem) (j : meminj) :
      (∀ cenv, match_cont cfg prog j cenv k tk m m.nextblock tm.nextblock) →
      Mem.inject j m tm → Val.inject j v tv →
      match_states cfg prog (.Returnstate v k m) (.Returnstate tv tk tm)

abbrev match_regular_states := @match_states.regular
abbrev match_call_state := @match_states.call
abbrev match_return_state := @match_states.return_

/-! ## Exact statement descriptors for later proof migration -/

def match_transf_programStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program),
    transf_program cfg p = .OK tp → match_prog cfg p tp

def comp_env_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    (globalenv tp).genv_cenv = (globalenv p).genv_cenv

def symbols_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    ∀ id, Genv.find_symbol (globalenv tp).genv_genv id =
      Genv.find_symbol (globalenv p).genv_genv id

def senv_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    Senv.equiv (Genv.to_senv (globalenv p).genv_genv)
      (Genv.to_senv (globalenv tp).genv_genv)

def function_ptr_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    ∀ b fd, Genv.find_funct_ptr (globalenv p).genv_genv b = some fd →
      ∃ tfd, Genv.find_funct_ptr (globalenv tp).genv_genv b = some tfd ∧
        transf_fundef cfg fd = .OK tfd

def type_of_fundef_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (fd tfd : fundef),
    transf_fundef cfg fd = .OK tfd → type_of_fundef tfd = type_of_fundef fd

def match_envs_invariantStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi f' m',
    match_envs f cenv e le m lo hi te tle tlo thi →
    (∀ b chunk v, f b = none → Ple lo b ∧ Plt b hi →
      Mem.load chunk m b (.Z0 : Z) = some v →
      Mem.load chunk m' b (.Z0 : Z) = some v) →
    inject_incr f f' →
    (∀ b, Ple lo b ∧ Plt b hi → f' b = f b) →
    (∀ b b' delta, f' b = some (b', delta) →
      Ple tlo b' ∧ Plt b' thi → f' b = f b) →
    match_envs f' cenv e le m' lo hi te tle tlo thi

def match_envs_extcallStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi tm f' m',
    match_envs f cenv e le m lo hi te tle tlo thi →
    Mem.unchanged_on (loc_unmapped f) m m' →
    inject_incr f f' → inject_separated f f' m tm →
    Ple hi m.nextblock → Ple thi tm.nextblock →
    match_envs f' cenv e le m' lo hi te tle tlo thi

def val_casted_load_resultStatement : Prop :=
  ∀ v ty chunk, val_casted v ty → access_mode ty = .By_value chunk →
    Val.load_result chunk v = v

def val_casted_injectStatement : Prop :=
  ∀ f v v' ty, Val.inject f v v' → val_casted v ty → val_casted v' ty

def forall2_val_casted_injectStatement : Prop :=
  ∀ f vl vl', Val.inject_list f vl vl' →
    ∀ tyl, CompCert4Lean.Lib.Coqlib.list_forall2 val_casted vl tyl →
      CompCert4Lean.Lib.Coqlib.list_forall2 val_casted vl' tyl

def val_casted_list_paramsStatement : Prop :=
  ∀ params vl, val_casted_list vl (type_of_params params) →
    CompCert4Lean.Lib.Coqlib.list_forall2 val_casted vl (params.map Prod.snd)

def make_cast_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tprog : program) e le m a v1 tto v2,
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) (globalenv tprog) e le m a v1 →
    sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 (typeof a) tto m = some v2 →
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) (globalenv tprog) e le m
        (make_cast a tto) v2

def cast_typeconvStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ v ty m, val_casted v ty →
    sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v ty (typeconv ty) m = some v

def step_Sdebug_tempStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tprog : program) f id ty k e le m v,
    PTree.get id le = some v → val_casted v ty →
    step2
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (globalenv tprog)
      (.State f (Sdebug_temp id ty) k e le m) E0
      (.State f .Sskip k e le m)

def step_Sdebug_varStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tprog : program) f id ty k e le m b,
    PTree.get id e = some (b, ty) →
    step2
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (globalenv tprog)
      (.State f (Sdebug_var id ty) k e le m) E0
      (.State f .Sskip k e le m)

def step_Sset_debugStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (tprog : program)
    f id ty a k e le m v v',
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) (globalenv tprog) e le m a v →
    sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v (typeof a) ty m = some v' →
    plus
      (step2
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
      (globalenv tprog) (.State f (Sset_debug cfg id ty a) k e le m) E0
      (.State f .Sskip k e (PTree.set id v' le) m)

def step_add_debug_varsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (tprog : program)
    f s e le m vars k,
    (∀ id ty, (id, ty) ∈ vars → ∃ b, PTree.get id e = some (b, ty)) →
    star
      (step2
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
      (globalenv tprog) (.State f (add_debug_vars cfg vars s) k e le m) E0
      (.State f s k e le m)

def bind_parameter_temps_invStatement : Prop :=
  ∀ id params args le le',
    bind_parameter_temps params args le = some le' →
    id ∉ var_names params → PTree.get id le' = PTree.get id le

def step_add_debug_paramsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (tprog : program)
    f s k e le m params vl le1,
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names params) →
    CompCert4Lean.Lib.Coqlib.list_forall2 val_casted vl (params.map Prod.snd) →
    bind_parameter_temps params vl le1 = some le →
    star
      (step2
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
      (globalenv tprog) (.State f (add_debug_params cfg params s) k e le m) E0
      (.State f s k e le m)

def match_envs_assign_liftedStatement : Prop :=
  ∀ (prog : program) f cenv e le m lo hi te tle tlo thi b ty v m' id tv,
    match_envs f cenv e le m lo hi te tle tlo thi →
    PTree.get id e = some (b, ty) → val_casted v ty → Val.inject f v tv →
    assign_loc (globalenv prog).genv_cenv ty m b Ptrofs.zero .Full v m' →
    VSet.mem id cenv = true →
    match_envs f cenv e le m' lo hi te (PTree.set id tv tle) tlo thi

def match_envs_set_tempStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi id v tv x,
    match_envs f cenv e le m lo hi te tle tlo thi → Val.inject f v tv →
    check_temp cenv id = .OK x →
    match_envs f cenv e (PTree.set id v le) m lo hi te
      (PTree.set id tv tle) tlo thi

def match_envs_set_opttempStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi optid v tv x,
    match_envs f cenv e le m lo hi te tle tlo thi → Val.inject f v tv →
    check_opttemp cenv optid = .OK x →
    match_envs f cenv e (set_opttemp optid v le) m lo hi te
      (set_opttemp optid tv tle) tlo thi

def match_envs_temps_extenStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi tle',
    match_envs f cenv e le m lo hi te tle tlo thi →
    (∀ id, PTree.get id tle' = PTree.get id tle) →
    match_envs f cenv e le m lo hi te tle' tlo thi

def match_envs_change_tempStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi id v,
    match_envs f cenv e le m lo hi te tle tlo thi →
    PTree.get id le = none → VSet.mem id cenv = false →
    match_envs f cenv e le m lo hi te (PTree.set id v tle) tlo thi

def add_local_variable_charactStatement : Prop :=
  ∀ id ty atk cenv id1,
    VSet.In id1 (add_local_variable atk (id, ty) cenv) ↔
      VSet.In id1 cenv ∨
        ∃ chunk, access_mode ty = .By_value chunk ∧ id = id1 ∧
          VSet.mem id atk = false

def cenv_for_gen_domainStatement : Prop :=
  ∀ atk id vars, VSet.In id (cenv_for_gen atk vars) → id ∈ var_names vars

def cenv_for_gen_by_valueStatement : Prop :=
  ∀ atk id ty vars, (id, ty) ∈ vars →
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names vars) →
    VSet.In id (cenv_for_gen atk vars) →
    ∃ chunk, access_mode ty = .By_value chunk

def cenv_for_gen_compatStatement : Prop :=
  ∀ atk id vars, VSet.In id (cenv_for_gen atk vars) → VSet.mem id atk = false

def compat_cenv_forStatement : Prop :=
  ∀ f, compat_cenv (addr_taken_stmt f.fn_body) (cenv_for f)

def compat_cenv_union_lStatement : Prop :=
  ∀ atk1 atk2 cenv,
    compat_cenv (VSet.union atk1 atk2) cenv → compat_cenv atk1 cenv

def compat_cenv_union_rStatement : Prop :=
  ∀ atk1 atk2 cenv,
    compat_cenv (VSet.union atk1 atk2) cenv → compat_cenv atk2 cenv

def compat_cenv_emptyStatement : Prop :=
  ∀ cenv, compat_cenv VSet.empty cenv

def alloc_variables_nextblockStatement : Prop :=
  ∀ ge e m vars e' m', alloc_variables ge e m vars e' m' →
    Ple m.nextblock m'.nextblock

def alloc_variables_rangeStatement : Prop :=
  ∀ ge id b ty e m vars e' m', alloc_variables ge e m vars e' m' →
    PTree.get id e' = some (b, ty) →
    PTree.get id e = some (b, ty) ∨ Ple m.nextblock b ∧ Plt b m'.nextblock

def alloc_variables_injectiveStatement : Prop :=
  ∀ ge id1 b1 ty1 id2 b2 ty2 e m vars e' m',
    alloc_variables ge e m vars e' m' →
    (PTree.get id1 e = some (b1, ty1) → PTree.get id2 e = some (b2, ty2) →
      id1 ≠ id2 → b1 ≠ b2) →
    (∀ id b ty, PTree.get id e = some (b, ty) → Plt b m.nextblock) →
    PTree.get id1 e' = some (b1, ty1) → PTree.get id2 e' = some (b2, ty2) →
    id1 ≠ id2 → b1 ≠ b2

def match_alloc_variablesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ cenv e m vars e' m', alloc_variables ge e m vars e' m' →
    ∀ j tm te, CompCert4Lean.Lib.Coqlib.list_norepet (var_names vars) →
    Mem.inject j m tm →
    ∃ j' te' tm',
      alloc_variables tge te tm (remove_lifted cenv vars) te' tm' ∧
      Mem.inject j' m' tm' ∧ inject_incr j j' ∧
      (∀ b, Mem.valid_block m b → j' b = j b) ∧
      (∀ b b' delta, j' b = some (b', delta) →
        Mem.valid_block tm b' → j' b = j b) ∧
      (∀ b b' delta, j' b = some (b', delta) → ¬ Mem.valid_block tm b' →
        ∃ id ty, PTree.get id e' = some (b, ty) ∧
          PTree.get id te' = some (b', ty) ∧ delta = (.Z0 : Z)) ∧
      (∀ id ty, (id, ty) ∈ vars → ∃ b,
        PTree.get id e' = some (b, ty) ∧
        if VSet.mem id cenv then PTree.get id te' = PTree.get id te ∧ j' b = none
        else ∃ tb, PTree.get id te' = some (tb, ty) ∧ j' b = some (tb, (.Z0 : Z))) ∧
      (∀ id, id ∉ var_names vars →
        PTree.get id e' = PTree.get id e ∧ PTree.get id te' = PTree.get id te)

def alloc_variables_loadStatement : Prop :=
  ∀ (prog : program) e m vars e' m',
    alloc_variables (globalenv prog) e m vars e' m' →
    ∀ chunk b ofs v, Mem.load chunk m b ofs = some v →
      Mem.load chunk m' b ofs = some v

def sizeof_by_valueStatement : Prop :=
  ∀ (prog : program) ty chunk, access_mode ty = .By_value chunk →
    ZArith.BinInt.Z.le (CompCert4Lean.Common.Memdata.size_chunk chunk)
      (sizeof (globalenv prog).genv_cenv ty)

def alloc_variables_initial_valueStatement : Prop :=
  ∀ (prog : program) e m vars e' m',
    alloc_variables (globalenv prog) e m vars e' m' →
    env_initial_value e m → env_initial_value e' m'

def create_undef_temps_charactStatement : Prop :=
  ∀ id ty vars, (id, ty) ∈ vars → PTree.get id (create_undef_temps vars) = some .Vundef

def create_undef_temps_invStatement : Prop :=
  ∀ vars id v, PTree.get id (create_undef_temps vars) = some v →
    v = .Vundef ∧ id ∈ var_names vars

def create_undef_temps_extenStatement : Prop :=
  ∀ id l1 l2, (id ∈ var_names l1 ↔ id ∈ var_names l2) →
    PTree.get id (create_undef_temps l1) = PTree.get id (create_undef_temps l2)

def var_names_appStatement : Prop :=
  ∀ vars1 vars2, var_names (vars1 ++ vars2) = var_names vars1 ++ var_names vars2

def filter_appStatement : Prop :=
  ∀ (A : Type) (f : A → Bool) l1 l2,
    List.filter f (l1 ++ l2) = List.filter f l1 ++ List.filter f l2

def filter_charactStatement : Prop :=
  ∀ (A : Type) (f : A → Bool) x l,
    x ∈ List.filter f l ↔ x ∈ l ∧ f x = true

def filter_norepetStatement : Prop :=
  ∀ (A : Type) (f : A → Bool) l,
    CompCert4Lean.Lib.Coqlib.list_norepet l →
    CompCert4Lean.Lib.Coqlib.list_norepet (List.filter f l)

def filter_mapStatement : Prop :=
  ∀ (A B : Type) (f : A → B) (pa : A → Bool) (pb : B → Bool),
    (∀ a, pb (f a) = pa a) → ∀ l,
      List.map f (List.filter pa l) = List.filter pb (List.map f l)

def create_undef_temps_liftedStatement : Prop :=
  ∀ id f, id ∉ var_names f.fn_params →
    PTree.get id (create_undef_temps (add_lifted (cenv_for f) f.fn_vars f.fn_temps)) =
    PTree.get id (create_undef_temps
      (add_lifted (cenv_for f) (f.fn_params ++ f.fn_vars) f.fn_temps))

def vars_and_temps_propertiesStatement : Prop :=
  ∀ cenv params vars temps,
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names params ++ var_names vars) →
    list_disjoint (var_names params) (var_names temps) →
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names params) ∧
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names (remove_lifted cenv (params ++ vars))) ∧
    list_disjoint (var_names params) (var_names (add_lifted cenv vars temps))

def match_envs_alloc_variablesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ cenv m vars e m' temps j tm,
    alloc_variables ge empty_env m vars e m' →
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names vars) →
    Mem.inject j m tm →
    (∀ id ty, (id, ty) ∈ vars → VSet.mem id cenv = true →
      ∃ chunk, access_mode ty = .By_value chunk) →
    (∀ id, VSet.mem id cenv = true → id ∈ var_names vars) →
    ∃ j' te tm',
      alloc_variables tge empty_env tm (remove_lifted cenv vars) te tm' ∧
      match_envs j' cenv e (create_undef_temps temps) m'
        m.nextblock m'.nextblock te
        (create_undef_temps (add_lifted cenv vars temps)) tm.nextblock tm'.nextblock ∧
      Mem.inject j' m' tm' ∧ inject_incr j j' ∧
      (∀ b, Mem.valid_block m b → j' b = j b) ∧
      (∀ b b' delta, j' b = some (b', delta) →
        Mem.valid_block tm b' → j' b = j b) ∧
      (∀ id ty, (id, ty) ∈ vars → VSet.mem id cenv = false →
        ∃ b, PTree.get id te = some (b, ty))

def assign_loc_injectStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ f ty m loc ofs bf v m' tm loc' ofs' v',
    assign_loc ge.genv_cenv ty m loc ofs bf v m' →
    Val.inject f (.Vptr loc ofs) (.Vptr loc' ofs') → Val.inject f v v' →
    Mem.inject f m tm →
    ∃ tm', assign_loc tge.genv_cenv ty tm loc' ofs' bf v' tm' ∧
      Mem.inject f m' tm' ∧
      ∀ b chunk value, f b = none →
        Mem.load chunk m b (.Z0 : Z) = some value →
        Mem.load chunk m' b (.Z0 : Z) = some value

def assign_loc_nextblockStatement : Prop :=
  ∀ ge ty m b ofs bf v m', assign_loc ge ty m b ofs bf v m' →
    m'.nextblock = m.nextblock

def store_params_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (p tp : program),
    match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ j f k cenv le lo hi te tlo thi e m params args m',
    bind_parameters ge e m params args m' →
    ∀ s tm tle1 tle2 targs,
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names params) →
    CompCert4Lean.Lib.Coqlib.list_forall2 val_casted args (params.map Prod.snd) →
    Val.inject_list j args targs →
    match_envs j cenv e le m lo hi te tle1 tlo thi → Mem.inject j m tm →
    (∀ id, id ∉ var_names params → PTree.get id tle2 = PTree.get id tle1) →
    (∀ id, id ∈ var_names params → PTree.get id le = none) →
    ∃ tle tm',
      star
        (step2
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        tge (.State f (store_params cenv params s) k te tle tm) E0
        (.State f s k te tle tm') ∧
      bind_parameter_temps params targs tle2 = some tle ∧
      Mem.inject j m' tm' ∧ match_envs j cenv e le m' lo hi te tle tlo thi ∧
      tm'.nextblock = tm.nextblock

def bind_parameters_nextblockStatement : Prop :=
  ∀ ge e m params args m', bind_parameters ge e m params args m' →
    m'.nextblock = m.nextblock

def bind_parameters_loadStatement : Prop :=
  ∀ ge e chunk b ofs,
    (∀ id b' ty, PTree.get id e = some (b', ty) → b ≠ b') →
    ∀ m params args m', bind_parameters ge e m params args m' →
      Mem.load chunk m' b ofs = Mem.load chunk m b ofs

def free_blocks_of_env_perm_1Statement : Prop :=
  ∀ ce m e m' id b ty ofs k permission,
    Mem.free_list m (blocks_of_env ce e) = some m' →
    PTree.get id e = some (b, ty) → Mem.perm m' b ofs k permission →
    ZArith.BinInt.Z.le (.Z0 : Z) ofs ∧
      ZArith.BinInt.Z.lt ofs (sizeof ce.genv_cenv ty) → False

def free_list_perm'Statement : Prop :=
  ∀ b lo hi l m m', Mem.free_list m l = some m' → (b, lo, hi) ∈ l →
    Mem.range_perm m b lo hi .Cur .Freeable

def free_blocks_of_env_perm_2Statement : Prop :=
  ∀ ce m e m' id b ty, Mem.free_list m (blocks_of_env ce e) = some m' →
    PTree.get id e = some (b, ty) →
    Mem.range_perm m b (.Z0 : Z) (sizeof ce.genv_cenv ty) .Cur .Freeable

def can_free_listStatement : Prop :=
  ∀ l m,
    (∀ b lo hi, (b, lo, hi) ∈ l → Mem.range_perm m b lo hi .Cur .Freeable) →
    freelist_no_overlap l → ∃ m', Mem.free_list m l = some m'

def blocks_of_env_no_overlapStatement : Prop :=
  ∀ (ge : genv) j cenv e le m lo hi te tle tlo thi tm,
    match_envs j cenv e le m lo hi te tle tlo thi → Mem.inject j m tm →
    (∀ id b ty, PTree.get id e = some (b, ty) →
      Mem.range_perm m b (.Z0 : Z) (sizeof ge.genv_cenv ty) .Cur .Freeable) →
    ∀ (l : List (ident × (block × type))),
    CompCert4Lean.Lib.Coqlib.list_norepet (l.map Prod.fst) →
    (∀ id bty, (id, bty) ∈ l → PTree.get id te = some bty) →
    freelist_no_overlap (l.map (block_of_binding ge))

def free_list_right_injectStatement : Prop :=
  ∀ j m1 l m2 m2', Mem.inject j m1 m2 → Mem.free_list m2 l = some m2' →
    (∀ b1 b2 delta lo hi ofs k permission,
      j b1 = some (b2, delta) → (b2, lo, hi) ∈ l →
      Mem.perm m1 b1 ofs k permission →
      ZArith.BinInt.Z.le lo (ZArith.BinInt.Z.add ofs delta) ∧
        ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add ofs delta) hi → False) →
    Mem.inject j m1 m2'

def blocks_of_env_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    ∀ e, blocks_of_env (globalenv tp) e = blocks_of_env (globalenv p) e

def match_envs_free_blocksStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ j cenv e le m lo hi te tle tlo thi m' tm,
    match_envs j cenv e le m lo hi te tle tlo thi → Mem.inject j m tm →
    Mem.free_list m (blocks_of_env ge e) = some m' →
    ∃ tm', Mem.free_list tm (blocks_of_env tge te) = some tm' ∧ Mem.inject j m' tm'

def match_globalenvs_preserves_globalsStatement : Prop :=
  ∀ (prog : program) f, (∃ bound, match_globalenvs prog f bound) →
    meminj_preserves_globals fundef type (Genv.globalenv (program_of_program prog)) f

def typeof_simpl_exprStatement : Prop :=
  ∀ cenv a, typeof (simpl_expr cenv a) = typeof a

def deref_loc_injectStatement : Prop :=
  ∀ m tm f, Mem.inject f m tm →
    ∀ ty loc ofs bf v loc' ofs', deref_loc ty m loc ofs bf v →
    Val.inject f (.Vptr loc ofs) (.Vptr loc' ofs') →
    ∃ tv, deref_loc ty tm loc' ofs' bf tv ∧ Val.inject f v tv

def eval_simpl_exprStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ e te le tle m tm f cenv lo hi tlo thi,
    match_envs f cenv e le m lo hi te tle tlo thi → Mem.inject f m tm →
    (∃ bound, match_globalenvs p f bound) →
    ∀ a v,
      eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v →
      compat_cenv (addr_taken_expr a) cenv →
      ∃ tv,
        eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) tge te tle tm
            (simpl_expr cenv a) tv ∧ Val.inject f v tv

def eval_simpl_lvalueStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ e te le tle m tm f cenv lo hi tlo thi,
    match_envs f cenv e le m lo hi te tle tlo thi → Mem.inject f m tm →
    (∃ bound, match_globalenvs p f bound) →
    ∀ a b ofs bf,
      eval_lvalue
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a b ofs bf →
    compat_cenv (addr_taken_expr a) cenv →
    (match a with | .Evar id _ => VSet.mem id cenv = false | _ => True) →
    ∃ b' ofs',
      eval_lvalue
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) tge te tle tm
          (simpl_expr cenv a) b' ofs' bf ∧
      Val.inject f (.Vptr b ofs) (.Vptr b' ofs')

def eval_simpl_exprlistStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ e te le tle m tm f cenv lo hi tlo thi,
    match_envs f cenv e le m lo hi te tle tlo thi → Mem.inject f m tm →
    (∃ bound, match_globalenvs p f bound) →
    ∀ al tyl vl,
      eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m al tyl vl →
    compat_cenv (addr_taken_exprlist al) cenv →
    val_casted_list vl tyl ∧
      ∃ tvl,
        eval_exprlist
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) tge te tle tm
            (simpl_exprlist cenv al) tyl tvl ∧
        Val.inject_list f vl tvl

def match_cont_invariantStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f' m' f cenv k tk m bound tbound,
    match_cont cfg prog f cenv k tk m bound tbound →
    (∀ b chunk v, f b = none → Plt b bound →
      Mem.load chunk m b (.Z0 : Z) = some v →
      Mem.load chunk m' b (.Z0 : Z) = some v) →
    inject_incr f f' →
    (∀ b, Plt b bound → f' b = f b) →
    (∀ b b' delta, f' b = some (b', delta) → Plt b' tbound → f' b = f b) →
    match_cont cfg prog f' cenv k tk m' bound tbound

def match_cont_assign_locStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound ty loc ofs bf v m',
    match_cont cfg prog f cenv k tk m bound tbound →
    assign_loc (globalenv prog).genv_cenv ty m loc ofs bf v m' → Ple bound loc →
    match_cont cfg prog f cenv k tk m' bound tbound

def match_cont_extcallStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound tm f' m',
    match_cont cfg prog f cenv k tk m bound tbound →
    Mem.unchanged_on (loc_unmapped f) m m' → inject_incr f f' →
    inject_separated f f' m tm → Ple bound m.nextblock → Ple tbound tm.nextblock →
    match_cont cfg prog f' cenv k tk m' bound tbound

def match_cont_incr_boundsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound,
    match_cont cfg prog f cenv k tk m bound tbound →
    ∀ bound' tbound', Ple bound bound' → Ple tbound tbound' →
      match_cont cfg prog f cenv k tk m bound' tbound'

def match_cont_change_cenvStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound cenv',
    match_cont cfg prog f cenv k tk m bound tbound → is_call_cont k →
    match_cont cfg prog f cenv' k tk m bound tbound

def match_cont_is_call_contStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound,
    match_cont cfg prog f cenv k tk m bound tbound → is_call_cont k → is_call_cont tk

def match_cont_call_contStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound,
    match_cont cfg prog f cenv k tk m bound tbound → ∀ cenv',
    match_cont cfg prog f cenv' (call_cont k) (call_cont tk) m bound tbound

def free_list_nextblockStatement : Prop :=
  ∀ l m m', Mem.free_list m l = some m' → m'.nextblock = m.nextblock

def free_list_loadStatement : Prop :=
  ∀ chunk b' l m m', Mem.free_list m l = some m' →
    (∀ b lo hi, (b, lo, hi) ∈ l → Plt b' b) →
    Mem.load chunk m' b' (.Z0 : Z) = Mem.load chunk m b' (.Z0 : Z)

def match_cont_free_envStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    let ge := globalenv prog
    let tge := globalenv tprog
    ∀ f cenv e le m lo hi te tle tm tlo thi k tk m' tm',
    match_envs f cenv e le m lo hi te tle tlo thi →
    match_cont cfg prog f cenv k tk m lo tlo → Ple hi m.nextblock →
    Ple thi tm.nextblock → Mem.free_list m (blocks_of_env ge e) = some m' →
    Mem.free_list tm (blocks_of_env tge te) = some tm' →
    match_cont cfg prog f cenv k tk m' m'.nextblock tm'.nextblock

def match_cont_globalenvStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound,
    match_cont cfg prog f cenv k tk m bound tbound →
    ∃ bound, match_globalenvs prog f bound

def match_cont_find_functStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    ∀ f cenv k tk m bound tbound vf fd tvf,
    match_cont cfg p f cenv k tk m bound tbound →
    Genv.find_funct (Genv.globalenv (program_of_program p)) vf = some fd → Val.inject f vf tvf →
    ∃ tfd, Genv.find_funct (Genv.globalenv (program_of_program tp)) tvf = some tfd ∧
      transf_fundef cfg fd = .OK tfd

def is_liftable_var_charactStatement : Prop :=
  ∀ cenv a,
    match is_liftable_var cenv a with
    | some id => ∃ ty, a = .Evar id ty ∧ VSet.mem id cenv = true
    | none => match a with | .Evar id _ => VSet.mem id cenv = false | _ => True

def simpl_select_switchStatement : Prop :=
  ∀ cfg cenv n ls tls, simpl_lblstmt cfg cenv ls = .OK tls →
    simpl_lblstmt cfg cenv (select_switch n ls) = .OK (select_switch n tls)

def simpl_seq_of_labeled_statementStatement : Prop :=
  ∀ cfg cenv ls tls, simpl_lblstmt cfg cenv ls = .OK tls →
    simpl_stmt cfg cenv (seq_of_labeled_statement ls) =
      .OK (seq_of_labeled_statement tls)

def compat_cenv_select_switchStatement : Prop :=
  ∀ cenv n ls, compat_cenv (addr_taken_lblstmt ls) cenv →
    compat_cenv (addr_taken_lblstmt (select_switch n ls)) cenv

def addr_taken_seq_of_labeled_statementStatement : Prop :=
  ∀ ls, addr_taken_stmt (seq_of_labeled_statement ls) = addr_taken_lblstmt ls

def simpl_find_labelStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv m bound tbound lbl s k ts tk,
    simpl_stmt cfg cenv s = .OK ts →
    match_cont cfg prog f cenv k tk m bound tbound →
    compat_cenv (addr_taken_stmt s) cenv →
    match find_label lbl s k with
    | none => find_label lbl ts tk = none
    | some (s', k') => ∃ ts' tk', find_label lbl ts tk = some (ts', tk') ∧
        compat_cenv (addr_taken_stmt s') cenv ∧ simpl_stmt cfg cenv s' = .OK ts' ∧
        match_cont cfg prog f cenv k' tk' m bound tbound

def simpl_find_label_lsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv m bound tbound lbl ls k tls tk,
    simpl_lblstmt cfg cenv ls = .OK tls →
    match_cont cfg prog f cenv k tk m bound tbound →
    compat_cenv (addr_taken_lblstmt ls) cenv →
    match find_label_ls lbl ls k with
    | none => find_label_ls lbl tls tk = none
    | some (s', k') => ∃ ts' tk', find_label_ls lbl tls tk = some (ts', tk') ∧
        compat_cenv (addr_taken_stmt s') cenv ∧ simpl_stmt cfg cenv s' = .OK ts' ∧
        match_cont cfg prog f cenv k' tk' m bound tbound

def find_label_store_paramsStatement : Prop :=
  ∀ lbl cenv s k params,
    find_label lbl (store_params cenv params s) k = find_label lbl s k

def find_label_add_debug_varsStatement : Prop :=
  ∀ cfg lbl s k vars,
    find_label lbl (add_debug_vars cfg vars s) k = find_label lbl s k

def find_label_add_debug_paramsStatement : Prop :=
  ∀ cfg lbl s k vars,
    find_label lbl (add_debug_params cfg vars s) k = find_label lbl s k

def step_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (p tp : program),
    match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ S1 t S2,
      step1
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge S1 t S2 →
      ∀ S1',
      match_states cfg p S1 S1' →
      ∃ S2',
        plus
          (step2
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi)
          tge S1' t S2' ∧ match_states cfg p S2 S2'

def initial_states_simulationStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    ∀ S, initial_state p S → ∃ R, initial_state tp R ∧
      match_states cfg p S R

def final_states_simulationStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p : program) S R result,
    match_states cfg p S R → final_state S result → final_state R result

def transf_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (p tp : program),
    match_prog cfg p tp →
    forward_simulation
      (semantics1
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi p)
      (semantics2
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tp)

def TransfSimplLocalsLinkStatement
    (cfg : CompilerConfig)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations) : Prop :=
  @CompCert4Lean.Common.Linking.TransfLink program program
    (Ctypes.Linker_program function clightLinkerCertificate)
    (Ctypes.Linker_program function clightLinkerCertificate)
    (match_prog cfg)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals

namespace VSF

private abbrev proof_F := CompCert4Lean.Cfrontend.SimplLocals.VSet.MFProvider

theorem add_iff_proof : add_iff := by
  intro s x y
  constructor
  · intro h
    by_cases heq : proof_F.E.eq x y
    · exact Or.inl heq
    · exact Or.inr (proof_F.M.add_3 s x y heq h)
  · intro h
    cases h with
    | inl heq => exact proof_F.M.add_1 s x y heq
    | inr hin => exact proof_F.M.add_2 s x y hin

theorem empty_iff_proof : empty_iff := by
  intro x
  constructor
  · intro h
    exact (proof_F.M.empty_1 x) h
  · intro h
    exact False.elim h

theorem mem_iff_proof : mem_iff := by
  intro s x
  constructor
  · intro h
    exact proof_F.M.mem_1 s x h
  · intro h
    exact proof_F.M.mem_2 s x h

end VSF

private theorem compat_union_left (a b : VSet.t) (cenv : compilenv) :
    compat_cenv (VSet.union a b) cenv → compat_cenv a cenv := by
  intro h id ha hc
  exact h id (VSet.MFProvider.M.union_2 a b id ha) hc

private theorem compat_union_right (a b : VSet.t) (cenv : compilenv) :
    compat_cenv (VSet.union a b) cenv → compat_cenv b cenv := by
  intro h id hb hc
  exact h id (VSet.MFProvider.M.union_3 a b id hb) hc

private theorem compat_seq_of_labeled_statement (ls : labeled_statements) (cenv : compilenv) :
    compat_cenv (addr_taken_lblstmt ls) cenv →
      compat_cenv (addr_taken_stmt (seq_of_labeled_statement ls)) cenv := by
  let P : statement → Prop := fun _ => True
  let P0 : labeled_statements → Prop := fun ls =>
    compat_cenv (addr_taken_lblstmt ls) cenv →
      compat_cenv (addr_taken_stmt (seq_of_labeled_statement ls)) cenv
  have H : ∀ ls, P0 ls := by
    apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec (motive_1 := P) (motive_2 := P0)
    all_goals try simp [P]
    case LSnil =>
      intro _ id h
      exact False.elim ((VSet.MFProvider.M.empty_1 id) h)
    case LScons =>
      intro case stmt rest ih h id hu hc
      rcases VSet.MFProvider.M.union_1 _ _ id hu with hs | hr
      · exact h id (VSet.MFProvider.M.union_2 _ _ id hs) hc
      · exact (ih (compat_union_right _ _ _ h)) id hr hc
  exact H ls

private theorem simpl_seq_of_labeled_statement (cfg : CompilerConfig) (cenv : compilenv)
    (ls tls : labeled_statements) :
    simpl_lblstmt cfg cenv ls = .OK tls →
      simpl_stmt cfg cenv (seq_of_labeled_statement ls) =
        .OK (seq_of_labeled_statement tls) := by
  let P : statement → Prop := fun _ => True
  let P0 : labeled_statements → Prop := fun ls =>
    ∀ tls, simpl_lblstmt cfg cenv ls = .OK tls →
      simpl_stmt cfg cenv (seq_of_labeled_statement ls) =
        .OK (seq_of_labeled_statement tls)
  have H : ∀ ls, P0 ls := by
    apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec (motive_1 := P) (motive_2 := P0)
    all_goals try simp [P]
    case LSnil => simp [P0, simpl_lblstmt, simpl_stmt, seq_of_labeled_statement]
    case LScons =>
      intro case stmt rest ih tls h
      simp only [simpl_lblstmt, simpl_stmt, seq_of_labeled_statement] at h ⊢
      split at h <;> try contradiction
      rename_i hstmt
      split at h <;> try contradiction
      rename_i hrest
      cases h
      rw [ih _ hrest]
      rfl
  exact H ls tls

private theorem find_label_Sset_debug_none (cfg : CompilerConfig) (lbl id : ident)
    (ty : type) (a : expr) (k : cont) :
    find_label lbl (Sset_debug cfg id ty a) k = none := by
  unfold Sset_debug
  split <;> rfl

theorem simpl_find_label_ls : simpl_find_label_lsStatement := by
  intro cfg prog f cenv m bound tbound lbl ls
  let P : statement → Prop := fun s =>
    ∀ k ts tk, simpl_stmt cfg cenv s = .OK ts →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (addr_taken_stmt s) cenv →
      match find_label lbl s k with
      | none => find_label lbl ts tk = none
      | some (s', k') => ∃ ts' tk', find_label lbl ts tk = some (ts', tk') ∧
          compat_cenv (addr_taken_stmt s') cenv ∧ simpl_stmt cfg cenv s' = .OK ts' ∧
          match_cont cfg prog f cenv k' tk' m bound tbound
  let P0 : labeled_statements → Prop := fun ls =>
    ∀ k tls tk, simpl_lblstmt cfg cenv ls = .OK tls →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (addr_taken_lblstmt ls) cenv →
      match find_label_ls lbl ls k with
      | none => find_label_ls lbl tls tk = none
      | some (s', k') => ∃ ts' tk', find_label_ls lbl tls tk = some (ts', tk') ∧
          compat_cenv (addr_taken_stmt s') cenv ∧ simpl_stmt cfg cenv s' = .OK ts' ∧
          match_cont cfg prog f cenv k' tk' m bound tbound
  have H : ∀ ls, P0 ls := by
    apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec (motive_1 := P) (motive_2 := P0)
    case Sskip =>
      intro k ts tk h _ _
      cases h
      rfl
    case Sassign =>
      intro lhs rhs k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h
      · cases h
        exact find_label_Sset_debug_none cfg lbl _ _ _ tk
      · cases h
        rfl
    case Sset =>
      intro id rhs k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      cases h
      rfl
    case Scall =>
      intro result fn args k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      cases h
      rfl
    case Sbuiltin =>
      intro result ef argTypes args k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      cases h
      rfl
    case Ssequence =>
      intro s1 s2 ih1 ih2 k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i h1
      split at h <;> try contradiction
      rename_i h2
      cases h
      have compat1 : compat_cenv (addr_taken_stmt s1) cenv :=
        compat_union_left _ _ _ compat
      have compat2 : compat_cenv (addr_taken_stmt s2) cenv :=
        compat_union_right _ _ _ compat
      have mc1 := match_Kseq cenv s2 k _ tk m bound tbound h2 mc compat2
      have h1' := ih1 (.Kseq s2 k) _ (.Kseq _ tk) h1 mc1 compat1
      cases e : find_label lbl s1 (.Kseq s2 k) with
      | none =>
          simp [e] at h1'
          simpa [find_label, e, h1'] using ih2 k _ tk h2 mc compat2
      | some found =>
          rcases (by simpa [e] using h1') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
    case Sloop =>
      intro body iter ihbody ihiter k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i hbody
      split at h <;> try contradiction
      rename_i hiter
      cases h
      have compatbody : compat_cenv (addr_taken_stmt body) cenv :=
        compat_union_left _ _ _ compat
      have compatiter : compat_cenv (addr_taken_stmt iter) cenv :=
        compat_union_right _ _ _ compat
      have mcbody := match_Kloop1 cenv body iter k _ _ tk m bound tbound
        hbody hiter mc compat
      have hbody' := ihbody (.Kloop1 body iter k) _ (.Kloop1 _ _ tk)
        hbody mcbody compatbody
      cases e : find_label lbl body (.Kloop1 body iter k) with
      | none =>
          simp [e] at hbody'
          have mciter := match_Kloop2 cenv body iter k _ _ tk m bound tbound
            hbody hiter mc compat
          simpa [find_label, e, hbody'] using
            ihiter (.Kloop2 body iter k) _ (.Kloop2 _ _ tk) hiter mciter compatiter
      | some found =>
          rcases (by simpa [e] using hbody') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
    case Sswitch =>
      intro selector cases ihcases k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i hcases
      cases h
      have compatcases : compat_cenv (addr_taken_lblstmt cases) cenv :=
        compat_union_right _ _ _ compat
      have mc' := match_Kswitch cenv k tk m bound tbound mc
      simpa [find_label] using ihcases (.Kswitch k) _ (.Kswitch tk) hcases mc' compatcases
    case Slabel =>
      intro l body ihbody k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i hbody
      cases h
      have compatbody : compat_cenv (addr_taken_stmt body) cenv := by
        simpa [addr_taken_stmt] using compat
      cases e : CompCert4Lean.Common.AST.ident_eq lbl l with
      | left heq =>
          simp only [find_label, e]
          exact ⟨_, tk, rfl, compatbody, hbody, mc⟩
      | right hne =>
          simpa [find_label, e] using ihbody k _ tk hbody mc compatbody
    case Sifthenelse =>
      intro cond s1 s2 ih1 ih2 k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i h1
      split at h <;> try contradiction
      rename_i h2
      cases h
      have compat12 : compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv :=
        compat_union_right _ _ _ compat
      have compat1 : compat_cenv (addr_taken_stmt s1) cenv :=
        compat_union_left _ _ _ compat12
      have compat2 : compat_cenv (addr_taken_stmt s2) cenv :=
        compat_union_right _ _ _ compat12
      have h1' := ih1 k _ tk h1 mc compat1
      cases e : find_label lbl s1 k with
      | none =>
          simp [e] at h1'
          simpa [find_label, e, h1'] using ih2 k _ tk h2 mc compat2
      | some found =>
          rcases (by simpa [e] using h1') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
    case Sbreak =>
      intro k ts tk h _ _
      cases h
      rfl
    case Scontinue =>
      intro k ts tk h _ _
      cases h
      rfl
    case Sreturn =>
      intro result k ts tk h _ _
      cases h
      rfl
    case Sgoto =>
      intro l k ts tk h _ _
      cases h
      rfl
    case LSnil =>
      intro k tls tk h _ _
      cases h
      rfl
    case LScons =>
      intro case stmt rest ihstmt ihrest k tls tk h mc compat
      simp only [simpl_lblstmt] at h
      split at h <;> try contradiction
      rename_i hstmt
      split at h <;> try contradiction
      rename_i hrest
      cases h
      have compatstmt : compat_cenv (addr_taken_stmt stmt) cenv :=
        compat_union_left _ _ _ compat
      have compatrest : compat_cenv (addr_taken_lblstmt rest) cenv :=
        compat_union_right _ _ _ compat
      have hseq := simpl_seq_of_labeled_statement cfg cenv rest _ hrest
      have compatseq := compat_seq_of_labeled_statement rest cenv compatrest
      have mcstmt := match_Kseq cenv (seq_of_labeled_statement rest) k
        (seq_of_labeled_statement _) tk m bound tbound hseq mc compatseq
      have hstmt' := ihstmt (.Kseq (seq_of_labeled_statement rest) k) _
        (.Kseq (seq_of_labeled_statement _) tk) hstmt mcstmt compatstmt
      cases e : find_label lbl stmt (.Kseq (seq_of_labeled_statement rest) k) with
      | none =>
          simp [e] at hstmt'
          simpa [find_label_ls, e, hstmt'] using ihrest k _ tk hrest mc compatrest
      | some found =>
          rcases (by simpa [e] using hstmt') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label_ls, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
  exact H ls

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib

private theorem simplLocals_transf_globdefs_match
    (cfg : CompilerConfig) (p : Clight.program) :
    ∀ (l : List (ident × CompCert4Lean.Common.AST.globdef Clight.fundef Ctypes.type))
      (defs : List (ident × CompCert4Lean.Common.AST.globdef Clight.fundef Ctypes.type)),
      transf_globdefs (fun _ f => transf_fundef cfg f) (fun _ v => .OK v) l = .OK defs →
      list_forall2
        (match_ident_globdef
          (fun _ f tf => transf_fundef cfg f = .OK tf) Eq
          (Ctypes.program_of_program p)) l defs := by
  intro l
  induction l with
  | nil =>
      intro defs hdefs
      simp [transf_globdefs] at hdefs
      subst defs
      exact list_forall2.nil _
  | cons hd tl ih =>
      intro defs hdefs
      cases hd with
      | mk id gd =>
          cases gd with
          | Gfun f =>
              cases htf : transf_fundef cfg f with
              | Error msg => simp [transf_globdefs, htf] at hdefs
              | OK tf =>
                  cases htail : transf_globdefs
                      (fun _ f => transf_fundef cfg f) (fun _ v => .OK v) tl with
                  | Error msg => simp [transf_globdefs, htf, htail] at hdefs
                  | OK defsTail =>
                      simp [transf_globdefs, htf, htail] at hdefs
                      subst defs
                      apply list_forall2.cons
                      · constructor
                        · rfl
                        · apply match_globdef_fun (ctx' := Ctypes.program_of_program p)
                          · exact linkorder_refl _
                          · exact htf
                      · exact ih defsTail htail
          | Gvar v =>
              cases v with
              | mk info init readonly volatile =>
                  cases htail : transf_globdefs
                      (fun _ f => transf_fundef cfg f) (fun _ v => .OK v) tl with
                  | Error msg => simp [transf_globdefs, transf_globvar, htail] at hdefs
                  | OK defsTail =>
                      simp [transf_globdefs, transf_globvar, htail] at hdefs
                      subst defs
                      apply list_forall2.cons
                      · constructor
                        · rfl
                        · apply match_globdef_var
                          exact match_globvar_intro _ _ _ _ _ _ rfl
                      · exact ih defsTail htail

theorem match_transf_program : match_transf_programStatement := by
  intro cfg p tp h
  unfold transf_program at h
  unfold match_prog
  unfold transform_partial_program transform_partial_program2 at h
  cases hdefs : transf_globdefs
      (fun _ f => transf_fundef cfg f) (fun _ v => .OK v)
      (Ctypes.program_of_program p).prog_defs with
  | Error msg => simp [hdefs] at h
  | OK defs =>
      simp [hdefs] at h
      injection h with hEq
      unfold match_program match_program_gen
      have hdefsEq : (Ctypes.program_of_program tp).prog_defs = defs := by
        exact (congrArg (fun q : Clight.program => q.prog_defs) hEq).symm
      have hmainEq : (Ctypes.program_of_program tp).prog_main =
          (Ctypes.program_of_program p).prog_main := by
        exact (congrArg (fun q : Clight.program => q.prog_main) hEq).symm
      have hpublicEq : (Ctypes.program_of_program tp).prog_public =
          (Ctypes.program_of_program p).prog_public := by
        exact (congrArg (fun q : Clight.program => q.prog_public) hEq).symm
      apply And.intro
      · apply And.intro
        · rw [hdefsEq]
          exact simplLocals_transf_globdefs_match cfg p _ _ hdefs
        · exact ⟨hmainEq, hpublicEq⟩
      · exact (congrArg (fun q : Clight.program => q.prog_types) hEq).symm

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem comp_env_preserved : comp_env_preservedStatement := by
  intro cfg p tp hmatch
  have htypes : tp.prog_types = p.prog_types := hmatch.2
  change tp.prog_comp_env = p.prog_comp_env
  have hp : Ctypes.build_composite_env p.prog_types = .OK p.prog_comp_env :=
    p.prog_comp_env_eq
  have htp : Ctypes.build_composite_env tp.prog_types = .OK tp.prog_comp_env :=
    tp.prog_comp_env_eq
  rw [htypes] at htp
  apply CompCert4Lean.Common.Errors.res.OK.inj
  exact htp.symm.trans hp

end CompCert4Lean.Cfrontend.SimplLocalsproof
