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

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem simpllocalsproof_add_global_match
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

private theorem simpllocalsproof_add_globals_match
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
                (simpllocalsproof_add_global_match R ge1 ge2 hge id1 gd1 gd2 hrel)

private theorem simpllocalsproof_globalenvs_match
    {A B V : Type} [Linker A] [Linker V]
    (transf : A → CompCert4Lean.Common.Errors.res B)
    (p : CompCert4Lean.Common.AST.program A V)
    (tp : CompCert4Lean.Common.AST.program B V)
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
  exact simpllocalsproof_add_globals_match
    (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
    p.prog_defs tp.prog_defs
    (Genv.empty_genv A V p.prog_public) (Genv.empty_genv B V tp.prog_public)
    hmatch.1 hempty

theorem symbols_preserved : symbols_preservedStatement := by
  intro cfg p tp hmatch id
  have hgenv := simpllocalsproof_globalenvs_match
    (A := CompCert4Lean.Cfrontend.Ctypes.fundef CompCert4Lean.Cfrontend.Clight.function)
    (B := CompCert4Lean.Cfrontend.Ctypes.fundef CompCert4Lean.Cfrontend.Clight.function)
    (V := type)
    (transf := fun f => CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f)
    (p := Ctypes.program_of_program p) (tp := Ctypes.program_of_program tp) hmatch.1
  exact hgenv.mge_symb id

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem simpllocalsproof_add_globals_public_suffix
    {A V : Type} (ge : Genv.t A V) (gl : List (ident × globdef A V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x xs ih =>
      simp only [Genv.add_globals, List.foldl]
      exact ih (Genv.add_global ge x)

private theorem simpllocalsproof_add_global_match_suffix
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W)
    (h : Genv.match_genvs R ge1 ge2)
    (id : ident) (g1 : globdef A V) (g2 : globdef B W) (hr : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
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
            some ge2.genv_next := by simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            some ge1.genv_next := by simpa [heq] using hx1
        rw [hx2', hx1', h.mge_next]
    | right hne =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            PTree.get id' ge2.genv_symb := by simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            PTree.get id' ge1.genv_symb := by simpa [heq] using hx1
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
                some g1 := by simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                some g2 := by simpa [hpeq2] using hx2
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
                PTree.get b ge1.genv_defs := by simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                PTree.get b ge2.genv_defs := by simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact h.mge_defs b

private theorem simpllocalsproof_add_globals_match_suffix
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
                (simpllocalsproof_add_global_match_suffix R ge1 ge2 hge id1 gd1 gd2 hrel)

private theorem simpllocalsproof_globalenvs_match_suffix
    {A B V : Type} [Linker A] [Linker V]
    (transf : A → CompCert4Lean.Common.Errors.res B)
    (p : CompCert4Lean.Common.AST.program A V)
    (tp : CompCert4Lean.Common.AST.program B V)
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
  exact simpllocalsproof_add_globals_match_suffix
    (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
    p.prog_defs tp.prog_defs
    (Genv.empty_genv A V p.prog_public) (Genv.empty_genv B V tp.prog_public)
    hmatch.1 hempty

theorem senv_preserved : senv_preservedStatement := by
  intro cfg p tp hmatch
  have hgenv := simpllocalsproof_globalenvs_match_suffix
    (A := CompCert4Lean.Cfrontend.Ctypes.fundef CompCert4Lean.Cfrontend.Clight.function)
    (B := CompCert4Lean.Cfrontend.Ctypes.fundef CompCert4Lean.Cfrontend.Clight.function)
    (V := type)
    (transf := fun f => CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f)
    (p := Ctypes.program_of_program p) (tp := Ctypes.program_of_program tp) hmatch.1
  unfold Senv.equiv
  constructor
  · intro id
    exact hgenv.mge_symb id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv (Ctypes.program_of_program tp)) id =
      Genv.public_symbol (Genv.globalenv (Ctypes.program_of_program p)) id
    have ht : (Genv.globalenv (Ctypes.program_of_program tp)).genv_public = tp.prog_public := by
      unfold Genv.globalenv
      exact simpllocalsproof_add_globals_public_suffix _ _
    have hp : (Genv.globalenv (Ctypes.program_of_program p)).genv_public = p.prog_public := by
      unfold Genv.globalenv
      exact simpllocalsproof_add_globals_public_suffix _ _
    unfold Genv.public_symbol Genv.find_symbol
    rw [hgenv.mge_symb id, ht, hp]
    have hpub : tp.prog_public = p.prog_public := hmatch.1.2.2
    rw [hpub]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv (Ctypes.program_of_program tp)) b =
      Genv.block_is_volatile (Genv.globalenv (Ctypes.program_of_program p)) b
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    cases h1 : PTree.get b (Genv.globalenv (Ctypes.program_of_program p)).genv_defs with
    | none =>
        cases h2 : PTree.get b (Genv.globalenv (Ctypes.program_of_program tp)).genv_defs with
        | none => rfl
        | some gd2 =>
            have hd := hgenv.mge_defs b
            simp [h1, h2] at hd
            cases hd
    | some gd1 =>
        cases h2 : PTree.get b (Genv.globalenv (Ctypes.program_of_program tp)).genv_defs with
        | none =>
            have hd := hgenv.mge_defs b
            simp [h1, h2] at hd
            cases hd
        | some gd2 =>
            have hd := hgenv.mge_defs b
            simp [h1, h2] at hd
            cases hd with
            | some x y hrel =>
                cases hrel with
                | match_globdef_fun ctx' f1 f2 horder htrans => rfl
                | match_globdef_var v1 v2 hvar =>
                    cases hvar
                    rfl

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem type_of_fundef_preserved : type_of_fundef_preservedStatement := by
  intro cfg fd tfd h
  cases fd with
  | External ef args result cc =>
      simp [CompCert4Lean.Cfrontend.SimplLocals.transf_fundef] at h
      cases h
      rfl
  | Internal f =>
      unfold CompCert4Lean.Cfrontend.SimplLocals.transf_fundef at h
      cases htrans : CompCert4Lean.Cfrontend.SimplLocals.transf_function cfg f with
      | Error msg =>
          simp [htrans] at h
      | OK transformed =>
          simp [htrans] at h
          cases h
          simp [CompCert4Lean.Cfrontend.Clight.type_of_fundef,
            CompCert4Lean.Cfrontend.Clight.type_of_function] at ⊢
          unfold CompCert4Lean.Cfrontend.SimplLocals.transf_function at htrans
          split at htrans
          · cases hbody : CompCert4Lean.Cfrontend.SimplLocals.simpl_stmt cfg
                (CompCert4Lean.Cfrontend.SimplLocals.cenv_for f) f.fn_body with
            | Error message =>
                simp [hbody] at htrans
            | OK body' =>
                simp [hbody] at htrans
                cases htrans
                simp
          · cases htrans

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib

private theorem simpllocalsproof_val_inject_incr
    {f f' : meminj} {v v' : val}
    (hinc : inject_incr f f') (hval : Val.inject f v v') :
    Val.inject f' v v' := by
  cases hval with
  | inject_int n => exact Val.inject.inject_int n
  | inject_long n => exact Val.inject.inject_long n
  | inject_float x => exact Val.inject.inject_float x
  | inject_single x => exact Val.inject.inject_single x
  | inject_ptr b ofs b' ofs' delta hmap hofs =>
      exact Val.inject.inject_ptr b ofs b' ofs' delta (hinc b b' delta hmap) hofs
  | val_inject_undef => exact Val.inject.val_inject_undef _

theorem match_envs_invariant : match_envs_invariantStatement := by
  intro f cenv e le m lo hi te tle tlo thi f' m' hme hload hincr hinv1 hinv2
  rcases hme with ⟨hvars, htemps, hinj, hrange, htrange, hmapped, hflat, hlo, htlo⟩
  refine ⟨?_, ?_, hinj, hrange, htrange, ?_, ?_, hlo, htlo⟩
  · intro id
    cases hvars id with
    | match_var_lifted b ty chunk v tv henv htenv hlift hmap hmode hload0 htlenv hv =>
        have hbounds : Ple lo b ∧ Plt b hi := hrange id b ty henv
        have hmap' : f' b = none := by
          rw [hinv1 b hbounds, hmap]
        have hload' : Mem.load chunk m' b (.Z0 : Z) = some v :=
          hload b chunk v hmap hbounds hload0
        exact match_var_lifted b ty chunk v tv henv htenv hlift hmap' hmode hload'
          htlenv (simpllocalsproof_val_inject_incr hincr hv)
    | match_var_not_lifted b ty b' henv htenv hnlocal hmap =>
        exact match_var_not_lifted b ty b' henv htenv hnlocal
          (hincr b b' (.Z0 : Z) hmap)
    | match_var_not_local henv htenv hnlocal =>
        exact match_var_not_local henv htenv hnlocal
  · intro id v hle
    rcases htemps id v hle with ⟨⟨tv, htle, hv⟩, hcenv⟩
    exact ⟨⟨tv, htle, simpllocalsproof_val_inject_incr hincr hv⟩, hcenv⟩
  · intro id b' ty hte
    rcases hmapped id b' ty hte with ⟨b, hmap, henv⟩
    exact ⟨b, hincr b b' (.Z0 : Z) hmap, henv⟩
  · intro id b' ty b delta hte hmap'
    have hmap : f b = some (b', delta) :=
      (hinv2 b b' delta hmap' (htrange id b' ty hte)).symm.trans hmap'
    exact hflat id b' ty b delta hte hmap

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem val_casted_load_result : val_casted_load_resultStatement := by
  intro v ty chunk hcast hmode
  cases hcast with
  | val_casted_int sz si attr n hcast =>
      cases sz <;> cases si <;> simp [CompCert4Lean.Cfrontend.Ctypes.access_mode] at hmode
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        by_cases hn : CompCert4Lean.Lib.Integers.Int.eq n
            CompCert4Lean.Lib.Integers.Int.zero
        · simp [CompCert4Lean.Common.Values.Val.load_result,
            CompCert4Lean.Cfrontend.Cop.cast_int_int, hn] at hcast ⊢
          cases hcast
          rfl
        · simp [CompCert4Lean.Common.Values.Val.load_result,
            CompCert4Lean.Cfrontend.Cop.cast_int_int, hn] at hcast ⊢
          cases hcast
          rfl
      · cases hmode
        by_cases hn : CompCert4Lean.Lib.Integers.Int.eq n
            CompCert4Lean.Lib.Integers.Int.zero
        · simp [CompCert4Lean.Common.Values.Val.load_result,
            CompCert4Lean.Cfrontend.Cop.cast_int_int, hn] at hcast ⊢
          cases hcast
          rfl
        · simp [CompCert4Lean.Common.Values.Val.load_result,
            CompCert4Lean.Cfrontend.Cop.cast_int_int, hn] at hcast ⊢
          cases hcast
          rfl
  | val_casted_float attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode] at hmode
      cases hmode
      rfl
  | val_casted_single attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode] at hmode
      cases hmode
      rfl
  | val_casted_long si attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode] at hmode
      cases hmode
      rfl
  | val_casted_ptr_ptr b ofs ty attr =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode,
        CompCert4Lean.Common.AST.Mptr,
        CompCert4Lean.X86_64.Archi.ptr64] at hmode
      cases hmode
      simp [CompCert4Lean.Common.Values.Val.load_result,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_int_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode,
        CompCert4Lean.Common.AST.Mptr, hptr64] at hmode
      cases hmode
      rfl
  | val_casted_ptr_int b ofs si attr hptr64 =>
      simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64
  | val_casted_long_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode,
        CompCert4Lean.Common.AST.Mptr, hptr64] at hmode
      cases hmode
      rfl
  | val_casted_ptr_long b ofs si attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode, hptr64] at hmode
      cases hmode
      rfl
  | val_casted_struct id attr b ofs =>
      cases hmode
  | val_casted_union id attr b ofs =>
      cases hmode
  | val_casted_void v =>
      cases hmode

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem val_casted_inject : val_casted_injectStatement := by
  intro f v v' ty hinj hcast
  cases hinj <;> cases hcast <;> constructor <;> assumption

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem forall2_val_casted_inject : forall2_val_casted_injectStatement := by
  intro f vl vl' hinj
  induction hinj with
  | inject_list_nil =>
      intro tyl hcast
      cases hcast
      exact .nil _
  | inject_list_cons v1 v2 vl1 vl2 hhead htail ih =>
      intro tyl hcast
      cases hcast with
      | cons _ _ hty htys =>
          exact .cons _ _ (val_casted_inject f v1 v2 _ hhead hty) (ih _ htys)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem val_casted_list_params : val_casted_list_paramsStatement := by
  intro params vl hcast
  induction params generalizing vl with
  | nil =>
      cases hcast
      exact .nil _
  | cons p ps ih =>
      cases p with
      | mk id ty =>
          cases hcast with
          | cons _ _ _ _ hhead htail =>
              exact .cons _ _ hhead (ih _ htail)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem step_Sdebug_var
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_Sdebug_varStatement := by
  intro xi tprog f id ty k e le m b henv
  unfold CompCert4Lean.Cfrontend.SimplLocals.Sdebug_var
  change CompCert4Lean.Cfrontend.Clight.step
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi
    (CompCert4Lean.Cfrontend.Clight.globalenv tprog)
      (CompCert4Lean.Cfrontend.Clight.function_entry2
      (CompCert4Lean.Cfrontend.Clight.globalenv tprog)) _ _ _
  refine CompCert4Lean.Cfrontend.Clight.step.step_builtin
    (xi := xi)
    (ge := CompCert4Lean.Cfrontend.Clight.globalenv tprog)
    (function_entry := CompCert4Lean.Cfrontend.Clight.function_entry2
      (CompCert4Lean.Cfrontend.Clight.globalenv tprog))
    (f := f) (result := none)
    (ef := .EF_debug (.xI (.xO .xH)) id [CompCert4Lean.Common.AST.Tptr])
    (argTypes := [.Tpointer ty CompCert4Lean.Cfrontend.Ctypes.noattr])
    (args := [.Eaddrof (.Evar id ty) (.Tpointer ty CompCert4Lean.Cfrontend.Ctypes.noattr)])
    (k := k) (e := e) (le := le) (m := m)
    (vargs := [.Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero])
    (t := CompCert4Lean.Common.Events.E0) (vres := .Vundef) (m' := m) ?_ ?_
  · refine CompCert4Lean.Cfrontend.Clight.eval_exprlist.cons
      (a := .Eaddrof (.Evar id ty) (.Tpointer ty CompCert4Lean.Cfrontend.Ctypes.noattr))
      (rest := []) (ty := .Tpointer ty CompCert4Lean.Cfrontend.Ctypes.noattr)
      (types := []) (v1 := .Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero)
      (v2 := .Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero) (values := []) ?_ ?_
      CompCert4Lean.Cfrontend.Clight.eval_exprlist.nil
    · exact CompCert4Lean.Cfrontend.Clight.eval_expr.eval_Eaddrof _ _ _ _
        (CompCert4Lean.Cfrontend.Clight.eval_lvalue.eval_Evar_local _ _ _ henv)
    · simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Clight.typeof,
        CompCert4Lean.X86_64.Archi.ptr64]
  · exact CompCert4Lean.Common.Events.extcall_debug_sem.extcall_debug_sem_intro _ _

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem cast_typeconv
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    cast_typeconvStatement := by
  intro v ty m h
  cases h with
  | val_casted_int sz si attr n hcast =>
      cases sz <;> cases si <;>
        simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
          CompCert4Lean.Cfrontend.Cop.classify_cast,
          CompCert4Lean.Cfrontend.Ctypes.typeconv,
          CompCert4Lean.Cfrontend.Ctypes.type_int32s,
          CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
          CompCert4Lean.Cfrontend.Ctypes.change_attributes,
          CompCert4Lean.Cfrontend.Cop.cast_int_int,
          CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_float attr n =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_single attr n =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_long si attr n =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_ptr_ptr b ofs ty attr =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_int_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64
  | val_casted_ptr_int b ofs si attr hptr64 =>
      simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64
  | val_casted_long_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64, hptr64]
  | val_casted_ptr_long b ofs si attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64, hptr64]
  | val_casted_struct id attr b ofs =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_union id attr b ofs =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_void v =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem step_Sdebug_temp
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_Sdebug_tempStatement := by
  intro xi tprog f id ty k e le m v hfind hcasted
  unfold CompCert4Lean.Cfrontend.SimplLocals.Sdebug_temp
  change CompCert4Lean.Cfrontend.Clight.step
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi
    (CompCert4Lean.Cfrontend.Clight.globalenv tprog)
    (CompCert4Lean.Cfrontend.Clight.function_entry2
      (CompCert4Lean.Cfrontend.Clight.globalenv tprog)) _ _ _
  refine CompCert4Lean.Cfrontend.Clight.step.step_builtin
    (xi := xi)
    (ge := CompCert4Lean.Cfrontend.Clight.globalenv tprog)
    (function_entry := CompCert4Lean.Cfrontend.Clight.function_entry2
      (CompCert4Lean.Cfrontend.Clight.globalenv tprog))
    (f := f) (result := none)
    (ef := .EF_debug (.xO .xH) id
      [CompCert4Lean.Cfrontend.Ctypes.typ_of_type ty])
    (argTypes := [CompCert4Lean.Cfrontend.Ctypes.typeconv ty])
    (args := [.Etempvar id ty]) (k := k) (e := e) (le := le) (m := m)
    (vargs := [v]) (t := CompCert4Lean.Common.Events.E0) (vres := .Vundef) (m' := m) ?_ ?_
  · refine CompCert4Lean.Cfrontend.Clight.eval_exprlist.cons
      (a := .Etempvar id ty) (rest := [])
      (ty := CompCert4Lean.Cfrontend.Ctypes.typeconv ty) (types := [])
      (v1 := v) (v2 := v) (values := []) ?_ ?_
      CompCert4Lean.Cfrontend.Clight.eval_exprlist.nil
    · exact CompCert4Lean.Cfrontend.Clight.eval_expr.eval_Etempvar _ _ _ hfind
    · exact cast_typeconv v ty m hcasted
  · exact CompCert4Lean.Common.Events.extcall_debug_sem.extcall_debug_sem_intro _ _

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem make_cast_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_cast_correctStatement := by
  intro tprog e le m a v1 tto v2 ha hsem
  have hcast : CompCert4Lean.Cfrontend.Clight.eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (CompCert4Lean.Cfrontend.Clight.globalenv tprog) e le m
      (.Ecast a tto) v2 :=
    CompCert4Lean.Cfrontend.Clight.eval_expr.cast a tto v1 v2 ha hsem
  unfold CompCert4Lean.Cfrontend.SimplLocals.make_cast
  cases hclass : CompCert4Lean.Cfrontend.Cop.classify_cast
      (CompCert4Lean.Cfrontend.Clight.typeof a) tto with
  | cast_case_pointer =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass,
        CompCert4Lean.X86_64.Archi.ptr64] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_i2i sz2 si2 =>
      cases sz2 with
      | I32 =>
          simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass,
            CompCert4Lean.Cfrontend.Cop.cast_int_int,
            CompCert4Lean.X86_64.Archi.ptr64] at hsem
          cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast,
            CompCert4Lean.Cfrontend.Cop.cast_int_int]
      | I8 =>
          simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
      | I16 =>
          simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
      | IBool =>
          simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_f2f =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_s2s =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_l2l =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass,
        CompCert4Lean.X86_64.Archi.ptr64] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_struct id1 id2 =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_union id1 id2 =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_void =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_f2s =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_s2f =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_i2f si1 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_i2s si1 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_f2i sz2 si2 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_s2i sz2 si2 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_l2bool =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_i2bool =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_f2bool =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_s2bool =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_i2l si1 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_l2i sz2 si2 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_l2f si1 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_l2s si1 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_f2l si2 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_s2l si2 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_default =>
      exact hcast

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem bind_parameter_temps_inv : bind_parameter_temps_invStatement := by
  intro id params args le le' hbind hnot
  induction params generalizing args le le' with
  | nil =>
      cases args <;> simp [bind_parameter_temps] at hbind
      cases hbind
      rfl
  | cons p params ih =>
      cases p with
      | mk id1 ty1 =>
          cases args with
          | nil => simp [bind_parameter_temps] at hbind
          | cons v args =>
              simp only [bind_parameter_temps] at hbind
              have hnot' : id ∉ var_names params := by
                intro hin
                apply hnot
                simp only [var_names, List.map_cons, List.mem_cons]
                have hin' : id ∈ List.map Prod.fst params := by simpa [var_names] using hin
                exact Or.inr hin'
              have hi := ih (args := args) (le := PTree.set id1 v le) (le' := le') hbind hnot'
              have hget : PTree.get id (PTree.set id1 v le) = PTree.get id le := by
                apply PTree.gso
                intro heq
                apply hnot
                simp [var_names, heq]
              exact hi.trans hget
end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Driver.Compopts
open CompCert4Lean.Lib.Maps

theorem step_add_debug_vars
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_add_debug_varsStatement := by
  intro cfg xi tprog f s e le m vars k h
  unfold add_debug_vars
  by_cases hd : CompCert4Lean.Driver.Compopts.debug cfg = true
  · rw [hd]
    induction vars with
    | nil =>
        exact star_refl _ _ _
    | cons p vars ih =>
        cases p with
        | mk id ty =>
            have hb : ∃ b, PTree.get id e = some (b, ty) := h id ty (List.mem_cons_self)
            rcases hb with ⟨b, hbe⟩
            have hrest := fun id' ty' (hm : (id', ty') ∈ vars) =>
              h id' ty' (List.mem_cons_of_mem _ hm)
            apply star_left
            · exact CompCert4Lean.Cfrontend.Clight.step.step_seq f
                (Sdebug_var id ty) (List.foldr add_debug_var s vars) k e le m
            · apply star_left
              · exact step_Sdebug_var xi tprog f id ty
                  (.Kseq (List.foldr add_debug_var s vars) k) e le m b hbe
              · apply star_left
                · exact CompCert4Lean.Cfrontend.Clight.step.step_skip_seq f
                    (List.foldr add_debug_var s vars) k e le m
                · exact ih hrest
                · rfl
              · rfl
            · rfl
  · simp [hd]
    exact star_refl _ _ _
end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Driver.Compopts

theorem step_add_debug_params
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_add_debug_paramsStatement := by
  intro cfg xi tprog f s k e le m params vl le1 hnr hcast hbind
  unfold add_debug_params
  by_cases hd : CompCert4Lean.Driver.Compopts.debug cfg = true
  · rw [hd]
    induction params generalizing vl le1 le with
    | nil =>
        cases vl with
        | nil =>
            cases hcast
            cases hbind
            exact star_refl _ _ _
        | cons v vl =>
            cases hcast
    | cons p params ih =>
        cases p with
        | mk id ty =>
            cases vl with
            | nil => cases hcast
            | cons v vl =>
                cases hcast with
                | cons _ _ hvc hvcTail =>
                    cases hnr with
                    | cons _ hnotmem hnrTail =>
                        have hidnot : id ∉ var_names params := by
                            intro hm
                            exact hnotmem (by simpa [var_names] using hm)
                        have hle' := bind_parameter_temps_inv id params vl
                            (PTree.set id v le1) le hbind hidnot
                        have hget : PTree.get id le = some v := by
                            exact hle'.trans (PTree.gss id v le1)
                        have hrest := ih (le := le) (vl := vl)
                            (le1 := PTree.set id v le1) hnrTail hvcTail hbind
                        apply star_left
                        · exact CompCert4Lean.Cfrontend.Clight.step.step_seq f
                            (Sdebug_temp id ty) (List.foldr add_debug_param s params) k e le m
                        · apply star_left
                          · exact step_Sdebug_temp xi tprog f id ty
                              (.Kseq (List.foldr add_debug_param s params) k) e le m v hget hvc
                          · apply star_left
                            · exact CompCert4Lean.Cfrontend.Clight.step.step_skip_seq f
                                (List.foldr add_debug_param s params) k e le m
                            · exact hrest
                            · rfl
                          · rfl
                        · rfl
  · simp [hd]
    exact star_refl _ _ _
end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Maps

theorem match_envs_set_opttemp : match_envs_set_opttempStatement := by
  intro f cenv e le m lo hi te tle tlo thi optid v tv x hme hinj hcheck
  cases optid with
  | none =>
      cases hcheck
      simpa [set_opttemp] using hme
  | some id =>
      unfold check_opttemp check_temp at hcheck
      by_cases hmem : VSet.mem id cenv = true
      · simp [hmem] at hcheck
      · simp [hmem] at hcheck
        simp only [set_opttemp]
        rcases hme with ⟨hvars, htemps, hinj_env, hrange, htrange,
          hmapped, hflat, hlo, htlo⟩
        refine ⟨?_, ?_, hinj_env, hrange, htrange, hmapped, hflat, hlo, htlo⟩
        · intro id0
          cases hvars id0 with
          | match_var_lifted b ty chunk v0 tv0 henv htenv hlift hmap hmode hload htlenv hv =>
              have hne : id0 ≠ id := by
                intro heq
                subst id0
                exact hmem hlift
              exact match_var_lifted b ty chunk v0 tv0 henv htenv hlift hmap hmode hload
                (by
                  have hg : PTree.get id0 (PTree.set id tv tle) = PTree.get id0 tle :=
                    PTree.gso (A := val) (i := id0) (j := id) tv tle hne
                  exact hg.trans htlenv)
                hv
          | match_var_not_lifted b ty b' henv htenv hnlocal hmap =>
              exact match_var_not_lifted b ty b' henv htenv hnlocal hmap
          | match_var_not_local henv htenv hnlocal =>
              exact match_var_not_local henv htenv hnlocal
        · intro id0 v0 hget
          change PTree.get id0 (PTree.set id v le) = some v0 at hget
          by_cases heq : id0 = id
          · subst id0
            have hs : PTree.get id (PTree.set id v le) = some v := PTree.gss id v le
            have hv0 : v = v0 := Option.some.inj (hs.symm.trans hget)
            subst v0
            refine ⟨⟨tv, PTree.gss id tv tle, hinj⟩, ?_⟩
            intro hmem'
            exact (hmem hmem').elim
          · have hget' : PTree.get id0 le = some v0 := by
              have hg : PTree.get id0 (PTree.set id v le) = PTree.get id0 le :=
                PTree.gso (A := val) (i := id0) (j := id) v le heq
              exact hg.symm.trans hget
            rcases htemps id0 v0 hget' with ⟨⟨tv0, htle, hv⟩, hcenv⟩
            refine ⟨⟨tv0, ?_, hv⟩, hcenv⟩
            change PTree.get id0 (PTree.set id tv tle) = some tv0
            have hg : PTree.get id0 (PTree.set id tv tle) = PTree.get id0 tle :=
              PTree.gso (A := val) (i := id0) (j := id) tv tle heq
            exact hg.trans htle

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Maps

theorem match_envs_change_temp : match_envs_change_tempStatement := by
  intro f cenv e le m lo hi te tle tlo thi id v hme hle hmem
  rcases hme with ⟨hvars, htemps, hinj_env, hrange, htrange,
    hmapped, hflat, hlo, htlo⟩
  refine ⟨?_, ?_, hinj_env, hrange, htrange, hmapped, hflat, hlo, htlo⟩
  · intro id0
    cases hvars id0 with
    | match_var_lifted b ty chunk v0 tv0 henv htenv hlift hmap hmode hload htlenv hv =>
        have hne : id0 ≠ id := by
          intro heq
          subst id0
          have hbad : (true : Bool) = false := hlift.symm.trans hmem
          cases hbad
        exact match_var_lifted b ty chunk v0 tv0 henv htenv hlift hmap hmode hload
          (by
            have hg : PTree.get id0 (PTree.set id v tle) = PTree.get id0 tle :=
              PTree.gso (A := val) (i := id0) (j := id) v tle hne
            exact hg.trans htlenv)
          hv
    | match_var_not_lifted b ty b' henv htenv hnlocal hmap =>
        exact match_var_not_lifted b ty b' henv htenv hnlocal hmap
    | match_var_not_local henv htenv hnlocal =>
        exact match_var_not_local henv htenv hnlocal
  · intro id0 v0 hget
    have hne : id0 ≠ id := by
      intro heq
      subst id0
      simpa [hle] using hget
    rcases htemps id0 v0 hget with ⟨⟨tv, htle, hv⟩, hcenv⟩
    refine ⟨⟨tv, ?_, hv⟩, hcenv⟩
    have hg : PTree.get id0 (PTree.set id v tle) = PTree.get id0 tle :=
      PTree.gso (A := val) (i := id0) (j := id) v tle hne
    exact hg.trans htle

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals

theorem cenv_for_gen_domain : cenv_for_gen_domainStatement := by
  intro atk id vars
  induction vars with
  | nil =>
      intro h
      exact False.elim (VSet.MFProvider.M.empty_1 id h)
  | cons hd rest ih =>
      rcases hd with ⟨id1, ty1⟩
      intro h
      change VSet.In id (add_local_variable atk (id1, ty1) (cenv_for_gen atk rest)) at h
      unfold add_local_variable at h
      cases hmode : access_mode ty1 with
      | By_value chunk =>
          by_cases hmem : VSet.mem id1 atk = true
          · simp [hmode, hmem] at h
            exact List.mem_cons.mpr (Or.inr (ih h))
          · simp [hmode, hmem] at h
            have hadd := (VSF.add_iff_proof _ id1 id).mp h
            cases hadd with
            | inl heq =>
                have : id1 = id := heq
                subst id
                exact List.mem_cons.mpr (Or.inl rfl)
            | inr hrest =>
                exact List.mem_cons.mpr (Or.inr (ih hrest))
      | By_reference =>
          simp [hmode] at h
          exact List.mem_cons.mpr (Or.inr (ih h))
      | By_copy =>
          simp [hmode] at h
          exact List.mem_cons.mpr (Or.inr (ih h))
      | By_nothing =>
          simp [hmode] at h
          exact List.mem_cons.mpr (Or.inr (ih h))

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals

private theorem add_local_variable_charact_aux :
    ∀ id ty atk cenv id1,
      VSet.In id1 (add_local_variable atk (id, ty) cenv) ↔
        VSet.In id1 cenv ∨
          ∃ chunk, access_mode ty = .By_value chunk ∧ id = id1 ∧
            VSet.mem id atk = false := by
  intro id ty atk cenv id1
  unfold add_local_variable
  cases hmode : access_mode ty with
  | By_value chunk =>
      cases hmem : VSet.mem id atk with
      | false =>
          simp only [hmode, hmem, ↓reduceIte]
          constructor
          · intro h
            rcases (VSF.add_iff_proof _ id id1).mp h with heq | hrest
            · exact Or.inr ⟨chunk, rfl, heq, trivial⟩
            · exact Or.inl hrest
          · intro h
            rcases h with hrest | ⟨chunk', hmode', heq, hmem'⟩
            · exact (VSF.add_iff_proof _ id id1).mpr (Or.inr hrest)
            · exact (VSF.add_iff_proof _ id id1).mpr (Or.inl heq)
      | true =>
          simp [hmode, hmem]
  | By_reference => simp [hmode]
  | By_copy => simp [hmode]
  | By_nothing => simp [hmode]

theorem cenv_for_gen_by_value : cenv_for_gen_by_valueStatement := by
  intro atk id ty vars
  induction vars generalizing id ty with
  | nil =>
      intro hin _ _
      cases hin
  | cons hd rest ih =>
      rcases hd with ⟨id1, ty1⟩
      intro hin hnr hmem
      cases hin with
      | head =>
          cases hnr with
          | cons _ hnot htail =>
              have hchar :=
                (add_local_variable_charact_aux id ty atk
                  (cenv_for_gen atk rest) id).mp hmem
              cases hchar with
              | inl hrest =>
                  have hdom : id ∈ var_names rest :=
                    cenv_for_gen_domain atk id rest hrest
                  exact False.elim (hnot hdom)
              | inr hex =>
                  rcases hex with ⟨chunk, hmode, heq, hfalse⟩
                  exact ⟨chunk, hmode⟩
      | tail _ htail =>
          cases hnr with
          | cons _ hnot hnrTail =>
              have hchar :=
                (add_local_variable_charact_aux id1 ty1 atk
                  (cenv_for_gen atk rest) id).mp hmem
              cases hchar with
              | inl hrest => exact ih id ty htail hnrTail hrest
              | inr hex =>
                  rcases hex with ⟨chunk, hmode, heq, hfalse⟩
                  have hdom : id1 ∈ var_names rest :=
                    by
                      rw [heq]
                      exact List.mem_map.mpr ⟨(id, ty), htail, rfl⟩
                  exact False.elim (hnot hdom)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals

theorem cenv_for_gen_compat : cenv_for_gen_compatStatement := by
  intro atk id vars
  induction vars with
  | nil =>
      intro h
      exact False.elim (VSet.MFProvider.M.empty_1 id h)
  | cons hd rest ih =>
      rcases hd with ⟨id1, ty1⟩
      intro h
      change VSet.In id (add_local_variable atk (id1, ty1) (cenv_for_gen atk rest)) at h
      unfold add_local_variable at h
      cases hmode : access_mode ty1 with
      | By_value chunk =>
          by_cases hmem : VSet.mem id1 atk = true
          · simp [hmode, hmem] at h
            exact ih h
          · simp [hmode, hmem] at h
            have hadd := (VSF.add_iff_proof _ id1 id).mp h
            cases hadd with
            | inl heq =>
                subst id
                simpa using hmem
            | inr hrest => exact ih hrest
      | By_reference =>
          simp [hmode] at h
          exact ih h
      | By_copy =>
          simp [hmode] at h
          exact ih h
      | By_nothing =>
          simp [hmode] at h
          exact ih h

theorem compat_cenv_for : compat_cenv_forStatement := by
  intro f id hatk hcenv
  have hfalse : VSet.mem id (addr_taken_stmt f.fn_body) = false := by
    apply cenv_for_gen_compat (addr_taken_stmt f.fn_body) id (f.fn_params ++ f.fn_vars)
    change VSet.In id (cenv_for_gen (addr_taken_stmt f.fn_body) (f.fn_params ++ f.fn_vars))
    exact hcenv
  have htrue : VSet.mem id (addr_taken_stmt f.fn_body) = true :=
    (VSF.mem_iff_proof _ _).mp hatk
  rw [hfalse] at htrue
  cases htrue

theorem compat_cenv_union_l : compat_cenv_union_lStatement := by
  intro atk1 atk2 cenv h
  exact compat_union_left atk1 atk2 cenv h

theorem compat_cenv_union_r : compat_cenv_union_rStatement := by
  intro atk1 atk2 cenv h
  exact compat_union_right atk1 atk2 cenv h

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals

theorem compat_cenv_empty : compat_cenv_emptyStatement := by
  intro cenv id hid hcid
  exact (VSet.MFProvider.M.empty_1 id) hid

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

private theorem alloc_nextblock_local (m : mem) (lo hi : Z) (m' : mem)
    (b : block) (halloc : Mem.alloc m lo hi = (m', b)) :
    m'.nextblock = PArith.BinPos.Pos.succ m.nextblock := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have hnext := congrArg Mem.nextblock hfirst
  exact hnext.symm

theorem alloc_variables_nextblock : alloc_variables_nextblockStatement := by
  intro ge e m vars e' m' halloc
  induction halloc with
  | nil =>
      exact Ple_refl _
  | cons e m id ty vars m1 b1 m2 e2 halloc hrest ih =>
      apply Ple_trans _ m1.nextblock _
      · rw [alloc_nextblock_local m (.Z0 : Z) (sizeof ge.genv_cenv ty) m1 b1 halloc]
        exact Ple_succ _
      · exact ih

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem alloc_result_range_local (m : mem) (lo hi : Z) (m' : mem)
    (b : block) (halloc : Mem.alloc m lo hi = (m', b)) : b = m.nextblock := by
  unfold Mem.alloc at halloc
  exact (congrArg Prod.snd halloc).symm

theorem alloc_variables_range : alloc_variables_rangeStatement := by
  intro ge id b ty e m vars e' m' halloc
  induction halloc generalizing id b ty with
  | nil =>
      intro hget
      exact Or.inl hget
  | cons e m id0 ty0 vars m1 b1 m2 e2 halloc hrest ih =>
      intro hget
      have hstep := ih id b ty hget
      cases hstep with
      | inl hget1 =>
          have hspec := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
            (A := block × type) id id0 (b1, ty0) e
          rw [hspec] at hget1
          cases hp : peq id id0 with
          | left heq =>
            subst id0
            simp only [hp] at hget1
            cases hget1
            right
            constructor
            · rw [alloc_result_range_local m (.Z0 : Z) (sizeof ge.genv_cenv ty0) m1 b1 halloc]
              exact Ple_refl _
            · exact Plt_Ple_trans b1 m1.nextblock m2.nextblock
                (by
                  rw [alloc_result_range_local m (.Z0 : Z) (sizeof ge.genv_cenv ty0) m1 b1 halloc]
                  rw [alloc_nextblock_local m (.Z0 : Z) (sizeof ge.genv_cenv ty0) m1 b1 halloc]
                  exact Plt_succ _)
                (alloc_variables_nextblock ge (PTree.set id (b1, ty0) e) m1 vars e2 m2 hrest)
          | right heq =>
            simp only [hp] at hget1
            exact Or.inl hget1
      | inr hrange =>
          right
          constructor
          · exact Ple_trans m.nextblock m1.nextblock b
              (by
                rw [alloc_nextblock_local m (.Z0 : Z) (sizeof ge.genv_cenv ty0) m1 b1 halloc]
                exact Ple_succ _)
              hrange.1
          · exact hrange.2

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem alloc_variables_injective_alloc_result
    (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) : b = m.nextblock := by
  unfold Mem.alloc at halloc
  exact (congrArg Prod.snd halloc).symm

private theorem alloc_variables_injective_alloc_nextblock
    (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) :
    m'.nextblock = PArith.BinPos.Pos.succ m.nextblock := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have hnext := congrArg Mem.nextblock hfirst
  exact hnext.symm

theorem alloc_variables_injective : alloc_variables_injectiveStatement := by
  intro ge id1 b1 ty1 id2 b2 ty2 e m vars e' m' halloc
  induction halloc generalizing id1 b1 ty1 id2 b2 ty2 with
  | nil =>
      intro hbase hrange hget1 hget2 hids
      exact hbase hget1 hget2 hids
  | cons e m id0 ty0 vars m1 b0 m2 e2 halloc hrest ih =>
      intro hbase hrange hget1 hget2 hids
      apply ih
      · intro hj1 hj2 hjneq
        have hs1 := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
          (A := block × type) id1 id0 (b0, ty0) e
        have hs2 := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
          (A := block × type) id2 id0 (b0, ty0) e
        rw [hs1] at hj1
        rw [hs2] at hj2
        cases hp1 : peq id1 id0 with
        | left heq1 =>
          cases hp2 : peq id2 id0 with
          | left heq2 =>
            exfalso
            exact hjneq (heq1.trans heq2.symm)
          | right heq2 =>
            simp only [hp1, hp2] at hj1 hj2
            injection hj1 with hb
            have hb' : b0 = b1 := congrArg Prod.fst hb
            have hlt := hrange id2 b2 ty2 hj2
            have hne : m.nextblock ≠ b2 := by
              intro hbc
              exact (Plt_ne b2 m.nextblock hlt) hbc.symm
            intro hbc
            apply hne
            rw [← alloc_variables_injective_alloc_result m (.Z0 : Z)
              (sizeof ge.genv_cenv ty0) m1 b0 halloc]
            exact hb'.trans hbc
        | right heq1 =>
          cases hp2 : peq id2 id0 with
          | left heq2 =>
            simp only [hp1, hp2] at hj1 hj2
            injection hj2 with hb
            have hb' : b0 = b2 := congrArg Prod.fst hb
            have hlt := hrange id1 b1 ty1 hj1
            have hne : m.nextblock ≠ b1 := by
              intro hbc
              exact (Plt_ne b1 m.nextblock hlt) hbc.symm
            intro hbc
            apply hne
            rw [← alloc_variables_injective_alloc_result m (.Z0 : Z)
              (sizeof ge.genv_cenv ty0) m1 b0 halloc]
            exact hb'.trans hbc.symm
          | right heq2 =>
            simp only [hp1, hp2] at hj1 hj2
            exact hbase hj1 hj2 hjneq
      · intro j c t hj
        have hs := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
          (A := block × type) j id0 (b0, ty0) e
        rw [hs] at hj
        cases hp : peq j id0 with
        | left heq =>
          simp only [hp] at hj
          cases hj
          rw [alloc_variables_injective_alloc_result m (.Z0 : Z)
            (sizeof ge.genv_cenv ty0) m1 b0 halloc]
          rw [alloc_variables_injective_alloc_nextblock m (.Z0 : Z)
            (sizeof ge.genv_cenv ty0) m1 b0 halloc]
          exact Plt_succ _
        | right heq =>
          simp only [hp] at hj
          exact Plt_trans c m.nextblock m1.nextblock (hrange j c t hj)
            (by
              rw [alloc_variables_injective_alloc_nextblock m (.Z0 : Z)
                (sizeof ge.genv_cenv ty0) m1 b0 halloc]
              exact Plt_succ _)
      · exact hget1
      · exact hget2
      · exact hids

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem mav_alloc_result (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) : b = m.nextblock := by
  unfold Mem.alloc at halloc
  exact (congrArg Prod.snd halloc).symm

private theorem mav_alloc_nextblock (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) :
    m'.nextblock = PArith.BinPos.Pos.succ m.nextblock := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  exact (congrArg Mem.nextblock hfirst).symm

private theorem mav_alloc_valid_old (m : mem) (lo hi : Z) (m' : mem) (b b' : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (hvalid : Mem.valid_block m b') :
    Mem.valid_block m' b' := by
  unfold Mem.valid_block at hvalid ⊢
  rw [mav_alloc_nextblock m lo hi m' b halloc]
  exact Plt_trans_succ _ _ hvalid

private theorem mav_alloc_fresh_invalid (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) : ¬ Mem.valid_block m b := by
  rw [mav_alloc_result m lo hi m' b halloc]
  exact Plt_strict _

private theorem mav_alloc_fresh_valid (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) : Mem.valid_block m' b := by
  unfold Mem.valid_block
  rw [mav_alloc_result m lo hi m' b halloc]
  rw [mav_alloc_nextblock m lo hi m' b halloc]
  exact Plt_succ _

private theorem mav_alloc_valid_inv (m : mem) (lo hi : Z) (m' : mem) (b x : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (hvalid : Mem.valid_block m' x) :
    x = b ∨ Mem.valid_block m x := by
  have hlt : Plt x (PArith.BinPos.Pos.succ m.nextblock) := by
    unfold Mem.valid_block at hvalid
    rwa [mav_alloc_nextblock m lo hi m' b halloc] at hvalid
  have hle : PArith.BinPos.Pos.le x m.nextblock :=
    (PArith.BinPos.Pos.lt_succ_r x m.nextblock).mp hlt
  by_cases hx : x = b
  · exact Or.inl hx
  · right
    unfold Mem.valid_block Plt
    change posToNat x < posToNat m.nextblock
    change posToNat x ≤ posToNat m.nextblock at hle
    have hne : posToNat x ≠ posToNat m.nextblock := by
      intro heq
      apply hx
      rw [mav_alloc_result m lo hi m' b halloc]
      exact posToNat_injective heq
    omega

private theorem mav_alloc_access_old (m : mem) (lo hi : Z) (m' : mem) (b b' : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (hne : b' ≠ b) :
    PMap.get b' m'.mem_access = PMap.get b' m.mem_access := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have haccess := congrArg (fun x : mem => x.mem_access) hfirst
  rw [← haccess]
  apply PMap.gso
  rwa [mav_alloc_result m lo hi m' b halloc] at hne

private theorem mav_alloc_contents_old (m : mem) (lo hi : Z) (m' : mem) (b b' : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (hne : b' ≠ b) :
    PMap.get b' m'.mem_contents = PMap.get b' m.mem_contents := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have hcontents := congrArg (fun x : mem => x.mem_contents) hfirst
  rw [← hcontents]
  apply PMap.gso
  rwa [mav_alloc_result m lo hi m' b halloc] at hne

private theorem mav_alloc_perm_old_iff (m : mem) (lo hi : Z) (m' : mem) (b b' : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (hne : b' ≠ b)
    (ofs : Z) (k : perm_kind) (p : permission) :
    Mem.perm m' b' ofs k p ↔ Mem.perm m b' ofs k p := by
  unfold Mem.perm
  rw [mav_alloc_access_old m lo hi m' b b' halloc hne]

private theorem mav_alloc_new_perm_transfer
    (m tm m' tm' : mem) (lo hi : Z) (b tb : block)
    (halloc : Mem.alloc m lo hi = (m', b))
    (htalloc : Mem.alloc tm lo hi = (tm', tb))
    (ofs : Z) (k : perm_kind) (p : permission) :
    Mem.perm m' b ofs k p → Mem.perm tm' tb ofs k p := by
  intro hperm
  unfold Mem.alloc at halloc htalloc
  cases halloc
  cases htalloc
  unfold Mem.perm at hperm ⊢
  rw [PMap.gss] at hperm ⊢
  exact hperm

private theorem mav_alloc_new_contents_undef
    (m m' : mem) (lo hi : Z) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (ofs : Z) :
    ZMap.get ofs (PMap.get b m'.mem_contents) = Undef := by
  unfold Mem.alloc at halloc
  cases halloc
  rw [PMap.gss]
  exact ZMap.gi_proof _ _ _

private theorem mav_alloc_left_unmapped
    (f : meminj) (m tm m' : mem) (lo hi : Z) (b : block)
    (hinj : Mem.inject f m tm) (halloc : Mem.alloc m lo hi = (m', b)) :
    ∃ f', Mem.inject f' m' tm ∧ inject_incr f f' ∧ f' b = none ∧
      ∀ x, x ≠ b → f' x = f x := by
  let f' : meminj := fun x => if x = b then none else f x
  have hfb : f b = none := hinj.mi_freeblocks b
    (mav_alloc_fresh_invalid m lo hi m' b halloc)
  have hincr : inject_incr f f' := by
    intro x x' delta hmap
    by_cases hx : x = b
    · subst x
      rw [hfb] at hmap
      cases hmap
    · simpa [f', hx] using hmap
  refine ⟨f', ?_, hincr, by simp [f'], ?_⟩
  · refine {
      mi_inj := ?_,
      mi_freeblocks := ?_,
      mi_mappedblocks := ?_,
      mi_no_overlap := ?_,
      mi_representable := ?_,
      mi_perm_inv := ?_ }
    · refine {
        mi_perm := ?_,
        mi_align := ?_,
        mi_memval := ?_ }
      · intro x x' delta ofs k p hmap hperm
        have hx : x ≠ b := by
          intro heq
          subst x
          simp [f'] at hmap
        have hmap0 : f x = some (x', delta) := by simpa [f', hx] using hmap
        exact hinj.mi_inj.mi_perm x x' delta ofs k p hmap0
          ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs k p).mp hperm)
      · intro x x' delta chunk ofs p hmap hrange
        have hx : x ≠ b := by
          intro heq
          subst x
          simp [f'] at hmap
        have hmap0 : f x = some (x', delta) := by simpa [f', hx] using hmap
        apply hinj.mi_inj.mi_align x x' delta chunk ofs p hmap0
        intro q hq
        exact (mav_alloc_perm_old_iff m lo hi m' b x halloc hx q Max p).mp
          (hrange q hq)
      · intro x ofs x' delta hmap hperm
        have hx : x ≠ b := by
          intro heq
          subst x
          simp [f'] at hmap
        have hmap0 : f x = some (x', delta) := by simpa [f', hx] using hmap
        rw [mav_alloc_contents_old m lo hi m' b x halloc hx]
        exact CompCert4Lean.Common.Memdata.memval_inject_incr f f' _ _
          (hinj.mi_inj.mi_memval x ofs x' delta hmap0
            ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs Cur Readable).mp hperm))
          hincr
    · intro x hinvalid
      by_cases hx : x = b
      · simp [f', hx]
      · have hinvalid0 : ¬ Mem.valid_block m x := by
          intro hvalid
          exact hinvalid (mav_alloc_valid_old m lo hi m' b x halloc hvalid)
        dsimp [f']
        split
        · rename_i heq
          exact False.elim (hx heq)
        · exact hinj.mi_freeblocks x hinvalid0
    · intro x x' delta hmap
      have hx : x ≠ b := by
        intro heq
        subst x
        simp [f'] at hmap
      exact hinj.mi_mappedblocks x x' delta (by simpa [f', hx] using hmap)
    · intro x x' delta y y' delta' ofs ofs' hxy hmap hmap' hperm hperm'
      have hx : x ≠ b := by
        intro heq
        subst x
        simp [f'] at hmap
      have hy : y ≠ b := by
        intro heq
        subst y
        simp [f'] at hmap'
      apply hinj.mi_no_overlap x x' delta y y' delta' ofs ofs' hxy
        (by simpa [f', hx] using hmap) (by simpa [f', hy] using hmap')
      · exact (mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs Max Nonempty).mp hperm
      · exact (mav_alloc_perm_old_iff m lo hi m' b y halloc hy ofs' Max Nonempty).mp hperm'
    · intro x x' delta ofs hmap hperm
      have hx : x ≠ b := by
        intro heq
        subst x
        simp [f'] at hmap
      apply hinj.mi_representable x x' delta ofs (by simpa [f', hx] using hmap)
      cases hperm with
      | inl hp =>
          exact Or.inl ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
            (Ptrofs.unsigned ofs) Max Nonempty).mp hp)
      | inr hp =>
          exact Or.inr ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
            (ZArith.BinInt.Z.sub (Ptrofs.unsigned ofs) (.Zpos .xH)) Max Nonempty).mp hp)
    · intro x ofs x' delta k p hmap hperm
      have hx : x ≠ b := by
        intro heq
        subst x
        simp [f'] at hmap
      have hbase := hinj.mi_perm_inv x ofs x' delta k p
        (by simpa [f', hx] using hmap) hperm
      cases hbase with
      | inl hp =>
          exact Or.inl ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs k p).mpr hp)
      | inr hp =>
          exact Or.inr (by
            intro hp'
            exact hp ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
              ofs Max Nonempty).mp hp'))
  · intro x hx
    simp [f', hx]

private theorem mav_zdivide_zero (a : Z) : ZArith.BinInt.Z.divide a (.Z0 : Z) := by
  refine ⟨.Z0, ?_⟩
  apply intOfZ_injective
  change intOfZ (.Z0 : Z) = intOfZ (zOfInt (intOfZ a * intOfZ (.Z0 : Z)))
  rw [intOfZ_zOfInt]
  change 0 = intOfZ a * 0
  omega

private theorem mav_zadd_zero (a : Z) : ZArith.BinInt.Z.add a (.Z0 : Z) = a := by
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  change intOfZ a + 0 = intOfZ a
  omega

private theorem mav_ptrofs_unsigned_range (i : Ptrofs.int) :
    ZArith.BinInt.Z.le (.Z0 : Z) (Ptrofs.unsigned i) ∧
      ZArith.BinInt.Z.le (Ptrofs.unsigned i) Ptrofs.max_unsigned := by
  constructor
  · have h := i.intrange.1
    change (-1 : _root_.Int) < intOfZ i.intval at h
    change 0 ≤ intOfZ i.intval
    omega
  · have h := i.intrange.2
    change intOfZ i.intval < intOfZ Ptrofs.modulus at h
    change intOfZ i.intval ≤
      intOfZ (ZArith.BinInt.Z.sub Ptrofs.modulus (.Zpos .xH))
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change intOfZ i.intval ≤ intOfZ Ptrofs.modulus - 1
    omega

private theorem mav_alloc_parallel_same
    (f : meminj) (m tm m' tm' : mem) (lo hi : Z) (b tb : block)
    (hinj : Mem.inject f m tm)
    (halloc : Mem.alloc m lo hi = (m', b))
    (htalloc : Mem.alloc tm lo hi = (tm', tb)) :
    ∃ f', Mem.inject f' m' tm' ∧ inject_incr f f' ∧
      f' b = some (tb, (.Z0 : Z)) ∧ ∀ x, x ≠ b → f' x = f x := by
  let f' : meminj := fun x => if x = b then some (tb, (.Z0 : Z)) else f x
  have hfb : f b = none := hinj.mi_freeblocks b
    (mav_alloc_fresh_invalid m lo hi m' b halloc)
  have hincr : inject_incr f f' := by
    intro x x' delta hmap
    by_cases hx : x = b
    · subst x
      rw [hfb] at hmap
      cases hmap
    · simpa [f', hx] using hmap
  have hnew : f' b = some (tb, (.Z0 : Z)) := by simp [f']
  have hold : ∀ x, x ≠ b → f' x = f x := by
    intro x hx
    simp [f', hx]
  refine ⟨f', ?_, hincr, hnew, hold⟩
  refine {
    mi_inj := ?_,
    mi_freeblocks := ?_,
    mi_mappedblocks := ?_,
    mi_no_overlap := ?_,
    mi_representable := ?_,
    mi_perm_inv := ?_ }
  · refine {
      mi_perm := ?_,
      mi_align := ?_,
      mi_memval := ?_ }
    · intro x x' delta ofs k p hmap hperm
      by_cases hx : x = b
      · subst x
        rw [hnew] at hmap
        have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
        have hxb : tb = x' := congrArg Prod.fst hpair
        have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
        subst x'
        subst delta
        change Mem.perm tm' (show positive from tb)
          (ZArith.BinInt.Z.add ofs (.Z0 : Z)) k p
        rw [mav_zadd_zero]
        exact mav_alloc_new_perm_transfer m tm m' tm' lo hi b tb
          halloc htalloc ofs k p hperm
      · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
        have hx'valid := hinj.mi_mappedblocks x x' delta hmap0
        have hx' : x' ≠ tb := by
          rw [mav_alloc_result tm lo hi tm' tb htalloc]
          exact Plt_ne x' tm.nextblock hx'valid
        exact (mav_alloc_perm_old_iff tm lo hi tm' tb x' htalloc hx'
          (ZArith.BinInt.Z.add ofs delta) k p).mpr
            (hinj.mi_inj.mi_perm x x' delta ofs k p hmap0
              ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs k p).mp hperm))
    · intro x x' delta chunk ofs p hmap hrange
      by_cases hx : x = b
      · subst x
        rw [hnew] at hmap
        have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
        have hxb : tb = x' := congrArg Prod.fst hpair
        have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
        subst x'
        subst delta
        exact mav_zdivide_zero _
      · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
        apply hinj.mi_inj.mi_align x x' delta chunk ofs p hmap0
        intro q hq
        exact (mav_alloc_perm_old_iff m lo hi m' b x halloc hx q Max p).mp
          (hrange q hq)
    · intro x ofs x' delta hmap hperm
      by_cases hx : x = b
      · subst x
        rw [hnew] at hmap
        have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
        have hxb : tb = x' := congrArg Prod.fst hpair
        have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
        subst x'
        subst delta
        rw [mav_alloc_new_contents_undef m m' lo hi b halloc ofs]
        exact memval_inject.undef f' _
      · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
        have hx'valid := hinj.mi_mappedblocks x x' delta hmap0
        have hx' : x' ≠ tb := by
          rw [mav_alloc_result tm lo hi tm' tb htalloc]
          exact Plt_ne x' tm.nextblock hx'valid
        rw [mav_alloc_contents_old m lo hi m' b x halloc hx]
        rw [mav_alloc_contents_old tm lo hi tm' tb x' htalloc hx']
        exact CompCert4Lean.Common.Memdata.memval_inject_incr f f' _ _
          (hinj.mi_inj.mi_memval x ofs x' delta hmap0
            ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs Cur Readable).mp hperm))
          hincr
  · intro x hinvalid
    by_cases hx : x = b
    · subst x
      exact False.elim (hinvalid (mav_alloc_fresh_valid m lo hi m' b halloc))
    · have hinvalid0 : ¬ Mem.valid_block m x := by
        intro hvalid
        exact hinvalid (mav_alloc_valid_old m lo hi m' b x halloc hvalid)
      rw [hold x hx]
      exact hinj.mi_freeblocks x hinvalid0
  · intro x x' delta hmap
    by_cases hx : x = b
    · subst x
      rw [hnew] at hmap
      have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
      have hxb : tb = x' := congrArg Prod.fst hpair
      have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
      subst x'
      exact mav_alloc_fresh_valid tm lo hi tm' tb htalloc
    · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
      exact mav_alloc_valid_old tm lo hi tm' tb x' htalloc
        (hinj.mi_mappedblocks x x' delta hmap0)
  · intro x x' delta y y' delta' ofs ofs' hxy hmap hmap' hperm hperm'
    by_cases hx : x = b
    · subst x
      by_cases hy : y = b
      · exact False.elim (hxy hy.symm)
      · rw [hnew] at hmap
        have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
        have hxb : tb = x' := congrArg Prod.fst hpair
        have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
        subst x'
        have hmap0 : f y = some (y', delta') := by simpa [hold y hy] using hmap'
        left
        intro heq
        have hyvalid := hinj.mi_mappedblocks y y' delta' hmap0
        have hyne : y' ≠ tb := by
          rw [mav_alloc_result tm lo hi tm' tb htalloc]
          exact Plt_ne y' tm.nextblock hyvalid
        exact hyne heq.symm
    · by_cases hy : y = b
      · subst y
        rw [hnew] at hmap'
        have hpair : (tb, (.Z0 : Z)) = (y', delta') := Option.some.inj hmap'
        have hyb : tb = y' := congrArg Prod.fst hpair
        have hdelta' : (.Z0 : Z) = delta' := congrArg Prod.snd hpair
        subst y'
        have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
        left
        have hxvalid := hinj.mi_mappedblocks x x' delta hmap0
        rw [mav_alloc_result tm lo hi tm' tb htalloc]
        exact Plt_ne x' tm.nextblock hxvalid
      · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
        have hmap0' : f y = some (y', delta') := by simpa [hold y hy] using hmap'
        apply hinj.mi_no_overlap x x' delta y y' delta' ofs ofs' hxy hmap0 hmap0'
        · exact (mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs Max Nonempty).mp hperm
        · exact (mav_alloc_perm_old_iff m lo hi m' b y halloc hy ofs' Max Nonempty).mp hperm'
  · intro x x' delta ofs hmap hperm
    by_cases hx : x = b
    · subst x
      rw [hnew] at hmap
      have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
      have hxb : tb = x' := congrArg Prod.fst hpair
      have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
      subst x'
      subst delta
      have hrange := mav_ptrofs_unsigned_range ofs
      have hz : ZArith.BinInt.Z.le (.Z0 : Z) .Z0 := by
        change (0 : _root_.Int) ≤ 0
        omega
      change ZArith.BinInt.Z.le (.Z0 : Z) .Z0 ∧
        ZArith.BinInt.Z.le (.Z0 : Z)
          (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) (.Z0 : Z)) ∧
        ZArith.BinInt.Z.le
          (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) (.Z0 : Z)) Ptrofs.max_unsigned
      rw [mav_zadd_zero]
      exact And.intro hz hrange
    · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
      apply hinj.mi_representable x x' delta ofs hmap0
      cases hperm with
      | inl hp =>
          exact Or.inl ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
            (Ptrofs.unsigned ofs) Max Nonempty).mp hp)
      | inr hp =>
          exact Or.inr ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
            (ZArith.BinInt.Z.sub (Ptrofs.unsigned ofs) (.Zpos .xH)) Max Nonempty).mp hp)
  · intro x ofs x' delta k p hmap hperm
    by_cases hx : x = b
    · subst x
      rw [hnew] at hmap
      have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
      have hxb : tb = x' := congrArg Prod.fst hpair
      have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
      subst x'
      subst delta
      exact Or.inl (by
        change Mem.perm tm' (show positive from tb)
          (ZArith.BinInt.Z.add ofs (.Z0 : Z)) k p at hperm
        rw [mav_zadd_zero] at hperm
        exact mav_alloc_new_perm_transfer tm m tm' m' lo hi tb b
          htalloc halloc ofs k p hperm)
    · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
      have hx'valid := hinj.mi_mappedblocks x x' delta hmap0
      have hx' : x' ≠ tb := by
        rw [mav_alloc_result tm lo hi tm' tb htalloc]
        exact Plt_ne x' tm.nextblock hx'valid
      have hbase := hinj.mi_perm_inv x ofs x' delta k p hmap0
        ((mav_alloc_perm_old_iff tm lo hi tm' tb x' htalloc hx'
          (ZArith.BinInt.Z.add ofs delta) k p).mp hperm)
      cases hbase with
      | inl hp =>
          exact Or.inl ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs k p).mpr hp)
      | inr hp =>
          exact Or.inr (by
            intro hp'
            exact hp ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
              ofs Max Nonempty).mp hp'))

theorem match_alloc_variables : match_alloc_variablesStatement := by
  unfold match_alloc_variablesStatement
  intro cfg p tp hprog
  dsimp only
  intro cenv e m vars e' m' halloc j tm te hnorep hinj
  have hcenv : (globalenv tp).genv_cenv = (globalenv p).genv_cenv :=
    comp_env_preserved cfg p tp hprog
  induction halloc generalizing j tm te with
  | nil =>
      refine ⟨j, te, tm, alloc_variables.nil te tm, hinj, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro b b' delta hmap
        exact hmap
      · intro b _
        rfl
      · intro b b' delta _ _
        rfl
      · intro b b' delta hmap hnot
        exact False.elim (hnot (hinj.mi_mappedblocks b b' delta hmap))
      · intro id ty hmem
        cases hmem
      · intro id _
        exact ⟨rfl, rfl⟩
  | cons e m id ty vars m1 b1 m2 e2 halloc hrest ih =>
      change list_norepet (id :: var_names vars) at hnorep
      cases hnorep with
      | cons _ hnotid hnrtail =>
        by_cases hmem : VSet.mem id cenv = true
        · rcases mav_alloc_left_unmapped j m tm m1 (.Z0 : Z)
              (sizeof (globalenv p).genv_cenv ty) b1 hinj halloc with
            ⟨j1, hinj1, hincr1, hj1new, hj1same⟩
          rcases ih j1 tm te hnrtail hinj1 with
            ⟨j', te', tm', htalloc, hinj', hincr', hsrc, htgt, hnew, hvars, hout⟩
          have htalloc' : alloc_variables (globalenv tp) te tm
              (remove_lifted cenv ((id, ty) :: vars)) te' tm' := by
            simpa [remove_lifted, hmem] using htalloc
          refine ⟨j', te', tm', htalloc', hinj', ?_, ?_, ?_, hnew, ?_, ?_⟩
          · intro x x' delta hmap
            exact hincr' x x' delta (hincr1 x x' delta hmap)
          · intro x hvalid
            have hx : x ≠ b1 := by
              intro heq
              subst x
              exact (mav_alloc_fresh_invalid m (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) m1 b1 halloc) hvalid
            calc
              j' x = j1 x := hsrc x (mav_alloc_valid_old m (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) m1 b1 x halloc hvalid)
              _ = j x := hj1same x hx
          · intro x x' delta hmap hvalid
            have hj : j' x = j1 x := htgt x x' delta hmap hvalid
            have hmap1 : j1 x = some (x', delta) := by simpa [← hj] using hmap
            have hx : x ≠ b1 := by
              intro heq
              subst x
              rw [hj1new] at hmap1
              cases hmap1
            exact hj.trans (hj1same x hx)
          · intro id0 ty0 hpair
            simp only [List.mem_cons] at hpair
            cases hpair with
            | inl heq =>
                cases heq
                have ho := hout id hnotid
                refine ⟨b1, ?_, ?_⟩
                · calc
                    PTree.get id e2 = PTree.get id (PTree.set id (b1, ty) e) := ho.1
                    _ = some (b1, ty) := PTree.gss (A := block × type) id (b1, ty) e
                · simp only [hmem, if_true]
                  exact ⟨ho.2, (hsrc b1 (mav_alloc_fresh_valid m (.Z0 : Z)
                    (sizeof (globalenv p).genv_cenv ty) m1 b1 halloc)).trans hj1new⟩
            | inr htail => exact hvars id0 ty0 htail
          · intro id0 hall
            change id0 ∉ id :: var_names vars at hall
            have hid : id0 ≠ id := by
              intro heq
              apply hall
              simp [heq]
            have htail : id0 ∉ var_names vars := by
              intro h
              exact hall (List.mem_cons_of_mem id h)
            have ho := hout id0 htail
            constructor
            · calc
                PTree.get id0 e2 = PTree.get id0 (PTree.set id (b1, ty) e) := ho.1
                _ = PTree.get id0 e := PTree.gso (A := block × type) (b1, ty) e hid
            · exact ho.2
        · rcases htm : Mem.alloc tm (.Z0 : Z)
              (sizeof (globalenv p).genv_cenv ty) with ⟨tm1, tb1⟩
          have htallocSource : Mem.alloc tm (.Z0 : Z)
              (sizeof (globalenv p).genv_cenv ty) = (tm1, tb1) := htm
          have htallocTarget : Mem.alloc tm (.Z0 : Z)
              (sizeof (globalenv tp).genv_cenv ty) = (tm1, tb1) := by
            rw [hcenv]
            exact htallocSource
          rcases mav_alloc_parallel_same j m tm m1 tm1 (.Z0 : Z)
              (sizeof (globalenv p).genv_cenv ty) b1 tb1 hinj halloc htallocSource with
            ⟨j1, hinj1, hincr1, hj1new, hj1same⟩
          rcases ih j1 tm1 (PTree.set id (tb1, ty) te) hnrtail hinj1 with
            ⟨j', te', tm', htrest, hinj', hincr', hsrc, htgt, hnew, hvars, hout⟩
          have htcons : alloc_variables (globalenv tp) te tm ((id, ty) ::
              remove_lifted cenv vars) te' tm' :=
            alloc_variables.cons te tm id ty (remove_lifted cenv vars) tm1 tb1 tm' te'
              htallocTarget htrest
          have htalloc' : alloc_variables (globalenv tp) te tm
              (remove_lifted cenv ((id, ty) :: vars)) te' tm' := by
            simpa [remove_lifted, hmem] using htcons
          refine ⟨j', te', tm', htalloc', hinj', ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro x x' delta hmap
            exact hincr' x x' delta (hincr1 x x' delta hmap)
          · intro x hvalid
            have hx : x ≠ b1 := by
              intro heq
              subst x
              exact (mav_alloc_fresh_invalid m (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) m1 b1 halloc) hvalid
            calc
              j' x = j1 x := hsrc x (mav_alloc_valid_old m (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) m1 b1 x halloc hvalid)
              _ = j x := hj1same x hx
          · intro x x' delta hmap hvalid
            have hj : j' x = j1 x := htgt x x' delta hmap
              (mav_alloc_valid_old tm (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) tm1 tb1 x' htallocSource hvalid)
            have hmap1 : j1 x = some (x', delta) := by simpa [← hj] using hmap
            have hx : x ≠ b1 := by
              intro heq
              subst x
              rw [hj1new] at hmap1
              have hp : (tb1, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap1
              have hb : tb1 = x' := congrArg Prod.fst hp
              subst x'
              exact (mav_alloc_fresh_invalid tm (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) tm1 tb1 htallocSource) hvalid
            exact hj.trans (hj1same x hx)
          · intro x x' delta hmap hnot
            by_cases hxb : x' = tb1
            · subst x'
              have hj : j' x = j1 x := htgt x tb1 delta hmap
                (mav_alloc_fresh_valid tm (.Z0 : Z)
                  (sizeof (globalenv p).genv_cenv ty) tm1 tb1 htallocSource)
              have hmap1 : j1 x = some (tb1, delta) := hj.symm.trans hmap
              by_cases hx : x = b1
              · subst x
                rw [hj1new] at hmap1
                have hp : (tb1, (.Z0 : Z)) = (tb1, delta) := Option.some.inj hmap1
                have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hp
                subst delta
                have ho := hout id hnotid
                refine ⟨id, ty, ?_, ?_, rfl⟩
                · calc
                    PTree.get id e2 = PTree.get id (PTree.set id (b1, ty) e) := ho.1
                    _ = some (b1, ty) := PTree.gss (A := block × type) id (b1, ty) e
                · rw [ho.2]
                  exact PTree.gss (A := block × type) id (tb1, ty) te
              · rw [hj1same x hx] at hmap1
                exact False.elim (hnot (hinj.mi_mappedblocks x tb1 delta hmap1))
            · apply hnew x x' delta hmap
              intro hvalid1
              cases mav_alloc_valid_inv tm (.Z0 : Z)
                  (sizeof (globalenv p).genv_cenv ty) tm1 tb1 x'
                  htallocSource hvalid1 with
              | inl heq => exact hxb heq
              | inr hvalid0 => exact hnot hvalid0
          · intro id0 ty0 hpair
            simp only [List.mem_cons] at hpair
            cases hpair with
            | inl heq =>
                cases heq
                have ho := hout id hnotid
                refine ⟨b1, ?_, ?_⟩
                · calc
                    PTree.get id e2 = PTree.get id (PTree.set id (b1, ty) e) := ho.1
                    _ = some (b1, ty) := PTree.gss (A := block × type) id (b1, ty) e
                · simp only [hmem, if_false]
                  refine ⟨tb1, ?_, ?_⟩
                  · rw [ho.2]
                    exact PTree.gss (A := block × type) id (tb1, ty) te
                  · exact (hsrc b1 (mav_alloc_fresh_valid m (.Z0 : Z)
                    (sizeof (globalenv p).genv_cenv ty) m1 b1 halloc)).trans hj1new
            | inr htail =>
                have hid : id0 ≠ id := by
                  intro heq
                  subst id0
                  apply hnotid
                  change id ∈ var_names vars
                  exact List.mem_map.mpr ⟨(id, ty0), htail, rfl⟩
                have hv := hvars id0 ty0 htail
                rcases hv with ⟨b, hb, hv⟩
                refine ⟨b, hb, ?_⟩
                cases hm0 : VSet.mem id0 cenv with
                | false => simpa [hm0] using hv
                | true =>
                    simp only [hm0, if_true] at hv ⊢
                    exact ⟨hv.1.trans (PTree.gso (A := block × type)
                      (tb1, ty) te hid), hv.2⟩
          · intro id0 hall
            change id0 ∉ id :: var_names vars at hall
            have hid : id0 ≠ id := by
              intro heq
              apply hall
              simp [heq]
            have htail : id0 ∉ var_names vars := by
              intro h
              exact hall (List.mem_cons_of_mem id h)
            have ho := hout id0 htail
            constructor
            · calc
                PTree.get id0 e2 = PTree.get id0 (PTree.set id (b1, ty) e) := ho.1
                _ = PTree.get id0 e := PTree.gso (A := block × type) (b1, ty) e hid
            · rw [ho.2]
              exact PTree.gso (A := block × type) (tb1, ty) te hid

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem alloc_variables_load_alloc_local
    (m : mem) (lo hi : Z) (m' : mem) (fresh : block)
    (halloc : Mem.alloc m lo hi = (m', fresh))
    (chunk : memory_chunk) (b : block) (ofs : Z) (v : val)
    (hload : Mem.load chunk m b ofs = some v) :
    Mem.load chunk m' b ofs = some v := by
  have hvacc := Mem.load_valid_access m chunk b ofs v hload
  have hperm : Mem.perm m b ofs Cur Readable := by
    apply hvacc.1 ofs
    constructor
    · change intOfZ ofs ≤ intOfZ ofs
      omega
    · change intOfZ ofs < intOfZ (ZArith.BinInt.Z.add ofs (size_chunk chunk))
      have hsize := CompCert4Lean.Common.Memdata.size_chunk_pos chunk
      change 0 < intOfZ (size_chunk chunk) at hsize
      unfold ZArith.BinInt.Z.add
      rw [intOfZ_zOfInt]
      omega
  have hvalid := Mem.perm_valid_block m b ofs Cur Readable hperm
  have hfresh : fresh = m.nextblock := by
    unfold Mem.alloc at halloc
    exact (congrArg Prod.snd halloc).symm
  have hne : b ≠ fresh := by
    rw [hfresh]
    exact Plt_ne b m.nextblock hvalid
  have haccess : PMap.get b m'.mem_access = PMap.get b m.mem_access := by
    unfold Mem.alloc at halloc
    have hfirst := congrArg Prod.fst halloc
    have heq := congrArg (fun x : mem => x.mem_access) hfirst
    rw [← heq]
    apply PMap.gso
    rwa [hfresh] at hne
  have hcontents : PMap.get b m'.mem_contents = PMap.get b m.mem_contents := by
    unfold Mem.alloc at halloc
    have hfirst := congrArg Prod.fst halloc
    have heq := congrArg (fun x : mem => x.mem_contents) hfirst
    rw [← heq]
    apply PMap.gso
    rwa [hfresh] at hne
  have hvacc' : Mem.valid_access m' chunk b ofs Readable := by
    constructor
    · intro q hq
      unfold Mem.perm
      rw [haccess]
      exact hvacc.1 q hq
    · exact hvacc.2
  rcases Mem.valid_access_load m' chunk b ofs hvacc' with ⟨v', hload'⟩
  have hres' := Mem.load_result chunk m' b ofs v' hload'
  have hres := Mem.load_result chunk m b ofs v hload
  have hv : v' = v := by
    calc
      v' = decode_val chunk
          (Mem.getN (size_chunk_nat chunk) ofs (PMap.get b m'.mem_contents)) := hres'
      _ = decode_val chunk
          (Mem.getN (size_chunk_nat chunk) ofs (PMap.get b m.mem_contents)) := by rw [hcontents]
      _ = v := hres.symm
  simpa [hv] using hload'

theorem alloc_variables_load : alloc_variables_loadStatement := by
  intro prog e m vars e' m' halloc
  induction halloc with
  | nil =>
      intro chunk b ofs v hload
      exact hload
  | cons e m id ty vars m1 b1 m2 e2 halloc hrest ih =>
      intro chunk b ofs v hload
      apply ih
      exact alloc_variables_load_alloc_local m (.Z0 : Z)
        (sizeof (globalenv prog).genv_cenv ty) m1 b1 halloc chunk b ofs v hload

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem sizeof_by_value : sizeof_by_valueStatement := by
  intro prog ty chunk hmode
  cases ty with
  | Tvoid => cases hmode
  | Tint sz sg a =>
      cases sz <;> cases sg <;> cases hmode <;>
        simp [CompCert4Lean.Cfrontend.Ctypes.sizeof,
          CompCert4Lean.Common.Memdata.size_chunk,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le]
  | Tlong sg a =>
      cases hmode
      simp [CompCert4Lean.Cfrontend.Ctypes.sizeof,
        CompCert4Lean.Common.Memdata.size_chunk,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le]
  | Tfloat sz a =>
      cases sz <;> cases hmode <;>
        simp [CompCert4Lean.Cfrontend.Ctypes.sizeof,
          CompCert4Lean.Common.Memdata.size_chunk,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le]
  | Tpointer t a =>
      cases hmode
      simp [CompCert4Lean.Cfrontend.Ctypes.sizeof,
        CompCert4Lean.Common.Memdata.size_chunk,
        CompCert4Lean.Common.AST.Mptr,
        CompCert4Lean.X86_64.Archi.ptr64,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le]
  | Tarray t n a => cases hmode
  | Tfunction args ret cc => cases hmode
  | Tstruct id a => cases hmode
  | Tunion id a => cases hmode

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem alloc_variables_initial_value_fresh
    (prog : program) (m m' : mem) (b : block) (ty : type)
    (halloc : Mem.alloc m (.Z0 : Z) (sizeof (globalenv prog).genv_cenv ty) = (m', b))
    (chunk : memory_chunk) (hmode : access_mode ty = .By_value chunk) :
    Mem.load chunk m' b (.Z0 : Z) = some .Vundef := by
  have hsize := sizeof_by_value prog ty chunk hmode
  have hvacc : Mem.valid_access m' chunk b (.Z0 : Z) Readable := by
    constructor
    · intro ofs hof
      have hlo := hof.1
      have hhi := hof.2
      have hbound : ZArith.BinInt.Z.lt ofs (sizeof (globalenv prog).genv_cenv ty) := by
        change 0 ≤ intOfZ ofs at hlo
        change intOfZ ofs < intOfZ (ZArith.BinInt.Z.add (.Z0 : Z) (size_chunk chunk)) at hhi
        change intOfZ (size_chunk chunk) ≤
          intOfZ (sizeof (globalenv prog).genv_cenv ty) at hsize
        unfold ZArith.BinInt.Z.add at hhi
        rw [intOfZ_zOfInt] at hhi
        have hz : intOfZ (.Z0 : Z) = 0 := rfl
        rw [hz] at hhi
        change intOfZ ofs < intOfZ (sizeof (globalenv prog).genv_cenv ty)
        omega
      unfold Mem.perm
      unfold Mem.alloc at halloc
      cases halloc
      rw [PMap.gss]
      change Mem.perm_order'
        (if (ZArith.BinInt.Z.leb (.Z0 : Z) ofs &&
          ZArith.BinInt.Z.ltb ofs (sizeof (globalenv prog).genv_cenv ty)) = true
          then some Freeable else none) Readable
      have hin : (ZArith.BinInt.Z.leb (.Z0 : Z) ofs &&
          ZArith.BinInt.Z.ltb ofs (sizeof (globalenv prog).genv_cenv ty)) = true := by
        change intOfZ (.Z0 : Z) ≤ intOfZ ofs at hlo
        change intOfZ ofs < intOfZ (sizeof (globalenv prog).genv_cenv ty) at hbound
        simpa [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb] using And.intro hlo hbound
      rw [if_pos hin]
      exact perm_F_any Readable
    · exact mav_zdivide_zero _
  rcases Mem.valid_access_load m' chunk b (.Z0 : Z) hvacc with ⟨v, hload⟩
  have hres := Mem.load_result chunk m' b (.Z0 : Z) v hload
  have hhead := mav_alloc_new_contents_undef m m' (.Z0 : Z)
    (sizeof (globalenv prog).genv_cenv ty) b halloc (.Z0 : Z)
  have hdecode : decode_val chunk
      (Mem.getN (size_chunk_nat chunk) (.Z0 : Z) (PMap.get b m'.mem_contents)) =
      Vundef := by
    obtain ⟨n, hn⟩ := size_chunk_nat_pos chunk
    rw [hn]
    simpa only [Mem.getN, hhead] using
      (decode_val_undef
        (Mem.getN n (ZArith.BinInt.Z.add (.Z0 : Z) (.Zpos .xH))
          (PMap.get b m'.mem_contents)) chunk)
  have hv : v = Vundef := hres.trans hdecode
  simpa [hv] using hload

theorem alloc_variables_initial_value : alloc_variables_initial_valueStatement := by
  intro prog e m vars e' m' halloc hinit
  induction halloc with
  | nil => exact hinit
  | cons e m id ty vars m1 b1 m2 e2 halloc hrest ih =>
      apply ih
      intro id' b ty' chunk hget hmode
      have hspec := PTree.gsspec_proof (A := block × type)
        id' id (b1, ty) e
      rw [hspec] at hget
      cases hid : peq id' id with
      | left heq =>
          simp only [hid] at hget
          cases hget
          exact alloc_variables_initial_value_fresh prog m m1 b1 ty halloc chunk hmode
      | right hne =>
          simp only [hid] at hget
          exact alloc_variables_load_alloc_local m (.Z0 : Z)
            (sizeof (globalenv prog).genv_cenv ty) m1 b1 halloc chunk b (.Z0 : Z)
            Vundef (hinit id' b ty' chunk hget hmode)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Maps

theorem create_undef_temps_charact : create_undef_temps_charactStatement := by
  intro id ty vars hmem
  induction vars with
  | nil => cases hmem
  | cons hd rest ih =>
      rcases hd with ⟨id1, ty1⟩
      cases hmem with
      | head _ =>
          simpa [create_undef_temps] using
            (PTree.gss (A := CompCert4Lean.Common.Values.val) id
              (.Vundef) (create_undef_temps rest))
      | tail _ htail =>
          by_cases hne : id ≠ id1
          · have hget := PTree.gso (A := CompCert4Lean.Common.Values.val)
                (i := id) (j := id1)
                (.Vundef) (create_undef_temps rest) hne
            change PTree.get id
              (PTree.set id1 (.Vundef) (create_undef_temps rest)) =
              some .Vundef
            exact hget.trans (ih htail)
          · have heq : id = id1 := Classical.byContradiction (fun hneq => hne hneq)
            subst id
            simpa [create_undef_temps] using
              (PTree.gss (A := CompCert4Lean.Common.Values.val) id1
                (.Vundef) (create_undef_temps rest))

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Maps

theorem create_undef_temps_inv : create_undef_temps_invStatement := by
  intro vars id v h
  induction vars with
  | nil =>
      have hempty : PTree.get id (PTree.empty CompCert4Lean.Common.Values.val) = none :=
        PTree.gempty _ _
      change PTree.get id (PTree.empty CompCert4Lean.Common.Values.val) = some v at h
      rw [hempty] at h
      cases h
  | cons hd rest ih =>
      rcases hd with ⟨id1, ty1⟩
      change PTree.get id
        (PTree.set id1 (.Vundef) (create_undef_temps rest)) = some v at h
      have hspec := PTree.gsspec_proof (A := CompCert4Lean.Common.Values.val)
        id id1 (.Vundef) (create_undef_temps rest)
      rw [hspec] at h
      cases hp : CompCert4Lean.Lib.Coqlib.peq id id1 with
      | left heq =>
          subst id
          simp only [hp] at h
          constructor
          · exact (Option.some.inj h).symm
          · exact List.mem_cons_self
      | right hne =>
          have htail : PTree.get id (create_undef_temps rest) = some v := by
            simpa [hp] using h
          rcases ih htail with ⟨hv, hin⟩
          constructor
          · exact hv
          · exact List.mem_cons.mpr (Or.inr hin)

end CompCert4Lean.Cfrontend.SimplLocalsproof
