import CompCert4Lean.Backend.RTLgen
import CompCert4Lean.Backend.RTLgenspec
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Foundation.Recursion

/-!
# Correctness surface for RTL generation

The executable relations and specification predicates from
`backend/RTLgenproof.v` are translated directly.  Proof declarations assigned
to the later proof-migration phase are retained as exact transparent
proposition descriptors.
-/

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Support
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

/-! ## Compilation-environment matching -/

structure map_wf (m : mapping) : Prop where
  mapWfInjective : ∀ id1 id2 r,
    PTree.get id1 m.map_vars = some r →
    PTree.get id2 m.map_vars = some r → id1 = id2
  mapWfDisjoint : ∀ id r,
    PTree.get id m.map_vars = some r → r ∈ m.map_letvars → False

structure match_env (map : mapping) (e : CompCert4Lean.Backend.Cminor.env)
    (le : letenv) (rs : regset) : Prop where
  me_vars : ∀ id v,
    PTree.get id e = some v →
    ∃ r, PTree.get id map.map_vars = some r ∧ Val.lessdef v (Regmap.get r rs)
  me_letvars : Val.lessdef_list le (map.map_letvars.map (fun r => Regmap.get r rs))

export match_env (me_vars me_letvars)

/-! ## Program matching -/

def match_prog (p : CminorSel.program) (tp : RTL.program) : Prop :=
  @match_program (fundef CminorSel.function) Unit (fundef RTL.function) Unit
    (Linker_fundef CminorSel.function) Linker_unit
    (fun _ f tf => RTLgen.transl_fundef f = .OK tf) Eq p tp

/-! ## Expression and exit simulation predicates -/

def transl_expr_prop (xi : ExternalCalls) (tprog : RTL.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : expr) (v : val) : Prop :=
  let tge := Genv.globalenv tprog
  ∀ tm cs f map pr ns nd rd rs dst,
    map_wf map →
    tr_expr f.fn_code map pr a ns nd rd dst →
    match_env map e le rs →
    Mem.extends m tm →
    ∃ rs' tm',
      star (RTL.step xi) tge (RTL.State cs f sp ns rs tm) E0
          (RTL.State cs f sp nd rs' tm') ∧
      match_env map (CompCert4Lean.Backend.Cminor.set_optvar dst v e) le rs' ∧
      Val.lessdef v (Regmap.get rd rs') ∧
      (∀ r, r ∈ pr → Regmap.get r rs' = Regmap.get r rs) ∧
      Mem.extends m tm'

def transl_exprlist_prop (xi : ExternalCalls) (tprog : RTL.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (al : exprlist) (vl : List val) : Prop :=
  let tge := Genv.globalenv tprog
  ∀ tm cs f map pr ns nd rl rs,
    map_wf map →
    tr_exprlist f.fn_code map pr al ns nd rl →
    match_env map e le rs →
    Mem.extends m tm →
    ∃ rs' tm',
      star (RTL.step xi) tge (RTL.State cs f sp ns rs tm) E0
          (RTL.State cs f sp nd rs' tm') ∧
      match_env map e le rs' ∧
      Val.lessdef_list vl (rl.map (fun r => Regmap.get r rs')) ∧
      (∀ r, r ∈ pr → Regmap.get r rs' = Regmap.get r rs) ∧
      Mem.extends m tm'

def transl_condexpr_prop (xi : ExternalCalls) (tprog : RTL.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : condexpr) (v : Bool) : Prop :=
  let tge := Genv.globalenv tprog
  ∀ tm cs f map pr ns ntrue nfalse rs,
    map_wf map →
    tr_condition f.fn_code map pr a ns ntrue nfalse →
    match_env map e le rs →
    Mem.extends m tm →
    ∃ rs' tm',
      plus (RTL.step xi) tge (RTL.State cs f sp ns rs tm) E0
          (RTL.State cs f sp (if v then ntrue else nfalse) rs' tm') ∧
      match_env map e le rs' ∧
      (∀ r, r ∈ pr → Regmap.get r rs' = Regmap.get r rs) ∧
      Mem.extends m tm'

def transl_exitexpr_prop (xi : ExternalCalls) (tprog : RTL.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : exitexpr) (x : Nat) : Prop :=
  let tge := Genv.globalenv tprog
  ∀ tm cs f map ns nexits rs,
    map_wf map →
    tr_exitexpr f.fn_code map a ns nexits →
    match_env map e le rs →
    Mem.extends m tm →
    ∃ nd rs' tm',
      star (RTL.step xi) tge (RTL.State cs f sp ns rs tm) E0
          (RTL.State cs f sp nd rs' tm') ∧
      nth_error nexits x = some nd ∧
      match_env map e le rs' ∧
      Mem.extends m tm'

/-! ## Measures -/

def size_stmt : stmt → Nat
  | .Sskip => 0
  | .Sseq s1 s2 => size_stmt s1 + size_stmt s2 + 1
  | .Sifthenelse _ s1 s2 => size_stmt s1 + size_stmt s2 + 1
  | .Sloop s1 => size_stmt s1 + 1
  | .Sblock s1 => size_stmt s1 + 1
  | .Sexit _ => 0
  | .Slabel _ s1 => size_stmt s1 + 1
  | _ => 1

def size_cont : cont → Nat
  | .Kseq s k1 => size_stmt s + size_cont k1 + 1
  | .Kblock k1 => size_cont k1 + 1
  | _ => 0

def measure_state : CminorSel.state → Nat × Nat
  | .State _ s k _ _ _ => (size_stmt s + size_cont k, size_stmt s)
  | _ => (0, 0)

def lt_state (s1 s2 : CminorSel.state) : Prop :=
  lex_ord Nat.lt Nat.lt (measure_state s1) (measure_state s2)

/-! ## Continuations and state matching -/

private inductive trFunSupport (tf : RTL.function) (map : mapping)
    (f : CminorSel.function) (ngoto : labelmap) (nret : node)
    (rret : Option reg) : Prop where
  | intro :
      tr_stmt tf.fn_code map f.fn_body nret nret [] ngoto nret rret →
      trFunSupport tf map f ngoto nret rret

mutual
  inductive tr_cont : RTL.code → mapping → CminorSel.cont → node → List node →
      labelmap → node → Option reg → List RTL.stackframe → Prop where
    | trContSeq (c : RTL.code) (map : mapping) (s : stmt) (k : cont)
        (nd : node) (nexits : List node) (ngoto : labelmap) (nret : node)
        (rret : Option reg) (cs : List RTL.stackframe) (n : node)
        (hstmt : tr_stmt c map s nd n nexits ngoto nret rret)
        (hk : tr_cont c map k n nexits ngoto nret rret cs) :
        tr_cont c map (.Kseq s k) nd nexits ngoto nret rret cs
    | trContBlock (c : RTL.code) (map : mapping) (k : cont) (nd : node)
        (nexits : List node) (ngoto : labelmap) (nret : node)
        (rret : Option reg) (cs : List RTL.stackframe)
        (hk : tr_cont c map k nd nexits ngoto nret rret cs) :
        tr_cont c map (.Kblock k) nd (nd :: nexits) ngoto nret rret cs
    | trContStop (c : RTL.code) (map : mapping) (ngoto : labelmap) (nret : node)
        (rret : Option reg) (cs : List RTL.stackframe)
        (hcode : PTree.get nret c = some (.Ireturn rret))
        (hs : match_stacks .Kstop cs) :
        tr_cont c map .Kstop nret [] ngoto nret rret cs
    | trContCall (c : RTL.code) (map : mapping) (optid : Option ident)
        (f : CminorSel.function) (sp : val) (e : CompCert4Lean.Backend.Cminor.env)
        (k : cont) (ngoto : labelmap) (nret : node) (rret : Option reg)
        (cs : List RTL.stackframe)
        (hcode : PTree.get nret c = some (.Ireturn rret))
        (hs : match_stacks (.Kcall optid f sp e k) cs) :
        tr_cont c map (.Kcall optid f sp e k) nret [] ngoto nret rret cs

  inductive match_stacks : CminorSel.cont → List RTL.stackframe → Prop where
    | matchStacksStop : match_stacks .Kstop []
    | matchStacksCall (optid : Option ident) (f : CminorSel.function)
        (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (k : cont)
        (r : reg) (tf : RTL.function) (n : node) (rs : regset)
        (cs : List RTL.stackframe) (map : mapping) (nexits : List node)
        (ngoto : labelmap) (nret : node) (rret : Option reg)
        (mwf : map_wf map) (tfrel : trFunSupport tf map f ngoto nret rret)
        (me : match_env map e [] rs)
        (rok : reg_map_ok map r optid)
        (tc : tr_cont tf.fn_code map k n nexits ngoto nret rret cs) :
        match_stacks (.Kcall optid f sp e k)
          (RTL.Stackframe r tf sp n rs :: cs)
end

inductive match_states : CminorSel.state → RTL.state → Prop where
  | matchStateState (f : CminorSel.function) (s : stmt) (k : cont) (sp : val)
      (e : CompCert4Lean.Backend.Cminor.env) (m tm : mem)
      (cs : List RTL.stackframe) (tf : RTL.function) (ns : node) (rs : regset)
      (map : mapping) (ncont : node) (nexits : List node) (ngoto : labelmap)
      (nret : node) (rret : Option reg)
      (mwf : map_wf map)
      (ts : tr_stmt tf.fn_code map s ns ncont nexits ngoto nret rret)
      (tfrel : trFunSupport tf map f ngoto nret rret)
      (tc : tr_cont tf.fn_code map k ncont nexits ngoto nret rret cs)
      (me : match_env map e [] rs) (mext : Mem.extends m tm) :
      match_states (.State f s k sp e m) (RTL.State cs tf sp ns rs tm)
  | matchStateCall (f : CminorSel.fundef) (args targs : List val)
      (k : cont) (m tm : mem) (cs : List RTL.stackframe)
      (tf : RTL.fundef)
      (htrans : RTLgen.transl_fundef f = .OK tf)
      (hs : match_stacks k cs) (ld : Val.lessdef_list args targs)
      (mext : Mem.extends m tm) :
      match_states (.Callstate f args k m) (RTL.Callstate cs tf targs tm)
  | matchStateReturn (v tv : val) (k : cont) (m tm : mem)
      (cs : List RTL.stackframe) (hs : match_stacks k cs)
      (ld : Val.lessdef v tv) (mext : Mem.extends m tm) :
      match_states (.returnState v k m) (RTL.Returnstate cs tv tm)

/-! ## Exact statement descriptors -/

def add_letvar_wfStatement : Prop :=
  ∀ (map : mapping) (r : reg), map_wf map → ¬ reg_in_map map r → map_wf (add_letvar map r)

def add_var_wfStatement : Prop :=
  ∀ (s1 s2 : RTLgen.state) (map : mapping) (name : ident) (r : reg)
    (map' : mapping) (i : RTLgen.state_incr s1 s2),
    add_var map name s1 = .OK (r, map') s2 i → map_wf map → map_valid map s1 → map_wf map'

def add_vars_wfStatement : Prop :=
  ∀ (names : List ident) (s1 s2 : RTLgen.state) (map map' : mapping)
    (rl : List reg) (i : RTLgen.state_incr s1 s2),
    add_vars map names s1 = .OK (rl, map') s2 i → map_wf map → map_valid map s1 → map_wf map'

def eval_builtin_args_trivialStatement : Prop :=
  ∀ (ge : RTL.genv) (rs : regset) (sp : val) (m : mem) (rl : List reg),
    eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs) sp m (rl.map (.BA ·))
      (rl.map (fun r => Regmap.get r rs))

def eval_exprlist_appendStatement : Prop :=
  ∀ (xi : ExternalCalls) (ge : CminorSel.genv) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem) (le : letenv)
    (al1 al2 : List expr) (vl1 vl2 : List val),
    CminorSel.eval_exprlist xi ge sp e m le
      (RTLgen.exprlist_of_expr_list al1) vl1 →
    CminorSel.eval_exprlist xi ge sp e m le
      (RTLgen.exprlist_of_expr_list al2) vl2 →
    CminorSel.eval_exprlist xi ge sp e m le
      (RTLgen.exprlist_of_expr_list (al1 ++ al2)) (vl1 ++ vl2)

def function_ptr_translatedStatement : Prop :=
  ∀ (prog : CminorSel.program) (tprog : RTL.program), match_prog prog tprog →
    ∀ (b : block) (f : CminorSel.fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      ∃ tf, Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧ RTLgen.transl_fundef f = .OK tf

def functions_translatedStatement : Prop :=
  ∀ (prog : CminorSel.program) (tprog : RTL.program), match_prog prog tprog →
    ∀ (v : val) (f : CminorSel.fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      ∃ tf, Genv.find_funct (Genv.globalenv tprog) v = some tf ∧ RTLgen.transl_fundef f = .OK tf

def init_mapping_wfStatement : Prop := map_wf RTLgen.init_mapping

def invert_eval_builtin_argStatement : Prop :=
  ∀ (xi : ExternalCalls) (ge : CminorSel.genv) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem) (a : builtin_arg expr) (v : val),
    CminorSel.eval_builtin_arg xi ge sp e m a v →
    ∃ vl,
      CminorSel.eval_exprlist xi ge sp e m []
        (RTLgen.exprlist_of_expr_list (params_of_builtin_arg a)) vl ∧
      eval_builtin_arg (Genv.to_senv ge) (fun v => v) sp m
          (convert_builtin_arg a vl).1 v ∧
      (∀ vl',
        convert_builtin_arg a (vl ++ vl') =
          ((convert_builtin_arg a vl).1, vl'))

def invert_eval_builtin_argsStatement : Prop :=
  ∀ (xi : ExternalCalls) (ge : CminorSel.genv) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (al : List (builtin_arg expr)) (vl : List val),
    list_forall2 (CminorSel.eval_builtin_arg xi ge sp e m) al vl →
    ∃ vl',
      CminorSel.eval_exprlist xi ge sp e m []
        (RTLgen.exprlist_of_expr_list (params_of_builtin_args al)) vl' ∧
      eval_builtin_args (Genv.to_senv ge) (fun v => v) sp m
        (convert_builtin_args al vl') vl

def lt_state_wfStatement : Prop := WellFounded lt_state

def match_env_bind_letvarStatement : Prop :=
  ∀ (map : mapping) (e : CompCert4Lean.Backend.Cminor.env) (le : letenv)
    (rs : regset) (r : reg) (v : val),
    match_env map e le rs → Val.lessdef v (Regmap.get r rs) →
    match_env (add_letvar map r) e (v :: le) rs

def match_env_emptyStatement : Prop :=
  ∀ (map : mapping), map.map_letvars = [] →
    match_env map (PTree.empty val) [] (Regmap.init Vundef)

def match_env_find_letvarStatement : Prop :=
  ∀ (map : mapping) (e : CompCert4Lean.Backend.Cminor.env) (le : letenv) (rs : regset)
    (idx : Nat) (v : val) (r : reg), match_env map e le rs →
    nth_error le idx = some v → nth_error map.map_letvars idx = some r →
    Val.lessdef v (Regmap.get r rs)

def match_env_find_varStatement : Prop :=
  ∀ (map : mapping) (e : CompCert4Lean.Backend.Cminor.env) (le : letenv) (rs : regset)
    (id : ident) (v : val) (r : reg), match_env map e le rs →
    PTree.get id e = some v → PTree.get id map.map_vars = some r →
    Val.lessdef v (Regmap.get r rs)

def match_env_invariantStatement : Prop :=
  ∀ (map : mapping) (e : CompCert4Lean.Backend.Cminor.env) (le : letenv)
    (rs rs' : regset), match_env map e le rs →
    (∀ r, reg_in_map map r → Regmap.get r rs' = Regmap.get r rs) → match_env map e le rs'

def match_env_unbind_letvarStatement : Prop :=
  ∀ (map : mapping) (e : CompCert4Lean.Backend.Cminor.env) (le : letenv)
    (rs : regset) (r : reg) (v : val),
    match_env (add_letvar map r) e (v :: le) rs → match_env map e le rs

def match_env_update_destStatement : Prop :=
  ∀ (map : mapping) (e : CompCert4Lean.Backend.Cminor.env) (le : letenv) (rs : regset)
    (dst : Option ident) (r : reg) (v tv : val), Val.lessdef v tv → map_wf map →
    reg_map_ok map r dst → match_env map e le rs →
    match_env map (CompCert4Lean.Backend.Cminor.set_optvar dst v e) le (Regmap.set r tv rs)

def match_env_update_resStatement : Prop :=
  ∀ (map : mapping) (res : builtin_res ident) (v : val)
    (e : CompCert4Lean.Backend.Cminor.env) (le : letenv) (tres : builtin_res reg)
    (tv : val) (rs : regset), Val.lessdef v tv → map_wf map →
    tr_builtin_res map res tres → match_env map e le rs →
    match_env map (set_builtin_res res v e) le
      (regmap_setres tres tv rs)

def match_env_update_tempStatement : Prop :=
  ∀ (map : mapping) (e : CompCert4Lean.Backend.Cminor.env) (le : letenv)
    (rs : regset) (r : reg) (v : val), match_env map e le rs → ¬ reg_in_map map r →
    match_env map e le (Regmap.set r v rs)

def match_env_update_varStatement : Prop :=
  ∀ (map : mapping) (e : CompCert4Lean.Backend.Cminor.env) (le : letenv) (rs : regset)
    (id : ident) (r : reg) (v tv : val), Val.lessdef v tv → map_wf map →
    PTree.get id map.map_vars = some r → match_env map e le rs →
    match_env map (PTree.set id v e) le
      (Regmap.set r tv rs)

def match_init_env_init_regStatement : Prop :=
  ∀ (params vars : List ident) (s0 s1 s2 : RTLgen.state)
    (rparams rvars : List reg) (map1 map2 : mapping)
    (i1 : RTLgen.state_incr s0 s1) (i2 : RTLgen.state_incr s1 s2)
    (vparams tvparams : List val),
    add_vars RTLgen.init_mapping params s0 = .OK (rparams, map1) s1 i1 →
    add_vars map1 vars s1 = .OK (rvars, map2) s2 i2 →
    Val.lessdef_list vparams tvparams →
    match_env map2
      (CompCert4Lean.Backend.Cminor.set_locals vars
        (CompCert4Lean.Backend.Cminor.set_params vparams params))
      [] (init_regs tvparams rparams)

def match_set_localsStatement : Prop :=
  ∀ (map1 : mapping) (s1 : RTLgen.state) (il : List ident)
    (rl : List reg) (map2 : mapping) (s2 : RTLgen.state)
    (e : CompCert4Lean.Backend.Cminor.env) (le : letenv) (rs : regset)
    (i : RTLgen.state_incr s1 s2),
    map_wf map1 →
    match_env map1 e le rs →
    (∀ r, reg_fresh r s1 → Regmap.get r rs = Vundef) →
    add_vars map1 il s1 = .OK (rl, map2) s2 i →
    match_env map2 (CompCert4Lean.Backend.Cminor.set_locals il e) le rs

def match_set_params_init_regsStatement : Prop :=
  ∀ (il : List ident) (rl : List reg) (s1 s2 : RTLgen.state)
    (map2 : mapping) (i : RTLgen.state_incr s1 s2)
    (vl tvl : List val),
    add_vars RTLgen.init_mapping il s1 = .OK (rl, map2) s2 i →
    Val.lessdef_list vl tvl →
    match_env map2 (CompCert4Lean.Backend.Cminor.set_params vl il) []
      (init_regs tvl rl) ∧
    (∀ r, reg_fresh r s2 → Regmap.get r (init_regs tvl rl) = Vundef)

def match_stacks_call_contStatement : Prop :=
  ∀ (c : RTL.code) (map : mapping) (k : cont) (ncont : node)
    (nexits : List node) (ngoto : labelmap) (nret : node)
    (rret : Option reg) (cs : List RTL.stackframe),
    tr_cont c map k ncont nexits ngoto nret rret cs →
    match_stacks (CompCert4Lean.Backend.CminorSel.call_cont k) cs ∧
      PTree.get nret c = some (.Ireturn rret)

def senv_preservedStatement : Prop :=
  ∀ (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    Senv.equiv
      (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def sig_transl_functionStatement : Prop :=
  ∀ (f : CminorSel.fundef) (tf : RTL.fundef),
    RTLgen.transl_fundef f = .OK tf →
    RTL.funsig tf = CminorSel.funsig f

def symbols_preservedStatement : Prop :=
  ∀ (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (id : ident),
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id

def tr_cont_call_contStatement : Prop :=
  ∀ (c : RTL.code) (map : mapping) (k : cont) (ncont : node)
    (nexits : List node) (ngoto : labelmap) (nret : node)
    (rret : Option reg) (cs : List RTL.stackframe),
    tr_cont c map k ncont nexits ngoto nret rret cs →
    tr_cont c map (CompCert4Lean.Backend.CminorSel.call_cont k) nret []
      ngoto nret rret cs

def tr_find_labelStatement : Prop :=
  ∀ (c : RTL.code) (map : mapping) (lbl : ident) (n : node)
    (ngoto : labelmap) (nret : node) (rret : Option reg)
    (s' : stmt) (k' : cont) (cs : List RTL.stackframe),
    PTree.get lbl ngoto = some n →
    ∀ (s : stmt) (k : cont) (ns1 nd1 : node) (nexits1 : List node),
      CompCert4Lean.Backend.CminorSel.find_label lbl s k = some (s', k') →
      tr_stmt c map s ns1 nd1 nexits1 ngoto nret rret →
      tr_cont c map k nd1 nexits1 ngoto nret rret cs →
      ∃ ns2 nd2 nexits2,
        PTree.get n c = some (.Inop ns2) ∧
        tr_stmt c map s' ns2 nd2 nexits2 ngoto nret rret ∧
        tr_cont c map k' nd2 nexits2 ngoto nret rret cs

def tr_move_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (tprog : RTL.program) (r1 : reg) (ns : node)
    (r2 : reg) (nd : node) (cs : List RTL.stackframe)
    (f : RTL.function) (sp : val) (rs : regset) (m : mem),
    tr_move f.fn_code ns r1 nd r2 →
    ∃ rs',
      star (RTL.step xi) (Genv.globalenv tprog)
        (RTL.State cs f sp ns rs m) E0
        (RTL.State cs f sp nd rs' m) ∧
      Regmap.get r2 rs' = Regmap.get r1 rs ∧
      (∀ r, r ≠ r2 → Regmap.get r rs' = Regmap.get r rs)

def transf_program_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    forward_simulation
      (CminorSel.semantics xi prog)
      (RTL.semantics xi tprog)

def transf_program_matchStatement : Prop :=
  ∀ (p : CminorSel.program) (tp : RTL.program),
    RTLgen.transl_program p = .OK tp → match_prog p tp
def transl_condexpr_CEcond_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (cond : condition) (al : exprlist) (vl : List val)
    (vb : Bool),
    eval_exprlist xi (Genv.globalenv prog) sp e m le al vl →
    transl_exprlist_prop xi tprog sp e m le al vl →
    eval_condition cond vl m = some vb →
    transl_condexpr_prop xi tprog sp e m le (.CEcond cond al) vb

def transl_condexpr_CEcondition_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a b c : condexpr) (va : Bool) (v : Bool),
    eval_condexpr xi (Genv.globalenv prog) sp e m le a va →
    transl_condexpr_prop xi tprog sp e m le a va →
    eval_condexpr xi (Genv.globalenv prog) sp e m le (if va then b else c) v →
    transl_condexpr_prop xi tprog sp e m le (if va then b else c) v →
    transl_condexpr_prop xi tprog sp e m le (.CEcondition a b c) v

def transl_condexpr_CElet_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : expr) (b : condexpr) (v1 : val) (v2 : Bool),
    eval_expr xi (Genv.globalenv prog) sp e m le a v1 →
    transl_expr_prop xi tprog sp e m le a v1 →
    eval_condexpr xi (Genv.globalenv prog) sp e m (v1 :: le) b v2 →
    transl_condexpr_prop xi tprog sp e m (v1 :: le) b v2 →
    transl_condexpr_prop xi tprog sp e m le (.CElet a b) v2

def transl_condexpr_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : condexpr) (v : Bool),
    eval_condexpr xi (Genv.globalenv prog) sp e m le a v →
    transl_condexpr_prop xi tprog sp e m le a v

def transl_eval_builtin_argStatement : Prop :=
  ∀ (prog : CminorSel.program) (sp : val) (m : mem)
    (rs : regset) (a : builtin_arg expr) (vl : List val)
    (rl : List reg) (v : val),
    Val.lessdef_list vl (rl.map (fun r => Regmap.get r rs)) →
    eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
      (fun v => v) sp m (convert_builtin_arg a vl).1 v →
    ∃ v',
      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
        (fun r => Regmap.get r rs) sp m (convert_builtin_arg a rl).1 v' ∧
      Val.lessdef v v' ∧
      Val.lessdef_list (convert_builtin_arg a vl).2
        ((convert_builtin_arg a rl).2.map (fun r => Regmap.get r rs))

def transl_eval_builtin_argsStatement : Prop :=
  ∀ (prog : CminorSel.program) (sp : val) (m : mem)
    (rs : regset) (al : List (builtin_arg expr))
    (vl1 : List val) (rl : List reg) (vl : List val),
    Val.lessdef_list vl1 (rl.map (fun r => Regmap.get r rs)) →
    eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
      (fun v => v) sp m (convert_builtin_args al vl1) vl →
    ∃ vl',
      eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
        (fun r => Regmap.get r rs) sp m (convert_builtin_args al rl) vl' ∧
      Val.lessdef_list vl vl'

def transl_exitexpr_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : exitexpr) (x : Nat),
    eval_exitexpr xi (Genv.globalenv prog) sp e m le a x →
    transl_exitexpr_prop xi tprog sp e m le a x

def transl_expr_Ebuiltin_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (ef : external_function) (al : exprlist)
    (vl : List val) (v : val),
    eval_exprlist xi (Genv.globalenv prog) sp e m le al vl →
    transl_exprlist_prop xi tprog sp e m le al vl →
    external_call xi ef (Genv.to_senv (Genv.globalenv prog)) vl m E0 v m →
    transl_expr_prop xi tprog sp e m le (.Ebuiltin ef al) v

def transl_expr_Econdition_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : condexpr) (ifso ifnot : expr)
    (va : Bool) (v : val),
    eval_condexpr xi (Genv.globalenv prog) sp e m le a va →
    transl_condexpr_prop xi tprog sp e m le a va →
    eval_expr xi (Genv.globalenv prog) sp e m le (if va then ifso else ifnot) v →
    transl_expr_prop xi tprog sp e m le (if va then ifso else ifnot) v →
    transl_expr_prop xi tprog sp e m le (.Econdition a ifso ifnot) v

def transl_expr_Eexternal_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (id : ident) (sg : signature) (al : exprlist)
    (b : block) (ef : external_function) (vl : List val) (v : val),
    Genv.find_symbol (Genv.globalenv prog) id = some b →
    Genv.find_funct_ptr (Genv.globalenv prog) b = some (.External ef) →
    ef_sig ef = sg →
    eval_exprlist xi (Genv.globalenv prog) sp e m le al vl →
    transl_exprlist_prop xi tprog sp e m le al vl →
    external_call xi ef (Genv.to_senv (Genv.globalenv prog)) vl m E0 v m →
    transl_expr_prop xi tprog sp e m le (.Eexternal id sg al) v

def transl_expr_Elet_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a1 a2 : expr) (v1 v2 : val),
    eval_expr xi (Genv.globalenv prog) sp e m le a1 v1 →
    transl_expr_prop xi tprog sp e m le a1 v1 →
    eval_expr xi (Genv.globalenv prog) sp e m (v1 :: le) a2 v2 →
    transl_expr_prop xi tprog sp e m (v1 :: le) a2 v2 →
    transl_expr_prop xi tprog sp e m le (.Elet a1 a2) v2

def transl_expr_Eletvar_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : List val) (n : Nat) (v : val),
    nth_error le n = some v →
    transl_expr_prop xi tprog sp e m le (.Eletvar n) v

def transl_expr_Eload_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (chunk : memory_chunk) (addr : addressing)
    (args : exprlist) (vargs : List val) (vaddr v : val),
    eval_exprlist xi (Genv.globalenv prog) sp e m le args vargs →
    transl_exprlist_prop xi tprog sp e m le args vargs →
    eval_addressing (Genv.globalenv prog) sp addr vargs = some vaddr →
    Mem.loadv chunk m vaddr = some v →
    transl_expr_prop xi tprog sp e m le (.Eload chunk addr args) v

def transl_expr_Eop_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (op : operation) (args : exprlist)
    (vargs : List val) (v : val),
    eval_exprlist xi (Genv.globalenv prog) sp e m le args vargs →
    transl_exprlist_prop xi tprog sp e m le args vargs →
    eval_operation (Genv.globalenv prog) sp op vargs m = some v →
    transl_expr_prop xi tprog sp e m le (.Eop op args) v

def transl_expr_Evar_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (id : ident) (v : val),
    PTree.get id e = some v →
    transl_expr_prop xi tprog sp e m le (.Evar id) v

def transl_expr_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : expr) (v : val),
    eval_expr xi (Genv.globalenv prog) sp e m le a v →
    transl_expr_prop xi tprog sp e m le a v

def transl_exprlist_Econs_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a1 : expr) (al : exprlist) (v1 : val)
    (vl : List val),
    eval_expr xi (Genv.globalenv prog) sp e m le a1 v1 →
    transl_expr_prop xi tprog sp e m le a1 v1 →
    eval_exprlist xi (Genv.globalenv prog) sp e m le al vl →
    transl_exprlist_prop xi tprog sp e m le al vl →
    transl_exprlist_prop xi tprog sp e m le (.Econs a1 al) (v1 :: vl)

def transl_exprlist_Enil_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv),
    transl_exprlist_prop xi tprog sp e m le .Enil []

def transl_exprlist_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (al : exprlist) (vl : List val),
    eval_exprlist xi (Genv.globalenv prog) sp e m le al vl →
    transl_exprlist_prop xi tprog sp e m le al vl

def transl_final_statesStatement : Prop :=
  ∀ (S : CminorSel.state) (R : RTL.state)
    (r : CompCert4Lean.Lib.Integers.int),
    match_states S R →
    CminorSel.final_state S r →
    RTL.final_state R r

def transl_initial_statesStatement : Prop :=
  ∀ (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ S, CminorSel.initial_state prog S →
      ∃ R, RTL.initial_state tprog R ∧ match_states S R

def transl_step_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (S1 : CminorSel.state) (t : trace) (S2 : CminorSel.state),
      CminorSel.step xi (Genv.globalenv prog) S1 t S2 →
      ∀ R1, match_states S1 R1 →
        ∃ R2,
          (plus (RTL.step xi) (Genv.globalenv tprog) R1 t R2 ∨
            (star (RTL.step xi) (Genv.globalenv tprog) R1 t R2 ∧
              lt_state S2 S1)) ∧
          match_states S2 R2

end CompCert4Lean.Backend.RTLgenproof
