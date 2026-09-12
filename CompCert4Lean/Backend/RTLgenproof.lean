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

private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

/-! ## Compilation-environment matching -/

structure map_wf (m : mapping) : Prop where
  mk_map_wf ::
  map_wf_inj : ∀ id1 id2 r,
    PTree.get id1 m.map_vars = some r →
    PTree.get id2 m.map_vars = some r → id1 = id2
  map_wf_disj : ∀ id r,
    PTree.get id m.map_vars = some r → r ∈ m.map_letvars → False

export map_wf (mk_map_wf map_wf_inj map_wf_disj)

structure match_env (map : mapping) (e : CompCert4Lean.Backend.Cminor.env)
    (le : letenv) (rs : regset) : Prop where
  mk_match_env ::
  me_vars : ∀ id v,
    PTree.get id e = some v →
    ∃ r, PTree.get id map.map_vars = some r ∧ Val.lessdef v (Regmap.get r rs)
  me_letvars : Val.lessdef_list le (map.map_letvars.map (fun r => Regmap.get r rs))

export match_env (mk_match_env me_vars me_letvars)

/-! ## Program matching -/

def match_prog (p : CminorSel.program) (tp : RTL.program) : Prop :=
  @match_program (fundef CminorSel.function) Unit (fundef RTL.function) Unit
    (Linker_fundef CminorSel.function) Linker_unit
    (fun _ f tf => RTLgen.transl_fundef f = .OK tf) Eq p tp

/-! ## Expression and exit simulation predicates -/

def transl_expr_prop
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (tprog : RTL.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : expr) (v : val) : Prop :=
  let tge := Genv.globalenv tprog
  ∀ tm cs f map pr ns nd rd rs dst,
    map_wf map →
    tr_expr f.fn_code map pr a ns nd rd dst →
    match_env map e le rs →
    Mem.extends m tm →
    ∃ rs' tm',
      star (RTL.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
        tge (RTL.State cs f sp ns rs tm) E0
          (RTL.State cs f sp nd rs' tm') ∧
      match_env map (CompCert4Lean.Backend.Cminor.set_optvar dst v e) le rs' ∧
      Val.lessdef v (Regmap.get rd rs') ∧
      (∀ r, r ∈ pr → Regmap.get r rs' = Regmap.get r rs) ∧
      Mem.extends m tm'

def transl_exprlist_prop
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (tprog : RTL.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (al : exprlist) (vl : List val) : Prop :=
  let tge := Genv.globalenv tprog
  ∀ tm cs f map pr ns nd rl rs,
    map_wf map →
    tr_exprlist f.fn_code map pr al ns nd rl →
    match_env map e le rs →
    Mem.extends m tm →
    ∃ rs' tm',
      star (RTL.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
        tge (RTL.State cs f sp ns rs tm) E0
          (RTL.State cs f sp nd rs' tm') ∧
      match_env map e le rs' ∧
      Val.lessdef_list vl (rl.map (fun r => Regmap.get r rs')) ∧
      (∀ r, r ∈ pr → Regmap.get r rs' = Regmap.get r rs) ∧
      Mem.extends m tm'

def transl_condexpr_prop
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (tprog : RTL.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : condexpr) (v : Bool) : Prop :=
  let tge := Genv.globalenv tprog
  ∀ tm cs f map pr ns ntrue nfalse rs,
    map_wf map →
    tr_condition f.fn_code map pr a ns ntrue nfalse →
    match_env map e le rs →
    Mem.extends m tm →
    ∃ rs' tm',
      plus (RTL.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
        tge (RTL.State cs f sp ns rs tm) E0
          (RTL.State cs f sp (if v then ntrue else nfalse) rs' tm') ∧
      match_env map e le rs' ∧
      (∀ r, r ∈ pr → Regmap.get r rs' = Regmap.get r rs) ∧
      Mem.extends m tm'

def transl_exitexpr_prop
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (tprog : RTL.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : exitexpr) (x : Nat) : Prop :=
  let tge := Genv.globalenv tprog
  ∀ tm cs f map ns nexits rs,
    map_wf map →
    tr_exitexpr f.fn_code map a ns nexits →
    match_env map e le rs →
    Mem.extends m tm →
    ∃ nd rs' tm',
      star (RTL.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
        tge (RTL.State cs f sp ns rs tm) E0
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

def lt_state_introStatement : Prop :=
  ∀ f1 s1 k1 sp1 e1 m1 f2 s2 k2 sp2 e2 m2,
    size_stmt s1 + size_cont k1 < size_stmt s2 + size_cont k2 ∨
      (size_stmt s1 + size_cont k1 = size_stmt s2 + size_cont k2 ∧
        size_stmt s1 < size_stmt s2) →
    lt_state (CminorSel.State f1 s1 k1 sp1 e1 m1)
      (CminorSel.State f2 s2 k2 sp2 e2 m2)

/-! ## Continuations and state matching -/

inductive tr_fun (tf : RTL.function) (map : mapping)
    (f : CminorSel.function) (ngoto : labelmap) (nret : node)
    (rret : Option reg) : Prop where
  | tr_fun_intro (nentry : node) (r : reg)
      (hret : rret = ret_reg f.fn_sig r)
      (hstmt : tr_stmt tf.fn_code map f.fn_body nentry nret [] ngoto nret rret)
      (hstack : tf.fn_stacksize = f.fn_stackspace) :
      tr_fun tf map f ngoto nret rret

export tr_fun (tr_fun_intro)

mutual
  inductive tr_cont : RTL.code → mapping → CminorSel.cont → node → List node →
      labelmap → node → Option reg → List RTL.stackframe → Prop where
    | tr_Kseq (c : RTL.code) (map : mapping) (s : stmt) (k : cont)
        (nd : node) (nexits : List node) (ngoto : labelmap) (nret : node)
        (rret : Option reg) (cs : List RTL.stackframe) (n : node)
        (hstmt : tr_stmt c map s nd n nexits ngoto nret rret)
        (hk : tr_cont c map k n nexits ngoto nret rret cs) :
        tr_cont c map (.Kseq s k) nd nexits ngoto nret rret cs
    | tr_Kblock (c : RTL.code) (map : mapping) (k : cont) (nd : node)
        (nexits : List node) (ngoto : labelmap) (nret : node)
        (rret : Option reg) (cs : List RTL.stackframe)
        (hk : tr_cont c map k nd nexits ngoto nret rret cs) :
        tr_cont c map (.Kblock k) nd (nd :: nexits) ngoto nret rret cs
    | tr_Kstop (c : RTL.code) (map : mapping) (ngoto : labelmap) (nret : node)
        (rret : Option reg) (cs : List RTL.stackframe)
        (hcode : PTree.get nret c = some (.Ireturn rret))
        (hs : match_stacks .Kstop cs) :
        tr_cont c map .Kstop nret [] ngoto nret rret cs
    | tr_Kcall (c : RTL.code) (map : mapping) (optid : Option ident)
        (f : CminorSel.function) (sp : val) (e : CompCert4Lean.Backend.Cminor.env)
        (k : cont) (ngoto : labelmap) (nret : node) (rret : Option reg)
        (cs : List RTL.stackframe)
        (hcode : PTree.get nret c = some (.Ireturn rret))
        (hs : match_stacks (.Kcall optid f sp e k) cs) :
        tr_cont c map (.Kcall optid f sp e k) nret [] ngoto nret rret cs

  inductive match_stacks : CminorSel.cont → List RTL.stackframe → Prop where
    | match_stacks_stop : match_stacks .Kstop []
    | match_stacks_call (optid : Option ident) (f : CminorSel.function)
        (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (k : cont)
        (r : reg) (tf : RTL.function) (n : node) (rs : regset)
        (cs : List RTL.stackframe) (map : mapping) (nexits : List node)
        (ngoto : labelmap) (nret : node) (rret : Option reg)
        (mwf : map_wf map) (tfrel : tr_fun tf map f ngoto nret rret)
        (me : match_env map e [] rs)
        (rok : reg_map_ok map r optid)
        (tc : tr_cont tf.fn_code map k n nexits ngoto nret rret cs) :
        match_stacks (.Kcall optid f sp e k)
          (RTL.Stackframe r tf sp n rs :: cs)
end

export tr_cont (tr_Kseq tr_Kblock tr_Kstop tr_Kcall)
export match_stacks (match_stacks_stop match_stacks_call)

inductive match_states : CminorSel.state → RTL.state → Prop where
  | match_state (f : CminorSel.function) (s : stmt) (k : cont) (sp : val)
      (e : CompCert4Lean.Backend.Cminor.env) (m tm : mem)
      (cs : List RTL.stackframe) (tf : RTL.function) (ns : node) (rs : regset)
      (map : mapping) (ncont : node) (nexits : List node) (ngoto : labelmap)
      (nret : node) (rret : Option reg)
      (mwf : map_wf map)
      (ts : tr_stmt tf.fn_code map s ns ncont nexits ngoto nret rret)
      (tfrel : tr_fun tf map f ngoto nret rret)
      (tc : tr_cont tf.fn_code map k ncont nexits ngoto nret rret cs)
      (me : match_env map e [] rs) (mext : Mem.extends m tm) :
      match_states (.State f s k sp e m) (RTL.State cs tf sp ns rs tm)
  | match_callstate (f : CminorSel.fundef) (args targs : List val)
      (k : cont) (m tm : mem) (cs : List RTL.stackframe)
      (tf : RTL.fundef)
      (htrans : RTLgen.transl_fundef f = .OK tf)
      (hs : match_stacks k cs) (ld : Val.lessdef_list args targs)
      (mext : Mem.extends m tm) :
      match_states (.Callstate f args k m) (RTL.Callstate cs tf targs tm)
  | match_returnstate (v tv : val) (k : cont) (m tm : mem)
      (cs : List RTL.stackframe) (hs : match_stacks k cs)
      (ld : Val.lessdef v tv) (mext : Mem.extends m tm) :
      match_states (.Returnstate v k m) (RTL.Returnstate cs tv tm)

export match_states (match_state match_callstate match_returnstate)

/-! The selected Rocq proofs consume this generated induction scheme.  Keep its
    source-named proposition and constructor-case order explicit; construction
    of the proof term remains assigned to proof grinding under DMC-003. -/
def tr_cont_ind : Prop :=
  ∀ (P : RTL.code → mapping → CminorSel.cont → node → List node → labelmap →
      node → Option reg → List RTL.stackframe → Prop),
    (∀ (c : RTL.code) (map : mapping) (s : stmt) (k : cont)
      (nd : node) (nexits : List node) (ngoto : labelmap) (nret : node)
      (rret : Option reg) (cs : List RTL.stackframe) (n : node),
      tr_stmt c map s nd n nexits ngoto nret rret →
      tr_cont c map k n nexits ngoto nret rret cs →
      P c map k n nexits ngoto nret rret cs →
      P c map (.Kseq s k) nd nexits ngoto nret rret cs) →
    (∀ (c : RTL.code) (map : mapping) (k : cont) (nd : node)
      (nexits : List node) (ngoto : labelmap) (nret : node)
      (rret : Option reg) (cs : List RTL.stackframe),
      tr_cont c map k nd nexits ngoto nret rret cs →
      P c map k nd nexits ngoto nret rret cs →
      P c map (.Kblock k) nd (nd :: nexits) ngoto nret rret cs) →
    (∀ (c : RTL.code) (map : mapping) (ngoto : labelmap) (nret : node)
      (rret : Option reg) (cs : List RTL.stackframe),
      PTree.get nret c = some (.Ireturn rret) →
      match_stacks .Kstop cs →
      P c map .Kstop nret [] ngoto nret rret cs) →
    (∀ (c : RTL.code) (map : mapping) (optid : Option ident)
      (f : CminorSel.function) (sp : val) (e : Cminor.env) (k : cont)
      (ngoto : labelmap) (nret : node) (rret : Option reg)
      (cs : List RTL.stackframe),
      PTree.get nret c = some (.Ireturn rret) →
      match_stacks (.Kcall optid f sp e k) cs →
      P c map (.Kcall optid f sp e k) nret [] ngoto nret rret cs) →
    ∀ (c : RTL.code) (m : mapping) (c0 : cont) (n : node)
      (l : List node) (l0 : labelmap) (n0 : node) (o : Option reg)
      (l1 : List RTL.stackframe),
      tr_cont c m c0 n l l0 n0 o l1 → P c m c0 n l l0 n0 o l1

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

def eval_exprlist_appendStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem) (le : letenv)
    (al1 : List expr) (vl1 : List val) (al2 : List expr) (vl2 : List val),
    CminorSel.eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le
      (RTLgen.exprlist_of_expr_list al1) vl1 →
    CminorSel.eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le
      (RTLgen.exprlist_of_expr_list al2) vl2 →
    CminorSel.eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le
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

def invert_eval_builtin_argStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem) (a : builtin_arg expr) (v : val),
    CminorSel.eval_builtin_arg
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m a v →
    ∃ vl,
      CminorSel.eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m []
        (RTLgen.exprlist_of_expr_list (params_of_builtin_arg a)) vl ∧
      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun v => v) sp m
          (convert_builtin_arg a vl).1 v ∧
      (∀ vl',
        convert_builtin_arg a (vl ++ vl') =
          ((convert_builtin_arg a vl).1, vl'))

def invert_eval_builtin_argsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (sp : val)
    (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (al : List (builtin_arg expr)) (vl : List val),
    list_forall2 (CminorSel.eval_builtin_arg
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m) al vl →
    ∃ vl',
      CminorSel.eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m []
        (RTLgen.exprlist_of_expr_list (params_of_builtin_args al)) vl' ∧
      eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun v => v) sp m
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
  ∀ (params : List ident) (s0 : RTLgen.state) (rparams : List reg)
    (map1 : mapping) (s1 : RTLgen.state) (i1 : RTLgen.state_incr s0 s1)
    (vars : List ident) (rvars : List reg) (map2 : mapping)
    (s2 : RTLgen.state) (i2 : RTLgen.state_incr s1 s2)
    (vparams tvparams : List val),
    add_vars RTLgen.init_mapping params s0 = .OK (rparams, map1) s1 i1 →
    add_vars map1 vars s1 = .OK (rvars, map2) s2 i2 →
    Val.lessdef_list vparams tvparams →
    match_env map2
      (CompCert4Lean.Backend.Cminor.set_locals vars
        (CompCert4Lean.Backend.Cminor.set_params vparams params))
      [] (init_regs tvparams rparams)

def match_set_localsStatement : Prop :=
  ∀ (map1 : mapping) (s1 : RTLgen.state),
    map_wf map1 →
    ∀ (il : List ident) (rl : List reg) (map2 : mapping) (s2 : RTLgen.state)
      (e : CompCert4Lean.Backend.Cminor.env) (le : letenv) (rs : regset)
      (i : RTLgen.state_incr s1 s2),
    match_env map1 e le rs →
    (∀ r, reg_fresh r s1 → Regmap.get r rs = Vundef) →
    add_vars map1 il s1 = .OK (rl, map2) s2 i →
    match_env map2 (CompCert4Lean.Backend.Cminor.set_locals il e) le rs

def match_set_params_init_regsStatement : Prop :=
  ∀ (il : List ident) (rl : List reg) (s1 : RTLgen.state)
    (map2 : mapping) (s2 : RTLgen.state) (vl tvl : List val)
    (i : RTLgen.state_incr s1 s2),
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

def tr_move_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tprog : RTL.program) (r1 : reg) (ns : node)
    (r2 : reg) (nd : node) (cs : List RTL.stackframe)
    (f : RTL.function) (sp : val) (rs : regset) (m : mem),
    tr_move f.fn_code ns r1 nd r2 →
    ∃ rs',
      star (RTL.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
        (Genv.globalenv tprog)
        (RTL.State cs f sp ns rs m) E0
        (RTL.State cs f sp nd rs' m) ∧
      Regmap.get r2 rs' = Regmap.get r1 rs ∧
      (∀ r, r ≠ r2 → Regmap.get r rs' = Regmap.get r rs)

def transf_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    forward_simulation
      (CminorSel.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog)
      (RTL.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tprog)

def transf_program_matchStatement : Prop :=
  ∀ (p : CminorSel.program) (tp : RTL.program),
    RTLgen.transl_program p = .OK tp → match_prog p tp
def transl_condexpr_CEcond_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (cond : condition) (al : exprlist) (vl : List val)
    (vb : Bool),
    eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le al vl →
    transl_exprlist_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le al vl →
    eval_condition cond vl m = some vb →
    transl_condexpr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.CEcond cond al) vb

def transl_condexpr_CEcondition_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a b c : condexpr) (va : Bool) (v : Bool),
    eval_condexpr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le a va →
    transl_condexpr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le a va →
    eval_condexpr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le (if va then b else c) v →
    transl_condexpr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (if va then b else c) v →
    transl_condexpr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.CEcondition a b c) v

def transl_condexpr_CElet_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : expr) (b : condexpr) (v1 : val) (v2 : Bool),
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le a v1 →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le a v1 →
    eval_condexpr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m (v1 :: le) b v2 →
    transl_condexpr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m (v1 :: le) b v2 →
    transl_condexpr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.CElet a b) v2

def transl_condexpr_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : condexpr) (v : Bool),
    eval_condexpr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le a v →
    transl_condexpr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le a v

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

def transl_exitexpr_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : exitexpr) (x : Nat),
    eval_exitexpr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le a x →
    transl_exitexpr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le a x

def transl_expr_Ebuiltin_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (ef : external_function) (al : exprlist)
    (vl : List val) (v : val),
    eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le al vl →
    transl_exprlist_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le al vl →
    external_call
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ef (Genv.to_senv (Genv.globalenv prog)) vl m E0 v m →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.Ebuiltin ef al) v

def transl_expr_Econdition_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : condexpr) (ifso ifnot : expr)
    (va : Bool) (v : val),
    eval_condexpr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le a va →
    transl_condexpr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le a va →
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le (if va then ifso else ifnot) v →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (if va then ifso else ifnot) v →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.Econdition a ifso ifnot) v

def transl_expr_Eexternal_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (id : ident) (sg : signature) (al : exprlist)
    (b : block) (ef : external_function) (vl : List val) (v : val),
    Genv.find_symbol (Genv.globalenv prog) id = some b →
    Genv.find_funct_ptr (Genv.globalenv prog) b = some (.External ef) →
    ef_sig ef = sg →
    eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le al vl →
    transl_exprlist_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le al vl →
    external_call
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ef (Genv.to_senv (Genv.globalenv prog)) vl m E0 v m →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.Eexternal id sg al) v

def transl_expr_Elet_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a1 a2 : expr) (v1 v2 : val),
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le a1 v1 →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le a1 v1 →
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m (v1 :: le) a2 v2 →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m (v1 :: le) a2 v2 →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.Elet a1 a2) v2

def transl_expr_Eletvar_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : List val) (n : Nat) (v : val),
    nth_error le n = some v →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.Eletvar n) v

def transl_expr_Eload_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (chunk : memory_chunk) (addr : addressing)
    (args : exprlist) (vargs : List val) (vaddr v : val),
    eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le args vargs →
    transl_exprlist_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le args vargs →
    eval_addressing (Genv.globalenv prog) sp addr vargs = some vaddr →
    Mem.loadv chunk m vaddr = some v →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.Eload chunk addr args) v

def transl_expr_Eop_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (op : operation) (args : exprlist)
    (vargs : List val) (v : val),
    eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le args vargs →
    transl_exprlist_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le args vargs →
    eval_operation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (Genv.globalenv prog) sp op vargs m = some v →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.Eop op args) v

def transl_expr_Evar_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (id : ident) (v : val),
    PTree.get id e = some v →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.Evar id) v

def transl_expr_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : expr) (v : val),
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le a v →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le a v

def transl_exprlist_Econs_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a1 : expr) (al : exprlist) (v1 : val)
    (vl : List val),
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le a1 v1 →
    transl_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le a1 v1 →
    eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le al vl →
    transl_exprlist_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le al vl →
    transl_exprlist_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le (.Econs a1 al) (v1 :: vl)

def transl_exprlist_Enil_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tprog : RTL.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv),
    transl_exprlist_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le .Enil []

def transl_exprlist_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (al : exprlist) (vl : List val),
    eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le al vl →
    transl_exprlist_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog sp e m le al vl

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

def transl_step_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorSel.program) (tprog : RTL.program),
    match_prog prog tprog →
    ∀ (S1 : CminorSel.state) (t : trace) (S2 : CminorSel.state),
      CminorSel.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) S1 t S2 →
      ∀ R1, match_states S1 R1 →
        ∃ R2,
          (plus (RTL.step
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi)
            (Genv.globalenv tprog) R1 t R2 ∨
            (star (RTL.step
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) xi)
              (Genv.globalenv tprog) R1 t R2 ∧
              lt_state S2 S1)) ∧
          match_states S2 R2

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

private theorem transfGlobdefsMatch
    (p : CminorSel.program)
    (l : List (ident × globdef (fundef CminorSel.function) Unit))
    (l' : List (ident × globdef (fundef RTL.function) Unit))
    (h : transf_globdefs
      (fun _ f => RTLgen.transl_fundef f)
      (fun _ v => .OK v) l = .OK l') :
    list_forall2
      (@match_ident_globdef
        CminorSel.program (fundef CminorSel.function) Unit
          (fundef RTL.function) Unit
          (@Linker_prog (fundef CminorSel.function) Unit
            (@Linker_fundef CminorSel.function) Linker_unit)
        (fun _ f tf => RTLgen.transl_fundef f = .OK tf) Eq p) l l' := by
  induction l generalizing l' with
  | nil =>
      simp [transf_globdefs] at h
      cases h
      exact list_forall2_nil _
  | cons hd tl ih =>
      cases hd with
      | mk id gd =>
          cases gd with
          | Gfun f =>
              cases htf : RTLgen.transl_fundef f with
              | Error msg => simp [transf_globdefs, htf] at h
              | OK tf =>
                  cases htl : transf_globdefs
                      (fun _ f => RTLgen.transl_fundef f)
                      (fun _ v => .OK v) tl with
                  | Error msg => simp [transf_globdefs, htf, htl] at h
                  | OK tlt =>
                      simp [transf_globdefs, htf, htl] at h
                      cases h
                      apply list_forall2.cons
                      · constructor
                        · rfl
                        · exact @match_globdef_fun
                            CminorSel.program (fundef CminorSel.function) Unit
                            (fundef RTL.function) Unit
                            (@Linker_prog (fundef CminorSel.function) Unit
                              (@Linker_fundef CminorSel.function) Linker_unit)
                            (fun _ f tf => RTLgen.transl_fundef f = .OK tf)
                            Eq p p f tf
                            (@Linker.linkorder_refl CminorSel.program
                              (@Linker_prog (fundef CminorSel.function) Unit
                                (@Linker_fundef CminorSel.function) Linker_unit) p)
                            htf
                      · exact ih tlt htl
          | Gvar v =>
              cases htl : transf_globdefs
                  (fun _ f => RTLgen.transl_fundef f)
                  (fun _ v => .OK v) tl with
              | Error msg => simp [transf_globdefs, transf_globvar, htl] at h
              | OK tlt =>
                  simp [transf_globdefs, transf_globvar, htl] at h
                  cases h
                  apply list_forall2.cons
                  · constructor
                    · rfl
                    · exact @match_globdef_var
                        CminorSel.program (fundef CminorSel.function) Unit
                        (fundef RTL.function) Unit
                        (@Linker_prog (fundef CminorSel.function) Unit
                          (@Linker_fundef CminorSel.function) Linker_unit)
                        (fun _ f tf => RTLgen.transl_fundef f = .OK tf)
                        Eq p v
                        { gvar_info := v.gvar_info
                          gvar_init := v.gvar_init
                          gvar_readonly := v.gvar_readonly
                          gvar_volatile := v.gvar_volatile }
                        (match_globvar_intro Eq v.gvar_info v.gvar_info
                          v.gvar_init v.gvar_readonly v.gvar_volatile rfl)
                  · exact ih tlt htl

theorem transf_program_match : transf_program_matchStatement := by
  intro p tp h
  unfold RTLgen.transl_program at h
  unfold match_prog match_program
  cases hdefs : transf_globdefs
      (fun _ f => RTLgen.transl_fundef f)
      (fun _ v => .OK v) p.prog_defs with
  | Error msg => simp [transform_partial_program, transform_partial_program2, hdefs] at h
  | OK defs =>
      simp [transform_partial_program, transform_partial_program2, hdefs] at h
      cases h
      refine ⟨transfGlobdefsMatch p p.prog_defs defs hdefs, ?_, ?_⟩
      · rfl
      · rfl

end CompCert4Lean.Backend.RTLgenproof
namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem rtlgenproof_plt_succ (p : positive) :
    Plt p (PArith.BinPos.Pos.succ p) := by
  unfold Plt
  induction p with
  | xH =>
    change 1 < 2
    omega
  | xI p ih =>
    change PArith.BinPos.Pos.to_nat p <
      PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p) at ih
    change 2 * PArith.BinPos.Pos.to_nat p + 1 <
      2 * PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p)
    omega
  | xO p ih =>
    change 2 * PArith.BinPos.Pos.to_nat p < 2 * PArith.BinPos.Pos.to_nat p + 1
    omega

private theorem rtlgenproof_add_var_valid
    (s1 s2 : RTLgen.state) (map mapPrime : RTLgen.mapping) (name : ident) (r : reg)
    (i : RTLgen.state_incr s1 s2) :
    RTLgen.add_var map name s1 = .OK (r, mapPrime) s2 i →
    map_valid map s1 → map_valid mapPrime s2 := by
  intro h hvalid
  cases map with
  | mk mapVars mapLetvars =>
    unfold PTree.t at mapVars
    unfold CompCert4Lean.Common.AST.ident at name
    unfold CompCert4Lean.Backend.Registers.reg at *
    change RTLgen.bind RTLgen.new_reg
      (fun r => RTLgen.ret (r,
        ({ map_vars := PTree.set name r mapVars, map_letvars := mapLetvars } : RTLgen.mapping)))
      s1 = RTLgen.res.OK (r, mapPrime) s2 i at h
    dsimp [RTLgen.bind] at h
    rw [show RTLgen.new_reg s1 = .OK s1.st_nextreg _ _ from rfl] at h
    simp [RTLgen.ret] at h
    cases h
    unfold map_valid at hvalid ⊢
    intro r hin
    unfold CompCert4Lean.Backend.Registers.reg at r
    unfold reg_in_map at hin
    change Plt r (PArith.BinPos.Pos.succ s1.st_nextreg)
    rcases hin with ⟨id, hget⟩ | hmem
    · change PTree.get id (PTree.set name s1.st_nextreg mapVars) = some r at hget
      rw [PTree.getSet_equation] at hget
      by_cases hid : id = name
      · subst id
        simp at hget
        cases hget
        exact rtlgenproof_plt_succ _
      · simp [hid] at hget
        exact Nat.lt_trans (hvalid r (Or.inl ⟨id, hget⟩)) (rtlgenproof_plt_succ _)
    · exact Nat.lt_trans (hvalid r (Or.inr hmem)) (rtlgenproof_plt_succ _)

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem init_mapping_wf : init_mapping_wfStatement := by
  constructor
  · intro id1 id2 r h1 h2
    simp [RTLgen.init_mapping, PTree.get, PTree.empty] at h1
  · intro id r h1 h2
    simp [RTLgen.init_mapping, PTree.get, PTree.empty] at h1

theorem add_var_wf : add_var_wfStatement := by
  intro s1 s2 map name r mapPrime i h hwf hvalid
  cases map with
  | mk mapVars mapLetvars =>
    unfold PTree.t at mapVars
    unfold CompCert4Lean.Common.AST.ident at name
    unfold CompCert4Lean.Backend.Registers.reg at *
    change RTLgen.bind RTLgen.new_reg
      (fun r => RTLgen.ret (r,
        ({ map_vars := PTree.set name r mapVars, map_letvars := mapLetvars } : RTLgen.mapping)))
      s1 = RTLgen.res.OK (r, mapPrime) s2 i at h
    dsimp [RTLgen.bind] at h
    rw [show RTLgen.new_reg s1 = .OK s1.st_nextreg _ _ from rfl] at h
    simp [RTLgen.ret] at h
    cases h
    have hfresh : ¬ reg_in_map { map_vars := mapVars, map_letvars := mapLetvars }
        s1.st_nextreg := by
      intro hin
      exact Nat.lt_irrefl _ (hvalid _ hin)
    constructor
    · intro id1 id2 r h1 h2
      unfold CompCert4Lean.Backend.Registers.reg at r
      change PTree.get id1 (PTree.set name s1.st_nextreg mapVars) = some r at h1
      change PTree.get id2 (PTree.set name s1.st_nextreg mapVars) = some r at h2
      rw [PTree.getSet_equation] at h1 h2
      by_cases hid1 : id1 = name
      · by_cases hid2 : id2 = name
        · exact hid1.trans hid2.symm
        · simp [hid1] at h1
          cases h1
          simp [hid2] at h2
          exact False.elim (hfresh (Or.inl ⟨id2, h2⟩))
      · by_cases hid2 : id2 = name
        · simp [hid1] at h1
          simp [hid2] at h2
          cases h2
          exact False.elim (hfresh (Or.inl ⟨id1, h1⟩))
        · simp [hid1] at h1
          simp [hid2] at h2
          exact hwf.map_wf_inj id1 id2 r h1 h2
    · intro id r hget hmem
      unfold CompCert4Lean.Backend.Registers.reg at r
      change PTree.get id (PTree.set name s1.st_nextreg mapVars) = some r at hget
      change r ∈ mapLetvars at hmem
      rw [PTree.getSet_equation] at hget
      by_cases hid : id = name
      · subst id
        simp at hget
        subst r
        exact hfresh (Or.inr hmem)
      · simp [hid] at hget
        exact hwf.map_wf_disj id r hget hmem

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Lib.Coqlib

theorem lt_state_intro : lt_state_introStatement := by
  intro f1 s1 k1 sp1 e1 m1 f2 s2 k2 sp2 e2 m2 h
  unfold lt_state
  rcases h with h | ⟨h1, h2⟩
  · change lex_ord Nat.lt Nat.lt (size_stmt s1 + size_cont k1, size_stmt s1)
      (size_stmt s2 + size_cont k2, size_stmt s2)
    exact lex_ord.left _ _ _ _ _ _ h
  · change lex_ord Nat.lt Nat.lt (size_stmt s1 + size_cont k1, size_stmt s1)
      (size_stmt s2 + size_cont k2, size_stmt s2)
    rw [h1]
    exact lex_ord.right _ _ _ _ _ h2

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem rtlgenproof_add_vars_wf_valid
    (names : List ident) (s1 s2 : RTLgen.state) (map mapPrime : RTLgen.mapping)
    (rl : List reg) (i : RTLgen.state_incr s1 s2) :
    RTLgen.add_vars map names s1 = .OK (rl, mapPrime) s2 i →
    map_wf map → map_valid map s1 → map_wf mapPrime ∧ map_valid mapPrime s2 := by
  induction names generalizing s1 s2 map mapPrime rl i with
  | nil =>
    intro h hwf hvalid
    change RTLgen.ret ([], map) s1 = .OK (rl, mapPrime) s2 i at h
    simp [RTLgen.ret] at h
    rcases h with ⟨⟨hrl, hmap⟩, hs⟩
    cases hrl
    cases hmap
    cases hs
    exact ⟨hwf, hvalid⟩
  | cons name names ih =>
    intro h hwf hvalid
    change RTLgen.bind (RTLgen.add_vars map names)
      (fun x => RTLgen.bind (RTLgen.add_var x.2 name)
        (fun y => RTLgen.ret (y.1 :: x.1, y.2))) s1 = .OK (rl, mapPrime) s2 i at h
    cases hrec : RTLgen.add_vars map names s1 with
    | Error msg =>
      simp [RTLgen.bind, hrec] at h
    | OK x sm hincr =>
      cases x with
      | mk rlmid mapmid =>
        simp [RTLgen.bind, hrec] at h
        cases hvar : RTLgen.add_var mapmid name sm with
        | Error msg =>
          simp [hvar] at h
        | OK x sn hinc =>
          cases x with
          | mk rnew mapnew =>
            simp [RTLgen.ret, hvar] at h
            rcases h with ⟨⟨hrl, hmap⟩, hs⟩
            have hrecwf := ih (s1 := s1) (s2 := sm) (map := map)
              (mapPrime := mapmid) (rl := rlmid) (i := hincr) hrec hwf hvalid
            constructor
            · simpa only [hmap, hs] using
                (add_var_wf sm sn mapmid name rnew mapnew hinc hvar hrecwf.1 hrecwf.2)
            · simpa only [hmap, hs] using
                (rtlgenproof_add_var_valid (s1 := sm) (s2 := sn) (map := mapmid)
                  (mapPrime := mapnew) (name := name) (r := rnew) (i := hinc) hvar hrecwf.2)

theorem add_vars_wf : add_vars_wfStatement := by
  intro names s1 s2 map mapPrime rl i h hwf hvalid
  exact (rtlgenproof_add_vars_wf_valid names s1 s2 map mapPrime rl i h hwf hvalid).1

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

private theorem rtlgenproof_lessdef_list_nth
    (le : List val) (rl : List reg) (rs : Regmap.t val) (idx : Nat) (v : val) (r : reg) :
    Val.lessdef_list le (rl.map (fun r => Regmap.get r rs)) →
    nth_error le idx = some v → nth_error rl idx = some r →
    Val.lessdef v (Regmap.get r rs) := by
  induction idx generalizing le rl v r with
  | zero =>
    intro hless hle hrl
    cases le with
    | nil => simp [nth_error] at hle
    | cons v' le =>
      cases rl with
      | nil => simp [nth_error] at hrl
      | cons r' rl =>
        simp [nth_error] at hle hrl
        cases hle
        cases hrl
        cases hless with
        | lessdef_list_cons v₁ v₂ vl₁ vl₂ hhead htail => exact hhead
  | succ idx ih =>
    intro hless hle hrl
    cases le with
    | nil => simp [nth_error] at hle
    | cons v' le =>
      cases rl with
      | nil => simp [nth_error] at hrl
      | cons r' rl =>
        cases hless with
        | lessdef_list_cons v₁ v₂ vl₁ vl₂ hhead htail =>
          apply ih (le := le) (rl := rl) (v := v) (r := r) htail
          · simpa [nth_error] using hle
          · simpa [nth_error] using hrl

private theorem rtlgenproof_lessdef_list_invariant
    (le : List val) (rl : List reg) (rs rs' : Regmap.t val)
    (hless : Val.lessdef_list le (rl.map (fun r => Regmap.get r rs)))
    (hstable : ∀ r, r ∈ rl → Regmap.get r rs' = Regmap.get r rs) :
    Val.lessdef_list le (rl.map (fun r => Regmap.get r rs')) := by
  induction rl generalizing le with
  | nil =>
    cases hless
    exact Val.lessdef_list_nil
  | cons r rl ih =>
    cases le with
    | nil => cases hless
    | cons v le =>
      cases hless with
      | lessdef_list_cons v₁ v₂ vl₁ vl₂ hhead htail =>
        refine Val.lessdef_list_cons _ _ _ _ ?_ ?_
        · change Val.lessdef v (Regmap.get r rs')
          rw [hstable r (by simp)]
          exact hhead
        · exact ih le htail (fun r hr => hstable r (by simp [hr]))

theorem add_letvar_wf : add_letvar_wfStatement := by
  intro map r hwf hfresh
  constructor
  · intro id1 id2 r' h1 h2
    change PTree.get id1 map.map_vars = some r' at h1
    change PTree.get id2 map.map_vars = some r' at h2
    exact hwf.map_wf_inj id1 id2 r' h1 h2
  · intro id r' hget hmem
    change PTree.get id map.map_vars = some r' at hget
    simp only [RTLgen.add_letvar, List.mem_cons] at hmem
    rcases hmem with h | h
    · subst r'
      exact hfresh (Or.inl ⟨id, hget⟩)
    · exact hwf.map_wf_disj id r' hget h

theorem match_env_find_var : match_env_find_varStatement := by
  intro map e le rs id v r hmatch henv hmap
  rcases hmatch.me_vars id v henv with ⟨r', hget, hless⟩
  rw [hmap] at hget
  cases hget
  exact hless

theorem match_env_find_letvar : match_env_find_letvarStatement := by
  intro map e le rs idx v r hmatch hle hmap
  exact rtlgenproof_lessdef_list_nth (le := le) (rl := map.map_letvars)
    (rs := rs) idx v r hmatch.me_letvars hle hmap

theorem match_env_invariant : match_env_invariantStatement := by
  intro map e le rs rs' hmatch hstable
  constructor
  · intro id v henv
    rcases hmatch.me_vars id v henv with ⟨r, hget, hless⟩
    refine ⟨r, hget, ?_⟩
    rw [hstable r (Or.inl ⟨id, hget⟩)]
    exact hless
  · exact rtlgenproof_lessdef_list_invariant (le := le) (rl := map.map_letvars)
      (rs := rs) (rs' := rs') hmatch.me_letvars (fun r hr => hstable r (Or.inr hr))

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

private theorem rtlgenproof_lessdef_list_invariant_update
    (le : List val) (rl : List reg) (rs rs' : Regmap.t val)
    (hless : Val.lessdef_list le (rl.map (fun r => Regmap.get r rs)))
    (hstable : ∀ r, r ∈ rl → Regmap.get r rs' = Regmap.get r rs) :
    Val.lessdef_list le (rl.map (fun r => Regmap.get r rs')) := by
  induction rl generalizing le with
  | nil =>
      cases hless
      exact Val.lessdef_list_nil
  | cons r rl ih =>
      cases le with
      | nil => cases hless
      | cons v le =>
          cases hless with
          | lessdef_list_cons _ _ _ _ hhead htail =>
              refine Val.lessdef_list_cons _ _ _ _ ?_ ?_
              · change Val.lessdef v (Regmap.get r rs')
                rw [hstable r (by simp)]
                exact hhead
              · exact ih le htail (fun r hr => hstable r (by simp [hr]))

private theorem rtlgenproof_match_env_invariant_update
    (map : RTLgen.mapping) (e : CompCert4Lean.Backend.Cminor.env) (le : letenv)
    (rs rs' : RTL.regset) : match_env map e le rs →
    (∀ r, reg_in_map map r → Regmap.get r rs' = Regmap.get r rs) →
    match_env map e le rs' := by
  intro hmatch hstable
  constructor
  · intro id v henv
    rcases hmatch.me_vars id v henv with ⟨r, hget, hless⟩
    refine ⟨r, hget, ?_⟩
    rw [hstable r (Or.inl ⟨id, hget⟩)]
    exact hless
  · exact rtlgenproof_lessdef_list_invariant_update (le := le) (rl := map.map_letvars)
      (rs := rs) (rs' := rs') hmatch.me_letvars (fun r hr => hstable r (Or.inr hr))

theorem match_env_update_temp : match_env_update_tempStatement := by
  intro map e le rs r v hmatch hfresh
  apply rtlgenproof_match_env_invariant_update map e le rs (Regmap.set r v rs) hmatch
  intro r' hin
  have hne : r' ≠ r := by
    intro heq
    subst r'
    exact hfresh hin
  exact Regmap.gso_proof val r' r v rs hne

theorem match_env_update_var : match_env_update_varStatement := by
  intro map e le rs id r v tv hless hwf hmap hmatch
  constructor
  · intro id' v' henv
    unfold CompCert4Lean.Common.AST.ident at id
    unfold CompCert4Lean.Backend.Cminor.env at e
    unfold PTree.t at e
    change PTree.get id' (PTree.set id v e) = some v' at henv
    rw [PTree.getSet_equation] at henv
    by_cases hid : id' = id
    · subst id'
      simp at henv
      cases henv
      refine ⟨r, hmap, ?_⟩
      rw [Regmap.gss_proof val r tv rs]
      exact hless
    · simp [hid] at henv
      rcases hmatch.me_vars id' v' henv with ⟨r', hget, hless'⟩
      refine ⟨r', hget, ?_⟩
      have hne : r' ≠ r := by
        intro heq
        subst r'
        exact hid (hwf.map_wf_inj id' id r hget hmap)
      rw [Regmap.gso_proof val r' r tv rs hne]
      exact hless'
  · apply rtlgenproof_lessdef_list_invariant_update (le := le) (rl := map.map_letvars)
      (rs := rs) (rs' := Regmap.set r tv rs) hmatch.me_letvars
    intro r' hmem
    have hne : r' ≠ r := by
      intro heq
      subst r'
      exact hwf.map_wf_disj id r hmap hmem
    exact Regmap.gso_proof val r' r tv rs hne

theorem match_env_update_dest : match_env_update_destStatement := by
  intro map e le rs dst r v tv hless hwf hrok hmatch
  cases hrok with
  | reg_map_ok_novar hfresh =>
      exact match_env_update_temp map e le rs r tv hmatch hfresh
  | reg_map_ok_somevar id hmap =>
      exact match_env_update_var map e le rs id r v tv hless hwf hmap hmatch

theorem match_env_update_res : match_env_update_resStatement := by
  intro map res v e le tres tv rs hless hwf htr hmatch
  cases htr with
  | tr_builtin_res_var id r hmap =>
      exact match_env_update_var map e le rs id r v tv hless hwf hmap hmatch
  | tr_builtin_res_none =>
      exact hmatch
  | tr_builtin_res_fresh r hfresh =>
      exact match_env_update_temp map e le rs r tv hmatch hfresh

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

theorem match_env_bind_letvar : match_env_bind_letvarStatement := by
  intro map e le rs r v hmatch hless
  constructor
  · exact hmatch.me_vars
  · exact Val.lessdef_list_cons v (Regmap.get r rs) le
      (map.map_letvars.map (fun r => Regmap.get r rs)) hless hmatch.me_letvars

theorem match_env_unbind_letvar : match_env_unbind_letvarStatement := by
  intro map e le rs r v hmatch
  constructor
  · exact hmatch.me_vars
  · cases hmatch.me_letvars with
    | lessdef_list_cons _ _ _ _ _ htail => exact htail

theorem match_env_empty : match_env_emptyStatement := by
  intro map hmap
  constructor
  · intro id v henv
    simp [PTree.get, PTree.empty] at henv
  · simpa [hmap] using (Val.lessdef_list_nil : Val.lessdef_list [] [])

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

theorem match_set_locals : match_set_localsStatement := by
  intro map1 s1 hmap il rl map2 s2 e le rs i hmatch hfresh hadd
  induction il generalizing map1 s1 rl map2 s2 i with
  | nil =>
      change RTLgen.ret ([], map1) s1 = .OK (rl, map2) s2 i at hadd
      simp [RTLgen.ret] at hadd
      rcases hadd with ⟨⟨hrl, hmap2⟩, hs⟩
      cases hrl
      cases hmap2
      cases hs
      exact hmatch
  | cons name names ih =>
      change RTLgen.bind (RTLgen.add_vars map1 names)
        (fun x => RTLgen.bind (RTLgen.add_var x.2 name)
          (fun y => RTLgen.ret (y.1 :: x.1, y.2))) s1 =
        .OK (rl, map2) s2 i at hadd
      cases hrec : RTLgen.add_vars map1 names s1 with
      | Error msg =>
          simp [RTLgen.bind, hrec] at hadd
      | OK x sm hincr =>
          cases x with
          | mk rlmid mapmid =>
              simp [RTLgen.bind, hrec] at hadd
              cases hvar : RTLgen.add_var mapmid name sm with
              | Error msg =>
                  simp [hvar] at hadd
              | OK x sn hinc =>
                  cases x with
                  | mk rnew mapnew =>
                      simp [RTLgen.ret, hvar] at hadd
                      rcases hadd with ⟨⟨hrl, hmap2⟩, hs⟩
                      have htail := ih map1 s1 hmap rlmid mapmid sm hincr
                        hmatch hfresh hrec
                      subst rl
                      subst map2
                      subst s2
                      unfold RTLgen.add_var at hvar
                      cases mapmid with
                      | mk mapVars mapLetvars =>
                          unfold PTree.t at mapVars
                          unfold CompCert4Lean.Common.AST.ident at name
                          unfold CompCert4Lean.Backend.Registers.reg at rnew
                          change RTLgen.bind RTLgen.new_reg
                            (fun r => RTLgen.ret (r,
                              ({ map_vars := PTree.set name r mapVars, map_letvars := mapLetvars } : RTLgen.mapping))) sm =
                            .OK (rnew, mapnew) sn hinc at hvar
                          dsimp [RTLgen.bind] at hvar
                          rw [show RTLgen.new_reg sm = .OK sm.st_nextreg _ _ from rfl] at hvar
                          simp [RTLgen.ret] at hvar
                          rcases hvar with ⟨hpair, hstate⟩
                          cases hpair
                          cases hstate
                          constructor
                          · intro id v henv
                            by_cases hid : id = name
                            · subst id
                              dsimp [CompCert4Lean.Backend.Cminor.set_locals] at henv
                              have hset := @PTree.getSet_equation val name name Vundef
                                (show PTree.tree val from
                                  (CompCert4Lean.Backend.Cminor.set_locals names e))
                              rw [hset] at henv
                              simp at henv
                              cases henv
                              refine ⟨sm.st_nextreg, ?_, ?_⟩
                              · change PTree.get name
                                  (PTree.set name sm.st_nextreg mapVars) = some sm.st_nextreg
                                have hmapset := @PTree.getSet_equation _ name name
                                  sm.st_nextreg mapVars
                                rw [hmapset]
                                simp
                              · have hfresh_sm : reg_fresh sm.st_nextreg sm := by
                                  intro hlt
                                  exact Nat.lt_irrefl _ hlt
                                have hfresh_new : reg_fresh sm.st_nextreg s1 :=
                                  reg_fresh_decr sm.st_nextreg s1 sm hincr hfresh_sm
                                rw [hfresh sm.st_nextreg hfresh_new]
                                exact Val.lessdef_undef _
                            · dsimp [CompCert4Lean.Backend.Cminor.set_locals] at henv
                              have hset := @PTree.getSet_equation val id name Vundef
                                (show PTree.tree val from
                                  (CompCert4Lean.Backend.Cminor.set_locals names e))
                              rw [hset] at henv
                              simp [hid] at henv
                              rcases htail.me_vars id v henv with ⟨r, hget, hless⟩
                              refine ⟨r, ?_, hless⟩
                              change PTree.get id (PTree.set name sm.st_nextreg mapVars) = some r
                              have hmapset := @PTree.getSet_equation _ id name sm.st_nextreg mapVars
                              rw [hmapset]
                              simp [hid]
                              exact hget
                          · exact htail.me_letvars

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem rtlgen_symbol_add_global
    (ge1 : Genv.t CminorSel.fundef Unit) (ge2 : Genv.t RTL.fundef Unit)
    (id : ident)
    (hm : ∀ id', PTree.get id' ge2.genv_symb = PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', PTree.get id'
      (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id'
      (PTree.set id ge1.genv_next ge1.genv_symb) := by
  intro id'
  have h2 := @PTree.getSet_equation _ id' id ge2.genv_next ge2.genv_symb
  have h1 := @PTree.getSet_equation _ id' id ge1.genv_next ge1.genv_symb
  by_cases h : id' = id
  · rw [h2, h1]
    simp only [dif_pos h]
    exact congrArg some hn
  · rw [h2, h1]
    simp only [dif_neg h]
    exact hm id'

private theorem rtlgen_match_genvs_add_global
    (R : globdef CminorSel.fundef Unit → globdef RTL.fundef Unit → Prop)
    (ge1 : Genv.t CminorSel.fundef Unit) (ge2 : Genv.t RTL.fundef Unit)
    (id : ident) (g1 : globdef CminorSel.fundef Unit)
    (g2 : globdef RTL.fundef Unit)
    (hm : Genv.match_genvs R ge1 ge2) (hrel : R g1 g2) :
    Genv.match_genvs R
      (Genv.add_global ge1 (id, g1)) (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · exact rtlgen_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @PTree.getSet_equation _ b ge1.genv_next g1 ge1.genv_defs
    have h2 := @PTree.getSet_equation _ b ge2.genv_next g2 ge2.genv_defs
    by_cases h : b = ge1.genv_next
    · have h' : b = ge2.genv_next := h.trans hm.mge_next.symm
      rw [h1, h2]
      simp only [dif_pos h, dif_pos h']
      exact option_rel.some g1 g2 hrel
    · have h' : b ≠ ge2.genv_next := by
        intro hb
        apply h
        exact hb.trans hm.mge_next
      rw [h1, h2]
      simp only [dif_neg h, dif_neg h']
      exact hm.mge_defs b

private theorem rtlgen_match_genvs_add_globals
    (R : globdef CminorSel.fundef Unit → globdef RTL.fundef Unit → Prop)
    (xs : List (ident × globdef CminorSel.fundef Unit))
    (ys : List (ident × globdef RTL.fundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 : Genv.t CminorSel.fundef Unit) (ge2 : Genv.t RTL.fundef Unit)
    (hm : Genv.match_genvs R ge1 ge2) :
    Genv.match_genvs R (Genv.add_globals ge1 xs) (Genv.add_globals ge2 ys) := by
  induction hxy generalizing ge1 ge2 with
  | nil => simpa [Genv.add_globals] using hm
  | @cons a xs b ys hab htail ih =>
      rcases a with ⟨aid, ag⟩
      rcases b with ⟨bid, bg⟩
      rcases hab with ⟨habid, habg⟩
      change aid = bid at habid
      subst bid
      simp only [Genv.add_globals, List.foldl_cons]
      apply ih
      simpa using (rtlgen_match_genvs_add_global R ge1 ge2 aid ag bg hm habg)

private theorem rtlgen_globalenvs_match
    (prog : CminorSel.program) (tprog : RTL.program)
    (hm : match_prog prog tprog) :
    Genv.match_genvs
      (@match_globdef
        (CminorSel.program) CminorSel.fundef Unit RTL.fundef Unit
        (@Linker_prog CminorSel.fundef Unit
          (Linker_fundef CminorSel.function) Linker_unit)
        (fun (_ : CminorSel.program) f tf => RTLgen.transl_fundef f = .OK tf)
        (fun x y : Unit => x = y) prog)
      (Genv.globalenv prog) (Genv.globalenv tprog) := by
  letI : Linker CminorSel.fundef := Linker_fundef CminorSel.function
  letI : Linker RTL.fundef := Linker_fundef RTL.function
  letI : Linker CminorSel.program := Linker_prog CminorSel.fundef Unit
  unfold match_prog match_program match_program_gen at hm
  let R : globdef CminorSel.fundef Unit → globdef RTL.fundef Unit → Prop :=
    match_globdef
      (fun (_ : CminorSel.program) f tf => RTLgen.transl_fundef f = .OK tf)
      (fun x y : Unit => x = y) prog
  have hempty : Genv.match_genvs R
      (Genv.empty_genv CminorSel.fundef Unit prog.prog_public)
      (Genv.empty_genv RTL.fundef Unit tprog.prog_public) := by
    constructor
    · rfl
    · intro id'
      rfl
    · intro b
      exact option_rel.none R
  have hlist_of : ∀
      (xs : List (ident × globdef CminorSel.fundef Unit))
      (ys : List (ident × globdef RTL.fundef Unit)),
      list_forall2
        (@match_ident_globdef
          CminorSel.program CminorSel.fundef Unit RTL.fundef Unit
          (@Linker_prog CminorSel.fundef Unit
            (Linker_fundef CminorSel.function) Linker_unit)
          (fun (_ : CminorSel.program) f tf => RTLgen.transl_fundef f = .OK tf)
          (fun x y : Unit => x = y) prog) xs ys →
      list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys := by
    intro xs ys h
    induction h with
    | nil => exact list_forall2.nil _
    | @cons a xs b ys hab htail ih =>
        apply list_forall2.cons
        · exact ⟨hab.1, by simpa [R] using hab.2⟩
        · exact ih
  have hlist := hlist_of prog.prog_defs tprog.prog_defs hm.1
  exact rtlgen_match_genvs_add_globals R prog.prog_defs tprog.prog_defs
    hlist _ _ hempty

private theorem rtlgen_function_ptr_translated : function_ptr_translatedStatement := by
  intro prog tprog hm b f hfind
  have hg := rtlgen_globalenvs_match prog tprog hm
  unfold Genv.find_funct_ptr Genv.find_def at hfind ⊢
  cases h1 : PTree.get b (Genv.globalenv prog).genv_defs with
  | none => simp [h1] at hfind
  | some gd1 =>
      cases gd1 with
      | Gfun f1 =>
          have hf : f1 = f := by simpa [h1] using hfind
          subst f1
          cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
          | none =>
              have hd := hg.mge_defs b
              simp [h1, h2] at hd
              cases hd
          | some gd2 =>
              cases gd2 with
              | Gfun f2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel =>
                      cases hrel with
                      | match_globdef_fun ctx' f1 f2 horder htrans =>
                          simpa using htrans
              | Gvar v2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel => cases hrel
      | Gvar v1 => simp [h1] at hfind

theorem functions_translated : functions_translatedStatement := by
  intro prog tprog hm v f hfind
  unfold Genv.find_funct at hfind ⊢
  cases v with
  | Vundef => simp at hfind
  | Vint n => simp at hfind
  | Vlong n => simp at hfind
  | Vfloat n => simp at hfind
  | Vsingle n => simp at hfind
  | Vptr b ofs =>
      cases hzero : Lib.Integers.Ptrofs.eq ofs Lib.Integers.Ptrofs.zero with
      | false => simp [hzero] at hfind
      | true =>
          simp [hzero] at hfind ⊢
          exact rtlgen_function_ptr_translated prog tprog hm b f hfind

end CompCert4Lean.Backend.RTLgenproof
