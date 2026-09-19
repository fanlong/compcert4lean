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

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Common.Linking

private theorem rtlgen_add_globals_public {F V : Type}
    (ge : Genv.t F V) (gl : List (ident × globdef F V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x xs ih =>
      simp only [Genv.add_globals, List.foldl_cons]
      simpa [Genv.add_globals, Genv.add_global] using ih (Genv.add_global ge x)

theorem senv_preserved : senv_preservedStatement := by
  intro prog tprog hm
  unfold Senv.equiv
  constructor
  · intro id
    have hg := rtlgen_globalenvs_match prog tprog hm
    change Genv.find_symbol (Genv.globalenv tprog) id =
      Genv.find_symbol (Genv.globalenv prog) id
    simpa [Genv.find_symbol] using hg.mge_symb id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv tprog) id =
      Genv.public_symbol (Genv.globalenv prog) id
    have ht : (Genv.globalenv tprog).genv_public = tprog.prog_public := by
      unfold Genv.globalenv
      exact rtlgen_add_globals_public _ _
    have hp : (Genv.globalenv prog).genv_public = prog.prog_public := by
      unfold Genv.globalenv
      exact rtlgen_add_globals_public _ _
    unfold Genv.public_symbol
    have hs : Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id := by
      simpa [Genv.find_symbol] using
        (rtlgen_globalenvs_match prog tprog hm).mge_symb id
    rw [hs, ht, hp]
    unfold match_prog match_program match_program_gen at hm
    rw [hm.2.2]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv tprog) b =
      Genv.block_is_volatile (Genv.globalenv prog) b
    have hg := rtlgen_globalenvs_match prog tprog hm
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    cases h1 : PTree.get b (Genv.globalenv prog).genv_defs with
    | none =>
        cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
        | none => rfl
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
    | some gd1 =>
        cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
        | none =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd with
            | some x y hrel =>
                cases hrel with
                | match_globdef_fun ctx' f1 f2 horder htrans => rfl
                | match_globdef_var v1 v2 hvar =>
                    cases hvar
                    rfl

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep

theorem tr_move_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    tr_move_correctStatement := by
  intro xi tprog r1 ns r2 nd cs f sp rs m hmove
  cases hmove with
  | tr_move_0 =>
      refine ⟨rs, ?_, ?_, ?_⟩
      · exact CompCert4Lean.Common.Smallstep.star_refl _ _ _
      · rfl
      · intro r' hr'
        rfl
  | tr_move_1 =>
      refine ⟨Regmap.set r2 (Regmap.get r1 rs) rs, ?_, ?_, ?_⟩
      · apply CompCert4Lean.Common.Smallstep.star_one
        apply RTL.step.exec_Iop (op := .Omove) (args := [r1])
        · rename_i hcode
          exact hcode
        · rfl
      · exact Regmap.gss_proof CompCert4Lean.Common.Values.val r2 (Regmap.get r1 rs) rs
      · intro r' hne
        exact Regmap.gso_proof CompCert4Lean.Common.Values.val r' r2
          (Regmap.get r1 rs) rs hne

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values

private theorem rtlgenproof_match_env_same_move
    (map : RTLgen.mapping) (e : CompCert4Lean.Backend.Cminor.env)
    (le : letenv) (rs rs' : regset) (r rd : reg)
    (hmatch : match_env map e le rs)
    (heq : rd = r)
    (hresult : Regmap.get rd rs' = Regmap.get r rs)
    (hstable : ∀ r', r' ≠ rd → Regmap.get r' rs' = Regmap.get r' rs) :
    match_env map e le rs' := by
  apply match_env_invariant map e le rs rs' hmatch
  intro r' hr'
  by_cases hrd : r' = rd
  · subst r'
    simpa [heq] using hresult
  · exact hstable r' hrd

private theorem rtlgenproof_match_env_updated_move
    (map : RTLgen.mapping) (e : CompCert4Lean.Backend.Cminor.env)
    (le : letenv) (rs rs' : regset) (dst : Option ident)
    (r rd : reg) (v tv : val)
    (hmatch : match_env map e le rs)
    (hless : Val.lessdef v tv)
    (hwf : map_wf map)
    (hok : reg_map_ok map rd dst)
    (hresult : Regmap.get rd rs' = tv)
    (hstable : ∀ r', r' ≠ rd → Regmap.get r' rs' = Regmap.get r' rs) :
    match_env map (CompCert4Lean.Backend.Cminor.set_optvar dst v e) le rs' := by
  have hset : match_env map
      (CompCert4Lean.Backend.Cminor.set_optvar dst v e) le
      (Regmap.set rd tv rs) :=
    match_env_update_dest map e le rs dst rd v tv hless hwf hok hmatch
  apply match_env_invariant map
    (CompCert4Lean.Backend.Cminor.set_optvar dst v e) le
    (Regmap.set rd tv rs) rs' hset
  intro r' hr'
  by_cases hrd : r' = rd
  · subst r'
    rw [Regmap.gss_proof val rd tv rs]
    exact hresult
  · rw [Regmap.gso_proof val r' rd tv rs hrd]
    exact hstable r' hrd

theorem transl_expr_Evar_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_expr_Evar_correctStatement := by
  intro xi tprog sp e m le id v henv
  unfold transl_expr_prop
  intro tge tm cs f map pr ns nd rd rs dst hwf htr hmatch hext
  cases htr with
  | @tr_Evar map pr id ns nd r rd dst hmap hok hmove =>
      have hvar := match_env_find_var map e le rs id v _ hmatch henv hmap
      obtain ⟨rs', hstar, hresult, hstable⟩ :=
        tr_move_correct xi tprog _ _ _ _ cs f sp rs tm hmove
      have hlessResult : Val.lessdef v (Regmap.get rd rs') := by
        rw [hresult]
        exact hvar
      have hcase : (rd = r) ∨ (¬ rd ∈ pr) := by
        rcases hok with ⟨hopt, _⟩ | ⟨_, hpr⟩
        · exact Or.inl hopt
        · exact Or.inr hpr
      refine ⟨rs', tm, hstar, ?_, ?_, ?_, ?_⟩
      · rcases hok with ⟨hopt, hdst⟩ | ⟨hok, hpr⟩
        · subst rd
          simpa [hdst, CompCert4Lean.Backend.Cminor.set_optvar] using
            rtlgenproof_match_env_same_move
            map e le rs rs' _ _ hmatch rfl hresult hstable
        · exact rtlgenproof_match_env_updated_move map e le rs rs' dst r rd v
            (Regmap.get rd rs') hmatch hlessResult hwf hok rfl hstable
      · exact hlessResult
      · intro r' hr'
        rcases hcase with hrd | hpr
        · by_cases heq : r' = rd
          · subst r'
            simpa [hrd] using hresult
          · exact hstable r' heq
        · exact hstable r' (by
            intro heq
            subst r'
            exact hpr hr')
      · exact hext

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values

theorem transl_expr_Econdition_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_expr_Econdition_correctStatement := by
  intro xi prog tprog sp e m le a ifso ifnot va v
    hevalcond htranscond hevalbranch htransbranch
  unfold transl_expr_prop at htransbranch ⊢
  intro tge tm cs f map pr ns nd rd rs dst hwf htr hmatch hext
  cases htr with
  | tr_Econdition map pr a ifso ifnot ns nd rd ntrue nfalse dst htrcond htrtrue htrfalse =>
      have htrbranch : tr_expr f.fn_code map pr (if va then ifso else ifnot)
          (if va then ntrue else nfalse) nd rd dst := by
        cases va
        · exact htrfalse
        · exact htrtrue
      have hcond := htranscond tm cs f map pr ns ntrue nfalse rs hwf htrcond hmatch hext
      obtain ⟨rs1, tm1, hstar1, hmatch1, hstable1, hext1⟩ := hcond
      have hbranch := htransbranch tm1 cs f map pr (if va then ntrue else nfalse)
          nd rd rs1 dst hwf htrbranch hmatch1 hext1
      obtain ⟨rs2, tm2, hstar2, hmatch2, hresult2, hstable2, hext2⟩ := hbranch
      refine ⟨rs2, tm2, ?_, hmatch2, hresult2, ?_, hext2⟩
      · exact star_trans _ _ _ _ _ _ _
          (plus_star _ _ _ _ _ _ _ hstar1) _ _ _ hstar2 rfl
      · intro r hr
        calc
          Regmap.get r rs2 = Regmap.get r rs1 := hstable2 r hr
          _ = Regmap.get r rs := hstable1 r hr

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem eval_builtin_args_trivial : eval_builtin_args_trivialStatement := by
  intro ge rs sp m rl
  unfold eval_builtin_args
  induction rl with
  | nil => exact list_forall2.nil _
  | cons r rl ih =>
      simp only [List.map]
      apply list_forall2.cons
      · exact eval_BA r
      · exact ih

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values

theorem transl_expr_Eletvar_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_expr_Eletvar_correctStatement := by
  intro xi tprog sp e m le n v hle
  unfold transl_expr_prop
  intro tge tm cs f map pr ns nd rd rs dst hwf htr hmatch hext
  cases htr with
  | tr_Eletvar map pr n ns nd rd r dst hlet hok hmove =>
      have hvar := match_env_find_letvar map e le rs n v r hmatch hle hlet
      obtain ⟨rs', hstar, hresult, hstable⟩ :=
        tr_move_correct xi tprog _ _ _ _ cs f sp rs tm hmove
      have hlessResult : Val.lessdef v (Regmap.get rd rs') := by
        rw [hresult]
        exact hvar
      have hcase : (rd = r) ∨ (¬ rd ∈ pr) := by
        rcases hok with ⟨hopt, _⟩ | ⟨_, hpr⟩
        · exact Or.inl hopt
        · exact Or.inr hpr
      refine ⟨rs', tm, hstar, ?_, hlessResult, ?_, hext⟩
      · rcases hok with ⟨hopt, hdst⟩ | ⟨hok, hpr⟩
        · subst rd
          simpa [hdst, CompCert4Lean.Backend.Cminor.set_optvar] using
            rtlgenproof_match_env_same_move
            map e le rs rs' _ _ hmatch rfl hresult hstable
        · exact rtlgenproof_match_env_updated_move map e le rs rs' dst r rd v
            (Regmap.get rd rs') hmatch hlessResult hwf hok rfl hstable
      · intro r' hr'
        rcases hcase with hrd | hpr
        · by_cases heq : r' = rd
          · subst r'
            simpa [hrd] using hresult
          · exact hstable r' heq
        · exact hstable r' (by
            intro heq
            subst r'
            exact hpr hr')

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values

theorem transl_expr_Elet_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_expr_Elet_correctStatement := by
  intro xi prog tprog sp e m le a1 a2 v1 v2
    heval1 htrans1 heval2 htrans2
  unfold transl_expr_prop at htrans1 htrans2 ⊢
  intro tge tm cs f map pr ns nd rd rs dst hwf htr hmatch hext
  cases htr with
  | tr_Elet map pr b1 b2 ns nd rd n1 r dst hfresh hbound hbody =>
      have hmapwf : map_wf (RTLgen.add_letvar map r) :=
        add_letvar_wf map r hwf hfresh
      have hfirst := htrans1 tm cs f map pr ns n1 r rs none hwf hbound hmatch hext
      obtain ⟨rs1, tm1, hstar1, hmatch1, hresult1, hstable1, hext1⟩ := hfirst
      have hboundMatch : match_env (RTLgen.add_letvar map r) e (v1 :: le) rs1 := by
        exact match_env_bind_letvar map e le rs1 r v1 hmatch1 hresult1
      have hsecond := htrans2 tm1 cs f (RTLgen.add_letvar map r) pr n1 nd rd rs1 dst
        hmapwf hbody hboundMatch hext1
      obtain ⟨rs2, tm2, hstar2, hmatch2, hresult2, hstable2, hext2⟩ := hsecond
      refine ⟨rs2, tm2, ?_, ?_, hresult2, ?_, hext2⟩
      · exact star_trans _ _ _ _ _ _ _ hstar1 _ _ _ hstar2 rfl
      · exact match_env_unbind_letvar map
          (CompCert4Lean.Backend.Cminor.set_optvar dst v2 e) le rs2 r v1 hmatch2
      · intro r' hr'
        calc
          Regmap.get r' rs2 = Regmap.get r' rs1 := hstable2 r' hr'
          _ = Regmap.get r' rs := hstable1 r' hr'

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values

theorem transl_exprlist_Enil_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_exprlist_Enil_correctStatement := by
  intro xi tprog sp e m le
  unfold transl_exprlist_prop
  intro tge tm cs f map pr ns nd rl rs hwf htr hmatch hext
  cases htr with
  | tr_Enil map pr n =>
      refine ⟨rs, tm, ?_, hmatch, ?_, ?_, hext⟩
      · exact star_refl _ _ _
      · exact Val.lessdef_list_nil
      · intro r hr
        rfl

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values

theorem transl_exprlist_Econs_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_exprlist_Econs_correctStatement := by
  intro xi prog tprog sp e m le a1 al v1 vl
    heval1 htrans1 heval2 htrans2
  unfold transl_expr_prop at htrans1
  unfold transl_exprlist_prop at htrans2 ⊢
  intro tge tm cs f map pr ns nd rl rs hwf htr hmatch hext
  cases htr with
  | tr_Econs map pr a1 al ns nd r1 rl n1 hhead htail =>
      have hfirst := htrans1 tm cs f map pr ns n1 r1 rs none hwf hhead hmatch hext
      obtain ⟨rs1, tm1, hstar1, hmatch1, hresult1, hstable1, hext1⟩ := hfirst
      have htail' := htrans2 tm1 cs f map (r1 :: pr) n1 nd rl rs1
        hwf htail hmatch1 hext1
      obtain ⟨rs2, tm2, hstar2, hmatch2, hresult2, hstable2, hext2⟩ := htail'
      refine ⟨rs2, tm2, ?_, hmatch2, ?_, ?_, hext2⟩
      · exact star_trans _ _ _ _ _ _ _ hstar1 _ _ _ hstar2 rfl
      · change Val.lessdef_list (v1 :: vl)
          (Regmap.get r1 rs2 :: rl.map (fun r => Regmap.get r rs2))
        apply Val.lessdef_list_cons
        · rw [hstable2 r1 (by simp)]
          exact hresult1
        · simpa using hresult2
      · intro r hr
        calc
          Regmap.get r rs2 = Regmap.get r rs1 := hstable2 r (by simp [hr])
          _ = Regmap.get r rs := hstable1 r hr

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.RTLgen

theorem eval_exprlist_append
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_exprlist_appendStatement := by
  intro xi prog sp e m le al1 vl1 al2 vl2 h1 h2
  induction al1 generalizing vl1 with
  | nil =>
      cases h1
      simpa using h2
  | cons a1 al1 ih =>
      cases h1 with
      | cons le' a1' al1' v1 vl hhead htail =>
          apply CminorSel.eval_exprlist.cons
          · exact hhead
          · exact ih vl htail

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Lib.Coqlib

theorem lt_state_wf : lt_state_wfStatement := by
  unfold lt_state_wfStatement
  unfold lt_state
  have hlex : WellFounded (lex_ord Nat.lt Nat.lt) := by
    apply wf_lex_ord
    · exact Nat.lt_wfRel.wf
    · exact Nat.lt_wfRel.wf
  have hacc : ∀ p, Acc (lex_ord Nat.lt Nat.lt) p →
      ∀ s, measure_state s = p →
        Acc (fun s1 s2 => lex_ord Nat.lt Nat.lt (measure_state s1) (measure_state s2)) s := by
    intro p hp
    induction hp with
    | intro p hp ih =>
        intro s hs
        apply Acc.intro s
        intro t hts
        apply ih (measure_state t) ?_ t rfl
        simpa [hs] using hts
  apply WellFounded.intro
  intro s
  exact hacc (measure_state s) (hlex.apply (measure_state s)) s rfl

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Values

private theorem invert_eval_builtin_arg_aux
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    invert_eval_builtin_argStatement := by
  intro xi prog sp e m a v hev
  induction hev with
  | argument a v heval =>
      refine ⟨[v], ?_, ?_, ?_⟩
      · exact CminorSel.eval_exprlist.cons [] a .Enil v [] heval
          (CminorSel.eval_exprlist.nil [])
      · exact eval_BA v
      · intro vl'
        rfl
  | intValue n =>
      refine ⟨[], ?_, ?_, ?_⟩
      · exact CminorSel.eval_exprlist.nil []
      · exact eval_BA_int n
      · intro vl'
        rfl
  | longValue n =>
      refine ⟨[], ?_, ?_, ?_⟩
      · exact CminorSel.eval_exprlist.nil []
      · exact eval_BA_long n
      · intro vl'
        rfl
  | floatValue n =>
      refine ⟨[], ?_, ?_, ?_⟩
      · exact CminorSel.eval_exprlist.nil []
      · exact eval_BA_float n
      · intro vl'
        rfl
  | singleValue n =>
      refine ⟨[], ?_, ?_, ?_⟩
      · exact CminorSel.eval_exprlist.nil []
      · exact eval_BA_single n
      · intro vl'
        rfl
  | loadStack chunk ofs v hload =>
      refine ⟨[], ?_, ?_, ?_⟩
      · exact CminorSel.eval_exprlist.nil []
      · exact eval_BA_loadstack chunk ofs v hload
      · intro vl'
        rfl
  | addressStack ofs =>
      refine ⟨[], ?_, ?_, ?_⟩
      · exact CminorSel.eval_exprlist.nil []
      · exact eval_BA_addrstack ofs
      · intro vl'
        rfl
  | loadGlobal chunk id ofs v hload =>
      refine ⟨[], ?_, ?_, ?_⟩
      · exact CminorSel.eval_exprlist.nil []
      · exact eval_BA_loadglobal chunk id ofs v hload
      · intro vl'
        rfl
  | addressGlobal id ofs =>
      refine ⟨[], ?_, ?_, ?_⟩
      · exact CminorSel.eval_exprlist.nil []
      · exact eval_BA_addrglobal id ofs
      · intro vl'
        rfl
  | splitLong a1 a2 v1 v2 h1 h2 =>
      refine ⟨[v1, v2], ?_, ?_, ?_⟩
      · apply CminorSel.eval_exprlist.cons
        · exact h1
        · apply CminorSel.eval_exprlist.cons
          · exact h2
          · exact CminorSel.eval_exprlist.nil []
      · simpa [convert_builtin_arg] using
          (eval_BA_splitlong (.BA v1) (.BA v2) v1 v2 (eval_BA v1) (eval_BA v2))
      · intro vl'
        rfl
  | addPointer a1 a2 v1 v2 h1 h2 ih1 ih2 =>
      obtain ⟨vl1, hvl1, hev1, hconv1⟩ := ih1
      obtain ⟨vl2, hvl2, hev2, hconv2⟩ := ih2
      refine ⟨vl1 ++ vl2, ?_, ?_, ?_⟩
      · exact eval_exprlist_append xi prog sp e m []
          (params_of_builtin_arg a1) vl1 (params_of_builtin_arg a2) vl2 hvl1 hvl2
      · simpa [convert_builtin_arg, hconv1 vl2, hconv2 []] using
          (eval_BA_addptr (convert_builtin_arg a1 vl1).1
            (convert_builtin_arg a2 vl2).1 v1 v2 hev1 hev2)
      · intro vl'
        simp [convert_builtin_arg, List.append_assoc,
          hconv1 vl2, hconv1 (vl2 ++ vl'), hconv2 vl']

theorem invert_eval_builtin_args
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    invert_eval_builtin_argsStatement := by
  intro xi prog sp e m al vl hargs
  induction hargs with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · exact CminorSel.eval_exprlist.nil []
      · exact CompCert4Lean.Lib.Coqlib.list_forall2_nil _
  | cons a v ha htail ih =>
      obtain ⟨vl1, hvl1, hev1, hconv1⟩ :=
        invert_eval_builtin_arg_aux xi prog sp e m a v ha
      obtain ⟨vl2, hvl2, hev2⟩ := ih
      refine ⟨vl1 ++ vl2, ?_, ?_⟩
      · exact eval_exprlist_append xi prog sp e m []
          (params_of_builtin_arg a) vl1 (params_of_builtin_args _) vl2 hvl1 hvl2
      · rw [convert_builtin_args, hconv1]
        exact CompCert4Lean.Lib.Coqlib.list_forall2.cons _ _ hev1 hev2

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values

private theorem rtlgenproof_longofwords_lessdef
    (v1 v2 v1' v2' : val) :
    Val.lessdef v1 v1' → Val.lessdef v2 v2' →
      Val.lessdef (Val.longofwords v1 v2) (Val.longofwords v1' v2') := by
  intro h1 h2
  cases h1 with
  | lessdef_refl v1 =>
      cases h2 with
      | lessdef_refl v2 => exact Val.lessdef_refl _
      | lessdef_undef v2' =>
          simpa [Val.longofwords] using
            (Val.lessdef_undef (Val.longofwords v1 v2'))
  | lessdef_undef v1' =>
      simpa [Val.longofwords] using
        (Val.lessdef_undef (Val.longofwords v1' v2'))

private theorem rtlgenproof_add_lessdef
    (v1 v2 v1' v2' : val) :
    Val.lessdef v1 v1' → Val.lessdef v2 v2' →
      Val.lessdef (Val.add v1 v2) (Val.add v1' v2') := by
  intro h1 h2
  cases h1 with
  | lessdef_refl v1 =>
      cases h2 with
      | lessdef_refl v2 => exact Val.lessdef_refl _
      | lessdef_undef v2' =>
          simpa [Val.add] using (Val.lessdef_undef (Val.add v1 v2'))
  | lessdef_undef v1' =>
      simpa [Val.add] using (Val.lessdef_undef (Val.add v1' v2'))

private theorem rtlgenproof_addl_lessdef
    (v1 v2 v1' v2' : val) :
    Val.lessdef v1 v1' → Val.lessdef v2 v2' →
      Val.lessdef (Val.addl v1 v2) (Val.addl v1' v2') := by
  intro h1 h2
  cases h1 with
  | lessdef_refl v1 =>
      cases h2 with
      | lessdef_refl v2 => exact Val.lessdef_refl _
      | lessdef_undef v2' =>
          simpa [Val.addl] using (Val.lessdef_undef (Val.addl v1 v2'))
  | lessdef_undef v1' =>
      simpa [Val.addl] using (Val.lessdef_undef (Val.addl v1' v2'))

theorem transl_eval_builtin_arg : transl_eval_builtin_argStatement := by
  intro prog sp m rs a
  induction a with
  | BA x =>
      intro vl rl v hless hev
      cases vl with
      | nil =>
          cases rl with
          | nil =>
              cases hev
              exact ⟨_, eval_BA_int _, Val.lessdef_refl _, Val.lessdef_list_nil⟩
          | cons r rl => cases hless
      | cons w vl =>
          cases rl with
          | nil => cases hless
          | cons r rl =>
              cases hless with
              | lessdef_list_cons _ _ _ _ hhead htail =>
                  cases hev
                  exact ⟨_, eval_BA _, hhead, htail⟩
  | BA_int n =>
      intro vl rl v hless hev
      cases hev
      exact ⟨_, eval_BA_int _, Val.lessdef_refl _, hless⟩
  | BA_long n =>
      intro vl rl v hless hev
      cases hev
      exact ⟨_, eval_BA_long _, Val.lessdef_refl _, hless⟩
  | BA_float f =>
      intro vl rl v hless hev
      cases hev
      exact ⟨_, eval_BA_float _, Val.lessdef_refl _, hless⟩
  | BA_single f =>
      intro vl rl v hless hev
      cases hev
      exact ⟨_, eval_BA_single _, Val.lessdef_refl _, hless⟩
  | BA_loadstack chunk ofs =>
      intro vl rl v hless hev
      cases hev with
      | eval_BA_loadstack _ _ _ hload =>
          exact ⟨_, eval_BA_loadstack _ _ _ hload, Val.lessdef_refl _, hless⟩
  | BA_addrstack ofs =>
      intro vl rl v hless hev
      cases hev
      exact ⟨_, eval_BA_addrstack _, Val.lessdef_refl _, hless⟩
  | BA_loadglobal chunk id ofs =>
      intro vl rl v hless hev
      cases hev with
      | eval_BA_loadglobal _ _ _ _ hload =>
          exact ⟨_, eval_BA_loadglobal _ _ _ _ hload, Val.lessdef_refl _, hless⟩
  | BA_addrglobal id ofs =>
      intro vl rl v hless hev
      cases hev
      exact ⟨_, eval_BA_addrglobal _ _, Val.lessdef_refl _, hless⟩
  | BA_splitlong hi lo ihHi ihLo =>
      intro vl rl v hless hev
      cases hvlHi : convert_builtin_arg hi vl with
      | mk ahi vl1 =>
        cases hvlLo : convert_builtin_arg lo vl1 with
        | mk alo vl2 =>
          cases hrlHi : convert_builtin_arg hi rl with
          | mk rhi rl1 =>
            cases hrlLo : convert_builtin_arg lo rl1 with
            | mk rlo rl2 =>
              simp [convert_builtin_arg, hvlHi, hvlLo] at hev
              cases hev with
              | eval_BA_splitlong _ _ vhi vlo hevHi hevLo =>
                  have hevHi' :
                      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
                        (fun v => v) sp m (convert_builtin_arg hi vl).1 vhi := by
                    rw [hvlHi]
                    exact hevHi
                  have hevLo' :
                      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
                        (fun v => v) sp m (convert_builtin_arg lo vl1).1 vlo := by
                    rw [hvlLo]
                    exact hevLo
                  obtain ⟨vhi', htargetHi, hlessHi, hremHi⟩ :=
                    ihHi vl rl vhi hless hevHi'
                  have htargetHi' := htargetHi
                  have hremHi' := hremHi
                  simp [hrlHi] at htargetHi'
                  simp [hvlHi, hrlHi] at hremHi'
                  obtain ⟨vlo', htargetLo, hlessLo, hremLo⟩ :=
                    ihLo vl1 rl1 vlo hremHi' hevLo'
                  have htargetLo' := htargetLo
                  have hremLo' := hremLo
                  simp [hrlLo] at htargetLo'
                  simp [hvlLo, hrlLo] at hremLo'
                  refine ⟨Val.longofwords vhi' vlo', ?_, ?_, ?_⟩
                  · simpa [convert_builtin_arg, hrlHi, hrlLo] using
                      (eval_BA_splitlong rhi rlo vhi' vlo' htargetHi' htargetLo')
                  · exact rtlgenproof_longofwords_lessdef _ _ _ _ hlessHi hlessLo
                  · simpa [convert_builtin_arg, hvlHi, hvlLo, hrlHi, hrlLo] using hremLo'
  | BA_addptr a1 a2 ih1 ih2 =>
      intro vl rl v hless hev
      cases hvl1 : convert_builtin_arg a1 vl with
      | mk av1 vl1 =>
        cases hvl2 : convert_builtin_arg a2 vl1 with
        | mk av2 vl2 =>
          cases hrl1 : convert_builtin_arg a1 rl with
          | mk ar1 rl1 =>
            cases hrl2 : convert_builtin_arg a2 rl1 with
            | mk ar2 rl2 =>
              simp [convert_builtin_arg, hvl1, hvl2] at hev
              cases hev with
              | eval_BA_addptr _ _ v1 v2 hev1 hev2 =>
                  have hev1' :
                      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
                        (fun v => v) sp m (convert_builtin_arg a1 vl).1 v1 := by
                    rw [hvl1]
                    exact hev1
                  have hev2' :
                      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
                        (fun v => v) sp m (convert_builtin_arg a2 vl1).1 v2 := by
                    rw [hvl2]
                    exact hev2
                  obtain ⟨v1', htarget1, hless1, hrem1⟩ :=
                    ih1 vl rl v1 hless hev1'
                  have htarget1' := htarget1
                  have hrem1' := hrem1
                  simp [hrl1] at htarget1'
                  simp [hvl1, hrl1] at hrem1'
                  obtain ⟨v2', htarget2, hless2, hrem2⟩ :=
                    ih2 vl1 rl1 v2 hrem1' hev2'
                  have htarget2' := htarget2
                  have hrem2' := hrem2
                  simp [hrl2] at htarget2'
                  simp [hvl2, hrl2] at hrem2'
                  let v' := if CompCert4Lean.X86_64.Archi.ptr64
                    then Val.addl v1' v2' else Val.add v1' v2'
                  refine ⟨v', ?_, ?_, ?_⟩
                  · simpa [v', convert_builtin_arg, hrl1, hrl2] using
                      (eval_BA_addptr ar1 ar2 v1' v2' htarget1' htarget2')
                  · simp only [v']
                    split
                    · exact rtlgenproof_addl_lessdef _ _ _ _ hless1 hless2
                    · exact rtlgenproof_add_lessdef _ _ _ _ hless1 hless2
                  · simpa [convert_builtin_arg, hvl1, hvl2, hrl1, hrl2] using hrem2'

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem transl_eval_builtin_args : transl_eval_builtin_argsStatement := by
  intro prog sp m rs al vl1 rl vl hless hev
  induction al generalizing vl1 rl vl with
  | nil =>
      cases hev
      exact ⟨[], list_forall2_nil _, Val.lessdef_list_nil⟩
  | cons a al ih =>
      cases hvl : convert_builtin_arg a vl1 with
      | mk a1 vl2 =>
        have hev' : eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
            (fun v => v) sp m (a1 :: convert_builtin_args al vl2) vl := by
          simpa [convert_builtin_args, hvl] using hev
        cases hev' with
        | cons _ _ hevHead hevTail =>
            have harg := transl_eval_builtin_arg prog sp m rs a vl1 rl
                _ hless (by simpa [hvl] using hevHead)
            obtain ⟨v1', harg', hless', hrem'⟩ := harg
            cases hrl : convert_builtin_arg a rl with
            | mk a1' rl2 =>
              have harg'' : eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
                  (fun r => Regmap.get r rs) sp m a1' v1' := by
                simpa [hrl] using harg'
              have hrem'' : Val.lessdef_list vl2
                  (rl2.map (fun r => Regmap.get r rs)) := by
                simpa [hvl, hrl] using hrem'
              obtain ⟨vl', htail', hvl'⟩ := ih vl2 rl2 _ hrem'' hevTail
              refine ⟨v1' :: vl', ?_, ?_⟩
              · simpa [eval_builtin_args, convert_builtin_args, hrl] using
                  (list_forall2.cons a1' _ harg'' htail')
              · exact Val.lessdef_list_cons _ _ _ _ hless' hvl'

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Lib.Maps

theorem tr_cont_ind_proof : tr_cont_ind := by
  intro P hseq hblock hstop hcall
  intro c m c0 n l l0 n0 o l1 h
  exact tr_cont.rec
    (motive_1 := fun c m k n l l0 n0 o cs _ => P c m k n l l0 n0 o cs)
    (motive_2 := fun _ _ _ => True)
    (fun c m s k nd nexits ngoto nret rret cs n hs hk ih =>
      hseq c m s k nd nexits ngoto nret rret cs n hs hk ih)
    (fun c m k nd nexits ngoto nret rret cs hk ih =>
      hblock c m k nd nexits ngoto nret rret cs hk ih)
    (fun c m ngoto nret rret cs hcode hs _ =>
      hstop c m ngoto nret rret cs hcode hs)
    (fun c m optid f sp e k ngoto nret rret cs hcode hs _ =>
      hcall c m optid f sp e k ngoto nret rret cs hcode hs)
    True.intro (by simp) h

theorem match_stacks_call_cont : match_stacks_call_contStatement := by
  intro c map k ncont nexits ngoto nret rret cs h
  refine tr_cont_ind_proof
    (P := fun c _ k _ _ _ nret rret cs =>
      match_stacks (CompCert4Lean.Backend.CminorSel.call_cont k) cs ∧
        PTree.get nret c = some (.Ireturn rret)) ?_ ?_ ?_ ?_
    c map k ncont nexits ngoto nret rret cs h
  · intro c map s k nd nexits ngoto nret rret cs n hs hk ih
    simpa [CompCert4Lean.Backend.CminorSel.call_cont] using ih
  · intro c map k nd nexits ngoto nret rret cs hk ih
    simpa [CompCert4Lean.Backend.CminorSel.call_cont] using ih
  · intro c map ngoto nret rret cs hcode hs
    simpa [CompCert4Lean.Backend.CminorSel.call_cont] using And.intro hs hcode
  · intro c map optid f sp e k ngoto nret rret cs hcode hs
    simpa [CompCert4Lean.Backend.CminorSel.call_cont] using And.intro hs hcode

theorem tr_cont_call_cont : tr_cont_call_contStatement := by
  intro c map k ncont nexits ngoto nret rret cs h
  refine tr_cont_ind_proof
    (P := fun c map k _ _ ngoto nret rret cs =>
      tr_cont c map (CompCert4Lean.Backend.CminorSel.call_cont k)
        nret [] ngoto nret rret cs) ?_ ?_ ?_ ?_
    c map k ncont nexits ngoto nret rret cs h
  · intro c map s k nd nexits ngoto nret rret cs n hs hk ih
    simpa [CompCert4Lean.Backend.CminorSel.call_cont] using ih
  · intro c map k nd nexits ngoto nret rret cs hk ih
    simpa [CompCert4Lean.Backend.CminorSel.call_cont] using ih
  · intro c map ngoto nret rret cs hcode hs
    simpa [CompCert4Lean.Backend.CminorSel.call_cont] using
      (tr_Kstop c map ngoto nret rret cs hcode hs)
  · intro c map optid f sp e k ngoto nret rret cs hcode hs
    simpa [CompCert4Lean.Backend.CminorSel.call_cont] using
      (tr_Kcall c map optid f sp e k ngoto nret rret cs hcode hs)

theorem tr_find_label : tr_find_labelStatement := by
  intro c map lbl n ngoto nret rret s' k' cs hgoto
  intro s k ns nd nexits hfind hstmt hcont
  induction hstmt generalizing k <;>
    simp only [CompCert4Lean.Backend.CminorSel.find_label] at hfind
  case tr_Sseq s1 s2 ns nd nexits ngoto nret rret mid h2 h1 ih2 ih1 =>
    cases hfirst : CompCert4Lean.Backend.CminorSel.find_label
        lbl s1 (.Kseq s2 k) with
    | none =>
        simp [hfirst] at hfind
        exact ih2 hgoto k hfind hcont
    | some sk =>
        simp [hfirst] at hfind
        have hfind' : CompCert4Lean.Backend.CminorSel.find_label
            lbl s1 (.Kseq s2 k) = some (s', k') :=
          hfirst.trans (congrArg some hfind)
        exact ih1 hgoto (.Kseq s2 k) hfind'
          (tr_Kseq c map s2 k mid nexits ngoto nret rret cs nd h2 hcont)
  case tr_Sifthenelse a strue sfalse ns nd nexits ngoto nret rret
      ntrue nfalse htrue hfalse hcond ihtrue ihfalse =>
    cases hfirst : CompCert4Lean.Backend.CminorSel.find_label lbl strue k with
    | none =>
        simp [hfirst] at hfind
        exact ihfalse hgoto k hfind hcont
    | some sk =>
        simp [hfirst] at hfind
        have hfind' : CompCert4Lean.Backend.CminorSel.find_label
            lbl strue k = some (s', k') :=
          hfirst.trans (congrArg some hfind)
        exact ihtrue hgoto k hfind' hcont
  case tr_Sloop sbody ns nd nexits ngoto nret rret nloop nend
      hbody hstart hend ihbody =>
    have hloop : tr_stmt c map (.Sloop sbody) nend nd nexits ngoto nret rret :=
      tr_stmt.tr_Sloop sbody nend nd nexits ngoto nret rret nloop nend
        hbody hend hend
    exact ihbody hgoto (.Kseq (.Sloop sbody) k) hfind
      (tr_Kseq c map (.Sloop sbody) k nend nexits ngoto nret rret cs nd
        hloop hcont)
  case tr_Sblock sbody ns nd nexits ngoto nret rret hbody ihbody =>
    exact ihbody hgoto (.Kblock k) hfind
      (tr_Kblock c map k nd nexits ngoto nret rret cs hcont)
  case tr_Slabel lbl' sbody ns nd nexits ngoto nret rret nlabel
      hgoto' hcode hbody ihbody =>
    cases hident : CompCert4Lean.Common.AST.ident_eq lbl lbl' with
    | left heq =>
        simp [hident] at hfind
        rcases hfind with ⟨rfl, rfl⟩
        subst lbl'
        have hn : nlabel = n := Option.some.inj (hgoto'.symm.trans hgoto)
        subst nlabel
        exact ⟨ns, nd, nexits, hcode, hbody, hcont⟩
    | right hne =>
        simp [hident] at hfind
        exact ihbody hgoto k hfind hcont
  all_goals simp at hfind

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem rtlgen_initial_store_init_data
    {prog : CminorSel.program} {tprog : RTL.program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    (m : mem) (b : positive) (p : Z) (i : init_data) :
    Genv.store_init_data (Genv.globalenv prog) m b p i =
      Genv.store_init_data (Genv.globalenv tprog) m b p i := by
  cases i with
  | Init_addrof symb ofs =>
      simp [Genv.store_init_data, hsymb symb]
  | _ => rfl

private theorem rtlgen_initial_store_init_data_list
    {prog : CminorSel.program} {tprog : RTL.program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id) :
    ∀ (m : mem) (b : positive) (p : Z) (il : List init_data),
      Genv.store_init_data_list (Genv.globalenv prog) m b p il =
        Genv.store_init_data_list (Genv.globalenv tprog) m b p il := by
  intro m b p il
  induction il generalizing m b p with
  | nil => rfl
  | cons i rest ih =>
      simp only [Genv.store_init_data_list]
      rw [rtlgen_initial_store_init_data hsymb]
      cases h : Genv.store_init_data (Genv.globalenv tprog) m b p i with
      | none => simp [h]
      | some m' =>
          simp only [h]
          exact ih m' b
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
              p (init_data_size i))

private theorem rtlgen_initial_alloc_global
    [Linker CminorSel.program]
    {prog : CminorSel.program} {tprog : RTL.program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    {id : ident} {gd : globdef CminorSel.fundef Unit}
    {tg : globdef RTL.fundef Unit}
    (hgd : match_globdef
      (fun _ f tf => RTLgen.transl_fundef f = .OK tf)
      (fun x y : Unit => x = y) prog gd tg)
    (m : mem) :
    Genv.alloc_global (Genv.globalenv prog) m (id, gd) =
      Genv.alloc_global (Genv.globalenv tprog) m (id, tg) := by
  cases hgd with
  | match_globdef_fun ctx' f1 f2 horder htrans => rfl
  | match_globdef_var v1 v2 hvar =>
      cases hvar with
      | match_globvar_intro info1 info2 init ro vol hinfo =>
          cases hinfo
          simp only [Genv.alloc_global]
          simp [rtlgen_initial_store_init_data_list hsymb]

private theorem rtlgen_initial_alloc_globals
    [Linker CminorSel.program]
    {prog : CminorSel.program} {tprog : RTL.program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    (gl : List (ident × globdef CminorSel.fundef Unit))
    (tgl : List (ident × globdef RTL.fundef Unit))
    (hlist : list_forall2
      (match_ident_globdef
        (fun _ f tf => RTLgen.transl_fundef f = .OK tf)
        (fun x y : Unit => x = y) prog) gl tgl) :
    ∀ (m m' : mem),
      Genv.alloc_globals (Genv.globalenv prog) m gl = some m' →
      Genv.alloc_globals (Genv.globalenv tprog) m tgl = some m' := by
  induction hlist with
  | nil =>
      intro m m' h
      simpa [Genv.alloc_globals] using h
  | cons hd thd hhd htl ih =>
      intro m m' h
      rcases hhd with ⟨hid, hgd⟩
      rcases hd with ⟨id, gd⟩
      rcases thd with ⟨tid, tgd⟩
      have halloc :
          Genv.alloc_global (Genv.globalenv prog) m (id, gd) =
            Genv.alloc_global (Genv.globalenv tprog) m (tid, tgd) := by
        change id = tid at hid
        subst tid
        exact rtlgen_initial_alloc_global hsymb hgd m
      simp only [Genv.alloc_globals] at h ⊢
      rw [halloc] at h
      cases ha : Genv.alloc_global (Genv.globalenv tprog) m (tid, tgd) with
      | none => simp [ha] at h
      | some m1 =>
          simp only [ha] at h ⊢
          exact ih m1 m' h

private theorem rtlgen_sig_transl_fundef
    (f : CminorSel.fundef) (tf : RTL.fundef) :
    RTLgen.transl_fundef f = .OK tf → RTL.funsig tf = CminorSel.funsig f := by
  intro h
  cases f with
  | Internal f =>
      unfold RTLgen.transl_fundef CompCert4Lean.Common.AST.transf_partial_fundef at h
      cases htf : RTLgen.transl_function f with
      | Error msg => simp [htf] at h
      | OK tf' =>
          simp [htf] at h
          cases h
          unfold RTLgen.transl_function at htf
          cases hbuild : RTLgen.transl_fun f RTLgen.init_state with
          | Error msg => simp [hbuild] at htf
          | OK nr s i =>
              simp [hbuild] at htf
              cases htf
              rfl
  | External ef =>
      simp [RTLgen.transl_fundef, CompCert4Lean.Common.AST.transf_partial_fundef] at h
      cases h
      rfl

private theorem rtlgen_mem_extends_refl (m : mem) : Mem.extends m m := by
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro b1 b2 delta ofs k p hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change Mem.perm m b1 (ZArith.BinInt.Z.add ofs (.Z0 : Z)) k p
      have hzadd : ZArith.BinInt.Z.add ofs (.Z0 : Z) = ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
        rw [intOfZ_zOfInt]
        simp
      rw [hzadd]
      exact hp
    · intro b1 b2 delta chunk ofs p hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      refine ⟨.Z0, ?_⟩
      apply intOfZ_injective
      change 0 = intOfZ (ZArith.BinInt.Z.mul
        (CompCert4Lean.Common.Memdata.align_chunk chunk) (.Z0 : Z))
      change 0 = intOfZ (zOfInt (intOfZ
        (CompCert4Lean.Common.Memdata.align_chunk chunk) * 0))
      rw [intOfZ_zOfInt]
      simp
    · intro b1 ofs b2 delta hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change memval_inject inject_id
        (ZMap.get ofs (PMap.get b1 m.mem_contents))
        (ZMap.get (ZArith.BinInt.Z.add ofs (.Z0 : Z))
          (PMap.get b1 m.mem_contents))
      have hzadd : ZArith.BinInt.Z.add ofs (.Z0 : Z) = ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
        rw [intOfZ_zOfInt]
        simp
      rw [hzadd]
      exact memval_lessdef_refl _
  · intro b ofs k p hp
    exact Or.inl hp

theorem transl_initial_states : transl_initial_statesStatement := by
  letI : Linker CminorSel.fundef := @Linker_fundef CminorSel.function
  letI : Linker Unit := Linker_unit
  letI : Linker CminorSel.program := @Linker_prog CminorSel.fundef Unit _ _
  intro prog tprog hmatch S hinit
  cases hinit with
  | intro b f m0 hmem hsymb hfun hsig =>
      rcases rtlgen_function_ptr_translated prog tprog hmatch b f hfun with
        ⟨tf, htf, htrans⟩
      refine ⟨RTL.Callstate [] tf [] m0, ?_, ?_⟩
      · apply RTL.initial_state.intro b tf m0
        · unfold Genv.init_mem at hmem ⊢
          apply rtlgen_initial_alloc_globals (prog := prog) (tprog := tprog)
            (fun id => (rtlgen_globalenvs_match prog tprog hmatch).mge_symb id)
            prog.prog_defs tprog.prog_defs hmatch.1 Mem.empty m0
          exact hmem
        · change Genv.find_symbol (Genv.globalenv tprog) tprog.prog_main = some b
          rw [hmatch.2.1]
          have hs : Genv.find_symbol (Genv.globalenv tprog) prog.prog_main =
              Genv.find_symbol (Genv.globalenv prog) prog.prog_main := by
            simpa [Genv.find_symbol] using
              (rtlgen_globalenvs_match prog tprog hmatch).mge_symb prog.prog_main
          rw [hs]
          exact hsymb
        · exact htf
        · rw [rtlgen_sig_transl_fundef f tf htrans]
          exact hsig
      · exact match_callstate f [] [] .Kstop m0 m0 [] tf htrans
          match_stacks_stop Val.lessdef_list_nil (rtlgen_mem_extends_refl m0)

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

theorem transl_final_states : transl_final_statesStatement := by
  intro S R r hmatch hfinal
  cases hfinal with
  | intro r m =>
      cases hmatch with
      | match_returnstate v tv k m tm cs hs hld mext =>
          cases hs with
          | match_stacks_stop =>
              cases hld with
              | lessdef_refl =>
                  exact RTL.final_state.intro r tm

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

 theorem match_set_params_init_regs : match_set_params_init_regsStatement := by
  intro il rl s1 map2 s2 vl tvl i
  induction il generalizing rl s1 map2 s2 vl tvl i with
  | nil =>
      intro hadd hless
      change RTLgen.ret ([], RTLgen.init_mapping) s1 = .OK (rl, map2) s2 i at hadd
      simp [RTLgen.ret] at hadd
      rcases hadd with ⟨⟨hrl, hmap⟩, hs⟩
      cases hrl
      cases hmap
      cases hs
      have hset : CompCert4Lean.Backend.Cminor.set_params vl [] = PTree.empty val := by
        cases vl <;> rfl
      have hregs : RTL.init_regs tvl [] = Regmap.init Vundef := by
        cases tvl <;> rfl
      rw [hset, hregs]
      constructor
      · exact match_env_empty RTLgen.init_mapping (by rfl)
      · intro r hfresh
        exact Regmap.gi_proof val r Vundef
  | cons name names ih =>
      intro hadd hless
      change RTLgen.bind (RTLgen.add_vars RTLgen.init_mapping names)
        (fun x => RTLgen.bind (RTLgen.add_var x.2 name)
          (fun y => RTLgen.ret (y.1 :: x.1, y.2))) s1 =
        .OK (rl, map2) s2 i at hadd
      cases hrec : RTLgen.add_vars RTLgen.init_mapping names s1 with
      | Error msg => simp [RTLgen.bind, hrec] at hadd
      | OK x sm hincr =>
          cases x with
          | mk rlmid mapmid =>
              simp [RTLgen.bind, hrec] at hadd
              cases hvar : RTLgen.add_var mapmid name sm with
              | Error msg => simp [hvar] at hadd
              | OK x sn hinc =>
                  cases x with
                  | mk rnew mapnew =>
                      simp [RTLgen.ret, hvar] at hadd
                      rcases hadd with ⟨⟨hrl, hmap⟩, hs⟩
                      have hvalidmid := add_vars_valid names s1 sm RTLgen.init_mapping mapmid rlmid hincr hrec
                        (init_mapping_valid s1)
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
                          cases hless with
                          | lessdef_list_nil =>
                              have htail := ih (rl := rlmid) (s1 := s1) (map2 := { map_vars := mapVars, map_letvars := mapLetvars })
                                (s2 := sm) (i := hincr) (vl := []) (tvl := []) hrec Val.lessdef_list_nil
                              constructor
                              · constructor
                                · intro id v henv
                                  dsimp [CompCert4Lean.Backend.Cminor.set_params] at henv
                                  have hset := @PTree.getSet_equation val id name Vundef
                                    (show PTree.tree val from
                                      (CompCert4Lean.Backend.Cminor.set_params [] names))
                                  rw [hset] at henv
                                  by_cases hid : id = name
                                  · subst id
                                    simp at henv
                                    cases henv
                                    refine ⟨sm.st_nextreg, ?_, ?_⟩
                                    · change PTree.get name
                                        (PTree.set name sm.st_nextreg mapVars) = some sm.st_nextreg
                                      rw [@PTree.getSet_equation _ name name sm.st_nextreg mapVars]
                                      simp
                                    · change Val.lessdef Vundef
                                        (Regmap.get sm.st_nextreg (Regmap.init Vundef))
                                      exact Val.lessdef_undef _
                                  · simp [hid] at henv
                                    rcases htail.1.me_vars id v henv with ⟨r, hget, hless⟩
                                    refine ⟨r, ?_, ?_⟩
                                    · change PTree.get id
                                        (PTree.set name sm.st_nextreg mapVars) = some r
                                      rw [@PTree.getSet_equation _ id name sm.st_nextreg mapVars]
                                      simp [hid]
                                      exact hget
                                    · change Val.lessdef v (Regmap.get r (Regmap.init Vundef))
                                      exact hless
                                · exact htail.1.me_letvars
                              · intro r hfresh
                                change Regmap.get r (Regmap.init Vundef) = Vundef
                                exact Regmap.gi_proof val r Vundef
                          | lessdef_list_cons v tv vs ts hhead htail0 =>
                              have htail := ih (rl := rlmid) (s1 := s1) (map2 := { map_vars := mapVars, map_letvars := mapLetvars })
                                (s2 := sm) (i := hincr) (vl := vs) (tvl := ts) hrec htail0
                              constructor
                              · constructor
                                · intro id v' henv
                                  dsimp [CompCert4Lean.Backend.Cminor.set_params] at henv
                                  have hset := @PTree.getSet_equation val id name v
                                    (show PTree.tree val from
                                      (CompCert4Lean.Backend.Cminor.set_params vs names))
                                  rw [hset] at henv
                                  by_cases hid : id = name
                                  · subst id
                                    simp at henv
                                    cases henv
                                    refine ⟨sm.st_nextreg, ?_, ?_⟩
                                    · change PTree.get name
                                        (PTree.set name sm.st_nextreg mapVars) = some sm.st_nextreg
                                      rw [@PTree.getSet_equation _ name name sm.st_nextreg mapVars]
                                      simp
                                    · change Val.lessdef v
                                        (Regmap.get sm.st_nextreg
                                          (Regmap.set sm.st_nextreg tv
                                            (init_regs ts rlmid)))
                                      rw [Regmap.gss_proof val sm.st_nextreg tv
                                        (init_regs ts rlmid)]
                                      exact hhead
                                  · simp [hid] at henv
                                    rcases htail.1.me_vars id v' henv with ⟨r, hget, hless⟩
                                    refine ⟨r, ?_, ?_⟩
                                    · change PTree.get id
                                        (PTree.set name sm.st_nextreg mapVars) = some r
                                      rw [@PTree.getSet_equation _ id name sm.st_nextreg mapVars]
                                      simp [hid]
                                      exact hget
                                    · change Val.lessdef v'
                                        (Regmap.get r
                                          (Regmap.set sm.st_nextreg tv
                                            (init_regs ts rlmid)))
                                      have hrvalid : reg_valid r sm :=
                                        hvalidmid.2 r (Or.inl ⟨id, hget⟩)
                                      have hnextfresh : reg_fresh sm.st_nextreg sm := by
                                        intro hlt
                                        exact Nat.lt_irrefl _ hlt
                                      have hne : r ≠ sm.st_nextreg :=
                                        valid_fresh_different r sm.st_nextreg sm hrvalid hnextfresh
                                      rw [Regmap.gso_proof val r sm.st_nextreg tv
                                        (init_regs ts rlmid) hne]
                                      exact hless
                                · cases mapLetvars with
                                  | nil => exact Val.lessdef_list_nil
                                  | cons r rs => cases htail.1.me_letvars
                              · intro r hfresh
                                have hfresh_sm := reg_fresh_decr r sm sn hinc hfresh
                                have hnextvalid : reg_valid sm.st_nextreg sn := by
                                  rw [← hstate]
                                  unfold reg_valid
                                  change PArith.BinPos.Pos.to_nat sm.st_nextreg <
                                    PArith.BinPos.Pos.to_nat
                                      (PArith.BinPos.Pos.succ sm.st_nextreg)
                                  exact rtlgenproof_plt_succ _
                                have hne : r ≠ sm.st_nextreg := by
                                  intro heq
                                  subst r
                                  exact hfresh hnextvalid
                                change Regmap.get r
                                    (Regmap.set sm.st_nextreg tv (init_regs ts rlmid)) = Vundef
                                rw [Regmap.gso_proof val r sm.st_nextreg tv
                                  (init_regs ts rlmid) hne]
                                exact htail.2 r hfresh_sm

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

private theorem match_init_locals_aux
    (map1 : mapping) (s1 : RTLgen.state) (names : List ident)
    (rl : List reg) (map2 : mapping) (s2 : RTLgen.state)
    (e : CompCert4Lean.Backend.Cminor.env) (le : letenv) (rs : regset)
    (i : RTLgen.state_incr s1 s2)
    (hmatch : match_env map1 e le rs)
    (hadd : add_vars map1 names s1 = .OK (rl, map2) s2 i) :
    match_env map2 (CompCert4Lean.Backend.Cminor.set_locals names e) le rs := by
  induction names generalizing rl map2 s2 i with
  | nil =>
      change RTLgen.ret ([], map1) s1 = .OK (rl, map2) s2 i at hadd
      simp [RTLgen.ret] at hadd
      rcases hadd with ⟨⟨hrl, hmap⟩, hs⟩
      cases hmap
      exact hmatch
  | cons name names ih =>
      change RTLgen.bind (add_vars map1 names)
        (fun x => RTLgen.bind (add_var x.2 name)
          (fun y => RTLgen.ret (y.1 :: x.1, y.2))) s1 =
        .OK (rl, map2) s2 i at hadd
      cases hrec : add_vars map1 names s1 with
      | Error msg => simp [RTLgen.bind, hrec] at hadd
      | OK x sm hincr =>
          rcases x with ⟨rlmid, mapmid⟩
          have htail := ih rlmid mapmid sm hincr hrec
          simp [RTLgen.bind, hrec, add_var, RTLgen.ret] at hadd
          rcases hadd with ⟨rfl, rfl⟩
          constructor
          · intro id v henv
            change PTree.get id
              (PTree.set name Vundef
                (CompCert4Lean.Backend.Cminor.set_locals names e)) = some v at henv
            by_cases hid : id = name
            · subst id
              rw [@PTree.gss val name Vundef
                (CompCert4Lean.Backend.Cminor.set_locals names e)] at henv
              cases henv
              refine ⟨sm.st_nextreg, ?_, Val.lessdef_undef _⟩
              exact @PTree.gss reg name sm.st_nextreg mapmid.map_vars
            · rw [@PTree.gso val id name Vundef
                (CompCert4Lean.Backend.Cminor.set_locals names e) hid] at henv
              rcases htail.me_vars id v henv with ⟨r, hr, hv⟩
              refine ⟨r, ?_, hv⟩
              exact (@PTree.gso reg id name sm.st_nextreg mapmid.map_vars hid).trans hr
          · exact htail.me_letvars

theorem match_init_env_init_reg : match_init_env_init_regStatement := by
  intro params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams tvparams
    hparams hvars hless
  have hparams_match := match_set_params_init_regs params rparams s0 map1 s1
    vparams tvparams i1 hparams hless
  exact match_init_locals_aux map1 s1 vars rvars map2 s2 _ []
    (init_regs tvparams rparams) i2 hparams_match.1 hvars

end CompCert4Lean.Backend.RTLgenproof


namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Common.Globalenvs

theorem symbols_preserved : symbols_preservedStatement := by
  intro prog tprog hm id
  have hg := rtlgen_globalenvs_match prog tprog hm
  change Genv.find_symbol (Genv.globalenv tprog) id =
    Genv.find_symbol (Genv.globalenv prog) id
  simpa [Genv.find_symbol] using hg.mge_symb id

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

theorem function_ptr_translated : function_ptr_translatedStatement :=
  rtlgen_function_ptr_translated

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

theorem sig_transl_function : sig_transl_functionStatement :=
  rtlgen_sig_transl_fundef

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Events
open CompCert4Lean.Lib.Integers

private theorem eop_unary_total_aux (f : val → val)
    (hundef : f .Vundef = .Vundef) {a b : val} (h : Val.lessdef a b) :
    Val.lessdef (f a) (f b) := by
  cases h with
  | lessdef_refl => exact Val.lessdef_refl _
  | lessdef_undef => rw [hundef]; exact Val.lessdef_undef _

private theorem eop_binary_total_aux (f : val → val → val)
    (hleft : ∀ v, f .Vundef v = .Vundef)
    (hright : ∀ v, f v .Vundef = .Vundef)
    {a a' b b' : val} (ha : Val.lessdef a a') (hb : Val.lessdef b b') :
    Val.lessdef (f a b) (f a' b') := by
  cases ha with
  | lessdef_undef => rw [hleft]; exact Val.lessdef_undef _
  | lessdef_refl =>
      cases hb with
      | lessdef_undef => rw [hright]; exact Val.lessdef_undef _
      | lessdef_refl => exact Val.lessdef_refl _

private theorem eop_unary_partial_aux {α : Type} (f : val → Option α)
    (hundef : f .Vundef = none) {a b : val} {v : α}
    (h : Val.lessdef a b) (heval : f a = some v) : f b = some v := by
  cases h with
  | lessdef_refl => exact heval
  | lessdef_undef => rw [hundef] at heval; contradiction

private theorem eop_binary_partial_aux {α : Type} (f : val → val → Option α)
    (hleft : ∀ v, f .Vundef v = none)
    (hright : ∀ v, f v .Vundef = none)
    {a a' b b' : val} {v : α}
    (ha : Val.lessdef a a') (hb : Val.lessdef b b')
    (heval : f a b = some v) : f a' b' = some v := by
  cases ha with
  | lessdef_undef => rw [hleft] at heval; contradiction
  | lessdef_refl =>
      cases hb with
      | lessdef_undef => rw [hright] at heval; contradiction
      | lessdef_refl => exact heval

private theorem eop_valid_pointer_aux {m1 m2 : mem} (hext : Mem.extends m1 m2) :
    ∀ b ofs, Mem.valid_pointer m1 b ofs = true →
      Mem.valid_pointer m2 b ofs = true := by
  intro b ofs hp
  apply (Mem.valid_pointer_nonempty_perm m2 b ofs).2
  have h := hext.mext_inj.mi_perm b b (.Z0 : Z) ofs _ _ rfl
    ((Mem.valid_pointer_nonempty_perm m1 b ofs).1 hp)
  have hz : ZArith.BinInt.Z.add ofs .Z0 = ofs := by
    apply intOfZ_injective
    change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
    rw [intOfZ_zOfInt]
    simp
  simpa only [hz] using h

private theorem eop_condition_aux (cond : condition) (vl1 vl2 : List val)
    (b : Bool) (m1 m2 : mem) (hl : Val.lessdef_list vl1 vl2)
    (hext : Mem.extends m1 m2) (heval : eval_condition cond vl1 m1 = some b) :
    eval_condition cond vl2 m2 = some b := by
  cases cond with
  | Ccomp c =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_condition] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_condition] at heval
              | lessdef_list_nil =>
                  exact eop_binary_partial_aux (fun v1 v2 => Val.cmp_bool c v1 v2)
                    (by intro v; cases v <;> rfl) (by intro v; cases v <;> rfl)
                    h1 h2 heval
  | Ccompu c =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_condition] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_condition] at heval
              | lessdef_list_nil =>
                  exact Val.cmpu_bool_lessdef _ _ c v1 v1' v2 v2' b
                    (eop_valid_pointer_aux hext) h1 h2 heval
  | Ccompimm c n =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_condition] at heval
          | lessdef_list_nil =>
              exact eop_unary_partial_aux (fun v1 => Val.cmp_bool c v1 (.Vint n)) rfl h1 heval
  | Ccompuimm c n =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_condition] at heval
          | lessdef_list_nil =>
              exact Val.cmpu_bool_lessdef _ _ c v1 v1' (.Vint n) (.Vint n) b
                (eop_valid_pointer_aux hext) h1 (Val.lessdef_refl _) heval
  | Ccompl c =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_condition] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_condition] at heval
              | lessdef_list_nil =>
                  exact eop_binary_partial_aux (fun v1 v2 => Val.cmpl_bool c v1 v2)
                    (by intro v; cases v <;> rfl) (by intro v; cases v <;> rfl)
                    h1 h2 heval
  | Ccomplu c =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_condition] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_condition] at heval
              | lessdef_list_nil =>
                  exact Val.cmplu_bool_lessdef _ _ c v1 v1' v2 v2' b
                    (eop_valid_pointer_aux hext) h1 h2 heval
  | Ccomplimm c n =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_condition] at heval
          | lessdef_list_nil =>
              exact eop_unary_partial_aux (fun v1 => Val.cmpl_bool c v1 (.Vlong n)) rfl h1 heval
  | Ccompluimm c n =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_condition] at heval
          | lessdef_list_nil =>
              exact Val.cmplu_bool_lessdef _ _ c v1 v1' (.Vlong n) (.Vlong n) b
                (eop_valid_pointer_aux hext) h1 (Val.lessdef_refl _) heval
  | Ccompf c =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_condition] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_condition] at heval
              | lessdef_list_nil =>
                  exact eop_binary_partial_aux (fun v1 v2 => Val.cmpf_bool c v1 v2)
                    (by intro v; cases v <;> rfl) (by intro v; cases v <;> rfl)
                    h1 h2 heval
  | Cnotcompf c =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_condition] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_condition] at heval
              | lessdef_list_nil =>
                  exact eop_binary_partial_aux (fun v1 v2 => (Val.cmpf_bool c v1 v2).map (!·))
                    (by intro v; cases v <;> rfl) (by intro v; cases v <;> rfl)
                    h1 h2 heval
  | Ccompfs c =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_condition] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_condition] at heval
              | lessdef_list_nil =>
                  exact eop_binary_partial_aux (fun v1 v2 => Val.cmpfs_bool c v1 v2)
                    (by intro v; cases v <;> rfl) (by intro v; cases v <;> rfl)
                    h1 h2 heval
  | Cnotcompfs c =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_condition] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_condition] at heval
              | lessdef_list_nil =>
                  exact eop_binary_partial_aux (fun v1 v2 => (Val.cmpfs_bool c v1 v2).map (!·))
                    (by intro v; cases v <;> rfl) (by intro v; cases v <;> rfl)
                    h1 h2 heval
  | Cmaskzero n =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_condition] at heval
          | lessdef_list_nil =>
              exact eop_unary_partial_aux (fun v1 => Val.maskzero_bool v1 n) rfl h1 heval
  | Cmasknotzero n =>
      cases hl with
      | lessdef_list_nil => simp [eval_condition] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_condition] at heval
          | lessdef_list_nil =>
              exact eop_unary_partial_aux (fun v1 => (Val.maskzero_bool v1 n).map (!·)) rfl h1 heval

private theorem eop_addressing32_aux {F V : Type} (ge : Genv.t F V)
    (sp : val) (addr : addressing) (vl1 vl2 : List val) (v : val)
    (hl : Val.lessdef_list vl1 vl2) (heval : eval_addressing32 ge sp addr vl1 = some v) :
    ∃ v', eval_addressing32 ge sp addr vl2 = some v' ∧ Val.lessdef v v' := by
  cases addr with
  | Aindexed n =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | lessdef_list_nil =>
              simp only [eval_addressing32, Option.some.injEq] at heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => Val.add v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr n))) rfl h1
  | Aindexed2 n =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
              | lessdef_list_nil =>
                  simp only [eval_addressing32, Option.some.injEq] at heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => Val.add (Val.add v1 v2) (.Vint (CompCert4Lean.Lib.Integers.Int.repr n)))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Ascaled scale ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | lessdef_list_nil =>
              simp only [eval_addressing32, Option.some.injEq] at heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => Val.add         (Val.mul v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr scale)))         (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))) rfl h1
  | Aindexed2scaled scale ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
              | lessdef_list_nil =>
                  simp only [eval_addressing32, Option.some.injEq] at heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => Val.add v1         (Val.add           (Val.mul v2 (.Vint (CompCert4Lean.Lib.Integers.Int.repr scale)))           (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Aglobal id ofs =>
      cases hl with
      | lessdef_list_cons => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_nil =>
          simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
  | Abased id ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | lessdef_list_nil =>
              simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
  | Abasedscaled scale id ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | lessdef_list_nil =>
              simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
  | Ainstack ofs =>
      cases hl with
      | lessdef_list_cons => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_nil =>
          simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval

private theorem eop_addressing64_aux {F V : Type} (ge : Genv.t F V)
    (sp : val) (addr : addressing) (vl1 vl2 : List val) (v : val)
    (hl : Val.lessdef_list vl1 vl2) (heval : eval_addressing64 ge sp addr vl1 = some v) :
    ∃ v', eval_addressing64 ge sp addr vl2 = some v' ∧ Val.lessdef v v' := by
  cases addr with
  | Aindexed n =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | lessdef_list_nil =>
              simp only [eval_addressing64, Option.some.injEq] at heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => Val.addl v1 (.Vlong (Int64.repr n))) rfl h1
  | Aindexed2 n =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
              | lessdef_list_nil =>
                  simp only [eval_addressing64, Option.some.injEq] at heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => Val.addl (Val.addl v1 v2) (.Vlong (Int64.repr n)))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Ascaled scale ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | lessdef_list_nil =>
              simp only [eval_addressing64, Option.some.injEq] at heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => Val.addl (Val.mull v1 (.Vlong (Int64.repr scale)))         (.Vlong (Int64.repr ofs))) rfl h1
  | Aindexed2scaled scale ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
              | lessdef_list_nil =>
                  simp only [eval_addressing64, Option.some.injEq] at heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => Val.addl v1         (Val.addl (Val.mull v2 (.Vlong (Int64.repr scale)))           (.Vlong (Int64.repr ofs))))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Aglobal id ofs =>
      cases hl with
      | lessdef_list_cons => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_nil =>
          simp only [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64, if_true, Option.some.injEq] at heval
          subst v
          exact ⟨_, rfl, Val.lessdef_refl _⟩
  | Ainstack ofs =>
      cases hl with
      | lessdef_list_cons => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_nil =>
          simp only [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64, if_true, Option.some.injEq] at heval
          subst v
          exact ⟨_, rfl, Val.lessdef_refl _⟩
  | Abased id ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 <;> simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
  | Abasedscaled scale id ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 <;> simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval

set_option maxHeartbeats 2000000 in
private theorem eop_operation_aux
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    {F V : Type} (ge : Genv.t F V) (sp : val) (op : operation)
    (vl1 vl2 : List val) (v : val) (m1 m2 : mem)
    (hl : Val.lessdef_list vl1 vl2) (hext : Mem.extends m1 m2)
    (heval : eval_operation ge sp op vl1 m1 = some v) :
    ∃ v', eval_operation ge sp op vl2 m2 = some v' ∧ Val.lessdef v v' := by
  cases op with
  | Omove =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : v1 = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => v1) rfl h1
  | Ointconst n =>
      cases hl with
      | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_nil =>
          have hv : (.Vint n) = v := Option.some.inj heval
          subst v
          exact ⟨_, rfl, Val.lessdef_refl _⟩
  | Olongconst n =>
      cases hl with
      | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_nil =>
          have hv : (.Vlong n) = v := Option.some.inj heval
          subst v
          exact ⟨_, rfl, Val.lessdef_refl _⟩
  | Ofloatconst n =>
      cases hl with
      | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_nil =>
          have hv : (.Vfloat n) = v := Option.some.inj heval
          subst v
          exact ⟨_, rfl, Val.lessdef_refl _⟩
  | Osingleconst n =>
      cases hl with
      | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_nil =>
          have hv : (.Vsingle n) = v := Option.some.inj heval
          subst v
          exact ⟨_, rfl, Val.lessdef_refl _⟩
  | Oindirectsymbol id =>
      cases hl with
      | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_nil =>
          have hv : (Genv.symbol_address ge id Ptrofs.zero) = v := Option.some.inj heval
          subst v
          exact ⟨_, rfl, Val.lessdef_refl _⟩
  | Ocast8signed =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.sign_ext (zOfNat 8) v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.sign_ext (zOfNat 8) v1)) rfl h1
  | Ocast8unsigned =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.zero_ext (zOfNat 8) v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.zero_ext (zOfNat 8) v1)) rfl h1
  | Ocast16signed =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.sign_ext (zOfNat 16) v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.sign_ext (zOfNat 16) v1)) rfl h1
  | Ocast16unsigned =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.zero_ext (zOfNat 16) v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.zero_ext (zOfNat 16) v1)) rfl h1
  | Oneg =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.neg v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.neg v1)) rfl h1
  | Osub =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.sub v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.sub v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Omul =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.mul v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.mul v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Omulimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.mul v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.mul v1 (.Vint n))) rfl h1
  | Omulhs =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.mulhs v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.mulhs v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Omulhu =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.mulhu v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.mulhu v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Odiv =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  refine ⟨v, ?_, Val.lessdef_refl _⟩
                  exact eop_binary_partial_aux (fun v1 v2 => Val.divs v1 v2)
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2 heval
  | Odivu =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  refine ⟨v, ?_, Val.lessdef_refl _⟩
                  exact eop_binary_partial_aux (fun v1 v2 => Val.divu v1 v2)
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2 heval
  | Omod =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  refine ⟨v, ?_, Val.lessdef_refl _⟩
                  exact eop_binary_partial_aux (fun v1 v2 => Val.mods v1 v2)
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2 heval
  | Omodu =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  refine ⟨v, ?_, Val.lessdef_refl _⟩
                  exact eop_binary_partial_aux (fun v1 v2 => Val.modu v1 v2)
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2 heval
  | Oand =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.and v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.and v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oandimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.and v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.and v1 (.Vint n))) rfl h1
  | Oor =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.or v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.or v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oorimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.or v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.or v1 (.Vint n))) rfl h1
  | Oxor =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.xor v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.xor v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oxorimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.xor v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.xor v1 (.Vint n))) rfl h1
  | Onot =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.notint v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.notint v1)) rfl h1
  | Oshl =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.shl v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.shl v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oshlimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.shl v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.shl v1 (.Vint n))) rfl h1
  | Oshr =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.shr v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.shr v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oshrimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.shr v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.shr v1 (.Vint n))) rfl h1
  | Oshrximm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              refine ⟨v, ?_, Val.lessdef_refl _⟩
              exact eop_unary_partial_aux (fun v1 => Val.shrx v1 (.Vint n)) rfl h1 heval
  | Oshru =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.shru v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.shru v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oshruimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.shru v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.shru v1 (.Vint n))) rfl h1
  | Ororimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.ror v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.ror v1 (.Vint n))) rfl h1
  | Oshldimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.or (Val.shl v1 (.Vint n)) (Val.shru v2 (.Vint (CompCert4Lean.Lib.Integers.Int.sub CompCert4Lean.Lib.Integers.Int.iwordsize n)))) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.or (Val.shl v1 (.Vint n)) (Val.shru v2 (.Vint (CompCert4Lean.Lib.Integers.Int.sub CompCert4Lean.Lib.Integers.Int.iwordsize n)))))
                    (by intro x; cases x <;> rfl)
                    (by intro x; cases x <;> simp [Val.shl, Val.shru, Val.or] <;> split <;> rfl) h1 h2
  | Olea addr =>
      exact eop_addressing32_aux ge sp addr vl1 vl2 v hl heval
  | Omakelong =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.longofwords v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.longofwords v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Olowlong =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.loword v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.loword v1)) rfl h1
  | Ohighlong =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.hiword v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.hiword v1)) rfl h1
  | Ocast32signed =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.longofint v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.longofint v1)) rfl h1
  | Ocast32unsigned =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.longofintu v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.longofintu v1)) rfl h1
  | Onegl =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.negl v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.negl v1)) rfl h1
  | Oaddlimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.addl v1 (.Vlong n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.addl v1 (.Vlong n))) rfl h1
  | Osubl =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.subl v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.subl v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Omull =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.mull v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.mull v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Omullimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.mull v1 (.Vlong n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.mull v1 (.Vlong n))) rfl h1
  | Omullhs =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.mullhs v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.mullhs v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Omullhu =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.mullhu v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.mullhu v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Odivl =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  refine ⟨v, ?_, Val.lessdef_refl _⟩
                  exact eop_binary_partial_aux (fun v1 v2 => Val.divls v1 v2)
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2 heval
  | Odivlu =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  refine ⟨v, ?_, Val.lessdef_refl _⟩
                  exact eop_binary_partial_aux (fun v1 v2 => Val.divlu v1 v2)
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2 heval
  | Omodl =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  refine ⟨v, ?_, Val.lessdef_refl _⟩
                  exact eop_binary_partial_aux (fun v1 v2 => Val.modls v1 v2)
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2 heval
  | Omodlu =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  refine ⟨v, ?_, Val.lessdef_refl _⟩
                  exact eop_binary_partial_aux (fun v1 v2 => Val.modlu v1 v2)
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2 heval
  | Oandl =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.andl v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.andl v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oandlimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.andl v1 (.Vlong n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.andl v1 (.Vlong n))) rfl h1
  | Oorl =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.orl v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.orl v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oorlimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.orl v1 (.Vlong n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.orl v1 (.Vlong n))) rfl h1
  | Oxorl =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.xorl v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.xorl v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oxorlimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.xorl v1 (.Vlong n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.xorl v1 (.Vlong n))) rfl h1
  | Onotl =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.notl v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.notl v1)) rfl h1
  | Oshll =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.shll v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.shll v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oshllimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.shll v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.shll v1 (.Vint n))) rfl h1
  | Oshrl =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.shrl v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.shrl v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oshrlimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.shrl v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.shrl v1 (.Vint n))) rfl h1
  | Oshrxlimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              refine ⟨v, ?_, Val.lessdef_refl _⟩
              exact eop_unary_partial_aux (fun v1 => Val.shrxl v1 (.Vint n)) rfl h1 heval
  | Oshrlu =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.shrlu v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.shrlu v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Oshrluimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.shrlu v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.shrlu v1 (.Vint n))) rfl h1
  | Ororlimm n =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.rorl v1 (.Vint n)) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.rorl v1 (.Vint n))) rfl h1
  | Oleal addr =>
      exact eop_addressing64_aux ge sp addr vl1 vl2 v hl heval
  | Onegf =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.negf v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.negf v1)) rfl h1
  | Oabsf =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.absf v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.absf v1)) rfl h1
  | Oaddf =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.addf v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.addf v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Osubf =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.subf v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.subf v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Omulf =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.mulf v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.mulf v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Odivf =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.divf v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.divf v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Omaxf =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (maxf v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (maxf v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Ominf =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (minf v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (minf v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Onegfs =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.negfs v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.negfs v1)) rfl h1
  | Oabsfs =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.absfs v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.absfs v1)) rfl h1
  | Oaddfs =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.addfs v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.addfs v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Osubfs =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.subfs v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.subfs v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Omulfs =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.mulfs v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.mulfs v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Odivfs =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
              | lessdef_list_nil =>
                  have hv : (Val.divfs v1 v2) = v := Option.some.inj heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact eop_binary_total_aux (fun v1 v2 => (Val.divfs v1 v2))
                    (by intro x; cases x <;> rfl) (by intro x; cases x <;> rfl) h1 h2
  | Osingleoffloat =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.singleoffloat v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.singleoffloat v1)) rfl h1
  | Ofloatofsingle =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              have hv : (Val.floatofsingle v1) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact eop_unary_total_aux (fun v1 => (Val.floatofsingle v1)) rfl h1
  | Ointoffloat =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              refine ⟨v, ?_, Val.lessdef_refl _⟩
              exact eop_unary_partial_aux (fun v1 => Val.intoffloat v1) rfl h1 heval
  | Ofloatofint =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              refine ⟨v, ?_, Val.lessdef_refl _⟩
              exact eop_unary_partial_aux (fun v1 => Val.floatofint (binary64_certificate := binary64_certificate) v1) rfl h1 heval
  | Ointofsingle =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              refine ⟨v, ?_, Val.lessdef_refl _⟩
              exact eop_unary_partial_aux (fun v1 => Val.intofsingle v1) rfl h1 heval
  | Osingleofint =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              refine ⟨v, ?_, Val.lessdef_refl _⟩
              exact eop_unary_partial_aux (fun v1 => Val.singleofint (binary32_certificate := binary32_certificate) v1) rfl h1 heval
  | Olongoffloat =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              refine ⟨v, ?_, Val.lessdef_refl _⟩
              exact eop_unary_partial_aux (fun v1 => Val.longoffloat v1) rfl h1 heval
  | Ofloatoflong =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              refine ⟨v, ?_, Val.lessdef_refl _⟩
              exact eop_unary_partial_aux (fun v1 => Val.floatoflong (binary64_certificate := binary64_certificate) v1) rfl h1 heval
  | Olongofsingle =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              refine ⟨v, ?_, Val.lessdef_refl _⟩
              exact eop_unary_partial_aux (fun v1 => Val.longofsingle v1) rfl h1 heval
  | Osingleoflong =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_nil =>
              refine ⟨v, ?_, Val.lessdef_refl _⟩
              exact eop_unary_partial_aux (fun v1 => Val.singleoflong (binary32_certificate := binary32_certificate) v1) rfl h1 heval
  | Ocmp c =>
      have hv : (Val.of_optbool (eval_condition c vl1 m1)) = v := Option.some.inj heval
      subst v
      refine ⟨_, rfl, ?_⟩
      exact Val.of_optbool_lessdef _ _ (fun b hb =>
        eop_condition_aux c vl1 vl2 b m1 m2 hl hext hb)
  | Osel c ty =>
      cases hl with
      | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => have hn : (none : Option val) = some v := heval; cases hn
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              have hv : (Val.select (eval_condition c l2 m1) v1 v2 ty) = v := Option.some.inj heval
              subst v
              refine ⟨_, rfl, ?_⟩
              cases hc : eval_condition c l2 m1 with
              | none => simp only [Val.select, hc]; exact Val.lessdef_undef _
              | some b =>
                  have hc' := eop_condition_aux c l2 l2' b m1 m2 ht2 hext hc
                  simp only [Val.select, hc, hc']
                  apply Val.normalize_lessdef
                  cases b
                  · exact h2
                  · exact h1

theorem transl_expr_Eop_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_expr_Eop_correctStatement := by
  intro xi prog tprog hprog sp e m le op args vargs v hevalargs htransargs heval
  unfold transl_expr_prop
  intro tge tm cs f map pr ns nd rd rs dst hwf htr hmatch hext
  cases htr with
  | tr_Eop map pr op args ns nd rd n1 rl dst hargs hcode hmap hpr =>
      obtain ⟨rs1, tm1, hstar, hmatch1, hresults, hstable, hext1⟩ :=
        htransargs tm cs f map pr ns n1 rl rs hwf hargs hmatch hext
      obtain ⟨v', heval', hless⟩ := eop_operation_aux (Genv.globalenv prog) sp op
        vargs (rl.map (fun r => Regmap.get r rs1)) v m tm1 hresults hext1 heval
      have hevalt : eval_operation tge sp op
          (rl.map (fun r => Regmap.get r rs1)) tm1 = some v' := by
        rw [eval_operation_preserved _ _ _ _ (Genv.globalenv prog) tge
          (symbols_preserved prog tprog hprog)]
        exact heval'
      refine ⟨Regmap.set rd v' rs1, tm1, ?_, ?_, ?_, ?_, hext1⟩
      · exact star_right _ _ _ _ _ _ _ _ _ _ hstar
          (RTL.step.exec_Iop cs f sp n1 rs1 tm1 op rl rd nd v' hcode hevalt) rfl
      · exact match_env_update_dest map e le rs1 dst rd v v'
          hless hwf hmap hmatch1
      · rw [Regmap.gss_proof val rd v' rs1]
        exact hless
      · intro r hr
        have hne : r ≠ rd := by
          intro heq
          subst r
          exact hpr hr
        rw [Regmap.gso_proof val r rd v' rs1 hne]
        exact hstable r hr

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem rtlgen_unary_total_aux (f : val → val)
    (hundef : f .Vundef = .Vundef) {a b : val} (h : Val.lessdef a b) :
    Val.lessdef (f a) (f b) := by
  cases h with
  | lessdef_refl => exact Val.lessdef_refl _
  | lessdef_undef => rw [hundef]; exact Val.lessdef_undef _

private theorem rtlgen_binary_total_aux (f : val → val → val)
    (hleft : ∀ v, f .Vundef v = .Vundef)
    (hright : ∀ v, f v .Vundef = .Vundef)
    {a a' b b' : val} (ha : Val.lessdef a a') (hb : Val.lessdef b b') :
    Val.lessdef (f a b) (f a' b') := by
  cases ha with
  | lessdef_undef => rw [hleft]; exact Val.lessdef_undef _
  | lessdef_refl =>
      cases hb with
      | lessdef_undef => rw [hright]; exact Val.lessdef_undef _
      | lessdef_refl => exact Val.lessdef_refl _

private theorem rtlgen_eop_addressing64_aux {F V : Type} (ge : Genv.t F V)
    (sp : val) (addr : addressing) (vl1 vl2 : List val) (v : val)
    (hl : Val.lessdef_list vl1 vl2)
    (heval : eval_addressing64 ge sp addr vl1 = some v) :
    ∃ v', eval_addressing64 ge sp addr vl2 = some v' ∧ Val.lessdef v v' := by
  cases addr with
  | Aindexed n =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_addressing64] at heval
          | lessdef_list_nil =>
              simp only [eval_addressing64, Option.some.injEq] at heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact rtlgen_unary_total_aux
                (fun v1 => Val.addl v1 (.Vlong (Int64.repr n))) rfl h1
  | Aindexed2 n =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_addressing64] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_addressing64] at heval
              | lessdef_list_nil =>
                  simp only [eval_addressing64, Option.some.injEq] at heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact rtlgen_binary_total_aux
                    (fun v1 v2 => Val.addl (Val.addl v1 v2)
                      (.Vlong (Int64.repr n)))
                    (by intro x; cases x <;> rfl)
                    (by intro x; cases x <;> rfl) h1 h2
  | Ascaled scale ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_cons => simp [eval_addressing64] at heval
          | lessdef_list_nil =>
              simp only [eval_addressing64, Option.some.injEq] at heval
              subst v
              refine ⟨_, rfl, ?_⟩
              exact rtlgen_unary_total_aux
                (fun v1 => Val.addl (Val.mull v1 (.Vlong (Int64.repr scale)))
                  (.Vlong (Int64.repr ofs))) rfl h1
  | Aindexed2scaled scale ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 with
          | lessdef_list_nil => simp [eval_addressing64] at heval
          | lessdef_list_cons v2 v2' l2 l2' h2 ht2 =>
              cases ht2 with
              | lessdef_list_cons => simp [eval_addressing64] at heval
              | lessdef_list_nil =>
                  simp only [eval_addressing64, Option.some.injEq] at heval
                  subst v
                  refine ⟨_, rfl, ?_⟩
                  exact rtlgen_binary_total_aux
                    (fun v1 v2 => Val.addl v1
                      (Val.addl (Val.mull v2 (.Vlong (Int64.repr scale)))
                        (.Vlong (Int64.repr ofs))))
                    (by intro x; cases x <;> rfl)
                    (by intro x; cases x <;> rfl) h1 h2
  | Aglobal id ofs =>
      cases hl with
      | lessdef_list_cons => simp [eval_addressing64] at heval
      | lessdef_list_nil =>
          simp only [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64,
            if_true, Option.some.injEq] at heval
          subst v
          exact ⟨_, rfl, Val.lessdef_refl _⟩
  | Ainstack ofs =>
      cases hl with
      | lessdef_list_cons => simp [eval_addressing64] at heval
      | lessdef_list_nil =>
          simp only [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64,
            if_true, Option.some.injEq] at heval
          subst v
          exact ⟨_, rfl, Val.lessdef_refl _⟩
  | Abased id ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 <;> simp [eval_addressing64] at heval
  | Abasedscaled scale id ofs =>
      cases hl with
      | lessdef_list_nil => simp [eval_addressing64] at heval
      | lessdef_list_cons v1 v1' l1 l1' h1 ht1 =>
          cases ht1 <;> simp [eval_addressing64] at heval

private theorem rtlgen_eval_addressing_lessdef {F V : Type}
    (ge : Genv.t F V) (sp : val) (addr : addressing)
    (vl1 vl2 : List val) (v : val) :
    Val.lessdef_list vl1 vl2 →
    eval_addressing ge sp addr vl1 = some v →
    ∃ v', eval_addressing ge sp addr vl2 = some v' ∧ Val.lessdef v v' := by
  intro hvals heval
  simp only [eval_addressing, CompCert4Lean.X86_64.Archi.ptr64,
    ↓reduceIte] at heval ⊢
  exact rtlgen_eop_addressing64_aux ge sp addr vl1 vl2 v hvals heval

private theorem rtlgen_loadv_extends
    (chunk : memory_chunk) (m1 m2 : mem) (addr1 addr2 v1 : val) :
    Mem.extends m1 m2 →
    Mem.loadv chunk m1 addr1 = some v1 →
    Val.lessdef addr1 addr2 →
    ∃ v2, Mem.loadv chunk m2 addr2 = some v2 ∧ Val.lessdef v1 v2 := by
  intro hext hload haddr
  cases addr1 with
  | Vundef => simp [Mem.loadv] at hload
  | Vint n => cases haddr; simp [Mem.loadv] at hload
  | Vlong n => cases haddr; simp [Mem.loadv] at hload
  | Vfloat n => cases haddr; simp [Mem.loadv] at hload
  | Vsingle n => cases haddr; simp [Mem.loadv] at hload
  | Vptr b ofs =>
      cases haddr with
      | lessdef_refl _ =>
          simp only [Mem.loadv] at hload ⊢
          obtain ⟨v2, hload2, hless⟩ :=
            Mem.load_extends chunk m1 m2 b (Ptrofs.unsigned ofs) v1 hext hload
          exact ⟨v2, hload2, hless⟩

theorem transl_expr_Eload_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_expr_Eload_correctStatement := by
  intro xi prog tprog hprog sp e m le chunk addr args vargs vaddr v
    hevalargs htransargs haddr hload
  unfold transl_expr_prop
  intro tge tm cs f map pr ns nd rd rs dst hwf htr hmatch hext
  cases htr with
  | tr_Eload map pr chunk addr args ns nd rd n1 rl dst hargs hcode hmap hpr =>
      obtain ⟨rs1, tm1, hstar, hmatch1, hresults, hstable, hext1⟩ :=
        htransargs tm cs f map pr ns n1 rl rs hwf hargs hmatch hext
      obtain ⟨vaddr', haddr', hlessaddr⟩ :=
        rtlgen_eval_addressing_lessdef (Genv.globalenv prog) sp addr vargs
          (rl.map (fun r => Regmap.get r rs1)) vaddr hresults haddr
      obtain ⟨v', hload', hless⟩ :=
        rtlgen_loadv_extends chunk m tm1 vaddr vaddr' v hext1 hload hlessaddr
      have haddr'' : eval_addressing tge sp addr
          (rl.map (fun r => Regmap.get r rs1)) = some vaddr' := by
        rw [eval_addressing_preserved _ _ _ _ (Genv.globalenv prog) tge
          (symbols_preserved prog tprog hprog)]
        exact haddr'
      refine ⟨Regmap.set rd v' rs1, tm1, ?_, ?_, ?_, ?_, hext1⟩
      · exact star_right _ _ _ _ _ _ _ _ _ _ hstar
          (RTL.step.exec_Iload cs f sp n1 rs1 tm1 chunk addr rl rd nd vaddr' v'
            hcode haddr'' hload') rfl
      · exact match_env_update_dest map e le rs1 dst rd v v'
          hless hwf hmap hmatch1
      · rw [Regmap.gss_proof val rd v' rs1]
        exact hless
      · intro r hr
        have hne : r ≠ rd := by
          intro heq
          subst r
          exact hpr hr
        rw [Regmap.gso_proof val r rd v' rs1 hne]
        exact hstable r hr

end CompCert4Lean.Backend.RTLgenproof

namespace CompCert4Lean.Backend.RTLgenproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.Backend.RTLgenspec
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op

theorem transl_condexpr_CEcond_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_condexpr_CEcond_correctStatement := by
  intro xi prog tprog sp e m le cond al vl vb
    hevalargs htransargs hevalcond
  unfold transl_condexpr_prop
  intro tge tm cs f map pr ns ntrue nfalse rs hwf htr hmatch hext
  cases htr with
  | tr_CEcond map pr cond al ns ntrue nfalse n1 rl hargs hcode =>
      obtain ⟨rs1, tm1, hstar, hmatch1, hresults, hstable, hext1⟩ :=
        htransargs tm cs f map pr ns n1 rl rs hwf hargs hmatch hext
      have hevalcond' : eval_condition cond
          (rl.map (fun r => Regmap.get r rs1)) tm1 = some vb := by
        exact eval_condition_lessdef cond vl
          (rl.map (fun r => Regmap.get r rs1)) vb m tm1 hresults hext1 hevalcond
      refine ⟨rs1, tm1, ?_, hmatch1, ?_, hext1⟩
      · apply plus_right _ _ _ _ _ _ _ _ _ _ hstar
        · exact RTL.step.exec_Icond cs f sp n1 rs1 tm1 cond rl ntrue nfalse vb
            (if vb then ntrue else nfalse) hcode hevalcond' rfl
        · rfl
      · intro r hr
        exact hstable r hr

end CompCert4Lean.Backend.RTLgenproof
