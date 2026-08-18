import CompCert4Lean.Backend.Cminor
import CompCert4Lean.Common.Unityping

/-!
# Cminor type checking

Definition-bearing translation of CompCert's `backend/Cminortyping.v`.
Proofs assigned to later migration are represented by exact proposition
descriptors.
-/

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Unityping
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Cminor

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private def rocqStringOfBytes : List UInt8 → RocqString
  | [] => .EmptyString
  | byte :: rest => .String byte (rocqStringOfBytes rest)

private def typeMismatchText : RocqString :=
  rocqStringOfBytes [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104]

private def arityMismatchText : RocqString :=
  rocqStringOfBytes [97, 114, 105, 116, 121, 32, 109, 105, 115, 109, 97, 116, 99, 104]

private def typEq (x y : typ) : Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

private def cminorTypeAlgebra : TYPE_ALGEBRA where
  t := typ
  eq := typEq
  default := Tint

private abbrev InferEnv := UniSolver.typenv cminorTypeAlgebra
private abbrev TypeAssign := UniSolver.typassign cminorTypeAlgebra

/-! ## Type inference -/

def type_constant : constant → typ
  | .Ointconst _ => Tint
  | .Ofloatconst _ => Tfloat
  | .Osingleconst _ => Tsingle
  | .Olongconst _ => Tlong
  | .Oaddrsymbol _ _ => Tptr
  | .Oaddrstack _ => Tptr

def type_unop : unary_operation → typ × typ
  | .Ocast8unsigned | .Ocast8signed | .Ocast16unsigned | .Ocast16signed
  | .Onegint | .Onotint => (Tint, Tint)
  | .Onegf | .Oabsf => (Tfloat, Tfloat)
  | .Onegfs | .Oabsfs => (Tsingle, Tsingle)
  | .Osingleoffloat => (Tfloat, Tsingle)
  | .Ofloatofsingle => (Tsingle, Tfloat)
  | .Ointoffloat | .Ointuoffloat => (Tfloat, Tint)
  | .Ofloatofint | .Ofloatofintu => (Tint, Tfloat)
  | .Ointofsingle | .Ointuofsingle => (Tsingle, Tint)
  | .Osingleofint | .Osingleofintu => (Tint, Tsingle)
  | .Onegl | .Onotl => (Tlong, Tlong)
  | .Ointoflong => (Tlong, Tint)
  | .Olongofint | .Olongofintu => (Tint, Tlong)
  | .Olongoffloat | .Olonguoffloat => (Tfloat, Tlong)
  | .Ofloatoflong | .Ofloatoflongu => (Tlong, Tfloat)
  | .Olongofsingle | .Olonguofsingle => (Tsingle, Tlong)
  | .Osingleoflong | .Osingleoflongu => (Tlong, Tsingle)

def type_binop : binary_operation → (typ × typ) × typ
  | .Oadd | .Osub | .Omul | .Odiv | .Odivu | .Omod | .Omodu
  | .Oand | .Oor | .Oxor | .Oshl | .Oshr | .Oshru => ((Tint, Tint), Tint)
  | .Oaddf | .Osubf | .Omulf | .Odivf => ((Tfloat, Tfloat), Tfloat)
  | .Oaddfs | .Osubfs | .Omulfs | .Odivfs => ((Tsingle, Tsingle), Tsingle)
  | .Oaddl | .Osubl | .Omull | .Odivl | .Odivlu | .Omodl | .Omodlu
  | .Oandl | .Oorl | .Oxorl => ((Tlong, Tlong), Tlong)
  | .Oshll | .Oshrl | .Oshrlu => ((Tlong, Tint), Tlong)
  | .Ocmp _ | .Ocmpu _ => ((Tint, Tint), Tint)
  | .Ocmpf _ => ((Tfloat, Tfloat), Tint)
  | .Ocmpfs _ => ((Tsingle, Tsingle), Tint)
  | .Ocmpl _ | .Ocmplu _ => ((Tlong, Tlong), Tint)

def expect (e : InferEnv) (t1 t2 : typ) : res InferEnv :=
  match typEq t1 t2 with
  | .left _ => OK e
  | .right _ => Error (msg typeMismatchText)

def type_expr : InferEnv → expr → typ → res InferEnv
  | e, .Evar id, t => UniSolver.set cminorTypeAlgebra e id t
  | e, .Econst c, t => expect e (type_constant c) t
  | e, .Eunop op a1, t =>
      let (targ1, tres) := type_unop op
      match type_expr e a1 targ1 with
      | Error message => Error message
      | OK e1 => expect e1 tres t
  | e, .Ebinop op a1 a2, t =>
      let ((targ1, targ2), tres) := type_binop op
      match type_expr e a1 targ1 with
      | Error message => Error message
      | OK e1 =>
          match type_expr e1 a2 targ2 with
          | Error message => Error message
          | OK e2 => expect e2 tres t
  | e, .Eload chunk a1, t =>
      match type_expr e a1 Tptr with
      | Error message => Error message
      | OK e1 => expect e1 (type_of_chunk chunk) t

def type_exprlist : InferEnv → List expr → List typ → res InferEnv
  | e, [], [] => OK e
  | e, a :: al, t :: tl =>
      match type_expr e a t with
      | Error message => Error message
      | OK e1 => type_exprlist e1 al tl
  | _, _, _ => Error (msg arityMismatchText)

def type_assign (e : InferEnv) (id : ident) (a : expr) : res InferEnv :=
  match a with
  | .Evar id' =>
      match UniSolver.move cminorTypeAlgebra e id id' with
      | Error message => Error message
      | OK (_, e1) => OK e1
  | .Econst c => UniSolver.set cminorTypeAlgebra e id (type_constant c)
  | .Eunop op a1 =>
      let (targ1, tres) := type_unop op
      match type_expr e a1 targ1 with
      | Error message => Error message
      | OK e1 => UniSolver.set cminorTypeAlgebra e1 id tres
  | .Ebinop op a1 a2 =>
      let ((targ1, targ2), tres) := type_binop op
      match type_expr e a1 targ1 with
      | Error message => Error message
      | OK e1 =>
          match type_expr e1 a2 targ2 with
          | Error message => Error message
          | OK e2 => UniSolver.set cminorTypeAlgebra e2 id tres
  | .Eload chunk a1 =>
      match type_expr e a1 Tptr with
      | Error message => Error message
      | OK e1 => UniSolver.set cminorTypeAlgebra e1 id (type_of_chunk chunk)

def opt_set (e : InferEnv) (optid : Option ident) (ty : typ) : res InferEnv :=
  match optid with
  | none => OK e
  | some id => UniSolver.set cminorTypeAlgebra e id ty

def type_stmt (tret : xtype) : InferEnv → stmt → res InferEnv
  | e, .Sskip => OK e
  | e, .Sassign id a => type_assign e id a
  | e, .Sstore chunk a1 a2 =>
      match type_expr e a1 Tptr with
      | Error message => Error message
      | OK e1 => type_expr e1 a2 (type_of_chunk chunk)
  | e, .Scall optid sg fn args =>
      match type_expr e fn Tptr with
      | Error message => Error message
      | OK e1 =>
          match type_exprlist e1 args (proj_sig_args sg) with
          | Error message => Error message
          | OK e2 => opt_set e2 optid (proj_sig_res sg)
  | e, .Stailcall sg fn args =>
      if sg.sig_res = tret then
        match type_expr e fn Tptr with
        | Error message => Error message
        | OK e1 => type_exprlist e1 args (proj_sig_args sg)
      else
        assertion_failed
  | e, .Sbuiltin optid ef args =>
      let sg := ef_sig ef
      match type_exprlist e args (proj_sig_args sg) with
      | Error message => Error message
      | OK e1 => opt_set e1 optid (proj_sig_res sg)
  | e, .Sseq s1 s2 =>
      match type_stmt tret e s1 with
      | Error message => Error message
      | OK e1 => type_stmt tret e1 s2
  | e, .Sifthenelse a s1 s2 =>
      match type_expr e a Tint with
      | Error message => Error message
      | OK e1 =>
          match type_stmt tret e1 s1 with
          | Error message => Error message
          | OK e2 => type_stmt tret e2 s2
  | e, .Sloop s => type_stmt tret e s
  | e, .Sblock s => type_stmt tret e s
  | e, .Sexit _ => OK e
  | e, .Sswitch isLong a _ _ =>
      type_expr e a (if isLong then Tlong else Tint)
  | e, .Sreturn none => OK e
  | e, .Sreturn (some a) => type_expr e a (proj_xtype tret)
  | e, .Slabel _ s => type_stmt tret e s
  | e, .Sgoto _ => OK e

def typenv := ident → typ

def type_function (f : function) : res typenv :=
  match UniSolver.set_list cminorTypeAlgebra (UniSolver.initial cminorTypeAlgebra)
      f.fn_params (proj_sig_args f.fn_sig) with
  | Error message => Error message
  | OK e1 =>
      match type_stmt f.fn_sig.sig_res e1 f.fn_body with
      | Error message => Error message
      | OK e2 => UniSolver.solve cminorTypeAlgebra e2

/-! ## Relational specification -/

def wt_expr (env : typenv) : expr → typ → Prop
  | .Evar id, t => t = env id
  | .Econst c, t => t = type_constant c
  | .Eunop op a1, t =>
      ∃ targ1 tres,
        type_unop op = (targ1, tres) ∧ wt_expr env a1 targ1 ∧ t = tres
  | .Ebinop op a1 a2, t =>
      ∃ targ1 targ2 tres,
        type_binop op = ((targ1, targ2), tres) ∧
          wt_expr env a1 targ1 ∧ wt_expr env a2 targ2 ∧ t = tres
  | .Eload chunk a1, t => wt_expr env a1 Tptr ∧ t = type_of_chunk chunk

def wt_opt_assign (env : typenv) (optid : Option ident) (ty : xtype) : Prop :=
  match optid with
  | some id => proj_xtype ty = env id
  | none => True

def wt_stmt (env : typenv) (tret : xtype) : stmt → Prop
  | .Sskip => True
  | .Sassign id a => wt_expr env a (env id)
  | .Sstore chunk a1 a2 =>
      wt_expr env a1 Tptr ∧ wt_expr env a2 (type_of_chunk chunk)
  | .Scall optid sg a1 args =>
      wt_expr env a1 Tptr ∧
        list_forall2 (wt_expr env) args (proj_sig_args sg) ∧
        wt_opt_assign env optid sg.sig_res
  | .Stailcall sg a1 args =>
      wt_expr env a1 Tptr ∧
        list_forall2 (wt_expr env) args (proj_sig_args sg) ∧ sg.sig_res = tret
  | .Sbuiltin optid ef args =>
      list_forall2 (wt_expr env) args (proj_sig_args (ef_sig ef)) ∧
        wt_opt_assign env optid (ef_sig ef).sig_res
  | .Sseq s1 s2 => wt_stmt env tret s1 ∧ wt_stmt env tret s2
  | .Sifthenelse a s1 s2 =>
      wt_expr env a Tint ∧ wt_stmt env tret s1 ∧ wt_stmt env tret s2
  | .Sloop s => wt_stmt env tret s
  | .Sblock s => wt_stmt env tret s
  | .Sexit _ => True
  | .Sswitch isLong a _ _ => wt_expr env a (if isLong then Tlong else Tint)
  | .Sreturn none => True
  | .Sreturn (some a) => wt_expr env a (proj_xtype tret)
  | .Slabel _ s => wt_stmt env tret s
  | .Sgoto _ => True

def wt_Sskip (env : typenv) (tret : xtype) : wt_stmt env tret Sskip :=
  True.intro

def wt_Sexit (env : typenv) (tret : xtype) (n : Nat) :
    wt_stmt env tret (Sexit n) :=
  True.intro

def wt_function (env : typenv) (f : function) : Prop :=
  type_function f = OK env ∧
    List.map env f.fn_params = proj_sig_args f.fn_sig ∧
    wt_stmt env f.fn_sig.sig_res f.fn_body

def wt_fundef : fundef → Prop
  | .Internal f => ∃ env, wt_function env f
  | .External _ => True

def wt_program (p : program) : Prop :=
  ∀ i f, (i, Gfun f) ∈ p.prog_defs → wt_fundef f

/-! ## Semantic typing invariants -/

def wt_env (env : typenv) (e : Cminor.env) : Prop :=
  ∀ id v, PTree.get id e = some v → Val.has_type v (env id)

def def_env (f : function) (e : Cminor.env) : Prop :=
  ∀ id, id ∈ f.fn_params ∨ id ∈ f.fn_vars →
    ∃ v, PTree.get id e = some v

def wt_cont (env : typenv) (tret : xtype) : cont → Prop
  | .Kstop => tret = Xint
  | .Kseq s k => wt_stmt env tret s ∧ wt_cont env tret k
  | .Kblock k => wt_cont env tret k
  | .Kcall optid f _ e k =>
      ∃ callerEnv,
        wt_function callerEnv f ∧
          wt_cont callerEnv f.fn_sig.sig_res k ∧
          wt_env callerEnv e ∧
          def_env f e ∧
          wt_opt_assign callerEnv optid tret

def wt_cont_call : cont → xtype → Prop
  | .Kstop, tret => tret = Xint
  | .Kcall optid f _ e k, tret =>
      ∃ env,
        wt_function env f ∧
          wt_cont env f.fn_sig.sig_res k ∧
          wt_env env e ∧
          def_env f e ∧
          wt_opt_assign env optid tret
  | _, _ => False

def wt_state : state → Prop
  | .State f s k _ e _ =>
      ∃ env,
        wt_function env f ∧
          wt_stmt env f.fn_sig.sig_res s ∧
          wt_cont env f.fn_sig.sig_res k ∧
          wt_env env e ∧
          def_env f e
  | .Callstate f args k _ =>
      wt_fundef f ∧
        Val.has_type_list args (proj_sig_args (funsig f)) ∧
        wt_cont_call k (funsig f).sig_res
  | .Returnstate v k _ =>
      ∃ tret, Val.has_type v (proj_xtype tret) ∧ wt_cont_call k tret

/-! ## Exact statement descriptors for later proofs -/

def expect_soundStatement : Prop :=
  ∀ (e : InferEnv) (t1 t2 : typ) (e' : InferEnv),
    expect e t1 t2 = OK e' → t1 = t2

def type_expr_soundStatement : Prop :=
  ∀ (te : typenv) (a : expr) (t : typ) (e e' : InferEnv),
    type_expr e a t = OK e' →
      UniSolver.satisf cminorTypeAlgebra te e' → wt_expr te a t

def type_exprlist_soundStatement : Prop :=
  ∀ (te : typenv) (al : List expr) (tl : List typ) (e e' : InferEnv),
    type_exprlist e al tl = OK e' →
      UniSolver.satisf cminorTypeAlgebra te e' →
        list_forall2 (wt_expr te) al tl

def type_assign_soundStatement : Prop :=
  ∀ (te : typenv) (id : ident) (a : expr) (e e' : InferEnv),
    type_assign e id a = OK e' →
      UniSolver.satisf cminorTypeAlgebra te e' → wt_expr te a (te id)

def opt_set_soundStatement : Prop :=
  ∀ (te : typenv) (optid : Option ident) (sg : signature) (e e' : InferEnv),
    opt_set e optid (proj_sig_res sg) = OK e' →
      UniSolver.satisf cminorTypeAlgebra te e' →
        wt_opt_assign te optid sg.sig_res

def type_stmt_soundStatement : Prop :=
  ∀ (te : typenv) (tret : xtype) (s : stmt) (e e' : InferEnv),
    type_stmt tret e s = OK e' →
      UniSolver.satisf cminorTypeAlgebra te e' → wt_stmt te tret s

def type_function_soundStatement : Prop :=
  ∀ (f : function) (env : typenv),
    type_function f = OK env → wt_function env f

def wt_is_call_contStatement : Prop :=
  ∀ (env : typenv) (tret : xtype) (k : cont),
    wt_cont env tret k → is_call_cont k → wt_cont_call k tret

def call_cont_wtStatement : Prop :=
  ∀ (env : typenv) (tret : xtype) (k : cont),
    wt_cont env tret k → wt_cont_call (call_cont k) tret

def wt_env_assignStatement : Prop :=
  ∀ (env : typenv) (id : ident) (e : Cminor.env) (v : val),
    wt_env env e → Val.has_type v (env id) →
      wt_env env (PTree.set id v e)

def def_env_assignStatement : Prop :=
  ∀ (f : function) (e : Cminor.env) (id : ident) (v : val),
    def_env f e → def_env f (PTree.set id v e)

def wt_env_set_paramsStatement : Prop :=
  ∀ (env : typenv) (il : List ident) (vl : List val),
    Val.has_type_list vl (List.map env il) → wt_env env (set_params vl il)

def def_set_paramsStatement : Prop :=
  ∀ (id : ident) (il : List ident) (vl : List val),
    id ∈ il → ∃ v, PTree.get id (set_params vl il) = some v

def wt_env_set_localsStatement : Prop :=
  ∀ (env : typenv) (il : List ident) (e : Cminor.env),
    wt_env env e → wt_env env (set_locals il e)

def def_set_localsStatement : Prop :=
  ∀ (id : ident) (il : List ident) (e : Cminor.env),
    ((∃ v, PTree.get id e = some v) ∨ id ∈ il) →
      ∃ v, PTree.get id (set_locals il e) = some v

def wt_find_labelStatement : Prop :=
  ∀ (env : typenv) (tret : xtype) (lbl : label) (s : stmt) (k : cont),
    wt_stmt env tret s → wt_cont env tret k →
      match find_label lbl s k with
      | some (s', k') => wt_stmt env tret s' ∧ wt_cont env tret k'
      | none => True

def type_constant_soundStatement : Prop :=
  ∀ (p : program) (sp : val) (cst : constant) (v : val),
    eval_constant (Genv.globalenv p) sp cst = some v →
      Val.has_type v (type_constant cst)

def type_unop_soundStatement : Prop :=
  ∀ (op : unary_operation) (v1 v : val),
    eval_unop op v1 = some v → Val.has_type v (type_unop op).2

def type_binop_soundStatement : Prop :=
  ∀ (op : binary_operation) (v1 v2 : val) (m : mem) (v : val),
    eval_binop op v1 v2 m = some v → Val.has_type v (type_binop op).2

def wt_eval_exprStatement : Prop :=
  ∀ (p : program) (env : typenv) (sp : val) (e : Cminor.env) (m : mem)
    (a : expr) (v : val),
    eval_expr (Genv.globalenv p) sp e m a v →
      ∀ t, wt_expr env a t → wt_env env e → Val.has_type v t

def wt_eval_exprlistStatement : Prop :=
  ∀ (p : program) (env : typenv) (sp : val) (e : Cminor.env) (m : mem)
    (al : List expr) (vl : List val),
    eval_exprlist (Genv.globalenv p) sp e m al vl →
      ∀ tl,
        list_forall2 (wt_expr env) al tl →
          wt_env env e → Val.has_type_list vl tl

def wt_find_functStatement : Prop :=
  ∀ (p : program),
    wt_program p →
      ∀ (v : val) (fd : fundef),
        Genv.find_funct (Genv.globalenv p) v = some fd → wt_fundef fd

def subject_reductionStatement : Prop :=
  ∀ (xi : ExternalCalls) (p : program),
    wt_program p →
      ∀ (st1 : state) (t : trace) (st2 : state),
        step xi (Genv.globalenv p) st1 t st2 → wt_state st1 → wt_state st2

def wt_initial_stateStatement : Prop :=
  ∀ (p : program), wt_program p → ∀ s, initial_state p s → wt_state s

/-! ## Safe expressions -/

def known_idents := PTree.t Unit

def is_known (ki : known_idents) (id : ident) : Bool :=
  match PTree.get id ki with
  | some _ => true
  | none => false

def known_id (f : function) : known_idents :=
  let add := fun (ki : known_idents) (id : ident) => PTree.set id () ki
  f.fn_vars.foldl add (f.fn_params.foldl add (PTree.empty Unit))

def safe_unop : unary_operation → Bool
  | .Ointoffloat | .Ointuoffloat | .Ofloatofint | .Ofloatofintu
  | .Ointofsingle | .Ointuofsingle | .Osingleofint | .Osingleofintu
  | .Olongoffloat | .Olonguoffloat | .Ofloatoflong | .Ofloatoflongu
  | .Olongofsingle | .Olonguofsingle | .Osingleoflong | .Osingleoflongu => false
  | _ => true

def safe_binop : binary_operation → Bool
  | .Odiv | .Odivu | .Omod | .Omodu
  | .Odivl | .Odivlu | .Omodl | .Omodlu
  | .Ocmpl _ | .Ocmplu _ => false
  | _ => true

def safe_expr (ki : known_idents) : expr → Bool
  | .Evar id => is_known ki id
  | .Econst _ => true
  | .Eunop op a1 => safe_unop op && safe_expr ki a1
  | .Ebinop op a1 a2 => safe_binop op && safe_expr ki a1 && safe_expr ki a2
  | .Eload _ _ => false

def known_id_sound_1Statement : Prop :=
  ∀ (f : function) (id : ident) (x : Unit),
    PTree.get id (known_id f) = some x → id ∈ f.fn_params ∨ id ∈ f.fn_vars

def known_id_sound_2Statement : Prop :=
  ∀ (f : function) (id : ident),
    is_known (known_id f) id = true → id ∈ f.fn_params ∨ id ∈ f.fn_vars

def eval_safe_exprStatement : Prop :=
  ∀ (ge : genv) (f : function) (sp : val) (e : Cminor.env) (m : mem)
    (a : expr),
    def_env f e → safe_expr (known_id f) a = true →
      ∃ v, eval_expr ge sp e m a v

end CompCert4Lean.Backend.Cminortyping
