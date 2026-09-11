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
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

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

namespace RTLtypes

abbrev t : Type := typ
def eq (x y : t) : Sumbool (x = y) (x ≠ y) := typEq x y
def default : t := Tint

def algebra : TYPE_ALGEBRA where
  t := t
  eq := eq
  default := default

end RTLtypes

private abbrev cminorTypeAlgebra : TYPE_ALGEBRA := RTLtypes.algebra

/-! Canonical generated surface for `Unityping.UniSolver(RTLtypes)`.  Only
the members consumed by the frozen Cminortyping source are promoted; unused
generic generated proof machinery remains deferred under DMC-006. -/
namespace S

abbrev typenv : Type := UniSolver.typenv cminorTypeAlgebra
abbrev typassign : Type := UniSolver.typassign cminorTypeAlgebra

def initial : typenv := UniSolver.initial cminorTypeAlgebra

def set (e : typenv) (x : positive) (ty : RTLtypes.t) : res typenv :=
  UniSolver.set cminorTypeAlgebra e x ty

def set_list (e : typenv) (xs : List positive)
    (tys : List RTLtypes.t) : res typenv :=
  UniSolver.set_list cminorTypeAlgebra e xs tys

def move (e : typenv) (r1 r2 : positive) : res (Bool × typenv) :=
  UniSolver.move cminorTypeAlgebra e r1 r2

def solve (e : typenv) : res typassign :=
  UniSolver.solve cminorTypeAlgebra e

def satisf (te : typassign) (e : typenv) : Prop :=
  UniSolver.satisf cminorTypeAlgebra te e

def set_sound : Prop :=
  ∀ (te : typassign) (x : positive) (ty : RTLtypes.t) (e e' : typenv),
    set e x ty = OK e' → satisf te e' → te x = ty

def set_list_sound : Prop :=
  ∀ (te : typassign) (xs : List positive) (tys : List RTLtypes.t)
    (e e' : typenv), set_list e xs tys = OK e' →
    satisf te e' → List.map te xs = tys

def move_sound : Prop :=
  ∀ (te : typassign) (e : typenv) (r1 r2 : positive)
    (e' : typenv) (changed : Bool), move e r1 r2 = OK (changed, e') →
    satisf te e' → te r1 = te r2

def solve_sound : Prop :=
  ∀ (e : typenv) (te : typassign), solve e = OK te → satisf te e

end S

private abbrev InferEnv := S.typenv
private abbrev TypeAssign := S.typassign

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
  | e, .Evar id, t => S.set e id t
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
      match S.move e id id' with
      | Error message => Error message
      | OK (_, e1) => OK e1
  | .Econst c => S.set e id (type_constant c)
  | .Eunop op a1 =>
      let (targ1, tres) := type_unop op
      match type_expr e a1 targ1 with
      | Error message => Error message
      | OK e1 => S.set e1 id tres
  | .Ebinop op a1 a2 =>
      let ((targ1, targ2), tres) := type_binop op
      match type_expr e a1 targ1 with
      | Error message => Error message
      | OK e1 =>
          match type_expr e1 a2 targ2 with
          | Error message => Error message
          | OK e2 => S.set e2 id tres
  | .Eload chunk a1 =>
      match type_expr e a1 Tptr with
      | Error message => Error message
      | OK e1 => S.set e1 id (type_of_chunk chunk)

def opt_set (e : InferEnv) (optid : Option ident) (ty : typ) : res InferEnv :=
  match optid with
  | none => OK e
  | some id => S.set e id ty

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
  match S.set_list S.initial
      f.fn_params (proj_sig_args f.fn_sig) with
  | Error message => Error message
  | OK e1 =>
      match type_stmt f.fn_sig.sig_res e1 f.fn_body with
      | Error message => Error message
      | OK e2 => S.solve e2

/-! ## Relational specification -/

inductive wt_expr : typenv → expr → typ → Prop where
  | wt_Evar (env : typenv) (id : ident) :
      wt_expr env (.Evar id) (env id)
  | wt_Econst (env : typenv) (c : constant) :
      wt_expr env (.Econst c) (type_constant c)
  | wt_Eunop (env : typenv) (op : unary_operation) (a1 : expr)
      (targ1 tres : typ) :
      type_unop op = (targ1, tres) →
      wt_expr env a1 targ1 →
      wt_expr env (.Eunop op a1) tres
  | wt_Ebinop (env : typenv) (op : binary_operation) (a1 a2 : expr)
      (targ1 targ2 tres : typ) :
      type_binop op = ((targ1, targ2), tres) →
      wt_expr env a1 targ1 →
      wt_expr env a2 targ2 →
      wt_expr env (.Ebinop op a1 a2) tres
  | wt_Eload (env : typenv) (chunk : memory_chunk) (a1 : expr) :
      wt_expr env a1 Tptr →
      wt_expr env (.Eload chunk a1) (type_of_chunk chunk)

export wt_expr (wt_Evar wt_Econst wt_Eunop wt_Ebinop wt_Eload)

def wt_opt_assign (env : typenv) (optid : Option ident) (ty : xtype) : Prop :=
  match optid with
  | some id => proj_xtype ty = env id
  | none => True

inductive wt_stmt : typenv → xtype → stmt → Prop where
  | wt_Sskip (env : typenv) (tret : xtype) :
      wt_stmt env tret Sskip
  | wt_Sassign (env : typenv) (tret : xtype) (id : ident) (a : expr) :
      wt_expr env a (env id) →
      wt_stmt env tret (.Sassign id a)
  | wt_Sstore (env : typenv) (tret : xtype) (chunk : memory_chunk)
      (a1 a2 : expr) :
      wt_expr env a1 Tptr →
      wt_expr env a2 (type_of_chunk chunk) →
      wt_stmt env tret (.Sstore chunk a1 a2)
  | wt_Scall (env : typenv) (tret : xtype) (optid : Option ident)
      (sg : signature) (a1 : expr)
      (al : List expr) :
      wt_expr env a1 Tptr →
      list_forall2 (wt_expr env) al (proj_sig_args sg) →
      wt_opt_assign env optid sg.sig_res →
      wt_stmt env tret (.Scall optid sg a1 al)
  | wt_Stailcall (env : typenv) (tret : xtype) (sg : signature)
      (a1 : expr) (al : List expr) :
      wt_expr env a1 Tptr →
      list_forall2 (wt_expr env) al (proj_sig_args sg) →
      sg.sig_res = tret →
      wt_stmt env tret (.Stailcall sg a1 al)
  | wt_Sbuiltin (env : typenv) (tret : xtype) (optid : Option ident)
      (ef : external_function) (al : List expr) :
      list_forall2 (wt_expr env) al (proj_sig_args (ef_sig ef)) →
      wt_opt_assign env optid (ef_sig ef).sig_res →
      wt_stmt env tret (.Sbuiltin optid ef al)
  | wt_Sseq (env : typenv) (tret : xtype) (s1 s2 : stmt) :
      wt_stmt env tret s1 →
      wt_stmt env tret s2 →
      wt_stmt env tret (.Sseq s1 s2)
  | wt_Sifthenelse (env : typenv) (tret : xtype) (a : expr)
      (s1 s2 : stmt) :
      wt_expr env a Tint →
      wt_stmt env tret s1 →
      wt_stmt env tret s2 →
      wt_stmt env tret (.Sifthenelse a s1 s2)
  | wt_Sloop (env : typenv) (tret : xtype) (s1 : stmt) :
      wt_stmt env tret s1 →
      wt_stmt env tret (.Sloop s1)
  | wt_Sblock (env : typenv) (tret : xtype) (s1 : stmt) :
      wt_stmt env tret s1 →
      wt_stmt env tret (.Sblock s1)
  | wt_Sexit (env : typenv) (tret : xtype) (n : Nat) :
      wt_stmt env tret (.Sexit n)
  | wt_Sswitch (env : typenv) (tret : xtype) (sz : Bool) (a : expr)
      (tbl : List (Z × Nat))
      (dfl : Nat) :
      wt_expr env a (if sz then Tlong else Tint) →
      wt_stmt env tret (.Sswitch sz a tbl dfl)
  | wt_Sreturn_none (env : typenv) (tret : xtype) :
      wt_stmt env tret (.Sreturn none)
  | wt_Sreturn_some (env : typenv) (tret : xtype) (a : expr) :
      wt_expr env a (proj_xtype tret) →
      wt_stmt env tret (.Sreturn (some a))
  | wt_Slabel (env : typenv) (tret : xtype) (lbl : label) (s1 : stmt) :
      wt_stmt env tret s1 →
      wt_stmt env tret (.Slabel lbl s1)
  | wt_Sgoto (env : typenv) (tret : xtype) (lbl : label) :
      wt_stmt env tret (.Sgoto lbl)

export wt_stmt (wt_Sskip wt_Sassign wt_Sstore wt_Scall wt_Stailcall wt_Sbuiltin
  wt_Sseq wt_Sifthenelse wt_Sloop wt_Sblock wt_Sexit wt_Sswitch
  wt_Sreturn_none wt_Sreturn_some wt_Slabel wt_Sgoto)

inductive wt_function : typenv → function → Prop where
  | wt_function_intro (env : typenv) (f : function) :
      type_function f = OK env →
      List.map env f.fn_params = proj_sig_args f.fn_sig →
      wt_stmt env f.fn_sig.sig_res f.fn_body →
      wt_function env f

export wt_function (wt_function_intro)

inductive wt_fundef : fundef → Prop where
  | wt_fundef_internal (env : typenv) (f : function) :
      wt_function env f →
      wt_fundef (.Internal f)
  | wt_fundef_external (ef : external_function) :
      wt_fundef (.External ef)

export wt_fundef (wt_fundef_internal wt_fundef_external)

def wt_program (p : program) : Prop :=
  ∀ i f, (i, Gfun f) ∈ p.prog_defs → wt_fundef f

/-! ## Semantic typing invariants -/

def wt_env (env : typenv) (e : Cminor.env) : Prop :=
  ∀ id v, PTree.get id e = some v → Val.has_type v (env id)

def def_env (f : function) (e : Cminor.env) : Prop :=
  ∀ id, id ∈ f.fn_params ∨ id ∈ f.fn_vars →
    ∃ v, PTree.get id e = some v

mutual
  inductive wt_cont_call : cont → xtype → Prop where
    | wt_cont_Kstop :
        wt_cont_call Kstop Xint
    | wt_cont_Kcall (optid : Option ident) (f : function) (sp : val)
        (e : Cminor.env) (k : cont) (tret : xtype) (env : typenv) :
        (WT_FN : wt_function env f) →
        (WT_CONT : wt_cont env f.fn_sig.sig_res k) →
        (WT_ENV : wt_env env e) →
        (DEF_ENV : def_env f e) →
        (WT_DEST : wt_opt_assign env optid tret) →
        wt_cont_call (.Kcall optid f sp e k) tret

  inductive wt_cont : typenv → xtype → cont → Prop where
    | wt_cont_Kseq (env : typenv) (tret : xtype) (s : stmt) (k : cont) :
        wt_stmt env tret s →
        wt_cont env tret k →
        wt_cont env tret (.Kseq s k)
    | wt_cont_Kblock (env : typenv) (tret : xtype) (k : cont) :
        wt_cont env tret k →
        wt_cont env tret (.Kblock k)
    | wt_cont_other (env : typenv) (tret : xtype) (k : cont) :
        wt_cont_call k tret →
        wt_cont env tret k

end

export wt_cont_call (wt_cont_Kstop wt_cont_Kcall)
export wt_cont (wt_cont_Kseq wt_cont_Kblock wt_cont_other)

  inductive wt_state : state → Prop where
  | wt_normal_state (f : function) (s : stmt) (k : cont) (sp : val)
      (e : Cminor.env) (m : mem) (env : typenv) :
      (WT_FN : wt_function env f) →
      (WT_STMT : wt_stmt env f.fn_sig.sig_res s) →
      (WT_CONT : wt_cont env f.fn_sig.sig_res k) →
      (WT_ENV : wt_env env e) →
      (DEF_ENV : def_env f e) →
      wt_state (.State f s k sp e m)
  | wt_call_state (f : fundef) (args : List val) (k : cont) (m : mem) :
      (WT_FD : wt_fundef f) →
      (WT_ARGS : Val.has_type_list args (proj_sig_args (funsig f))) →
      (WT_CONT : wt_cont_call k (funsig f).sig_res) →
      wt_state (.Callstate f args k m)
  | wt_return_state (v : val) (k : cont) (m : mem) (tret : xtype) :
      (WT_RES : Val.has_type v (proj_xtype tret)) →
      (WT_CONT : wt_cont_call k tret) →
      wt_state (.Returnstate v k m)

export wt_state (wt_normal_state wt_call_state wt_return_state)

/-! ## Exact statement descriptors for later proofs -/

def expect_soundStatement : Prop :=
  ∀ (e : InferEnv) (t1 t2 : typ) (e' : InferEnv),
    expect e t1 t2 = OK e' → t1 = t2

def type_expr_soundStatement : Prop :=
  ∀ (te : typenv) (a : expr) (t : typ) (e e' : InferEnv),
    type_expr e a t = OK e' →
      S.satisf te e' → wt_expr te a t

def type_exprlist_soundStatement : Prop :=
  ∀ (te : typenv) (al : List expr) (tl : List typ) (e e' : InferEnv),
    type_exprlist e al tl = OK e' →
      S.satisf te e' →
        list_forall2 (wt_expr te) al tl

def type_assign_soundStatement : Prop :=
  ∀ (te : typenv) (id : ident) (a : expr) (e e' : InferEnv),
    type_assign e id a = OK e' →
      S.satisf te e' → wt_expr te a (te id)

def opt_set_soundStatement : Prop :=
  ∀ (te : typenv) (optid : Option ident) (sg : signature) (e e' : InferEnv),
    opt_set e optid (proj_sig_res sg) = OK e' →
      S.satisf te e' →
        wt_opt_assign te optid sg.sig_res

def type_stmt_soundStatement : Prop :=
  ∀ (te : typenv) (tret : xtype) (s : stmt) (e e' : InferEnv),
    type_stmt tret e s = OK e' →
      S.satisf te e' → wt_stmt te tret s

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

def type_unop_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (op : unary_operation) (v1 v : val),
    eval_unop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      op v1 = some v → Val.has_type v (type_unop op).2

def type_binop_soundStatement : Prop :=
  ∀ (op : binary_operation) (v1 v2 : val) (m : mem) (v : val),
    eval_binop op v1 v2 m = some v → Val.has_type v (type_binop op).2

def wt_eval_exprStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : program) (env : typenv) (sp : val) (e : Cminor.env) (m : mem)
    (a : expr) (v : val),
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (Genv.globalenv p) sp e m a v →
      ∀ t, wt_expr env a t → wt_env env e → Val.has_type v t

def wt_eval_exprlistStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : program) (env : typenv) (sp : val) (e : Cminor.env) (m : mem)
    (al : List expr) (vl : List val),
    eval_exprlist
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (Genv.globalenv p) sp e m al vl →
      ∀ tl,
        list_forall2 (wt_expr env) al tl →
          wt_env env e → Val.has_type_list vl tl

def wt_find_functStatement : Prop :=
  ∀ (p : program),
    wt_program p →
      ∀ (v : val) (fd : fundef),
        Genv.find_funct (Genv.globalenv p) v = some fd → wt_fundef fd

def subject_reductionStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : program),
    wt_program p →
      ∀ (st1 : state) (t : trace) (st2 : state),
        step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi (Genv.globalenv p) st1 t st2 → wt_state st1 → wt_state st2

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

def eval_safe_exprStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (f : function) (sp : val) (e : Cminor.env) (m : mem)
    (a : expr),
    def_env f e → safe_expr (known_id f) a = true →
      ∃ v, eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge sp e m a v

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping.S

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Unityping
open CompCert4Lean.Common.Unityping.UniSolver
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Common.Errors

private theorem set_incr_aux :
    ∀ (te : typassign) (x : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
      (ty : RTLtypes.t) (e e' : typenv),
      S.set e x ty = OK e' → satisf te e' → satisf te e := by
  intro te x ty e e' hset hs
  unfold set CompCert4Lean.Common.Unityping.UniSolver.set at hset
  split at hset
  · rename_i hget
    cases hset
    constructor
    · intro y t hy
      have hgs :=
        (CompCert4Lean.Lib.Maps.PTree.gsspec_proof
          (A := RTLtypes.t) y x ty (te_typ e))
      cases hp : peq y x with
      | left hxy =>
          subst y
          simp [hget] at hy
      | right hne =>
          have hupd : PTree.get y (PTree.set x ty (te_typ e)) = some t := by
            rw [hgs]
            simp [hp]
            exact hy
          exact hs.1 y t hupd
    · intro y z heq
      exact hs.2 y z heq
  · rename_i hget
    split at hset
    · rename_i opt ty' dec hproof hmatch
      cases hset
      exact hs
    · rename_i hne
      cases hset

theorem set_sound_proof : set_sound := by
  intro te x ty e e' hset hs
  unfold set CompCert4Lean.Common.Unityping.UniSolver.set at hset
  split at hset
  · rename_i hget
    cases hset
    have hg : PTree.get x (PTree.set x ty (te_typ e)) = some ty := by
      have hg0 :=
        (CompCert4Lean.Lib.Maps.PTree.gsspec_proof
          (A := RTLtypes.t) x x ty (te_typ e))
      cases hpeq : peq x x with
      | left h => simpa [hpeq] using hg0
      | right h => exact False.elim (h rfl)
    exact hs.1 x ty hg
  · rename_i hget
    split at hset
    · rename_i opt ty' dec hproof hmatch
      cases hset
      simpa [hproof] using hs.1 x ty' hget
    · rename_i hne
      cases hset

private theorem set_list_incr_aux :
    ∀ (te : typassign)
      (xs : List CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
      (tys : List RTLtypes.t)
      (e e' : typenv),
      S.set_list e xs tys = OK e' → satisf te e' → satisf te e := by
  intro te xs tys e e' h hs
  induction xs generalizing tys e e' with
  | nil =>
      cases tys with
      | nil =>
          cases h
          exact hs
      | cons ty tys =>
          simp [S.set_list, CompCert4Lean.Common.Unityping.UniSolver.set_list] at h
  | cons x xs ih =>
      cases tys with
      | nil =>
          simp [S.set_list, CompCert4Lean.Common.Unityping.UniSolver.set_list] at h
      | cons ty tys =>
          simp only [S.set_list, CompCert4Lean.Common.Unityping.UniSolver.set_list] at h
          split at h
          · cases h
          · rename_i e1 hset
            have htail := ih (tys := tys) (e := e1) (e' := e') h hs
            exact set_incr_aux te x ty e e1 hset htail

theorem set_list_sound_proof : set_list_sound := by
  intro te xs tys e e' h hs
  induction xs generalizing tys e e' with
  | nil =>
      cases tys with
      | nil =>
          simp [S.set_list, CompCert4Lean.Common.Unityping.UniSolver.set_list] at h
          cases h
          rfl
      | cons ty tys =>
          simp [S.set_list, CompCert4Lean.Common.Unityping.UniSolver.set_list] at h
  | cons x xs ih =>
      cases tys with
      | nil =>
          simp [S.set_list, CompCert4Lean.Common.Unityping.UniSolver.set_list] at h
      | cons ty tys =>
          simp only [S.set_list, CompCert4Lean.Common.Unityping.UniSolver.set_list] at h
          split at h
          · rename_i msg herr
            cases h
          · rename_i e1 hset
            change S.set e x ty = OK e1 at hset
            have hs1 : satisf te e1 := set_list_incr_aux te xs tys e1 e' h hs
            have htail := ih (tys := tys) (e := e1) (e' := e') h hs
            have hx : te x = ty := set_sound_proof te x ty e e1 hset hs1
            simp only [List.map] at htail ⊢
            rw [hx, htail]
            rfl

private theorem pget_set_same {A : Type}
    (i : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (v : A) (m : PTree.t A) :
    PTree.get i (PTree.set i v m) = some v := by
  have h := CompCert4Lean.Lib.Maps.PTree.gsspec_proof i i v m
  cases hpeq : peq i i with
  | left hEq => simpa [hpeq] using h
  | right hNe => exact False.elim (hNe rfl)

private theorem pget_set_other {A : Type}
    (i j : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (v : A) (m : PTree.t A) (hne : i ≠ j) :
    PTree.get i (PTree.set j v m) = PTree.get i m := by
  have h := CompCert4Lean.Lib.Maps.PTree.gsspec_proof i j v m
  cases hpeq : peq i j with
  | left hEq => exact False.elim (hne hEq)
  | right hNe => simpa [hpeq] using h

theorem move_sound_proof : move_sound := by
  intro te e r1 r2 e' changed h hs
  unfold S.move CompCert4Lean.Common.Unityping.UniSolver.move at h
  cases hp : peq r1 r2 with
  | left hEq =>
      simp [hp] at h
      cases h
      exact hEq ▸ rfl
  | right hNe =>
      cases h1 : PTree.get r1 (te_typ e) with
      | none =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              apply hs.2 r1 r2
              change (r1, r2) ∈ (r1, r2) :: te_equ e
              exact List.mem_cons_self
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases h
              have hu1 := pget_set_same r1 ty2 (te_typ e)
              have hu2 := pget_set_other r2 r1 ty2 (te_typ e) hNe.symm
              have htr1 : te r1 = ty2 := hs.1 r1 ty2 (by
                change PTree.get r1 (PTree.set r1 ty2 (te_typ e)) = some ty2
                exact hu1)
              have htr2 : te r2 = ty2 := hs.1 r2 ty2 (by
                change PTree.get r2 (PTree.set r1 ty2 (te_typ e)) = some ty2
                exact hu2.trans h2)
              exact htr1.trans htr2.symm
      | some ty1 =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              have hu1 := pget_set_other r1 r2 ty1 (te_typ e) hNe
              have hu2 := pget_set_same r2 ty1 (te_typ e)
              have htr1 : te r1 = ty1 := hs.1 r1 ty1 (by
                change PTree.get r1 (PTree.set r2 ty1 (te_typ e)) = some ty1
                exact hu1.trans h1)
              have htr2 : te r2 = ty1 := hs.1 r2 ty1 (by
                change PTree.get r2 (PTree.set r2 ty1 (te_typ e)) = some ty1
                exact hu2)
              exact htr1.trans htr2.symm
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases hEq : cminorTypeAlgebra.eq ty1 ty2 with
              | left hty =>
                simp [hEq] at h
                have he' : e' = e := h.2.symm
                subst e'
                have htr1 := hs.1 r1 ty1 (by exact h1)
                have htr2 := hs.1 r2 ty2 (by exact h2)
                exact htr1.trans (hty.trans htr2.symm)
              | right hty =>
                simp [hEq] at h

end CompCert4Lean.Backend.Cminortyping.S

namespace CompCert4Lean.Backend.Cminortyping.S

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Unityping
open CompCert4Lean.Common.Unityping.UniSolver
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Common.Errors

private theorem move_incr_aux :
    ∀ (te : typassign) (e : typenv) (r1 r2 : positive)
      (e' : typenv) (changed : Bool),
      move e r1 r2 = OK (changed, e') → satisf te e' → satisf te e := by
  intro te e r1 r2 e' changed h hs
  unfold S.move CompCert4Lean.Common.Unityping.UniSolver.move at h
  cases hp : peq r1 r2 with
  | left hEq =>
      simp [hp] at h
      rcases h with ⟨rfl, rfl⟩
      exact hs
  | right hNe =>
      cases h1 : PTree.get r1 (te_typ e) with
      | none =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              constructor
              · intro x ty hx
                exact hs.1 x ty hx
              · intro x y hxy
                exact hs.2 x y (List.mem_cons_of_mem _ hxy)
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases h
              constructor
              · intro x ty hx
                by_cases hxr : x = r1
                · subst x
                  rw [h1] at hx
                  cases hx
                · exact hs.1 x ty (by
                    rw [pget_set_other x r1 ty2 (te_typ e) hxr]
                    exact hx)
              · intro x y hxy
                exact hs.2 x y hxy
      | some ty1 =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              constructor
              · intro x ty hx
                by_cases hxr : x = r2
                · subst x
                  rw [h2] at hx
                  cases hx
                · exact hs.1 x ty (by
                    rw [pget_set_other x r2 ty1 (te_typ e) hxr]
                    exact hx)
              · intro x y hxy
                exact hs.2 x y hxy
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases hEq : cminorTypeAlgebra.eq ty1 ty2 with
              | left hty =>
                  simp [hEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact hs
              | right hty =>
                  simp [hEq] at h

private theorem solve_rec_incr_aux :
    ∀ (te : typassign) (q : List (positive × positive))
      (e : typenv) (changed : Bool) (e' : typenv) (changed' : Bool),
      CompCert4Lean.Common.Unityping.UniSolver.solve_rec cminorTypeAlgebra
        e changed q = OK (e', changed') →
      satisf te e' → satisf te e := by
  intro te q
  induction q with
  | nil =>
      intro e changed e' changed' h hs
      simp [CompCert4Lean.Common.Unityping.UniSolver.solve_rec] at h
      rcases h with ⟨rfl, rfl⟩
      exact hs
  | cons a q ih =>
      rcases a with ⟨r1, r2⟩
      intro e changed e' changed' h hs
      simp only [CompCert4Lean.Common.Unityping.UniSolver.solve_rec] at h
      split at h
      · cases h
      · rename_i changed1 e1 hmove
        exact move_incr_aux te e r1 r2 e1 changed1 hmove
          (ih e1 (changed || changed1) e' changed' h hs)

private theorem solve_rec_sound_aux :
    ∀ (te : typassign) (r1 r2 : positive)
      (q : List (positive × positive)) (e : typenv) (changed : Bool)
      (e' : typenv) (changed' : Bool),
      CompCert4Lean.Common.Unityping.UniSolver.solve_rec cminorTypeAlgebra
        e changed q = OK (e', changed') →
      (r1, r2) ∈ q → satisf te e' → te r1 = te r2 := by
  intro te r1 r2 q
  induction q generalizing r1 r2 with
  | nil =>
      intro e changed e' changed' h hmem hs
      cases hmem
  | cons a q ih =>
      rcases a with ⟨a1, a2⟩
      intro e changed e' changed' h hmem hs
      simp only [CompCert4Lean.Common.Unityping.UniSolver.solve_rec] at h
      split at h
      · cases h
      · rename_i changed1 e1 hmove
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · injection hmem with hr1 hr2
          subst r1
          subst r2
          exact move_sound_proof te e a1 a2 e1 changed1 hmove
            (solve_rec_incr_aux te q e1 (changed || changed1) e' changed' h hs)
        · exact ih r1 r2 e1 (changed || changed1) e' changed' h hmem hs

private theorem move_false_aux :
    ∀ (e : typenv) (r1 r2 : positive) (e' : typenv),
      move e r1 r2 = OK (false, e') →
      te_typ e' = te_typ e ∧
        makeassign cminorTypeAlgebra e r1 = makeassign cminorTypeAlgebra e r2 := by
  intro e r1 r2 e' h
  unfold S.move CompCert4Lean.Common.Unityping.UniSolver.move at h
  cases hp : peq r1 r2 with
  | left hEq =>
      simp [hp] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, hEq ▸ rfl⟩
  | right hNe =>
      cases h1 : PTree.get r1 (te_typ e) with
      | none =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              rcases h with ⟨rfl, rfl⟩
              constructor
              · rfl
              · simp [CompCert4Lean.Common.Unityping.UniSolver.makeassign, h1, h2]
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases h
      | some ty1 =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases hEq : cminorTypeAlgebra.eq ty1 ty2 with
              | left hty =>
                  simp [hEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  constructor
                  · rfl
                  · simp [CompCert4Lean.Common.Unityping.UniSolver.makeassign, h1, h2, hty]
              | right hty =>
                  simp [hEq] at h

private theorem solve_rec_false_aux :
    ∀ (r1 r2 : positive) (q : List (positive × positive))
      (e : typenv) (changed : Bool) (e' : typenv),
      CompCert4Lean.Common.Unityping.UniSolver.solve_rec cminorTypeAlgebra
        e changed q = OK (e', false) →
      changed = false ∧
        ((r1, r2) ∈ q →
          makeassign cminorTypeAlgebra e r1 = makeassign cminorTypeAlgebra e r2) := by
  intro r1 r2 q
  induction q with
  | nil =>
      intro e changed e' h
      simp only [CompCert4Lean.Common.Unityping.UniSolver.solve_rec] at h
      cases changed with
      | false =>
          rcases h with ⟨rfl, rfl⟩
          exact ⟨rfl, by intro hmem; cases hmem⟩
      | true =>
          cases h
  | cons a q ih =>
      rcases a with ⟨a1, a2⟩
      intro e changed e' h
      simp only [CompCert4Lean.Common.Unityping.UniSolver.solve_rec] at h
      split at h
      · cases h
      · rename_i changed1 e1 hmove
        have htail := ih e1 (changed || changed1) e' h
        rcases htail with ⟨hchanged, hmem⟩
        have hc : changed = false := by
          cases changed <;> cases changed1 <;> simp_all
        have hc1 : changed1 = false := by
          cases changed <;> cases changed1 <;> simp_all
        subst changed
        subst changed1
        have hmf := move_false_aux e a1 a2 e1 hmove
        constructor
        · rfl
        · intro hmem'
          simp only [List.mem_cons] at hmem'
          rcases hmem' with hhead | htailmem
          · rcases hhead with ⟨rfl, rfl⟩
            exact hmf.2
          · have hEq := hmem htailmem
            unfold CompCert4Lean.Common.Unityping.UniSolver.makeassign at hEq ⊢
            rw [hmf.1] at hEq
            exact hEq

private theorem solve_constraints_incr_aux :
    ∀ (te : typassign) (e e' : typenv),
      CompCert4Lean.Common.Unityping.UniSolver.solve_constraints cminorTypeAlgebra e =
        OK e' → satisf te e' → satisf te e := by
  intro te e e' h hs
  let P : typenv → res typenv → Prop := fun e r =>
    ∀ e', r = OK e' → satisf te e' → satisf te e
  have hind :=
    CompCert4Lean.Common.Unityping.UniSolver.solve_constraints_ind
      cminorTypeAlgebra P
      (by
        intro e e' hrec e'' heq hs'
        cases heq
        exact hs')
      (by
        intro e e' hrec ih e'' heq hs'
        have hsbase := ih e'' heq hs'
        have hsorig : satisf te e := by
          have hs0 := solve_rec_incr_aux te (te_equ e)
            { te_typ := te_typ e, te_equ := [] } false e' true hrec hsbase
          constructor
          · intro x ty hx
            exact hs0.1 x ty hx
          · intro x y hxy
            exact solve_rec_sound_aux te x y (te_equ e)
              { te_typ := te_typ e, te_equ := [] } false e' true hrec hxy hsbase
        exact hsorig)
      (by
        intro e message hrec e'' heq hs'
        cases heq)
      e
  exact hind e' h hs

private theorem solve_constraints_sound_aux :
    ∀ (e e' : typenv),
      CompCert4Lean.Common.Unityping.UniSolver.solve_constraints cminorTypeAlgebra e =
        OK e' →
      satisf (makeassign cminorTypeAlgebra e') e' := by
  intro e e' h
  let P : typenv → res typenv → Prop := fun _ r =>
    ∀ e', r = OK e' →
      satisf (makeassign cminorTypeAlgebra e') e'
  have hind :=
    CompCert4Lean.Common.Unityping.UniSolver.solve_constraints_ind
      cminorTypeAlgebra P
      (by
        intro e e' hrec e'' heq
        cases heq
        constructor
        · intro x ty hx
          simp [CompCert4Lean.Common.Unityping.UniSolver.makeassign, hx]
        · intro x y hxy
          have hf := solve_rec_false_aux x y (te_equ e)
            { te_typ := te_typ e, te_equ := [] } false e' hrec
          have heq' := hf.2 hxy
          simpa [CompCert4Lean.Common.Unityping.UniSolver.makeassign] using heq')
      (by
        intro e e' hrec ih e'' heq
        have hs := ih e'' heq
        exact hs)
      (by
        intro e message hrec e' heq
        cases heq)
      e
  exact hind e' h

theorem solve_sound_proof : solve_sound := by
  intro e te h
  unfold S.solve CompCert4Lean.Common.Unityping.UniSolver.solve at h
  split at h
  · cases h
  · rename_i e' hconstraints
    rcases h with ⟨rfl⟩
    exact solve_constraints_incr_aux (makeassign cminorTypeAlgebra e') e e'
      hconstraints (solve_constraints_sound_aux e e' hconstraints)

end CompCert4Lean.Backend.Cminortyping.S

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Common.Errors

theorem expect_sound : expect_soundStatement := by
  intro e t1 t2 e' h
  unfold expect at h
  cases hEq : typEq t1 t2 with
  | left htyp =>
      simp [hEq] at h
      exact htyp
  | right htyp =>
      simp [hEq] at h

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Unityping
open CompCert4Lean.Common.Unityping.UniSolver
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Cminor

private theorem type_expr_set_incr_aux :
    ∀ (te : S.typassign) (x : positive) (ty : RTLtypes.t) (e e' : S.typenv),
      S.set e x ty = OK e' → S.satisf te e' → S.satisf te e := by
  intro te x ty e e' hset hs
  unfold S.set CompCert4Lean.Common.Unityping.UniSolver.set at hset
  split at hset
  · rename_i hget
    cases hset
    constructor
    · intro y t hy
      have hgs :=
        CompCert4Lean.Lib.Maps.PTree.gsspec_proof
          (A := RTLtypes.t) y x ty (te_typ e)
      cases hp : peq y x with
      | left hxy =>
          subst y
          simp [hget] at hy
      | right hne =>
          have hupd : PTree.get y (PTree.set x ty (te_typ e)) = some t := by
            rw [hgs]
            simp [hp]
            exact hy
          exact hs.1 y t hupd
    · intro y z heq
      exact hs.2 y z heq
  · rename_i hget
    split at hset
    · rename_i opt ty' dec hproof hmatch
      cases hset
      exact hs
    · rename_i hne
      cases hset

private theorem type_expr_expect_incr_aux :
    ∀ (te : S.typassign) (e : S.typenv) (t1 t2 : typ) (e' : S.typenv),
      expect e t1 t2 = OK e' → S.satisf te e' → S.satisf te e := by
  intro te e t1 t2 e' h hs
  unfold expect at h
  cases hEq : typEq t1 t2 with
  | left htyp =>
      simp [hEq] at h
      cases h
      exact hs
  | right htyp =>
      simp [hEq] at h

private theorem type_expr_incr_aux :
    ∀ (te : S.typassign) (a : expr) (t : typ) (e e' : S.typenv),
      type_expr e a t = OK e' → S.satisf te e' → S.satisf te e := by
  intro te a
  induction a with
  | Evar id =>
      intro t e e' h hs
      exact type_expr_set_incr_aux te id t e e' h hs
  | Econst c =>
      intro t e e' h hs
      exact type_expr_expect_incr_aux te e (type_constant c) t e' h hs
  | Eunop op a ih =>
      intro t e e' h hs
      rcases hOp : type_unop op with ⟨targ, tres⟩
      cases h1 : type_expr e a targ with
      | Error message =>
          simp [type_expr, hOp, h1] at h
      | OK e1 =>
          simp [type_expr, hOp, h1] at h
          exact ih targ e e1 h1
            (type_expr_expect_incr_aux te e1 tres t e' h hs)
  | Ebinop op a1 a2 ih1 ih2 =>
      intro t e e' h hs
      rcases hOp : type_binop op with ⟨⟨targ1, targ2⟩, tres⟩
      cases h1 : type_expr e a1 targ1 with
      | Error message =>
          simp [type_expr, hOp, h1] at h
      | OK e1 =>
          cases h2 : type_expr e1 a2 targ2 with
          | Error message =>
              simp [type_expr, hOp, h1, h2] at h
          | OK e2 =>
              simp [type_expr, hOp, h1, h2] at h
              exact ih1 targ1 e e1 h1
                (ih2 targ2 e1 e2 h2
                  (type_expr_expect_incr_aux te e2 tres t e' h hs))
  | Eload chunk a ih =>
      intro t e e' h hs
      cases h1 : type_expr e a Tptr with
      | Error message =>
          simp [type_expr, h1] at h
      | OK e1 =>
          simp [type_expr, h1] at h
          exact ih Tptr e e1 h1
            (type_expr_expect_incr_aux te e1 (type_of_chunk chunk) t e' h hs)

theorem type_expr_sound : type_expr_soundStatement := by
  intro te a
  induction a with
  | Evar id =>
      intro t e e' h hs
      have hty : te id = t := S.set_sound_proof te id t e e' h hs
      exact hty ▸ wt_Evar te id
  | Econst c =>
      intro t e e' h hs
      have hty : type_constant c = t := expect_sound e (type_constant c) t e' h
      exact hty ▸ wt_Econst te c
  | Eunop op a ih =>
      intro t e e' h hs
      rcases hOp : type_unop op with ⟨targ, tres⟩
      cases h1 : type_expr e a targ with
      | Error message =>
          simp [type_expr, hOp, h1] at h
      | OK e1 =>
          simp [type_expr, hOp, h1] at h
          have hs1 : S.satisf te e1 :=
            type_expr_expect_incr_aux te e1 tres t e' h hs
          have hrec : wt_expr te a targ := ih targ e e1 h1 hs1
          have hty : tres = t := expect_sound e1 tres t e' h
          exact hty ▸ wt_Eunop te op a targ tres hOp hrec
  | Ebinop op a1 a2 ih1 ih2 =>
      intro t e e' h hs
      rcases hOp : type_binop op with ⟨⟨targ1, targ2⟩, tres⟩
      cases h1 : type_expr e a1 targ1 with
      | Error message =>
          simp [type_expr, hOp, h1] at h
      | OK e1 =>
          cases h2 : type_expr e1 a2 targ2 with
          | Error message =>
              simp [type_expr, hOp, h1, h2] at h
          | OK e2 =>
              simp [type_expr, hOp, h1, h2] at h
              have hs2 : S.satisf te e2 :=
                type_expr_expect_incr_aux te e2 tres t e' h hs
              have hs1 : S.satisf te e1 :=
                type_expr_incr_aux te a2 targ2 e1 e2 h2 hs2
              have hrec1 : wt_expr te a1 targ1 := ih1 targ1 e e1 h1 hs1
              have hrec2 : wt_expr te a2 targ2 := ih2 targ2 e1 e2 h2 hs2
              have hty : tres = t := expect_sound e2 tres t e' h
              exact hty ▸ wt_Ebinop te op a1 a2 targ1 targ2 tres hOp hrec1 hrec2
  | Eload chunk a ih =>
      intro t e e' h hs
      cases h1 : type_expr e a Tptr with
      | Error message =>
          simp [type_expr, h1] at h
      | OK e1 =>
          simp [type_expr, h1] at h
          have hs1 : S.satisf te e1 :=
            type_expr_expect_incr_aux te e1 (type_of_chunk chunk) t e' h hs
          have hrec : wt_expr te a Tptr := ih Tptr e e1 h1 hs1
          have hty : type_of_chunk chunk = t :=
            expect_sound e1 (type_of_chunk chunk) t e' h
          exact hty ▸ wt_Eload te chunk a hrec

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Backend.Cminor

private theorem type_exprlist_incr_aux :
    ∀ (te : S.typassign) (al : List expr) (tl : List typ) (e e' : S.typenv),
      type_exprlist e al tl = OK e' → S.satisf te e' → S.satisf te e := by
  intro te al
  induction al with
  | nil =>
      intro tl e e' h hs
      cases tl with
      | nil =>
          simp [type_exprlist] at h
          cases h
          exact hs
      | cons t tl =>
          simp [type_exprlist] at h
  | cons a al ih =>
      intro tl e e' h hs
      cases tl with
      | nil =>
          simp [type_exprlist] at h
      | cons t tl =>
          cases h1 : type_expr e a t with
          | Error message =>
              simp [type_exprlist, h1] at h
          | OK e1 =>
              simp [type_exprlist, h1] at h
              exact type_expr_incr_aux te a t e e1 h1
                (ih tl e1 e' h hs)

theorem type_exprlist_sound : type_exprlist_soundStatement := by
  intro te al
  induction al with
  | nil =>
      intro tl e e' h hs
      cases tl with
      | nil =>
          simp [type_exprlist] at h
          cases h
          exact list_forall2.nil _
      | cons t tl =>
          simp [type_exprlist] at h
  | cons a al ih =>
      intro tl e e' h hs
      cases tl with
      | nil =>
          simp [type_exprlist] at h
      | cons t tl =>
          cases h1 : type_expr e a t with
          | Error message =>
              simp [type_exprlist, h1] at h
          | OK e1 =>
              simp [type_exprlist, h1] at h
              have hs1 : S.satisf te e1 :=
                type_exprlist_incr_aux te al tl e1 e' h hs
              exact list_forall2.cons a t
                (type_expr_sound te a t e e1 h1 hs1)
                (ih tl e1 e' h hs)

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Backend.Cminor

theorem type_assign_sound : type_assign_soundStatement := by
  intro te id a e e' h hs
  cases a with
  | Evar id' =>
      cases hmove : S.move e id id' with
      | Error message =>
          simp [type_assign, hmove] at h
      | OK result =>
          rcases result with ⟨changed, e1⟩
          simp [type_assign, hmove] at h
          cases h
          have hty : te id = te id' :=
            S.move_sound_proof te e id id' e' changed hmove hs
          exact hty.symm ▸ wt_Evar te id'
  | Econst c =>
      cases hset : S.set e id (type_constant c) with
      | Error message =>
          simp [type_assign, hset] at h
      | OK e1 =>
          simp [type_assign, hset] at h
          cases h
          have hty : te id = type_constant c :=
            S.set_sound_proof te id (type_constant c) e e' hset hs
          exact hty.symm ▸ wt_Econst te c
  | Eunop op a1 =>
      rcases hOp : type_unop op with ⟨targ, tres⟩
      cases h1 : type_expr e a1 targ with
      | Error message =>
          simp [type_assign, hOp, h1] at h
      | OK e1 =>
          cases hset : S.set e1 id tres with
          | Error message =>
              simp [type_assign, hOp, h1, hset] at h
          | OK e2 =>
              simp [type_assign, hOp, h1, hset] at h
              cases h
              have hty : te id = tres :=
                S.set_sound_proof te id tres e1 e' hset hs
              have hs1 : S.satisf te e1 :=
                type_expr_set_incr_aux te id tres e1 e' hset hs
              have hrec : wt_expr te a1 targ :=
                type_expr_sound te a1 targ e e1 h1 hs1
              exact hty.symm ▸ wt_Eunop te op a1 targ tres hOp hrec
  | Ebinop op a1 a2 =>
      rcases hOp : type_binop op with ⟨⟨targ1, targ2⟩, tres⟩
      cases h1 : type_expr e a1 targ1 with
      | Error message =>
          simp [type_assign, hOp, h1] at h
      | OK e1 =>
          cases h2 : type_expr e1 a2 targ2 with
          | Error message =>
              simp [type_assign, hOp, h1, h2] at h
          | OK e2 =>
              cases hset : S.set e2 id tres with
              | Error message =>
                  simp [type_assign, hOp, h1, h2, hset] at h
              | OK e3 =>
                  simp [type_assign, hOp, h1, h2, hset] at h
                  cases h
                  have hty : te id = tres :=
                    S.set_sound_proof te id tres e2 e' hset hs
                  have hs2 : S.satisf te e2 :=
                    type_expr_set_incr_aux te id tres e2 e' hset hs
                  have hs1 : S.satisf te e1 :=
                    type_expr_incr_aux te a2 targ2 e1 e2 h2 hs2
                  have hrec1 : wt_expr te a1 targ1 :=
                    type_expr_sound te a1 targ1 e e1 h1 hs1
                  have hrec2 : wt_expr te a2 targ2 :=
                    type_expr_sound te a2 targ2 e1 e2 h2 hs2
                  exact hty.symm ▸
                    wt_Ebinop te op a1 a2 targ1 targ2 tres hOp hrec1 hrec2
  | Eload chunk a1 =>
      cases h1 : type_expr e a1 Tptr with
      | Error message =>
          simp [type_assign, h1] at h
      | OK e1 =>
          cases hset : S.set e1 id (type_of_chunk chunk) with
          | Error message =>
              simp [type_assign, h1, hset] at h
          | OK e2 =>
              simp [type_assign, h1, hset] at h
              cases h
              have hty : te id = type_of_chunk chunk :=
                S.set_sound_proof te id (type_of_chunk chunk) e1 e' hset hs
              have hs1 : S.satisf te e1 :=
                type_expr_set_incr_aux te id (type_of_chunk chunk) e1 e' hset hs
              have hrec : wt_expr te a1 Tptr :=
                type_expr_sound te a1 Tptr e e1 h1 hs1
              exact hty.symm ▸ wt_Eload te chunk a1 hrec

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Backend.Cminor

theorem opt_set_sound : opt_set_soundStatement := by
  intro te optid sg e e' h hs
  unfold opt_set at h
  cases optid with
  | none =>
      simp at h
      cases h
      trivial
  | some id =>
      unfold wt_opt_assign
      exact (S.set_sound_proof te id (proj_sig_res sg) e e' h hs).symm

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Backend.Cminor

private theorem type_assign_incr_aux :
    ∀ (te : S.typassign) (id : ident) (a : expr) (e e' : S.typenv),
      type_assign e id a = OK e' → S.satisf te e' → S.satisf te e := by
  intro te id a
  cases a with
  | Evar id' =>
      intro e e' h hs
      cases hmove : S.move e id id' with
      | Error message =>
          simp [type_assign, hmove] at h
      | OK result =>
          rcases result with ⟨changed, e1⟩
          simp [type_assign, hmove] at h
          cases h
          exact S.move_incr_aux te e id id' e' changed hmove hs
  | Econst c =>
      intro e e' h hs
      cases hset : S.set e id (type_constant c) with
      | Error message =>
          simp [type_assign, hset] at h
      | OK e1 =>
          simp [type_assign, hset] at h
          cases h
          exact S.set_incr_aux te id (type_constant c) e e' hset hs
  | Eunop op a1 =>
      intro e e' h hs
      rcases hOp : type_unop op with ⟨targ, tres⟩
      cases h1 : type_expr e a1 targ with
      | Error message =>
          simp [type_assign, hOp, h1] at h
      | OK e1 =>
          cases hset : S.set e1 id tres with
          | Error message =>
              simp [type_assign, hOp, h1, hset] at h
          | OK e2 =>
              simp [type_assign, hOp, h1, hset] at h
              cases h
              exact type_expr_incr_aux te a1 targ e e1 h1
                (S.set_incr_aux te id tres e1 e' hset hs)
  | Ebinop op a1 a2 =>
      intro e e' h hs
      rcases hOp : type_binop op with ⟨⟨targ1, targ2⟩, tres⟩
      cases h1 : type_expr e a1 targ1 with
      | Error message =>
          simp [type_assign, hOp, h1] at h
      | OK e1 =>
          cases h2 : type_expr e1 a2 targ2 with
          | Error message =>
              simp [type_assign, hOp, h1, h2] at h
          | OK e2 =>
              cases hset : S.set e2 id tres with
              | Error message =>
                  simp [type_assign, hOp, h1, h2, hset] at h
              | OK e3 =>
                  simp [type_assign, hOp, h1, h2, hset] at h
                  cases h
                  have hs2 := S.set_incr_aux te id tres e2 e' hset hs
                  have hs1 := type_expr_incr_aux te a2 targ2 e1 e2 h2 hs2
                  exact type_expr_incr_aux te a1 targ1 e e1 h1 hs1
  | Eload chunk a1 =>
      intro e e' h hs
      cases h1 : type_expr e a1 Tptr with
      | Error message =>
          simp [type_assign, h1] at h
      | OK e1 =>
          cases hset : S.set e1 id (type_of_chunk chunk) with
          | Error message =>
              simp [type_assign, h1, hset] at h
          | OK e2 =>
              simp [type_assign, h1, hset] at h
              cases h
              exact type_expr_incr_aux te a1 Tptr e e1 h1
                (S.set_incr_aux te id (type_of_chunk chunk) e1 e' hset hs)

private theorem opt_set_incr_aux :
    ∀ (te : S.typassign) (optid : Option ident) (ty : typ) (e e' : S.typenv),
      opt_set e optid ty = OK e' → S.satisf te e' → S.satisf te e := by
  intro te optid ty e e' h hs
  cases optid with
  | none =>
      simp [opt_set] at h
      cases h
      exact hs
  | some id =>
      exact S.set_incr_aux te id ty e e' h hs

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Backend.Cminor

private theorem type_stmt_incr_aux :
    ∀ (te : S.typassign) (tret : xtype) (s : stmt) (e e' : S.typenv),
      type_stmt tret e s = OK e' → S.satisf te e' → S.satisf te e := by
  intro te tret s
  induction s with
  | Sskip =>
      intro e e' h hs
      simp [type_stmt] at h
      cases h
      exact hs
  | Sassign id a =>
      intro e e' h hs
      simp [type_stmt] at h
      exact type_assign_incr_aux te id a e e' h hs
  | Sstore chunk address value =>
      intro e e' h hs
      cases h1 : type_expr e address Tptr with
      | Error message =>
          simp [type_stmt, h1] at h
      | OK e1 =>
          cases h2 : type_expr e1 value (type_of_chunk chunk) with
          | Error message =>
              simp [type_stmt, h1, h2] at h
          | OK e2 =>
              simp [type_stmt, h1, h2] at h
              cases h
              exact type_expr_incr_aux te address Tptr e e1 h1
                (type_expr_incr_aux te value (type_of_chunk chunk) e1 e' h2 hs)
  | Scall result sig callee args =>
      intro e e' h hs
      cases h1 : type_expr e callee Tptr with
      | Error message =>
          simp [type_stmt, h1] at h
      | OK e1 =>
          cases h2 : type_exprlist e1 args (proj_sig_args sig) with
          | Error message =>
              simp [type_stmt, h1, h2] at h
          | OK e2 =>
              cases h3 : opt_set e2 result (proj_sig_res sig) with
              | Error message =>
                  simp [type_stmt, h1, h2, h3] at h
              | OK e3 =>
                  simp [type_stmt, h1, h2, h3] at h
                  cases h
                  have hs2 := opt_set_incr_aux te result (proj_sig_res sig)
                    e2 e' h3 hs
                  have hs1 := type_exprlist_incr_aux te args (proj_sig_args sig)
                    e1 e2 h2 hs2
                  exact type_expr_incr_aux te callee Tptr e e1 h1 hs1
  | Stailcall sig callee args =>
      intro e e' h hs
      by_cases hEq : sig.sig_res = tret
      ·
          cases h1 : type_expr e callee Tptr with
          | Error message =>
              simp [type_stmt, hEq, h1] at h
          | OK e1 =>
              cases h2 : type_exprlist e1 args (proj_sig_args sig) with
              | Error message =>
                  simp [type_stmt, hEq, h1, h2] at h
              | OK e2 =>
                  simp [type_stmt, hEq, h1, h2] at h
                  cases h
                  exact type_expr_incr_aux te callee Tptr e e1 h1
                    (type_exprlist_incr_aux te args (proj_sig_args sig)
                      e1 e' h2 hs)
      · simp [type_stmt, hEq, assertion_failed] at h
  | Sbuiltin result ef args =>
      intro e e' h hs
      cases h1 : type_exprlist e args (proj_sig_args (ef_sig ef)) with
      | Error message =>
          simp [type_stmt, h1] at h
      | OK e1 =>
          cases h2 : opt_set e1 result (proj_sig_res (ef_sig ef)) with
          | Error message =>
              simp [type_stmt, h1, h2] at h
          | OK e2 =>
              simp [type_stmt, h1, h2] at h
              cases h
              exact type_exprlist_incr_aux te args (proj_sig_args (ef_sig ef))
                e e1 h1
                (opt_set_incr_aux te result (proj_sig_res (ef_sig ef))
                  e1 e' h2 hs)
  | Sseq first second ih1 ih2 =>
      intro e e' h hs
      cases h1 : type_stmt tret e first with
      | Error message =>
          simp [type_stmt, h1] at h
      | OK e1 =>
          cases h2 : type_stmt tret e1 second with
          | Error message =>
              simp [type_stmt, h1, h2] at h
          | OK e2 =>
              simp [type_stmt, h1, h2] at h
              cases h
              exact ih1 e e1 h1 (ih2 e1 e' h2 hs)
  | Sifthenelse condition ifso ifnot ih1 ih2 =>
      intro e e' h hs
      cases h1 : type_expr e condition Tint with
      | Error message =>
          simp [type_stmt, h1] at h
      | OK e1 =>
          cases h2 : type_stmt tret e1 ifso with
          | Error message =>
              simp [type_stmt, h1, h2] at h
          | OK e2 =>
              cases h3 : type_stmt tret e2 ifnot with
              | Error message =>
                  simp [type_stmt, h1, h2, h3] at h
              | OK e3 =>
                  simp [type_stmt, h1, h2, h3] at h
                  cases h
                  have hs2 := ih2 e2 e' h3 hs
                  have hs1 := ih1 e1 e2 h2 hs2
                  exact type_expr_incr_aux te condition Tint e e1 h1 hs1
  | Sloop body ih =>
      intro e e' h hs
      simp [type_stmt] at h
      exact ih e e' h hs
  | Sblock body ih =>
      intro e e' h hs
      simp [type_stmt] at h
      exact ih e e' h hs
  | Sexit depth =>
      intro e e' h hs
      simp [type_stmt] at h
      cases h
      exact hs
  | Sswitch isLong argument cases default =>
      intro e e' h hs
      cases isLong with
      | false =>
          cases h1 : type_expr e argument Tint with
          | Error message =>
              simp [type_stmt, h1] at h
          | OK e1 =>
              simp [type_stmt, h1] at h
              cases h
              exact type_expr_incr_aux te argument Tint e e' h1 hs
      | true =>
          cases h1 : type_expr e argument Tlong with
          | Error message =>
              simp [type_stmt, h1] at h
          | OK e1 =>
              simp [type_stmt, h1] at h
              cases h
              exact type_expr_incr_aux te argument Tlong e e' h1 hs
  | Sreturn value =>
      intro e e' h hs
      cases value with
      | none =>
          simp [type_stmt] at h
          cases h
          exact hs
      | some a =>
          simp [type_stmt] at h
          exact type_expr_incr_aux te a (proj_xtype tret) e e' h hs
  | Slabel label body ih =>
      intro e e' h hs
      simp [type_stmt] at h
      exact ih e e' h hs
  | Sgoto label =>
      intro e e' h hs
      simp [type_stmt] at h
      cases h
      exact hs

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Backend.Cminor

theorem type_stmt_sound : type_stmt_soundStatement := by
  intro te tret s
  induction s with
  | Sskip =>
      intro e e' h hs
      simp [type_stmt] at h
      cases h
      exact wt_Sskip te tret
  | Sassign id a =>
      intro e e' h hs
      simp [type_stmt] at h
      exact wt_Sassign te tret id a (type_assign_sound te id a e e' h hs)
  | Sstore chunk address value =>
      intro e e' h hs
      cases h1 : type_expr e address Tptr with
      | Error message =>
          simp [type_stmt, h1] at h
      | OK e1 =>
          cases h2 : type_expr e1 value (type_of_chunk chunk) with
          | Error message =>
              simp [type_stmt, h1, h2] at h
          | OK e2 =>
              simp [type_stmt, h1, h2] at h
              cases h
              have hs1 := type_expr_incr_aux te value (type_of_chunk chunk)
                e1 e' h2 hs
              exact wt_Sstore te tret chunk address value
                (type_expr_sound te address Tptr e e1 h1 hs1)
                (type_expr_sound te value (type_of_chunk chunk) e1 e' h2 hs)
  | Scall result sig callee args =>
      intro e e' h hs
      cases h1 : type_expr e callee Tptr with
      | Error message =>
          simp [type_stmt, h1] at h
      | OK e1 =>
          cases h2 : type_exprlist e1 args (proj_sig_args sig) with
          | Error message =>
              simp [type_stmt, h1, h2] at h
          | OK e2 =>
              cases h3 : opt_set e2 result (proj_sig_res sig) with
              | Error message =>
                  simp [type_stmt, h1, h2, h3] at h
              | OK e3 =>
                  simp [type_stmt, h1, h2, h3] at h
                  cases h
                  have hs2 := opt_set_incr_aux te result (proj_sig_res sig)
                    e2 e' h3 hs
                  have hs1 := type_exprlist_incr_aux te args (proj_sig_args sig)
                    e1 e2 h2 hs2
                  exact wt_Scall te tret result sig callee args
                    (type_expr_sound te callee Tptr e e1 h1 hs1)
                    (type_exprlist_sound te args (proj_sig_args sig) e1 e2 h2 hs2)
                    (opt_set_sound te result sig e2 e' h3 hs)
  | Stailcall sig callee args =>
      intro e e' h hs
      by_cases hEq : sig.sig_res = tret
      · cases h1 : type_expr e callee Tptr with
        | Error message =>
            simp [type_stmt, hEq, h1] at h
        | OK e1 =>
            cases h2 : type_exprlist e1 args (proj_sig_args sig) with
            | Error message =>
                simp [type_stmt, hEq, h1, h2] at h
            | OK e2 =>
                simp [type_stmt, hEq, h1, h2] at h
                cases h
                have hs1 := type_exprlist_incr_aux te args (proj_sig_args sig)
                  e1 e' h2 hs
                exact wt_Stailcall te tret sig callee args
                  (type_expr_sound te callee Tptr e e1 h1 hs1)
                  (type_exprlist_sound te args (proj_sig_args sig) e1 e' h2 hs)
                  hEq
      · simp [type_stmt, hEq, assertion_failed] at h
  | Sbuiltin result ef args =>
      intro e e' h hs
      cases h1 : type_exprlist e args (proj_sig_args (ef_sig ef)) with
      | Error message =>
          simp [type_stmt, h1] at h
      | OK e1 =>
          cases h2 : opt_set e1 result (proj_sig_res (ef_sig ef)) with
          | Error message =>
              simp [type_stmt, h1, h2] at h
          | OK e2 =>
              simp [type_stmt, h1, h2] at h
              cases h
              have hsl := opt_set_incr_aux te result (proj_sig_res (ef_sig ef))
                e1 e' h2 hs
              exact wt_Sbuiltin te tret result ef args
                (type_exprlist_sound te args (proj_sig_args (ef_sig ef)) e e1 h1 hsl)
                (opt_set_sound te result (ef_sig ef) e1 e' h2 hs)
  | Sseq first second ih1 ih2 =>
      intro e e' h hs
      cases h1 : type_stmt tret e first with
      | Error message =>
          simp [type_stmt, h1] at h
      | OK e1 =>
          cases h2 : type_stmt tret e1 second with
          | Error message =>
              simp [type_stmt, h1, h2] at h
          | OK e2 =>
              simp [type_stmt, h1, h2] at h
              cases h
              exact wt_Sseq te tret first second
                (ih1 e e1 h1 (type_stmt_incr_aux te tret second e1 e' h2 hs))
                (ih2 e1 e' h2 hs)
  | Sifthenelse condition ifso ifnot ih1 ih2 =>
      intro e e' h hs
      cases h1 : type_expr e condition Tint with
      | Error message =>
          simp [type_stmt, h1] at h
      | OK e1 =>
          cases h2 : type_stmt tret e1 ifso with
          | Error message =>
              simp [type_stmt, h1, h2] at h
          | OK e2 =>
              cases h3 : type_stmt tret e2 ifnot with
              | Error message =>
                  simp [type_stmt, h1, h2, h3] at h
              | OK e3 =>
                  simp [type_stmt, h1, h2, h3] at h
                  cases h
                  have hte2 := type_stmt_incr_aux te tret ifnot e2 e' h3 hs
                  have hte1 := type_stmt_incr_aux te tret ifso e1 e2 h2 hte2
                  exact wt_Sifthenelse te tret condition ifso ifnot
                    (type_expr_sound te condition Tint e e1 h1 hte1)
                    (ih1 e1 e2 h2 hte2) (ih2 e2 e' h3 hs)
  | Sloop body ih =>
      intro e e' h hs
      simp [type_stmt] at h
      exact wt_Sloop te tret body (ih e e' h hs)
  | Sblock body ih =>
      intro e e' h hs
      simp [type_stmt] at h
      exact wt_Sblock te tret body (ih e e' h hs)
  | Sexit depth =>
      intro e e' h hs
      simp [type_stmt] at h
      cases h
      exact wt_Sexit te tret depth
  | Sswitch isLong argument cases default =>
      intro e e' h hs
      cases isLong with
      | false =>
          cases h1 : type_expr e argument Tint with
          | Error message =>
              simp [type_stmt, h1] at h
          | OK e1 =>
              simp [type_stmt, h1] at h
              cases h
              exact wt_Sswitch te tret false argument cases default
                (type_expr_sound te argument Tint e e' h1 hs)
      | true =>
          cases h1 : type_expr e argument Tlong with
          | Error message =>
              simp [type_stmt, h1] at h
          | OK e1 =>
              simp [type_stmt, h1] at h
              cases h
              exact wt_Sswitch te tret true argument cases default
                (type_expr_sound te argument Tlong e e' h1 hs)
  | Sreturn value =>
      intro e e' h hs
      cases value with
      | none =>
          simp [type_stmt] at h
          cases h
          exact wt_Sreturn_none te tret
      | some a =>
          simp [type_stmt] at h
          exact wt_Sreturn_some te tret a
            (type_expr_sound te a (proj_xtype tret) e e' h hs)
  | Slabel label body ih =>
      intro e e' h hs
      simp [type_stmt] at h
      exact wt_Slabel te tret label body (ih e e' h hs)
  | Sgoto label =>
      intro e e' h hs
      simp [type_stmt] at h
      cases h
      exact wt_Sgoto te tret label

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Backend.Cminor

theorem type_function_sound : type_function_soundStatement := by
  intro f env h
  unfold type_function at h
  cases h1 : S.set_list S.initial f.fn_params (proj_sig_args f.fn_sig) with
  | Error message =>
      simp [h1] at h
  | OK e1 =>
      cases h2 : type_stmt f.fn_sig.sig_res e1 f.fn_body with
      | Error message =>
          simp [h1, h2] at h
      | OK e2 =>
          cases h3 : S.solve e2 with
          | Error message =>
              simp [h1, h2, h3] at h
          | OK envSolved =>
              have htype := h
              simp [type_function, h1, h2, h3] at h
              injection h with henv
              subst env
              have hs2 : S.satisf envSolved e2 :=
                S.solve_sound_proof e2 envSolved h3
              have hs1 : S.satisf envSolved e1 :=
                type_stmt_incr_aux envSolved f.fn_sig.sig_res f.fn_body e1 e2 h2 hs2
              exact wt_function_intro envSolved f htype
                (S.set_list_sound_proof envSolved f.fn_params
                  (proj_sig_args f.fn_sig) S.initial e1 h1 hs1)
                (type_stmt_sound envSolved f.fn_sig.sig_res f.fn_body e1 e2 h2 hs2)

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Backend.Cminor

theorem wt_is_call_cont : wt_is_call_contStatement := by
  intro env tret k hwt
  cases hwt with
  | wt_cont_Kseq env tret s k hstmt hcont =>
      intro hcall
      simp [is_call_cont] at hcall
  | wt_cont_Kblock env tret k hcont =>
      intro hcall
      simp [is_call_cont] at hcall
  | wt_cont_other env tret k hcall =>
      intro _
      exact hcall

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Cminor

theorem call_cont_wt : call_cont_wtStatement := by
  intro env tret k hwt
  let motive1 : ∀ (k : cont) (tret : xtype), wt_cont_call k tret → Prop :=
    fun k tret _ => wt_cont_call (call_cont k) tret
  let motive2 : ∀ (env : typenv) (tret : xtype) (k : cont),
      wt_cont env tret k → Prop :=
    fun _ tret k _ => wt_cont_call (call_cont k) tret
  exact @wt_cont.rec motive1 motive2
    wt_cont_Kstop
    (fun optid f sp e k tret env WT_FN WT_CONT WT_ENV DEF_ENV WT_DEST ih =>
      wt_cont_Kcall optid f sp e k tret env WT_FN WT_CONT WT_ENV DEF_ENV WT_DEST)
    (fun env tret s k WT_STMT WT_CONT ih => ih)
    (fun env tret k WT_CONT ih => ih)
    (fun env tret k WT_CALL ih => ih)
    env tret k hwt

theorem wt_env_assign : wt_env_assignStatement := by
  intro env id e v henv hv i w hi
  have hgs := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
    (A := val) i id v e
  cases hp : peq i id with
  | left hEq =>
      subst i
      have hsame : PTree.get id (PTree.set id v e) = some v := by
        simpa [hp] using hgs
      rw [hsame] at hi
      cases hi
      exact hv
  | right hNe =>
      rw [hgs] at hi
      exact henv i w (by simpa [hp] using hi)

theorem def_env_assign : def_env_assignStatement := by
  intro f e id v hdef i hi
  have hgs := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
    (A := val) i id v e
  cases hp : peq i id with
  | left hEq =>
      subst i
      refine ⟨v, ?_⟩
      simpa [hp] using hgs
  | right hNe =>
      rcases hdef i hi with ⟨w, hw⟩
      refine ⟨w, ?_⟩
      rw [hgs]
      simp [hp, hw]

theorem wt_env_set_params : wt_env_set_paramsStatement := by
  intro env il vl h
  induction il generalizing vl with
  | nil =>
      cases vl with
      | nil =>
          intro i v hi
          have hempty : PTree.get i (PTree.empty val) = none :=
            CompCert4Lean.Lib.Maps.PTree.gempty val i
          rw [show set_params [] [] = PTree.empty val by rfl, hempty] at hi
          cases hi
      | cons v vl =>
          cases h
  | cons i il ih =>
      cases vl with
      | nil =>
          cases h
      | cons v vl =>
          change Val.has_type v (env i) ∧
            Val.has_type_list vl (List.map env il) at h
          apply wt_env_assign env i (set_params vl il) v
          · exact ih vl h.2
          · exact h.1

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Cminor

theorem def_set_params : def_set_paramsStatement := by
  intro id il vl hid
  induction il generalizing vl with
  | nil => cases hid
  | cons i il ih =>
      cases vl with
      | nil =>
          cases hp : peq id i with
          | left heq =>
              subst id
              refine ⟨Vundef, ?_⟩
              change PTree.get i (PTree.set i Vundef (set_params [] il)) = some Vundef
              have hgs := PTree.gsspec_proof
                (A := val) i i Vundef (set_params [] il)
              simpa [hp] using hgs
          | right hne =>
              have hid' : id ∈ il := by
                simp only [List.mem_cons] at hid
                exact hid.resolve_left (fun heq => hne heq)
              rcases ih (vl := []) hid' with ⟨v, hv⟩
              refine ⟨v, ?_⟩
              change PTree.get id (PTree.set i Vundef (set_params [] il)) = some v
              have hgs := PTree.gsspec_proof
                (A := val) id i Vundef (set_params [] il)
              rw [hgs]
              simpa [hp] using hv
      | cons v vl =>
          cases hp : peq id i with
          | left heq =>
              subst id
              refine ⟨v, ?_⟩
              change PTree.get i (PTree.set i v (set_params vl il)) = some v
              have hgs := PTree.gsspec_proof
                (A := val) i i v (set_params vl il)
              simpa [hp] using hgs
          | right hne =>
              have hid' : id ∈ il := by
                simp only [List.mem_cons] at hid
                exact hid.resolve_left (fun heq => hne heq)
              rcases ih (vl := vl) hid' with ⟨w, hw⟩
              refine ⟨w, ?_⟩
              change PTree.get id (PTree.set i v (set_params vl il)) = some w
              have hgs := PTree.gsspec_proof
                (A := val) id i v (set_params vl il)
              rw [hgs]
              simpa [hp] using hw

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Cminor

theorem wt_env_set_locals : wt_env_set_localsStatement := by
  intro env il e henv
  induction il with
  | nil => exact henv
  | cons i il ih =>
      apply wt_env_assign env i (set_locals il e) Vundef
      · exact ih
      · exact True.intro

end CompCert4Lean.Backend.Cminortyping

namespace CompCert4Lean.Backend.Cminortyping

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Cminor

theorem def_set_locals : def_set_localsStatement := by
  intro id il e hdef
  induction il generalizing e with
  | nil =>
      rcases hdef with ⟨v, hv⟩ | hid
      · exact ⟨v, hv⟩
      · cases hid
  | cons i il ih =>
      cases hp : peq id i with
      | left heq =>
          subst id
          refine ⟨Vundef, ?_⟩
          change PTree.get i (PTree.set i Vundef (set_locals il e)) = some Vundef
          have hgs := PTree.gsspec_proof
            (A := val) i i Vundef (set_locals il e)
          simpa [hp] using hgs
      | right hne =>
          rcases hdef with hget | hid
          · rcases ih (e := e) (Or.inl hget) with ⟨v, hv⟩
            refine ⟨v, ?_⟩
            change PTree.get id (PTree.set i Vundef (set_locals il e)) = some v
            have hgs := PTree.gsspec_proof
              (A := val) id i Vundef (set_locals il e)
            rw [hgs]
            simpa [hp] using hv
          · simp only [List.mem_cons] at hid
            rcases hid with rfl | hid
            · exact False.elim (hne rfl)
            · rcases ih (e := e) (Or.inr hid) with ⟨v, hv⟩
              refine ⟨v, ?_⟩
              change PTree.get id (PTree.set i Vundef (set_locals il e)) = some v
              have hgs := PTree.gsspec_proof
                (A := val) id i Vundef (set_locals il e)
              rw [hgs]
              simpa [hp] using hv

end CompCert4Lean.Backend.Cminortyping
