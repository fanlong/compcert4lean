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
