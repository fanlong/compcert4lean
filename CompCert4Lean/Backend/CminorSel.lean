import CompCert4Lean.Foundation.RocqStdlib
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Values
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Backend.Cminor
import CompCert4Lean.X86.Op

/-!
# CminorSel abstract syntax and semantics

Definition-bearing translation of CompCert's `backend/CminorSel.v`.  The
external-call environment is explicit, following the integrated Events API.
Proofs assigned to later migration are represented by exact proposition
descriptors.
-/

namespace CompCert4Lean.Backend.CminorSel

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev env := CompCert4Lean.Backend.Cminor.env
private abbrev z0 : Z := .Z0

/-! ## Abstract syntax -/

mutual
  inductive expr : Type where
    | Evar (id : ident)
    | Eop (op : operation) (args : exprlist)
    | Eload (chunk : memory_chunk) (addr : addressing) (args : exprlist)
    | Econdition (condition : condexpr) (ifso ifnot : expr)
    | Elet (bound body : expr)
    | Eletvar (index : Nat)
    | Ebuiltin (ef : external_function) (args : exprlist)
    | Eexternal (id : ident) (sig : signature) (args : exprlist)

  inductive exprlist : Type where
    | Enil
    | Econs (head : expr) (tail : exprlist)

  inductive condexpr : Type where
    | CEcond (condition : condition) (args : exprlist)
    | CEcondition (condition ifso ifnot : condexpr)
    | CElet (bound : expr) (body : condexpr)
end

export expr (Evar Eop Eload Econdition Elet Eletvar Ebuiltin Eexternal)
export exprlist (Enil Econs)
export condexpr (CEcond CEcondition CElet)

inductive exitexpr : Type where
  | XEexit (exitNumber : Nat)
  | XEjumptable (argument : expr) (table : List Nat)
  | XEcondition (condition : condexpr) (ifso ifnot : exitexpr)
  | XElet (bound : expr) (body : exitexpr)

export exitexpr (XEexit XEjumptable XEcondition XElet)

inductive stmt : Type where
  | Sskip
  | Sassign (id : ident) (value : expr)
  | Sstore (chunk : memory_chunk) (addr : addressing) (args : exprlist)
      (value : expr)
  | Scall (result : Option ident) (sig : signature) (callee : Sum expr ident)
      (args : exprlist)
  | Stailcall (sig : signature) (callee : Sum expr ident) (args : exprlist)
  | Sbuiltin (result : builtin_res ident) (ef : external_function)
      (args : List (builtin_arg expr))
  | Sseq (first second : stmt)
  | Sifthenelse (condition : condexpr) (ifso ifnot : stmt)
  | Sloop (body : stmt)
  | Sblock (body : stmt)
  | Sexit (depth : Nat)
  | Sswitch (exit : exitexpr)
  | Sreturn (value : Option expr)
  | Slabel (label : ident) (body : stmt)
  | Sgoto (label : ident)

export stmt (Sskip Sassign Sstore Scall Stailcall Sbuiltin Sseq Sifthenelse
  Sloop Sblock Sexit Sswitch Sreturn Slabel Sgoto)

structure function : Type where
  fn_sig : signature
  fn_params : List ident
  fn_vars : List ident
  fn_stackspace : Z
  fn_body : stmt

export function (fn_sig fn_params fn_vars fn_stackspace fn_body)

def fundef := CompCert4Lean.Common.AST.fundef function

def program := CompCert4Lean.Common.AST.program fundef Unit

def funsig : fundef → signature
  | .Internal f => f.fn_sig
  | .External ef => ef_sig ef

/-! ## Operational semantics -/

def genv := Genv.t fundef Unit

def letenv := List val

inductive cont : Type where
  | Kstop
  | Kseq (statement : stmt) (continuation : cont)
  | Kblock (continuation : cont)
  | Kcall (result : Option ident) (caller : function) (stackPointer : val)
      (locals : env) (continuation : cont)

export cont (Kstop Kseq Kblock Kcall)

inductive state : Type where
  | State (currentFunction : function) (statement : stmt) (continuation : cont)
      (stackPointer : val) (locals : env) (memory : mem)
  | Callstate (callee : fundef) (args : List val) (continuation : cont)
      (memory : mem)
  | returnState (result : val) (continuation : cont) (memory : mem)

export state (State Callstate)

mutual
  inductive eval_expr (xi : ExternalCalls) (ge : genv) (sp : val) (e : env)
      (m : mem) : letenv → expr → val → Prop where
    | var (le : letenv) (id : ident) (v : val)
        (hget : PTree.get id e = some v) :
        eval_expr xi ge sp e m le (.Evar id) v
    | eval_Eop (le : letenv) (op : operation) (al : exprlist)
        (vl : List val) (v : val)
        (hargs : eval_exprlist xi ge sp e m le al vl)
        (hop : eval_operation ge sp op vl m = some v) :
        eval_expr xi ge sp e m le (.Eop op al) v
    | eval_Eload (le : letenv) (chunk : memory_chunk) (addr : addressing)
        (al : exprlist) (vl : List val) (vaddr v : val)
        (hargs : eval_exprlist xi ge sp e m le al vl)
        (haddr : eval_addressing ge sp addr vl = some vaddr)
        (hload : Mem.loadv chunk m vaddr = some v) :
        eval_expr xi ge sp e m le (.Eload chunk addr al) v
    | eval_Econdition (le : letenv) (a : condexpr) (b c : expr) (va : Bool)
        (v : val)
        (hcond : eval_condexpr xi ge sp e m le a va)
        (hbranch : eval_expr xi ge sp e m le (if va then b else c) v) :
        eval_expr xi ge sp e m le (.Econdition a b c) v
    | eval_Elet (le : letenv) (a b : expr) (v1 v2 : val)
        (hbound : eval_expr xi ge sp e m le a v1)
        (hbody : eval_expr xi ge sp e m (v1 :: le) b v2) :
        eval_expr xi ge sp e m le (.Elet a b) v2
    | eval_Eletvar (le : letenv) (n : Nat) (v : val)
        (hget : nth_error le n = some v) :
        eval_expr xi ge sp e m le (.Eletvar n) v
    | builtin (le : letenv) (ef : external_function) (al : exprlist)
        (vl : List val) (v : val)
        (hargs : eval_exprlist xi ge sp e m le al vl)
        (hext : external_call xi ef (Genv.to_senv ge) vl m E0 v m) :
        eval_expr xi ge sp e m le (.Ebuiltin ef al) v
    | external (le : letenv) (id : ident) (sg : signature)
        (al : exprlist) (b : block) (ef : external_function) (vl : List val)
        (v : val)
        (hsymbol : Genv.find_symbol ge id = some b)
        (hfun : Genv.find_funct_ptr ge b = some (.External ef))
        (hsig : ef_sig ef = sg)
        (hargs : eval_exprlist xi ge sp e m le al vl)
        (hext : external_call xi ef (Genv.to_senv ge) vl m E0 v m) :
        eval_expr xi ge sp e m le (.Eexternal id sg al) v

  inductive eval_exprlist (xi : ExternalCalls) (ge : genv) (sp : val)
      (e : env) (m : mem) : letenv → exprlist → List val → Prop where
    | nil (le : letenv) :
        eval_exprlist xi ge sp e m le .Enil []
    | cons (le : letenv) (a1 : expr) (al : exprlist) (v1 : val)
        (vl : List val)
        (hhead : eval_expr xi ge sp e m le a1 v1)
        (htail : eval_exprlist xi ge sp e m le al vl) :
        eval_exprlist xi ge sp e m le (.Econs a1 al) (v1 :: vl)

  inductive eval_condexpr (xi : ExternalCalls) (ge : genv) (sp : val)
      (e : env) (m : mem) : letenv → condexpr → Bool → Prop where
    | condition (le : letenv) (cond : condition) (al : exprlist)
        (vl : List val) (vb : Bool)
        (hargs : eval_exprlist xi ge sp e m le al vl)
        (hcond : eval_condition cond vl m = some vb) :
        eval_condexpr xi ge sp e m le (.CEcond cond al) vb
    | eval_CEcondition (le : letenv) (a b c : condexpr) (va v : Bool)
        (hcondition : eval_condexpr xi ge sp e m le a va)
        (hbranch : eval_condexpr xi ge sp e m le (if va then b else c) v) :
        eval_condexpr xi ge sp e m le (.CEcondition a b c) v
    | eval_CElet (le : letenv) (a : expr) (b : condexpr) (v1 : val)
        (v2 : Bool)
        (hbound : eval_expr xi ge sp e m le a v1)
        (hbody : eval_condexpr xi ge sp e m (v1 :: le) b v2) :
        eval_condexpr xi ge sp e m le (.CElet a b) v2
end

export eval_expr (eval_Eop eval_Eload eval_Econdition eval_Elet eval_Eletvar)
export eval_condexpr (eval_CEcondition eval_CElet)

private structure EvalInductionResult (xi : ExternalCalls) (ge : genv)
    (sp : val) (e : env) (m : mem)
    (P : letenv → expr → val → Prop)
    (PList : letenv → exprlist → List val → Prop)
    (PCond : letenv → condexpr → Bool → Prop) : Prop where
  exprCase : ∀ le a v, eval_expr xi ge sp e m le a v → P le a v
  listCase : ∀ le al vl, eval_exprlist xi ge sp e m le al vl → PList le al vl
  condCase : ∀ le a v, eval_condexpr xi ge sp e m le a v → PCond le a v

private def evalInduction (xi : ExternalCalls) (ge : genv) (sp : val)
    (e : env) (m : mem)
    (P : letenv → expr → val → Prop)
    (PList : letenv → exprlist → List val → Prop)
    (PCond : letenv → condexpr → Bool → Prop)
    (fVar : ∀ le id v, PTree.get id e = some v → P le (.Evar id) v)
    (fOp : ∀ le op al vl v,
      eval_exprlist xi ge sp e m le al vl → PList le al vl →
      eval_operation ge sp op vl m = some v → P le (.Eop op al) v)
    (fLoad : ∀ le chunk addr al vl vaddr v,
      eval_exprlist xi ge sp e m le al vl → PList le al vl →
      eval_addressing ge sp addr vl = some vaddr →
      Mem.loadv chunk m vaddr = some v → P le (.Eload chunk addr al) v)
    (fCondition : ∀ le a b c va v,
      eval_condexpr xi ge sp e m le a va → PCond le a va →
      eval_expr xi ge sp e m le (if va then b else c) v →
      P le (if va then b else c) v → P le (.Econdition a b c) v)
    (fLet : ∀ le a b v1 v2,
      eval_expr xi ge sp e m le a v1 → P le a v1 →
      eval_expr xi ge sp e m (v1 :: le) b v2 → P (v1 :: le) b v2 →
      P le (.Elet a b) v2)
    (fLetVar : ∀ le n v, nth_error le n = some v → P le (.Eletvar n) v)
    (fBuiltin : ∀ le ef al vl v,
      eval_exprlist xi ge sp e m le al vl → PList le al vl →
      external_call xi ef (Genv.to_senv ge) vl m E0 v m →
      P le (.Ebuiltin ef al) v)
    (fExternal : ∀ le id sg al b ef vl v,
      Genv.find_symbol ge id = some b →
      Genv.find_funct_ptr ge b = some (.External ef) → ef_sig ef = sg →
      eval_exprlist xi ge sp e m le al vl → PList le al vl →
      external_call xi ef (Genv.to_senv ge) vl m E0 v m →
      P le (.Eexternal id sg al) v)
    (fNil : ∀ le, PList le .Enil [])
    (fCons : ∀ le a al v vl,
      eval_expr xi ge sp e m le a v → P le a v →
      eval_exprlist xi ge sp e m le al vl → PList le al vl →
      PList le (.Econs a al) (v :: vl))
    (fCEcond : ∀ le cond al vl vb,
      eval_exprlist xi ge sp e m le al vl → PList le al vl →
      eval_condition cond vl m = some vb → PCond le (.CEcond cond al) vb)
    (fCEcondition : ∀ le a b c va v,
      eval_condexpr xi ge sp e m le a va → PCond le a va →
      eval_condexpr xi ge sp e m le (if va then b else c) v →
      PCond le (if va then b else c) v → PCond le (.CEcondition a b c) v)
    (fCElet : ∀ le a b v1 v2,
      eval_expr xi ge sp e m le a v1 → P le a v1 →
      eval_condexpr xi ge sp e m (v1 :: le) b v2 → PCond (v1 :: le) b v2 →
      PCond le (.CElet a b) v2) :
    EvalInductionResult xi ge sp e m P PList PCond :=
  let gOp := fun le op al vl v hargs hop ih =>
    fOp le op al vl v hargs ih hop
  let gLoad := fun le chunk addr al vl vaddr v hargs haddr hload ih =>
    fLoad le chunk addr al vl vaddr v hargs ih haddr hload
  let gCondition := fun le a b c va v hcond hbranch ihCond ihBranch =>
    fCondition le a b c va v hcond ihCond hbranch ihBranch
  let gLet := fun le a b v1 v2 hbound hbody ihBound ihBody =>
    fLet le a b v1 v2 hbound ihBound hbody ihBody
  let gBuiltin := fun le ef al vl v hargs hext ih =>
    fBuiltin le ef al vl v hargs ih hext
  let gExternal := fun le id sg al b ef vl v hsymbol hfun hsig hargs hext ih =>
    fExternal le id sg al b ef vl v hsymbol hfun hsig hargs ih hext
  let gCons := fun le a al v vl hhead htail ihHead ihTail =>
    fCons le a al v vl hhead ihHead htail ihTail
  let gCEcond := fun le cond al vl vb hargs hcond ih =>
    fCEcond le cond al vl vb hargs ih hcond
  let gCEcondition := fun le a b c va v hcond hbranch ihCond ihBranch =>
    fCEcondition le a b c va v hcond ihCond hbranch ihBranch
  let gCElet := fun le a b v1 v2 hbound hbody ihBound ihBody =>
    fCElet le a b v1 v2 hbound ihBound hbody ihBody
  { exprCase := @eval_expr.rec xi ge sp e m
      (fun le a v _ => P le a v)
      (fun le al vl _ => PList le al vl)
      (fun le a v _ => PCond le a v)
      fVar gOp gLoad gCondition gLet fLetVar gBuiltin gExternal fNil gCons
      gCEcond gCEcondition gCElet
    listCase := @eval_exprlist.rec xi ge sp e m
      (fun le a v _ => P le a v)
      (fun le al vl _ => PList le al vl)
      (fun le a v _ => PCond le a v)
      fVar gOp gLoad gCondition gLet fLetVar gBuiltin gExternal fNil gCons
      gCEcond gCEcondition gCElet
    condCase := @eval_condexpr.rec xi ge sp e m
      (fun le a v _ => P le a v)
      (fun le al vl _ => PList le al vl)
      (fun le a v _ => PCond le a v)
      fVar gOp gLoad gCondition gLet fLetVar gBuiltin gExternal fNil gCons
      gCEcond gCEcondition gCElet }

def eval_expr_ind3 := fun xi ge sp e m P PList PCond fVar fOp fLoad
    fCondition fLet fLetVar fBuiltin fExternal fNil fCons fCEcond fCEcondition
    fCElet =>
  (evalInduction xi ge sp e m P PList PCond fVar fOp fLoad fCondition fLet
    fLetVar fBuiltin fExternal fNil fCons fCEcond fCEcondition fCElet).exprCase

def eval_exprlist_ind3 := fun xi ge sp e m P PList PCond fVar fOp fLoad
    fCondition fLet fLetVar fBuiltin fExternal fNil fCons fCEcond fCEcondition
    fCElet =>
  (evalInduction xi ge sp e m P PList PCond fVar fOp fLoad fCondition fLet
    fLetVar fBuiltin fExternal fNil fCons fCEcond fCEcondition fCElet).listCase

def eval_condexpr_ind3 := fun xi ge sp e m P PList PCond fVar fOp fLoad
    fCondition fLet fLetVar fBuiltin fExternal fNil fCons fCEcond fCEcondition
    fCElet =>
  (evalInduction xi ge sp e m P PList PCond fVar fOp fLoad fCondition fLet
    fLetVar fBuiltin fExternal fNil fCons fCEcond fCEcondition fCElet).condCase

inductive eval_exitexpr (xi : ExternalCalls) (ge : genv) (sp : val) (e : env)
    (m : mem) : letenv → exitexpr → Nat → Prop where
  | exit (le : letenv) (x : Nat) :
      eval_exitexpr xi ge sp e m le (.XEexit x) x
  | jumptable (le : letenv) (a : expr) (table : List Nat)
      (n : CCInt) (x : Nat)
      (heval : eval_expr xi ge sp e m le a (.Vint n))
      (hlookup : list_nth_z table (Int.unsigned n) = some x) :
      eval_exitexpr xi ge sp e m le (.XEjumptable a table) x
  | eval_XEcondition (le : letenv) (a : condexpr) (b c : exitexpr)
      (va : Bool) (x : Nat)
      (hcondition : eval_condexpr xi ge sp e m le a va)
      (hbranch : eval_exitexpr xi ge sp e m le (if va then b else c) x) :
      eval_exitexpr xi ge sp e m le (.XEcondition a b c) x
  | letBinding (le : letenv) (a : expr) (b : exitexpr) (v : val) (x : Nat)
      (hbound : eval_expr xi ge sp e m le a v)
      (hbody : eval_exitexpr xi ge sp e m (v :: le) b x) :
      eval_exitexpr xi ge sp e m le (.XElet a b) x

export eval_exitexpr (eval_XEcondition)

private inductive evalExprOrSymbol (xi : ExternalCalls) (ge : genv) (sp : val)
    (e : env) (m : mem) : letenv → Sum expr ident → val → Prop where
  | expression (le : letenv) (a : expr) (v : val)
      (heval : eval_expr xi ge sp e m le a v) :
      evalExprOrSymbol xi ge sp e m le (.inl a) v
  | symbol (le : letenv) (id : ident) (b : block)
      (hfind : Genv.find_symbol ge id = some b) :
      evalExprOrSymbol xi ge sp e m le (.inr id) (.Vptr b Ptrofs.zero)

inductive eval_builtin_arg (xi : ExternalCalls) (ge : genv) (sp : val)
    (e : env) (m : mem) : builtin_arg expr → val → Prop where
  | argument (a : expr) (v : val)
      (heval : eval_expr xi ge sp e m [] a v) :
      eval_builtin_arg xi ge sp e m (.BA a) v
  | intValue (n : CCInt) :
      eval_builtin_arg xi ge sp e m (.BA_int n) (.Vint n)
  | longValue (n : int64) :
      eval_builtin_arg xi ge sp e m (.BA_long n) (.Vlong n)
  | floatValue (n : CompCert4Lean.Lib.Floats.float) :
      eval_builtin_arg xi ge sp e m (.BA_float n) (.Vfloat n)
  | singleValue (n : CompCert4Lean.Lib.Floats.float32) :
      eval_builtin_arg xi ge sp e m (.BA_single n) (.Vsingle n)
  | loadStack (chunk : memory_chunk) (ofs : Ptrofs) (v : val)
      (hload : Mem.loadv chunk m (Val.offset_ptr sp ofs) = some v) :
      eval_builtin_arg xi ge sp e m (.BA_loadstack chunk ofs) v
  | addressStack (ofs : Ptrofs) :
      eval_builtin_arg xi ge sp e m (.BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | loadGlobal (chunk : memory_chunk) (id : ident) (ofs : Ptrofs)
      (v : val)
      (hload : Mem.loadv chunk m (Genv.symbol_address ge id ofs) = some v) :
      eval_builtin_arg xi ge sp e m (.BA_loadglobal chunk id ofs) v
  | addressGlobal (id : ident) (ofs : Ptrofs) :
      eval_builtin_arg xi ge sp e m (.BA_addrglobal id ofs)
        (Genv.symbol_address ge id ofs)
  | splitLong (a1 a2 : expr) (v1 v2 : val)
      (h1 : eval_expr xi ge sp e m [] a1 v1)
      (h2 : eval_expr xi ge sp e m [] a2 v2) :
      eval_builtin_arg xi ge sp e m (.BA_splitlong (.BA a1) (.BA a2))
        (Val.longofwords v1 v2)
  | addPointer (a1 a2 : builtin_arg expr) (v1 v2 : val)
      (h1 : eval_builtin_arg xi ge sp e m a1 v1)
      (h2 : eval_builtin_arg xi ge sp e m a2 v2) :
      eval_builtin_arg xi ge sp e m (.BA_addptr a1 a2)
        (if CompCert4Lean.X86_64.Archi.ptr64 then Val.addl v1 v2
         else Val.add v1 v2)

def set_builtin_res (res : builtin_res ident) (v : val) (e : env) : env :=
  match res with
  | .BR id => PTree.set id v e
  | _ => e

def call_cont : cont → cont
  | .Kseq _ k => call_cont k
  | .Kblock k => call_cont k
  | k => k

def is_call_cont : cont → Prop
  | .Kstop => True
  | .Kcall _ _ _ _ _ => True
  | _ => False

def find_label (lbl : ident) : stmt → cont → Option (stmt × cont)
  | .Sseq s1 s2, k =>
      match find_label lbl s1 (.Kseq s2 k) with
      | some sk => some sk
      | none => find_label lbl s2 k
  | .Sifthenelse _ s1 s2, k =>
      match find_label lbl s1 k with
      | some sk => some sk
      | none => find_label lbl s2 k
  | .Sloop s, k => find_label lbl s (.Kseq (.Sloop s) k)
  | .Sblock s, k => find_label lbl s (.Kblock k)
  | .Slabel lbl' s, k =>
      match ident_eq lbl lbl' with
      | .left _ => some (s, k)
      | .right _ => find_label lbl s k
  | _, _ => none

inductive step (xi : ExternalCalls) (ge : genv) : state → trace → state → Prop where
  | skipSequence (f : function) (s : stmt) (k : cont) (sp : val) (e : env)
      (m : mem) :
      step xi ge (.State f .Sskip (.Kseq s k) sp e m) E0
        (.State f s k sp e m)
  | skipBlock (f : function) (k : cont) (sp : val) (e : env) (m : mem) :
      step xi ge (.State f .Sskip (.Kblock k) sp e m) E0
        (.State f .Sskip k sp e m)
  | skipCall (f : function) (k : cont) (sp : block) (e : env) (m m' : mem)
      (hcall : is_call_cont k)
      (hfree : Mem.free m sp z0 f.fn_stackspace = some m') :
      step xi ge (.State f .Sskip k (.Vptr sp Ptrofs.zero) e m) E0
        (.returnState Vundef k m')
  | assign (f : function) (id : ident) (a : expr) (k : cont) (sp : val)
      (e : env) (m : mem) (v : val)
      (heval : eval_expr xi ge sp e m [] a v) :
      step xi ge (.State f (.Sassign id a) k sp e m) E0
        (.State f .Sskip k sp (PTree.set id v e) m)
  | step_store (f : function) (chunk : memory_chunk) (addr : addressing)
      (al : exprlist) (b : expr) (k : cont) (sp : val) (e : env) (m : mem)
      (vl : List val) (v vaddr : val) (m' : mem)
      (hargs : eval_exprlist xi ge sp e m [] al vl)
      (hvalue : eval_expr xi ge sp e m [] b v)
      (haddr : eval_addressing ge sp addr vl = some vaddr)
      (hstore : Mem.storev chunk m vaddr v = some m') :
      step xi ge (.State f (.Sstore chunk addr al b) k sp e m) E0
        (.State f .Sskip k sp e m')
  | call (f : function) (optid : Option ident) (sig : signature)
      (a : Sum expr ident) (bl : exprlist) (k : cont) (sp : val) (e : env)
      (m : mem) (vf : val) (vargs : List val) (fd : fundef)
      (hcallee : evalExprOrSymbol xi ge sp e m [] a vf)
      (hargs : eval_exprlist xi ge sp e m [] bl vargs)
      (hfind : Genv.find_funct ge vf = some fd)
      (hsig : funsig fd = sig) :
      step xi ge (.State f (.Scall optid sig a bl) k sp e m) E0
        (.Callstate fd vargs (.Kcall optid f sp e k) m)
  | tailcall (f : function) (sig : signature) (a : Sum expr ident)
      (bl : exprlist) (k : cont) (sp : block) (e : env) (m : mem) (vf : val)
      (vargs : List val) (fd : fundef) (m' : mem)
      (hcallee : evalExprOrSymbol xi ge (.Vptr sp Ptrofs.zero) e m [] a vf)
      (hargs : eval_exprlist xi ge (.Vptr sp Ptrofs.zero) e m [] bl vargs)
      (hfind : Genv.find_funct ge vf = some fd)
      (hsig : funsig fd = sig)
      (hfree : Mem.free m sp z0 f.fn_stackspace = some m') :
      step xi ge (.State f (.Stailcall sig a bl) k (.Vptr sp Ptrofs.zero) e m) E0
        (.Callstate fd vargs (call_cont k) m')
  | builtinCall (f : function) (res : builtin_res ident) (ef : external_function)
      (al : List (builtin_arg expr)) (k : cont) (sp : val) (e : env) (m : mem)
      (vl : List val) (t : trace) (v : val) (m' : mem)
      (hargs : list_forall2 (eval_builtin_arg xi ge sp e m) al vl)
      (hext : external_call xi ef (Genv.to_senv ge) vl m t v m') :
      step xi ge (.State f (.Sbuiltin res ef al) k sp e m) t
        (.State f .Sskip k sp (set_builtin_res res v e) m')
  | sequence (f : function) (s1 s2 : stmt) (k : cont) (sp : val) (e : env)
      (m : mem) :
      step xi ge (.State f (.Sseq s1 s2) k sp e m) E0
        (.State f s1 (.Kseq s2 k) sp e m)
  | conditional (f : function) (c : condexpr) (s1 s2 : stmt) (k : cont)
      (sp : val) (e : env) (m : mem) (b : Bool)
      (heval : eval_condexpr xi ge sp e m [] c b) :
      step xi ge (.State f (.Sifthenelse c s1 s2) k sp e m) E0
        (.State f (if b then s1 else s2) k sp e m)
  | loop (f : function) (s : stmt) (k : cont) (sp : val) (e : env)
      (m : mem) :
      step xi ge (.State f (.Sloop s) k sp e m) E0
        (.State f s (.Kseq (.Sloop s) k) sp e m)
  | blockStep (f : function) (s : stmt) (k : cont) (sp : val) (e : env)
      (m : mem) :
      step xi ge (.State f (.Sblock s) k sp e m) E0
        (.State f s (.Kblock k) sp e m)
  | exitSequence (f : function) (n : Nat) (s : stmt) (k : cont) (sp : val)
      (e : env) (m : mem) :
      step xi ge (.State f (.Sexit n) (.Kseq s k) sp e m) E0
        (.State f (.Sexit n) k sp e m)
  | exitBlockZero (f : function) (k : cont) (sp : val) (e : env) (m : mem) :
      step xi ge (.State f (.Sexit 0) (.Kblock k) sp e m) E0
        (.State f .Sskip k sp e m)
  | exitBlockSucc (f : function) (n : Nat) (k : cont) (sp : val) (e : env)
      (m : mem) :
      step xi ge (.State f (.Sexit (n + 1)) (.Kblock k) sp e m) E0
        (.State f (.Sexit n) k sp e m)
  | switch (f : function) (a : exitexpr) (k : cont) (sp : val) (e : env)
      (m : mem) (n : Nat)
      (heval : eval_exitexpr xi ge sp e m [] a n) :
      step xi ge (.State f (.Sswitch a) k sp e m) E0
        (.State f (.Sexit n) k sp e m)
  | returnNone (f : function) (k : cont) (sp : block) (e : env) (m m' : mem)
      (hfree : Mem.free m sp z0 f.fn_stackspace = some m') :
      step xi ge (.State f (.Sreturn none) k (.Vptr sp Ptrofs.zero) e m) E0
        (.returnState Vundef (call_cont k) m')
  | returnSome (f : function) (a : expr) (k : cont) (sp : block) (e : env)
      (m : mem) (v : val) (m' : mem)
      (heval : eval_expr xi ge (.Vptr sp Ptrofs.zero) e m [] a v)
      (hfree : Mem.free m sp z0 f.fn_stackspace = some m') :
      step xi ge (.State f (.Sreturn (some a)) k (.Vptr sp Ptrofs.zero) e m) E0
        (.returnState v (call_cont k) m')
  | label (f : function) (lbl : ident) (s : stmt) (k : cont) (sp : val)
      (e : env) (m : mem) :
      step xi ge (.State f (.Slabel lbl s) k sp e m) E0
        (.State f s k sp e m)
  | gotoLabel (f : function) (lbl : ident) (k : cont) (sp : val) (e : env)
      (m : mem) (s' : stmt) (k' : cont)
      (hfind : find_label lbl f.fn_body (call_cont k) = some (s', k')) :
      step xi ge (.State f (.Sgoto lbl) k sp e m) E0
        (.State f s' k' sp e m)
  | internalFunction (f : function) (vargs : List val) (k : cont)
      (m m' : mem) (sp : block) (e : env)
      (htypes : Val.has_argtype_list vargs f.fn_sig.sig_args)
      (halloc : Mem.alloc m z0 f.fn_stackspace = (m', sp))
      (henv : CompCert4Lean.Backend.Cminor.set_locals f.fn_vars
        (CompCert4Lean.Backend.Cminor.set_params vargs f.fn_params) = e) :
      step xi ge (.Callstate (.Internal f) vargs k m) E0
        (.State f f.fn_body k (.Vptr sp Ptrofs.zero) e m')
  | externalFunction (ef : external_function) (vargs : List val) (k : cont)
      (m : mem) (t : trace) (v : val) (m' : mem)
      (hext : external_call xi ef (Genv.to_senv ge) vargs m t v m') :
      step xi ge (.Callstate (.External ef) vargs k m) t
        (.returnState v k m')
  | returnToCaller (v : val) (optid : Option ident) (f : function) (sp : val)
      (e : env) (k : cont) (m : mem) :
      step xi ge (.returnState v (.Kcall optid f sp e k) m) E0
        (.State f .Sskip k sp
          (CompCert4Lean.Backend.Cminor.set_optvar optid v e) m)

export step (step_store)

inductive initial_state (p : program) : state → Prop where
  | intro (b : block) (f : fundef) (m0 : mem)
      (hmem : Genv.init_mem p = some m0)
      (hsymbol : Genv.find_symbol (Genv.globalenv p) p.prog_main = some b)
      (hfun : Genv.find_funct_ptr (Genv.globalenv p) b = some f)
      (hsig : funsig f = signature_main) :
      initial_state p (.Callstate f [] .Kstop m0)

inductive final_state : state → CCInt → Prop where
  | intro (r : CCInt) (m : mem) :
      final_state (.returnState (.Vint r) .Kstop m) r

def semantics (xi : ExternalCalls) (p : program) :
    CompCert4Lean.Common.Smallstep.semantics :=
  Semantics (step xi) (initial_state p) final_state (Genv.globalenv p)

/-! ## Lifting let-bound variables -/

mutual
  def lift_expr (p : Nat) : expr → expr
    | .Evar id => .Evar id
    | .Eop op al => .Eop op (lift_exprlist p al)
    | .Eload chunk addr al => .Eload chunk addr (lift_exprlist p al)
    | .Econdition a b c =>
        .Econdition (lift_condexpr p a) (lift_expr p b) (lift_expr p c)
    | .Elet b c => .Elet (lift_expr p b) (lift_expr (p + 1) c)
    | .Eletvar n => if p ≤ n then .Eletvar (n + 1) else .Eletvar n
    | .Ebuiltin ef al => .Ebuiltin ef (lift_exprlist p al)
    | .Eexternal id sg al => .Eexternal id sg (lift_exprlist p al)

  def lift_exprlist (p : Nat) : exprlist → exprlist
    | .Enil => .Enil
    | .Econs b rest => .Econs (lift_expr p b) (lift_exprlist p rest)

  def lift_condexpr (p : Nat) : condexpr → condexpr
    | .CEcond c al => .CEcond c (lift_exprlist p al)
    | .CEcondition a b c =>
        .CEcondition (lift_condexpr p a) (lift_condexpr p b) (lift_condexpr p c)
    | .CElet a b => .CElet (lift_expr p a) (lift_condexpr (p + 1) b)
end

def lift (a : expr) : expr := lift_expr 0 a

inductive insert_lenv : letenv → Nat → val → letenv → Prop where
  | insert_lenv_0 (le : letenv) (v : val) :
      insert_lenv le 0 v (v :: le)
  | insert_lenv_S (le : letenv) (p : Nat) (w : val) (le' : letenv) (v : val)
      (hinsert : insert_lenv le p w le') :
      insert_lenv (v :: le) (p + 1) w (v :: le')

export insert_lenv (insert_lenv_0 insert_lenv_S)

def insert_lenv_lookup1Statement : Prop :=
  ∀ (le : letenv) (p : Nat) (w : val) (le' : letenv),
    insert_lenv le p w le' →
      ∀ (n : Nat) (v : val), nth_error le n = some v → p > n →
        nth_error le' n = some v

def insert_lenv_lookup2Statement : Prop :=
  ∀ (le : letenv) (p : Nat) (w : val) (le' : letenv),
    insert_lenv le p w le' →
      ∀ (n : Nat) (v : val), nth_error le n = some v → p ≤ n →
        nth_error le' (n + 1) = some v

def eval_lift_exprStatement : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (w : val) (le : letenv) (a : expr) (v : val),
    eval_expr xi ge sp e m le a v →
      ∀ (p : Nat) (le' : letenv), insert_lenv le p w le' →
        eval_expr xi ge sp e m le' (lift_expr p a) v

def eval_liftStatement : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (v w : val),
    eval_expr xi ge sp e m le a v →
      eval_expr xi ge sp e m (w :: le) (lift a) v

end CompCert4Lean.Backend.CminorSel
