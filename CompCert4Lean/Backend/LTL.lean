import CompCert4Lean.Backend.Conventions
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.X86.Op

/-!
# Location transfer language

Definition-bearing translation of CompCert's `backend/LTL.v`.  The external-
call environment and immutable ABI configuration are threaded explicitly
through the transition relation and whole-program semantics, following the
integrated Events and calling-convention APIs.
-/

namespace CompCert4Lean.Backend.LTL

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev isCalleeSave := CompCert4Lean.X86.Conventions1.is_callee_save
private abbrev locArguments := CompCert4Lean.X86.Conventions1.loc_arguments
private abbrev locResult := CompCert4Lean.X86.Conventions1.loc_result

/-! ## Abstract syntax -/

def node : Type := positive

inductive instruction : Type where
  | Lop (op : operation) (args : List mreg) (res : mreg)
  | Lload (chunk : memory_chunk) (addr : addressing) (args : List mreg)
      (dst : mreg)
  | Lgetstack (sl : slot) (ofs : Z) (ty : typ) (dst : mreg)
  | Lsetstack (src : mreg) (sl : slot) (ofs : Z) (ty : typ)
  | Lstore (chunk : memory_chunk) (addr : addressing) (args : List mreg)
      (src : mreg)
  | Lcall (sig : signature) (ros : Sum mreg ident)
  | Ltailcall (sig : signature) (ros : Sum mreg ident)
  | Lbuiltin (ef : external_function) (args : List (builtin_arg loc))
      (res : builtin_res mreg)
  | Lbranch (succ : node)
  | Lcond (cond : condition) (args : List mreg) (ifso ifnot : node)
  | Ljumptable (arg : mreg) (tbl : List node)
  | Lreturn

export instruction
  (Lop Lload Lgetstack Lsetstack Lstore Lcall Ltailcall Lbuiltin Lbranch Lcond
    Ljumptable Lreturn)

def bblock : Type := List instruction

def code : Type := PTree.t bblock

structure function : Type where
  fn_sig : signature
  fn_stacksize : Z
  fn_code : code
  fn_entrypoint : node

export function (fn_sig fn_stacksize fn_code fn_entrypoint)

def fundef : Type := CompCert4Lean.Common.AST.fundef function

def program : Type := CompCert4Lean.Common.AST.program fundef Unit

def funsig : fundef → signature
  | .Internal f => f.fn_sig
  | .External ef => ef_sig ef

/-! ## Operational semantics -/

def genv : Type := Genv.t fundef Unit

def locset : Type := Locmap.t

def call_regs (caller : locset) : locset :=
  fun l =>
    match l with
    | .R r => caller (R r)
    | .S .Local _ _ => Vundef
    | .S .Incoming ofs ty => caller (S Outgoing ofs ty)
    | .S .Outgoing _ _ => Vundef

def return_regs (cfg : CompilerConfig) (caller callee : locset) : locset :=
  fun l =>
    match l with
    | .R r => if isCalleeSave cfg r then caller (R r) else callee (R r)
    | .S .Outgoing _ _ => Vundef
    | .S sl ofs ty => caller (S sl ofs ty)

def undef_caller_save_regs (cfg : CompilerConfig) (ls : locset) : locset :=
  fun l =>
    match l with
    | .R r => if isCalleeSave cfg r then ls (R r) else Vundef
    | .S .Outgoing _ _ => Vundef
    | .S sl ofs ty => ls (S sl ofs ty)

inductive stackframe : Type where
  | Stackframe (f : function) (sp : val) (ls : locset) (bb : bblock)

export stackframe (Stackframe)

inductive state : Type where
  | State (stack : List stackframe) (f : function) (sp : val) (pc : node)
      (ls : locset) (m : mem)
  | Block (stack : List stackframe) (f : function) (sp : val) (bb : bblock)
      (ls : locset) (m : mem)
  | Callstate (stack : List stackframe) (f : fundef) (ls : locset) (m : mem)
  | Returnstate (stack : List stackframe) (ls : locset) (m : mem)

export state (State Block Callstate Returnstate)

def reglist (rs : locset) (rl : List mreg) : List val :=
  rl.map (fun r => rs (R r))

def undef_regs : List mreg → locset → locset
  | [], rs => rs
  | r :: rl, rs => Locmap.set (R r) Vundef (undef_regs rl rs)

def destroyed_by_getstack : slot → List mreg
  | .Incoming => [temp_for_parent_frame]
  | _ => []

def find_function (ge : genv) (ros : Sum mreg ident) (rs : locset) : Option fundef :=
  match ros with
  | .inl r => Genv.find_funct ge (rs (R r))
  | .inr symb =>
      match Genv.find_symbol ge symb with
      | none => none
      | some b => Genv.find_funct_ptr ge b

def parent_locset : List stackframe → locset
  | [] => Locmap.init Vundef
  | Stackframe _ _ ls _ :: _ => ls

inductive step (cfg : CompilerConfig) (xi : ExternalCalls) (ge : genv) :
    state → trace → state → Prop where
  | exec_Lop
      (s : List stackframe) (f : function) (sp : val) (op : operation)
      (args : List mreg) (res : mreg) (bb : bblock) (rs : locset) (m : mem)
      (v : val) (rs' : locset)
      (heval : eval_operation ge sp op (reglist rs args) m = some v)
      (hrs : rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs)) :
      step cfg xi ge (Block s f sp (Lop op args res :: bb) rs m) E0
        (Block s f sp bb rs' m)
  | exec_Lload
      (s : List stackframe) (f : function) (sp : val) (chunk : memory_chunk)
      (addr : addressing) (args : List mreg) (dst : mreg) (bb : bblock)
      (rs : locset) (m : mem) (a v : val) (rs' : locset)
      (haddr : eval_addressing ge sp addr (reglist rs args) = some a)
      (hload : Mem.loadv chunk m a = some v)
      (hrs : rs' = Locmap.set (R dst) v
        (undef_regs (destroyed_by_load chunk addr) rs)) :
      step cfg xi ge (Block s f sp (Lload chunk addr args dst :: bb) rs m) E0
        (Block s f sp bb rs' m)
  | exec_Lstore
      (s : List stackframe) (f : function) (sp : val) (chunk : memory_chunk)
      (addr : addressing) (args : List mreg) (src : mreg) (bb : bblock)
      (rs : locset) (m : mem) (a : val) (rs' : locset) (m' : mem)
      (haddr : eval_addressing ge sp addr (reglist rs args) = some a)
      (hstore : Mem.storev chunk m a (rs (R src)) = some m')
      (hrs : rs' = undef_regs (destroyed_by_store chunk addr) rs) :
      step cfg xi ge (Block s f sp (Lstore chunk addr args src :: bb) rs m) E0
        (Block s f sp bb rs' m')
  | exec_Lcall
      (s : List stackframe) (f : function) (sp : val) (sig : signature)
      (ros : Sum mreg ident) (bb : bblock) (rs : locset) (m : mem)
      (fd : fundef)
      (hfind : find_function ge ros rs = some fd)
      (hsig : funsig fd = sig) :
      step cfg xi ge (Block s f sp (Lcall sig ros :: bb) rs m) E0
        (Callstate (Stackframe f sp rs bb :: s) fd rs m)
  | exec_Ltailcall
      (s : List stackframe) (f : function) (stk : block) (sig : signature)
      (ros : Sum mreg ident) (bb : bblock) (rs : locset) (m : mem)
      (fd : fundef) (rs' : locset) (m' : mem)
      (hrs : rs' = return_regs cfg (parent_locset s) rs)
      (hfind : find_function ge ros rs' = some fd)
      (hsig : funsig fd = sig)
      (hfree : Mem.free m stk .Z0 f.fn_stacksize = some m') :
      step cfg xi ge
        (Block s f (Vptr stk Ptrofs.zero) (Ltailcall sig ros :: bb) rs m) E0
        (Callstate s fd rs' m')
  | exec_Lbuiltin
      (s : List stackframe) (f : function) (sp : val) (ef : external_function)
      (args : List (builtin_arg loc)) (res : builtin_res mreg) (bb : bblock)
      (rs : locset) (m : mem) (vargs : List val) (t : trace) (vres : val)
      (rs' : locset) (m' : mem)
      (hargs : eval_builtin_args (Genv.to_senv ge) rs sp m args vargs)
      (hcall : external_call xi ef (Genv.to_senv ge) vargs m t vres m')
      (hrs : rs' = Locmap.setres res vres
        (undef_regs (destroyed_by_builtin ef) rs)) :
      step cfg xi ge (Block s f sp (Lbuiltin ef args res :: bb) rs m) t
        (Block s f sp bb rs' m')
  | exec_Lbranch
      (s : List stackframe) (f : function) (sp : val) (pc : node)
      (bb : bblock) (rs : locset) (m : mem) :
      step cfg xi ge (Block s f sp (Lbranch pc :: bb) rs m) E0
        (State s f sp pc rs m)
  | exec_Lcond
      (s : List stackframe) (f : function) (sp : val) (cond : condition)
      (args : List mreg) (pc1 pc2 : node) (bb : bblock) (rs : locset)
      (b : Bool) (pc : node) (rs' : locset) (m : mem)
      (heval : eval_condition cond (reglist rs args) m = some b)
      (hpc : pc = if b then pc1 else pc2)
      (hrs : rs' = undef_regs (destroyed_by_cond cond) rs) :
      step cfg xi ge (Block s f sp (Lcond cond args pc1 pc2 :: bb) rs m) E0
        (State s f sp pc rs' m)
  | exec_Ljumptable
      (s : List stackframe) (f : function) (sp : val) (arg : mreg)
      (tbl : List node) (bb : bblock) (rs : locset) (m : mem) (n : int)
      (pc : node) (rs' : locset)
      (harg : rs (R arg) = Vint n)
      (hnth : list_nth_z tbl (Int.unsigned n) = some pc)
      (hrs : rs' = undef_regs destroyed_by_jumptable rs) :
      step cfg xi ge (Block s f sp (Ljumptable arg tbl :: bb) rs m) E0
        (State s f sp pc rs' m)
  | exec_Lreturn
      (s : List stackframe) (f : function) (stk : block) (bb : bblock)
      (rs : locset) (m m' : mem)
      (hfree : Mem.free m stk .Z0 f.fn_stacksize = some m') :
      step cfg xi ge
        (Block s f (Vptr stk Ptrofs.zero) (Lreturn :: bb) rs m) E0
        (Returnstate s (return_regs cfg (parent_locset s) rs) m')
  | exec_function_internal
      (s : List stackframe) (f : function) (rs : locset) (m m' : mem)
      (stk : block) (rs' : locset)
      (halloc : Mem.alloc m .Z0 f.fn_stacksize = (m', stk))
      (hrs : rs' = undef_regs destroyed_at_function_entry (call_regs rs)) :
      step cfg xi ge (Callstate s (Internal f) rs m) E0
        (State s f (Vptr stk Ptrofs.zero) f.fn_entrypoint rs' m')
  | exec_function_external
      (s : List stackframe) (ef : external_function) (t : trace)
      (args : List val) (res : val) (rs : locset) (m : mem) (rs' : locset)
      (m' : mem)
      (hargs : args =
        (locArguments cfg (ef_sig ef)).map (fun p => Locmap.getpair p rs))
      (hcall : external_call xi ef (Genv.to_senv ge) args m t res m')
      (hrs : rs' = Locmap.setpair (locResult (ef_sig ef)) res
        (undef_caller_save_regs cfg rs)) :
      step cfg xi ge (Callstate s (External ef) rs m) t
        (Returnstate s rs' m')
  | exec_return
      (f : function) (sp : val) (rs1 : locset) (bb : bblock)
      (s : List stackframe) (rs : locset) (m : mem) :
      step cfg xi ge (Returnstate (Stackframe f sp rs1 bb :: s) rs m) E0
        (Block s f sp bb rs m)

export step
  (exec_Lop exec_Lload exec_Lstore exec_Lcall exec_Ltailcall exec_Lbuiltin
    exec_Lbranch exec_Lcond exec_Ljumptable exec_Lreturn
    exec_function_internal exec_function_external exec_return)

inductive initial_state (p : program) : state → Prop where
  | intro (b : block) (f : fundef) (m0 : mem)
      (hmem : Genv.init_mem p = some m0)
      (hsymb : Genv.find_symbol (Genv.globalenv p) p.prog_main = some b)
      (hfun : Genv.find_funct_ptr (Genv.globalenv p) b = some f)
      (hsig : funsig f = signature_main) :
      initial_state p (Callstate [] f (Locmap.init Vundef) m0)

inductive final_state : state → int → Prop where
  | intro (rs : locset) (m : mem) (retcode : int)
      (hresult : Locmap.getpair (map_rpair R (locResult signature_main)) rs =
        Vint retcode) :
      final_state (Returnstate [] rs m) retcode

def semantics (cfg : CompilerConfig) (xi : ExternalCalls) (p : program) :
    CompCert4Lean.Common.Smallstep.semantics :=
  Semantics (step cfg xi) (initial_state p) final_state (Genv.globalenv p)

/-! ## Operations on LTL syntax -/

def successors_block : bblock → List node
  | [] => []
  | Ltailcall _ _ :: _ => []
  | Lbranch s :: _ => [s]
  | Lcond _ _ s1 s2 :: _ => [s1, s2]
  | Ljumptable _ tbl :: _ => tbl
  | Lreturn :: _ => []
  | _ :: rest => successors_block rest

end CompCert4Lean.Backend.LTL
