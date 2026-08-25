import CompCert4Lean.Backend.Locations
import CompCert4Lean.Backend.LTL
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Config
import CompCert4Lean.X86.Machregs
import CompCert4Lean.X86.Op
import CompCert4Lean.X86.Conventions1

/-!
# Linear intermediate language

Definition-bearing translation of CompCert's `backend/Linear.v`.  The
processor configuration and proof-bearing external-call environment are
explicit parameters of the executable semantics, as in the integrated
backend APIs.
-/

namespace CompCert4Lean.Backend.Linear

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
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev int := CompCert4Lean.Lib.Integers.int

private abbrev z0 : Z := .Z0
private abbrev locArguments := CompCert4Lean.X86.Conventions1.loc_arguments
private abbrev locResult := CompCert4Lean.X86.Conventions1.loc_result

/-! ## Abstract syntax -/

def label : Type := positive

inductive instruction : Type where
  | Lgetstack (sl : slot) (ofs : Z) (ty : typ) (dst : mreg)
  | Lsetstack (src : mreg) (sl : slot) (ofs : Z) (ty : typ)
  | Lop (op : operation) (args : List mreg) (res : mreg)
  | Lload (chunk : memory_chunk) (addr : addressing) (args : List mreg)
      (dst : mreg)
  | Lstore (chunk : memory_chunk) (addr : addressing) (args : List mreg)
      (src : mreg)
  | Lcall (sig : signature) (ros : Sum mreg ident)
  | Ltailcall (sig : signature) (ros : Sum mreg ident)
  | Lbuiltin (ef : external_function) (args : List (builtin_arg loc))
      (res : builtin_res mreg)
  | Llabel (lbl : label)
  | Lgoto (lbl : label)
  | Lcond (cond : condition) (args : List mreg) (lbl : label)
  | Ljumptable (arg : mreg) (tbl : List label)
  | Lreturn

export instruction
  (Lgetstack Lsetstack Lop Lload Lstore Lcall Ltailcall Lbuiltin Llabel Lgoto
    Lcond Ljumptable Lreturn)

def code : Type := List instruction

structure function : Type where
  fn_sig : signature
  fn_stacksize : Z
  fn_code : code

export function (fn_sig fn_stacksize fn_code)

def fundef : Type := CompCert4Lean.Common.AST.fundef function
def program : Type := CompCert4Lean.Common.AST.program fundef Unit

def funsig : fundef → signature
  | .Internal f => fn_sig f
  | .External ef => ef_sig ef

def genv : Type := Genv.t fundef Unit
def locset : Type := Locmap.t

/-! ## Label lookup and operational state -/

def is_label (lbl : label) (instr : instruction) : Bool :=
  match instr with
  | Llabel lbl' =>
      match peq lbl lbl' with
      | .left _ => true
      | .right _ => false
  | _ => false

def is_label_correctStatement : Prop :=
  ∀ lbl instr,
    if is_label lbl instr then instr = Llabel lbl else instr ≠ Llabel lbl

def find_label (lbl : label) (c : code) : Option code :=
  match c with
  | [] => none
  | i1 :: il => if is_label lbl i1 then some il else find_label lbl il

def find_function (ge : genv) (ros : Sum mreg ident) (rs : locset) : Option fundef :=
  match ros with
  | .inl r => Genv.find_funct ge (rs (R r))
  | .inr symb =>
      match Genv.find_symbol ge symb with
      | none => none
      | some b => Genv.find_funct_ptr ge b

inductive stackframe : Type where
  | Stackframe (f : function) (sp : val) (ls : locset) (c : code)

export stackframe (Stackframe)

def parent_locset : List stackframe → locset
  | [] => Locmap.init Vundef
  | Stackframe _ _ ls _ :: _ => ls

inductive state : Type where
  | State (stack : List stackframe) (f : function) (sp : val) (c : code)
      (rs : locset) (m : mem)
  | Callstate (stack : List stackframe) (f : fundef) (rs : locset) (m : mem)
  | Returnstate (stack : List stackframe) (rs : locset) (m : mem)

export state (State Callstate Returnstate)

/-! ## Transition semantics -/

inductive step
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompilerConfig) (xi : ExternalCalls) (ge : genv) :
    state → trace → state → Prop where
  | exec_Lgetstack
      (s : List stackframe) (f : function) (sp : val) (sl : slot) (ofs : Z)
      (ty : typ) (dst : mreg) (b : code) (rs : locset) (m : mem) (rs' : locset)
      (hrs : rs' = Locmap.set (R dst) (rs (S sl ofs ty))
        (CompCert4Lean.Backend.LTL.undef_regs
          (CompCert4Lean.Backend.LTL.destroyed_by_getstack sl) rs)) :
      step cfg xi ge (State s f sp (Lgetstack sl ofs ty dst :: b) rs m) E0
        (State s f sp b rs' m)
  | exec_Lsetstack
      (s : List stackframe) (f : function) (sp : val) (src : mreg) (sl : slot)
      (ofs : Z) (ty : typ) (b : code) (rs : locset) (m : mem) (rs' : locset)
      (hrs : rs' = Locmap.set (S sl ofs ty) (rs (R src))
        (CompCert4Lean.Backend.LTL.undef_regs (destroyed_by_setstack ty) rs)) :
      step cfg xi ge (State s f sp (Lsetstack src sl ofs ty :: b) rs m) E0
        (State s f sp b rs' m)
  | exec_Lop
      (s : List stackframe) (f : function) (sp : val) (op : operation)
      (args : List mreg) (res : mreg) (b : code) (rs : locset) (m : mem)
      (v : val) (rs' : locset)
      (heval : eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge sp op (CompCert4Lean.Backend.LTL.reglist rs args) m = some v)
      (hrs : rs' = Locmap.set (R res) v
        (CompCert4Lean.Backend.LTL.undef_regs (destroyed_by_op op) rs)) :
      step cfg xi ge (State s f sp (Lop op args res :: b) rs m) E0
        (State s f sp b rs' m)
  | exec_Lload
      (s : List stackframe) (f : function) (sp : val) (chunk : memory_chunk)
      (addr : addressing) (args : List mreg) (dst : mreg) (b : code)
      (rs : locset) (m : mem) (a v : val) (rs' : locset)
      (haddr : eval_addressing ge sp addr
        (CompCert4Lean.Backend.LTL.reglist rs args) = some a)
      (hload : Mem.loadv chunk m a = some v)
      (hrs : rs' = Locmap.set (R dst) v
        (CompCert4Lean.Backend.LTL.undef_regs
          (destroyed_by_load chunk addr) rs)) :
      step cfg xi ge (State s f sp (Lload chunk addr args dst :: b) rs m) E0
        (State s f sp b rs' m)
  | exec_Lstore
      (s : List stackframe) (f : function) (sp : val) (chunk : memory_chunk)
      (addr : addressing) (args : List mreg) (src : mreg) (b : code)
      (rs : locset) (m m' : mem) (a : val) (rs' : locset)
      (haddr : eval_addressing ge sp addr
        (CompCert4Lean.Backend.LTL.reglist rs args) = some a)
      (hstore : Mem.storev chunk m a (rs (R src)) = some m')
      (hrs : rs' = CompCert4Lean.Backend.LTL.undef_regs
        (destroyed_by_store chunk addr) rs) :
      step cfg xi ge (State s f sp (Lstore chunk addr args src :: b) rs m) E0
        (State s f sp b rs' m')
  | exec_Lcall
      (s : List stackframe) (f : function) (sp : val) (sig : signature)
      (ros : Sum mreg ident) (b : code) (rs : locset) (m : mem) (f' : fundef)
      (hfind : find_function ge ros rs = some f')
      (hsig : sig = funsig f') :
      step cfg xi ge (State s f sp (Lcall sig ros :: b) rs m) E0
        (Callstate (Stackframe f sp rs b :: s) f' rs m)
  | exec_Ltailcall
      (s : List stackframe) (f : function) (stk : block) (sig : signature)
      (ros : Sum mreg ident) (b : code) (rs : locset) (m : mem) (rs' : locset)
      (f' : fundef) (m' : mem)
      (hrs : rs' = CompCert4Lean.Backend.LTL.return_regs cfg
        (parent_locset s) rs)
      (hfind : find_function ge ros rs' = some f')
      (hsig : sig = funsig f')
      (hfree : Mem.free m stk z0 f.fn_stacksize = some m') :
      step cfg xi ge
        (State s f (Vptr stk Ptrofs.zero) (Ltailcall sig ros :: b) rs m) E0
        (Callstate s f' rs' m')
  | exec_Lbuiltin
      (s : List stackframe) (f : function) (sp : val) (rs : locset) (m : mem)
      (ef : external_function) (args : List (builtin_arg loc))
      (res : builtin_res mreg) (b : code)
      (vargs : List val) (t : trace) (vres : val) (rs' : locset) (m' : mem)
      (hargs : eval_builtin_args (Genv.to_senv ge) rs sp m args vargs)
      (hcall : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs m t vres m')
      (hrs : rs' = Locmap.setres res vres
        (CompCert4Lean.Backend.LTL.undef_regs (destroyed_by_builtin ef) rs)) :
      step cfg xi ge (State s f sp (Lbuiltin ef args res :: b) rs m) t
        (State s f sp b rs' m')
  | exec_Llabel
      (s : List stackframe) (f : function) (sp : val) (lbl : label) (b : code)
      (rs : locset) (m : mem) :
      step cfg xi ge (State s f sp (Llabel lbl :: b) rs m) E0
        (State s f sp b rs m)
  | exec_Lgoto
      (s : List stackframe) (f : function) (sp : val) (lbl : label) (b : code)
      (rs : locset) (m : mem) (b' : code)
      (hfind : find_label lbl f.fn_code = some b') :
      step cfg xi ge (State s f sp (Lgoto lbl :: b) rs m) E0
        (State s f sp b' rs m)
  | exec_Lcond_true
      (s : List stackframe) (f : function) (sp : val) (cond : condition)
      (args : List mreg) (lbl : label) (b : code) (rs : locset) (m : mem)
      (rs' : locset) (b' : code)
      (heval : eval_condition cond
        (CompCert4Lean.Backend.LTL.reglist rs args) m = some true)
      (hrs : rs' = CompCert4Lean.Backend.LTL.undef_regs
        (destroyed_by_cond cond) rs)
      (hfind : find_label lbl f.fn_code = some b') :
      step cfg xi ge (State s f sp (Lcond cond args lbl :: b) rs m) E0
        (State s f sp b' rs' m)
  | exec_Lcond_false
      (s : List stackframe) (f : function) (sp : val) (cond : condition)
      (args : List mreg) (lbl : label) (b : code) (rs : locset) (m : mem)
      (rs' : locset)
      (heval : eval_condition cond
        (CompCert4Lean.Backend.LTL.reglist rs args) m = some false)
      (hrs : rs' = CompCert4Lean.Backend.LTL.undef_regs
        (destroyed_by_cond cond) rs) :
      step cfg xi ge (State s f sp (Lcond cond args lbl :: b) rs m) E0
        (State s f sp b rs' m)
  | exec_Ljumptable
      (s : List stackframe) (f : function) (sp : val) (arg : mreg)
      (tbl : List label) (b : code) (rs : locset) (m : mem) (n : int)
      (lbl : label) (b' : code) (rs' : locset)
      (harg : rs (R arg) = Vint n)
      (hnth : list_nth_z tbl (Int.unsigned n) = some lbl)
      (hfind : find_label lbl f.fn_code = some b')
      (hrs : rs' = CompCert4Lean.Backend.LTL.undef_regs
        destroyed_by_jumptable rs) :
      step cfg xi ge (State s f sp (Ljumptable arg tbl :: b) rs m) E0
        (State s f sp b' rs' m)
  | exec_Lreturn
      (s : List stackframe) (f : function) (stk : block) (b : code)
      (rs : locset) (m m' : mem)
      (hfree : Mem.free m stk z0 f.fn_stacksize = some m') :
      step cfg xi ge (State s f (Vptr stk Ptrofs.zero) (Lreturn :: b) rs m) E0
        (Returnstate s (CompCert4Lean.Backend.LTL.return_regs cfg
          (parent_locset s) rs) m')
  | exec_function_internal
      (s : List stackframe) (f : function) (rs : locset) (m : mem)
      (rs' : locset) (m' : mem) (stk : block)
      (halloc : Mem.alloc m z0 f.fn_stacksize = (m', stk))
      (hrs : rs' = CompCert4Lean.Backend.LTL.undef_regs
        destroyed_at_function_entry (CompCert4Lean.Backend.LTL.call_regs rs)) :
      step cfg xi ge (Callstate s (Internal f) rs m) E0
        (State s f (Vptr stk Ptrofs.zero) f.fn_code rs' m')
  | exec_function_external
      (s : List stackframe) (ef : external_function) (args : List val)
      (res : val) (rs1 rs2 : locset) (m : mem) (t : trace) (m' : mem)
      (hargs : args = (locArguments cfg (ef_sig ef)).map
        (fun p => Locmap.getpair p rs1))
      (hcall : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) args m t res m')
      (hrs : rs2 = Locmap.setpair (locResult (ef_sig ef)) res
        (CompCert4Lean.Backend.LTL.undef_caller_save_regs cfg rs1)) :
      step cfg xi ge (Callstate s (External ef) rs1 m) t
        (Returnstate s rs2 m')
  | exec_return
      (s : List stackframe) (f : function) (sp : val) (rs0 : locset) (c : code)
      (rs : locset) (m : mem) :
      step cfg xi ge (Returnstate (Stackframe f sp rs0 c :: s) rs m) E0
        (State s f sp c rs m)

export step
  (exec_Lload exec_Lstore exec_Lbuiltin exec_Lgoto exec_Lcond_true
    exec_Lcond_false exec_Ljumptable exec_function_internal
    exec_function_external)

inductive initial_state (p : program) : state → Prop where
  | initial_state_intro (b : block) (f : fundef) (m0 : mem)
      (hmem : Genv.init_mem p = some m0)
      (hsymb : Genv.find_symbol (Genv.globalenv p) p.prog_main = some b)
      (hfun : Genv.find_funct_ptr (Genv.globalenv p) b = some f)
      (hsig : funsig f = signature_main) :
      initial_state p (Callstate [] f (Locmap.init Vundef) m0)

export initial_state (initial_state_intro)

inductive final_state : state → int → Prop where
  | final_state_intro (rs : locset) (m : mem) (retcode : int)
      (hresult : Locmap.getpair (map_rpair R (locResult signature_main)) rs =
        Vint retcode) :
      final_state (Returnstate [] rs m) retcode

def semantics
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompilerConfig) (xi : ExternalCalls) (p : program) :
    CompCert4Lean.Common.Smallstep.semantics :=
  Semantics
    (step (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg xi)
    (initial_state p) final_state (Genv.globalenv p)

end CompCert4Lean.Backend.Linear
