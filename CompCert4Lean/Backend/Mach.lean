import CompCert4Lean.Config
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Conventions
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.X86.Machregs
import CompCert4Lean.X86.Op
import CompCert4Lean.X86.Stacklayout

/-!
# Mach intermediate language

Definition-bearing translation of CompCert's `backend/Mach.v`.  The packet
selects the source syntax, the stack/call helpers, and the theorem-facing
transition constructors needed by the current migration layer.  Deferred
source collateral is intentionally not reintroduced here.
-/

namespace CompCert4Lean.Backend.Mach

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Conventions
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
open CompCert4Lean.X86.Stacklayout

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := ZArith.BinInt.Z.of_nat 1
private abbrev z4 : Z := ZArith.BinInt.Z.of_nat 4
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zMul := ZArith.BinInt.Z.mul

private def mregDecEq : DecidableEq mreg := by
  intro x y
  cases x <;> cases y <;>
    first
    | exact isTrue rfl
    | exact isFalse (by intro h; cases h)

private def mregEq (x y : mreg) : Sumbool (x = y) (x ≠ y) :=
  match mregDecEq x y with
  | isTrue h => .left h
  | isFalse h => .right h

/-! ## Abstract syntax -/

def label : Type := positive

inductive instruction : Type where
  | Mgetstack (ofs : Ptrofs) (ty : typ) (dst : mreg)
  | Msetstack (src : mreg) (ofs : Ptrofs) (ty : typ)
  | Mgetparam (ofs : Ptrofs) (ty : typ) (dst : mreg)
  | Mop (op : operation) (args : List mreg) (res : mreg)
  | Mload (chunk : memory_chunk) (addr : addressing) (args : List mreg)
      (dst : mreg)
  | Mstore (chunk : memory_chunk) (addr : addressing) (args : List mreg)
      (src : mreg)
  | Mcall (sig : signature) (ros : Sum mreg ident)
  | Mtailcall (sig : signature) (ros : Sum mreg ident)
  | Mbuiltin (ef : external_function) (args : List (builtin_arg mreg))
      (res : builtin_res mreg)
  | Mlabel (lbl : label)
  | Mgoto (lbl : label)
  | Mcond (cond : condition) (args : List mreg) (lbl : label)
  | Mjumptable (arg : mreg) (tbl : List label)
  | Mreturn

export instruction
  (Mgetstack Msetstack Mgetparam Mop Mload Mstore Mcall Mtailcall Mbuiltin
    Mlabel Mgoto Mcond Mjumptable Mreturn)

def code : Type := List instruction

structure function : Type where
  fn_sig : signature
  fn_code : code
  fn_stacksize : Z
  fn_link_ofs : Ptrofs
  fn_retaddr_ofs : Ptrofs

export function (fn_sig fn_code fn_stacksize fn_link_ofs fn_retaddr_ofs)

def fundef : Type := CompCert4Lean.Common.AST.fundef function
def program : Type := CompCert4Lean.Common.AST.program fundef Unit
def genv : Type := Genv.t fundef Unit

/-! ## Stack and register helpers -/

def load_stack (m : mem) (sp : val) (ty : typ) (ofs : Ptrofs) : Option val :=
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr sp ofs)

def store_stack (m : mem) (sp : val) (ty : typ) (ofs : Ptrofs) (v : val) : Option mem :=
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr sp ofs) v

namespace RegEq

def eq (x y : mreg) : Sumbool (x = y) (x ≠ y) := mregEq x y

end RegEq

/-! The EMap application owned by this module.  Its public surface is kept
source-shaped while the executable carrier is a total register-indexed
function. -/
namespace Regmap

abbrev Regmap (A : Type) : Type := mreg → A
abbrev elt : Type := mreg
def elt_eq (x y : elt) : Sumbool (x = y) (x ≠ y) := RegEq.eq x y
abbrev t (A : Type) : Type := Regmap A

def init {A : Type} (x : A) : t A := fun _ => x
def get {A : Type} (i : elt) (m : t A) : A := m i
def set {A : Type} (i : elt) (x : A) (m : t A) : t A :=
  fun j =>
    match elt_eq j i with
    | .left _ => x
    | .right _ => m j

def map {A B : Type} (f : A → B) (m : t A) : t B := fun i => f (m i)

def gi : Prop := ∀ (A : Type) (i : elt) (x : A), get i (init x) = x
def gss : Prop :=
  ∀ (A : Type) (i : elt) (x : A) (m : t A), get i (set i x m) = x
def gso : Prop :=
  ∀ (A : Type) (i j : elt) (x : A) (m : t A),
    i ≠ j → get i (set j x m) = get i m
def gsspec : Prop :=
  ∀ (A : Type) (i j : elt) (x : A) (m : t A),
    get i (set j x m) =
      match elt_eq i j with
      | .left _ => x
      | .right _ => get i m
def gsident : Prop :=
  ∀ (A : Type) (i j : elt) (m : t A), get j (set i (get i m) m) = get j m
def gmap : Prop :=
  ∀ (A B : Type) (f : A → B) (i : elt) (m : t A),
    get i (map f m) = f (get i m)

end Regmap

def regset : Type := Regmap.t val

def undef_regs : List mreg → regset → regset
  | [], rs => rs
  | r :: rl, rs => Regmap.set r Vundef (undef_regs rl rs)

def undef_regs_otherStatement : Prop :=
  ∀ (r : mreg) (rl : List mreg) (rs : regset),
    r ∉ rl → undef_regs rl rs r = rs r

def undef_regs_sameStatement : Prop :=
  ∀ (r : mreg) (rl : List mreg) (rs : regset),
    r ∈ rl → undef_regs rl rs r = Vundef

def undef_regs_other : Prop := undef_regs_otherStatement

def undef_regs_same : Prop := undef_regs_sameStatement

def undef_caller_save_regs (cfg : CompilerConfig) (rs : regset) : regset :=
  fun r => if CompCert4Lean.X86.Conventions1.is_callee_save cfg r then rs r else Vundef

def set_pair (p : rpair mreg) (v : val) (rs : regset) : regset :=
  match p with
  | .One r => Regmap.set r v rs
  | .Twolong rhi rlo =>
      Regmap.set rlo (Val.loword v) (Regmap.set rhi (Val.hiword v) rs)

def set_res (res : builtin_res mreg) (v : val) (rs : regset) : regset :=
  match res with
  | .BR r => Regmap.set r v rs
  | .BR_none => rs
  | .BR_splitlong hi lo =>
      set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)

/-! ## Labels and calls -/

def is_label (lbl : label) (instr : instruction) : Bool :=
  match instr with
  | .Mlabel lbl' =>
      match peq lbl lbl' with
      | .left _ => true
      | .right _ => false
  | _ => false

def is_label_correctStatement : Prop :=
  ∀ (lbl : label) (instr : instruction),
    if is_label lbl instr then instr = .Mlabel lbl else instr ≠ .Mlabel lbl

def is_label_correct : Prop := is_label_correctStatement

def find_label (lbl : label) (c : code) : Option code :=
  match c with
  | [] => none
  | i1 :: il => if is_label lbl i1 then some il else find_label lbl il

def find_function_ptr (ge : genv) (ros : Sum mreg ident) (rs : regset) : Option block :=
  match ros with
  | .inl r =>
      match rs r with
      | .Vptr b ofs => if Ptrofs.eq ofs Ptrofs.zero then some b else none
      | _ => none
  | .inr symb => Genv.find_symbol ge symb

/-! ## External-call arguments -/

inductive extcall_arg (cfg : CompilerConfig) (rs : regset) (m : mem) (sp : val) :
    loc → val → Prop where
  | extcall_arg_reg (r : mreg) :
      extcall_arg cfg rs m sp (.R r) (rs r)
  | extcall_arg_stack (ofs : Z) (ty : typ) (v : val)
      (hload : load_stack m sp ty
        (Ptrofs.repr (zAdd (fe_ofs_arg cfg) (zMul z4 ofs))) = some v) :
      extcall_arg cfg rs m sp (.S Outgoing ofs ty) v

inductive extcall_arg_pair (cfg : CompilerConfig) (rs : regset) (m : mem) (sp : val) :
    rpair loc → val → Prop where
  | extcall_arg_one (l : loc) (v : val)
      (harg : extcall_arg cfg rs m sp l v) :
      extcall_arg_pair cfg rs m sp (.One l) v
  | extcall_arg_twolong (hi lo : loc) (vhi vlo : val)
      (hhi : extcall_arg cfg rs m sp hi vhi)
      (hlo : extcall_arg cfg rs m sp lo vlo) :
      extcall_arg_pair cfg rs m sp (.Twolong hi lo) (Val.longofwords vhi vlo)

def extcall_arguments (cfg : CompilerConfig) (rs : regset) (m : mem) (sp : val)
    (sg : signature) (args : List val) : Prop :=
  list_forall2 (extcall_arg_pair cfg rs m sp)
    (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg) args

/-! ## Machine states -/

inductive stackframe : Type where
  | Stackframe (f : block) (sp : val) (retaddr : val) (c : code)

export stackframe (Stackframe)

inductive state : Type where
  | State (stack : List stackframe) (f : block) (sp : val) (c : code)
      (rs : regset) (m : mem)
  | Callstate (stack : List stackframe) (f : block) (rs : regset) (m : mem)
  | Returnstate (stack : List stackframe) (rs : regset) (m : mem)

export state (State Callstate Returnstate)

def parent_sp : List stackframe → val
  | [] => Vnullptr
  | .Stackframe _ sp _ _ :: _ => sp

def parent_ra : List stackframe → val
  | [] => Vnullptr
  | .Stackframe _ _ ra _ :: _ => ra

/-! ## Transition semantics -/

inductive step
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompilerConfig) (xi : ExternalCalls)
    (return_address_offset : function → code → Ptrofs → Prop) (ge : genv) :
    state → trace → state → Prop where
  | exec_Mlabel
      (s : List stackframe) (f : block) (sp : val) (lbl : label) (c : code)
      (rs : regset) (m : mem) :
      step cfg xi return_address_offset ge
        (State s f sp (.Mlabel lbl :: c) rs m) E0
        (State s f sp c rs m)
  | exec_Mgetstack
      (s : List stackframe) (f : block) (sp : val) (ofs : Ptrofs) (ty : typ)
      (dst : mreg) (c : code) (rs : regset) (m : mem) (v : val)
      (hload : load_stack m sp ty ofs = some v) :
      step cfg xi return_address_offset ge
        (State s f sp (.Mgetstack ofs ty dst :: c) rs m) E0
        (State s f sp c (Regmap.set dst v rs) m)
  | exec_Msetstack
      (s : List stackframe) (f : block) (sp : val) (src : mreg) (ofs : Ptrofs)
      (ty : typ) (c : code) (rs : regset) (m m' : mem) (rs' : regset)
      (hstore : store_stack m sp ty ofs (rs src) = some m')
      (hrs : rs' = undef_regs (destroyed_by_setstack ty) rs) :
      step cfg xi return_address_offset ge
        (State s f sp (.Msetstack src ofs ty :: c) rs m) E0
        (State s f sp c rs' m')
  | exec_Mgetparam
      (s : List stackframe) (fb : block) (f : function) (sp : val)
      (ofs : Ptrofs) (ty : typ)
      (dst : mreg) (c : code) (rs : regset) (m : mem) (v : val) (rs' : regset)
      (hfun : Genv.find_funct_ptr ge fb = some (.Internal f))
      (hlink : load_stack m sp Tptr f.fn_link_ofs = some (parent_sp s))
      (hload : load_stack m (parent_sp s) ty ofs = some v)
      (hrs : rs' = Regmap.set dst v (Regmap.set temp_for_parent_frame Vundef rs)) :
      step cfg xi return_address_offset ge
        (State s fb sp (.Mgetparam ofs ty dst :: c) rs m) E0
        (State s fb sp c rs' m)
  | exec_Mop
      (s : List stackframe) (f : block) (sp : val) (op : operation)
      (args : List mreg) (res : mreg) (c : code) (rs : regset) (m : mem)
      (v : val) (rs' : regset)
      (heval : eval_operation ge sp op (args.map rs) m = some v)
      (hrs : rs' = Regmap.set res v (undef_regs (destroyed_by_op op) rs)) :
      step cfg xi return_address_offset ge
        (State s f sp (.Mop op args res :: c) rs m) E0
        (State s f sp c rs' m)
  | exec_Mload
      (s : List stackframe) (f : block) (sp : val) (chunk : memory_chunk)
      (addr : addressing) (args : List mreg) (dst : mreg) (c : code)
      (rs : regset) (m : mem) (a v : val) (rs' : regset)
      (haddr : eval_addressing ge sp addr (args.map rs) = some a)
      (hload : Mem.loadv chunk m a = some v)
      (hrs : rs' = Regmap.set dst v
        (undef_regs (destroyed_by_load chunk addr) rs)) :
      step cfg xi return_address_offset ge
        (State s f sp (.Mload chunk addr args dst :: c) rs m) E0
        (State s f sp c rs' m)
  | exec_Mstore
      (s : List stackframe) (f : block) (sp : val) (chunk : memory_chunk)
      (addr : addressing) (args : List mreg) (src : mreg) (c : code)
      (rs : regset) (m m' : mem) (a : val) (rs' : regset)
      (haddr : eval_addressing ge sp addr (args.map rs) = some a)
      (hstore : Mem.storev chunk m a (rs src) = some m')
      (hrs : rs' = undef_regs (destroyed_by_store chunk addr) rs) :
      step cfg xi return_address_offset ge
        (State s f sp (.Mstore chunk addr args src :: c) rs m) E0
        (State s f sp c rs' m')
  | exec_Mcall
      (s : List stackframe) (fb : block) (sp : val) (sig : signature)
      (ros : Sum mreg ident) (c : code) (rs : regset) (m : mem)
      (f : function) (f' : block) (ra : Ptrofs)
      (hfind : find_function_ptr ge ros rs = some f')
      (hfun : Genv.find_funct_ptr ge fb = some (.Internal f))
      (hra : return_address_offset f c ra) :
      step cfg xi return_address_offset ge
        (State s fb sp (.Mcall sig ros :: c) rs m) E0
        (Callstate (.Stackframe fb sp (.Vptr fb ra) c :: s) f' rs m)
  | exec_Mtailcall
      (s : List stackframe) (fb stk : block) (soff : Ptrofs) (sig : signature)
      (ros : Sum mreg ident) (c : code) (rs : regset) (m : mem)
      (f : function) (f' : block) (m' : mem)
      (hfind : find_function_ptr ge ros rs = some f')
      (hfun : Genv.find_funct_ptr ge fb = some (.Internal f))
      (hlink : load_stack m (.Vptr stk soff) Tptr f.fn_link_ofs =
        some (parent_sp s))
      (hretaddr : load_stack m (.Vptr stk soff) Tptr f.fn_retaddr_ofs =
        some (parent_ra s))
      (hfree : Mem.free m stk z0 f.fn_stacksize = some m') :
      step cfg xi return_address_offset ge
        (State s fb (.Vptr stk soff) (.Mtailcall sig ros :: c) rs m) E0
        (Callstate s f' rs m')
  | exec_Mbuiltin
      (s : List stackframe) (f : block) (sp : val) (rs : regset) (m : mem)
      (ef : external_function) (args : List (builtin_arg mreg))
      (res : builtin_res mreg) (b : code) (vargs : List val) (t : trace)
      (vres : val) (rs' : regset) (m' : mem)
      (hargs : eval_builtin_args (Genv.to_senv ge) rs sp m args vargs)
      (hcall : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs m t vres m')
      (hrs : rs' = set_res res vres
        (undef_regs (destroyed_by_builtin ef) rs)) :
      step cfg xi return_address_offset ge
        (State s f sp (.Mbuiltin ef args res :: b) rs m) t
        (State s f sp b rs' m')
  | exec_Mgoto
      (s : List stackframe) (fb : block) (f : function) (sp : val)
      (lbl : label) (c : code)
      (rs : regset) (m : mem) (c' : code)
      (hfun : Genv.find_funct_ptr ge fb = some (.Internal f))
      (hfind : find_label lbl f.fn_code = some c') :
      step cfg xi return_address_offset ge
        (State s fb sp (.Mgoto lbl :: c) rs m) E0
        (State s fb sp c' rs m)
  | exec_Mcond_true
      (s : List stackframe) (fb : block) (f : function) (sp : val)
      (cond : condition)
      (args : List mreg) (lbl : label) (c : code) (rs : regset) (m : mem)
      (c' : code) (rs' : regset)
      (heval : eval_condition cond (args.map rs) m = some true)
      (hfun : Genv.find_funct_ptr ge fb = some (.Internal f))
      (hfind : find_label lbl f.fn_code = some c')
      (hrs : rs' = undef_regs (destroyed_by_cond cond) rs) :
      step cfg xi return_address_offset ge
        (State s fb sp (.Mcond cond args lbl :: c) rs m) E0
        (State s fb sp c' rs' m)
  | exec_Mcond_false
      (s : List stackframe) (f : block) (sp : val) (cond : condition)
      (args : List mreg) (lbl : label) (c : code) (rs : regset) (m : mem)
      (rs' : regset)
      (heval : eval_condition cond (args.map rs) m = some false)
      (hrs : rs' = undef_regs (destroyed_by_cond cond) rs) :
      step cfg xi return_address_offset ge
        (State s f sp (.Mcond cond args lbl :: c) rs m) E0
        (State s f sp c rs' m)
  | exec_Mjumptable
      (s : List stackframe) (fb : block) (f : function) (sp : val) (arg : mreg)
      (tbl : List label) (c : code) (rs : regset) (m : mem) (n : int)
      (lbl : label) (c' : code) (rs' : regset)
      (harg : rs arg = .Vint n)
      (hnth : list_nth_z tbl (Int.unsigned n) = some lbl)
      (hfun : Genv.find_funct_ptr ge fb = some (.Internal f))
      (hfind : find_label lbl f.fn_code = some c')
      (hrs : rs' = undef_regs destroyed_by_jumptable rs) :
      step cfg xi return_address_offset ge
        (State s fb sp (.Mjumptable arg tbl :: c) rs m) E0
        (State s fb sp c' rs' m)
  | exec_Mreturn
      (s : List stackframe) (fb stk : block) (soff : Ptrofs) (c : code)
      (rs : regset) (m : mem) (f : function) (m' : mem)
      (hfun : Genv.find_funct_ptr ge fb = some (.Internal f))
      (hlink : load_stack m (.Vptr stk soff) Tptr f.fn_link_ofs =
        some (parent_sp s))
      (hretaddr : load_stack m (.Vptr stk soff) Tptr f.fn_retaddr_ofs =
        some (parent_ra s))
      (hfree : Mem.free m stk z0 f.fn_stacksize = some m') :
      step cfg xi return_address_offset ge
        (State s fb (.Vptr stk soff) (.Mreturn :: c) rs m) E0
        (Returnstate s rs m')
  | exec_function_internal
      (s : List stackframe) (fb : block) (rs : regset) (m : mem)
      (f : function) (m1 m2 m3 : mem) (stk : block) (rs' : regset)
      (hfun : Genv.find_funct_ptr ge fb = some (.Internal f))
      (halloc : Mem.alloc m z0 f.fn_stacksize = (m1, stk))
      (hlink : store_stack m1 (.Vptr stk Ptrofs.zero) Tptr f.fn_link_ofs
        (parent_sp s) = some m2)
      (hretaddr : store_stack m2 (.Vptr stk Ptrofs.zero) Tptr f.fn_retaddr_ofs
        (parent_ra s) = some m3)
      (hrs : rs' = undef_regs destroyed_at_function_entry rs) :
      step cfg xi return_address_offset ge (Callstate s fb rs m) E0
        (State s fb (.Vptr stk Ptrofs.zero) f.fn_code rs' m3)
  | exec_function_external
      (s : List stackframe) (fb : block) (rs : regset) (m : mem)
      (t : trace) (rs' : regset) (ef : external_function) (args : List val)
      (res : val) (m' : mem)
      (hfun : Genv.find_funct_ptr ge fb = some (.External ef))
      (hargs : extcall_arguments cfg rs m (parent_sp s) (ef_sig ef) args)
      (hcall : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) args m t res m')
      (hrs : rs' = set_pair (CompCert4Lean.X86.Conventions1.loc_result (ef_sig ef))
        res (undef_caller_save_regs cfg rs)) :
      step cfg xi return_address_offset ge (Callstate s fb rs m) t
        (Returnstate s rs' m')
  | exec_return
      (s : List stackframe) (f : block) (sp : val) (ra : val) (c : code)
      (rs : regset) (m : mem) :
      step cfg xi return_address_offset ge
        (Returnstate (.Stackframe f sp ra c :: s) rs m) E0
        (State s f sp c rs m)

export step
  (exec_Mlabel exec_Mgetstack exec_Msetstack exec_Mgetparam exec_Mop exec_Mload
    exec_Mstore exec_Mcall exec_Mtailcall exec_Mbuiltin exec_Mgoto exec_Mcond_true
    exec_Mcond_false exec_Mjumptable exec_Mreturn exec_function_internal
    exec_function_external exec_return)

/-! ## Whole-program predicates -/

inductive initial_state (p : program) : state → Prop where
  | initial_state_intro (fb : block) (m0 : mem)
      (hmem : Genv.init_mem p = some m0)
      (hsymb : Genv.find_symbol (Genv.globalenv p) p.prog_main = some fb) :
      initial_state p (Callstate [] fb (Regmap.init Vundef) m0)

export initial_state (initial_state_intro)

inductive final_state : state → int → Prop where
  | final_state_intro (rs : regset) (m : mem) (r : mreg) (retcode : int)
      (hresult : CompCert4Lean.X86.Conventions1.loc_result signature_main = .One r)
      (hval : rs r = Vint retcode) :
      final_state (Returnstate [] rs m) retcode

def semantics
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompilerConfig) (xi : ExternalCalls)
    (return_address_offset : function → code → Ptrofs → Prop) (p : program) :
    CompCert4Lean.Common.Smallstep.semantics :=
  Semantics
    (step (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg xi return_address_offset)
    (initial_state p)
    final_state
    (Genv.globalenv p)

end CompCert4Lean.Backend.Mach
