import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Cminor
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Values
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Switch
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Floats

/-!
# Csharpminor abstract syntax and semantics

Definition-bearing translation of CompCert's `cfrontend/Csharpminor.v`.
The external-call environment is explicit, following the integrated Events
API.
-/

namespace CompCert4Lean.Cfrontend.Csharpminor

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Switch
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev z0 : Z := .Z0
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

/-! ## Abstract syntax -/

inductive constant : Type where
  | Ointconst (n : CCInt)
  | Ofloatconst (n : CCFloat)
  | Osingleconst (n : CCFloat32)
  | Olongconst (n : CCInt64)

export constant (Ointconst Ofloatconst Osingleconst Olongconst)

def unary_operation : Type := CompCert4Lean.Backend.Cminor.unary_operation

def binary_operation : Type := CompCert4Lean.Backend.Cminor.binary_operation

inductive expr : Type where
  | Evar (id : ident)
  | Eaddrof (id : ident)
  | Econst (constant : constant)
  | Eunop (operation : unary_operation) (argument : expr)
  | Ebinop (operation : binary_operation) (left right : expr)
  | Eload (chunk : memory_chunk) (address : expr)

export expr (Evar Eaddrof Econst Eunop Ebinop Eload)

def label := ident

mutual
  inductive stmt : Type where
    | Sskip
    | Sset (id : ident) (value : expr)
    | Sstore (chunk : memory_chunk) (address value : expr)
    | Scall (result : Option ident) (sig : signature) (callee : expr)
        (args : List expr)
    | Sbuiltin (result : Option ident) (ef : external_function) (args : List expr)
    | Sseq (first second : stmt)
    | Sifthenelse (condition : expr) (ifso ifnot : stmt)
    | Sloop (body : stmt)
    | Sblock (body : stmt)
    | Sexit (depth : Nat)
    | Sswitch (isLong : Bool) (argument : expr) (cases : lbl_stmt)
    | Sreturn (value : Option expr)
    | Slabel (label : label) (body : stmt)
    | Sgoto (label : label)

  inductive lbl_stmt : Type where
    | LSnil
    | LScons (caseValue : Option Z) (statement : stmt) (remaining : lbl_stmt)
end

export stmt (Sskip Sset Sstore Scall Sbuiltin Sseq Sifthenelse Sloop Sblock
  Sexit Sswitch Sreturn Slabel Sgoto)
export lbl_stmt (LSnil LScons)

structure function : Type where
  fn_sig : signature
  fn_params : List ident
  fn_vars : List (ident × Z)
  fn_temps : List ident
  fn_body : stmt

export function (fn_sig fn_params fn_vars fn_temps fn_body)

def fundef := CompCert4Lean.Common.AST.fundef function

def program := CompCert4Lean.Common.AST.program fundef Unit

def funsig : fundef → signature
  | .Internal f => f.fn_sig
  | .External ef => ef_sig ef

/-! ## Operational semantics -/

def genv := Genv.t fundef Unit

def env := PTree.t (block × Z)

def temp_env := PTree.t val

def empty_env : env := PTree.empty (block × Z)

def create_undef_temps : List ident → temp_env
  | [] => PTree.empty val
  | id :: temps => PTree.set id Vundef (create_undef_temps temps)

def bind_parameters : List ident → List val → temp_env → Option temp_env
  | [], [], le => some le
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | id :: formals, v :: args, le =>
      bind_parameters formals args (PTree.set id v le)

inductive cont : Type where
  | Kstop
  | Kseq (statement : stmt) (continuation : cont)
  | Kblock (continuation : cont)
  | Kcall (result : Option ident) (caller : function) (locals : env)
      (temporaries : temp_env) (continuation : cont)

export cont (Kstop Kseq Kblock Kcall)

inductive state : Type where
  | State (currentFunction : function) (statement : stmt) (continuation : cont)
      (locals : env) (temporaries : temp_env) (memory : mem)
  | Callstate (callee : fundef) (args : List val) (continuation : cont)
      (memory : mem)
  | Returnstate (result : val) (continuation : cont) (memory : mem)

export state (State Callstate Returnstate)

def call_cont : cont → cont
  | .Kseq _ k => call_cont k
  | .Kblock k => call_cont k
  | k => k

def is_call_cont : cont → Prop
  | .Kstop => True
  | .Kcall _ _ _ _ _ => True
  | _ => False

def select_switch_default : lbl_stmt → lbl_stmt
  | .LSnil => .LSnil
  | sl@(.LScons none _ _) => sl
  | .LScons (some _) _ remaining => select_switch_default remaining

def select_switch_case (n : Z) : lbl_stmt → Option lbl_stmt
  | .LSnil => none
  | .LScons none _ remaining => select_switch_case n remaining
  | sl@(.LScons (some c) _ remaining) =>
      match zeq c n with
      | .left _ => some sl
      | .right _ => select_switch_case n remaining

def select_switch (n : Z) (sl : lbl_stmt) : lbl_stmt :=
  match select_switch_case n sl with
  | some selected => selected
  | none => select_switch_default sl

def seq_of_lbl_stmt : lbl_stmt → stmt
  | .LSnil => .Sskip
  | .LScons _ s remaining => .Sseq s (seq_of_lbl_stmt remaining)

mutual
  def find_label (lbl : label) : stmt → cont → Option (stmt × cont)
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
    | .Sswitch _ _ cases, k => find_label_ls lbl cases k
    | .Slabel lbl' s, k =>
        match ident_eq lbl lbl' with
        | .left _ => some (s, k)
        | .right _ => find_label lbl s k
    | _, _ => none

  def find_label_ls (lbl : label) :
      lbl_stmt → cont → Option (stmt × cont)
    | .LSnil, _ => none
    | .LScons _ s remaining, k =>
        match find_label lbl s (.Kseq (seq_of_lbl_stmt remaining) k) with
        | some sk => some sk
        | none => find_label_ls lbl remaining k
end

def eval_constant : constant → Option val
  | .Ointconst n => some (.Vint n)
  | .Ofloatconst n => some (.Vfloat n)
  | .Osingleconst n => some (.Vsingle n)
  | .Olongconst n => some (.Vlong n)

def eval_unop
    [binary64_certificate :
      BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
        (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
        (ZArith.BinInt.Z.of_nat 128)] :
    unary_operation → val → Option val :=
  CompCert4Lean.Backend.Cminor.eval_unop
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)

def eval_binop := CompCert4Lean.Backend.Cminor.eval_binop

inductive alloc_variables : env → mem → List (ident × Z) → env → mem → Prop where
  | alloc_variables_nil (e : env) (m : mem) :
      alloc_variables e m [] e m
  | alloc_variables_cons (e : env) (m : mem) (id : ident) (size : Z)
      (vars : List (ident × Z)) (m1 : mem) (b1 : block) (m2 : mem) (e2 : env)
      (halloc : Mem.alloc m z0 size = (m1, b1))
      (hvars : alloc_variables (PTree.set id (b1, size) e) m1 vars e2 m2) :
      alloc_variables e m ((id, size) :: vars) e2 m2

export alloc_variables (alloc_variables_nil alloc_variables_cons)

def block_of_binding (binding : ident × (block × Z)) : block × Z × Z :=
  let (_, b, size) := binding
  (b, z0, size)

def blocks_of_env (e : env) : List (block × Z × Z) :=
  (PTree.elements e).map block_of_binding

inductive eval_var_addr (ge : genv) : env → ident → block → Prop where
  | eval_var_addr_local (e : env) (id : ident) (b : block) (size : Z)
      (hget : PTree.get id e = some (b, size)) :
      eval_var_addr ge e id b
  | eval_var_addr_global (e : env) (id : ident) (b : block)
      (hlocal : PTree.get id e = none)
      (hglobal : Genv.find_symbol ge id = some b) :
      eval_var_addr ge e id b

export eval_var_addr (eval_var_addr_local eval_var_addr_global)

inductive eval_expr
    [binary64_certificate :
      BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
        (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
        (ZArith.BinInt.Z.of_nat 128)]
    (ge : genv) (e : env) (le : temp_env) (m : mem) :
    expr → val → Prop where
  | eval_Evar (id : ident) (v : val)
      (hget : PTree.get id le = some v) :
      eval_expr ge e le m (.Evar id) v
  | eval_Eaddrof (id : ident) (b : block)
      (haddr : eval_var_addr ge e id b) :
      eval_expr ge e le m (.Eaddrof id) (.Vptr b Ptrofs.zero)
  | eval_Econst (cst : constant) (v : val)
      (heval : eval_constant cst = some v) :
      eval_expr ge e le m (.Econst cst) v
  | eval_Eunop (op : unary_operation) (a1 : expr) (v1 v : val)
      (ha1 : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a1 v1)
      (hop : eval_unop
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) op v1 = some v) :
      eval_expr ge e le m (.Eunop op a1) v
  | eval_Ebinop (op : binary_operation) (a1 a2 : expr) (v1 v2 v : val)
      (ha1 : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a1 v1)
      (ha2 : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a2 v2)
      (hop : eval_binop op v1 v2 m = some v) :
      eval_expr ge e le m (.Ebinop op a1 a2) v
  | eval_Eload (chunk : memory_chunk) (address : expr) (vaddr v : val)
      (haddr : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m address vaddr)
      (hload : Mem.loadv chunk m vaddr = some v) :
      eval_expr ge e le m (.Eload chunk address) v

export eval_expr (eval_Evar eval_Eaddrof eval_Econst eval_Eunop eval_Ebinop eval_Eload)

inductive eval_exprlist
    [binary64_certificate :
      BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
        (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
        (ZArith.BinInt.Z.of_nat 128)]
    (ge : genv) (e : env) (le : temp_env) (m : mem) :
    List expr → List val → Prop where
  | eval_Enil : eval_exprlist ge e le m [] []
  | eval_Econs (a1 : expr) (al : List expr) (v1 : val) (vl : List val)
      (ha1 : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a1 v1)
      (hal : eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m al vl) :
      eval_exprlist ge e le m (a1 :: al) (v1 :: vl)

export eval_exprlist (eval_Enil eval_Econs)

inductive step
    [binary64_certificate :
      BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
        (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
        (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) : state → trace → state → Prop where
  | step_skip_seq (f : function) (s : stmt) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge (.State f .Sskip (.Kseq s k) e le m) E0
        (.State f s k e le m)
  | step_skip_block (f : function) (k : cont) (e : env) (le : temp_env)
      (m : mem) :
      step xi ge (.State f .Sskip (.Kblock k) e le m) E0
        (.State f .Sskip k e le m)
  | step_skip_call (f : function) (k : cont) (e : env) (le : temp_env)
      (m m' : mem)
      (hcall : is_call_cont k)
      (hfree : Mem.free_list m (blocks_of_env e) = some m') :
      step xi ge (.State f .Sskip k e le m) E0 (.Returnstate Vundef k m')
  | step_set (f : function) (id : ident) (a : expr) (k : cont) (e : env)
      (le : temp_env) (m : mem) (v : val)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v) :
      step xi ge (.State f (.Sset id a) k e le m) E0
        (.State f .Sskip k e (PTree.set id v le) m)
  | step_store (f : function) (chunk : memory_chunk) (address value : expr)
      (k : cont) (e : env) (le : temp_env) (m : mem) (vaddr v : val)
      (m' : mem)
      (haddr : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m address vaddr)
      (hvalue : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m value v)
      (hstore : Mem.storev chunk m vaddr v = some m') :
      step xi ge (.State f (.Sstore chunk address value) k e le m) E0
        (.State f .Sskip k e le m')
  | step_call (f : function) (optid : Option ident) (sig : signature) (a : expr)
      (args : List expr) (k : cont) (e : env) (le : temp_env) (m : mem)
      (vf : val) (vargs : List val) (fd : fundef)
      (hcallee : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a vf)
      (hargs : eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m args vargs)
      (hfind : Genv.find_funct ge vf = some fd)
      (hsig : funsig fd = sig) :
      step xi ge (.State f (.Scall optid sig a args) k e le m) E0
        (.Callstate fd vargs (.Kcall optid f e le k) m)
  | step_builtin (f : function) (optid : Option ident) (ef : external_function)
      (args : List expr) (k : cont) (e : env) (le : temp_env) (m : mem)
      (vargs : List val) (t : trace) (vres : val) (m' : mem)
      (hargs : eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m args vargs)
      (hext : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs m t vres m') :
      step xi ge (.State f (.Sbuiltin optid ef args) k e le m) t
        (.State f .Sskip k e
          (CompCert4Lean.Backend.Cminor.set_optvar optid vres le) m')
  | step_seq (f : function) (s1 s2 : stmt) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge (.State f (.Sseq s1 s2) k e le m) E0
        (.State f s1 (.Kseq s2 k) e le m)
  | step_ifthenelse (f : function) (a : expr) (s1 s2 : stmt) (k : cont)
      (e : env) (le : temp_env) (m : mem) (v : val) (b : Bool)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v)
      (hbool : Val.bool_of_val v b) :
      step xi ge (.State f (.Sifthenelse a s1 s2) k e le m) E0
        (.State f (if b then s1 else s2) k e le m)
  | step_loop (f : function) (s : stmt) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge (.State f (.Sloop s) k e le m) E0
        (.State f s (.Kseq (.Sloop s) k) e le m)
  | step_block (f : function) (s : stmt) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge (.State f (.Sblock s) k e le m) E0
        (.State f s (.Kblock k) e le m)
  | step_exit_seq (f : function) (n : Nat) (s : stmt) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge (.State f (.Sexit n) (.Kseq s k) e le m) E0
        (.State f (.Sexit n) k e le m)
  | step_exit_block_0 (f : function) (k : cont) (e : env) (le : temp_env)
      (m : mem) :
      step xi ge (.State f (.Sexit 0) (.Kblock k) e le m) E0
        (.State f .Sskip k e le m)
  | step_exit_block_S (f : function) (n : Nat) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge (.State f (.Sexit (n + 1)) (.Kblock k) e le m) E0
        (.State f (.Sexit n) k e le m)
  | step_switch (f : function) (isLong : Bool) (a : expr) (cases : lbl_stmt)
      (k : cont) (e : env) (le : temp_env) (m : mem) (v : val) (n : Z)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v)
      (harg : switch_argument isLong v n) :
      step xi ge (.State f (.Sswitch isLong a cases) k e le m) E0
        (.State f (seq_of_lbl_stmt (select_switch n cases)) k e le m)
  | step_return_0 (f : function) (k : cont) (e : env) (le : temp_env)
      (m m' : mem)
      (hfree : Mem.free_list m (blocks_of_env e) = some m') :
      step xi ge (.State f (.Sreturn none) k e le m) E0
        (.Returnstate Vundef (call_cont k) m')
  | step_return_1 (f : function) (a : expr) (k : cont) (e : env)
      (le : temp_env) (m : mem) (v : val) (m' : mem)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v)
      (hfree : Mem.free_list m (blocks_of_env e) = some m') :
      step xi ge (.State f (.Sreturn (some a)) k e le m) E0
        (.Returnstate v (call_cont k) m')
  | step_label (f : function) (lbl : label) (s : stmt) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge (.State f (.Slabel lbl s) k e le m) E0
        (.State f s k e le m)
  | step_goto (f : function) (lbl : label) (k : cont) (e : env)
      (le : temp_env) (m : mem) (s' : stmt) (k' : cont)
      (hfind : find_label lbl f.fn_body (call_cont k) = some (s', k')) :
      step xi ge (.State f (.Sgoto lbl) k e le m) E0
        (.State f s' k' e le m)
  | step_internal_function (f : function) (vargs : List val) (k : cont)
      (m m1 : mem) (e : env) (le : temp_env)
      (htypes : Val.has_argtype_list vargs f.fn_sig.sig_args)
      (hvars : list_norepet (f.fn_vars.map Prod.fst))
      (hparams : list_norepet f.fn_params)
      (hdisjoint : list_disjoint f.fn_params f.fn_temps)
      (halloc : alloc_variables empty_env m f.fn_vars e m1)
      (hbind : bind_parameters f.fn_params vargs
          (create_undef_temps f.fn_temps) = some le) :
      step xi ge (.Callstate (.Internal f) vargs k m) E0
        (.State f f.fn_body k e le m1)
  | step_external_function (ef : external_function) (vargs : List val)
      (k : cont) (m : mem) (t : trace) (vres : val) (m' : mem)
      (hext : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs m t vres m') :
      step xi ge (.Callstate (.External ef) vargs k m) t
        (.Returnstate vres k m')
  | step_return (v : val) (optid : Option ident) (f : function) (e : env)
      (le : temp_env) (k : cont) (m : mem) :
      step xi ge (.Returnstate v (.Kcall optid f e le k) m) E0
        (.State f .Sskip k e
          (CompCert4Lean.Backend.Cminor.set_optvar optid v le) m)

export step (step_skip_seq step_skip_block step_skip_call step_set step_store
  step_call step_builtin step_seq step_ifthenelse step_loop step_block
  step_exit_seq step_exit_block_0 step_exit_block_S step_switch step_return_0
  step_return_1 step_label step_goto step_internal_function
  step_external_function step_return)

inductive initial_state (p : program) : state → Prop where
  | initial_state_intro (b : block) (f : fundef) (m0 : mem)
      (hmem : Genv.init_mem p = some m0)
      (hsymbol : Genv.find_symbol (Genv.globalenv p) p.prog_main = some b)
      (hfun : Genv.find_funct_ptr (Genv.globalenv p) b = some f)
      (hsig : funsig f = signature_main) :
      initial_state p (.Callstate f [] .Kstop m0)

export initial_state (initial_state_intro)

inductive final_state : state → CCInt → Prop where
  | final_state_intro (r : CCInt) (m : mem) :
      final_state (.Returnstate (.Vint r) .Kstop m) r

export final_state (final_state_intro)

def semantics
    [binary64_certificate :
      BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53)
        (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24)
        (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (p : program) :
    CompCert4Lean.Common.Smallstep.semantics :=
  Semantics
    (step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi)
    (initial_state p)
    final_state
    (Genv.globalenv p)

end CompCert4Lean.Cfrontend.Csharpminor
