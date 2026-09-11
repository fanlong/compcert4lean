import CompCert4Lean.Foundation.Numbers
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
# Cminor abstract syntax and semantics

Definition-bearing translation of CompCert's `backend/Cminor.v`.  The
external-call environment is explicit, following the integrated Events API.
The proof assigned to later migration is represented by its exact proposition
descriptor.
-/

namespace CompCert4Lean.Backend.Cminor

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Switch
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev z0 : Z := Z0
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

/-! ## Abstract syntax -/

inductive constant : Type where
  | Ointconst (n : CCInt)
  | Ofloatconst (n : CCFloat)
  | Osingleconst (n : CCFloat32)
  | Olongconst (n : CCInt64)
  | Oaddrsymbol (symbol : ident) (offset : Ptrofs)
  | Oaddrstack (offset : Ptrofs)

export constant (Ointconst Ofloatconst Osingleconst Olongconst Oaddrsymbol
  Oaddrstack)

inductive unary_operation : Type where
  | Ocast8unsigned
  | Ocast8signed
  | Ocast16unsigned
  | Ocast16signed
  | Onegint
  | Onotint
  | Onegf
  | Oabsf
  | Onegfs
  | Oabsfs
  | Osingleoffloat
  | Ofloatofsingle
  | Ointoffloat
  | Ointuoffloat
  | Ofloatofint
  | Ofloatofintu
  | Ointofsingle
  | Ointuofsingle
  | Osingleofint
  | Osingleofintu
  | Onegl
  | Onotl
  | Ointoflong
  | Olongofint
  | Olongofintu
  | Olongoffloat
  | Olonguoffloat
  | Ofloatoflong
  | Ofloatoflongu
  | Olongofsingle
  | Olonguofsingle
  | Osingleoflong
  | Osingleoflongu

export unary_operation (Ocast8unsigned Ocast8signed Ocast16unsigned
  Ocast16signed Onegint Onotint Onegf Oabsf Onegfs Oabsfs Osingleoffloat
  Ofloatofsingle Ointoffloat Ointuoffloat Ofloatofint Ofloatofintu
  Ointofsingle Ointuofsingle Osingleofint Osingleofintu Onegl Onotl
  Ointoflong Olongofint Olongofintu Olongoffloat Olonguoffloat
  Ofloatoflong Ofloatoflongu Olongofsingle Olonguofsingle Osingleoflong
  Osingleoflongu)

inductive binary_operation : Type where
  | Oadd
  | Osub
  | Omul
  | Odiv
  | Odivu
  | Omod
  | Omodu
  | Oand
  | Oor
  | Oxor
  | Oshl
  | Oshr
  | Oshru
  | Oaddf
  | Osubf
  | Omulf
  | Odivf
  | Oaddfs
  | Osubfs
  | Omulfs
  | Odivfs
  | Oaddl
  | Osubl
  | Omull
  | Odivl
  | Odivlu
  | Omodl
  | Omodlu
  | Oandl
  | Oorl
  | Oxorl
  | Oshll
  | Oshrl
  | Oshrlu
  | Ocmp (comparison : CompCert4Lean.Lib.Integers.comparison)
  | Ocmpu (comparison : CompCert4Lean.Lib.Integers.comparison)
  | Ocmpf (comparison : CompCert4Lean.Lib.Integers.comparison)
  | Ocmpfs (comparison : CompCert4Lean.Lib.Integers.comparison)
  | Ocmpl (comparison : CompCert4Lean.Lib.Integers.comparison)
  | Ocmplu (comparison : CompCert4Lean.Lib.Integers.comparison)

export binary_operation (Oadd Osub Omul Odiv Odivu Omod Omodu Oand Oor Oxor
  Oshl Oshr Oshru Oaddf Osubf Omulf Odivf Oaddfs Osubfs Omulfs Odivfs Oaddl
  Osubl Omull Odivl Odivlu Omodl Omodlu Oandl Oorl Oxorl Oshll Oshrl Oshrlu
  Ocmp Ocmpu Ocmpf Ocmpfs Ocmpl Ocmplu)

inductive expr : Type where
  | Evar (id : ident)
  | Econst (constant : constant)
  | Eunop (operation : unary_operation) (argument : expr)
  | Ebinop (operation : binary_operation) (left right : expr)
  | Eload (chunk : memory_chunk) (address : expr)

export expr (Evar Econst Eunop Ebinop Eload)

def label := ident

inductive stmt : Type where
  | Sskip
  | Sassign (id : ident) (value : expr)
  | Sstore (chunk : memory_chunk) (address value : expr)
  | Scall (result : Option ident) (sig : signature) (callee : expr)
      (args : List expr)
  | Stailcall (sig : signature) (callee : expr) (args : List expr)
  | Sbuiltin (result : Option ident) (ef : external_function) (args : List expr)
  | Sseq (first second : stmt)
  | Sifthenelse (condition : expr) (ifso ifnot : stmt)
  | Sloop (body : stmt)
  | Sblock (body : stmt)
  | Sexit (depth : Nat)
  | Sswitch (isLong : Bool) (argument : expr) (cases : List (Z × Nat))
      (default : Nat)
  | Sreturn (value : Option expr)
  | Slabel (label : label) (body : stmt)
  | Sgoto (label : label)

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

def env := PTree.t val

def set_params : List val → List ident → env
  | v :: values, id :: ids => PTree.set id v (set_params values ids)
  | [], id :: ids => PTree.set id Vundef (set_params [] ids)
  | _, _ => PTree.empty val

def set_locals : List ident → env → env
  | [], e => e
  | id :: ids, e => PTree.set id Vundef (set_locals ids e)

def set_optvar (id : Option ident) (v : val) (e : env) : env :=
  match id with
  | none => e
  | some id => PTree.set id v e

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
  | Returnstate (result : val) (continuation : cont) (memory : mem)

export state (State Callstate Returnstate)

def eval_constant (ge : genv) (sp : val) : constant → Option val
  | .Ointconst n => some (Vint n)
  | .Ofloatconst n => some (Vfloat n)
  | .Osingleconst n => some (Vsingle n)
  | .Olongconst n => some (Vlong n)
  | .Oaddrsymbol symbol offset => some (Genv.symbol_address ge symbol offset)
  | .Oaddrstack offset => some (Val.offset_ptr sp offset)

def eval_unop
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    unary_operation → val → Option val
  | .Ocast8unsigned, arg => some (Val.zero_ext (zOfNat 8) arg)
  | .Ocast8signed, arg => some (Val.sign_ext (zOfNat 8) arg)
  | .Ocast16unsigned, arg => some (Val.zero_ext (zOfNat 16) arg)
  | .Ocast16signed, arg => some (Val.sign_ext (zOfNat 16) arg)
  | .Onegint, arg => some (Val.negint arg)
  | .Onotint, arg => some (Val.notint arg)
  | .Onegf, arg => some (Val.negf arg)
  | .Oabsf, arg => some (Val.absf arg)
  | .Onegfs, arg => some (Val.negfs arg)
  | .Oabsfs, arg => some (Val.absfs arg)
  | .Osingleoffloat, arg => some (Val.singleoffloat arg)
  | .Ofloatofsingle, arg => some (Val.floatofsingle arg)
  | .Ointoffloat, arg => Val.intoffloat arg
  | .Ointuoffloat, arg => Val.intuoffloat arg
  | .Ofloatofint, arg =>
      Val.floatofint (binary64_certificate := binary64_certificate) arg
  | .Ofloatofintu, arg =>
      Val.floatofintu (binary64_certificate := binary64_certificate) arg
  | .Ointofsingle, arg => Val.intofsingle arg
  | .Ointuofsingle, arg => Val.intuofsingle arg
  | .Osingleofint, arg =>
      Val.singleofint (binary32_certificate := binary32_certificate) arg
  | .Osingleofintu, arg =>
      Val.singleofintu (binary32_certificate := binary32_certificate) arg
  | .Onegl, arg => some (Val.negl arg)
  | .Onotl, arg => some (Val.notl arg)
  | .Ointoflong, arg => some (Val.loword arg)
  | .Olongofint, arg => some (Val.longofint arg)
  | .Olongofintu, arg => some (Val.longofintu arg)
  | .Olongoffloat, arg => Val.longoffloat arg
  | .Olonguoffloat, arg => Val.longuoffloat arg
  | .Ofloatoflong, arg =>
      Val.floatoflong (binary64_certificate := binary64_certificate) arg
  | .Ofloatoflongu, arg =>
      Val.floatoflongu (binary64_certificate := binary64_certificate) arg
  | .Olongofsingle, arg => Val.longofsingle arg
  | .Olonguofsingle, arg => Val.longuofsingle arg
  | .Osingleoflong, arg =>
      Val.singleoflong (binary32_certificate := binary32_certificate) arg
  | .Osingleoflongu, arg =>
      Val.singleoflongu (binary32_certificate := binary32_certificate) arg

def eval_binop (op : binary_operation) (arg1 arg2 : val) (m : mem) : Option val :=
  match op with
  | .Oadd => some (Val.add arg1 arg2)
  | .Osub => some (Val.sub arg1 arg2)
  | .Omul => some (Val.mul arg1 arg2)
  | .Odiv => Val.divs arg1 arg2
  | .Odivu => Val.divu arg1 arg2
  | .Omod => Val.mods arg1 arg2
  | .Omodu => Val.modu arg1 arg2
  | .Oand => some (Val.and arg1 arg2)
  | .Oor => some (Val.or arg1 arg2)
  | .Oxor => some (Val.xor arg1 arg2)
  | .Oshl => some (Val.shl arg1 arg2)
  | .Oshr => some (Val.shr arg1 arg2)
  | .Oshru => some (Val.shru arg1 arg2)
  | .Oaddf => some (Val.addf arg1 arg2)
  | .Osubf => some (Val.subf arg1 arg2)
  | .Omulf => some (Val.mulf arg1 arg2)
  | .Odivf => some (Val.divf arg1 arg2)
  | .Oaddfs => some (Val.addfs arg1 arg2)
  | .Osubfs => some (Val.subfs arg1 arg2)
  | .Omulfs => some (Val.mulfs arg1 arg2)
  | .Odivfs => some (Val.divfs arg1 arg2)
  | .Oaddl => some (Val.addl arg1 arg2)
  | .Osubl => some (Val.subl arg1 arg2)
  | .Omull => some (Val.mull arg1 arg2)
  | .Odivl => Val.divls arg1 arg2
  | .Odivlu => Val.divlu arg1 arg2
  | .Omodl => Val.modls arg1 arg2
  | .Omodlu => Val.modlu arg1 arg2
  | .Oandl => some (Val.andl arg1 arg2)
  | .Oorl => some (Val.orl arg1 arg2)
  | .Oxorl => some (Val.xorl arg1 arg2)
  | .Oshll => some (Val.shll arg1 arg2)
  | .Oshrl => some (Val.shrl arg1 arg2)
  | .Oshrlu => some (Val.shrlu arg1 arg2)
  | .Ocmp cmp => some (Val.cmp cmp arg1 arg2)
  | .Ocmpu cmp => some (Val.cmpu (Mem.valid_pointer m) cmp arg1 arg2)
  | .Ocmpf cmp => some (Val.cmpf cmp arg1 arg2)
  | .Ocmpfs cmp => some (Val.cmpfs cmp arg1 arg2)
  | .Ocmpl cmp => Val.cmpl cmp arg1 arg2
  | .Ocmplu cmp => Val.cmplu (Mem.valid_pointer m) cmp arg1 arg2

inductive eval_expr
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (ge : genv) (sp : val) (e : env) (m : mem) :
    expr → val → Prop where
  | eval_Evar (id : ident) (v : val)
      (hget : PTree.get id e = some v) :
      eval_expr ge sp e m (.Evar id) v
  | eval_Econst (cst : constant) (v : val)
      (heval : eval_constant ge sp cst = some v) :
      eval_expr ge sp e m (.Econst cst) v
  | eval_Eunop (op : unary_operation) (a1 : expr) (v1 v : val)
      (ha1 : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m a1 v1)
      (hop : eval_unop
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) op v1 = some v) :
      eval_expr ge sp e m (.Eunop op a1) v
  | eval_Ebinop (op : binary_operation) (a1 a2 : expr) (v1 v2 v : val)
      (ha1 : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m a1 v1)
      (ha2 : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m a2 v2)
      (hop : eval_binop op v1 v2 m = some v) :
      eval_expr ge sp e m (.Ebinop op a1 a2) v
  | eval_Eload (chunk : memory_chunk) (address : expr) (vaddr v : val)
      (haddr : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m address vaddr)
      (hload : Mem.loadv chunk m vaddr = some v) :
      eval_expr ge sp e m (.Eload chunk address) v

inductive eval_exprlist
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (ge : genv) (sp : val) (e : env) (m : mem) :
    List expr → List val → Prop where
  | eval_Enil : eval_exprlist ge sp e m [] []
  | eval_Econs (a1 : expr) (al : List expr) (v1 : val) (vl : List val)
      (ha1 : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m a1 v1)
      (hal : eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m al vl) :
      eval_exprlist ge sp e m (a1 :: al) (v1 :: vl)

def call_cont : cont → cont
  | .Kseq _ k => call_cont k
  | .Kblock k => call_cont k
  | k => k

def is_call_cont : cont → Prop
  | .Kstop => True
  | .Kcall _ _ _ _ _ => True
  | _ => False

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
  | .Slabel lbl' s, k =>
      match ident_eq lbl lbl' with
      | .left _ => some (s, k)
      | .right _ => find_label lbl s k
  | _, _ => none

inductive step
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) : state → trace → state → Prop where
  | step_skip_seq (f : function) (s : stmt) (k : cont) (sp : val) (e : env)
      (m : mem) :
      step xi ge (.State f .Sskip (.Kseq s k) sp e m) E0 (.State f s k sp e m)
  | step_skip_block (f : function) (k : cont) (sp : val) (e : env) (m : mem) :
      step xi ge (.State f .Sskip (.Kblock k) sp e m) E0 (.State f .Sskip k sp e m)
  | step_skip_call (f : function) (k : cont) (sp : block) (e : env) (m m' : mem)
      (hcall : is_call_cont k)
      (hfree : Mem.free m sp z0 f.fn_stackspace = some m') :
      step xi ge (.State f .Sskip k (.Vptr sp Ptrofs.zero) e m) E0
        (.Returnstate Vundef k m')
  | step_assign (f : function) (id : ident) (a : expr) (k : cont) (sp : val)
      (e : env) (m : mem) (v : val)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m a v) :
      step xi ge (.State f (.Sassign id a) k sp e m) E0
        (.State f .Sskip k sp (PTree.set id v e) m)
  | step_store (f : function) (chunk : memory_chunk) (address value : expr)
      (k : cont) (sp : val) (e : env) (m : mem) (vaddr v : val) (m' : mem)
      (haddr : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m address vaddr)
      (hvalue : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m value v)
      (hstore : Mem.storev chunk m vaddr v = some m') :
      step xi ge (.State f (.Sstore chunk address value) k sp e m) E0
        (.State f .Sskip k sp e m')
  | step_call (f : function) (optid : Option ident) (sig : signature) (a : expr)
      (args : List expr) (k : cont) (sp : val) (e : env) (m : mem) (vf : val)
      (vargs : List val) (fd : fundef)
      (hcallee : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m a vf)
      (hargs : eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m args vargs)
      (hfind : Genv.find_funct ge vf = some fd)
      (hsig : funsig fd = sig) :
      step xi ge (.State f (.Scall optid sig a args) k sp e m) E0
        (.Callstate fd vargs (.Kcall optid f sp e k) m)
  | step_tailcall (f : function) (sig : signature) (a : expr) (args : List expr)
      (k : cont) (sp : block) (e : env) (m : mem) (vf : val) (vargs : List val)
      (fd : fundef) (m' : mem)
      (hcallee : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge (.Vptr sp Ptrofs.zero) e m a vf)
      (hargs : eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge (.Vptr sp Ptrofs.zero) e m args vargs)
      (hfind : Genv.find_funct ge vf = some fd)
      (hsig : funsig fd = sig)
      (hfree : Mem.free m sp z0 f.fn_stackspace = some m') :
      step xi ge (.State f (.Stailcall sig a args) k (.Vptr sp Ptrofs.zero) e m) E0
        (.Callstate fd vargs (call_cont k) m')
  | step_builtin (f : function) (optid : Option ident) (ef : external_function)
      (args : List expr) (k : cont) (sp : val) (e : env) (m : mem)
      (vargs : List val) (t : trace) (vres : val) (m' : mem)
      (hargs : eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m args vargs)
      (hext : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs m t vres m') :
      step xi ge (.State f (.Sbuiltin optid ef args) k sp e m) t
        (.State f .Sskip k sp (set_optvar optid vres e) m')
  | step_seq (f : function) (s1 s2 : stmt) (k : cont) (sp : val) (e : env)
      (m : mem) :
      step xi ge (.State f (.Sseq s1 s2) k sp e m) E0
        (.State f s1 (.Kseq s2 k) sp e m)
  | step_ifthenelse (f : function) (a : expr) (s1 s2 : stmt) (k : cont)
      (sp : val) (e : env) (m : mem) (v : val) (b : Bool)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m a v)
      (hbool : Val.bool_of_val v b) :
      step xi ge (.State f (.Sifthenelse a s1 s2) k sp e m) E0
        (.State f (if b then s1 else s2) k sp e m)
  | step_loop (f : function) (s : stmt) (k : cont) (sp : val) (e : env)
      (m : mem) :
      step xi ge (.State f (.Sloop s) k sp e m) E0
        (.State f s (.Kseq (.Sloop s) k) sp e m)
  | step_block (f : function) (s : stmt) (k : cont) (sp : val) (e : env)
      (m : mem) :
      step xi ge (.State f (.Sblock s) k sp e m) E0
        (.State f s (.Kblock k) sp e m)
  | step_exit_seq (f : function) (n : Nat) (s : stmt) (k : cont) (sp : val)
      (e : env) (m : mem) :
      step xi ge (.State f (.Sexit n) (.Kseq s k) sp e m) E0
        (.State f (.Sexit n) k sp e m)
  | step_exit_block_0 (f : function) (k : cont) (sp : val) (e : env) (m : mem) :
      step xi ge (.State f (.Sexit 0) (.Kblock k) sp e m) E0
        (.State f .Sskip k sp e m)
  | step_exit_block_S (f : function) (n : Nat) (k : cont) (sp : val) (e : env)
      (m : mem) :
      step xi ge (.State f (.Sexit (n + 1)) (.Kblock k) sp e m) E0
        (.State f (.Sexit n) k sp e m)
  | step_switch (f : function) (isLong : Bool) (a : expr) (cases : List (Z × Nat))
      (default : Nat) (k : cont) (sp : val) (e : env) (m : mem) (v : val)
      (n : Z) (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp e m a v)
      (harg : switch_argument isLong v n) :
      step xi ge (.State f (.Sswitch isLong a cases default) k sp e m) E0
        (.State f (.Sexit (switch_target n default cases)) k sp e m)
  | step_return_0 (f : function) (k : cont) (sp : block) (e : env) (m m' : mem)
      (hfree : Mem.free m sp z0 f.fn_stackspace = some m') :
      step xi ge (.State f (.Sreturn none) k (.Vptr sp Ptrofs.zero) e m) E0
        (.Returnstate Vundef (call_cont k) m')
  | step_return_1 (f : function) (a : expr) (k : cont) (sp : block) (e : env)
      (m : mem) (v : val) (m' : mem)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge (.Vptr sp Ptrofs.zero) e m a v)
      (hfree : Mem.free m sp z0 f.fn_stackspace = some m') :
      step xi ge (.State f (.Sreturn (some a)) k (.Vptr sp Ptrofs.zero) e m) E0
        (.Returnstate v (call_cont k) m')
  | step_label (f : function) (lbl : label) (s : stmt) (k : cont) (sp : val)
      (e : env) (m : mem) :
      step xi ge (.State f (.Slabel lbl s) k sp e m) E0 (.State f s k sp e m)
  | step_goto (f : function) (lbl : label) (k : cont) (sp : val) (e : env)
      (m : mem) (s' : stmt) (k' : cont)
      (hfind : find_label lbl f.fn_body (call_cont k) = some (s', k')) :
      step xi ge (.State f (.Sgoto lbl) k sp e m) E0 (.State f s' k' sp e m)
  | step_internal_function (f : function) (vargs : List val) (k : cont) (m m' : mem)
      (sp : block) (e : env)
      (htypes : Val.has_argtype_list vargs f.fn_sig.sig_args)
      (halloc : Mem.alloc m z0 f.fn_stackspace = (m', sp))
      (henv : set_locals f.fn_vars (set_params vargs f.fn_params) = e) :
      step xi ge (.Callstate (.Internal f) vargs k m) E0
        (.State f f.fn_body k (.Vptr sp Ptrofs.zero) e m')
  | step_external_function (ef : external_function) (vargs : List val) (k : cont)
      (m : mem) (t : trace) (vres : val) (m' : mem)
      (hext : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs m t vres m') :
      step xi ge (.Callstate (.External ef) vargs k m) t (.Returnstate vres k m')
  | step_return (v : val) (optid : Option ident) (f : function) (sp : val)
      (e : env) (k : cont) (m : mem) :
      step xi ge (.Returnstate v (.Kcall optid f sp e k) m) E0
        (.State f .Sskip k sp (set_optvar optid v e) m)

export step (step_skip_call step_call step_ifthenelse step_return_0 step_return_1
  step_goto)

inductive initial_state (p : program) : state → Prop where
  | initial_state_intro (b : block) (f : fundef) (m0 : mem)
      (hmem : Genv.init_mem p = some m0)
      (hsymbol : Genv.find_symbol (Genv.globalenv p) p.prog_main = some b)
      (hfun : Genv.find_funct_ptr (Genv.globalenv p) b = some f)
      (hsig : funsig f = signature_main) :
      initial_state p (.Callstate f [] .Kstop m0)

inductive final_state : state → CCInt → Prop where
  | final_state_intro (r : CCInt) (m : mem) :
      final_state (.Returnstate (.Vint r) .Kstop m) r

def semantics
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (p : program) :
    CompCert4Lean.Common.Smallstep.semantics :=
  Semantics
    (step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi)
    (initial_state p)
    final_state
    (Genv.globalenv p)

def eval_expr_determStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (e : env) (m : mem) (a : expr) (v : val),
    eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge sp e m a v →
      ∀ v', eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge sp e m a v' → v' = v

end CompCert4Lean.Backend.Cminor

namespace CompCert4Lean.Backend.Cminor

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eval_expr_determ
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    eval_expr_determStatement := by
  intro ge sp e m a v h
  induction h with
  | eval_Evar id v hget =>
      intro v' h'
      cases h' with
      | eval_Evar id' v' hget' =>
          exact Option.some.inj (hget'.symm.trans hget)
  | eval_Econst cst v heval =>
      intro v' h'
      cases h' with
      | eval_Econst cst' v' heval' =>
          exact Option.some.inj (heval'.symm.trans heval)
  | eval_Eunop op a1 v1 v ha1 hop ih1 =>
      intro v' h'
      cases h' with
      | eval_Eunop op' a1' v1' v' ha1' hop' =>
          have hv1 : v1' = v1 := ih1 v1' ha1'
          subst v1'
          exact Option.some.inj (hop'.symm.trans hop)
  | eval_Ebinop op a1 a2 v1 v2 v ha1 ha2 hop ih1 ih2 =>
      intro v' h'
      cases h' with
      | eval_Ebinop op' a1' a2' v1' v2' v' ha1' ha2' hop' =>
          have hv1 : v1' = v1 := ih1 v1' ha1'
          have hv2 : v2' = v2 := ih2 v2' ha2'
          subst v1'
          subst v2'
          exact Option.some.inj (hop'.symm.trans hop)
  | eval_Eload chunk address vaddr v haddr hload ihaddr =>
      intro v' h'
      cases h' with
      | eval_Eload chunk' address' vaddr' v' haddr' hload' =>
          have hvaddr : vaddr' = vaddr := ihaddr vaddr' haddr'
          subst vaddr'
          exact Option.some.inj (hload'.symm.trans hload)

end CompCert4Lean.Backend.Cminor
