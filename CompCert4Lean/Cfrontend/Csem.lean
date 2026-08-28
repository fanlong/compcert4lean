import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Cfrontend.Csyntax

/-!
# Dynamic semantics for CompCert C

Definition-bearing translation of CompCert's `cfrontend/Csem.v`.  External
calls are carried by the explicit provider already used by the Events layer.
-/

namespace CompCert4Lean.Cfrontend.Csem

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.Mem.mem
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev trace := CompCert4Lean.Common.Events.trace
private abbrev fundef := CompCert4Lean.Cfrontend.Csyntax.fundef
private abbrev function := CompCert4Lean.Cfrontend.Csyntax.function
private abbrev program := CompCert4Lean.Cfrontend.Csyntax.program
private abbrev expr := CompCert4Lean.Cfrontend.Csyntax.expr
private abbrev exprlist := CompCert4Lean.Cfrontend.Csyntax.exprlist
private abbrev statement := CompCert4Lean.Cfrontend.Csyntax.statement
private abbrev labeled_statements := CompCert4Lean.Cfrontend.Csyntax.labeled_statements
private abbrev label := CompCert4Lean.Cfrontend.Csyntax.label
private abbrev type := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev composite_env := CompCert4Lean.Cfrontend.Ctypes.composite_env
private abbrev ExternalCalls := CompCert4Lean.Common.ExternalCalls.ExternalCalls
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

private abbrev z0 : Z := .Z0
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zDivide := ZArith.BinInt.Z.divide

/-! ## Environments -/

structure genv : Type where
  genv_genv : Genv.t fundef type
  genv_cenv : composite_env

export genv (genv_genv genv_cenv)

def globalenv (p : program) : genv :=
  { genv_genv := Genv.globalenv (program_of_program p)
    genv_cenv := p.prog_comp_env }

def env := PTree.t (block × type)

def empty_env : env := PTree.empty (block × type)

private def symbolEnv (ge : genv) : Senv.t :=
  Genv.to_senv ge.genv_genv

/-! ## Locations and local storage -/

inductive deref_loc (ge : genv) (ty : type) (m : mem) (b : block) (ofs : ptrofs) :
    bitfield → trace → val → Prop where
  | value {chunk v} :
      access_mode ty = .By_value chunk →
      type_is_volatile ty = false →
      Mem.loadv chunk m (.Vptr b ofs) = some v →
      deref_loc ge ty m b ofs .Full E0 v
  | volatile {chunk t v} :
      access_mode ty = .By_value chunk →
      type_is_volatile ty = true →
      volatile_load (symbolEnv ge) chunk m b ofs t v →
      deref_loc ge ty m b ofs .Full t v
  | reference :
      access_mode ty = .By_reference →
      deref_loc ge ty m b ofs .Full E0 (.Vptr b ofs)
  | copy :
      access_mode ty = .By_copy →
      deref_loc ge ty m b ofs .Full E0 (.Vptr b ofs)
  | bitfield {sz sg pos width v} :
      load_bitfield ty sz sg pos width m (.Vptr b ofs) v →
      deref_loc ge ty m b ofs (.Bits sz sg pos width) E0 v

inductive assign_loc (ge : genv) (ty : type) (m : mem) (b : block) (ofs : ptrofs) :
    bitfield → val → trace → mem → val → Prop where
  | value {v chunk m'} :
      access_mode ty = .By_value chunk →
      type_is_volatile ty = false →
      Mem.storev chunk m (.Vptr b ofs) v = some m' →
      assign_loc ge ty m b ofs .Full v E0 m' v
  | volatile {v chunk t m'} :
      access_mode ty = .By_value chunk →
      type_is_volatile ty = true →
      volatile_store (symbolEnv ge) chunk m b ofs v t m' →
      assign_loc ge ty m b ofs .Full v t m' v
  | copy {b' ofs' bytes m'} :
      access_mode ty = .By_copy →
      zDivide (alignof_blockcopy ge.genv_cenv ty) (Ptrofs.unsigned ofs') →
      zDivide (alignof_blockcopy ge.genv_cenv ty) (Ptrofs.unsigned ofs) →
      (b' ≠ b ∨
        Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs ∨
        zLe (zAdd (Ptrofs.unsigned ofs') (sizeof ge.genv_cenv ty)) (Ptrofs.unsigned ofs) ∨
        zLe (zAdd (Ptrofs.unsigned ofs) (sizeof ge.genv_cenv ty)) (Ptrofs.unsigned ofs')) →
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ge.genv_cenv ty) = some bytes →
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = some m' →
      assign_loc ge ty m b ofs .Full (.Vptr b' ofs') E0 m' (.Vptr b' ofs')
  | bitfield {sz sg pos width v m' v'} :
      store_bitfield ty sz sg pos width m (.Vptr b ofs) v m' v' →
      assign_loc ge ty m b ofs (.Bits sz sg pos width) v E0 m' v'

inductive alloc_variables (ge : genv) : env → mem → List (ident × type) → env → mem → Prop where
  | nil (e : env) (m : mem) : alloc_variables ge e m [] e m
  | cons {e m id ty vars m1 b1 m2 e2} :
      Mem.alloc m z0 (sizeof ge.genv_cenv ty) = (m1, b1) →
      alloc_variables ge (PTree.set id (b1, ty) e) m1 vars e2 m2 →
      alloc_variables ge e m ((id, ty) :: vars) e2 m2

inductive bind_parameters (ge : genv) (e : env) :
    mem → List (ident × type) → List val → mem → Prop where
  | nil (m : mem) : bind_parameters ge e m [] [] m
  | cons {m id ty params v1 vl v1' b m1 m2} :
      PTree.get id e = some (b, ty) →
      assign_loc ge ty m b Ptrofs.zero .Full v1 E0 m1 v1' →
      bind_parameters ge e m1 params vl m2 →
      bind_parameters ge e m ((id, ty) :: params) (v1 :: vl) m2

def block_of_binding (ge : genv) (id_b_ty : ident × (block × type)) : block × Z × Z :=
  let (_, (b, ty)) := id_b_ty
  (b, z0, sizeof ge.genv_cenv ty)

def blocks_of_env (ge : genv) (e : env) : List (block × Z × Z) :=
  (PTree.elements e).map (block_of_binding ge)

/-! ## Switches and argument casts -/

def select_switch_default : labeled_statements → labeled_statements
  | sl@(.LSnil) => sl
  | sl@(.LScons none _ _) => sl
  | .LScons (some _) _ rest => select_switch_default rest

def select_switch_case (n : Z) : labeled_statements → Option labeled_statements
  | .LSnil => none
  | .LScons none _ rest => select_switch_case n rest
  | sl@(.LScons (some c) _ rest) =>
      match zeq c n with
      | .left _ => some sl
      | .right _ => select_switch_case n rest

def select_switch (n : Z) (sl : labeled_statements) : labeled_statements :=
  match select_switch_case n sl with
  | some sl' => sl'
  | none => select_switch_default sl

def seq_of_labeled_statement : labeled_statements → statement
  | .LSnil => .Sskip
  | .LScons _ s rest => .Ssequence s (seq_of_labeled_statement rest)

inductive cast_arguments
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (m : mem) : exprlist → List type → List val → Prop where
  | nil : cast_arguments m .Enil [] []
  | cons {v ty el targ1 targs v1 vl} :
      sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v ty targ1 m = some v1 →
      cast_arguments
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) m el targs vl →
      cast_arguments m (.Econs (.Eval v ty) el) (targ1 :: targs) (v1 :: vl)

/-! ## Head reductions -/

inductive lred (ge : genv) (e : env) : expr → mem → expr → mem → Prop where
  | varLocal {x ty m b} :
      PTree.get x e = some (b, ty) →
      lred ge e (.Evar x ty) m (.Eloc b Ptrofs.zero .Full ty) m
  | varGlobal {x ty m b} :
      PTree.get x e = none →
      Genv.find_symbol ge.genv_genv x = some b →
      lred ge e (.Evar x ty) m (.Eloc b Ptrofs.zero .Full ty) m
  | deref {b ofs ty1 ty m} :
      lred ge e (.Ederef (.Eval (.Vptr b ofs) ty1) ty) m (.Eloc b ofs .Full ty) m
  | fieldStruct {b ofs id co a f ty m delta bf} :
      PTree.get id ge.genv_cenv = some co →
      field_offset ge.genv_cenv f co.co_members = .OK (delta, bf) →
      lred ge e (.Efield (.Eval (.Vptr b ofs) (.Tstruct id a)) f ty) m
        (.Eloc b (Ptrofs.add ofs (Ptrofs.repr delta)) bf ty) m
  | fieldUnion {b ofs id co a f ty m delta bf} :
      PTree.get id ge.genv_cenv = some co →
      union_field_offset ge.genv_cenv f co.co_members = .OK (delta, bf) →
      lred ge e (.Efield (.Eval (.Vptr b ofs) (.Tunion id a)) f ty) m
        (.Eloc b (Ptrofs.add ofs (Ptrofs.repr delta)) bf ty) m

inductive rred
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (e : env) :
    expr → mem → trace → expr → mem → Prop where
  | rvalof {b ofs bf ty m t v} :
      deref_loc ge ty m b ofs bf t v →
      rred xi ge e (.Evalof (.Eloc b ofs bf ty) ty) m t (.Eval v ty) m
  | addrof {b ofs ty1 ty m} :
      rred xi ge e (.Eaddrof (.Eloc b ofs .Full ty1) ty) m E0 (.Eval (.Vptr b ofs) ty) m
  | unop {op v1 ty1 ty m v} :
      sem_unary_operation
          (binary64_certificate := binary64_certificate) op v1 ty1 m = some v →
      rred xi ge e (.Eunop op (.Eval v1 ty1) ty) m E0 (.Eval v ty) m
  | binop {op v1 ty1 v2 ty2 ty m v} :
      sem_binary_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge.genv_cenv op v1 ty1 v2 ty2 m = some v →
      rred xi ge e (.Ebinop op (.Eval v1 ty1) (.Eval v2 ty2) ty) m E0 (.Eval v ty) m
  | cast {ty v1 ty1 m v} :
      sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v1 ty1 ty m = some v →
      rred xi ge e (.Ecast (.Eval v1 ty1) ty) m E0 (.Eval v ty) m
  | red_seqand_true {v1 ty1 r2 ty m} :
      bool_val v1 ty1 m = some true →
      rred xi ge e (.Eseqand (.Eval v1 ty1) r2 ty) m E0 (.Eparen r2 type_bool ty) m
  | red_seqand_false {v1 ty1 r2 ty m} :
      bool_val v1 ty1 m = some false →
      rred xi ge e (.Eseqand (.Eval v1 ty1) r2 ty) m E0 (.Eval (.Vint Int.zero) ty) m
  | red_seqor_true {v1 ty1 r2 ty m} :
      bool_val v1 ty1 m = some true →
      rred xi ge e (.Eseqor (.Eval v1 ty1) r2 ty) m E0 (.Eval (.Vint Int.one) ty) m
  | red_seqor_false {v1 ty1 r2 ty m} :
      bool_val v1 ty1 m = some false →
      rred xi ge e (.Eseqor (.Eval v1 ty1) r2 ty) m E0 (.Eparen r2 type_bool ty) m
  | condition {v1 ty1 r1 r2 ty b m} :
      bool_val v1 ty1 m = some b →
      rred xi ge e (.Econdition (.Eval v1 ty1) r1 r2 ty) m E0
        (.Eparen (if b then r1 else r2) ty ty) m
  | sizeof {ty1 ty m} :
      rred xi ge e (.Esizeof ty1 ty) m E0
        (.Eval (CompCert4Lean.Common.Values.Vptrofs
          (Ptrofs.repr (Ctypes.sizeof ge.genv_cenv ty1))) ty) m
  | alignof {ty1 ty m} :
      rred xi ge e (.Ealignof ty1 ty) m E0
        (.Eval (CompCert4Lean.Common.Values.Vptrofs
          (Ptrofs.repr (Ctypes.alignof ge.genv_cenv ty1))) ty) m
  | assign {b ofs ty1 bf v2 ty2 m v t m' v'} :
      sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v2 ty2 ty1 m = some v →
      assign_loc ge ty1 m b ofs bf v t m' v' →
      rred xi ge e (.Eassign (.Eloc b ofs bf ty1) (.Eval v2 ty2) ty1) m
        t (.Eval v' ty1) m'
  | assignop {op b ofs ty1 bf v2 ty2 tyres m t v1} :
      deref_loc ge ty1 m b ofs bf t v1 →
      rred xi ge e (.Eassignop op (.Eloc b ofs bf ty1) (.Eval v2 ty2) tyres ty1) m t
        (.Eassign (.Eloc b ofs bf ty1)
          (.Ebinop op (.Eval v1 ty1) (.Eval v2 ty2) tyres) ty1) m
  | postincr {id b ofs ty bf m t v1 op} :
      deref_loc ge ty m b ofs bf t v1 →
      op = (match id with | .Incr => .Oadd | .Decr => .Osub) →
      rred xi ge e (.Epostincr id (.Eloc b ofs bf ty) ty) m t
        (.Ecomma
          (.Eassign (.Eloc b ofs bf ty)
            (.Ebinop op (.Eval v1 ty) (.Eval (.Vint Int.one) type_int32s)
              (incrdecr_type ty)) ty)
          (.Eval v1 ty) ty) m
  | comma {v ty1 r2 ty m} :
      typeof r2 = ty →
      rred xi ge e (.Ecomma (.Eval v ty1) r2 ty) m E0 r2 m
  | paren {v1 ty1 ty2 ty m v} :
      sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v1 ty1 ty2 m = some v →
      rred xi ge e (.Eparen (.Eval v1 ty1) ty2 ty) m E0 (.Eval v ty) m
  | builtin {ef tyargs el ty m vargs t vres m'} :
      cast_arguments
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) m el tyargs vargs →
      external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ef (symbolEnv ge) vargs m t vres m' →
      rred xi ge e (.Ebuiltin ef tyargs el ty) m t (.Eval vres ty) m'

export rred (red_seqand_true red_seqand_false red_seqor_true red_seqor_false)

inductive callred
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ge : genv) : expr → mem → fundef → List val → type → Prop where
  | call {vf tyf m tyargs tyres cconv el ty fd vargs} :
      Genv.find_funct ge.genv_genv vf = some fd →
      cast_arguments
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) m el tyargs vargs →
      type_of_fundef fd = .Tfunction tyargs tyres cconv →
      Cop.classify_fun tyf = .fun_case_f tyargs tyres cconv →
      callred ge (.Ecall (.Eval vf tyf) el ty) m fd vargs ty

/-! ## Reduction contexts and immediate safety -/

inductive kind : Type where
  | LV
  | RV

export kind (LV RV)

mutual
  inductive context : kind → kind → (expr → expr) → Prop where
    | ctx_top (k : kind) : context k k (fun x => x)
    | deref {k C ty} : context k .RV C → context k .LV (fun x => .Ederef (C x) ty)
    | field {k C f ty} : context k .RV C → context k .LV (fun x => .Efield (C x) f ty)
    | rvalof {k C ty} : context k .LV C → context k .RV (fun x => .Evalof (C x) ty)
    | addrof {k C ty} : context k .LV C → context k .RV (fun x => .Eaddrof (C x) ty)
    | unop {k C op ty} : context k .RV C → context k .RV (fun x => .Eunop op (C x) ty)
    | binopLeft {k C op e2 ty} :
        context k .RV C → context k .RV (fun x => .Ebinop op (C x) e2 ty)
    | binopRight {k C op e1 ty} :
        context k .RV C → context k .RV (fun x => .Ebinop op e1 (C x) ty)
    | cast {k C ty} : context k .RV C → context k .RV (fun x => .Ecast (C x) ty)
    | seqand {k C r2 ty} :
        context k .RV C → context k .RV (fun x => .Eseqand (C x) r2 ty)
    | seqor {k C r2 ty} :
        context k .RV C → context k .RV (fun x => .Eseqor (C x) r2 ty)
    | condition {k C r2 r3 ty} :
        context k .RV C → context k .RV (fun x => .Econdition (C x) r2 r3 ty)
    | assignLeft {k C e2 ty} :
        context k .LV C → context k .RV (fun x => .Eassign (C x) e2 ty)
    | assignRight {k C e1 ty} :
        context k .RV C → context k .RV (fun x => .Eassign e1 (C x) ty)
    | assignopLeft {k C op e2 tyres ty} :
        context k .LV C → context k .RV (fun x => .Eassignop op (C x) e2 tyres ty)
    | assignopRight {k C op e1 tyres ty} :
        context k .RV C → context k .RV (fun x => .Eassignop op e1 (C x) tyres ty)
    | postincr {k C id ty} :
        context k .LV C → context k .RV (fun x => .Epostincr id (C x) ty)
    | callLeft {k C el ty} :
        context k .RV C → context k .RV (fun x => .Ecall (C x) el ty)
    | callRight {k C e1 ty} :
        contextlist k C → context k .RV (fun x => .Ecall e1 (C x) ty)
    | builtin {k C ef tyargs ty} :
        contextlist k C → context k .RV (fun x => .Ebuiltin ef tyargs (C x) ty)
    | comma {k C e2 ty} :
        context k .RV C → context k .RV (fun x => .Ecomma (C x) e2 ty)
    | paren {k C tycast ty} :
        context k .RV C → context k .RV (fun x => .Eparen (C x) tycast ty)

  inductive contextlist : kind → (expr → exprlist) → Prop where
    | ctx_list_head {k C el} :
        context k .RV C → contextlist k (fun x => .Econs (C x) el)
    | ctx_list_tail {k C e1} :
        contextlist k C → contextlist k (fun x => .Econs e1 (C x))
end

export context (ctx_top)
export contextlist (ctx_list_head ctx_list_tail)

inductive imm_safe
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (e : env) :
    kind → expr → mem → Prop where
  | value (v : val) (ty : type) (m : mem) : imm_safe xi ge e .RV (.Eval v ty) m
  | location (b : block) (ofs : ptrofs) (bf : bitfield) (ty : type) (m : mem) :
      imm_safe xi ge e .LV (.Eloc b ofs bf ty) m
  | localRed {to C a m a' m'} :
      lred ge e a m a' m' →
      context .LV to C →
      imm_safe xi ge e to (C a) m
  | rvalRed {to C a m t a' m'} :
      rred
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge e a m t a' m' →
      context .RV to C →
      imm_safe xi ge e to (C a) m
  | callRed {to C a m fd args ty} :
      callred
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge a m fd args ty →
      context .RV to C →
      imm_safe xi ge e to (C a) m

/-! ## Continuations and states -/

inductive cont : Type where
  | Kstop
  | Kdo (k : cont)
  | Kseq (s : statement) (k : cont)
  | Kifthenelse (s1 s2 : statement) (k : cont)
  | Kwhile1 (x : expr) (s : statement) (k : cont)
  | Kwhile2 (x : expr) (s : statement) (k : cont)
  | Kdowhile1 (x : expr) (s : statement) (k : cont)
  | Kdowhile2 (x : expr) (s : statement) (k : cont)
  | Kfor2 (e2 : expr) (e3 s : statement) (k : cont)
  | Kfor3 (e2 : expr) (e3 s : statement) (k : cont)
  | Kfor4 (e2 : expr) (e3 s : statement) (k : cont)
  | Kswitch1 (ls : labeled_statements) (k : cont)
  | Kswitch2 (k : cont)
  | Kreturn (k : cont)
  | Kcall (f : function) (e : env) (C : expr → expr) (ty : type) (k : cont)

export cont (Kstop Kdo Kseq Kifthenelse Kwhile1 Kwhile2 Kdowhile1 Kdowhile2
  Kfor2 Kfor3 Kfor4 Kswitch1 Kswitch2 Kreturn Kcall)

def call_cont : cont → cont
  | k@(.Kstop) => k
  | .Kdo k => k
  | .Kseq _ k => call_cont k
  | .Kifthenelse _ _ k => call_cont k
  | .Kwhile1 _ _ k => call_cont k
  | .Kwhile2 _ _ k => call_cont k
  | .Kdowhile1 _ _ k => call_cont k
  | .Kdowhile2 _ _ k => call_cont k
  | .Kfor2 _ _ _ k => call_cont k
  | .Kfor3 _ _ _ k => call_cont k
  | .Kfor4 _ _ _ k => call_cont k
  | .Kswitch1 _ k => call_cont k
  | .Kswitch2 k => call_cont k
  | .Kreturn k => call_cont k
  | k@(.Kcall _ _ _ _ _) => k

def is_call_cont : cont → Prop
  | .Kstop => True
  | .Kcall _ _ _ _ _ => True
  | _ => False

inductive state : Type where
  | State (f : function) (s : statement) (k : cont) (e : env) (m : mem)
  | ExprState (f : function) (r : expr) (k : cont) (e : env) (m : mem)
  | Callstate (fd : fundef) (args : List val) (k : cont) (m : mem)
  | Returnstate (res : val) (k : cont) (m : mem)
  | Stuckstate

export state (State ExprState Callstate Returnstate Stuckstate)

/-! ## Labels -/

mutual
  def find_label (lbl : label) : statement → cont → Option (statement × cont)
    | .Ssequence s1 s2, k =>
        match find_label lbl s1 (.Kseq s2 k) with
        | some sk => some sk
        | none => find_label lbl s2 k
    | .Sifthenelse _ s1 s2, k =>
        match find_label lbl s1 k with
        | some sk => some sk
        | none => find_label lbl s2 k
    | .Swhile a s1, k => find_label lbl s1 (.Kwhile2 a s1 k)
    | .Sdowhile a s1, k => find_label lbl s1 (.Kdowhile1 a s1 k)
    | .Sfor a1 a2 a3 s1, k =>
        match find_label lbl a1 (.Kseq (.Sfor .Sskip a2 a3 s1) k) with
        | some sk => some sk
        | none =>
            match find_label lbl s1 (.Kfor3 a2 a3 s1 k) with
            | some sk => some sk
            | none => find_label lbl a3 (.Kfor4 a2 a3 s1 k)
    | .Sswitch _ sl, k => find_label_ls lbl sl (.Kswitch2 k)
    | .Slabel lbl' s', k =>
        match ident_eq lbl lbl' with
        | .left _ => some (s', k)
        | .right _ => find_label lbl s' k
    | _, _ => none

  def find_label_ls (lbl : label) :
      labeled_statements → cont → Option (statement × cont)
    | .LSnil, _ => none
    | .LScons _ s rest, k =>
        match find_label lbl s (.Kseq (seq_of_labeled_statement rest) k) with
        | some sk => some sk
        | none => find_label_ls lbl rest k
end

/-! ## Program transitions -/

inductive estep
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) : state → trace → state → Prop where
  | step_lred {C f a k e m a' m'} :
      lred ge e a m a' m' →
      context .LV .RV C →
      estep xi ge (.ExprState f (C a) k e m) E0 (.ExprState f (C a') k e m')
  | step_rred {C f a k e m t a' m'} :
      rred
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge e a m t a' m' →
      context .RV .RV C →
      estep xi ge (.ExprState f (C a) k e m) t (.ExprState f (C a') k e m')
  | step_call {C f a k e m fd vargs ty} :
      callred
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge a m fd vargs ty →
      context .RV .RV C →
      estep xi ge (.ExprState f (C a) k e m) E0
        (.Callstate fd vargs (.Kcall f e C ty k) m)
  | step_stuck {C f a k e m K} :
      context K .RV C →
      ¬ imm_safe
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge e K a m →
      estep xi ge (.ExprState f (C a) k e m) E0 .Stuckstate

export estep (step_lred step_rred step_call step_stuck)

inductive sstep
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) : state → trace → state → Prop where
  | do₁ {f x k e m} :
      sstep xi ge (.State f (.Sdo x) k e m) E0 (.ExprState f x (.Kdo k) e m)
  | do₂ {f v ty k e m} :
      sstep xi ge (.ExprState f (.Eval v ty) (.Kdo k) e m) E0 (.State f .Sskip k e m)
  | sequence {f s1 s2 k e m} :
      sstep xi ge (.State f (.Ssequence s1 s2) k e m) E0 (.State f s1 (.Kseq s2 k) e m)
  | skipSequence {f s k e m} :
      sstep xi ge (.State f .Sskip (.Kseq s k) e m) E0 (.State f s k e m)
  | continueSequence {f s k e m} :
      sstep xi ge (.State f .Scontinue (.Kseq s k) e m) E0 (.State f .Scontinue k e m)
  | breakSequence {f s k e m} :
      sstep xi ge (.State f .Sbreak (.Kseq s k) e m) E0 (.State f .Sbreak k e m)
  | ifStart {f a s1 s2 k e m} :
      sstep xi ge (.State f (.Sifthenelse a s1 s2) k e m) E0
        (.ExprState f a (.Kifthenelse s1 s2 k) e m)
  | ifFinish {f v ty s1 s2 k e m b} :
      bool_val v ty m = some b →
      sstep xi ge (.ExprState f (.Eval v ty) (.Kifthenelse s1 s2 k) e m) E0
        (.State f (if b then s1 else s2) k e m)
  | whileStart {f x s k e m} :
      sstep xi ge (.State f (.Swhile x s) k e m) E0
        (.ExprState f x (.Kwhile1 x s k) e m)
  | whileFalse {f v ty x s k e m} :
      bool_val v ty m = some false →
      sstep xi ge (.ExprState f (.Eval v ty) (.Kwhile1 x s k) e m) E0
        (.State f .Sskip k e m)
  | whileTrue {f v ty x s k e m} :
      bool_val v ty m = some true →
      sstep xi ge (.ExprState f (.Eval v ty) (.Kwhile1 x s k) e m) E0
        (.State f s (.Kwhile2 x s k) e m)
  | whileNext {f s0 x s k e m} :
      (s0 = .Sskip ∨ s0 = .Scontinue) →
      sstep xi ge (.State f s0 (.Kwhile2 x s k) e m) E0 (.State f (.Swhile x s) k e m)
  | whileBreak {f x s k e m} :
      sstep xi ge (.State f .Sbreak (.Kwhile2 x s k) e m) E0 (.State f .Sskip k e m)
  | dowhileStart {f a s k e m} :
      sstep xi ge (.State f (.Sdowhile a s) k e m) E0 (.State f s (.Kdowhile1 a s k) e m)
  | dowhileTest {f s0 x s k e m} :
      (s0 = .Sskip ∨ s0 = .Scontinue) →
      sstep xi ge (.State f s0 (.Kdowhile1 x s k) e m) E0
        (.ExprState f x (.Kdowhile2 x s k) e m)
  | dowhileFalse {f v ty x s k e m} :
      bool_val v ty m = some false →
      sstep xi ge (.ExprState f (.Eval v ty) (.Kdowhile2 x s k) e m) E0
        (.State f .Sskip k e m)
  | dowhileTrue {f v ty x s k e m} :
      bool_val v ty m = some true →
      sstep xi ge (.ExprState f (.Eval v ty) (.Kdowhile2 x s k) e m) E0
        (.State f (.Sdowhile x s) k e m)
  | dowhileBreak {f a s k e m} :
      sstep xi ge (.State f .Sbreak (.Kdowhile1 a s k) e m) E0 (.State f .Sskip k e m)
  | forStart {f a1 a2 a3 s k e m} :
      a1 ≠ .Sskip →
      sstep xi ge (.State f (.Sfor a1 a2 a3 s) k e m) E0
        (.State f a1 (.Kseq (.Sfor .Sskip a2 a3 s) k) e m)
  | forTest {f a2 a3 s k e m} :
      sstep xi ge (.State f (.Sfor .Sskip a2 a3 s) k e m) E0
        (.ExprState f a2 (.Kfor2 a2 a3 s k) e m)
  | forFalse {f v ty a2 a3 s k e m} :
      bool_val v ty m = some false →
      sstep xi ge (.ExprState f (.Eval v ty) (.Kfor2 a2 a3 s k) e m) E0
        (.State f .Sskip k e m)
  | forTrue {f v ty a2 a3 s k e m} :
      bool_val v ty m = some true →
      sstep xi ge (.ExprState f (.Eval v ty) (.Kfor2 a2 a3 s k) e m) E0
        (.State f s (.Kfor3 a2 a3 s k) e m)
  | forIter {f x a2 a3 s k e m} :
      (x = .Sskip ∨ x = .Scontinue) →
      sstep xi ge (.State f x (.Kfor3 a2 a3 s k) e m) E0
        (.State f a3 (.Kfor4 a2 a3 s k) e m)
  | forBreak {f a2 a3 s k e m} :
      sstep xi ge (.State f .Sbreak (.Kfor3 a2 a3 s k) e m) E0 (.State f .Sskip k e m)
  | forNext {f a2 a3 s k e m} :
      sstep xi ge (.State f .Sskip (.Kfor4 a2 a3 s k) e m) E0
        (.State f (.Sfor .Sskip a2 a3 s) k e m)
  | returnNone {f k e m m'} :
      Mem.free_list m (blocks_of_env ge e) = some m' →
      sstep xi ge (.State f (.Sreturn none) k e m) E0
        (.Returnstate .Vundef (call_cont k) m')
  | returnSome {f x k e m} :
      sstep xi ge (.State f (.Sreturn (some x)) k e m) E0
        (.ExprState f x (.Kreturn k) e m)
  | returnValue {f v1 ty k e m v2 m'} :
      sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v1 ty f.fn_return m = some v2 →
      Mem.free_list m (blocks_of_env ge e) = some m' →
      sstep xi ge (.ExprState f (.Eval v1 ty) (.Kreturn k) e m) E0
        (.Returnstate v2 (call_cont k) m')
  | skipCall {f k e m m'} :
      is_call_cont k →
      Mem.free_list m (blocks_of_env ge e) = some m' →
      sstep xi ge (.State f .Sskip k e m) E0 (.Returnstate .Vundef k m')
  | switchStart {f x sl k e m} :
      sstep xi ge (.State f (.Sswitch x sl) k e m) E0
        (.ExprState f x (.Kswitch1 sl k) e m)
  | switchSelect {f ty sl k e m v n} :
      sem_switch_arg v ty = some n →
      sstep xi ge (.ExprState f (.Eval v ty) (.Kswitch1 sl k) e m) E0
        (.State f (seq_of_labeled_statement (select_switch n sl)) (.Kswitch2 k) e m)
  | switchFinish {f x k e m} :
      (x = .Sskip ∨ x = .Sbreak) →
      sstep xi ge (.State f x (.Kswitch2 k) e m) E0 (.State f .Sskip k e m)
  | switchContinue {f k e m} :
      sstep xi ge (.State f .Scontinue (.Kswitch2 k) e m) E0 (.State f .Scontinue k e m)
  | label {f lbl s k e m} :
      sstep xi ge (.State f (.Slabel lbl s) k e m) E0 (.State f s k e m)
  | goto {f lbl k e m s' k'} :
      find_label lbl f.fn_body (call_cont k) = some (s', k') →
      sstep xi ge (.State f (.Sgoto lbl) k e m) E0 (.State f s' k' e m)
  | internalFunction {f vargs k m e m1 m2} :
      list_norepet (var_names f.fn_params ++ var_names f.fn_vars) →
      alloc_variables ge empty_env m (f.fn_params ++ f.fn_vars) e m1 →
      bind_parameters ge e m1 f.fn_params vargs m2 →
      sstep xi ge (.Callstate (.Internal f) vargs k m) E0 (.State f f.fn_body k e m2)
  | externalFunction {ef targs tres cc vargs k m vres t m'} :
      external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ef (symbolEnv ge) vargs m t vres m' →
      sstep xi ge (.Callstate (.External ef targs tres cc) vargs k m) t
        (.Returnstate vres k m')
  | returnstate {v f e C ty k m} :
      sstep xi ge (.Returnstate v (.Kcall f e C ty k) m) E0
        (.ExprState f (C (.Eval v ty)) k e m)

def step
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (S : state) (t : trace) (S' : state) : Prop :=
  estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge S t S' ∨
    sstep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge S t S'

/-! ## Whole-program semantics -/

inductive initial_state (p : program) : state → Prop where
  | intro {b f m0} :
      Genv.init_mem (program_of_program p) = some m0 →
      Genv.find_symbol (globalenv p).genv_genv p.prog_main = some b →
      Genv.find_funct_ptr (globalenv p).genv_genv b = some f →
      type_of_fundef f = .Tfunction [] type_int32s cc_default →
      initial_state p (.Callstate f [] .Kstop m0)

inductive final_state : state → int → Prop where
  | intro (r : int) (m : mem) : final_state (.Returnstate (.Vint r) .Kstop m) r

def semantics
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (p : program) : Smallstep.semantics :=
  { state := state
    genvtype := genv
    step := step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi
    initial_state := initial_state p
    final_state := final_state
    globalenv := globalenv p
    symbolenv := symbolEnv (globalenv p) }

def semantics_single_eventsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : program),
    single_events
      (semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi p)

end CompCert4Lean.Cfrontend.Csem
