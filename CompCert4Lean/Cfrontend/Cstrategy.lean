import CompCert4Lean.Cfrontend.Csem

/-!
# Deterministic evaluation strategy for CompCert C

Definition-bearing translation of the required surface of CompCert's
`cfrontend/Cstrategy.v`.  The integrated semantics makes the external-call
environment explicit, so the strategy carries the same `ExternalCalls`
parameter as `Csem`.
-/

namespace CompCert4Lean.Cfrontend.Cstrategy

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
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.Mem.mem
private abbrev trace := CompCert4Lean.Common.Events.trace
private abbrev event := CompCert4Lean.Common.Events.event
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev type := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev composite := CompCert4Lean.Cfrontend.Ctypes.composite
private abbrev expr := CompCert4Lean.Cfrontend.Csyntax.expr
private abbrev exprlist := CompCert4Lean.Cfrontend.Csyntax.exprlist
private abbrev function := CompCert4Lean.Cfrontend.Csyntax.function
private abbrev fundef := CompCert4Lean.Cfrontend.Csyntax.fundef
private abbrev program := CompCert4Lean.Cfrontend.Csyntax.program
private abbrev genv := CompCert4Lean.Cfrontend.Csem.genv
private abbrev env := CompCert4Lean.Cfrontend.Csem.env
private abbrev state := CompCert4Lean.Cfrontend.Csem.state
private abbrev cont := CompCert4Lean.Cfrontend.Csem.cont
private abbrev kind := CompCert4Lean.Cfrontend.Csem.kind
private abbrev ExternalCalls := CompCert4Lean.Common.ExternalCalls.ExternalCalls
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

private abbrev zOfNat := ZArith.BinInt.Z.of_nat

/-! ## Strategy definitions -/

def simple : expr → Bool
  | .Eloc _ _ _ _ => true
  | .Evar _ _ => true
  | .Ederef r _ => simple r
  | .Efield r _ _ => simple r
  | .Eval _ _ => true
  | .Evalof l _ => simple l && !type_is_volatile (typeof l)
  | .Eaddrof l _ => simple l
  | .Eunop _ r _ => simple r
  | .Ebinop _ r1 r2 _ => simple r1 && simple r2
  | .Ecast r _ => simple r
  | .Eseqand _ _ _ => false
  | .Eseqor _ _ _ => false
  | .Econdition _ _ _ _ => false
  | .Esizeof _ _ => true
  | .Ealignof _ _ => true
  | .Eassign _ _ _ => false
  | .Eassignop _ _ _ _ _ => false
  | .Epostincr _ _ _ => false
  | .Ecomma _ _ _ => false
  | .Ecall _ _ _ => false
  | .Ebuiltin _ _ _ _ => false
  | .Eparen _ _ _ => false

def simplelist : exprlist → Bool
  | .Enil => true
  | .Econs r rl => simple r && simplelist rl

mutual
  inductive eval_simple_lvalue
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ge : genv) (e : env) (m : mem) :
      expr → block → ptrofs → bitfield → Prop where
    | esl_loc {b ofs ty bf} :
        eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge e m (.Eloc b ofs bf ty) b ofs bf
    | esl_var_local {x ty b} :
        PTree.get x e = some (b, ty) →
        eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge e m (.Evar x ty) b Ptrofs.zero .Full
    | esl_var_global {x ty b} :
        PTree.get x e = none →
        Genv.find_symbol ge.genv_genv x = some b →
        eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge e m (.Evar x ty) b Ptrofs.zero .Full
    | esl_deref {r ty b ofs} :
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r (.Vptr b ofs) →
        eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge e m (.Ederef r ty) b ofs .Full
    | esl_field_struct {r f ty b ofs id co a delta bf} :
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r (.Vptr b ofs) →
        typeof r = .Tstruct id a →
        PTree.get id ge.genv_cenv = some co →
        field_offset ge.genv_cenv f co.co_members = .OK (delta, bf) →
        eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge e m (.Efield r f ty) b
          (Ptrofs.add ofs (Ptrofs.repr delta)) bf
    | esl_field_union {r f ty b ofs id co a delta bf} :
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r (.Vptr b ofs) →
        typeof r = .Tunion id a →
        union_field_offset ge.genv_cenv f co.co_members = .OK (delta, bf) →
        PTree.get id ge.genv_cenv = some co →
        eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge e m (.Efield r f ty) b
          (Ptrofs.add ofs (Ptrofs.repr delta)) bf

  inductive eval_simple_rvalue
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ge : genv) (e : env) (m : mem) :
      expr → val → Prop where
    | esr_val {v ty} :
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m (.Eval v ty) v
    | esr_rvalof {b ofs bf l ty v} :
        eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m l b ofs bf →
        ty = typeof l →
        type_is_volatile ty = false →
        Csem.deref_loc ge ty m b ofs bf E0 v →
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m (.Evalof l ty) v
    | esr_addrof {b ofs l ty} :
        eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m l b ofs .Full →
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m (.Eaddrof l ty) (.Vptr b ofs)
    | esr_unop {op r1 ty v1 v} :
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r1 v1 →
        sem_unary_operation
          (binary64_certificate := binary64_certificate) op v1 (typeof r1) m = some v →
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m (.Eunop op r1 ty) v
    | esr_binop {op r1 r2 ty v1 v2 v} :
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r1 v1 →
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r2 v2 →
        sem_binary_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge.genv_cenv op v1 (typeof r1) v2 (typeof r2) m = some v →
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m (.Ebinop op r1 r2 ty) v
    | esr_cast {ty r1 v1 v} :
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r1 v1 →
        sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v1 (typeof r1) ty m = some v →
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m (.Ecast r1 ty) v
    | esr_sizeof {ty1 ty} :
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m (.Esizeof ty1 ty)
          (CompCert4Lean.Common.Values.Vptrofs (Ptrofs.repr (sizeof ge.genv_cenv ty1)))
    | esr_alignof {ty1 ty} :
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m (.Ealignof ty1 ty)
          (CompCert4Lean.Common.Values.Vptrofs (Ptrofs.repr (alignof ge.genv_cenv ty1)))
end

section EvalSimpleLvalueSourceEndpoints

variable
  [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
  [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

def esl_var_local
    (ge : genv) (e : env) (m : mem) (x : ident) (ty : type) (b : block)
    (hlocal : PTree.get x e = some (b, ty)) :
    eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge e m (.Evar x ty) b Ptrofs.zero .Full :=
  eval_simple_lvalue.esl_var_local hlocal

def esl_var_global
    (ge : genv) (e : env) (m : mem) (x : ident) (ty : type) (b : block)
    (hlocal : PTree.get x e = none)
    (hglobal : Genv.find_symbol ge.genv_genv x = some b) :
    eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge e m (.Evar x ty) b Ptrofs.zero .Full :=
  eval_simple_lvalue.esl_var_global hlocal hglobal

def esl_field_struct
    (ge : genv) (e : env) (m : mem) (r : expr) (f : ident) (ty : type)
    (b : block) (ofs : ptrofs) (id : ident) (co : composite) (a : attr)
    (delta : Z) (bf : bitfield)
    (heval : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r (.Vptr b ofs))
    (htype : typeof r = .Tstruct id a)
    (hcomposite : PTree.get id ge.genv_cenv = some co)
    (hoffset : field_offset ge.genv_cenv f co.co_members = .OK (delta, bf)) :
    eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge e m (.Efield r f ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) bf :=
  eval_simple_lvalue.esl_field_struct heval htype hcomposite hoffset

def esl_field_union
    (ge : genv) (e : env) (m : mem) (r : expr) (f : ident) (ty : type)
    (b : block) (ofs : ptrofs) (id : ident) (co : composite) (a : attr)
    (delta : Z) (bf : bitfield)
    (heval : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r (.Vptr b ofs))
    (htype : typeof r = .Tunion id a)
    (hoffset : union_field_offset ge.genv_cenv f co.co_members = .OK (delta, bf))
    (hcomposite : PTree.get id ge.genv_cenv = some co) :
    eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge e m (.Efield r f ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) bf :=
  eval_simple_lvalue.esl_field_union heval htype hoffset hcomposite

end EvalSimpleLvalueSourceEndpoints

export eval_simple_lvalue (esl_loc esl_deref)

export eval_simple_rvalue
  (esr_val esr_rvalof esr_addrof esr_unop esr_binop esr_cast esr_sizeof esr_alignof)

inductive eval_simple_list
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (ge : genv) (e : env) (m : mem) :
    exprlist → List type → List val → Prop where
  | esrl_nil :
      eval_simple_list
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e m .Enil [] []
  | esrl_cons {r rl ty tyl v vl v'} :
      eval_simple_rvalue
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e m r v' →
      sem_cast
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) v' (typeof r) ty m = some v →
      eval_simple_list
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e m rl tyl vl →
      eval_simple_list
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e m (.Econs r rl) (ty :: tyl) (v :: vl)

export eval_simple_list (esrl_nil esrl_cons)

mutual
  inductive leftcontext : kind → kind → (expr → expr) → Prop where
    | lctx_top (k : kind) :
        leftcontext k k (fun x => x)
    | lctx_deref {k C ty} :
        leftcontext k .RV C →
        leftcontext k .LV (fun x => .Ederef (C x) ty)
    | lctx_field {k C f ty} :
        leftcontext k .RV C →
        leftcontext k .LV (fun x => .Efield (C x) f ty)
    | lctx_rvalof {k C ty} :
        leftcontext k .LV C →
        leftcontext k .RV (fun x => .Evalof (C x) ty)
    | lctx_addrof {k C ty} :
        leftcontext k .LV C →
        leftcontext k .RV (fun x => .Eaddrof (C x) ty)
    | lctx_unop {k C op ty} :
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Eunop op (C x) ty)
    | lctx_binop_left {k C op e2 ty} :
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Ebinop op (C x) e2 ty)
    | lctx_binop_right {k C op e1 ty} :
        simple e1 = true →
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Ebinop op e1 (C x) ty)
    | lctx_cast {k C ty} :
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Ecast (C x) ty)
    | lctx_seqand {k C r2 ty} :
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Eseqand (C x) r2 ty)
    | lctx_seqor {k C r2 ty} :
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Eseqor (C x) r2 ty)
    | lctx_condition {k C r2 r3 ty} :
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Econdition (C x) r2 r3 ty)
    | lctx_assign_left {k C e2 ty} :
        leftcontext k .LV C →
        leftcontext k .RV (fun x => .Eassign (C x) e2 ty)
    | lctx_assign_right {k C e1 ty} :
        simple e1 = true →
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Eassign e1 (C x) ty)
    | lctx_assignop_left {k C op e2 tyres ty} :
        leftcontext k .LV C →
        leftcontext k .RV (fun x => .Eassignop op (C x) e2 tyres ty)
    | lctx_assignop_right {k C op e1 tyres ty} :
        simple e1 = true →
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Eassignop op e1 (C x) tyres ty)
    | lctx_postincr {k C id ty} :
        leftcontext k .LV C →
        leftcontext k .RV (fun x => .Epostincr id (C x) ty)
    | lctx_call_left {k C el ty} :
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Ecall (C x) el ty)
    | lctx_call_right {k C e1 ty} :
        simple e1 = true →
        leftcontextlist k C →
        leftcontext k .RV (fun x => .Ecall e1 (C x) ty)
    | lctx_builtin {k C ef tyargs ty} :
        leftcontextlist k C →
        leftcontext k .RV (fun x => .Ebuiltin ef tyargs (C x) ty)
    | lctx_comma {k C e2 ty} :
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Ecomma (C x) e2 ty)
    | lctx_paren {k C tycast ty} :
        leftcontext k .RV C →
        leftcontext k .RV (fun x => .Eparen (C x) tycast ty)

  inductive leftcontextlist : kind → (expr → exprlist) → Prop where
    | lctx_list_head {k C el} :
        leftcontext k .RV C →
        leftcontextlist k (fun x => .Econs (C x) el)
    | lctx_list_tail {k C e1} :
        simple e1 = true →
        leftcontextlist k C →
        leftcontextlist k (fun x => .Econs e1 (C x))
end

export leftcontext
  (lctx_top lctx_deref lctx_field lctx_rvalof lctx_addrof lctx_unop
    lctx_binop_left lctx_binop_right lctx_cast lctx_seqand lctx_seqor
    lctx_condition lctx_assign_left lctx_assign_right lctx_assignop_left
    lctx_assignop_right lctx_postincr lctx_call_left lctx_call_right
    lctx_builtin lctx_comma lctx_paren)

export leftcontextlist (lctx_list_head lctx_list_tail)

inductive estep
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) : state → trace → state → Prop where
  | step_expr {f r k e m v ty} :
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r v →
      (match r with | .Eval _ _ => False | _ => True) →
      ty = typeof r →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f r k e m) E0
        (.ExprState f (.Eval v ty) k e m)
  | step_rvalof_volatile {f C l ty k e m b ofs bf t v} :
      leftcontext .RV .RV C →
      eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m l b ofs bf →
      Csem.deref_loc ge ty m b ofs bf t v →
      ty = typeof l →
      type_is_volatile ty = true →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Evalof l ty)) k e m) t
        (.ExprState f (C (.Eval v ty)) k e m)
  | step_seqand_true {f C r1 r2 ty k e m v} :
      leftcontext .RV .RV C →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r1 v →
      bool_val v (typeof r1) m = some true →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Eseqand r1 r2 ty)) k e m) E0
        (.ExprState f (C (.Eparen r2 type_bool ty)) k e m)
  | step_seqand_false {f C r1 r2 ty k e m v} :
      leftcontext .RV .RV C →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r1 v →
      bool_val v (typeof r1) m = some false →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Eseqand r1 r2 ty)) k e m) E0
        (.ExprState f (C (.Eval (.Vint Int.zero) ty)) k e m)
  | step_seqor_true {f C r1 r2 ty k e m v} :
      leftcontext .RV .RV C →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r1 v →
      bool_val v (typeof r1) m = some true →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Eseqor r1 r2 ty)) k e m) E0
        (.ExprState f (C (.Eval (.Vint Int.one) ty)) k e m)
  | step_seqor_false {f C r1 r2 ty k e m v} :
      leftcontext .RV .RV C →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r1 v →
      bool_val v (typeof r1) m = some false →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Eseqor r1 r2 ty)) k e m) E0
        (.ExprState f (C (.Eparen r2 type_bool ty)) k e m)
  | step_condition {f C r1 r2 r3 ty k e m v b} :
      leftcontext .RV .RV C →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r1 v →
      bool_val v (typeof r1) m = some b →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Econdition r1 r2 r3 ty)) k e m) E0
        (.ExprState f (C (.Eparen (if b then r2 else r3) ty ty)) k e m)
  | step_assign {f C l r ty k e m b ofs bf v v1 t m' v'} :
      leftcontext .RV .RV C →
      eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m l b ofs bf →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r v →
      sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v (typeof r) (typeof l) m = some v1 →
      Csem.assign_loc ge (typeof l) m b ofs bf v1 t m' v' →
      ty = typeof l →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Eassign l r ty)) k e m) t
        (.ExprState f (C (.Eval v' ty)) k e m')
  | step_assignop {f C op l r tyres ty k e m b ofs bf v1 v2 v3 v4 t1 t2 m' v' t} :
      leftcontext .RV .RV C →
      eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m l b ofs bf →
      Csem.deref_loc ge (typeof l) m b ofs bf t1 v1 →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r v2 →
      sem_binary_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge.genv_cenv op v1 (typeof l) v2 (typeof r) m = some v3 →
      sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v3 tyres (typeof l) m = some v4 →
      Csem.assign_loc ge (typeof l) m b ofs bf v4 t2 m' v' →
      ty = typeof l →
      t = Eapp t1 t2 →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Eassignop op l r tyres ty)) k e m) t
        (.ExprState f (C (.Eval v' ty)) k e m')
  | step_assignop_stuck {f C op l r tyres ty k e m b ofs bf v1 v2 t} :
      leftcontext .RV .RV C →
      eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m l b ofs bf →
      Csem.deref_loc ge (typeof l) m b ofs bf t v1 →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r v2 →
      (match sem_binary_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge.genv_cenv op v1 (typeof l) v2 (typeof r) m with
       | none => True
       | some v3 =>
           match sem_cast
             (binary64_certificate := binary64_certificate)
             (binary32_certificate := binary32_certificate) v3 tyres (typeof l) m with
           | none => True
           | some v4 => ∀ t2 m' v', ¬ Csem.assign_loc ge (typeof l) m b ofs bf v4 t2 m' v') →
      ty = typeof l →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Eassignop op l r tyres ty)) k e m) t .Stuckstate
  | step_postincr {f C id l ty k e m b ofs bf v1 v2 v3 t1 t2 m' v' t} :
      leftcontext .RV .RV C →
      eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m l b ofs bf →
      Csem.deref_loc ge ty m b ofs bf t1 v1 →
      sem_incrdecr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge.genv_cenv id v1 ty m = some v2 →
      sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v2 (incrdecr_type ty) ty m = some v3 →
      Csem.assign_loc ge ty m b ofs bf v3 t2 m' v' →
      ty = typeof l →
      t = Eapp t1 t2 →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Epostincr id l ty)) k e m) t
        (.ExprState f (C (.Eval v1 ty)) k e m')
  | step_postincr_stuck {f C id l ty k e m b ofs bf v1 t} :
      leftcontext .RV .RV C →
      eval_simple_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m l b ofs bf →
      Csem.deref_loc ge ty m b ofs bf t v1 →
      (match sem_incrdecr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge.genv_cenv id v1 ty m with
       | none => True
       | some v2 =>
           match sem_cast
             (binary64_certificate := binary64_certificate)
             (binary32_certificate := binary32_certificate) v2 (incrdecr_type ty) ty m with
           | none => True
           | some v3 => ∀ t2 m' v', ¬ Csem.assign_loc ge (typeof l) m b ofs bf v3 t2 m' v') →
      ty = typeof l →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Epostincr id l ty)) k e m) t .Stuckstate
  | step_comma {f C r1 r2 ty k e m v} :
      leftcontext .RV .RV C →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r1 v →
      ty = typeof r2 →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Ecomma r1 r2 ty)) k e m) E0
        (.ExprState f (C r2) k e m)
  | step_paren {f C r tycast ty k e m v1 v} :
      leftcontext .RV .RV C →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r v1 →
      sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v1 (typeof r) tycast m = some v →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Eparen r tycast ty)) k e m) E0
        (.ExprState f (C (.Eval v ty)) k e m)
  | step_call {f C rf rargs ty k e m targs tres cconv vf vargs fd} :
      leftcontext .RV .RV C →
      Cop.classify_fun (typeof rf) = .fun_case_f targs tres cconv →
      eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m rf vf →
      eval_simple_list
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m rargs targs vargs →
      Genv.find_funct ge.genv_genv vf = some fd →
      Csyntax.type_of_fundef fd = .Tfunction targs tres cconv →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Ecall rf rargs ty)) k e m) E0
        (.Callstate fd vargs (.Kcall f e C ty k) m)
  | step_builtin {f C ef tyargs rargs ty k e m vargs t vres m'} :
      leftcontext .RV .RV C →
      eval_simple_list
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m rargs tyargs vargs →
      external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi ef (Genv.to_senv ge.genv_genv) vargs m t vres m' →
      estep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Ebuiltin ef tyargs rargs ty)) k e m) t
        (.ExprState f (C (.Eval vres ty)) k e m')

section EstepSourceEndpoints

variable
  [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
  [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

def step_expr
    (xi : ExternalCalls) (ge : genv) (f : function) (r : expr) (k : cont)
    (e : env) (m : mem) (v : val) (ty : type)
    (heval : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r v)
    (hnotval : (fun r : expr => match r with | .Eval _ _ => False | _ => True) r)
    (htype : ty = typeof r) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f r k e m) E0 (.ExprState f (.Eval v ty) k e m) :=
  estep.step_expr heval hnotval htype

def step_rvalof_volatile
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (l : expr) (ty : type) (k : cont) (e : env) (m : mem) (b : block)
    (ofs : ptrofs) (bf : bitfield) (t : trace) (v : val)
    (hcontext : leftcontext .RV .RV C)
    (heval : eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m l b ofs bf)
    (hderef : Csem.deref_loc ge ty m b ofs bf t v)
    (htype : ty = typeof l) (hvolatile : type_is_volatile ty = true) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Evalof l ty)) k e m) t
      (.ExprState f (C (.Eval v ty)) k e m) :=
  estep.step_rvalof_volatile hcontext heval hderef htype hvolatile

def step_seqand_true
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (r1 r2 : expr) (ty : type) (k : cont) (e : env) (m : mem) (v : val)
    (hcontext : leftcontext .RV .RV C)
    (heval : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r1 v)
    (hbool : bool_val v (typeof r1) m = some true) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Eseqand r1 r2 ty)) k e m) E0
      (.ExprState f (C (.Eparen r2 type_bool ty)) k e m) :=
  estep.step_seqand_true hcontext heval hbool

def step_seqand_false
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (r1 r2 : expr) (ty : type) (k : cont) (e : env) (m : mem) (v : val)
    (hcontext : leftcontext .RV .RV C)
    (heval : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r1 v)
    (hbool : bool_val v (typeof r1) m = some false) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Eseqand r1 r2 ty)) k e m) E0
      (.ExprState f (C (.Eval (.Vint Int.zero) ty)) k e m) :=
  estep.step_seqand_false hcontext heval hbool

def step_seqor_true
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (r1 r2 : expr) (ty : type) (k : cont) (e : env) (m : mem) (v : val)
    (hcontext : leftcontext .RV .RV C)
    (heval : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r1 v)
    (hbool : bool_val v (typeof r1) m = some true) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Eseqor r1 r2 ty)) k e m) E0
      (.ExprState f (C (.Eval (.Vint Int.one) ty)) k e m) :=
  estep.step_seqor_true hcontext heval hbool

def step_seqor_false
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (r1 r2 : expr) (ty : type) (k : cont) (e : env) (m : mem) (v : val)
    (hcontext : leftcontext .RV .RV C)
    (heval : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r1 v)
    (hbool : bool_val v (typeof r1) m = some false) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Eseqor r1 r2 ty)) k e m) E0
      (.ExprState f (C (.Eparen r2 type_bool ty)) k e m) :=
  estep.step_seqor_false hcontext heval hbool

def step_condition
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (r1 r2 r3 : expr) (ty : type) (k : cont) (e : env) (m : mem) (v : val)
    (b : Bool) (hcontext : leftcontext .RV .RV C)
    (heval : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r1 v)
    (hbool : bool_val v (typeof r1) m = some b) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Econdition r1 r2 r3 ty)) k e m) E0
      (.ExprState f (C (.Eparen (if b then r2 else r3) ty ty)) k e m) :=
  estep.step_condition hcontext heval hbool

def step_assign
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (l r : expr) (ty : type) (k : cont) (e : env) (m : mem) (b : block)
    (ofs : ptrofs) (bf : bitfield) (v v1 : val) (t : trace) (m' : mem)
    (v' : val) (hcontext : leftcontext .RV .RV C)
    (hlvalue : eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m l b ofs bf)
    (hrvalue : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r v)
    (hcast : sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      v (typeof r) (typeof l) m = some v1)
    (hassign : Csem.assign_loc ge (typeof l) m b ofs bf v1 t m' v')
    (htype : ty = typeof l) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Eassign l r ty)) k e m) t
      (.ExprState f (C (.Eval v' ty)) k e m') :=
  estep.step_assign hcontext hlvalue hrvalue hcast hassign htype

def step_assignop
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (op : binary_operation) (l r : expr) (tyres ty : type) (k : cont)
    (e : env) (m : mem) (b : block) (ofs : ptrofs) (bf : bitfield)
    (v1 v2 v3 v4 : val) (t1 t2 : trace) (m' : mem) (v' : val) (t : trace)
    (hcontext : leftcontext .RV .RV C)
    (hlvalue : eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m l b ofs bf)
    (hderef : Csem.deref_loc ge (typeof l) m b ofs bf t1 v1)
    (hrvalue : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r v2)
    (hbinary : sem_binary_operation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge.genv_cenv op v1 (typeof l) v2 (typeof r) m = some v3)
    (hcast : sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      v3 tyres (typeof l) m = some v4)
    (hassign : Csem.assign_loc ge (typeof l) m b ofs bf v4 t2 m' v')
    (htype : ty = typeof l) (htrace : t = Eapp t1 t2) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Eassignop op l r tyres ty)) k e m) t
      (.ExprState f (C (.Eval v' ty)) k e m') :=
  estep.step_assignop hcontext hlvalue hderef hrvalue hbinary hcast hassign htype htrace

def step_assignop_stuck
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (op : binary_operation) (l r : expr) (tyres ty : type) (k : cont)
    (e : env) (m : mem) (b : block) (ofs : ptrofs) (bf : bitfield)
    (v1 v2 : val) (t : trace) (hcontext : leftcontext .RV .RV C)
    (hlvalue : eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m l b ofs bf)
    (hderef : Csem.deref_loc ge (typeof l) m b ofs bf t v1)
    (hrvalue : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r v2)
    (hstuck :
      match sem_binary_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge.genv_cenv op v1 (typeof l) v2 (typeof r) m with
      | none => True
      | some v3 =>
          match sem_cast
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              v3 tyres (typeof l) m with
          | none => True
          | some v4 => ∀ t2 m' v',
              ¬ Csem.assign_loc ge (typeof l) m b ofs bf v4 t2 m' v')
    (htype : ty = typeof l) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Eassignop op l r tyres ty)) k e m) t .Stuckstate :=
  estep.step_assignop_stuck hcontext hlvalue hderef hrvalue hstuck htype

def step_postincr
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (id : incr_or_decr) (l : expr) (ty : type) (k : cont) (e : env) (m : mem)
    (b : block) (ofs : ptrofs) (bf : bitfield) (v1 v2 v3 : val)
    (t1 t2 : trace) (m' : mem) (v' : val) (t : trace)
    (hcontext : leftcontext .RV .RV C)
    (hlvalue : eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m l b ofs bf)
    (hderef : Csem.deref_loc ge ty m b ofs bf t1 v1)
    (hincr : sem_incrdecr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge.genv_cenv id v1 ty m = some v2)
    (hcast : sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      v2 (incrdecr_type ty) ty m = some v3)
    (hassign : Csem.assign_loc ge ty m b ofs bf v3 t2 m' v')
    (htype : ty = typeof l) (htrace : t = Eapp t1 t2) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Epostincr id l ty)) k e m) t
      (.ExprState f (C (.Eval v1 ty)) k e m') :=
  estep.step_postincr hcontext hlvalue hderef hincr hcast hassign htype htrace

def step_postincr_stuck
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (id : incr_or_decr) (l : expr) (ty : type) (k : cont) (e : env) (m : mem)
    (b : block) (ofs : ptrofs) (bf : bitfield) (v1 : val) (t : trace)
    (hcontext : leftcontext .RV .RV C)
    (hlvalue : eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m l b ofs bf)
    (hderef : Csem.deref_loc ge ty m b ofs bf t v1)
    (hstuck :
      match sem_incrdecr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge.genv_cenv id v1 ty m with
      | none => True
      | some v2 =>
          match sem_cast
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              v2 (incrdecr_type ty) ty m with
          | none => True
          | some v3 => ∀ t2 m' v',
              ¬ Csem.assign_loc ge (typeof l) m b ofs bf v3 t2 m' v')
    (htype : ty = typeof l) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Epostincr id l ty)) k e m) t .Stuckstate :=
  estep.step_postincr_stuck hcontext hlvalue hderef hstuck htype

def step_comma
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (r1 r2 : expr) (ty : type) (k : cont) (e : env) (m : mem) (v : val)
    (hcontext : leftcontext .RV .RV C)
    (heval : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r1 v)
    (htype : ty = typeof r2) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Ecomma r1 r2 ty)) k e m) E0
      (.ExprState f (C r2) k e m) :=
  estep.step_comma hcontext heval htype

def step_paren
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (r : expr) (tycast ty : type) (k : cont) (e : env) (m : mem) (v1 v : val)
    (hcontext : leftcontext .RV .RV C)
    (heval : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r v1)
    (hcast : sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      v1 (typeof r) tycast m = some v) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Eparen r tycast ty)) k e m) E0
      (.ExprState f (C (.Eval v ty)) k e m) :=
  estep.step_paren hcontext heval hcast

def step_call
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (rf : expr) (rargs : exprlist) (ty : type) (k : cont) (e : env) (m : mem)
    (targs : List type) (tres : type) (cconv : calling_convention) (vf : val)
    (vargs : List val) (fd : fundef) (hcontext : leftcontext .RV .RV C)
    (hclassify : classify_fun (typeof rf) = .fun_case_f targs tres cconv)
    (hfun : eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m rf vf)
    (hargs : eval_simple_list
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m rargs targs vargs)
    (hfind : Genv.find_funct ge.genv_genv vf = some fd)
    (htype : type_of_fundef fd = .Tfunction targs tres cconv) :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Ecall rf rargs ty)) k e m) E0
      (.Callstate fd vargs (.Kcall f e C ty k) m) :=
  estep.step_call hcontext hclassify hfun hargs hfind htype

def step_builtin
    (xi : ExternalCalls) (ge : genv) (f : function) (C : expr → expr)
    (ef : external_function) (tyargs : List type) (rargs : exprlist) (ty : type)
    (k : cont) (e : env) (m : mem) (vargs : List val) (t : trace) (vres : val)
    (m' : mem) (hcontext : leftcontext .RV .RV C)
    (hargs : eval_simple_list
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m rargs tyargs vargs)
    (hexternal : external_call
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ef (Genv.to_senv ge.genv_genv) vargs m t vres m') :
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Ebuiltin ef tyargs rargs ty)) k e m) t
      (.ExprState f (C (.Eval vres ty)) k e m') :=
  estep.step_builtin hcontext hargs hexternal

end EstepSourceEndpoints

open CompCert4Lean.Cfrontend.Csem

def step
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (S : state) (t : trace) (S' : state) : Prop :=
  estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge S t S' ∨
    Csem.sstep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge S t S'

def safe
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (s : state) : Prop :=
  ∀ s', star
      (Csem.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi) ge s E0 s' →
    (∃ r, Csem.final_state s' r) ∨
    (∃ t s'', Csem.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge s' t s'')

def expr_kind : expr → kind
  | .Eloc _ _ _ _ => .LV
  | .Evar _ _ => .LV
  | .Ederef _ _ => .LV
  | .Efield _ _ _ => .LV
  | _ => .RV

def exprlist_all_values : exprlist → Prop
  | .Enil => True
  | .Econs (.Eval _ _) rl => exprlist_all_values rl
  | .Econs _ _ => False

def invert_expr_prop
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (e : env)
    (a : expr) (m : mem) : Prop :=
  match a with
  | .Eloc _ _ _ _ => False
  | .Evar x ty =>
      ∃ b, PTree.get x e = some (b, ty) ∨
        (PTree.get x e = none ∧ Genv.find_symbol ge.genv_genv x = some b)
  | .Ederef (.Eval v _) _ => ∃ b ofs, v = .Vptr b ofs
  | .Eaddrof (.Eloc _ _ bf _) _ => bf = .Full
  | .Efield (.Eval v ty1) f _ =>
      ∃ b ofs, v = .Vptr b ofs ∧
        match ty1 with
        | .Tstruct id _ =>
            ∃ co delta bf, PTree.get id ge.genv_cenv = some co ∧
              field_offset ge.genv_cenv f co.co_members = .OK (delta, bf)
        | .Tunion id _ =>
            ∃ co delta bf, PTree.get id ge.genv_cenv = some co ∧
              union_field_offset ge.genv_cenv f co.co_members = .OK (delta, bf)
        | _ => False
  | .Eval _ _ => False
  | .Evalof (.Eloc b ofs bf ty') ty =>
      ty' = ty ∧ ∃ t v, deref_loc ge ty m b ofs bf t v
  | .Eunop op (.Eval v1 ty1) _ =>
      ∃ v, sem_unary_operation
        (binary64_certificate := binary64_certificate) op v1 ty1 m = some v
  | .Ebinop op (.Eval v1 ty1) (.Eval v2 ty2) _ =>
      ∃ v, sem_binary_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge.genv_cenv op v1 ty1 v2 ty2 m = some v
  | .Ecast (.Eval v1 ty1) ty => ∃ v, sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 ty1 ty m = some v
  | .Eseqand (.Eval v1 ty1) _ _ => ∃ b, bool_val v1 ty1 m = some b
  | .Eseqor (.Eval v1 ty1) _ _ => ∃ b, bool_val v1 ty1 m = some b
  | .Econdition (.Eval v1 ty1) _ _ _ => ∃ b, bool_val v1 ty1 m = some b
  | .Eassign (.Eloc b ofs bf ty1) (.Eval v2 ty2) ty =>
      ∃ v m' v' t, ty = ty1 ∧
        sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v2 ty2 ty1 m = some v ∧
        assign_loc ge ty1 m b ofs bf v t m' v'
  | .Eassignop _ (.Eloc b ofs bf ty1) (.Eval _ _) _ ty =>
      ∃ t v1, ty = ty1 ∧ deref_loc ge ty1 m b ofs bf t v1
  | .Epostincr _ (.Eloc b ofs bf ty1) ty =>
      ∃ t v1, ty = ty1 ∧ deref_loc ge ty m b ofs bf t v1
  | .Ecomma (.Eval _ _) r2 ty => typeof r2 = ty
  | .Eparen (.Eval v1 ty1) ty2 _ => ∃ v, sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 ty1 ty2 m = some v
  | .Ecall (.Eval vf tyf) rargs _ =>
      exprlist_all_values rargs →
      ∃ tyargs tyres cconv fd vl,
        Cop.classify_fun tyf = .fun_case_f tyargs tyres cconv ∧
        Genv.find_funct ge.genv_genv vf = some fd ∧
        Csem.cast_arguments
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) m rargs tyargs vl ∧
        type_of_fundef fd = .Tfunction tyargs tyres cconv
  | .Ebuiltin ef tyargs rargs _ =>
      exprlist_all_values rargs →
      ∃ vargs t vres m',
        Csem.cast_arguments
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) m rargs tyargs vargs ∧
        external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi ef (Genv.to_senv ge.genv_genv) vargs m t vres m'
  | _ => True

def rval_list : List val → exprlist → exprlist
  | v :: vl, .Econs r rl => .Econs (.Eval v (typeof r)) (rval_list vl rl)
  | _, _ => .Enil

  inductive eval_simple_list'
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ge : genv) (e : env) (m : mem) :
    exprlist → List val → Prop where
    | esrl'_nil :
        eval_simple_list'
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m .Enil []
    | esrl'_cons {r rl v vl} :
        eval_simple_rvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m r v →
        eval_simple_list'
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m rl vl →
        eval_simple_list'
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m (.Econs r rl) (v :: vl)

export eval_simple_list' (esrl'_nil esrl'_cons)

def exprlist_app : exprlist → exprlist → exprlist
  | .Enil, rl2 => rl2
  | .Econs r rl1, rl2 => .Econs r (exprlist_app rl1 rl2)

inductive contextlist' : (exprlist → expr) → Prop where
  | contextlist'_call {r1 rl0 ty C} :
      context .RV .RV C →
      contextlist' (fun rl => C (.Ecall r1 (exprlist_app rl0 rl) ty))
  | contextlist'_builtin {ef tyargs rl0 ty C} :
      context .RV .RV C →
      contextlist' (fun rl => C (.Ebuiltin ef tyargs (exprlist_app rl0 rl) ty))

def contextlist'_call
    (r1 : expr) (rl0 : exprlist) (ty : type) (C : expr → expr)
    (hcontext : context .RV .RV C) :
    contextlist' (fun rl => C (.Ecall r1 (exprlist_app rl0 rl) ty)) :=
  contextlist'.contextlist'_call hcontext

def contextlist'_builtin
    (ef : external_function) (tyargs : List type) (rl0 : exprlist) (ty : type)
    (C : expr → expr) (hcontext : context .RV .RV C) :
    contextlist' (fun rl => C (.Ebuiltin ef tyargs (exprlist_app rl0 rl) ty)) :=
  contextlist'.contextlist'_builtin hcontext

def simple_side_effect : expr → Prop
  | .Evalof l _ => simple l = true ∧ type_is_volatile (typeof l) = true
  | .Eseqand r1 _ _ => simple r1 = true
  | .Eseqor r1 _ _ => simple r1 = true
  | .Econdition r1 _ _ _ => simple r1 = true
  | .Eassign l r _ => simple l = true ∧ simple r = true
  | .Eassignop _ l r _ _ => simple l = true ∧ simple r = true
  | .Epostincr _ l _ => simple l = true
  | .Ecomma r1 _ _ => simple r1 = true
  | .Ecall r rl _ => simple r = true ∧ simplelist rl = true
  | .Ebuiltin _ _ rl _ => simplelist rl = true
  | .Eparen r _ _ => simple r = true
  | _ => False

def semantics
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (p : program) :
    CompCert4Lean.Common.Smallstep.semantics :=
  { state := state
    genvtype := genv
    step := step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi
    initial_state := Csem.initial_state p
    final_state := Csem.final_state
    globalenv := Csem.globalenv p
    symbolenv := Genv.to_senv (Csem.globalenv p).genv_genv }

/-! ## Exact statement descriptors for later proof migration -/

def leftcontext_contextStatement : Prop :=
  ∀ k1 k2 C, leftcontext k1 k2 C → context k1 k2 C

def context_composeStatement : Prop :=
  ∀ k2 k3 C2, context k2 k3 C2 →
    ∀ k1 C1, context k1 k2 C1 →
      context k1 k3 (fun x => C2 (C1 x))

def safe_stepsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) s s',
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge s →
    star (Csem.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi) ge s E0 s' →
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge s'

def safe_imm_safeStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) f C a k e m K,
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C a) k e m) →
    context K .RV C →
    imm_safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge e K a m

def lred_kindStatement : Prop :=
  ∀ (ge : genv) e a m a' m',
    lred ge e a m a' m' → expr_kind a = .LV

def rred_kindStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) a m t a' m',
    rred
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge a m t a' m' →
    expr_kind a = .RV

def callred_kindStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) a m fd args ty,
    callred
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge a m fd args ty →
    expr_kind a = .RV

def context_kindStatement : Prop :=
  ∀ a fromKind to C, context fromKind to C →
    expr_kind a = fromKind → expr_kind (C a) = to

def imm_safe_kindStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) e k a m,
    imm_safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge e k a m →
    expr_kind a = k

def safe_expr_kindStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) fromKind C f a k e m,
    context fromKind .RV C →
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C a) k e m) →
    expr_kind a = fromKind

def lred_invertStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (e : env) l m l' m',
    lred ge e l m l' m' →
    invert_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge e l m

def rred_invertStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (e : env) r m t r' m',
    rred
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge r m t r' m' →
    invert_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge e r m

def callred_invertStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (e : env) r fd args ty m,
    callred
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge r m fd args ty →
    invert_expr_prop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge e r m

def invert_expr_contextStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (e : env),
    (∀ fromKind to C, context fromKind to C →
      ∀ a m,
        invert_expr_prop
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge e a m →
        invert_expr_prop
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge e (C a) m) ∧
    (∀ fromKind C, contextlist fromKind C →
      ∀ a m,
        invert_expr_prop
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge e a m →
        ¬ exprlist_all_values (C a))

def imm_safe_invStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (e : env) k a m,
    imm_safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge e k a m →
    match a with
    | .Eloc _ _ _ _ => True
    | .Eval _ _ => True
    | _ => invert_expr_prop
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge e a m

def safe_invStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (e : env) k C f a K m,
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C a) K e m) →
    context k .RV C →
    match a with
    | .Eloc _ _ _ _ => True
    | .Eval _ _ => True
    | _ => invert_expr_prop
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge e a m

def eval_simple_stepsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem),
    (∀ a v, eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m a v →
      ∀ C, context .RV .RV C →
        star (Csem.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) ge (.ExprState f (C a) k e m) E0
          (.ExprState f (C (.Eval v (typeof a))) k e m)) ∧
    (∀ a b ofs bf, eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m a b ofs bf →
      ∀ C, context .LV .RV C →
        star (Csem.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) ge (.ExprState f (C a) k e m) E0
          (.ExprState f (C (.Eloc b ofs bf (typeof a))) k e m))

def eval_simple_rvalue_stepsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem)
      a v,
    eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m a v →
    ∀ C, context .RV .RV C →
      star (Csem.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi) ge (.ExprState f (C a) k e m) E0
        (.ExprState f (C (.Eval v (typeof a))) k e m)

def eval_simple_lvalue_stepsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem)
      a b ofs bf,
    eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m a b ofs bf →
    ∀ C, context .LV .RV C →
      star (Csem.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi) ge (.ExprState f (C a) k e m) E0
        (.ExprState f (C (.Eloc b ofs bf (typeof a))) k e m)

def eval_simple_rvalue_safeStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem)
      C a v,
    eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m a v →
    context .RV .RV C →
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C a) k e m) →
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Eval v (typeof a))) k e m)

def eval_simple_lvalue_safeStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem)
      C a b ofs bf,
    eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m a b ofs bf →
    context .LV .RV C →
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C a) k e m) →
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ge (.ExprState f (C (.Eloc b ofs bf (typeof a))) k e m)

def simple_can_evalStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem)
      a fromKind C,
    simple a = true →
    context fromKind .RV C →
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C a) k e m) →
    match fromKind with
    | .LV => ∃ b ofs bf, eval_simple_lvalue
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e m a b ofs bf
    | .RV => ∃ v, eval_simple_rvalue
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e m a v

def simple_can_eval_rvalStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem)
      r C,
    simple r = true →
    context .RV .RV C →
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C r) k e m) →
    ∃ v, eval_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m r v ∧
      safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Eval v (typeof r))) k e m)

def simple_can_eval_lvalStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem)
      l C,
    simple l = true →
    context .LV .RV C →
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C l) k e m) →
    ∃ b ofs bf, eval_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m l b ofs bf ∧
      safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge (.ExprState f (C (.Eloc b ofs bf (typeof l))) k e m)

def eval_simple_list_impliesStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (e : env) (m : mem) rl tyl vl,
    eval_simple_list
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m rl tyl vl →
    ∃ vl', Csem.cast_arguments
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) m (rval_list vl' rl) tyl vl ∧
      eval_simple_list'
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e m rl vl'

def can_eval_simple_listStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (e : env) (m : mem) rl vl,
    eval_simple_list'
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m rl vl →
    ∀ tyl vl', Csem.cast_arguments
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) m (rval_list vl rl) tyl vl' →
      eval_simple_list
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e m rl tyl vl'

def exprlist_app_assocStatement : Prop :=
  ∀ rl2 rl3 rl1,
    exprlist_app (exprlist_app rl1 rl2) rl3 =
      exprlist_app rl1 (exprlist_app rl2 rl3)

def exprlist_app_contextStatement : Prop :=
  ∀ rl1 rl2, contextlist .RV (fun x => exprlist_app rl1 (.Econs x rl2))

def contextlist'_headStatement : Prop :=
  ∀ rl C, contextlist' C → context .RV .RV (fun x => C (.Econs x rl))

def contextlist'_tailStatement : Prop :=
  ∀ r1 C, contextlist' C → contextlist' (fun x => C (.Econs r1 x))

def eval_simple_list_stepsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem)
      rl vl,
    eval_simple_list'
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m rl vl →
    ∀ C, contextlist' C →
      star (Csem.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi) ge (.ExprState f (C rl) k e m) E0
        (.ExprState f (C (rval_list vl rl)) k e m)

def simple_list_can_evalStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem)
      rl C,
    simplelist rl = true →
    contextlist' C →
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C rl) k e m) →
    ∃ vl, eval_simple_list'
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ge e m rl vl

def rval_list_all_valuesStatement : Prop :=
  ∀ vl rl, exprlist_all_values (rval_list vl rl)

def decompose_exprStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem),
    (∀ a fromKind C, context fromKind .RV C →
      safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C a) k e m) →
      simple a = true ∨
        ∃ C' a', a = C' a' ∧ simple_side_effect a' ∧ leftcontext .RV fromKind C') ∧
    (∀ rl C, contextlist' C →
      safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge (.ExprState f (C rl) k e m) →
      simplelist rl = true ∨
        ∃ C' a', rl = C' a' ∧ simple_side_effect a' ∧ leftcontextlist .RV C')

def decompose_topexprStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (f : function) (k : cont) (e : env) (m : mem) a,
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f a k e m) →
    simple a = true ∨
      ∃ C a', a = C a' ∧ simple_side_effect a' ∧ leftcontext .RV .RV C

def estep_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) S t S',
    estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge S t S' →
    plus (Csem.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi) ge S t S'

def can_estepStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) f a k e m,
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f a k e m) →
    (match a with | .Eval _ _ => False | _ => True) →
    ∃ t S, estep
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge (.ExprState f a k e m) t S

def step_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) S1 t S2,
    step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge S1 t S2 →
    plus (Csem.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi) ge S1 t S2

def progressStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) S,
    safe
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge S →
    (∃ r, Csem.final_state S r) ∨
    (∃ t S', step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge S t S')

def deref_loc_traceStatement : Prop :=
  ∀ (ge : genv) ty m b ofs bf t v,
    deref_loc ge ty m b ofs bf t v →
    match t with
    | [] => True
    | [_] => True
    | _ => False

def deref_loc_receptiveStatement : Prop :=
  ∀ (ge : genv) ty m b ofs bf ev1 t1 v ev2,
    deref_loc ge ty m b ofs bf (ev1 :: t1) v →
    match_traces (Genv.to_senv ge.genv_genv) [ev1] [ev2] →
    t1 = [] ∧ ∃ v', deref_loc ge ty m b ofs bf [ev2] v'

def assign_loc_traceStatement : Prop :=
  ∀ (ge : genv) ty m b ofs bf t v m' v',
    assign_loc ge ty m b ofs bf v t m' v' →
    match t with
    | [] => True
    | [ev] => output_event ev
    | _ => False

def assign_loc_receptiveStatement : Prop :=
  ∀ (ge : genv) ty m b ofs bf ev1 t1 v m' v' ev2,
    assign_loc ge ty m b ofs bf v (ev1 :: t1) m' v' →
    match_traces (Genv.to_senv ge.genv_genv) [ev1] [ev2] →
    ev1 :: t1 = [ev2]

def semantics_strongly_receptiveStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : program), strongly_receptive
    (semantics
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi p)

def strategy_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : program),
    backward_simulation
      (Csem.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi p)
      (semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi p)

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem

theorem leftcontext_context : leftcontext_contextStatement := by
  unfold leftcontext_contextStatement
  intro k1 k2 C h
  exact leftcontext.rec
    (motive_1 := fun k C _ => context k1 k C)
    (motive_2 := fun C _ => contextlist k1 C)
    (.ctx_top k1)
    (fun _ ih => .deref ih)
    (fun _ ih => .field ih)
    (fun _ ih => .rvalof ih)
    (fun _ ih => .addrof ih)
    (fun _ ih => .unop ih)
    (fun _ ih => .binopLeft ih)
    (fun _ _ ih => .binopRight ih)
    (fun _ ih => .cast ih)
    (fun _ ih => .seqand ih)
    (fun _ ih => .seqor ih)
    (fun _ ih => .condition ih)
    (fun _ ih => .assignLeft ih)
    (fun _ _ ih => .assignRight ih)
    (fun _ ih => .assignopLeft ih)
    (fun _ _ ih => .assignopRight ih)
    (fun _ ih => .postincr ih)
    (fun _ ih => .callLeft ih)
    (fun _ _ ih => .callRight ih)
    (fun _ ih => .builtin ih)
    (fun _ ih => .comma ih)
    (fun _ ih => .paren ih)
    (fun _ ih => .ctx_list_head ih)
    (fun _ _ ih => .ctx_list_tail ih)
    h

theorem context_compose : context_composeStatement := by
  unfold context_composeStatement
  intro k2 k3 C2 h2 k1 C1 h1
  exact context.rec
    (motive_1 := fun k C _ => context k1 k (fun x => C (C1 x)))
    (motive_2 := fun C _ => contextlist k1 (fun x => C (C1 x)))
    h1
    (fun _ ih => .deref ih)
    (fun _ ih => .field ih)
    (fun _ ih => .rvalof ih)
    (fun _ ih => .addrof ih)
    (fun _ ih => .unop ih)
    (fun _ ih => .binopLeft ih)
    (fun _ ih => .binopRight ih)
    (fun _ ih => .cast ih)
    (fun _ ih => .seqand ih)
    (fun _ ih => .seqor ih)
    (fun _ ih => .condition ih)
    (fun _ ih => .assignLeft ih)
    (fun _ ih => .assignRight ih)
    (fun _ ih => .assignopLeft ih)
    (fun _ ih => .assignopRight ih)
    (fun _ ih => .postincr ih)
    (fun _ ih => .callLeft ih)
    (fun _ ih => .callRight ih)
    (fun _ ih => .builtin ih)
    (fun _ ih => .comma ih)
    (fun _ ih => .paren ih)
    (fun _ ih => .ctx_list_head ih)
    (fun _ ih => .ctx_list_tail ih)
    h2

theorem lred_kind : lred_kindStatement := by
  unfold lred_kindStatement
  intro ge e a m a' m' h
  cases h <;> rfl

theorem context_kind : context_kindStatement := by
  unfold context_kindStatement
  intro a fromKind to C h hkind
  cases h
  case ctx_top => exact hkind
  all_goals rfl

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Common.Events

theorem safe_imm_safe
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    safe_imm_safeStatement := by
  unfold safe_imm_safeStatement
  intro xi ge f C a k e m K hs hcontext
  apply Classical.byContradiction
  intro hnot
  have hstuck :
      CompCert4Lean.Cfrontend.Csem.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge
        (.ExprState f (C a) k e m) E0 .Stuckstate := by
    exact Or.inl (CompCert4Lean.Cfrontend.Csem.estep.step_stuck hcontext hnot)
  have hstar :
      CompCert4Lean.Common.Smallstep.star
        (CompCert4Lean.Cfrontend.Csem.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        ge (CompCert4Lean.Cfrontend.Csem.ExprState f (C a) k e m) E0
          CompCert4Lean.Cfrontend.Csem.Stuckstate := by
    exact CompCert4Lean.Common.Smallstep.star_one _ _ _ ge
      (CompCert4Lean.Cfrontend.Csem.ExprState f (C a) k e m) E0
      CompCert4Lean.Cfrontend.Csem.Stuckstate hstuck
  rcases hs CompCert4Lean.Cfrontend.Csem.Stuckstate hstar with ⟨r, hfinal⟩ | ⟨t, s'', hstep⟩
  · cases hfinal
  · rcases hstep with hstep | hstep <;> cases hstep

theorem safe_steps
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    safe_stepsStatement := by
  unfold safe_stepsStatement safe
  intro xi ge s s' hs hstar s'' hstar'
  apply hs s''
  exact CompCert4Lean.Common.Smallstep.star_trans
    (genv := genv) (state := state)
    (step := CompCert4Lean.Cfrontend.Csem.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi)
    (ge := ge) (s1 := s) (t1 := E0) (s2 := s') hstar
    (t2 := E0) (s3 := s'') (t := E0) hstar' rfl

theorem rred_kind
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    rred_kindStatement := by
  unfold rred_kindStatement
  intro xi ge a m t a' m' h
  cases h <;> rfl

theorem callred_kind
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    callred_kindStatement := by
  unfold callred_kindStatement
  intro ge a m fd args ty h
  cases h <;> rfl

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

theorem lred_invert
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    lred_invertStatement := by
  unfold lred_invertStatement
  intro xi ge e l m l' m' h
  cases h with
  | varLocal h => exact ⟨_, Or.inl h⟩
  | varGlobal hlocal hglobal => exact ⟨_, Or.inr ⟨hlocal, hglobal⟩⟩
  | deref => exact ⟨_, _, rfl⟩
  | fieldStruct hcomposite hoffset =>
      exact ⟨_, _, rfl, _, _, _, hcomposite, hoffset⟩
  | fieldUnion hcomposite hoffset =>
      exact ⟨_, _, rfl, _, _, _, hcomposite, hoffset⟩

theorem rred_invert
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    rred_invertStatement := by
  unfold rred_invertStatement
  intro xi ge e r m t r' m' h
  cases h with
  | rvalof hderef => exact ⟨rfl, _, _, hderef⟩
  | addrof => exact rfl
  | unop hsem => exact ⟨_, hsem⟩
  | binop hsem => exact ⟨_, hsem⟩
  | cast hsem => exact ⟨_, hsem⟩
  | red_seqand_true hbool => exact ⟨_, hbool⟩
  | red_seqand_false hbool => exact ⟨_, hbool⟩
  | red_seqor_true hbool => exact ⟨_, hbool⟩
  | red_seqor_false hbool => exact ⟨_, hbool⟩
  | condition hbool => exact ⟨_, hbool⟩
  | sizeof => exact trivial
  | alignof => exact trivial
  | assign hcast hassign => exact ⟨_, _, _, _, rfl, hcast, hassign⟩
  | assignop hderef => exact ⟨_, _, rfl, hderef⟩
  | postincr hderef hop => exact ⟨_, _, rfl, hderef⟩
  | comma htype => exact htype
  | paren hcast => exact ⟨_, hcast⟩
  | builtin hargs hexternal =>
      intro _
      exact ⟨_, _, _, _, hargs, hexternal⟩

theorem imm_safe_kind
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    imm_safe_kindStatement := by
  unfold imm_safe_kindStatement
  intro xi ge e k a m h
  cases h with
  | value => rfl
  | location => rfl
  | localRed hred hcontext =>
      exact context_kind _ .LV k _ hcontext (lred_kind ge e _ _ _ _ hred)
  | rvalRed hred hcontext =>
      exact context_kind _ .RV k _ hcontext (rred_kind xi ge _ _ _ _ _ hred)
  | callRed hred hcontext =>
      exact context_kind _ .RV k _ hcontext (callred_kind ge _ _ _ _ _ hred)

theorem safe_expr_kind
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    safe_expr_kindStatement := by
  unfold safe_expr_kindStatement
  intro xi ge fromKind C f a k e m hcontext hs
  apply imm_safe_kind
  exact safe_imm_safe (xi := xi) (ge := ge) (f := f) (C := C) (a := a)
    (k := k) (e := e) (m := m) (K := fromKind) hs hcontext

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

theorem callred_invert
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    callred_invertStatement := by
  unfold callred_invertStatement
  intro xi ge e r fd args ty m h
  cases h with
  | call hfind hcast htype hclass =>
      intro _
      exact ⟨_, _, _, _, _, hclass, hfind, hcast, htype⟩

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Events
open CompCert4Lean.Cfrontend.Csyntax

theorem eval_simple_rvalue_steps
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_simple_rvalue_stepsStatement := by
  unfold eval_simple_rvalue_stepsStatement
  intro xi ge f k e m a v h
  exact eval_simple_rvalue.rec
    (motive_1 := fun a b ofs bf _ =>
      ∀ C, context .LV .RV C →
        star (Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) ge
          (.ExprState f (C a) k e m) E0
          (.ExprState f (C (.Eloc b ofs bf (typeof a))) k e m))
    (motive_2 := fun a v _ =>
      ∀ C, context .RV .RV C →
        star (Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) ge
          (.ExprState f (C a) k e m) E0
          (.ExprState f (C (.Eval v (typeof a))) k e m))
    (fun C _ => star_refl _ ge _)
    (fun hlocal => fun C hC =>
      star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_lred
        (Csem.lred.varLocal hlocal) hC)))
    (fun hlocal hglobal => fun C hC =>
      star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_lred
        (Csem.lred.varGlobal hlocal hglobal) hC)))
    (fun hr ih => fun C hC =>
      star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        (ih (fun x => C (.Ederef x _))
          (context_compose .LV .RV C hC .RV (fun x => .Ederef x _)
            (.deref (.ctx_top .RV))))
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_lred
          Csem.lred.deref hC))) rfl)
    (fun {r f ty b ofs id co a delta bf} hr htype hco hoff ih => fun C hC => by
      have hih := ih (fun x => C (.Efield x f ty))
        (context_compose .LV .RV C hC .RV (fun x => .Efield x f ty)
          (.field (f := f) (ty := ty) (.ctx_top .RV)))
      rw [htype] at hih
      exact star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        hih
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_lred
          (Csem.lred.fieldStruct hco hoff) hC))) rfl)
    (fun {r f ty b ofs id co a delta bf} hr htype hoff hco ih => fun C hC => by
      have hih := ih (fun x => C (.Efield x f ty))
        (context_compose .LV .RV C hC .RV (fun x => .Efield x f ty)
          (.field (f := f) (ty := ty) (.ctx_top .RV)))
      rw [htype] at hih
      exact star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        hih
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_lred
          (Csem.lred.fieldUnion hco hoff) hC))) rfl)
    (fun C _ => star_refl _ ge _)
    (fun {b ofs bf l ty v} hl htype hvolatile hderef ih => fun C hC => by
      rw [htype] at hderef
      rw [htype]
      exact star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        (ih (fun x => C (.Evalof x _))
          (context_compose .RV .RV C hC .LV (fun x => .Evalof x _)
            (.rvalof (.ctx_top .LV))))
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_rred
          (Csem.rred.rvalof hderef) hC))) rfl)
    (fun _ ih => fun C hC =>
      star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        (ih (fun x => C (.Eaddrof x _))
          (context_compose .RV .RV C hC .LV (fun x => .Eaddrof x _)
            (.addrof (.ctx_top .LV))))
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_rred
          Csem.rred.addrof hC))) rfl)
    (fun _ hop ih => fun C hC =>
      star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        (ih (fun x => C (.Eunop _ x _))
          (context_compose .RV .RV C hC .RV (fun x => .Eunop _ x _)
            (.unop (.ctx_top .RV))))
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_rred
          (Csem.rred.unop hop) hC))) rfl)
    (fun _ _ hbin ih1 ih2 => fun C hC =>
      star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        (star_trans (genv := genv) (state := state)
          (step := Csem.step (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi)
          (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
          (ih1 (fun x => C (.Ebinop _ x _ _))
            (context_compose .RV .RV C hC .RV (fun x => .Ebinop _ x _ _)
              (.binopLeft (.ctx_top .RV))))
          (t2 := E0) (s3 := _) (t := E0)
          (ih2 (fun x => C (.Ebinop _ (.Eval _ _) x _))
            (context_compose .RV .RV C hC .RV
              (fun x => .Ebinop _ (.Eval _ _) x _)
              (.binopRight (.ctx_top .RV)))) rfl)
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_rred
          (Csem.rred.binop hbin) hC))) rfl)
    (fun _ hcast ih => fun C hC =>
      star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        (ih (fun x => C (.Ecast x _))
          (context_compose .RV .RV C hC .RV (fun x => .Ecast x _)
            (.cast (.ctx_top .RV))))
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_rred
          (Csem.rred.cast hcast) hC))) rfl)
    (fun C hC =>
      star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_rred
        Csem.rred.sizeof hC)))
    (fun C hC =>
      star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_rred
        Csem.rred.alignof hC)))
    h

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Common.Events
open CompCert4Lean.Cfrontend.Csyntax

theorem eval_simple_rvalue_safe
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_simple_rvalue_safeStatement := by
  unfold eval_simple_rvalue_safeStatement
  intro xi ge f k e m C a v h hC hs
  exact safe_steps (xi := xi) (ge := ge)
    (s := .ExprState f (C a) k e m)
    (s' := .ExprState f (C (.Eval v (typeof a))) k e m)
    hs (eval_simple_rvalue_steps xi ge f k e m a v h C hC)

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Events
open CompCert4Lean.Cfrontend.Csyntax

theorem eval_simple_lvalue_steps
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_simple_lvalue_stepsStatement := by
  unfold eval_simple_lvalue_stepsStatement
  intro xi ge f k e m a b ofs bf h
  have hrsteps : ∀ {a v}, eval_simple_rvalue ge e m a v →
      ∀ C, context .RV .RV C →
        star (Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) ge
          (.ExprState f (C a) k e m) E0
          (.ExprState f (C (.Eval v (typeof a))) k e m) := by
    intro a v h
    exact eval_simple_rvalue_steps xi ge f k e m a v h
  exact eval_simple_lvalue.rec
    (motive_1 := fun a b ofs bf _ =>
      ∀ C, context .LV .RV C →
        star (Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) ge
          (.ExprState f (C a) k e m) E0
          (.ExprState f (C (.Eloc b ofs bf (typeof a))) k e m))
    (motive_2 := fun a v _ =>
      ∀ C, context .RV .RV C →
        star (Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) ge
          (.ExprState f (C a) k e m) E0
          (.ExprState f (C (.Eval v (typeof a))) k e m))
    (fun C _ => star_refl _ ge _)
    (fun hlocal => fun C hC =>
      star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_lred
        (Csem.lred.varLocal hlocal) hC)))
    (fun hlocal hglobal => fun C hC =>
      star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_lred
        (Csem.lred.varGlobal hlocal hglobal) hC)))
    (fun hr ihr => fun C hC =>
      star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        (ihr (fun x => C (.Ederef x _))
          (context_compose .LV .RV C hC .RV (fun x => .Ederef x _)
            (.deref (.ctx_top .RV))))
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_lred
          Csem.lred.deref hC))) rfl)
    (fun {r f ty b ofs id co a delta bf} hr htype hco hoff ihr => fun C hC => by
      have hih := ihr (fun x => C (.Efield x f ty))
        (context_compose .LV .RV C hC .RV (fun x => .Efield x f ty)
          (.field (f := f) (ty := ty) (.ctx_top .RV)))
      rw [htype] at hih
      exact star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        hih
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_lred
          (Csem.lred.fieldStruct hco hoff) hC))) rfl)
    (fun {r f ty b ofs id co a delta bf} hr htype hoff hco ihr => fun C hC => by
      have hih := ihr (fun x => C (.Efield x f ty))
        (context_compose .LV .RV C hC .RV (fun x => .Efield x f ty)
          (.field (f := f) (ty := ty) (.ctx_top .RV)))
      rw [htype] at hih
      exact star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        hih
        (t2 := E0) (s3 := _) (t := E0)
        (star_one _ _ _ ge _ E0 _ (Or.inl (Csem.estep.step_lred
          (Csem.lred.fieldUnion hco hoff) hC))) rfl)
    (fun {v ty} => hrsteps (eval_simple_rvalue.esr_val))
    (fun {b ofs bf l ty v} hl htype hvolatile hderef ih =>
      hrsteps (eval_simple_rvalue.esr_rvalof hl htype hvolatile hderef))
    (fun {b ofs l ty} hl ih =>
      hrsteps (eval_simple_rvalue.esr_addrof hl))
    (fun {op r1 ty v1 v} hr hop ih =>
      hrsteps (eval_simple_rvalue.esr_unop hr hop))
    (fun {op r1 r2 ty v1 v2 v} hr1 hr2 hbin ih1 ih2 =>
      hrsteps (eval_simple_rvalue.esr_binop hr1 hr2 hbin))
    (fun {ty r1 v1 v} hr hcast ih =>
      hrsteps (eval_simple_rvalue.esr_cast hr hcast))
    (fun {ty1 ty} => hrsteps (eval_simple_rvalue.esr_sizeof))
    (fun {ty1 ty} => hrsteps (eval_simple_rvalue.esr_alignof))
    h

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Events
open CompCert4Lean.Cfrontend.Csyntax

theorem eval_simple_lvalue_safe
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_simple_lvalue_safeStatement := by
  unfold eval_simple_lvalue_safeStatement
  intro xi ge f k e m C a b ofs bf h hC hs
  exact safe_steps (xi := xi) (ge := ge)
    (s := .ExprState f (C a) k e m)
    (s' := .ExprState f (C (.Eloc b ofs bf (typeof a))) k e m)
    hs (eval_simple_lvalue_steps xi ge f k e m a b ofs bf h C hC)

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem

theorem exprlist_app_assoc : exprlist_app_assocStatement := by
  unfold exprlist_app_assocStatement
  intro rl2 rl3 rl1
  refine CompCert4Lean.Cfrontend.Csyntax.exprlist.rec
    (motive_1 := fun _ => True)
    (motive_2 := fun rl1 =>
      exprlist_app (exprlist_app rl1 rl2) rl3 =
        exprlist_app rl1 (exprlist_app rl2 rl3))
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by rfl)
    (by intros r rl hr ih; simp [exprlist_app, ih])
    rl1

theorem exprlist_app_context : exprlist_app_contextStatement := by
  unfold exprlist_app_contextStatement
  intro rl1 rl2
  refine CompCert4Lean.Cfrontend.Csyntax.exprlist.rec
    (motive_1 := fun _ => True)
    (motive_2 := fun rl1 =>
      contextlist .RV (fun x => exprlist_app rl1 (.Econs x rl2)))
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by simpa only [exprlist_app] using
      (CompCert4Lean.Cfrontend.Csem.ctx_list_head
        (k := .RV) (C := fun x => x) (el := rl2)
        (CompCert4Lean.Cfrontend.Csem.ctx_top .RV)))
    (by intros r rl hr ih; simpa only [exprlist_app] using
      (CompCert4Lean.Cfrontend.Csem.ctx_list_tail (e1 := r) ih))
    rl1

theorem eval_simple_list_implies
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_simple_list_impliesStatement := by
  unfold eval_simple_list_impliesStatement
  intro ge e m rl tyl vl h
  induction h with
  | esrl_nil =>
      exact ⟨[], .nil, .esrl'_nil⟩
  | @esrl_cons r rl ty tyl v vl v' hr hcast htail ih =>
      rcases ih with ⟨vl', hargs, hsimple⟩
      exact ⟨v' :: vl', .cons hcast hargs, .esrl'_cons hr hsimple⟩

theorem can_eval_simple_list
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    can_eval_simple_listStatement := by
  unfold can_eval_simple_listStatement
  intro ge e m rl vl h
  induction h with
  | esrl'_nil =>
      intro tyl vl' hcast
      cases hcast
      exact .esrl_nil
  | esrl'_cons hr htail ih =>
      intro tyl vl' hcast
      cases hcast with
      | cons hhead htailcast =>
          exact .esrl_cons hr hhead (ih _ _ htailcast)

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem

theorem contextlist'_head : contextlist'_headStatement := by
  unfold contextlist'_headStatement
  intro rl C h
  cases h with
  | @contextlist'_call r1 rl0 ty C0 hcontext =>
      have hargs : contextlist .RV (fun x => exprlist_app rl0 (.Econs x rl)) := by
        exact exprlist_app_context rl0 rl
      have hcall : context .RV .RV
          (fun x => .Ecall r1 (exprlist_app rl0 (.Econs x rl)) ty) :=
        .callRight hargs
      exact context_compose .RV .RV C0 hcontext .RV _ hcall
  | @contextlist'_builtin ef tyargs rl0 ty C0 hcontext =>
      have hargs : contextlist .RV (fun x => exprlist_app rl0 (.Econs x rl)) := by
        exact exprlist_app_context rl0 rl
      have hcall : context .RV .RV
          (fun x => .Ebuiltin ef tyargs (exprlist_app rl0 (.Econs x rl)) ty) :=
        .builtin hargs
      exact context_compose .RV .RV C0 hcontext .RV _ hcall

theorem contextlist'_tail : contextlist'_tailStatement := by
  unfold contextlist'_tailStatement
  intro r1 C h
  cases h with
  | @contextlist'_call r0 rl0 ty C0 hcontext =>
      have happ : (fun x => C0 (.Ecall r0 (exprlist_app rl0 (.Econs r1 x)) ty)) =
          (fun x => C0 (.Ecall r0
            (exprlist_app (exprlist_app rl0 (.Econs r1 .Enil)) x) ty)) := by
        funext x
        congr 2
        simpa only [exprlist_app] using
          (exprlist_app_assoc (.Econs r1 .Enil) x rl0).symm
      rw [happ]
      exact .contextlist'_call hcontext
  | @contextlist'_builtin ef tyargs rl0 ty C0 hcontext =>
      have happ : (fun x => C0 (.Ebuiltin ef tyargs (exprlist_app rl0 (.Econs r1 x)) ty)) =
          (fun x => C0 (.Ebuiltin ef tyargs
            (exprlist_app (exprlist_app rl0 (.Econs r1 .Enil)) x) ty)) := by
        funext x
        congr 2
        simpa only [exprlist_app] using
          (exprlist_app_assoc (.Econs r1 .Enil) x rl0).symm
      rw [happ]
      exact .contextlist'_builtin hcontext

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Events
open CompCert4Lean.Cfrontend.Csyntax

theorem eval_simple_list_steps
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_simple_list_stepsStatement := by
  unfold eval_simple_list_stepsStatement
  intro xi ge f k e m rl vl h
  induction h with
  | esrl'_nil =>
      intro C hC
      exact star_refl _ ge _
  | @esrl'_cons r rl v vl hr htail ih =>
      intro C hC
      exact star_trans (genv := genv) (state := state)
        (step := Csem.step (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        (ge := ge) (s1 := _) (t1 := E0) (s2 := _)
        (eval_simple_rvalue_steps xi ge f k e m r v hr
          (fun x => C (.Econs x rl)) (contextlist'_head rl C hC))
        (t2 := E0) (s3 := _) (t := E0)
        (ih (fun x => C (.Econs (.Eval v (typeof r)) x))
          (contextlist'_tail (.Eval v (typeof r)) C hC)) rfl

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

theorem rval_list_all_values : rval_list_all_valuesStatement := by
  unfold rval_list_all_valuesStatement
  intro vl
  induction vl with
  | nil =>
      intro rl
      cases rl <;> simp [rval_list, exprlist_all_values]
  | cons v vl ih =>
      intro rl
      cases rl with
      | Enil => simp [rval_list, exprlist_all_values]
      | Econs r rl =>
          simpa [rval_list, exprlist_all_values] using ih rl

end CompCert4Lean.Cfrontend.Cstrategy
namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Events
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Ctypes

private theorem decompose_expr_aux
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    decompose_exprStatement := by
  unfold decompose_exprStatement
  intro xi ge f k e m
  have hexpr : ∀ a : expr,
      ∀ fromKind C, context fromKind .RV C →
        safe (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge
          (.ExprState f (C a) k e m) →
        simple a = true ∨
          ∃ C' a', a = C' a' ∧ simple_side_effect a' ∧
            leftcontext .RV fromKind C' := by
    intro a
    induction a using expr.rec
      (motive_2 := fun rl =>
        ∀ C, contextlist' C →
          safe (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi ge
            (.ExprState f (C rl) k e m) →
          simplelist rl = true ∨
            ∃ C' a', rl = C' a' ∧ simple_side_effect a' ∧
              leftcontextlist .RV C') with
    | Eval v ty =>
        intro fromKind C hcontext hs
        exact Or.inl rfl
    | Evar x ty =>
        intro fromKind C hcontext hs
        exact Or.inl rfl
    | Eloc b ofs bf ty =>
        intro fromKind C hcontext hs
        exact Or.inl rfl
    | Esizeof ty1 ty =>
        intro fromKind C hcontext hs
        exact Or.inl rfl
    | Ealignof ty1 ty =>
        intro fromKind C hcontext hs
        exact Or.inl rfl
    | Efield l fld ty ih =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Efield l fld ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .RV .RV (fun x => C (.Efield x fld ty)) := by
          exact context_compose .LV .RV C hcontext .RV _ (.field (.ctx_top .RV))
        rcases ih .RV (fun x => C (.Efield x fld ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inl (by simpa [simple] using hsimple)
        · exact Or.inr ⟨fun x => (.Efield (C' x) fld ty), a', rfl, hse,
            .lctx_field hleft⟩
    | Ederef r ty ih =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Ederef r ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .RV .RV (fun x => C (.Ederef x ty)) := by
          exact context_compose .LV .RV C hcontext .RV _ (.deref (.ctx_top .RV))
        rcases ih .RV (fun x => C (.Ederef x ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inl (by simpa [simple] using hsimple)
        · exact Or.inr ⟨fun x => (.Ederef (C' x) ty), a', rfl, hse,
            .lctx_deref hleft⟩
    | Evalof l ty ih =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Evalof l ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .LV .RV (fun x => C (.Evalof x ty)) := by
          exact context_compose .RV .RV C hcontext .LV _ (.rvalof (.ctx_top .LV))
        rcases ih .LV (fun x => C (.Evalof x ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · by_cases hv : type_is_volatile (typeof l) = true
          · exact Or.inr ⟨id, .Evalof l ty, rfl, ⟨hsimple, hv⟩, .lctx_top .RV⟩
          · exact Or.inl (by simpa [simple, hv] using hsimple)
        · exact Or.inr ⟨fun x => (.Evalof (C' x) ty), a', rfl, hse,
            .lctx_rvalof hleft⟩
    | Eaddrof l ty ih =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Eaddrof l ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .LV .RV (fun x => C (.Eaddrof x ty)) := by
          exact context_compose .RV .RV C hcontext .LV _ (.addrof (.ctx_top .LV))
        rcases ih .LV (fun x => C (.Eaddrof x ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inl (by simpa [simple] using hsimple)
        · exact Or.inr ⟨fun x => (.Eaddrof (C' x) ty), a', rfl, hse,
            .lctx_addrof hleft⟩
    | Eunop op r ty ih =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Eunop op r ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .RV .RV (fun x => C (.Eunop op x ty)) := by
          exact context_compose .RV .RV C hcontext .RV _ (.unop (.ctx_top .RV))
        rcases ih .RV (fun x => C (.Eunop op x ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inl (by simpa [simple] using hsimple)
        · exact Or.inr ⟨fun x => (.Eunop op (C' x) ty), a', rfl, hse,
            .lctx_unop hleft⟩
    | Ebinop op r1 r2 ty ih1 ih2 =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Ebinop op r1 r2 ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx1 : context .RV .RV (fun x => C (.Ebinop op x r2 ty)) := by
          exact context_compose .RV .RV C hcontext .RV _ (.binopLeft (.ctx_top .RV))
        rcases ih1 .RV (fun x => C (.Ebinop op x r2 ty)) hctx1 hs with hsimple1 | ⟨C', a', rfl, hse, hleft⟩
        · have hctx2 : context .RV .RV (fun x => C (.Ebinop op r1 x ty)) := by
            exact context_compose .RV .RV C hcontext .RV _
              (.binopRight (.ctx_top .RV))
          rcases ih2 .RV (fun x => C (.Ebinop op r1 x ty)) hctx2 hs with hsimple2 | ⟨C'', a'', rfl, hse2, hleft2⟩
          · exact Or.inl (by simpa [simple, hsimple1, hsimple2])
          · exact Or.inr ⟨fun x => (.Ebinop op r1 (C'' x) ty), a'', rfl, hse2,
              .lctx_binop_right hsimple1 hleft2⟩
        · exact Or.inr ⟨fun x => (.Ebinop op (C' x) r2 ty), a', rfl, hse,
            .lctx_binop_left hleft⟩
    | Ecast r ty ih =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Ecast r ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .RV .RV (fun x => C (.Ecast x ty)) := by
          exact context_compose .RV .RV C hcontext .RV _ (.cast (.ctx_top .RV))
        rcases ih .RV (fun x => C (.Ecast x ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inl (by simpa [simple] using hsimple)
        · exact Or.inr ⟨fun x => (.Ecast (C' x) ty), a', rfl, hse,
            .lctx_cast hleft⟩
    | Eseqand r1 r2 ty ih1 ih2 =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Eseqand r1 r2 ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .RV .RV (fun x => C (.Eseqand x r2 ty)) := by
          exact context_compose .RV .RV C hcontext .RV _ (.seqand (.ctx_top .RV))
        rcases ih1 .RV (fun x => C (.Eseqand x r2 ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inr ⟨fun x => x, (.Eseqand r1 r2 ty),
            rfl, hsimple, .lctx_top .RV⟩
        · exact Or.inr ⟨fun x => (.Eseqand (C' x) r2 ty), a', rfl, hse,
            .lctx_seqand hleft⟩
    | Eseqor r1 r2 ty ih1 ih2 =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Eseqor r1 r2 ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .RV .RV (fun x => C (.Eseqor x r2 ty)) := by
          exact context_compose .RV .RV C hcontext .RV _ (.seqor (.ctx_top .RV))
        rcases ih1 .RV (fun x => C (.Eseqor x r2 ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inr ⟨fun x => x, (.Eseqor r1 r2 ty),
            rfl, hsimple, .lctx_top .RV⟩
        · exact Or.inr ⟨fun x => (.Eseqor (C' x) r2 ty), a', rfl, hse,
            .lctx_seqor hleft⟩
    | Econdition r1 r2 r3 ty ih1 ih2 ih3 =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Econdition r1 r2 r3 ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .RV .RV (fun x => C (.Econdition x r2 r3 ty)) := by
          exact context_compose .RV .RV C hcontext .RV _ (.condition (.ctx_top .RV))
        rcases ih1 .RV (fun x => C (.Econdition x r2 r3 ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inr ⟨fun x => x, (.Econdition r1 r2 r3 ty),
            rfl, hsimple, .lctx_top .RV⟩
        · exact Or.inr ⟨fun x => (.Econdition (C' x) r2 r3 ty), a', rfl, hse,
            .lctx_condition hleft⟩
    | Eassign l r ty ihl ihr =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Eassign l r ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctxl : context .LV .RV (fun x => C (.Eassign x r ty)) := by
          exact context_compose .RV .RV C hcontext .LV _ (.assignLeft (.ctx_top .LV))
        rcases ihl .LV (fun x => C (.Eassign x r ty)) hctxl hs with hsimplel | ⟨C', a', rfl, hsel, hleftl⟩
        · have hctxr : context .RV .RV (fun x => C (.Eassign l x ty)) := by
            exact context_compose .RV .RV C hcontext .RV _
              (.assignRight (.ctx_top .RV))
          rcases ihr .RV (fun x => C (.Eassign l x ty)) hctxr hs with hsimpler | ⟨C'', a'', rfl, hser, hleftr⟩
          · exact Or.inr ⟨fun x => x, (.Eassign l r ty), rfl,
              ⟨hsimplel, hsimpler⟩, .lctx_top .RV⟩
          · exact Or.inr ⟨fun x => (.Eassign l (C'' x) ty), a'', rfl, hser,
              .lctx_assign_right hsimplel hleftr⟩
        · exact Or.inr ⟨fun x => (.Eassign (C' x) r ty), a', rfl, hsel,
            .lctx_assign_left hleftl⟩
    | Eassignop op l r tyres ty ihl ihr =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Eassignop op l r tyres ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctxl : context .LV .RV (fun x => C (.Eassignop op x r tyres ty)) := by
          exact context_compose .RV .RV C hcontext .LV _ (.assignopLeft (.ctx_top .LV))
        rcases ihl .LV (fun x => C (.Eassignop op x r tyres ty)) hctxl hs with hsimplel | ⟨C', a', rfl, hsel, hleftl⟩
        · have hctxr : context .RV .RV (fun x => C (.Eassignop op l x tyres ty)) := by
            exact context_compose .RV .RV C hcontext .RV _
              (.assignopRight (.ctx_top .RV))
          rcases ihr .RV (fun x => C (.Eassignop op l x tyres ty)) hctxr hs with hsimpler | ⟨C'', a'', rfl, hser, hleftr⟩
          · exact Or.inr ⟨fun x => x, (.Eassignop op l r tyres ty), rfl,
              ⟨hsimplel, hsimpler⟩, .lctx_top .RV⟩
          · exact Or.inr ⟨fun x => (.Eassignop op l (C'' x) tyres ty), a'', rfl, hser,
              .lctx_assignop_right hsimplel hleftr⟩
        · exact Or.inr ⟨fun x => (.Eassignop op (C' x) r tyres ty), a', rfl, hsel,
            .lctx_assignop_left hleftl⟩
    | Epostincr id l ty ih =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Epostincr id l ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .LV .RV (fun x => C (.Epostincr id x ty)) := by
          exact context_compose .RV .RV C hcontext .LV _ (.postincr (.ctx_top .LV))
        rcases ih .LV (fun x => C (.Epostincr id x ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inr ⟨fun x => x, (.Epostincr id l ty),
            rfl, hsimple, .lctx_top .RV⟩
        · exact Or.inr ⟨fun x => (.Epostincr id (C' x) ty), a', rfl, hse,
            .lctx_postincr hleft⟩
    | Ecomma r1 r2 ty ih1 ih2 =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Ecomma r1 r2 ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .RV .RV (fun x => C (.Ecomma x r2 ty)) := by
          exact context_compose .RV .RV C hcontext .RV _ (.comma (.ctx_top .RV))
        rcases ih1 .RV (fun x => C (.Ecomma x r2 ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inr ⟨fun x => x, (.Ecomma r1 r2 ty),
            rfl, hsimple, .lctx_top .RV⟩
        · exact Or.inr ⟨fun x => (.Ecomma (C' x) r2 ty), a', rfl, hse,
            .lctx_comma hleft⟩
    | Ecall r rargs ty ihr ihrargs =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Ecall r rargs ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctxr : context .RV .RV (fun x => C (.Ecall x rargs ty)) := by
          exact context_compose .RV .RV C hcontext .RV _ (.callLeft (.ctx_top .RV))
        rcases ihr .RV (fun x => C (.Ecall x rargs ty)) hctxr hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · have hctxargs : contextlist' (fun x => C (.Ecall r x ty)) := by
            exact contextlist'_call r .Enil ty C hcontext
          rcases ihrargs (fun x => C (.Ecall r x ty)) hctxargs hs with hsimpleargs | ⟨C'', a'', rfl, hseargs, hleftargs⟩
          · exact Or.inr ⟨fun x => x, (.Ecall r rargs ty), rfl,
              ⟨hsimple, hsimpleargs⟩, .lctx_top .RV⟩
          · exact Or.inr ⟨fun x => (.Ecall r (C'' x) ty), a'', rfl, hseargs,
              .lctx_call_right hsimple hleftargs⟩
        · exact Or.inr ⟨fun x => (.Ecall (C' x) rargs ty), a', rfl, hse,
            .lctx_call_left hleft⟩
    | Ebuiltin ef tyargs rargs ty ihrargs =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Ebuiltin ef tyargs rargs ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctxargs : contextlist' (fun x => C (.Ebuiltin ef tyargs x ty)) := by
          exact contextlist'_builtin ef tyargs .Enil ty C hcontext
        rcases ihrargs (fun x => C (.Ebuiltin ef tyargs x ty)) hctxargs hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inr ⟨fun x => x, (.Ebuiltin ef tyargs rargs ty), rfl,
            hsimple, .lctx_top .RV⟩
        · exact Or.inr ⟨fun x => (.Ebuiltin ef tyargs (C' x) ty), a', rfl, hse,
            .lctx_builtin hleft⟩
    | Eparen r tycast ty ih =>
        intro fromKind C hcontext hs
        have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge fromKind
          C f (.Eparen r tycast ty) k e m
          hcontext hs
        rw [← hkind] at hcontext ⊢
        have hctx : context .RV .RV (fun x => C (.Eparen x tycast ty)) := by
          exact context_compose .RV .RV C hcontext .RV _ (.paren (.ctx_top .RV))
        rcases ih .RV (fun x => C (.Eparen x tycast ty)) hctx hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · exact Or.inr ⟨fun x => x, (.Eparen r tycast ty),
            rfl, hsimple, .lctx_top .RV⟩
        · exact Or.inr ⟨fun x => (.Eparen (C' x) tycast ty), a', rfl, hse,
            .lctx_paren hleft⟩
    | Enil C hcontext hs =>
        exact Or.inl rfl
    | Econs r rl ihr ihrl C hcontext hs =>
        have hctxr : context .RV .RV (fun x => C (.Econs x rl)) :=
          contextlist'_head rl C hcontext
        rcases ihr .RV (fun x => C (.Econs x rl)) hctxr hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · have hctxrl : contextlist' (fun x => C (.Econs r x)) :=
            contextlist'_tail r C hcontext
          rcases ihrl (fun x => C (.Econs r x)) hctxrl hs with hsimplel | ⟨C'', a'', rfl, hsel, hleftl⟩
          · exact Or.inl (by simpa [simplelist, hsimple])
          · exact Or.inr ⟨fun x => (.Econs r (C'' x)), a'', rfl, hsel,
              .lctx_list_tail hsimple hleftl⟩
        · exact Or.inr ⟨fun x => (.Econs (C' x) rl), a', rfl, hse,
            .lctx_list_head hleft⟩
  have hlist : ∀ rl : exprlist,
      ∀ C, contextlist' C →
        safe (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge
          (.ExprState f (C rl) k e m) →
        simplelist rl = true ∨
          ∃ C' a', rl = C' a' ∧ simple_side_effect a' ∧
            leftcontextlist .RV C' := by
    intro rl
    induction rl using exprlist.rec (motive_1 := fun _ => True) <;> try exact True.intro
    case Enil =>
        intro C hcontext hs
        exact Or.inl rfl
    case Econs r rl ihr ihrl =>
        intro C hcontext hs
        have hctxr : context .RV .RV (fun x => C (.Econs x rl)) :=
          contextlist'_head rl C hcontext
        rcases hexpr r .RV (fun x => C (.Econs x rl)) hctxr hs with hsimple | ⟨C', a', rfl, hse, hleft⟩
        · have hctxrl : contextlist' (fun x => C (.Econs r x)) :=
            contextlist'_tail r C hcontext
          rcases ihrl (fun x => C (.Econs r x)) hctxrl hs with hsimplel | ⟨C'', a'', rfl, hsel, hleftl⟩
          · exact Or.inl (by simpa [simplelist, hsimple])
          · exact Or.inr ⟨fun x => (.Econs r (C'' x)), a'', rfl, hsel,
              .lctx_list_tail hsimple hleftl⟩
        · exact Or.inr ⟨fun x => (.Econs (C' x) rl), a', rfl, hse,
            .lctx_list_head hleft⟩
  exact ⟨hexpr, hlist⟩

theorem decompose_topexpr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    decompose_topexprStatement := by
  unfold decompose_topexprStatement
  intro xi ge f k e m a hs
  have h := decompose_expr_aux (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ge f k e m
  exact h.1 a .RV (fun x => x) (.ctx_top .RV) hs

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem

theorem deref_loc_trace : deref_loc_traceStatement := by
  unfold deref_loc_traceStatement
  intro ge ty m b ofs bf t v h
  cases h with
  | value hmode hvol hload => simp [CompCert4Lean.Common.Events.E0]
  | volatile hmode hvol hload =>
      cases hload <;> simp [CompCert4Lean.Common.Events.trace,
        CompCert4Lean.Common.Events.E0]
  | reference hmode => simp [CompCert4Lean.Common.Events.E0]
  | copy hmode => simp [CompCert4Lean.Common.Events.E0]
  | bitfield hload => simp [CompCert4Lean.Common.Events.E0]

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem

theorem assign_loc_trace : assign_loc_traceStatement := by
  unfold assign_loc_traceStatement
  intro ge ty m b ofs bf t v m' v' h
  cases h with
  | value hmode hvol hstore => simp [CompCert4Lean.Common.Events.E0]
  | volatile hmode hvol hstore =>
      cases hstore <;>
        simp [CompCert4Lean.Common.Events.trace,
          CompCert4Lean.Common.Events.E0,
          CompCert4Lean.Common.Events.output_event]
  | copy hmode halign' halign hdisj hload hstore =>
      simp [CompCert4Lean.Common.Events.E0]
  | bitfield hstore => simp [CompCert4Lean.Common.Events.E0]

theorem deref_loc_receptive : deref_loc_receptiveStatement := by
  unfold deref_loc_receptiveStatement
  intro ge ty m b ofs bf ev1 t1 v ev2 h hm
  have ht : t1 = [] := by
    have htr := deref_loc_trace ge ty m b ofs bf (ev1 :: t1) v h
    cases t1 with
    | nil => rfl
    | cons ev' tl =>
        cases tl <;> simp at htr
  subst t1
  cases h with
  | volatile hmode hvol hload =>
      rcases CompCert4Lean.Common.Events.volatile_load_receptive
        (CompCert4Lean.Common.Globalenvs.Genv.to_senv ge.genv_genv)
        _ _ _ _ _ _ _ hload hm with ⟨v', hv⟩
      exact ⟨rfl, ⟨v', .volatile hmode hvol hv⟩⟩

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem

theorem assign_loc_receptive : assign_loc_receptiveStatement := by
  unfold assign_loc_receptiveStatement
  intro ge ty m b ofs bf ev1 t1 v m' v' ev2 h hm
  have ht : t1 = [] := by
    have htr := assign_loc_trace ge ty m b ofs bf (ev1 :: t1) v m' v' h
    cases t1 with
    | nil => rfl
    | cons ev' tl =>
        cases tl <;> simp at htr
  subst t1
  cases h with
  | volatile hmode hvol hstore =>
      exact CompCert4Lean.Common.Events.volatile_store_receptive
        (CompCert4Lean.Common.Globalenvs.Genv.to_senv ge.genv_genv)
        _ _ _ _ _ _ _ _ hstore hm

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Common.Events
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Common.Events

set_option maxHeartbeats 2000000 in
theorem invert_expr_context
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    invert_expr_contextStatement := by
  unfold invert_expr_contextStatement
  intro xi ge e
  constructor
  · intro fromKind to C hcontext
    exact Csem.context.rec
      (motive_1 := fun k C _ =>
        ∀ a m, invert_expr_prop xi ge e a m → invert_expr_prop xi ge e (C a) m)
      (motive_2 := fun C _ =>
        ∀ a m, invert_expr_prop xi ge e a m → ¬ exprlist_all_values (C a))
      (by intros; assumption)
      (by
        intro C ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C f ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C op ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C op e2 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C op e1 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C r2 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C r2 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C r2 r3 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C e2 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C e1 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C op e2 tyres ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C op e1 tyres ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C id ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C el ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C e1 ty hctx ih a m h
        have hi := ih a m h
        cases he1 : e1 <;> simp only [invert_expr_prop, he1] at hi ⊢ <;>
          try contradiction <;> try assumption <;> try trivial
        case Eval =>
          intro hall
          exact (hi hall).elim)
      (by
        intro C ef tyargs ty hctx ih a m h
        have hi := ih a m h
        intro hall
        exact (hi hall).elim)
      (by
        intro C e2 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C tycast ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp [invert_expr_prop, hca] at hi ⊢)
      (by
        intro C el hctx ih a m h
        have hi := ih a m h
        intro hall
        cases hca : C a <;> simp only [exprlist_all_values, invert_expr_prop, hca] at hall hi ⊢ <;>
          contradiction)
      (by
        intro C e1 hctx ih a m h
        have hi := ih a m h
        intro hall
        cases he1 : e1 <;> simp only [exprlist_all_values, he1] at hall ⊢
        exact hi hall)
      hcontext
  · intro fromKind C hcontext
    exact Csem.contextlist.rec
      (motive_1 := fun k C _ =>
        ∀ a m, invert_expr_prop xi ge e a m → invert_expr_prop xi ge e (C a) m)
      (motive_2 := fun C _ =>
        ∀ a m, invert_expr_prop xi ge e a m → ¬ exprlist_all_values (C a))
      (by intros; assumption)
      (by
        intro C ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C f ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C op ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C op e2 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C op e1 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C r2 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C r2 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C r2 r3 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C e2 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C e1 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C op e2 tyres ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C op e1 tyres ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C id ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C el ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C e1 ty hctx ih a m h
        have hi := ih a m h
        cases he1 : e1 <;> simp only [invert_expr_prop, he1] at hi ⊢ <;>
          try contradiction <;> try assumption <;> try trivial
        case Eval =>
          intro hall
          exact (hi hall).elim)
      (by
        intro C ef tyargs ty hctx ih a m h
        have hi := ih a m h
        intro hall
        exact (hi hall).elim)
      (by
        intro C e2 ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C tycast ty hctx ih a m h
        have hi := ih a m h
        cases hca : C a <;> simp only [invert_expr_prop, hca] at hi ⊢ <;>
          try contradiction <;> try assumption)
      (by
        intro C el hctx ih a m h hall
        have hi := ih a m h
        cases hca : C a <;> simp only [exprlist_all_values, invert_expr_prop, hca] at hall hi ⊢ <;>
          try contradiction)
      (by
        intro C e1 hctx ih a m h
        have hi := ih a m h
        intro hall
        cases he1 : e1 <;> simp only [exprlist_all_values, he1] at hall ⊢
        exact hi hall)
      hcontext

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

theorem imm_safe_inv
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    imm_safe_invStatement := by
  unfold imm_safe_invStatement
  intro xi ge e k a m h
  cases h with
  | value => trivial
  | location => trivial
  | @localRed to C a m a' m' hred hcontext =>
      have hi :
          invert_expr_prop
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi ge e (C a) m := by
        exact (invert_expr_context
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge e).1
          _ _ _ hcontext _ _
          (lred_invert
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi ge e a m _ _ hred)
      cases hca : C a <;> simp only [hca] at hi ⊢ <;>
        try exact hi <;> trivial
  | @rvalRed to C a m t a' m' hred hcontext =>
      have hi :
          invert_expr_prop
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi ge e (C a) m := by
        exact (invert_expr_context
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge e).1
          _ _ _ hcontext _ _
          (rred_invert
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi ge e a m _ _ _ hred)
      cases hca : C a <;> simp only [hca] at hi ⊢ <;>
        try exact hi <;> trivial
  | @callRed to C a m fd args ty hred hcontext =>
      have hi :
          invert_expr_prop
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi ge e (C a) m := by
        exact (invert_expr_context
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge e).1
          _ _ _ hcontext _ _
          (callred_invert
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi ge e a _ _ _ m hred)
      cases hca : C a <;> simp only [hca] at hi ⊢ <;>
        try exact hi <;> trivial

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

theorem safe_inv
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    safe_invStatement := by
  unfold safe_invStatement
  intro xi ge e k C f a K m hs hcontext
  have himm := safe_imm_safe
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    xi ge f C a K e m k hs hcontext
  exact imm_safe_inv
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    xi ge e k a m himm

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

theorem eval_simple_steps
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_simple_stepsStatement := by
  unfold eval_simple_stepsStatement
  intro xi ge f k e m
  constructor
  · intro a v h C hC
    exact eval_simple_rvalue_steps xi ge f k e m a v h C hC
  · intro a b ofs bf h C hC
    exact eval_simple_lvalue_steps xi ge f k e m a b ofs bf h C hC

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Events
open CompCert4Lean.Lib.Integers

theorem simple_can_eval
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    simple_can_evalStatement := by
  unfold simple_can_evalStatement
  intro xi ge f k e m a
  induction a using expr.rec (motive_2 := fun _ => True) with
  | Eval v ty =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Eval v ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      simp [simple] at hs ⊢
      exact ⟨v, .esr_val⟩
  | Evar x ty =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Evar x ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      simp [simple] at hs ⊢
      have hinv := safe_inv (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge e .LV C f (.Evar x ty) k m hsafe hcontext
      rcases hinv with ⟨b, hlocal | ⟨hnone, hglobal⟩⟩
      · exact ⟨b, Ptrofs.zero, .Full, .esl_var_local hlocal⟩
      · exact ⟨b, Ptrofs.zero, .Full, .esl_var_global hnone hglobal⟩
  | Eloc b ofs bf ty =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Eloc b ofs bf ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      simp [simple] at hs ⊢
      exact ⟨b, ofs, bf, .esl_loc⟩
  | Esizeof ty1 ty =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Esizeof ty1 ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      simp [simple] at hs ⊢
      exact ⟨_, .esr_sizeof⟩
  | Ealignof ty1 ty =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Ealignof ty1 ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      simp [simple] at hs ⊢
      exact ⟨_, .esr_alignof⟩
  | Ederef r ty ih =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Ederef r ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      have hctx : context .RV .RV (fun x => C (.Ederef x ty)) := by
        exact context_compose .LV .RV C hcontext .RV _ (.deref (.ctx_top .RV))
      rcases ih .RV (fun x => C (.Ederef x ty)) hs hctx hsafe with ⟨v, hv⟩
      have hsafe' := eval_simple_rvalue_safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge f k e m
        (fun x => C (.Ederef x ty)) r v hv hctx hsafe
      have hinv := safe_inv (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge e .LV C f
        (.Ederef (.Eval v (typeof r)) ty) k m hsafe' hcontext
      rcases hinv with ⟨b, ofs, hptr⟩
      subst v
      exact ⟨b, ofs, .Full, .esl_deref hv⟩
  | Efield r fld ty ih =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Efield r fld ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      have hctx : context .RV .RV (fun x => C (.Efield x fld ty)) := by
        exact context_compose .LV .RV C hcontext .RV _ (.field (.ctx_top .RV))
      rcases ih .RV (fun x => C (.Efield x fld ty)) hs hctx hsafe with ⟨v, hv⟩
      have hsafe' := eval_simple_rvalue_safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge f k e m
        (fun x => C (.Efield x fld ty)) r v hv hctx hsafe
      have hinv := safe_inv (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge e .LV C f
        (.Efield (.Eval v (typeof r)) fld ty) k m hsafe' hcontext
      rcases hinv with ⟨b, ofs, hptr, hcase⟩
      subst v
      simp only [expr_kind] at ⊢
      cases htype : typeof r with
      | Tstruct id attr =>
          rw [htype] at hcase
          rcases hcase with ⟨co, delta, bf, hco, hoff⟩
          exact ⟨b, Ptrofs.add ofs (Ptrofs.repr delta), bf,
            .esl_field_struct hv htype hco hoff⟩
      | Tunion id attr =>
          rw [htype] at hcase
          rcases hcase with ⟨co, delta, bf, hco, hoff⟩
          exact ⟨b, Ptrofs.add ofs (Ptrofs.repr delta), bf,
            .esl_field_union hv htype hoff hco⟩
      | _ =>
          rw [htype] at hcase
          exact hcase.elim
  | Evalof l ty ih =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Evalof l ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      have hctx : context .LV .RV (fun x => C (.Evalof x ty)) := by
        exact context_compose .RV .RV C hcontext .LV _ (.rvalof (.ctx_top .LV))
      have hs' := hs
      simp [simple] at hs'
      have hsimple : simple l = true := hs'.1
      rcases ih .LV (fun x => C (.Evalof x ty)) hsimple hctx hsafe with ⟨b, ofs, bf, hl⟩
      have hsafe' := eval_simple_lvalue_safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge f k e m
        (fun x => C (.Evalof x ty)) l b ofs bf hl hctx hsafe
      have hinv := safe_inv (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge e .RV C f
        (.Evalof (.Eloc b ofs bf (typeof l)) ty) k m hsafe' hcontext
      rcases hinv with ⟨htype, t, v, hderef⟩
      have hvol : type_is_volatile ty = false := by
        simpa [← htype] using hs'.2
      have ht : t = E0 := by
        cases hderef with
        | value hmode hvol hload => rfl
        | volatile hmode hvol hload => simp_all
        | reference hmode => rfl
        | copy hmode => rfl
        | bitfield hload => rfl
      subst t
      exact ⟨v, .esr_rvalof hl htype.symm hvol hderef⟩
  | Eaddrof l ty ih =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Eaddrof l ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      have hctx : context .LV .RV (fun x => C (.Eaddrof x ty)) := by
        exact context_compose .RV .RV C hcontext .LV _ (.addrof (.ctx_top .LV))
      rcases ih .LV (fun x => C (.Eaddrof x ty)) hs hctx hsafe with ⟨b, ofs, bf, hl⟩
      have hsafe' := eval_simple_lvalue_safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge f k e m
        (fun x => C (.Eaddrof x ty)) l b ofs bf hl hctx hsafe
      have hinv := safe_inv (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge e .RV C f
        (.Eaddrof (.Eloc b ofs bf (typeof l)) ty) k m hsafe' hcontext
      have hfull : bf = .Full := hinv
      subst bf
      exact ⟨.Vptr b ofs, .esr_addrof hl⟩
  | Eunop op r ty ih =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Eunop op r ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      have hctx : context .RV .RV (fun x => C (.Eunop op x ty)) := by
        exact context_compose .RV .RV C hcontext .RV _ (.unop (.ctx_top .RV))
      rcases ih .RV (fun x => C (.Eunop op x ty)) hs hctx hsafe with ⟨v, hv⟩
      have hsafe' := eval_simple_rvalue_safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge f k e m
        (fun x => C (.Eunop op x ty)) r v hv hctx hsafe
      have hinv := safe_inv (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge e .RV C f
        (.Eunop op (.Eval v (typeof r)) ty) k m hsafe' hcontext
      rcases hinv with ⟨v', hop⟩
      exact ⟨v', .esr_unop hv hop⟩
  | Ebinop op r1 r2 ty ih1 ih2 =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Ebinop op r1 r2 ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      have hctx1 : context .RV .RV (fun x => C (.Ebinop op x r2 ty)) := by
        exact context_compose .RV .RV C hcontext .RV _ (.binopLeft (.ctx_top .RV))
      have hs' := hs
      simp [simple] at hs'
      have hs1 : simple r1 = true := hs'.1
      have hs2 : simple r2 = true := hs'.2
      rcases ih1 .RV (fun x => C (.Ebinop op x r2 ty)) hs1 hctx1 hsafe with ⟨v1, hv1⟩
      have hsafe1 := eval_simple_rvalue_safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge f k e m
        (fun x => C (.Ebinop op x r2 ty)) r1 v1 hv1 hctx1 hsafe
      have hctx2 : context .RV .RV (fun x => C (.Ebinop op (.Eval v1 (typeof r1)) x ty)) := by
        exact context_compose .RV .RV C hcontext .RV _
          (.binopRight (.ctx_top .RV))
      rcases ih2 .RV (fun x => C (.Ebinop op (.Eval v1 (typeof r1)) x ty)) hs2 hctx2 hsafe1 with ⟨v2, hv2⟩
      have hsafe2 := eval_simple_rvalue_safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge f k e m
        (fun x => C (.Ebinop op (.Eval v1 (typeof r1)) x ty)) r2 v2 hv2 hctx2 hsafe1
      have hinv := safe_inv (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge e .RV C f
        (.Ebinop op (.Eval v1 (typeof r1)) (.Eval v2 (typeof r2)) ty) k m hsafe2 hcontext
      rcases hinv with ⟨v, hbin⟩
      exact ⟨v, .esr_binop hv1 hv2 hbin⟩
  | Ecast r ty ih =>
      intro fromKind C hs hcontext hsafe
      have hkind := safe_expr_kind (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge fromKind C f (.Ecast r ty) k e m
        hcontext hsafe
      rw [← hkind] at hcontext ⊢
      have hctx : context .RV .RV (fun x => C (.Ecast x ty)) := by
        exact context_compose .RV .RV C hcontext .RV _ (.cast (.ctx_top .RV))
      rcases ih .RV (fun x => C (.Ecast x ty)) hs hctx hsafe with ⟨v, hv⟩
      have hsafe' := eval_simple_rvalue_safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge f k e m
        (fun x => C (.Ecast x ty)) r v hv hctx hsafe
      have hinv := safe_inv (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge e .RV C f
        (.Ecast (.Eval v (typeof r)) ty) k m hsafe' hcontext
      rcases hinv with ⟨v', hcast⟩
      exact ⟨v', .esr_cast hv hcast⟩
  | Eseqand r1 r2 ty ih1 ih2 =>
      intro fromKind C hs hcontext hsafe
      simp [simple] at hs
  | Eseqor r1 r2 ty ih1 ih2 =>
      intro fromKind C hs hcontext hsafe
      simp [simple] at hs
  | Econdition r1 r2 r3 ty ih1 ih2 ih3 =>
      intro fromKind C hs hcontext hsafe
      simp [simple] at hs
  | Eassign l r ty ihl ihr =>
      intro fromKind C hs hcontext hsafe
      simp [simple] at hs
  | Eassignop op l r tyres ty ihl ihr =>
      intro fromKind C hs hcontext hsafe
      simp [simple] at hs
  | Epostincr id l ty ih =>
      intro fromKind C hs hcontext hsafe
      simp [simple] at hs
  | Ecomma r1 r2 ty ih1 ih2 =>
      intro fromKind C hs hcontext hsafe
      simp [simple] at hs
  | Ecall r rargs ty ihr ihrargs =>
      intro fromKind C hs hcontext hsafe
      simp [simple] at hs
  | Ebuiltin ef tyargs rargs ty ihrargs =>
      intro fromKind C hs hcontext hsafe
      simp [simple] at hs
  | Eparen r tycast ty ih =>
      intro fromKind C hs hcontext hsafe
      simp [simple] at hs
  | Enil =>
      trivial
  | Econs r rl ihr ihrl =>
      trivial

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

theorem simple_can_eval_rval
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    simple_can_eval_rvalStatement := by
  unfold simple_can_eval_rvalStatement
  intro xi ge f k e m r C hs hcontext hsafe
  have hr := simple_can_eval
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    xi ge f k e m r .RV C hs hcontext hsafe
  rcases hr with ⟨v, hv⟩
  exact ⟨v, hv, eval_simple_rvalue_safe
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    xi ge f k e m C r v hv hcontext hsafe⟩

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

theorem simple_can_eval_lval
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    simple_can_eval_lvalStatement := by
  unfold simple_can_eval_lvalStatement
  intro xi ge f k e m l C hs hcontext hsafe
  have hl := simple_can_eval
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    xi ge f k e m l .LV C hs hcontext hsafe
  rcases hl with ⟨b, ofs, bf, hv⟩
  exact ⟨b, ofs, bf, hv, eval_simple_lvalue_safe
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    xi ge f k e m C l b ofs bf hv hcontext hsafe⟩

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Cfrontend.Csyntax

theorem simple_list_can_eval
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    simple_list_can_evalStatement := by
  unfold simple_list_can_evalStatement
  intro xi ge f k e m rl
  refine CompCert4Lean.Cfrontend.Csyntax.exprlist.rec
    (motive_1 := fun _ => True)
    (motive_2 := fun rl =>
      ∀ C, simplelist rl = true → contextlist' C →
        safe
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ge
          (.ExprState f (C rl) k e m) →
        ∃ vl, eval_simple_list'
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e m rl vl)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by
      intros C hs hcontext hsafe
      exact ⟨[], .esrl'_nil⟩)
    (by
      intros r rl hr ih C hs hcontext hsafe
      have hs' : simple r = true ∧ simplelist rl = true := by
        simpa [simplelist] using hs
      have hctx1 : context .RV .RV (fun x => C (.Econs x rl)) :=
        contextlist'_head rl C hcontext
      rcases simple_can_eval
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge f k e m r .RV (fun x => C (.Econs x rl)) hs'.1 hctx1 hsafe with
        ⟨v, hv⟩
      have hsafe' := eval_simple_rvalue_safe
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ge f k e m (fun x => C (.Econs x rl)) r v hv hctx1 hsafe
      have hctx2 : contextlist' (fun x => C (.Econs (.Eval v (typeof r)) x)) :=
        contextlist'_tail (.Eval v (typeof r)) C hcontext
      rcases ih (fun x => C (.Econs (.Eval v (typeof r)) x)) hs'.2 hctx2 hsafe' with
        ⟨vl, hvl⟩
      exact ⟨v :: vl, .esrl'_cons hv hvl⟩)
    rl

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

theorem decompose_expr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    decompose_exprStatement := by
  exact decompose_expr_aux
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Events
open CompCert4Lean.Lib.Integers

private theorem estep_simulation_pre {G S : Type}
    {step : G → S → trace → S → Prop} {ge : G} {a b c : S} {t : trace}
    (h : star step ge a E0 b) (h' : plus step ge b t c) : plus step ge a t c :=
  star_plus_trans G S step ge a E0 b t c t h h' rfl

private theorem estep_simulation_last {G S : Type}
    {step : G → S → trace → S → Prop} {ge : G} {a b c : S} {t : trace}
    (h : star step ge a E0 b) (h' : step ge b t c) : plus step ge a t c :=
  plus_right G S step ge a E0 b t c t h h' rfl

set_option maxHeartbeats 1200000 in
theorem estep_simulation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    estep_simulationStatement := by
  unfold estep_simulationStatement
  intro xi ge S t S' h
  cases h with
  | @step_expr f r k e m v ty heval hnot hty =>
      subst ty
      have hs := eval_simple_rvalue_steps xi ge f k e m r v heval
        (fun x => x) (.ctx_top .RV)
      rcases star_inv _ _ _ _ _ _ _ hs with ⟨heq, _⟩ | hp
      · have hr : expr.Eval v (typeof r) = r := by injection heq
        rw [← hr] at hnot
        exact False.elim hnot
      · exact hp
  | @step_rvalof_volatile f C l ty k e m b ofs bf t v hc hl hd ht hv =>
      subst ty
      have hC := leftcontext_context _ _ _ hc
      apply estep_simulation_last
        (eval_simple_lvalue_steps xi ge f k e m l b ofs bf hl
          (fun x => C (.Evalof x (typeof l)))
          (context_compose _ _ _ hC _ _ (.rvalof (.ctx_top .LV))))
      exact Or.inl (Csem.estep.step_rred (.rvalof hd) hC)
  | @step_seqand_true f C r1 r2 ty k e m v hc hr hb =>
      have hC := leftcontext_context _ _ _ hc
      apply estep_simulation_last
        (eval_simple_rvalue_steps xi ge f k e m r1 v hr
          (fun x => C (.Eseqand x r2 ty))
          (context_compose _ _ _ hC _ _ (.seqand (.ctx_top .RV))))
      exact Or.inl (Csem.estep.step_rred (.red_seqand_true hb) hC)
  | @step_seqand_false f C r1 r2 ty k e m v hc hr hb =>
      have hC := leftcontext_context _ _ _ hc
      apply estep_simulation_last
        (eval_simple_rvalue_steps xi ge f k e m r1 v hr
          (fun x => C (.Eseqand x r2 ty))
          (context_compose _ _ _ hC _ _ (.seqand (.ctx_top .RV))))
      exact Or.inl (Csem.estep.step_rred (.red_seqand_false hb) hC)
  | @step_seqor_true f C r1 r2 ty k e m v hc hr hb =>
      have hC := leftcontext_context _ _ _ hc
      apply estep_simulation_last
        (eval_simple_rvalue_steps xi ge f k e m r1 v hr
          (fun x => C (.Eseqor x r2 ty))
          (context_compose _ _ _ hC _ _ (.seqor (.ctx_top .RV))))
      exact Or.inl (Csem.estep.step_rred (.red_seqor_true hb) hC)
  | @step_seqor_false f C r1 r2 ty k e m v hc hr hb =>
      have hC := leftcontext_context _ _ _ hc
      apply estep_simulation_last
        (eval_simple_rvalue_steps xi ge f k e m r1 v hr
          (fun x => C (.Eseqor x r2 ty))
          (context_compose _ _ _ hC _ _ (.seqor (.ctx_top .RV))))
      exact Or.inl (Csem.estep.step_rred (.red_seqor_false hb) hC)
  | @step_condition f C r1 r2 r3 ty k e m v b hc hr hb =>
      have hC := leftcontext_context _ _ _ hc
      apply estep_simulation_last
        (eval_simple_rvalue_steps xi ge f k e m r1 v hr
          (fun x => C (.Econdition x r2 r3 ty))
          (context_compose _ _ _ hC _ _ (.condition (.ctx_top .RV))))
      exact Or.inl (Csem.estep.step_rred (.condition hb) hC)
  | @step_assign f C l r ty k e m b ofs bf v v1 t m' v' hc hl hr hcast ha ht =>
      subst ty
      have hC := leftcontext_context _ _ _ hc
      apply estep_simulation_pre
        (eval_simple_lvalue_steps xi ge f k e m l b ofs bf hl
          (fun x => C (.Eassign x r (typeof l)))
          (context_compose _ _ _ hC _ _ (.assignLeft (.ctx_top .LV))))
      apply estep_simulation_last
        (eval_simple_rvalue_steps xi ge f k e m r v hr
          (fun x => C (.Eassign (.Eloc b ofs bf (typeof l)) x (typeof l)))
          (context_compose _ _ _ hC _ _ (.assignRight (.ctx_top .RV))))
      exact Or.inl (Csem.estep.step_rred (.assign hcast ha) hC)
  | @step_assignop f C op l r tyres ty k e m b ofs bf v1 v2 v3 v4 t1 t2 m' v' t
      hc hl hd hr hb hcast ha ht htrace =>
      subst ty
      have hC := leftcontext_context _ _ _ hc
      apply estep_simulation_pre
        (eval_simple_lvalue_steps xi ge f k e m l b ofs bf hl
          (fun x => C (.Eassignop op x r tyres (typeof l)))
          (context_compose _ _ _ hC _ _ (.assignopLeft (.ctx_top .LV))))
      apply estep_simulation_pre
        (eval_simple_rvalue_steps xi ge f k e m r v2 hr
          (fun x => C (.Eassignop op (.Eloc b ofs bf (typeof l)) x tyres (typeof l)))
          (context_compose _ _ _ hC _ _ (.assignopRight (.ctx_top .RV))))
      refine plus_three _ _ _ _ _ t1
        (.ExprState f (C (.Eassign (.Eloc b ofs bf (typeof l))
          (.Ebinop op (.Eval v1 (typeof l)) (.Eval v2 (typeof r)) tyres) (typeof l))) k e m)
        E0
        (.ExprState f (C (.Eassign (.Eloc b ofs bf (typeof l))
          (.Eval v3 tyres) (typeof l))) k e m)
        t2 _ _ ?_ ?_ ?_ ?_
      · exact Or.inl (Csem.estep.step_rred (.assignop hd) hC)
      · exact Or.inl (Csem.estep.step_rred
          (C := fun x => C (.Eassign (.Eloc b ofs bf (typeof l)) x (typeof l)))
          (.binop hb)
          (context_compose _ _ _ hC _ _ (.assignRight (.ctx_top .RV))))
      · exact Or.inl (Csem.estep.step_rred (.assign hcast ha) hC)
      · exact htrace
  | @step_assignop_stuck f C op l r tyres ty k e m b ofs bf v1 v2 t
      hc hl hd hr hstuck ht =>
      subst ty
      have hC := leftcontext_context _ _ _ hc
      have hCa : context .RV .RV
          (fun x => C (.Eassign (.Eloc b ofs bf (typeof l)) x (typeof l))) :=
        context_compose _ _ _ hC _ _ (.assignRight (.ctx_top .RV))
      apply estep_simulation_pre
        (eval_simple_lvalue_steps xi ge f k e m l b ofs bf hl
          (fun x => C (.Eassignop op x r tyres (typeof l)))
          (context_compose _ _ _ hC _ _ (.assignopLeft (.ctx_top .LV))))
      apply estep_simulation_pre
        (eval_simple_rvalue_steps xi ge f k e m r v2 hr
          (fun x => C (.Eassignop op (.Eloc b ofs bf (typeof l)) x tyres (typeof l)))
          (context_compose _ _ _ hC _ _ (.assignopRight (.ctx_top .RV))))
      cases hb : sem_binary_operation ge.genv_cenv op v1 (typeof l) v2 (typeof r) m with
      | none =>
          refine plus_two _ _ _ _ _ t
            (.ExprState f (C (.Eassign (.Eloc b ofs bf (typeof l))
              (.Ebinop op (.Eval v1 (typeof l)) (.Eval v2 (typeof r)) tyres) (typeof l))) k e m)
            E0 _ _ ?_ ?_ ?_
          · exact Or.inl (Csem.estep.step_rred (.assignop hd) hC)
          · apply Or.inl
            apply Csem.estep.step_stuck hCa
            intro hs
            rcases imm_safe_inv xi ge e .RV _ m hs with ⟨v, hv⟩
            rw [hb] at hv
            contradiction
          · exact (CompCert4Lean.Common.Events.E0_right t).symm
      | some v3 =>
          simp only [hb] at hstuck
          refine plus_three _ _ _ _ _ t
            (.ExprState f (C (.Eassign (.Eloc b ofs bf (typeof l))
              (.Ebinop op (.Eval v1 (typeof l)) (.Eval v2 (typeof r)) tyres) (typeof l))) k e m)
            E0
            (.ExprState f (C (.Eassign (.Eloc b ofs bf (typeof l))
              (.Eval v3 tyres) (typeof l))) k e m)
            E0 _ _ ?_ ?_ ?_ ?_
          · exact Or.inl (Csem.estep.step_rred (.assignop hd) hC)
          · exact Or.inl (Csem.estep.step_rred
              (C := fun x => C (.Eassign (.Eloc b ofs bf (typeof l)) x (typeof l)))
              (.binop hb) hCa)
          · apply Or.inl
            apply Csem.estep.step_stuck hC
            intro hs
            rcases imm_safe_inv xi ge e .RV _ m hs with ⟨v4, m', v', t', _, hcast, ha⟩
            rw [hcast] at hstuck
            exact hstuck t' m' v' ha
          · exact (CompCert4Lean.Common.Events.E0_right t).symm
  | @step_postincr f C id l ty k e m b ofs bf v1 v2 v3 t1 t2 m' v' t
      hc hl hd hi hcast ha ht htrace =>
      subst ty
      have hC := leftcontext_context _ _ _ hc
      have hb : sem_binary_operation ge.genv_cenv
          (match (generalizing := false) id with | .Incr => .Oadd | .Decr => .Osub)
          v1 (typeof l) (.Vint Int.one) type_int32s m = some v2 := by
        cases id <;> exact hi
      apply estep_simulation_pre
        (eval_simple_lvalue_steps xi ge f k e m l b ofs bf hl
          (fun x => C (.Epostincr id x (typeof l)))
          (context_compose _ _ _ hC _ _ (.postincr (.ctx_top .LV))))
      refine plus_four _ _ _ _ _ t1
        (.ExprState f (C (.Ecomma
          (.Eassign (.Eloc b ofs bf (typeof l))
            (.Ebinop (match (generalizing := false) id with | .Incr => .Oadd | .Decr => .Osub)
              (.Eval v1 (typeof l)) (.Eval (.Vint Int.one) type_int32s)
              (incrdecr_type (typeof l))) (typeof l))
          (.Eval v1 (typeof l)) (typeof l))) k e m)
        E0
        (.ExprState f (C (.Ecomma
          (.Eassign (.Eloc b ofs bf (typeof l))
            (.Eval v2 (incrdecr_type (typeof l))) (typeof l))
          (.Eval v1 (typeof l)) (typeof l))) k e m)
        t2
        (.ExprState f (C (.Ecomma (.Eval v' (typeof l))
          (.Eval v1 (typeof l)) (typeof l))) k e m')
        E0 _ _ ?_ ?_ ?_ ?_ ?_
      · exact Or.inl (Csem.estep.step_rred (.postincr hd rfl) hC)
      · exact Or.inl (Csem.estep.step_rred
          (C := fun x => C (.Ecomma
            (.Eassign (.Eloc b ofs bf (typeof l)) x (typeof l))
            (.Eval v1 (typeof l)) (typeof l)))
          (.binop hb)
          (context_compose _ _ _ hC _ _ (.comma (.assignRight (.ctx_top .RV)))))
      · exact Or.inl (Csem.estep.step_rred
          (C := fun x => C (.Ecomma x (.Eval v1 (typeof l)) (typeof l)))
          (.assign hcast ha)
          (context_compose _ _ _ hC _ _ (.comma (.ctx_top .RV))))
      · exact Or.inl (Csem.estep.step_rred (.comma rfl) hC)
      · exact htrace.trans
          (congrArg (Eapp t1) (CompCert4Lean.Common.Events.E0_right t2).symm)
  | @step_postincr_stuck f C id l ty k e m b ofs bf v1 t hc hl hd hstuck ht =>
      subst ty
      have hC := leftcontext_context _ _ _ hc
      have hCc : context .RV .RV
          (fun x => C (.Ecomma x (.Eval v1 (typeof l)) (typeof l))) :=
        context_compose _ _ _ hC _ _ (.comma (.ctx_top .RV))
      have hCa : context .RV .RV
          (fun x => C (.Ecomma
            (.Eassign (.Eloc b ofs bf (typeof l)) x (typeof l))
            (.Eval v1 (typeof l)) (typeof l))) :=
        context_compose _ _ _ hCc _ _ (.assignRight (.ctx_top .RV))
      have hb : sem_binary_operation ge.genv_cenv
          (match (generalizing := false) id with | .Incr => .Oadd | .Decr => .Osub)
          v1 (typeof l) (.Vint Int.one) type_int32s m =
          sem_incrdecr ge.genv_cenv id v1 (typeof l) m := by
        cases id <;> rfl
      apply estep_simulation_pre
        (eval_simple_lvalue_steps xi ge f k e m l b ofs bf hl
          (fun x => C (.Epostincr id x (typeof l)))
          (context_compose _ _ _ hC _ _ (.postincr (.ctx_top .LV))))
      cases hi : sem_incrdecr ge.genv_cenv id v1 (typeof l) m with
      | none =>
          rw [hi] at hb
          refine plus_two _ _ _ _ _ t
            (.ExprState f (C (.Ecomma
              (.Eassign (.Eloc b ofs bf (typeof l))
                (.Ebinop (match (generalizing := false) id with | .Incr => .Oadd | .Decr => .Osub)
                  (.Eval v1 (typeof l)) (.Eval (.Vint Int.one) type_int32s)
                  (incrdecr_type (typeof l))) (typeof l))
              (.Eval v1 (typeof l)) (typeof l))) k e m)
            E0 _ _ ?_ ?_ ?_
          · exact Or.inl (Csem.estep.step_rred (.postincr hd rfl) hC)
          · apply Or.inl
            apply Csem.estep.step_stuck hCa
            intro hs
            rcases imm_safe_inv xi ge e .RV _ m hs with ⟨v, hv⟩
            rw [hb] at hv
            contradiction
          · exact (CompCert4Lean.Common.Events.E0_right t).symm
      | some v2 =>
          rw [hi] at hb
          simp only [hi] at hstuck
          refine plus_three _ _ _ _ _ t
            (.ExprState f (C (.Ecomma
              (.Eassign (.Eloc b ofs bf (typeof l))
                (.Ebinop (match (generalizing := false) id with | .Incr => .Oadd | .Decr => .Osub)
                  (.Eval v1 (typeof l)) (.Eval (.Vint Int.one) type_int32s)
                  (incrdecr_type (typeof l))) (typeof l))
              (.Eval v1 (typeof l)) (typeof l))) k e m)
            E0
            (.ExprState f (C (.Ecomma
              (.Eassign (.Eloc b ofs bf (typeof l))
                (.Eval v2 (incrdecr_type (typeof l))) (typeof l))
              (.Eval v1 (typeof l)) (typeof l))) k e m)
            E0 _ _ ?_ ?_ ?_ ?_
          · exact Or.inl (Csem.estep.step_rred (.postincr hd rfl) hC)
          · exact Or.inl (Csem.estep.step_rred
              (C := fun x => C (.Ecomma
                (.Eassign (.Eloc b ofs bf (typeof l)) x (typeof l))
                (.Eval v1 (typeof l)) (typeof l)))
              (.binop hb) hCa)
          · apply Or.inl
            apply Csem.estep.step_stuck hCc
            intro hs
            rcases imm_safe_inv xi ge e .RV _ m hs with ⟨v3, m', v', t', _, hcast, ha⟩
            rw [hcast] at hstuck
            exact hstuck t' m' v' ha
          · exact (CompCert4Lean.Common.Events.E0_right t).symm
  | @step_comma f C r1 r2 ty k e m v hc hr ht =>
      have hC := leftcontext_context _ _ _ hc
      apply estep_simulation_last
        (eval_simple_rvalue_steps xi ge f k e m r1 v hr
          (fun x => C (.Ecomma x r2 ty))
          (context_compose _ _ _ hC _ _ (.comma (.ctx_top .RV))))
      exact Or.inl (Csem.estep.step_rred (.comma ht.symm) hC)
  | @step_paren f C r tycast ty k e m v1 v hc hr hcast =>
      have hC := leftcontext_context _ _ _ hc
      apply estep_simulation_last
        (eval_simple_rvalue_steps xi ge f k e m r v1 hr
          (fun x => C (.Eparen x tycast ty))
          (context_compose _ _ _ hC _ _ (.paren (.ctx_top .RV))))
      exact Or.inl (Csem.estep.step_rred (.paren hcast) hC)
  | @step_call f C rf rargs ty k e m targs tres cconv vf vargs fd
      hc hclass hf hargs hfind ht =>
      have hC := leftcontext_context _ _ _ hc
      rcases eval_simple_list_implies ge e m rargs targs vargs hargs with ⟨vl, hcast, hargs'⟩
      apply estep_simulation_pre
        (eval_simple_rvalue_steps xi ge f k e m rf vf hf
          (fun x => C (.Ecall x rargs ty))
          (context_compose _ _ _ hC _ _ (.callLeft (.ctx_top .RV))))
      apply estep_simulation_last
        (eval_simple_list_steps xi ge f k e m rargs vl hargs'
          (fun x => C (.Ecall (.Eval vf (typeof rf)) x ty))
          (contextlist'_call _ .Enil _ _ hC))
      exact Or.inl (Csem.estep.step_call (.call hfind hcast ht hclass) hC)
  | @step_builtin f C ef tyargs rargs ty k e m vargs t vres m' hc hargs hext =>
      have hC := leftcontext_context _ _ _ hc
      rcases eval_simple_list_implies ge e m rargs tyargs vargs hargs with ⟨vl, hcast, hargs'⟩
      apply estep_simulation_last
        (eval_simple_list_steps xi ge f k e m rargs vl hargs'
          (fun x => C (.Ebuiltin ef tyargs x ty))
          (contextlist'_builtin _ _ .Enil _ _ hC))
      exact Or.inl (Csem.estep.step_rred (.builtin hcast hext) hC)

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Events

set_option maxHeartbeats 800000 in
 theorem can_estep
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    can_estepStatement := by
  classical
  unfold can_estepStatement
  intro xi ge f a k e m hsafe hnotval
  rcases decompose_topexpr xi ge f k e m a hsafe with hs | ⟨C, a', ha, hs, hl⟩
  · rcases simple_can_eval xi ge f k e m a .RV (fun x => x) hs (.ctx_top .RV) hsafe with
      ⟨v, hv⟩
    exact ⟨_, _, estep.step_expr hv hnotval rfl⟩
  · subst a
    have hC := leftcontext_context _ _ _ hl
    cases a' <;> simp only [simple_side_effect] at hs
    case Evalof l ty =>
      rcases simple_can_eval_lval xi ge f k e m l (fun x => C (.Evalof x ty))
        hs.1 (context_compose _ _ _ hC _ _ (.rvalof (.ctx_top .LV))) hsafe with
        ⟨b, ofs, bf, hv, hs1⟩
      rcases safe_inv xi ge e .RV C f _ k m hs1 hC with ⟨ht, t, v, hd⟩
      exact ⟨_, _, estep.step_rvalof_volatile hl hv hd ht.symm (ht ▸ hs.2)⟩
    case Eseqand r1 r2 ty =>
      rcases simple_can_eval_rval xi ge f k e m r1 (fun x => C (.Eseqand x r2 ty))
        hs (context_compose _ _ _ hC _ _ (.seqand (.ctx_top .RV))) hsafe with
        ⟨v, hv, hs1⟩
      rcases safe_inv xi ge e .RV C f _ k m hs1 hC with ⟨b, hb⟩
      cases b
      · exact ⟨_, _, estep.step_seqand_false hl hv hb⟩
      · exact ⟨_, _, estep.step_seqand_true hl hv hb⟩
    case Eseqor r1 r2 ty =>
      rcases simple_can_eval_rval xi ge f k e m r1 (fun x => C (.Eseqor x r2 ty))
        hs (context_compose _ _ _ hC _ _ (.seqor (.ctx_top .RV))) hsafe with
        ⟨v, hv, hs1⟩
      rcases safe_inv xi ge e .RV C f _ k m hs1 hC with ⟨b, hb⟩
      cases b
      · exact ⟨_, _, estep.step_seqor_false hl hv hb⟩
      · exact ⟨_, _, estep.step_seqor_true hl hv hb⟩
    case Econdition r1 r2 r3 ty =>
      rcases simple_can_eval_rval xi ge f k e m r1
        (fun x => C (.Econdition x r2 r3 ty))
        hs (context_compose _ _ _ hC _ _ (.condition (.ctx_top .RV))) hsafe with
        ⟨v, hv, hs1⟩
      rcases safe_inv xi ge e .RV C f _ k m hs1 hC with ⟨b, hb⟩
      exact ⟨_, _, estep.step_condition hl hv hb⟩
    case Eassign l r ty =>
      rcases simple_can_eval_lval xi ge f k e m l (fun x => C (.Eassign x r ty))
        hs.1 (context_compose _ _ _ hC _ _ (.assignLeft (.ctx_top .LV))) hsafe with
        ⟨b, ofs, bf, hv1, hs1⟩
      rcases simple_can_eval_rval xi ge f k e m r
        (fun x => C (.Eassign (.Eloc b ofs bf (typeof l)) x ty))
        hs.2 (context_compose _ _ _ hC _ _ (.assignRight (.ctx_top .RV))) hs1 with
        ⟨v, hv2, hs2⟩
      rcases safe_inv xi ge e .RV C f _ k m hs2 hC with
        ⟨v1, m', v', t, ht, hcast, ha⟩
      exact ⟨_, _, estep.step_assign hl hv1 hv2 hcast ha ht⟩
    case Eassignop op l r tyres ty =>
      rcases simple_can_eval_lval xi ge f k e m l
        (fun x => C (.Eassignop op x r tyres ty))
        hs.1 (context_compose _ _ _ hC _ _ (.assignopLeft (.ctx_top .LV))) hsafe with
        ⟨b, ofs, bf, hv1, hs1⟩
      rcases simple_can_eval_rval xi ge f k e m r
        (fun x => C (.Eassignop op (.Eloc b ofs bf (typeof l)) x tyres ty))
        hs.2 (context_compose _ _ _ hC _ _ (.assignopRight (.ctx_top .RV))) hs1 with
        ⟨v, hv2, hs2⟩
      rcases safe_inv xi ge e .RV C f _ k m hs2 hC with ⟨t1, v1, ht, hd⟩
      cases hop : sem_binary_operation ge.genv_cenv op v1 (typeof l) v (typeof r) m with
      | none =>
          exact ⟨_, _, estep.step_assignop_stuck hl hv1 hd hv2 (by simp [hop]) ht⟩
      | some v3 =>
          cases hcast : sem_cast v3 tyres (typeof l) m with
          | none =>
              exact ⟨_, _, estep.step_assignop_stuck hl hv1 hd hv2
                (by simp [hop, hcast]) ht⟩
          | some v4 =>
              by_cases ha : ∃ t2 m' v', assign_loc ge (typeof l) m b ofs bf v4 t2 m' v'
              · rcases ha with ⟨t2, m', v', ha⟩
                exact ⟨_, _, estep.step_assignop hl hv1 hd hv2 hop hcast ha ht rfl⟩
              · refine ⟨_, _, estep.step_assignop_stuck hl hv1 hd hv2 ?_ ht⟩
                simp only [hop, hcast]
                intro t2 m' v' h
                exact ha ⟨t2, m', v', h⟩
    case Epostincr id l ty =>
      rcases simple_can_eval_lval xi ge f k e m l
        (fun x => C (.Epostincr id x ty))
        hs (context_compose _ _ _ hC _ _ (.postincr (.ctx_top .LV))) hsafe with
        ⟨b, ofs, bf, hv, hs1⟩
      rcases safe_inv xi ge e .RV C f _ k m hs1 hC with ⟨t1, v1, ht, hd⟩
      subst ty
      cases hop : sem_incrdecr ge.genv_cenv id v1 (typeof l) m with
      | none =>
          exact ⟨_, _, estep.step_postincr_stuck hl hv hd (by simp [hop]) rfl⟩
      | some v2 =>
          cases hcast : sem_cast v2 (incrdecr_type (typeof l)) (typeof l) m with
          | none =>
              exact ⟨_, _, estep.step_postincr_stuck hl hv hd
                (by simp [hop, hcast]) rfl⟩
          | some v3 =>
              by_cases ha : ∃ t2 m' v', assign_loc ge (typeof l) m b ofs bf v3 t2 m' v'
              · rcases ha with ⟨t2, m', v', ha⟩
                exact ⟨_, _, estep.step_postincr hl hv hd hop hcast ha rfl rfl⟩
              · refine ⟨_, _, estep.step_postincr_stuck hl hv hd ?_ rfl⟩
                simp only [hop, hcast]
                intro t2 m' v' h
                exact ha ⟨t2, m', v', h⟩
    case Ecomma r1 r2 ty =>
      rcases simple_can_eval_rval xi ge f k e m r1 (fun x => C (.Ecomma x r2 ty))
        hs (context_compose _ _ _ hC _ _ (.comma (.ctx_top .RV))) hsafe with
        ⟨v, hv, hs1⟩
      have ht := safe_inv xi ge e .RV C f _ k m hs1 hC
      exact ⟨_, _, estep.step_comma hl hv ht.symm⟩
    case Ecall r rl ty =>
      rcases simple_can_eval_rval xi ge f k e m r (fun x => C (.Ecall x rl ty))
        hs.1 (context_compose _ _ _ hC _ _ (.callLeft (.ctx_top .RV))) hsafe with
        ⟨vf, hv, hs1⟩
      have hcl : contextlist' (fun x => C (.Ecall (.Eval vf (typeof r)) x ty)) :=
        contextlist'_call _ .Enil _ _ hC
      rcases simple_list_can_eval xi ge f k e m rl _ hs.2 hcl hs1 with ⟨vl, hvl⟩
      have hs2 := safe_steps xi ge _ _ hs1
        (eval_simple_list_steps xi ge f k e m rl vl hvl _ hcl)
      have hinv := safe_inv xi ge e .RV C f _ k m hs2 hC
      rcases hinv (rval_list_all_values vl rl) with
        ⟨tyargs, tyres, cconv, fd, vargs, hclass, hfind, hcast, hty⟩
      exact ⟨_, _, estep.step_call hl hclass hv
        (can_eval_simple_list ge e m rl vl hvl tyargs vargs hcast) hfind hty⟩
    case Ebuiltin ef tyargs rl ty =>
      have hcl : contextlist' (fun x => C (.Ebuiltin ef tyargs x ty)) :=
        contextlist'_builtin _ _ .Enil _ _ hC
      rcases simple_list_can_eval xi ge f k e m rl _ hs hcl hsafe with ⟨vl, hvl⟩
      have hs1 := safe_steps xi ge _ _ hsafe
        (eval_simple_list_steps xi ge f k e m rl vl hvl _ hcl)
      have hinv := safe_inv xi ge e .RV C f _ k m hs1 hC
      rcases hinv (rval_list_all_values vl rl) with ⟨vargs, t, vres, m', hcast, hext⟩
      exact ⟨_, _, estep.step_builtin hl
        (can_eval_simple_list ge e m rl vl hvl tyargs vargs hcast) hext⟩
    case Eparen r tycast ty =>
      rcases simple_can_eval_rval xi ge f k e m r (fun x => C (.Eparen x tycast ty))
        hs (context_compose _ _ _ hC _ _ (.paren (.ctx_top .RV))) hsafe with
        ⟨v1, hv, hs1⟩
      rcases safe_inv xi ge e .RV C f _ k m hs1 hC with ⟨v, hcast⟩
      exact ⟨_, _, estep.step_paren hl hv hcast⟩

end CompCert4Lean.Cfrontend.Cstrategy

namespace CompCert4Lean.Cfrontend.Cstrategy

theorem step_simulation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_simulationStatement := by
  unfold step_simulationStatement
  intro xi ge S1 t S2 h
  rcases h with he | hs
  · exact estep_simulation xi ge S1 t S2 he
  · exact CompCert4Lean.Common.Smallstep.plus_one _ _ _ _ _ _ _ (Or.inr hs)

end CompCert4Lean.Cfrontend.Cstrategy
