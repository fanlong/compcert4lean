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
