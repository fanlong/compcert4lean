import CompCert4Lean.Cfrontend.Cop
import CompCert4Lean.Cfrontend.Ctypes

/-!
# CompCert C abstract syntax

Definition-bearing translation of CompCert's `cfrontend/Csyntax.v`.
-/

namespace CompCert4Lean.Cfrontend.Csyntax

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev calling_convention := CompCert4Lean.Common.AST.calling_convention
private abbrev external_function := CompCert4Lean.Common.AST.external_function
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev type := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev unary_operation := CompCert4Lean.Cfrontend.Cop.unary_operation
private abbrev binary_operation := CompCert4Lean.Cfrontend.Cop.binary_operation
private abbrev incr_or_decr := CompCert4Lean.Cfrontend.Cop.incr_or_decr

mutual
  inductive expr : Type where
    | Eval (v : val) (ty : type)
    | Evar (x : ident) (ty : type)
    | Efield (l : expr) (f : ident) (ty : type)
    | Evalof (l : expr) (ty : type)
    | Ederef (r : expr) (ty : type)
    | Eaddrof (l : expr) (ty : type)
    | Eunop (op : unary_operation) (r : expr) (ty : type)
    | Ebinop (op : binary_operation) (r1 r2 : expr) (ty : type)
    | Ecast (r : expr) (ty : type)
    | Eseqand (r1 r2 : expr) (ty : type)
    | Eseqor (r1 r2 : expr) (ty : type)
    | Econdition (r1 r2 r3 : expr) (ty : type)
    | Esizeof (ty' : type) (ty : type)
    | Ealignof (ty' : type) (ty : type)
    | Eassign (l r : expr) (ty : type)
    | Eassignop (op : binary_operation) (l r : expr) (tyres ty : type)
    | Epostincr (id : incr_or_decr) (l : expr) (ty : type)
    | Ecomma (r1 r2 : expr) (ty : type)
    | Ecall (r1 : expr) (rargs : exprlist) (ty : type)
    | Ebuiltin (ef : external_function) (tyargs : List type)
        (rargs : exprlist) (ty : type)
    | Eloc (b : block) (ofs : ptrofs) (bf : bitfield) (ty : type)
    | Eparen (r : expr) (tycast ty : type)

  inductive exprlist : Type where
    | Enil
    | Econs (r1 : expr) (rl : exprlist)
end

export expr (Eval Evar Efield Evalof Ederef Eaddrof Eunop Ebinop Ecast Eseqand
  Eseqor Econdition Esizeof Ealignof Eassign Eassignop Epostincr Ecomma Ecall
  Ebuiltin Eloc Eparen)
export exprlist (Enil Econs)

def typeof : expr -> type
  | .Eloc _ _ _ ty => ty
  | .Evar _ ty => ty
  | .Ederef _ ty => ty
  | .Efield _ _ ty => ty
  | .Eval _ ty => ty
  | .Evalof _ ty => ty
  | .Eaddrof _ ty => ty
  | .Eunop _ _ ty => ty
  | .Ebinop _ _ _ ty => ty
  | .Ecast _ ty => ty
  | .Econdition _ _ _ ty => ty
  | .Eseqand _ _ ty => ty
  | .Eseqor _ _ ty => ty
  | .Esizeof _ ty => ty
  | .Ealignof _ ty => ty
  | .Eassign _ _ ty => ty
  | .Eassignop _ _ _ _ ty => ty
  | .Epostincr _ _ ty => ty
  | .Ecomma _ _ ty => ty
  | .Ecall _ _ ty => ty
  | .Ebuiltin _ _ _ ty => ty
  | .Eparen _ _ ty => ty

def label := ident

mutual
  inductive statement : Type where
    | Sskip
    | Sdo (r : expr)
    | Ssequence (s1 s2 : statement)
    | Sifthenelse (r : expr) (s1 s2 : statement)
    | Swhile (r : expr) (body : statement)
    | Sdowhile (r : expr) (body : statement)
    | Sfor (init : statement) (cond : expr) (iter body : statement)
    | Sbreak
    | Scontinue
    | Sreturn (r : Option expr)
    | Sswitch (r : expr) (cases : labeled_statements)
    | Slabel (lbl : label) (body : statement)
    | Sgoto (lbl : label)

  inductive labeled_statements : Type where
    | LSnil
    | LScons (lbl : Option Z) (stmt : statement) (rest : labeled_statements)
end

export statement (Sskip Sdo Ssequence Sifthenelse Swhile Sdowhile Sfor Sbreak
  Scontinue Sreturn Sswitch Slabel Sgoto)
export labeled_statements (LSnil LScons)

structure function : Type where
  fn_return : type
  fn_callconv : calling_convention
  fn_params : List (ident × type)
  fn_vars : List (ident × type)
  fn_body : statement

export function (fn_return fn_callconv fn_params fn_vars fn_body)

def fundef : Type :=
  CompCert4Lean.Cfrontend.Ctypes.fundef function

def type_of_function (f : function) : type :=
  .Tfunction (CompCert4Lean.Cfrontend.Ctypes.type_of_params f.fn_params)
    f.fn_return f.fn_callconv

def type_of_fundef (f : fundef) : type :=
  match f with
  | .Internal fd => type_of_function fd
  | .External _ args res cc => .Tfunction args res cc

def program : Type :=
  CompCert4Lean.Cfrontend.Ctypes.program function

end CompCert4Lean.Cfrontend.Csyntax
