import CompCert4Lean.Cfrontend.SimplExpr

/-!
# Relational specification of expression simplification

Definition-bearing translation of the selected surface of CompCert's
`cfrontend/SimplExprspec.v`.  Constructor surfaces outside this packet are
kept private; the seven mapped generated constructors are exposed below under
their source names.
-/

namespace CompCert4Lean.Cfrontend.SimplExprspec

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev type := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev composite := CompCert4Lean.Cfrontend.Ctypes.composite
private abbrev composite_env := CompCert4Lean.Cfrontend.Ctypes.composite_env
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev cexpr := CompCert4Lean.Cfrontend.Csyntax.expr
private abbrev cexprlist := CompCert4Lean.Cfrontend.Csyntax.exprlist
private abbrev cstatement := CompCert4Lean.Cfrontend.Csyntax.statement
private abbrev clabeled_statements :=
  CompCert4Lean.Cfrontend.Csyntax.labeled_statements
private abbrev cfunction := CompCert4Lean.Cfrontend.Csyntax.function
private abbrev cfundef := CompCert4Lean.Cfrontend.Csyntax.fundef
private abbrev cprogram := CompCert4Lean.Cfrontend.Csyntax.program
private abbrev expr := CompCert4Lean.Cfrontend.Clight.expr
private abbrev statement := CompCert4Lean.Cfrontend.Clight.statement
private abbrev labeled_statements :=
  CompCert4Lean.Cfrontend.Clight.labeled_statements
private abbrev function := CompCert4Lean.Cfrontend.Clight.function
private abbrev fundef := CompCert4Lean.Cfrontend.Clight.fundef
private abbrev genv := CompCert4Lean.Cfrontend.Clight.genv
private abbrev env := CompCert4Lean.Cfrontend.Clight.env
private abbrev temp_env := CompCert4Lean.Cfrontend.Clight.temp_env
private abbrev destination := CompCert4Lean.Cfrontend.SimplExpr.destination
private abbrev set_destination := CompCert4Lean.Cfrontend.SimplExpr.set_destination
private abbrev generator := CompCert4Lean.Cfrontend.SimplExpr.generator
private abbrev FreshIdentContext :=
  CompCert4Lean.Cfrontend.SimplExpr.FreshIdentContext

private abbrev Included {A : Type} (xs ys : List A) : Prop :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl xs ys

private abbrev Disjoint {A : Type} (xs ys : List A) : Prop :=
  CompCert4Lean.Lib.Coqlib.list_disjoint xs ys

def final (dst : destination) (a : expr) : List statement :=
  match dst with
  | .For_val => []
  | .For_effects => []
  | .For_set sd => CompCert4Lean.Cfrontend.SimplExpr.do_set sd a

def tr_is_bitfield_access (ce : composite_env) (l : expr) (bf : bitfield) : Prop :=
  match l with
  | .Efield r f _ =>
      ∃ (co : composite) (ofs : Z),
        match CompCert4Lean.Cfrontend.Clight.typeof r with
        | .Tstruct id _ =>
            PTree.get id ce = some co ∧
              field_offset ce f co.co_members = .OK (ofs, bf)
        | .Tunion id _ =>
            PTree.get id ce = some co ∧
              union_field_offset ce f co.co_members = .OK (ofs, bf)
        | _ => False
  | _ => bf = .Full

private def specMakeIf (a : expr) (s1 s2 : statement) : statement :=
  match CompCert4Lean.Cfrontend.SimplExpr.eval_simpl_expr a with
  | some v =>
      match CompCert4Lean.Cfrontend.Cop.bool_val v
          (CompCert4Lean.Cfrontend.Clight.typeof a) Mem.empty with
      | some b => if b then s1 else s2
      | none => .Sifthenelse a s1 s2
  | none => .Sifthenelse a s1 s2

private inductive TrRvalofCore (ce : composite_env) :
    type → expr → List statement → expr → List ident → Prop where
  | nonvolatile (ty : type) (a : expr) (tmp : List ident)
      (hvolatile : type_is_volatile ty = false) :
      TrRvalofCore ce ty a [] a tmp
  | volatile (ty : type) (a : expr) (t : ident) (bf : bitfield)
      (tmp : List ident) (hvolatile : type_is_volatile ty = true)
      (htmp : t ∈ tmp) (haccess : tr_is_bitfield_access ce a bf) :
      TrRvalofCore ce ty a
        [CompCert4Lean.Cfrontend.SimplExpr.make_set bf t a]
        (.Etempvar t ty) tmp

def tr_rvalof (ce : composite_env) (ty : type) (a : expr)
    (sl : List statement) (b : expr) (tmps : List ident) : Prop :=
  TrRvalofCore ce ty a sl b tmps

mutual
  private inductive TrExprCore (ce : composite_env) :
      temp_env → destination → cexpr → List statement → expr → List ident → Prop where
    | variable (le : temp_env) (dst : destination) (id : ident) (ty : type)
        (tmp : List ident) :
        TrExprCore ce le dst (.Evar id ty)
          (final dst (.Evar id ty)) (.Evar id ty) tmp
    | dereference (le : temp_env) (dst : destination) (e1 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp) :
        TrExprCore ce le dst (.Ederef e1 ty)
          (sl1 ++ final dst (CompCert4Lean.Cfrontend.SimplExpr.Ederef' a1 ty))
          (CompCert4Lean.Cfrontend.SimplExpr.Ederef' a1 ty) tmp
    | field (le : temp_env) (dst : destination) (e1 : cexpr) (f : ident)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp) :
        TrExprCore ce le dst (.Efield e1 f ty)
          (sl1 ++ final dst (.Efield a1 f ty)) (.Efield a1 f ty) tmp
    | valueEffects (le : temp_env) (v : val) (ty : type) (any : expr)
        (tmp : List ident) :
        TrExprCore ce le .For_effects (.Eval v ty) [] any tmp
    | valueValue (le : temp_env) (v : val) (ty : type) (a : expr)
        (tmp : List ident) (htype : CompCert4Lean.Cfrontend.Clight.typeof a = ty)
        (heval : ∀ (tge : genv) (e : env) (le' : temp_env) (m : mem),
          (∀ id, id ∈ tmp → PTree.get id le' = PTree.get id le) →
          CompCert4Lean.Cfrontend.Clight.eval_expr tge e le' m a v) :
        TrExprCore ce le .For_val (.Eval v ty) [] a tmp
    | valueSet (le : temp_env) (sd : set_destination) (v : val) (ty : type)
        (a any : expr) (tmp : List ident)
        (htype : CompCert4Lean.Cfrontend.Clight.typeof a = ty)
        (heval : ∀ (tge : genv) (e : env) (le' : temp_env) (m : mem),
          (∀ id, id ∈ tmp → PTree.get id le' = PTree.get id le) →
          CompCert4Lean.Cfrontend.Clight.eval_expr tge e le' m a v) :
        TrExprCore ce le (.For_set sd) (.Eval v ty)
          (CompCert4Lean.Cfrontend.SimplExpr.do_set sd a) any tmp
    | sizeOf (le : temp_env) (dst : destination) (ty' ty : type)
        (tmp : List ident) :
        TrExprCore ce le dst (.Esizeof ty' ty)
          (final dst (.Esizeof ty' ty)) (.Esizeof ty' ty) tmp
    | alignOf (le : temp_env) (dst : destination) (ty' ty : type)
        (tmp : List ident) :
        TrExprCore ce le dst (.Ealignof ty' ty)
          (final dst (.Ealignof ty' ty)) (.Ealignof ty' ty) tmp
    | valueOf (le : temp_env) (dst : destination) (e1 : cexpr) (ty : type)
        (tmp : List ident) (sl1 : List statement) (a1 : expr)
        (tmp1 : List ident) (sl2 : List statement) (a2 : expr)
        (tmp2 : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrRvalofCore ce (CompCert4Lean.Cfrontend.Csyntax.typeof e1)
          a1 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        TrExprCore ce le dst (.Evalof e1 ty)
          (sl1 ++ sl2 ++ final dst a2) a2 tmp
    | addressOf (le : temp_env) (dst : destination) (e1 : cexpr) (ty : type)
        (tmp : List ident) (sl1 : List statement) (a1 : expr)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp) :
        TrExprCore ce le dst (.Eaddrof e1 ty)
          (sl1 ++ final dst (CompCert4Lean.Cfrontend.SimplExpr.Eaddrof' a1 ty))
          (CompCert4Lean.Cfrontend.SimplExpr.Eaddrof' a1 ty) tmp
    | unary (le : temp_env) (dst : destination)
        (op : CompCert4Lean.Cfrontend.Cop.unary_operation) (e1 : cexpr)
        (ty : type) (tmp : List ident) (sl1 : List statement) (a1 : expr)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp) :
        TrExprCore ce le dst (.Eunop op e1 ty)
          (sl1 ++ final dst (.Eunop op a1 ty)) (.Eunop op a1 ty) tmp
    | binary (le : temp_env) (dst : destination)
        (op : CompCert4Lean.Cfrontend.Cop.binary_operation) (e1 e2 : cexpr)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le .For_val e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        TrExprCore ce le dst (.Ebinop op e1 e2 ty)
          (sl1 ++ sl2 ++ final dst (.Ebinop op a1 a2 ty))
          (.Ebinop op a1 a2 ty) tmp
    | castEffects (le : temp_env) (e1 : cexpr) (ty : type)
        (sl1 : List statement) (a1 any : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_effects e1 sl1 a1 tmp) :
        TrExprCore ce le .For_effects (.Ecast e1 ty) sl1 any tmp
    | castValue (le : temp_env) (dst : destination) (e1 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp) :
        TrExprCore ce le dst (.Ecast e1 ty)
          (sl1 ++ final dst (.Ecast a1 ty)) (.Ecast a1 ty) tmp
    | sequenceAndValue (le : temp_env) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident) (t : ident)
        (sl2 : List statement) (a2 : expr) (tmp2 tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le
          (.For_set (.SDbase type_bool ty t)) e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (htmp : t ∈ tmp) :
        TrExprCore ce le .For_val (.Eseqand e1 e2 ty)
          (sl1 ++ [specMakeIf a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
            (.Sset t (.Econst_int CompCert4Lean.Lib.Integers.Int.zero ty))])
          (.Etempvar t ty) tmp
    | sequenceAndEffects (le : temp_env) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident) (any : expr)
        (tmp : List ident) (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le .For_effects e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        TrExprCore ce le .For_effects (.Eseqand e1 e2 ty)
          (sl1 ++ [specMakeIf a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2) .Sskip]) any tmp
    | sequenceAndSet (le : temp_env) (sd : set_destination) (e1 e2 : cexpr)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (t : ident) (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
        (any : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le
          (.For_set (.SDcons type_bool ty t sd)) e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (htmp : t ∈ tmp) :
        TrExprCore ce le (.For_set sd) (.Eseqand e1 e2 ty)
          (sl1 ++ [specMakeIf a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq
              (CompCert4Lean.Cfrontend.SimplExpr.do_set sd
                (.Econst_int CompCert4Lean.Lib.Integers.Int.zero ty)))]) any tmp
    | sequenceOrValue (le : temp_env) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident) (t : ident)
        (sl2 : List statement) (a2 : expr) (tmp2 tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le
          (.For_set (.SDbase type_bool ty t)) e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (htmp : t ∈ tmp) :
        TrExprCore ce le .For_val (.Eseqor e1 e2 ty)
          (sl1 ++ [specMakeIf a1
            (.Sset t (.Econst_int CompCert4Lean.Lib.Integers.Int.one ty))
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)])
          (.Etempvar t ty) tmp
    | sequenceOrEffects (le : temp_env) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident) (any : expr)
        (tmp : List ident) (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le .For_effects e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        TrExprCore ce le .For_effects (.Eseqor e1 e2 ty)
          (sl1 ++ [specMakeIf a1 .Sskip
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)]) any tmp
    | sequenceOrSet (le : temp_env) (sd : set_destination) (e1 e2 : cexpr)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (t : ident) (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
        (any : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le
          (.For_set (.SDcons type_bool ty t sd)) e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (htmp : t ∈ tmp) :
        TrExprCore ce le (.For_set sd) (.Eseqor e1 e2 ty)
          (sl1 ++ [specMakeIf a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq
              (CompCert4Lean.Cfrontend.SimplExpr.do_set sd
                (.Econst_int CompCert4Lean.Lib.Integers.Int.one ty)))
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)]) any tmp
    | conditionValue (le : temp_env) (e1 e2 e3 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
        (sl3 : List statement) (a3 : expr) (tmp3 : List ident) (t : ident)
        (tmp : List ident) (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le (.For_set (.SDbase ty ty t)) e2 sl2 a2 tmp2)
        (h3 : TrExprCore ce le (.For_set (.SDbase ty ty t)) e3 sl3 a3 tmp3)
        (hdisjoint12 : Disjoint tmp1 tmp2) (hdisjoint13 : Disjoint tmp1 tmp3)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp)
        (hincl3 : Included tmp3 tmp) (htmp : t ∈ tmp) :
        TrExprCore ce le .For_val (.Econdition e1 e2 e3 ty)
          (sl1 ++ [specMakeIf a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl3)])
          (.Etempvar t ty) tmp
    | conditionEffects (le : temp_env) (e1 e2 e3 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
        (sl3 : List statement) (a3 : expr) (tmp3 : List ident) (any : expr)
        (tmp : List ident) (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le .For_effects e2 sl2 a2 tmp2)
        (h3 : TrExprCore ce le .For_effects e3 sl3 a3 tmp3)
        (hdisjoint12 : Disjoint tmp1 tmp2) (hdisjoint13 : Disjoint tmp1 tmp3)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp)
        (hincl3 : Included tmp3 tmp) :
        TrExprCore ce le .For_effects (.Econdition e1 e2 e3 ty)
          (sl1 ++ [specMakeIf a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl3)]) any tmp
    | conditionSet (le : temp_env) (sd : set_destination) (t : ident)
        (e1 e2 e3 : cexpr) (ty : type) (sl1 : List statement) (a1 : expr)
        (tmp1 : List ident) (sl2 : List statement) (a2 : expr)
        (tmp2 : List ident) (sl3 : List statement) (a3 : expr)
        (tmp3 : List ident) (any : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le (.For_set (.SDcons ty ty t sd)) e2 sl2 a2 tmp2)
        (h3 : TrExprCore ce le (.For_set (.SDcons ty ty t sd)) e3 sl3 a3 tmp3)
        (hdisjoint12 : Disjoint tmp1 tmp2) (hdisjoint13 : Disjoint tmp1 tmp3)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp)
        (hincl3 : Included tmp3 tmp) (htmp : t ∈ tmp) :
        TrExprCore ce le (.For_set sd) (.Econdition e1 e2 e3 ty)
          (sl1 ++ [specMakeIf a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl3)]) any tmp
    | assignEffects (le : temp_env) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
        (bf : bitfield) (any : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le .For_val e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (haccess : tr_is_bitfield_access ce a1 bf) :
        TrExprCore ce le .For_effects (.Eassign e1 e2 ty)
          (sl1 ++ sl2 ++
            [CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1 a2]) any tmp
    | assignValue (le : temp_env) (dst : destination) (e1 e2 : cexpr)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident) (t : ident)
        (tmp : List ident) (ty1 ty2 : type) (bf : bitfield)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le .For_val e2 sl2 a2 tmp2)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp)
        (hdisjoint : Disjoint tmp1 tmp2) (htmp : t ∈ tmp)
        (hnot1 : t ∉ tmp1) (hnot2 : t ∉ tmp2)
        (hty1 : ty1 = CompCert4Lean.Cfrontend.Csyntax.typeof e1)
        (hty2 : ty2 = CompCert4Lean.Cfrontend.Csyntax.typeof e2)
        (haccess : tr_is_bitfield_access ce a1 bf) :
        TrExprCore ce le dst (.Eassign e1 e2 ty)
          (sl1 ++ sl2 ++
            .Sset t (.Ecast a2 ty1) ::
            CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1 (.Etempvar t ty1) ::
            final dst (CompCert4Lean.Cfrontend.SimplExpr.make_assign_value bf
              (.Etempvar t ty1)))
          (CompCert4Lean.Cfrontend.SimplExpr.make_assign_value bf
            (.Etempvar t ty1)) tmp
    | assignOpEffects (le : temp_env)
        (op : CompCert4Lean.Cfrontend.Cop.binary_operation) (e1 e2 : cexpr)
        (tyres ty ty1 : type) (sl1 : List statement) (a1 : expr)
        (tmp1 : List ident) (sl2 : List statement) (a2 : expr)
        (tmp2 : List ident) (bf : bitfield) (sl3 : List statement)
        (a3 : expr) (tmp3 : List ident) (any : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le .For_val e2 sl2 a2 tmp2)
        (hty1 : ty1 = CompCert4Lean.Cfrontend.Csyntax.typeof e1)
        (h3 : TrRvalofCore ce ty1 a1 sl3 a3 tmp3)
        (hdisjoint12 : Disjoint tmp1 tmp2) (hdisjoint13 : Disjoint tmp1 tmp3)
        (hdisjoint23 : Disjoint tmp2 tmp3) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (hincl3 : Included tmp3 tmp)
        (haccess : tr_is_bitfield_access ce a1 bf) :
        TrExprCore ce le .For_effects (.Eassignop op e1 e2 tyres ty)
          (sl1 ++ sl2 ++ sl3 ++
            [CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1
              (.Ebinop op a3 a2 tyres)]) any tmp
    | assignOpValue (le : temp_env) (dst : destination)
        (op : CompCert4Lean.Cfrontend.Cop.binary_operation) (e1 e2 : cexpr)
        (tyres ty : type) (sl1 : List statement) (a1 : expr)
        (tmp1 : List ident) (sl2 : List statement) (a2 : expr)
        (tmp2 : List ident) (sl3 : List statement) (a3 : expr)
        (tmp3 : List ident) (t : ident) (bf : bitfield) (tmp : List ident)
        (ty1 : type) (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le .For_val e2 sl2 a2 tmp2)
        (h3 : TrRvalofCore ce ty1 a1 sl3 a3 tmp3)
        (hdisjoint12 : Disjoint tmp1 tmp2) (hdisjoint13 : Disjoint tmp1 tmp3)
        (hdisjoint23 : Disjoint tmp2 tmp3) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (hincl3 : Included tmp3 tmp)
        (htmp : t ∈ tmp) (hnot1 : t ∉ tmp1) (hnot2 : t ∉ tmp2)
        (hnot3 : t ∉ tmp3)
        (hty1 : ty1 = CompCert4Lean.Cfrontend.Csyntax.typeof e1)
        (haccess : tr_is_bitfield_access ce a1 bf) :
        TrExprCore ce le dst (.Eassignop op e1 e2 tyres ty)
          (sl1 ++ sl2 ++ sl3 ++
            .Sset t (.Ecast (.Ebinop op a3 a2 tyres) ty1) ::
            CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1 (.Etempvar t ty1) ::
            final dst (CompCert4Lean.Cfrontend.SimplExpr.make_assign_value bf
              (.Etempvar t ty1)))
          (CompCert4Lean.Cfrontend.SimplExpr.make_assign_value bf
            (.Etempvar t ty1)) tmp
    | postIncrementEffects (le : temp_env)
        (id : CompCert4Lean.Cfrontend.Cop.incr_or_decr) (e1 : cexpr)
        (ty ty1 : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident) (bf : bitfield)
        (any : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrRvalofCore ce ty1 a1 sl2 a2 tmp2)
        (hty1 : ty1 = CompCert4Lean.Cfrontend.Csyntax.typeof e1)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp)
        (hdisjoint : Disjoint tmp1 tmp2)
        (haccess : tr_is_bitfield_access ce a1 bf) :
        TrExprCore ce le .For_effects (.Epostincr id e1 ty)
          (sl1 ++ sl2 ++
            [CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1
              (CompCert4Lean.Cfrontend.SimplExpr.transl_incrdecr id a2 ty1)])
          any tmp
    | postIncrementValue (le : temp_env) (dst : destination)
        (id : CompCert4Lean.Cfrontend.Cop.incr_or_decr) (e1 : cexpr)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (bf : bitfield) (t : ident) (ty1 : type) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (hincl1 : Included tmp1 tmp) (htmp : t ∈ tmp) (hnot1 : t ∉ tmp1)
        (hty1 : ty1 = CompCert4Lean.Cfrontend.Csyntax.typeof e1)
        (haccess : tr_is_bitfield_access ce a1 bf) :
        TrExprCore ce le dst (.Epostincr id e1 ty)
          (sl1 ++
            CompCert4Lean.Cfrontend.SimplExpr.make_set bf t a1 ::
            CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1
              (CompCert4Lean.Cfrontend.SimplExpr.transl_incrdecr id
                (.Etempvar t ty1) ty1) ::
            final dst (.Etempvar t ty1))
          (.Etempvar t ty1) tmp
    | comma (le : temp_env) (dst : destination) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 tmp : List ident)
        (h1 : TrExprCore ce le .For_effects e1 sl1 a1 tmp1)
        (h2 : TrExprCore ce le dst e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        TrExprCore ce le dst (.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp
    | callEffects (le : temp_env) (e1 : cexpr) (el2 : cexprlist) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (al2 : List expr) (tmp2 : List ident)
        (any : expr) (tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprListCore ce le el2 sl2 al2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        TrExprCore ce le .For_effects (.Ecall e1 el2 ty)
          (sl1 ++ sl2 ++ [.Scall none a1 al2]) any tmp
    | callValue (le : temp_env) (dst : destination) (e1 : cexpr)
        (el2 : cexprlist) (ty : type) (sl1 : List statement) (a1 : expr)
        (tmp1 : List ident) (sl2 : List statement) (al2 : List expr)
        (tmp2 : List ident) (t : ident) (tmp : List ident)
        (hdst : dst ≠ .For_effects)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprListCore ce le el2 sl2 al2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (htmp : t ∈ tmp)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp) :
        TrExprCore ce le dst (.Ecall e1 el2 ty)
          (sl1 ++ sl2 ++ .Scall (some t) a1 al2 :: final dst (.Etempvar t ty))
          (.Etempvar t ty) tmp
    | builtinEffects (le : temp_env)
        (ef : CompCert4Lean.Common.AST.external_function) (tyargs : List type)
        (el : cexprlist) (ty : type) (sl : List statement) (al : List expr)
        (tmp1 : List ident) (any : expr) (tmp : List ident)
        (h1 : TrExprListCore ce le el sl al tmp1) (hincl : Included tmp1 tmp) :
        TrExprCore ce le .For_effects (.Ebuiltin ef tyargs el ty)
          (sl ++ [.Sbuiltin none ef tyargs al]) any tmp
    | builtinValue (le : temp_env) (dst : destination)
        (ef : CompCert4Lean.Common.AST.external_function) (tyargs : List type)
        (el : cexprlist) (ty : type) (sl : List statement) (al : List expr)
        (tmp1 : List ident) (t : ident) (tmp : List ident)
        (hdst : dst ≠ .For_effects) (h1 : TrExprListCore ce le el sl al tmp1)
        (htmp : t ∈ tmp) (hincl : Included tmp1 tmp) :
        TrExprCore ce le dst (.Ebuiltin ef tyargs el ty)
          (sl ++ .Sbuiltin (some t) ef tyargs al :: final dst (.Etempvar t ty))
          (.Etempvar t ty) tmp
    | parenthesizedValue (le : temp_env) (e1 : cexpr) (tycast ty : type)
        (sl1 : List statement) (a1 : expr) (t : ident) (tmp : List ident)
        (h1 : TrExprCore ce le
          (.For_set (.SDbase tycast ty t)) e1 sl1 a1 tmp)
        (htmp : t ∈ tmp) :
        TrExprCore ce le .For_val (.Eparen e1 tycast ty)
          sl1 (.Etempvar t ty) tmp
    | parenthesizedEffects (le : temp_env) (e1 : cexpr) (tycast ty : type)
        (sl1 : List statement) (a1 : expr) (tmp : List ident) (any : expr)
        (h1 : TrExprCore ce le .For_effects e1 sl1 a1 tmp) :
        TrExprCore ce le .For_effects (.Eparen e1 tycast ty) sl1 any tmp
    | parenthesizedSet (le : temp_env) (t : ident) (sd : set_destination)
        (e1 : cexpr) (tycast ty : type) (sl1 : List statement) (a1 : expr)
        (tmp : List ident) (any : expr)
        (h1 : TrExprCore ce le
          (.For_set (.SDcons tycast ty t sd)) e1 sl1 a1 tmp)
        (htmp : t ∈ tmp) :
        TrExprCore ce le (.For_set sd) (.Eparen e1 tycast ty) sl1 any tmp

  private inductive TrExprListCore (ce : composite_env) :
      temp_env → cexprlist → List statement → List expr → List ident → Prop where
    | empty (le : temp_env) (tmp : List ident) :
        TrExprListCore ce le .Enil [] [] tmp
    | cons (le : temp_env) (e1 : cexpr) (el2 : cexprlist)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (al2 : List expr) (tmp2 tmp : List ident)
        (h1 : TrExprCore ce le .For_val e1 sl1 a1 tmp1)
        (h2 : TrExprListCore ce le el2 sl2 al2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        TrExprListCore ce le (.Econs e1 el2) (sl1 ++ sl2) (a1 :: al2) tmp
end

def tr_expr (ce : composite_env) (le : temp_env) (dst : destination)
    (r : cexpr) (sl : List statement) (a : expr) (tmps : List ident) : Prop :=
  TrExprCore ce le dst r sl a tmps

def tr_exprlist (ce : composite_env) (le : temp_env) (rl : cexprlist)
    (sl : List statement) (al : List expr) (tmps : List ident) : Prop :=
  TrExprListCore ce le rl sl al tmps

def tr_condition_effects (ce : composite_env) :
    ∀ (le : temp_env) (e1 e2 e3 : cexpr) (ty : type)
      (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
      (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
      (sl3 : List statement) (a3 : expr) (tmp3 : List ident)
      (any : expr) (tmp : List ident),
      tr_expr ce le .For_val e1 sl1 a1 tmp1 →
      tr_expr ce le .For_effects e2 sl2 a2 tmp2 →
      tr_expr ce le .For_effects e3 sl3 a3 tmp3 →
      Disjoint tmp1 tmp2 → Disjoint tmp1 tmp3 →
      Included tmp1 tmp → Included tmp2 tmp → Included tmp3 tmp →
      tr_expr ce le .For_effects (.Econdition e1 e2 e3 ty)
        (sl1 ++ [specMakeIf a1
          (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
          (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl3)]) any tmp :=
  fun le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp
      h1 h2 h3 hd12 hd13 hi1 hi2 hi3 =>
    TrExprCore.conditionEffects le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2
      sl3 a3 tmp3 any tmp h1 h2 h3 hd12 hd13 hi1 hi2 hi3

def tr_condition_set (ce : composite_env) :
    ∀ (le : temp_env) (sd : set_destination) (t : ident)
      (e1 e2 e3 : cexpr) (ty : type) (sl1 : List statement) (a1 : expr)
      (tmp1 : List ident) (sl2 : List statement) (a2 : expr)
      (tmp2 : List ident) (sl3 : List statement) (a3 : expr)
      (tmp3 : List ident) (any : expr) (tmp : List ident),
      tr_expr ce le .For_val e1 sl1 a1 tmp1 →
      tr_expr ce le (.For_set (.SDcons ty ty t sd)) e2 sl2 a2 tmp2 →
      tr_expr ce le (.For_set (.SDcons ty ty t sd)) e3 sl3 a3 tmp3 →
      Disjoint tmp1 tmp2 → Disjoint tmp1 tmp3 →
      Included tmp1 tmp → Included tmp2 tmp → Included tmp3 tmp → t ∈ tmp →
      tr_expr ce le (.For_set sd) (.Econdition e1 e2 e3 ty)
        (sl1 ++ [specMakeIf a1
          (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
          (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl3)]) any tmp :=
  fun le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp
      h1 h2 h3 hd12 hd13 hi1 hi2 hi3 ht =>
    TrExprCore.conditionSet le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2
      sl3 a3 tmp3 any tmp h1 h2 h3 hd12 hd13 hi1 hi2 hi3 ht

def tr_paren_val (ce : composite_env) :
    ∀ (le : temp_env) (e1 : cexpr) (tycast ty : type)
      (sl1 : List statement) (a1 : expr) (t : ident) (tmp : List ident),
      tr_expr ce le (.For_set (.SDbase tycast ty t)) e1 sl1 a1 tmp →
      t ∈ tmp →
      tr_expr ce le .For_val (.Eparen e1 tycast ty) sl1 (.Etempvar t ty) tmp :=
  fun le e1 tycast ty sl1 a1 t tmp h1 ht =>
    TrExprCore.parenthesizedValue le e1 tycast ty sl1 a1 t tmp h1 ht

def tr_paren_effects (ce : composite_env) :
    ∀ (le : temp_env) (e1 : cexpr) (tycast ty : type)
      (sl1 : List statement) (a1 : expr) (tmp : List ident) (any : expr),
      tr_expr ce le .For_effects e1 sl1 a1 tmp →
      tr_expr ce le .For_effects (.Eparen e1 tycast ty) sl1 any tmp :=
  fun le e1 tycast ty sl1 a1 tmp any h1 =>
    TrExprCore.parenthesizedEffects le e1 tycast ty sl1 a1 tmp any h1

def tr_paren_set (ce : composite_env) :
    ∀ (le : temp_env) (t : ident) (sd : set_destination) (e1 : cexpr)
      (tycast ty : type) (sl1 : List statement) (a1 : expr)
      (tmp : List ident) (any : expr),
      tr_expr ce le (.For_set (.SDcons tycast ty t sd)) e1 sl1 a1 tmp →
      t ∈ tmp →
      tr_expr ce le (.For_set sd) (.Eparen e1 tycast ty) sl1 any tmp :=
  fun le t sd e1 tycast ty sl1 a1 tmp any h1 ht =>
    TrExprCore.parenthesizedSet le t sd e1 tycast ty sl1 a1 tmp any h1 ht

def tr_expr_invariantStatement : Prop :=
  ∀ (ce : composite_env) (le : temp_env) (dst : destination) (r : cexpr)
    (sl : List statement) (a : expr) (tmps : List ident),
    tr_expr ce le dst r sl a tmps →
    ∀ le', (∀ x, x ∈ tmps → PTree.get x le' = PTree.get x le) →
      tr_expr ce le' dst r sl a tmps

def tr_exprlist_invariantStatement : Prop :=
  ∀ (ce : composite_env) (le : temp_env) (rl : cexprlist)
    (sl : List statement) (al : List expr) (tmps : List ident),
    tr_exprlist ce le rl sl al tmps →
    ∀ le', (∀ x, x ∈ tmps → PTree.get x le' = PTree.get x le) →
      tr_exprlist ce le' rl sl al tmps

def tr_expr_monotoneStatement : Prop :=
  ∀ (ce : composite_env) (le : temp_env) (dst : destination) (r : cexpr)
    (sl : List statement) (a : expr) (tmps : List ident),
    tr_expr ce le dst r sl a tmps →
    ∀ tmps', Included tmps tmps' → tr_expr ce le dst r sl a tmps'

private inductive TrTopCore (ce : composite_env) (ge : genv) (e : env)
    (le : temp_env) (m : mem) :
    destination → cexpr → List statement → expr → List ident → Prop where
  | value (v : val) (ty : type) (a : expr) (tmp : List ident)
      (htype : CompCert4Lean.Cfrontend.Clight.typeof a = ty)
      (heval : CompCert4Lean.Cfrontend.Clight.eval_expr ge e le m a v) :
      TrTopCore ce ge e le m .For_val (.Eval v ty) [] a tmp
  | base (dst : destination) (r : cexpr) (sl : List statement) (a : expr)
      (tmp : List ident) (h : TrExprCore ce le dst r sl a tmp) :
      TrTopCore ce ge e le m dst r sl a tmp

def tr_top (ce : composite_env) (ge : genv) (e : env) (le : temp_env)
    (m : mem) (dst : destination) (r : cexpr) (sl : List statement)
    (a : expr) (tmps : List ident) : Prop :=
  TrTopCore ce ge e le m dst r sl a tmps

def tr_top_val_val (ce : composite_env) (ge : genv) (e : env)
    (le : temp_env) (m : mem) :
    ∀ (v : val) (ty : type) (a : expr) (tmp : List ident),
      CompCert4Lean.Cfrontend.Clight.typeof a = ty →
      CompCert4Lean.Cfrontend.Clight.eval_expr ge e le m a v →
      tr_top ce ge e le m .For_val (.Eval v ty) [] a tmp :=
  fun v ty a tmp htype heval => TrTopCore.value v ty a tmp htype heval

def tr_top_base (ce : composite_env) (ge : genv) (e : env)
    (le : temp_env) (m : mem) :
    ∀ (dst : destination) (r : cexpr) (sl : List statement) (a : expr)
      (tmp : List ident),
      tr_expr ce le dst r sl a tmp → tr_top ce ge e le m dst r sl a tmp :=
  fun dst r sl a tmp h => TrTopCore.base dst r sl a tmp h

private inductive TrExpressionCore (ce : composite_env) :
    cexpr → statement → expr → Prop where
  | intro (r : cexpr) (sl : List statement) (a : expr) (tmps : List ident)
      (h : ∀ (ge : genv) (e : env) (le : temp_env) (m : mem),
        TrTopCore ce ge e le m .For_val r sl a tmps) :
      TrExpressionCore ce r (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl) a

private inductive TrExprStmtCore (ce : composite_env) : cexpr → statement → Prop where
  | intro (r : cexpr) (sl : List statement) (a : expr) (tmps : List ident)
      (h : ∀ (ge : genv) (e : env) (le : temp_env) (m : mem),
        TrTopCore ce ge e le m .For_effects r sl a tmps) :
      TrExprStmtCore ce r (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl)

private inductive TrIfCore (ce : composite_env) :
    cexpr → statement → statement → statement → Prop where
  | intro (r : cexpr) (s1 s2 : statement) (sl : List statement) (a : expr)
      (tmps : List ident)
      (h : ∀ (ge : genv) (e : env) (le : temp_env) (m : mem),
        TrTopCore ce ge e le m .For_val r sl a tmps) :
      TrIfCore ce r s1 s2
        (CompCert4Lean.Cfrontend.SimplExpr.makeseq
          (sl ++ [specMakeIf a s1 s2]))

mutual
  private inductive TrStmtCore (ce : composite_env) :
      cstatement → statement → Prop where
    | skip : TrStmtCore ce .Sskip .Sskip
    | expression (r : cexpr) (s : statement) (h : TrExprStmtCore ce r s) :
        TrStmtCore ce (.Sdo r) s
    | sequence (s1 s2 : cstatement) (ts1 ts2 : statement)
        (h1 : TrStmtCore ce s1 ts1) (h2 : TrStmtCore ce s2 ts2) :
        TrStmtCore ce (.Ssequence s1 s2) (.Ssequence ts1 ts2)
    | ifEmpty (r : cexpr) (s' : statement) (a : expr)
        (h : TrExpressionCore ce r s' a) :
        TrStmtCore ce (.Sifthenelse r .Sskip .Sskip) (.Ssequence s' .Sskip)
    | ifThenElse (r : cexpr) (s1 s2 : cstatement) (s' : statement)
        (a : expr) (ts1 ts2 : statement) (hr : TrExpressionCore ce r s' a)
        (h1 : TrStmtCore ce s1 ts1) (h2 : TrStmtCore ce s2 ts2) :
        TrStmtCore ce (.Sifthenelse r s1 s2)
          (.Ssequence s' (.Sifthenelse a ts1 ts2))
    | whileLoop (r : cexpr) (s1 : cstatement) (s' ts1 : statement)
        (hr : TrIfCore ce r .Sskip .Sbreak s') (h1 : TrStmtCore ce s1 ts1) :
        TrStmtCore ce (.Swhile r s1)
          (.Sloop (.Ssequence s' ts1) .Sskip)
    | doWhile (r : cexpr) (s1 : cstatement) (s' ts1 : statement)
        (hr : TrIfCore ce r .Sskip .Sbreak s') (h1 : TrStmtCore ce s1 ts1) :
        TrStmtCore ce (.Sdowhile r s1) (.Sloop ts1 s')
    | forEmpty (r : cexpr) (s3 s4 : cstatement) (s' ts3 ts4 : statement)
        (hr : TrIfCore ce r .Sskip .Sbreak s') (h3 : TrStmtCore ce s3 ts3)
        (h4 : TrStmtCore ce s4 ts4) :
        TrStmtCore ce (.Sfor .Sskip r s3 s4)
          (.Sloop (.Ssequence s' ts4) ts3)
    | forNonempty (s1 : cstatement) (r : cexpr) (s3 s4 : cstatement)
        (s' ts1 ts3 ts4 : statement) (hnot : s1 ≠ .Sskip)
        (hr : TrIfCore ce r .Sskip .Sbreak s') (h1 : TrStmtCore ce s1 ts1)
        (h3 : TrStmtCore ce s3 ts3) (h4 : TrStmtCore ce s4 ts4) :
        TrStmtCore ce (.Sfor s1 r s3 s4)
          (.Ssequence ts1 (.Sloop (.Ssequence s' ts4) ts3))
    | breakStmt : TrStmtCore ce .Sbreak .Sbreak
    | continueStmt : TrStmtCore ce .Scontinue .Scontinue
    | returnNone : TrStmtCore ce (.Sreturn none) (.Sreturn none)
    | returnSome (r : cexpr) (s' : statement) (a : expr)
        (h : TrExpressionCore ce r s' a) :
        TrStmtCore ce (.Sreturn (some r)) (.Ssequence s' (.Sreturn (some a)))
    | switchStmt (r : cexpr) (ls : clabeled_statements) (s' : statement)
        (a : expr) (tls : labeled_statements) (hr : TrExpressionCore ce r s' a)
        (hls : TrLblstmtsCore ce ls tls) :
        TrStmtCore ce (.Sswitch r ls) (.Ssequence s' (.Sswitch a tls))
    | labelStmt (lbl : ident) (s : cstatement) (ts : statement)
        (h : TrStmtCore ce s ts) :
        TrStmtCore ce (.Slabel lbl s) (.Slabel lbl ts)
    | gotoStmt (lbl : ident) : TrStmtCore ce (.Sgoto lbl) (.Sgoto lbl)

  private inductive TrLblstmtsCore (ce : composite_env) :
      clabeled_statements → labeled_statements → Prop where
    | empty : TrLblstmtsCore ce .LSnil .LSnil
    | cons (c : Option Z) (s : cstatement) (ls : clabeled_statements)
        (ts : statement) (tls : labeled_statements) (hs : TrStmtCore ce s ts)
        (hls : TrLblstmtsCore ce ls tls) :
        TrLblstmtsCore ce (.LScons c s ls) (.LScons c ts tls)
end

def tr_stmt (ce : composite_env) (s : cstatement) (ts : statement) : Prop :=
  TrStmtCore ce s ts

def tr_lblstmts (ce : composite_env) (s : clabeled_statements)
    (ts : labeled_statements) : Prop :=
  TrLblstmtsCore ce s ts

def transl_stmt_meets_specStatement : Prop :=
  ∀ (ce : composite_env) (s : cstatement) (g : generator) (ts : statement)
    (g' : generator) (I : CompCert4Lean.Lib.Coqlib.Ple g.gen_next g'.gen_next),
    CompCert4Lean.Cfrontend.SimplExpr.transl_stmt ce s g =
      .Res ts g' I →
    tr_stmt ce s ts

private inductive TrFunctionCore (ce : composite_env) :
    cfunction → function → Prop where
  | intro (f : cfunction) (tf : function)
      (hbody : TrStmtCore ce f.fn_body tf.fn_body)
      (hreturn : tf.fn_return = f.fn_return)
      (hcallconv : tf.fn_callconv = f.fn_callconv)
      (hparams : tf.fn_params = f.fn_params)
      (hvars : tf.fn_vars = f.fn_vars) :
      TrFunctionCore ce f tf

def tr_function (ce : composite_env) (f : cfunction) (tf : function) : Prop :=
  TrFunctionCore ce f tf

def transl_function_specStatement : Prop :=
  ∀ (ctx : FreshIdentContext) (ce : composite_env) (f : cfunction) (tf : function),
    CompCert4Lean.Cfrontend.SimplExpr.transl_function ctx ce f = .OK tf →
    tr_function ce f tf

private inductive TrFundefCore (p : cprogram) : cfundef → fundef → Prop where
  | internal (f : cfunction) (tf : function)
      (h : TrFunctionCore p.prog_comp_env f tf) :
      TrFundefCore p (.Internal f) (.Internal tf)
  | external (ef : CompCert4Lean.Common.AST.external_function) (targs : List type)
      (tres : type) (cconv : CompCert4Lean.Common.AST.calling_convention) :
      TrFundefCore p (.External ef targs tres cconv) (.External ef targs tres cconv)

def tr_fundef (p : cprogram) (fd : cfundef) (tfd : fundef) : Prop :=
  TrFundefCore p fd tfd

def transl_fundef_specStatement : Prop :=
  ∀ (ctx : FreshIdentContext) (p : cprogram) (fd : cfundef) (tfd : fundef),
    CompCert4Lean.Cfrontend.SimplExpr.transl_fundef ctx p.prog_comp_env fd = .OK tfd →
    tr_fundef p fd tfd

end CompCert4Lean.Cfrontend.SimplExprspec
