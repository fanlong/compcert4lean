import CompCert4Lean.Cfrontend.SimplExpr

/-!
# Relational specification of expression simplification

Definition-bearing translation of the selected surface of CompCert's
`cfrontend/SimplExprspec.v`.  The selected primary relations are represented
directly as public inductives, with mapped constructor identities exposed under
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
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

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

inductive tr_rvalof (ce : composite_env) :
    type → expr → List statement → expr → List ident → Prop where
  | tr_rvalof_nonvol (ty : type) (a : expr) (tmp : List ident)
      (hvolatile : type_is_volatile ty = false) :
      tr_rvalof ce ty a [] a tmp
  | tr_rvalof_vol (ty : type) (a : expr) (t : ident) (bf : bitfield)
      (tmp : List ident) (hvolatile : type_is_volatile ty = true)
      (htmp : t ∈ tmp) (haccess : tr_is_bitfield_access ce a bf) :
      tr_rvalof ce ty a
        [CompCert4Lean.Cfrontend.SimplExpr.make_set bf t a]
        (.Etempvar t ty) tmp

mutual
  inductive tr_expr
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ce : composite_env) :
      temp_env → destination → cexpr → List statement → expr → List ident → Prop where
    | tr_var (le : temp_env) (dst : destination) (id : ident) (ty : type)
        (tmp : List ident) :
        tr_expr ce le dst (.Evar id ty)
          (final dst (.Evar id ty)) (.Evar id ty) tmp
    | tr_deref (le : temp_env) (dst : destination) (e1 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp) :
        tr_expr ce le dst (.Ederef e1 ty)
          (sl1 ++ final dst (CompCert4Lean.Cfrontend.SimplExpr.Ederef' a1 ty))
          (CompCert4Lean.Cfrontend.SimplExpr.Ederef' a1 ty) tmp
    | tr_field (le : temp_env) (dst : destination) (e1 : cexpr) (f : ident)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp) :
        tr_expr ce le dst (.Efield e1 f ty)
          (sl1 ++ final dst (.Efield a1 f ty)) (.Efield a1 f ty) tmp
    | tr_val_effect (le : temp_env) (v : val) (ty : type) (any : expr)
        (tmp : List ident) :
        tr_expr ce le .For_effects (.Eval v ty) [] any tmp
    | tr_val_value (le : temp_env) (v : val) (ty : type) (a : expr)
        (tmp : List ident) (htype : CompCert4Lean.Cfrontend.Clight.typeof a = ty)
        (heval : ∀ (tge : genv) (e : env) (le' : temp_env) (m : mem),
          (∀ id, id ∈ tmp → PTree.get id le' = PTree.get id le) →
          CompCert4Lean.Cfrontend.Clight.eval_expr
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) tge e le' m a v) :
        tr_expr ce le .For_val (.Eval v ty) [] a tmp
    | tr_val_set (le : temp_env) (sd : set_destination) (v : val) (ty : type)
        (a any : expr) (tmp : List ident)
        (htype : CompCert4Lean.Cfrontend.Clight.typeof a = ty)
        (heval : ∀ (tge : genv) (e : env) (le' : temp_env) (m : mem),
          (∀ id, id ∈ tmp → PTree.get id le' = PTree.get id le) →
          CompCert4Lean.Cfrontend.Clight.eval_expr
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) tge e le' m a v) :
        tr_expr ce le (.For_set sd) (.Eval v ty)
          (CompCert4Lean.Cfrontend.SimplExpr.do_set sd a) any tmp
    | tr_sizeof (le : temp_env) (dst : destination) (ty' ty : type)
        (tmp : List ident) :
        tr_expr ce le dst (.Esizeof ty' ty)
          (final dst (.Esizeof ty' ty)) (.Esizeof ty' ty) tmp
    | tr_alignof (le : temp_env) (dst : destination) (ty' ty : type)
        (tmp : List ident) :
        tr_expr ce le dst (.Ealignof ty' ty)
          (final dst (.Ealignof ty' ty)) (.Ealignof ty' ty) tmp
    | tr_valof (le : temp_env) (dst : destination) (e1 : cexpr) (ty : type)
        (tmp : List ident) (sl1 : List statement) (a1 : expr)
        (tmp1 : List ident) (sl2 : List statement) (a2 : expr)
        (tmp2 : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_rvalof ce (CompCert4Lean.Cfrontend.Csyntax.typeof e1)
          a1 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        tr_expr ce le dst (.Evalof e1 ty)
          (sl1 ++ sl2 ++ final dst a2) a2 tmp
    | tr_addrof (le : temp_env) (dst : destination) (e1 : cexpr) (ty : type)
        (tmp : List ident) (sl1 : List statement) (a1 : expr)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp) :
        tr_expr ce le dst (.Eaddrof e1 ty)
          (sl1 ++ final dst (CompCert4Lean.Cfrontend.SimplExpr.Eaddrof' a1 ty))
          (CompCert4Lean.Cfrontend.SimplExpr.Eaddrof' a1 ty) tmp
    | tr_unop (le : temp_env) (dst : destination)
        (op : CompCert4Lean.Cfrontend.Cop.unary_operation) (e1 : cexpr)
        (ty : type) (tmp : List ident) (sl1 : List statement) (a1 : expr)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp) :
        tr_expr ce le dst (.Eunop op e1 ty)
          (sl1 ++ final dst (.Eunop op a1 ty)) (.Eunop op a1 ty) tmp
    | tr_binop (le : temp_env) (dst : destination)
        (op : CompCert4Lean.Cfrontend.Cop.binary_operation) (e1 e2 : cexpr)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le .For_val e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        tr_expr ce le dst (.Ebinop op e1 e2 ty)
          (sl1 ++ sl2 ++ final dst (.Ebinop op a1 a2 ty))
          (.Ebinop op a1 a2 ty) tmp
    | tr_cast_effects (le : temp_env) (e1 : cexpr) (ty : type)
        (sl1 : List statement) (a1 any : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_effects e1 sl1 a1 tmp) :
        tr_expr ce le .For_effects (.Ecast e1 ty) sl1 any tmp
    | tr_cast_val (le : temp_env) (dst : destination) (e1 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp) :
        tr_expr ce le dst (.Ecast e1 ty)
          (sl1 ++ final dst (.Ecast a1 ty)) (.Ecast a1 ty) tmp
    | tr_seqand_val (le : temp_env) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident) (t : ident)
        (sl2 : List statement) (a2 : expr) (tmp2 tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le
          (.For_set (.SDbase type_bool ty t)) e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (htmp : t ∈ tmp) :
        tr_expr ce le .For_val (.Eseqand e1 e2 ty)
          (sl1 ++ [CompCert4Lean.Cfrontend.SimplExpr.makeif a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
            (.Sset t (.Econst_int CompCert4Lean.Lib.Integers.Int.zero ty))])
          (.Etempvar t ty) tmp
    | tr_seqand_effects (le : temp_env) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident) (any : expr)
        (tmp : List ident) (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le .For_effects e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        tr_expr ce le .For_effects (.Eseqand e1 e2 ty)
          (sl1 ++ [CompCert4Lean.Cfrontend.SimplExpr.makeif a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2) .Sskip]) any tmp
    | tr_seqand_set (le : temp_env) (sd : set_destination) (e1 e2 : cexpr)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (t : ident) (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
        (any : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le
          (.For_set (.SDcons type_bool ty t sd)) e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (htmp : t ∈ tmp) :
        tr_expr ce le (.For_set sd) (.Eseqand e1 e2 ty)
          (sl1 ++ [CompCert4Lean.Cfrontend.SimplExpr.makeif a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq
              (CompCert4Lean.Cfrontend.SimplExpr.do_set sd
                (.Econst_int CompCert4Lean.Lib.Integers.Int.zero ty)))]) any tmp
    | tr_seqor_val (le : temp_env) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident) (t : ident)
        (sl2 : List statement) (a2 : expr) (tmp2 tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le
          (.For_set (.SDbase type_bool ty t)) e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (htmp : t ∈ tmp) :
        tr_expr ce le .For_val (.Eseqor e1 e2 ty)
          (sl1 ++ [CompCert4Lean.Cfrontend.SimplExpr.makeif a1
            (.Sset t (.Econst_int CompCert4Lean.Lib.Integers.Int.one ty))
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)])
          (.Etempvar t ty) tmp
    | tr_seqor_effects (le : temp_env) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident) (any : expr)
        (tmp : List ident) (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le .For_effects e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        tr_expr ce le .For_effects (.Eseqor e1 e2 ty)
          (sl1 ++ [CompCert4Lean.Cfrontend.SimplExpr.makeif a1 .Sskip
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)]) any tmp
    | tr_seqor_set (le : temp_env) (sd : set_destination) (e1 e2 : cexpr)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (t : ident) (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
        (any : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le
          (.For_set (.SDcons type_bool ty t sd)) e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (htmp : t ∈ tmp) :
        tr_expr ce le (.For_set sd) (.Eseqor e1 e2 ty)
          (sl1 ++ [CompCert4Lean.Cfrontend.SimplExpr.makeif a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq
              (CompCert4Lean.Cfrontend.SimplExpr.do_set sd
                (.Econst_int CompCert4Lean.Lib.Integers.Int.one ty)))
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)]) any tmp
    | tr_condition_val (le : temp_env) (e1 e2 e3 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
        (sl3 : List statement) (a3 : expr) (tmp3 : List ident) (t : ident)
        (tmp : List ident) (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le (.For_set (.SDbase ty ty t)) e2 sl2 a2 tmp2)
        (h3 : tr_expr ce le (.For_set (.SDbase ty ty t)) e3 sl3 a3 tmp3)
        (hdisjoint12 : Disjoint tmp1 tmp2) (hdisjoint13 : Disjoint tmp1 tmp3)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp)
        (hincl3 : Included tmp3 tmp) (htmp : t ∈ tmp) :
        tr_expr ce le .For_val (.Econdition e1 e2 e3 ty)
          (sl1 ++ [CompCert4Lean.Cfrontend.SimplExpr.makeif a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl3)])
          (.Etempvar t ty) tmp
    | tr_condition_effects (le : temp_env) (e1 e2 e3 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
        (sl3 : List statement) (a3 : expr) (tmp3 : List ident) (any : expr)
        (tmp : List ident) (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le .For_effects e2 sl2 a2 tmp2)
        (h3 : tr_expr ce le .For_effects e3 sl3 a3 tmp3)
        (hdisjoint12 : Disjoint tmp1 tmp2) (hdisjoint13 : Disjoint tmp1 tmp3)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp)
        (hincl3 : Included tmp3 tmp) :
        tr_expr ce le .For_effects (.Econdition e1 e2 e3 ty)
          (sl1 ++ [CompCert4Lean.Cfrontend.SimplExpr.makeif a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl3)]) any tmp
    | tr_condition_set (le : temp_env) (sd : set_destination) (t : ident)
        (e1 e2 e3 : cexpr) (ty : type) (sl1 : List statement) (a1 : expr)
        (tmp1 : List ident) (sl2 : List statement) (a2 : expr)
        (tmp2 : List ident) (sl3 : List statement) (a3 : expr)
        (tmp3 : List ident) (any : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le (.For_set (.SDcons ty ty t sd)) e2 sl2 a2 tmp2)
        (h3 : tr_expr ce le (.For_set (.SDcons ty ty t sd)) e3 sl3 a3 tmp3)
        (hdisjoint12 : Disjoint tmp1 tmp2) (hdisjoint13 : Disjoint tmp1 tmp3)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp)
        (hincl3 : Included tmp3 tmp) (htmp : t ∈ tmp) :
        tr_expr ce le (.For_set sd) (.Econdition e1 e2 e3 ty)
          (sl1 ++ [CompCert4Lean.Cfrontend.SimplExpr.makeif a1
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl2)
            (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl3)]) any tmp
    | tr_assign_effects (le : temp_env) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident)
        (bf : bitfield) (any : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le .For_val e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (haccess : tr_is_bitfield_access ce a1 bf) :
        tr_expr ce le .For_effects (.Eassign e1 e2 ty)
          (sl1 ++ sl2 ++
            [CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1 a2]) any tmp
    | tr_assign_val (le : temp_env) (dst : destination) (e1 e2 : cexpr)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident) (t : ident)
        (tmp : List ident) (ty1 ty2 : type) (bf : bitfield)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le .For_val e2 sl2 a2 tmp2)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp)
        (hdisjoint : Disjoint tmp1 tmp2) (htmp : t ∈ tmp)
        (hnot1 : t ∉ tmp1) (hnot2 : t ∉ tmp2)
        (hty1 : ty1 = CompCert4Lean.Cfrontend.Csyntax.typeof e1)
        (hty2 : ty2 = CompCert4Lean.Cfrontend.Csyntax.typeof e2)
        (haccess : tr_is_bitfield_access ce a1 bf) :
        tr_expr ce le dst (.Eassign e1 e2 ty)
          (sl1 ++ sl2 ++
            .Sset t (.Ecast a2 ty1) ::
            CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1 (.Etempvar t ty1) ::
            final dst (CompCert4Lean.Cfrontend.SimplExpr.make_assign_value bf
              (.Etempvar t ty1)))
          (CompCert4Lean.Cfrontend.SimplExpr.make_assign_value bf
            (.Etempvar t ty1)) tmp
    | tr_assignop_effects (le : temp_env)
        (op : CompCert4Lean.Cfrontend.Cop.binary_operation) (e1 e2 : cexpr)
        (tyres ty ty1 : type) (sl1 : List statement) (a1 : expr)
        (tmp1 : List ident) (sl2 : List statement) (a2 : expr)
        (tmp2 : List ident) (bf : bitfield) (sl3 : List statement)
        (a3 : expr) (tmp3 : List ident) (any : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le .For_val e2 sl2 a2 tmp2)
        (hty1 : ty1 = CompCert4Lean.Cfrontend.Csyntax.typeof e1)
        (h3 : tr_rvalof ce ty1 a1 sl3 a3 tmp3)
        (hdisjoint12 : Disjoint tmp1 tmp2) (hdisjoint13 : Disjoint tmp1 tmp3)
        (hdisjoint23 : Disjoint tmp2 tmp3) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (hincl3 : Included tmp3 tmp)
        (haccess : tr_is_bitfield_access ce a1 bf) :
        tr_expr ce le .For_effects (.Eassignop op e1 e2 tyres ty)
          (sl1 ++ sl2 ++ sl3 ++
            [CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1
              (.Ebinop op a3 a2 tyres)]) any tmp
    | tr_assignop_val (le : temp_env) (dst : destination)
        (op : CompCert4Lean.Cfrontend.Cop.binary_operation) (e1 e2 : cexpr)
        (tyres ty : type) (sl1 : List statement) (a1 : expr)
        (tmp1 : List ident) (sl2 : List statement) (a2 : expr)
        (tmp2 : List ident) (sl3 : List statement) (a3 : expr)
        (tmp3 : List ident) (t : ident) (bf : bitfield) (tmp : List ident)
        (ty1 : type) (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le .For_val e2 sl2 a2 tmp2)
        (h3 : tr_rvalof ce ty1 a1 sl3 a3 tmp3)
        (hdisjoint12 : Disjoint tmp1 tmp2) (hdisjoint13 : Disjoint tmp1 tmp3)
        (hdisjoint23 : Disjoint tmp2 tmp3) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) (hincl3 : Included tmp3 tmp)
        (htmp : t ∈ tmp) (hnot1 : t ∉ tmp1) (hnot2 : t ∉ tmp2)
        (hnot3 : t ∉ tmp3)
        (hty1 : ty1 = CompCert4Lean.Cfrontend.Csyntax.typeof e1)
        (haccess : tr_is_bitfield_access ce a1 bf) :
        tr_expr ce le dst (.Eassignop op e1 e2 tyres ty)
          (sl1 ++ sl2 ++ sl3 ++
            .Sset t (.Ecast (.Ebinop op a3 a2 tyres) ty1) ::
            CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1 (.Etempvar t ty1) ::
            final dst (CompCert4Lean.Cfrontend.SimplExpr.make_assign_value bf
              (.Etempvar t ty1)))
          (CompCert4Lean.Cfrontend.SimplExpr.make_assign_value bf
            (.Etempvar t ty1)) tmp
    | tr_postincr_effects (le : temp_env)
        (id : CompCert4Lean.Cfrontend.Cop.incr_or_decr) (e1 : cexpr)
        (ty ty1 : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 : List ident) (bf : bitfield)
        (any : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_rvalof ce ty1 a1 sl2 a2 tmp2)
        (hty1 : ty1 = CompCert4Lean.Cfrontend.Csyntax.typeof e1)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp)
        (hdisjoint : Disjoint tmp1 tmp2)
        (haccess : tr_is_bitfield_access ce a1 bf) :
        tr_expr ce le .For_effects (.Epostincr id e1 ty)
          (sl1 ++ sl2 ++
            [CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1
              (CompCert4Lean.Cfrontend.SimplExpr.transl_incrdecr id a2 ty1)])
          any tmp
    | tr_postincr_val (le : temp_env) (dst : destination)
        (id : CompCert4Lean.Cfrontend.Cop.incr_or_decr) (e1 : cexpr)
        (ty : type) (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (bf : bitfield) (t : ident) (ty1 : type) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (hincl1 : Included tmp1 tmp) (htmp : t ∈ tmp) (hnot1 : t ∉ tmp1)
        (hty1 : ty1 = CompCert4Lean.Cfrontend.Csyntax.typeof e1)
        (haccess : tr_is_bitfield_access ce a1 bf) :
        tr_expr ce le dst (.Epostincr id e1 ty)
          (sl1 ++
            CompCert4Lean.Cfrontend.SimplExpr.make_set bf t a1 ::
            CompCert4Lean.Cfrontend.SimplExpr.make_assign bf a1
              (CompCert4Lean.Cfrontend.SimplExpr.transl_incrdecr id
                (.Etempvar t ty1) ty1) ::
            final dst (.Etempvar t ty1))
          (.Etempvar t ty1) tmp
    | tr_comma (le : temp_env) (dst : destination) (e1 e2 : cexpr) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (a2 : expr) (tmp2 tmp : List ident)
        (h1 : tr_expr ce le .For_effects e1 sl1 a1 tmp1)
        (h2 : tr_expr ce le dst e2 sl2 a2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        tr_expr ce le dst (.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp
    | tr_call_effects (le : temp_env) (e1 : cexpr) (el2 : cexprlist) (ty : type)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (al2 : List expr) (tmp2 : List ident)
        (any : expr) (tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_exprlist ce le el2 sl2 al2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        tr_expr ce le .For_effects (.Ecall e1 el2 ty)
          (sl1 ++ sl2 ++ [.Scall none a1 al2]) any tmp
    | tr_call_val (le : temp_env) (dst : destination) (e1 : cexpr)
        (el2 : cexprlist) (ty : type) (sl1 : List statement) (a1 : expr)
        (tmp1 : List ident) (sl2 : List statement) (al2 : List expr)
        (tmp2 : List ident) (t : ident) (tmp : List ident)
        (hdst : dst ≠ .For_effects)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_exprlist ce le el2 sl2 al2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (htmp : t ∈ tmp)
        (hincl1 : Included tmp1 tmp) (hincl2 : Included tmp2 tmp) :
        tr_expr ce le dst (.Ecall e1 el2 ty)
          (sl1 ++ sl2 ++ .Scall (some t) a1 al2 :: final dst (.Etempvar t ty))
          (.Etempvar t ty) tmp
    | tr_builtin_effects (le : temp_env)
        (ef : CompCert4Lean.Common.AST.external_function) (tyargs : List type)
        (el : cexprlist) (ty : type) (sl : List statement) (al : List expr)
        (tmp1 : List ident) (any : expr) (tmp : List ident)
        (h1 : tr_exprlist ce le el sl al tmp1) (hincl : Included tmp1 tmp) :
        tr_expr ce le .For_effects (.Ebuiltin ef tyargs el ty)
          (sl ++ [.Sbuiltin none ef tyargs al]) any tmp
    | tr_builtin_val (le : temp_env) (dst : destination)
        (ef : CompCert4Lean.Common.AST.external_function) (tyargs : List type)
        (el : cexprlist) (ty : type) (sl : List statement) (al : List expr)
        (tmp1 : List ident) (t : ident) (tmp : List ident)
        (hdst : dst ≠ .For_effects) (h1 : tr_exprlist ce le el sl al tmp1)
        (htmp : t ∈ tmp) (hincl : Included tmp1 tmp) :
        tr_expr ce le dst (.Ebuiltin ef tyargs el ty)
          (sl ++ .Sbuiltin (some t) ef tyargs al :: final dst (.Etempvar t ty))
          (.Etempvar t ty) tmp
    | tr_paren_val (le : temp_env) (e1 : cexpr) (tycast ty : type)
        (sl1 : List statement) (a1 : expr) (t : ident) (tmp : List ident)
        (h1 : tr_expr ce le
          (.For_set (.SDbase tycast ty t)) e1 sl1 a1 tmp)
        (htmp : t ∈ tmp) :
        tr_expr ce le .For_val (.Eparen e1 tycast ty)
          sl1 (.Etempvar t ty) tmp
    | tr_paren_effects (le : temp_env) (e1 : cexpr) (tycast ty : type)
        (sl1 : List statement) (a1 : expr) (tmp : List ident) (any : expr)
        (h1 : tr_expr ce le .For_effects e1 sl1 a1 tmp) :
        tr_expr ce le .For_effects (.Eparen e1 tycast ty) sl1 any tmp
    | tr_paren_set (le : temp_env) (t : ident) (sd : set_destination)
        (e1 : cexpr) (tycast ty : type) (sl1 : List statement) (a1 : expr)
        (tmp : List ident) (any : expr)
        (h1 : tr_expr ce le
          (.For_set (.SDcons tycast ty t sd)) e1 sl1 a1 tmp)
        (htmp : t ∈ tmp) :
        tr_expr ce le (.For_set sd) (.Eparen e1 tycast ty) sl1 any tmp

  inductive tr_exprlist
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ce : composite_env) :
      temp_env → cexprlist → List statement → List expr → List ident → Prop where
    | tr_nil (le : temp_env) (tmp : List ident) :
        tr_exprlist ce le .Enil [] [] tmp
    | tr_cons (le : temp_env) (e1 : cexpr) (el2 : cexprlist)
        (sl1 : List statement) (a1 : expr) (tmp1 : List ident)
        (sl2 : List statement) (al2 : List expr) (tmp2 tmp : List ident)
        (h1 : tr_expr ce le .For_val e1 sl1 a1 tmp1)
        (h2 : tr_exprlist ce le el2 sl2 al2 tmp2)
        (hdisjoint : Disjoint tmp1 tmp2) (hincl1 : Included tmp1 tmp)
        (hincl2 : Included tmp2 tmp) :
        tr_exprlist ce le (.Econs e1 el2) (sl1 ++ sl2) (a1 :: al2) tmp
end

export tr_expr
  (tr_condition_effects tr_condition_set tr_paren_val tr_paren_effects
    tr_paren_set)

abbrev tr_condition_effects := @tr_expr.tr_condition_effects
abbrev tr_condition_set := @tr_expr.tr_condition_set
abbrev tr_paren_val := @tr_expr.tr_paren_val
abbrev tr_paren_effects := @tr_expr.tr_paren_effects
abbrev tr_paren_set := @tr_expr.tr_paren_set

def tr_expr_invariantStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ce : composite_env) (le : temp_env) (dst : destination) (r : cexpr)
    (sl : List statement) (a : expr) (tmps : List ident),
    tr_expr ce le dst r sl a tmps →
    ∀ le', (∀ x, x ∈ tmps → PTree.get x le' = PTree.get x le) →
      tr_expr ce le' dst r sl a tmps

def tr_exprlist_invariantStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ce : composite_env) (le : temp_env) (rl : cexprlist)
    (sl : List statement) (al : List expr) (tmps : List ident),
    tr_exprlist ce le rl sl al tmps →
    ∀ le', (∀ x, x ∈ tmps → PTree.get x le' = PTree.get x le) →
      tr_exprlist ce le' rl sl al tmps

def tr_expr_monotoneStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ce : composite_env) (le : temp_env) (dst : destination) (r : cexpr)
    (sl : List statement) (a : expr) (tmps : List ident),
    tr_expr ce le dst r sl a tmps →
    ∀ tmps', Included tmps tmps' → tr_expr ce le dst r sl a tmps'

inductive tr_top
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ce : composite_env) (ge : genv) (e : env)
    (le : temp_env) (m : mem) :
    destination → cexpr → List statement → expr → List ident → Prop where
  | tr_top_val_val (v : val) (ty : type) (a : expr) (tmp : List ident)
      (htype : CompCert4Lean.Cfrontend.Clight.typeof a = ty)
      (heval : CompCert4Lean.Cfrontend.Clight.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v) :
      tr_top ce ge e le m .For_val (.Eval v ty) [] a tmp
  | tr_top_base (dst : destination) (r : cexpr) (sl : List statement) (a : expr)
      (tmp : List ident) (h : tr_expr ce le dst r sl a tmp) :
      tr_top ce ge e le m dst r sl a tmp

export tr_top (tr_top_val_val tr_top_base)

abbrev tr_top_val_val := @tr_top.tr_top_val_val
abbrev tr_top_base := @tr_top.tr_top_base

inductive tr_expression
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ce : composite_env) :
    cexpr → statement → expr → Prop where
  | tr_expression_intro (r : cexpr) (sl : List statement) (a : expr)
      (tmps : List ident)
      (h : ∀ (ge : genv) (e : env) (le : temp_env) (m : mem),
        tr_top ce ge e le m .For_val r sl a tmps) :
      tr_expression ce r (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl) a

inductive tr_expr_stmt
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ce : composite_env) : cexpr → statement → Prop where
  | tr_expr_stmt_intro (r : cexpr) (sl : List statement) (a : expr)
      (tmps : List ident)
      (h : ∀ (ge : genv) (e : env) (le : temp_env) (m : mem),
        tr_top ce ge e le m .For_effects r sl a tmps) :
      tr_expr_stmt ce r (CompCert4Lean.Cfrontend.SimplExpr.makeseq sl)

inductive tr_if
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ce : composite_env) :
    cexpr → statement → statement → statement → Prop where
  | tr_if_intro (r : cexpr) (s1 s2 : statement) (sl : List statement)
      (a : expr) (tmps : List ident)
      (h : ∀ (ge : genv) (e : env) (le : temp_env) (m : mem),
        tr_top ce ge e le m .For_val r sl a tmps) :
      tr_if ce r s1 s2
        (CompCert4Lean.Cfrontend.SimplExpr.makeseq
          (sl ++ [CompCert4Lean.Cfrontend.SimplExpr.makeif a s1 s2]))

export tr_expression (tr_expression_intro)
export tr_expr_stmt (tr_expr_stmt_intro)
export tr_if (tr_if_intro)

mutual
  inductive tr_stmt
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ce : composite_env) :
      cstatement → statement → Prop where
    | tr_skip : tr_stmt ce .Sskip .Sskip
    | tr_do (r : cexpr) (s : statement) (h : tr_expr_stmt ce r s) :
        tr_stmt ce (.Sdo r) s
    | tr_seq (s1 s2 : cstatement) (ts1 ts2 : statement)
        (h1 : tr_stmt ce s1 ts1) (h2 : tr_stmt ce s2 ts2) :
        tr_stmt ce (.Ssequence s1 s2) (.Ssequence ts1 ts2)
    | tr_ifthenelse_empty (r : cexpr) (s' : statement) (a : expr)
        (h : tr_expression ce r s' a) :
        tr_stmt ce (.Sifthenelse r .Sskip .Sskip) (.Ssequence s' .Sskip)
    | tr_ifthenelse (r : cexpr) (s1 s2 : cstatement) (s' : statement)
        (a : expr) (ts1 ts2 : statement) (hr : tr_expression ce r s' a)
        (h1 : tr_stmt ce s1 ts1) (h2 : tr_stmt ce s2 ts2) :
        tr_stmt ce (.Sifthenelse r s1 s2)
          (.Ssequence s' (.Sifthenelse a ts1 ts2))
    | tr_while (r : cexpr) (s1 : cstatement) (s' ts1 : statement)
        (hr : tr_if ce r .Sskip .Sbreak s') (h1 : tr_stmt ce s1 ts1) :
        tr_stmt ce (.Swhile r s1)
          (.Sloop (.Ssequence s' ts1) .Sskip)
    | tr_dowhile (r : cexpr) (s1 : cstatement) (s' ts1 : statement)
        (hr : tr_if ce r .Sskip .Sbreak s') (h1 : tr_stmt ce s1 ts1) :
        tr_stmt ce (.Sdowhile r s1) (.Sloop ts1 s')
    | tr_for_1 (r : cexpr) (s3 s4 : cstatement) (s' ts3 ts4 : statement)
        (hr : tr_if ce r .Sskip .Sbreak s') (h3 : tr_stmt ce s3 ts3)
        (h4 : tr_stmt ce s4 ts4) :
        tr_stmt ce (.Sfor .Sskip r s3 s4)
          (.Sloop (.Ssequence s' ts4) ts3)
    | tr_for_2 (s1 : cstatement) (r : cexpr) (s3 s4 : cstatement)
        (s' ts1 ts3 ts4 : statement)
        (hr : tr_if ce r .Sskip .Sbreak s') (hnot : s1 ≠ .Sskip)
        (h1 : tr_stmt ce s1 ts1)
        (h3 : tr_stmt ce s3 ts3) (h4 : tr_stmt ce s4 ts4) :
        tr_stmt ce (.Sfor s1 r s3 s4)
          (.Ssequence ts1 (.Sloop (.Ssequence s' ts4) ts3))
    | tr_break : tr_stmt ce .Sbreak .Sbreak
    | tr_continue : tr_stmt ce .Scontinue .Scontinue
    | tr_return_none : tr_stmt ce (.Sreturn none) (.Sreturn none)
    | tr_return_some (r : cexpr) (s' : statement) (a : expr)
        (h : tr_expression ce r s' a) :
        tr_stmt ce (.Sreturn (some r)) (.Ssequence s' (.Sreturn (some a)))
    | tr_switch (r : cexpr) (ls : clabeled_statements) (s' : statement)
        (a : expr) (tls : labeled_statements) (hr : tr_expression ce r s' a)
        (hls : tr_lblstmts ce ls tls) :
        tr_stmt ce (.Sswitch r ls) (.Ssequence s' (.Sswitch a tls))
    | tr_label (lbl : ident) (s : cstatement) (ts : statement)
        (h : tr_stmt ce s ts) :
        tr_stmt ce (.Slabel lbl s) (.Slabel lbl ts)
    | tr_goto (lbl : ident) : tr_stmt ce (.Sgoto lbl) (.Sgoto lbl)

  inductive tr_lblstmts
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ce : composite_env) :
      clabeled_statements → labeled_statements → Prop where
    | tr_ls_nil : tr_lblstmts ce .LSnil .LSnil
    | tr_ls_cons (c : Option Z) (s : cstatement) (ls : clabeled_statements)
        (ts : statement) (tls : labeled_statements) (hs : tr_stmt ce s ts)
        (hls : tr_lblstmts ce ls tls) :
        tr_lblstmts ce (.LScons c s ls) (.LScons c ts tls)
end

def transl_stmt_meets_specStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ce : composite_env) (s : cstatement) (g : generator) (ts : statement)
    (g' : generator) (I : CompCert4Lean.Lib.Coqlib.Ple g.gen_next g'.gen_next),
    CompCert4Lean.Cfrontend.SimplExpr.transl_stmt ce s g =
      .Res ts g' I →
    tr_stmt ce s ts

inductive tr_function
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ce : composite_env) :
    cfunction → function → Prop where
  | tr_function_intro (f : cfunction) (tf : function)
      (hbody : tr_stmt ce f.fn_body tf.fn_body)
      (hreturn : tf.fn_return = f.fn_return)
      (hcallconv : tf.fn_callconv = f.fn_callconv)
      (hparams : tf.fn_params = f.fn_params)
      (hvars : tf.fn_vars = f.fn_vars) :
      tr_function ce f tf

def transl_function_specStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ctx : FreshIdentContext) (ce : composite_env) (f : cfunction) (tf : function),
    CompCert4Lean.Cfrontend.SimplExpr.transl_function ctx ce f = .OK tf →
    tr_function ce f tf

inductive tr_fundef
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (p : cprogram) : cfundef → fundef → Prop where
  | tr_internal (f : cfunction) (tf : function)
      (h : tr_function p.prog_comp_env f tf) :
      tr_fundef p (.Internal f) (.Internal tf)
  | tr_external (ef : CompCert4Lean.Common.AST.external_function) (targs : List type)
      (tres : type) (cconv : CompCert4Lean.Common.AST.calling_convention) :
      tr_fundef p (.External ef targs tres cconv) (.External ef targs tres cconv)

def transl_fundef_specStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ctx : FreshIdentContext) (p : cprogram) (fd : cfundef) (tfd : fundef),
    CompCert4Lean.Cfrontend.SimplExpr.transl_fundef ctx p.prog_comp_env fd = .OK tfd →
    tr_fundef p fd tfd

end CompCert4Lean.Cfrontend.SimplExprspec

namespace CompCert4Lean.Cfrontend.SimplExprspec

private theorem agree_mono {A B : Type} {xs ys : List A} {f g : A → B}
    (hsub : ∀ x, x ∈ xs → x ∈ ys)
    (h : ∀ x, x ∈ ys → f x = g x) :
    ∀ x, x ∈ xs → f x = g x := by
  intro x hx
  exact h x (hsub x hx)

theorem tr_exprlist_invariant
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    tr_exprlist_invariantStatement := by
  intro ce le rl sl al tmps h
  intro le' hle
  revert le' hle
  let P1 := fun (dst : destination) (r : cexpr) (sl : List statement)
      (a : expr) (tmps : List ident) (_ : tr_expr ce le dst r sl a tmps) =>
      ∀ le', (∀ x, x ∈ tmps →
        CompCert4Lean.Lib.Maps.PTree.get x le' = CompCert4Lean.Lib.Maps.PTree.get x le) →
        tr_expr ce le' dst r sl a tmps
  let P2 := fun (rl : cexprlist) (sl : List statement)
      (al : List expr) (tmps : List ident) (_ : tr_exprlist ce le rl sl al tmps) =>
      ∀ le', (∀ x, x ∈ tmps →
        CompCert4Lean.Lib.Maps.PTree.get x le' = CompCert4Lean.Lib.Maps.PTree.get x le) →
        tr_exprlist ce le' rl sl al tmps
  refine tr_exprlist.rec (motive_1 := P1) (motive_2 := P2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros <;> dsimp [P1, P2, Included] at * <;> intro le' hle <;> constructor <;>
      try solve_by_elim [agree_mono] <;>
      try (intro tge e le1 m hle1; solve_by_elim [agree_mono])
  all_goals
    intro tge e le1 m hle1
    apply_assumption
    intro id hid
    exact Eq.trans (hle1 id hid) (hle id hid)

end CompCert4Lean.Cfrontend.SimplExprspec

namespace CompCert4Lean.Cfrontend.SimplExprspec

theorem tr_expr_monotone
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    tr_expr_monotoneStatement := by
  intro ce le dst r sl a tmps h
  intro tmps' htmps
  revert tmps' htmps
  let P1 := fun (dst : destination) (r : cexpr) (sl : List statement)
      (a : expr) (tmps : List ident) (_ : tr_expr ce le dst r sl a tmps) =>
      ∀ tmps', Included tmps tmps' → tr_expr ce le dst r sl a tmps'
  let P2 := fun (rl : cexprlist) (sl : List statement)
      (al : List expr) (tmps : List ident) (_ : tr_exprlist ce le rl sl al tmps) =>
      ∀ tmps', Included tmps tmps' → tr_exprlist ce le rl sl al tmps'
  refine tr_expr.rec (motive_1 := P1) (motive_2 := P2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros <;> dsimp [P1, P2, Included] at * <;> intro tmps' htmps' <;>
      constructor <;> try solve_by_elim
  all_goals
    intro tge e le' m hle'
    apply_assumption
    intro id hid
    exact hle' id (htmps' id hid)

end CompCert4Lean.Cfrontend.SimplExprspec

namespace CompCert4Lean.Cfrontend.SimplExprspec

theorem tr_expr_invariant
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    tr_expr_invariantStatement := by
  intro ce le dst r sl a tmps h
  intro le' hle
  revert le' hle
  let P1 := fun (dst : destination) (r : cexpr) (sl : List statement)
      (a : expr) (tmps : List ident) (_ : tr_expr ce le dst r sl a tmps) =>
      ∀ le', (∀ x, x ∈ tmps →
        CompCert4Lean.Lib.Maps.PTree.get x le' = CompCert4Lean.Lib.Maps.PTree.get x le) →
        tr_expr ce le' dst r sl a tmps
  let P2 := fun (rl : cexprlist) (sl : List statement)
      (al : List expr) (tmps : List ident) (_ : tr_exprlist ce le rl sl al tmps) =>
      ∀ le', (∀ x, x ∈ tmps →
        CompCert4Lean.Lib.Maps.PTree.get x le' = CompCert4Lean.Lib.Maps.PTree.get x le) →
        tr_exprlist ce le' rl sl al tmps
  refine tr_expr.rec (motive_1 := P1) (motive_2 := P2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros <;> dsimp [P1, P2, Included] at * <;> intro le' hle <;> constructor <;>
      try solve_by_elim [agree_mono] <;>
      try (intro tge e le1 m hle1; solve_by_elim [agree_mono])
  all_goals
    intro tge e le1 m hle1
    apply_assumption
    intro id hid
    exact Eq.trans (hle1 id hid) (hle id hid)

end CompCert4Lean.Cfrontend.SimplExprspec

namespace CompCert4Lean.Cfrontend.SimplExprspec

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

private def sprintTemps (first last : generator) : List ident :=
  ((List.range (posToNat last.gen_next)).filter
    (fun number => decide (posToNat first.gen_next ≤ number))).map posOfNat

private theorem sprintTemps_mem (first last : generator) (name : ident) :
    name ∈ sprintTemps first last ↔
      posToNat first.gen_next ≤ posToNat name ∧ posToNat name < posToNat last.gen_next := by
  unfold sprintTemps
  unfold ident at *
  unfold CompCert4Lean.Common.AST.ident at *
  rw [_root_.List.mem_map]
  simp only [_root_.List.mem_filter,
    _root_.List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨number, ⟨upper, lower⟩, rfl⟩
    have positive := posToNat_positive first.gen_next
    rw [posToNat_posOfNat (by omega)]
    exact ⟨lower, upper⟩
  · intro bounds
    exact ⟨posToNat name, ⟨bounds.2, bounds.1⟩, posOfNat_posToNat name⟩

private def sprintDest (dst : destination) (names : List ident) : List ident :=
  match dst with
  | .For_set target => sd_temp target :: names
  | _ => names

private theorem sprintTemps_mem_raw (first last : generator) (name : ident) :
    List.Mem name (sprintTemps first last) ↔
      posToNat first.gen_next ≤ posToNat name ∧ posToNat name < posToNat last.gen_next :=
  sprintTemps_mem first last name

private theorem sprintCons_mem_raw (name head : ident) (names : List ident) :
    List.Mem name (head :: names) ↔
      posToNat name = posToNat head ∨ List.Mem name names := by
  constructor
  · intro membership
    cases membership with
    | head => exact Or.inl rfl
    | tail _ membership => exact Or.inr membership
  · intro membership
    rcases membership with equal | membership
    · have equalNames := posToNat_injective equal
      cases equalNames
      exact List.Mem.head _
    · exact List.Mem.tail _ membership

private theorem sprintCons_mem (name head : ident) (names : List ident) :
    name ∈ head :: names ↔ posToNat name = posToNat head ∨ name ∈ names :=
  sprintCons_mem_raw name head names

private theorem sprintSdBase (castTy ty : type) (name : ident) :
    sd_temp (.SDbase castTy ty name) = name := rfl

private theorem sprintSdCons (castTy ty : type) (name : ident) (rest : set_destination) :
    sd_temp (.SDcons castTy ty name rest) = name := rfl

private def sprintBelow (dst : destination) (state : generator) : Prop :=
  match dst with
  | .For_set target => posToNat (sd_temp target) < posToNat state.gen_next
  | _ => True

private theorem sprintFinish (dst : destination) (statements : List statement) (value : expr) :
    finish dst statements value = (statements ++ final dst value, value) := by
  cases dst <;> simp [finish, final]

private theorem sprintBind {Alpha Beta : Type} {action : mon Alpha} {next : Alpha → mon Beta}
    {initial finalState : generator} {value : Beta} {bound}
    (success : SimplExpr.bind action next initial = .Res value finalState bound) :
    ∃ (intermediateValue : Alpha) (intermediateState : generator),
    ∃ (firstBound : posToNat initial.gen_next ≤ posToNat intermediateState.gen_next),
    ∃ (secondBound : posToNat intermediateState.gen_next ≤ posToNat finalState.gen_next),
      action initial = .Res intermediateValue intermediateState firstBound ∧
      next intermediateValue intermediateState = .Res value finalState secondBound := by
  cases first : action initial with
  | Err message => simp [SimplExpr.bind, first] at success
  | Res intermediateValue intermediateState firstBound =>
    cases second : next intermediateValue intermediateState with
    | Err message => simp [SimplExpr.bind, first, second] at success
    | Res resultValue resultState secondBound =>
      simp only [SimplExpr.bind, first, second] at success
      cases success
      exact ⟨_, _, _, _, rfl, second⟩

private theorem sprintBitfield {ce : composite_env} {value : expr} {initial finalState : generator}
    {field : bitfield} {bound}
    (success : is_bitfield_access ce value initial = .Res field finalState bound) :
    tr_is_bitfield_access ce value field := by
  have auxiliary : ∀ procedure tag label,
      is_bitfield_access_aux ce procedure tag label initial = .Res field finalState bound →
      ∃ composite offset,
        CompCert4Lean.Lib.Maps.PTree.get tag ce = some composite ∧
          procedure ce label composite.co_members = .OK (offset, field) := by
    intro procedure tag label result
    unfold is_bitfield_access_aux at result
    cases lookup : CompCert4Lean.Lib.Maps.PTree.get tag ce with
    | none => simp [lookup, error] at result
    | some composite =>
      cases offset : procedure ce label composite.co_members with
      | Error message => simp [lookup, offset, error] at result
      | OK pair =>
        rcases pair with ⟨position, bf⟩
        simp only [lookup, offset, ret] at result
        cases result
        exact ⟨composite, position, rfl, offset⟩
  cases value <;> simp only [is_bitfield_access, ret] at success <;>
    try (cases success; rfl)
  rename_i base label ty
  simp only [tr_is_bitfield_access]
  cases baseType : CompCert4Lean.Cfrontend.Clight.typeof base <;>
    simp only [baseType] at success ⊢ <;>
    try (solve | cases success)
  all_goals exact auxiliary _ _ _ success

private theorem sprintGensym {ty : type} {name : ident} {initial finalState : generator} {bound}
    (success : gensym ty initial = .Res name finalState bound) :
    posToNat name = posToNat initial.gen_next ∧
      posToNat initial.gen_next < posToNat finalState.gen_next := by
  cases success
  exact ⟨rfl, Plt_succ _⟩

private theorem sprintValof {ce : composite_env} {ty : type} {value : expr}
    {initial finalState : generator} {statements : List statement} {resultExpr : expr} {bound}
    (success : transl_valof ce ty value initial = .Res (statements, resultExpr) finalState bound) :
    tr_rvalof ce ty value statements resultExpr (sprintTemps initial finalState) := by
  unfold transl_valof at success
  split at success
  · rcases sprintBind success with ⟨name, middle, firstBound, secondBound, fresh, rest⟩
    rcases sprintBind rest with ⟨field, lastState, thirdBound, fourthBound, access, result⟩
    cases result
    apply tr_rvalof.tr_rvalof_vol
    · assumption
    · rw [sprintTemps_mem]
      have generated := sprintGensym fresh
      change posToNat middle.gen_next ≤ posToNat finalState.gen_next at thirdBound
      omega
    · exact sprintBitfield access
  · cases success
    apply tr_rvalof.tr_rvalof_nonvol
    simpa using ‹¬ type_is_volatile ty = true›

private theorem sprintTemporary {ty : type} {target : set_destination} {name : ident}
    {initial finalState : generator} {bound}
    (success : temp_for_sd ty target initial = .Res name finalState bound) :
    posToNat name = posToNat (sd_temp target) ∨
      (posToNat name = posToNat initial.gen_next ∧
        posToNat name < posToNat finalState.gen_next) := by
  unfold temp_for_sd at success
  split at success
  · cases success
    exact Or.inl rfl
  · have generated := sprintGensym success
    exact Or.inr ⟨generated.1, by omega⟩

local macro "sprint_bounds" : tactic => `(tactic|
  (try (cases ‹destination›)
   all_goals try dsimp only [Included, Disjoint, CompCert4Lean.Lib.Coqlib.list_disjoint,
     CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl,
     CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In]
   all_goals repeat intro
   all_goals subst_vars
   all_goals try dsimp only [sprintDest, sprintBelow, Ple,
     PArith.BinPos.Pos.le, PArith.BinPos.Pos.lt,
     CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In] at *
   all_goals try simp only [sprintTemps_mem, sprintTemps_mem_raw,
     sprintCons_mem_raw, sprintCons_mem, sprintSdBase, sprintSdCons] at *
   all_goals first | trivial | omega))

open CompCert4Lean.Flocq.IEEE754.Binary

section

set_option maxHeartbeats 8000000

variable [binary64_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

mutual
private theorem sprintExpr (ce : composite_env) (source : Csyntax.expr)
    (dst : destination) {initial finalState : generator}
    {statements : List statement} {value : expr}
    {bound : posToNat initial.gen_next ≤ posToNat finalState.gen_next}
    (success : transl_expr ce dst source initial = .Res (statements, value) finalState bound)
    (below : sprintBelow dst initial) (environment : temp_env) :
    tr_expr ce environment dst source statements value
      (sprintDest dst (sprintTemps initial finalState)) := by
  cases source with
  | Eloc block offset field ty => cases success
  | Eparen source castTy ty => cases success
  | Evar name ty =>
    simp only [transl_expr, ret, sprintFinish] at success
    cases success
    exact tr_expr.tr_var _ _ _ _ _
  | Esizeof measured ty =>
    simp only [transl_expr, ret, sprintFinish] at success
    cases success
    exact tr_expr.tr_sizeof _ _ _ _ _
  | Ealignof measured ty =>
    simp only [transl_expr, ret, sprintFinish] at success
    cases success
    exact tr_expr.tr_alignof _ _ _ _ _
  | Eval constant ty =>
    cases constant <;> try (solve | cases success)
    all_goals
      cases dst <;> simp only [transl_expr, ret, finish] at success <;> cases success
    all_goals
      first
      | exact tr_expr.tr_val_effect _ _ _ _ _
      | (apply tr_expr.tr_val_value <;> try rfl
         intros
         constructor)
      | (apply tr_expr.tr_val_set <;> try rfl
         intros
         constructor)
  | Ederef source ty =>
    simp only [transl_expr] at success
    rcases sprintBind success with ⟨⟨prelude, value⟩, middle, firstBound, nextBound, first, rest⟩
    simp only [Pure.pure, ret, sprintFinish] at rest
    cases rest
    apply tr_expr.tr_deref
    apply tr_expr_monotone _ _ _ _ _ _ _
      (sprintExpr ce source .For_val first trivial environment)
    sprint_bounds
  | Efield source label ty =>
    simp only [transl_expr] at success
    rcases sprintBind success with ⟨⟨prelude, value⟩, middle, firstBound, nextBound, first, rest⟩
    simp only [Pure.pure, ret, sprintFinish] at rest
    cases rest
    apply tr_expr.tr_field
    apply tr_expr_monotone _ _ _ _ _ _ _
      (sprintExpr ce source .For_val first trivial environment)
    sprint_bounds
  | Eaddrof source ty =>
    simp only [transl_expr] at success
    rcases sprintBind success with ⟨⟨prelude, value⟩, middle, firstBound, nextBound, first, rest⟩
    simp only [Pure.pure, ret, sprintFinish] at rest
    cases rest
    apply tr_expr.tr_addrof
    apply tr_expr_monotone _ _ _ _ _ _ _
      (sprintExpr ce source .For_val first trivial environment)
    sprint_bounds
  | Eunop operation source ty =>
    simp only [transl_expr] at success
    rcases sprintBind success with ⟨⟨prelude, value⟩, middle, firstBound, nextBound, first, rest⟩
    simp only [Pure.pure, ret, sprintFinish] at rest
    cases rest
    apply tr_expr.tr_unop
    apply tr_expr_monotone _ _ _ _ _ _ _
      (sprintExpr ce source .For_val first trivial environment)
    sprint_bounds
  | Ebinop operation left right ty =>
    rcases sprintBind success with ⟨⟨leftPrefix, leftValue⟩, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨⟨rightPrefix, rightValue⟩, lastState, secondBound, lastBound, second, result⟩
    simp only [Pure.pure, ret, sprintFinish] at result
    cases result
    apply tr_expr.tr_binop
    · exact sprintExpr ce left .For_val first trivial environment
    · exact sprintExpr ce right .For_val second trivial environment
    all_goals sprint_bounds
  | Evalof source ty =>
    rcases sprintBind success with ⟨⟨prelude, value⟩, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨⟨suffix, valueResult⟩, lastState, secondBound, lastBound, second, result⟩
    simp only [Pure.pure, ret, sprintFinish] at result
    cases result
    apply tr_expr.tr_valof
    · exact sprintExpr ce source .For_val first trivial environment
    · exact sprintValof second
    all_goals sprint_bounds
  | Ecast source ty =>
    cases dst with
    | For_effects =>
      exact tr_expr.tr_cast_effects _ _ _ _ _ _ _
        (sprintExpr ce source .For_effects success trivial environment)
    | For_val =>
      simp only [transl_expr] at success
      rcases sprintBind success with ⟨⟨prelude, value⟩, middle, firstBound, nextBound, first, rest⟩
      simp only [Pure.pure, ret, sprintFinish] at rest
      cases rest
      exact tr_expr.tr_cast_val _ _ _ _ _ _ _
        (sprintExpr ce source .For_val first trivial environment)
    | For_set target =>
      simp only [transl_expr] at success
      rcases sprintBind success with ⟨⟨prelude, value⟩, middle, firstBound, nextBound, first, rest⟩
      simp only [Pure.pure, ret, sprintFinish] at rest
      cases rest
      apply tr_expr.tr_cast_val
      apply tr_expr_monotone _ _ _ _ _ _ _
        (sprintExpr ce source .For_val first trivial environment)
      sprint_bounds
  | Ecomma left right ty =>
    rcases sprintBind success with ⟨⟨leftPrefix, leftValue⟩, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨⟨rightPrefix, rightValue⟩, lastState, secondBound, lastBound, second, result⟩
    cases result
    apply tr_expr.tr_comma
    · exact sprintExpr ce left .For_effects first trivial environment
    · exact sprintExpr ce right dst second (by cases dst <;> sprint_bounds) environment
    all_goals cases dst <;> sprint_bounds
  | Eseqand left right ty =>
    rcases sprintBind success with ⟨⟨prelude, test⟩, middle, firstBound, nextBound, first, rest⟩
    cases dst with
    | For_val =>
      rcases sprintBind rest with ⟨name, allocated, allocBound, afterBound, allocation, continuation⟩
      have generated := sprintGensym allocation
      rcases sprintBind continuation with ⟨⟨branchCode, branchValue⟩, lastState, branchBound, endBound, branch, result⟩
      cases result
      apply tr_expr.tr_seqand_val
      · exact sprintExpr ce left .For_val first trivial environment
      · exact sprintExpr ce right _ branch (by sprint_bounds) environment
      all_goals sprint_bounds
    | For_effects =>
      rcases sprintBind rest with ⟨⟨branchCode, branchValue⟩, lastState, branchBound, endBound, branch, result⟩
      cases result
      apply tr_expr.tr_seqand_effects
      · exact sprintExpr ce left .For_val first trivial environment
      · exact sprintExpr ce right .For_effects branch trivial environment
      all_goals sprint_bounds
    | For_set target =>
      rcases sprintBind rest with ⟨name, allocated, allocBound, afterBound, allocation, continuation⟩
      have generated := sprintTemporary allocation
      rcases sprintBind continuation with ⟨⟨branchCode, branchValue⟩, lastState, branchBound, endBound, branch, result⟩
      cases result
      apply tr_expr.tr_seqand_set
      · exact sprintExpr ce left .For_val first trivial environment
      · exact sprintExpr ce right _ branch (by sprint_bounds) environment
      all_goals sprint_bounds
  | Eseqor left right ty =>
    rcases sprintBind success with ⟨⟨prelude, test⟩, middle, firstBound, nextBound, first, rest⟩
    cases dst with
    | For_val =>
      rcases sprintBind rest with ⟨name, allocated, allocBound, afterBound, allocation, continuation⟩
      have generated := sprintGensym allocation
      rcases sprintBind continuation with ⟨⟨branchCode, branchValue⟩, lastState, branchBound, endBound, branch, result⟩
      cases result
      apply tr_expr.tr_seqor_val
      · exact sprintExpr ce left .For_val first trivial environment
      · exact sprintExpr ce right _ branch (by sprint_bounds) environment
      all_goals sprint_bounds
    | For_effects =>
      rcases sprintBind rest with ⟨⟨branchCode, branchValue⟩, lastState, branchBound, endBound, branch, result⟩
      cases result
      apply tr_expr.tr_seqor_effects
      · exact sprintExpr ce left .For_val first trivial environment
      · exact sprintExpr ce right .For_effects branch trivial environment
      all_goals sprint_bounds
    | For_set target =>
      rcases sprintBind rest with ⟨name, allocated, allocBound, afterBound, allocation, continuation⟩
      have generated := sprintTemporary allocation
      rcases sprintBind continuation with ⟨⟨branchCode, branchValue⟩, lastState, branchBound, endBound, branch, result⟩
      cases result
      apply tr_expr.tr_seqor_set
      · exact sprintExpr ce left .For_val first trivial environment
      · exact sprintExpr ce right _ branch (by sprint_bounds) environment
      all_goals sprint_bounds
  | Econdition condition left right ty =>
    rcases sprintBind success with ⟨⟨prelude, test⟩, middle, firstBound, nextBound, first, rest⟩
    cases dst with
    | For_val =>
      rcases sprintBind rest with ⟨name, allocated, allocBound, afterBound, allocation, continuation⟩
      have generated := sprintGensym allocation
      rcases sprintBind continuation with ⟨⟨leftCode, leftValue⟩, nextState, leftBound, remainderBound, leftResult, continuation⟩
      rcases sprintBind continuation with ⟨⟨rightCode, rightValue⟩, lastState, rightBound, endBound, rightResult, result⟩
      cases result
      apply tr_expr.tr_condition_val
      · exact sprintExpr ce condition .For_val first trivial environment
      · exact sprintExpr ce left _ leftResult (by sprint_bounds) environment
      · exact sprintExpr ce right _ rightResult (by sprint_bounds) environment
      all_goals sprint_bounds
    | For_effects =>
      rcases sprintBind rest with ⟨⟨leftCode, leftValue⟩, nextState, leftBound, remainderBound, leftResult, continuation⟩
      rcases sprintBind continuation with ⟨⟨rightCode, rightValue⟩, lastState, rightBound, endBound, rightResult, result⟩
      cases result
      apply tr_expr.tr_condition_effects
      · exact sprintExpr ce condition .For_val first trivial environment
      · exact sprintExpr ce left .For_effects leftResult trivial environment
      · exact sprintExpr ce right .For_effects rightResult trivial environment
      all_goals sprint_bounds
    | For_set target =>
      rcases sprintBind rest with ⟨name, allocated, allocBound, afterBound, allocation, continuation⟩
      have generated := sprintTemporary allocation
      rcases sprintBind continuation with ⟨⟨leftCode, leftValue⟩, nextState, leftBound, remainderBound, leftResult, continuation⟩
      rcases sprintBind continuation with ⟨⟨rightCode, rightValue⟩, lastState, rightBound, endBound, rightResult, result⟩
      cases result
      apply tr_expr.tr_condition_set
      · exact sprintExpr ce condition .For_val first trivial environment
      · exact sprintExpr ce left _ leftResult (by sprint_bounds) environment
      · exact sprintExpr ce right _ rightResult (by sprint_bounds) environment
      all_goals sprint_bounds
  | Eassign left right ty =>
    rcases sprintBind success with ⟨⟨leftCode, leftValue⟩, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨⟨rightCode, rightValue⟩, nextState, secondBound, afterBound, second, rest⟩
    rcases sprintBind rest with ⟨field, accessed, accessBound, remainderBound, access, continuation⟩
    cases dst
    case For_effects =>
      cases continuation
      apply tr_expr.tr_assign_effects
      · exact sprintExpr ce left .For_val first trivial environment
      · exact sprintExpr ce right .For_val second trivial environment
      all_goals first | exact sprintBitfield access | sprint_bounds
    all_goals
      rcases sprintBind continuation with ⟨name, allocated, allocBound, endBound, allocation, result⟩
      have generated := sprintGensym allocation
      simp only [Pure.pure, ret, sprintFinish] at result
      cases result
      simp only [_root_.List.append_assoc, _root_.List.cons_append, _root_.List.nil_append]
      simp only [← _root_.List.append_assoc]
      apply tr_expr.tr_assign_val
      · exact sprintExpr ce left .For_val first trivial environment
      · exact sprintExpr ce right .For_val second trivial environment
      all_goals first | rfl | exact sprintBitfield access | sprint_bounds
  | Eassignop operation left right resultTy ty =>
    rcases sprintBind success with ⟨⟨leftCode, leftValue⟩, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨⟨rightCode, rightValue⟩, nextState, secondBound, afterBound, second, rest⟩
    rcases sprintBind rest with ⟨⟨readCode, readValue⟩, readState, readBound, laterBound, readResult, rest⟩
    rcases sprintBind rest with ⟨field, accessed, accessBound, remainderBound, access, continuation⟩
    cases dst
    case For_effects =>
      cases continuation
      apply tr_expr.tr_assignop_effects
      · exact sprintExpr ce left .For_val first trivial environment
      · exact sprintExpr ce right .For_val second trivial environment
      · rfl
      · exact sprintValof readResult
      all_goals first | exact sprintBitfield access | sprint_bounds
    all_goals
      rcases sprintBind continuation with ⟨name, allocated, allocBound, endBound, allocation, result⟩
      have generated := sprintGensym allocation
      simp only [Pure.pure, ret, sprintFinish] at result
      cases result
      simp only [_root_.List.append_assoc, _root_.List.cons_append, _root_.List.nil_append]
      simp only [← _root_.List.append_assoc]
      apply tr_expr.tr_assignop_val
      · exact sprintExpr ce left .For_val first trivial environment
      · exact sprintExpr ce right .For_val second trivial environment
      · exact sprintValof readResult
      all_goals first | rfl | exact sprintBitfield access | sprint_bounds
  | Epostincr operation source ty =>
    rcases sprintBind success with ⟨⟨prelude, value⟩, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨field, accessed, accessBound, remainderBound, access, continuation⟩
    cases dst
    case For_effects =>
      rcases sprintBind continuation with ⟨⟨readCode, readValue⟩, readState, readBound, endBound, readResult, result⟩
      cases result
      apply tr_expr.tr_postincr_effects
      · exact sprintExpr ce source .For_val first trivial environment
      · exact sprintValof readResult
      all_goals first | rfl | exact sprintBitfield access | sprint_bounds
    all_goals
      rcases sprintBind continuation with ⟨name, allocated, allocBound, endBound, allocation, result⟩
      have generated := sprintGensym allocation
      simp only [Pure.pure, ret, sprintFinish] at result
      cases result
      simp only [_root_.List.append_assoc, _root_.List.cons_append, _root_.List.nil_append]
      apply tr_expr.tr_postincr_val
      · exact sprintExpr ce source .For_val first trivial environment
      all_goals first | rfl | exact sprintBitfield access | sprint_bounds
  | Ecall callee arguments ty =>
    rcases sprintBind success with ⟨⟨calleeCode, calleeValue⟩, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨⟨argumentCode, argumentValues⟩, nextState, secondBound, afterBound, second, continuation⟩
    cases dst
    case For_effects =>
      cases continuation
      apply tr_expr.tr_call_effects
      · exact sprintExpr ce callee .For_val first trivial environment
      · exact sprintExprlist ce arguments second environment
      all_goals sprint_bounds
    all_goals
      rcases sprintBind continuation with ⟨name, allocated, allocBound, endBound, allocation, result⟩
      have generated := sprintGensym allocation
      simp only [Pure.pure, ret, sprintFinish] at result
      cases result
      simp only [_root_.List.append_assoc, _root_.List.cons_append, _root_.List.nil_append]
      simp only [← _root_.List.append_assoc]
      apply tr_expr.tr_call_val
      · intro impossible; cases impossible
      · exact sprintExpr ce callee .For_val first trivial environment
      · exact sprintExprlist ce arguments second environment
      all_goals sprint_bounds
  | Ebuiltin builtin argumentTypes arguments ty =>
    rcases sprintBind success with ⟨⟨argumentCode, argumentValues⟩, nextState, firstBound, afterBound, first, continuation⟩
    cases dst
    case For_effects =>
      cases continuation
      apply tr_expr.tr_builtin_effects
      · exact sprintExprlist ce arguments first environment
      · sprint_bounds
    all_goals
      rcases sprintBind continuation with ⟨name, allocated, allocBound, endBound, allocation, result⟩
      have generated := sprintGensym allocation
      simp only [Pure.pure, ret, sprintFinish] at result
      cases result
      simp only [_root_.List.append_assoc, _root_.List.cons_append, _root_.List.nil_append]
      apply tr_expr.tr_builtin_val
      · intro impossible; cases impossible
      · exact sprintExprlist ce arguments first environment
      all_goals sprint_bounds
termination_by sizeOf source

private theorem sprintExprlist (ce : composite_env) (sources : Csyntax.exprlist)
    {initial finalState : generator} {statements : List statement} {values : List expr}
    {bound : posToNat initial.gen_next ≤ posToNat finalState.gen_next}
    (success : transl_exprlist ce sources initial = .Res (statements, values) finalState bound)
    (environment : temp_env) :
    tr_exprlist ce environment sources statements values (sprintTemps initial finalState) := by
  cases sources with
  | Enil =>
    cases success
    exact tr_exprlist.tr_nil _ _
  | Econs source sources =>
    rcases sprintBind success with ⟨⟨prelude, value⟩, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨⟨suffix, values⟩, lastState, secondBound, lastBound, second, result⟩
    cases result
    apply tr_exprlist.tr_cons
    · exact sprintExpr ce source .For_val first trivial environment
    · exact sprintExprlist ce sources second environment
    all_goals sprint_bounds
termination_by sizeOf sources
end

private theorem sprintExpression {ce : composite_env} {source : cexpr}
    {initial finalState : generator} {code : statement} {value : expr} {bound}
    (success : transl_expression ce source initial = .Res (code, value) finalState bound) :
    tr_expression ce source code value := by
  unfold transl_expression at success
  rcases sprintBind success with ⟨⟨prelude, resultValue⟩, middle, firstBound, nextBound, first, result⟩
  cases result
  apply tr_expression.tr_expression_intro
  intro global locals environment memory
  apply tr_top.tr_top_base
  exact sprintExpr ce source .For_val first trivial environment

private theorem sprintExpressionStatement {ce : composite_env} {source : cexpr}
    {initial finalState : generator} {code : statement} {bound}
    (success : transl_expr_stmt ce source initial = .Res code finalState bound) :
    tr_expr_stmt ce source code := by
  unfold transl_expr_stmt at success
  rcases sprintBind success with ⟨⟨prelude, resultValue⟩, middle, firstBound, nextBound, first, result⟩
  cases result
  apply tr_expr_stmt.tr_expr_stmt_intro
  intro global locals environment memory
  apply tr_top.tr_top_base
  exact sprintExpr ce source .For_effects first trivial environment

private theorem sprintIf {ce : composite_env} {source : cexpr} {yes no : statement}
    {initial finalState : generator} {code : statement} {bound}
    (success : transl_if ce source yes no initial = .Res code finalState bound) :
    tr_if ce source yes no code := by
  unfold transl_if at success
  rcases sprintBind success with ⟨⟨prelude, resultValue⟩, middle, firstBound, nextBound, first, result⟩
  cases result
  apply tr_if.tr_if_intro
  intro global locals environment memory
  apply tr_top.tr_top_base
  exact sprintExpr ce source .For_val first trivial environment

mutual
private theorem sprintStatement (ce : composite_env) (source : cstatement)
    {initial finalState : generator} {code : statement} {bound}
    (success : transl_stmt ce source initial = .Res code finalState bound) :
    tr_stmt ce source code := by
  cases source with
  | Sskip => cases success; exact tr_stmt.tr_skip
  | Sbreak => cases success; exact tr_stmt.tr_break
  | Scontinue => cases success; exact tr_stmt.tr_continue
  | Sgoto label => cases success; exact tr_stmt.tr_goto _
  | Sdo source => exact tr_stmt.tr_do _ _ (sprintExpressionStatement success)
  | Ssequence left right =>
    rcases sprintBind success with ⟨leftCode, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨rightCode, lastState, secondBound, endBound, second, result⟩
    cases result
    exact tr_stmt.tr_seq _ _ _ _ (sprintStatement ce left first) (sprintStatement ce right second)
  | Sifthenelse condition left right =>
    rcases sprintBind success with ⟨leftCode, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨rightCode, nextState, secondBound, afterBound, second, rest⟩
    rcases sprintBind rest with ⟨⟨conditionCode, conditionValue⟩, lastState, thirdBound, endBound, conditionResult, result⟩
    dsimp only at result
    split at result
    next selected =>
      have selections := _root_.Bool.and_eq_true_iff.mp selected
      have leftSkip : left = .Sskip := by
        have selection := selections.1
        cases left <;> first | rfl | (change false = true at selection; cases selection)
      have rightSkip : right = .Sskip := by
        have selection := selections.2
        cases right <;> first | rfl | (change false = true at selection; cases selection)
      subst left right
      cases result
      exact tr_stmt.tr_ifthenelse_empty _ _ _ (sprintExpression conditionResult)
    next selected =>
      cases result
      exact tr_stmt.tr_ifthenelse _ _ _ _ _ _ _ (sprintExpression conditionResult)
        (sprintStatement ce left first) (sprintStatement ce right second)
  | Swhile condition body =>
    rcases sprintBind success with ⟨conditionCode, middle, firstBound, nextBound, conditionResult, rest⟩
    rcases sprintBind rest with ⟨bodyCode, lastState, secondBound, endBound, bodyResult, result⟩
    cases result
    exact tr_stmt.tr_while _ _ _ _ (sprintIf conditionResult) (sprintStatement ce body bodyResult)
  | Sdowhile condition body =>
    rcases sprintBind success with ⟨conditionCode, middle, firstBound, nextBound, conditionResult, rest⟩
    rcases sprintBind rest with ⟨bodyCode, lastState, secondBound, endBound, bodyResult, result⟩
    cases result
    exact tr_stmt.tr_dowhile _ _ _ _ (sprintIf conditionResult) (sprintStatement ce body bodyResult)
  | Sfor start condition advance body =>
    rcases sprintBind success with ⟨startCode, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨conditionCode, nextState, secondBound, afterBound, conditionResult, rest⟩
    rcases sprintBind rest with ⟨advanceCode, advanced, thirdBound, laterBound, advanceResult, rest⟩
    rcases sprintBind rest with ⟨bodyCode, lastState, fourthBound, endBound, bodyResult, result⟩
    try dsimp only at result
    split at result
    next selected =>
      have startSkip : start = .Sskip := by
        cases start <;> first | rfl | (change false = true at selected; cases selected)
      subst start
      cases result
      exact tr_stmt.tr_for_1 _ _ _ _ _ _ (sprintIf conditionResult)
        (sprintStatement ce advance advanceResult) (sprintStatement ce body bodyResult)
    next selected =>
      have startNonempty : start ≠ .Sskip := by
        intro equal
        subst start
        exact selected rfl
      cases result
      exact tr_stmt.tr_for_2 _ _ _ _ _ _ _ _ (sprintIf conditionResult) startNonempty
        (sprintStatement ce start first) (sprintStatement ce advance advanceResult)
        (sprintStatement ce body bodyResult)
  | Sreturn resultValue =>
    cases resultValue with
    | none => cases success; exact tr_stmt.tr_return_none
    | some source =>
      simp only [transl_stmt] at success
      rcases sprintBind success with ⟨⟨prelude, value⟩, middle, firstBound, nextBound, first, result⟩
      cases result
      exact tr_stmt.tr_return_some _ _ _ (sprintExpression first)
  | Sswitch condition labels =>
    rcases sprintBind success with ⟨⟨conditionCode, conditionValue⟩, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨labelCode, lastState, secondBound, endBound, second, result⟩
    cases result
    exact tr_stmt.tr_switch _ _ _ _ _ (sprintExpression first) (sprintLabels ce labels second)
  | Slabel label body =>
    simp only [transl_stmt] at success
    rcases sprintBind success with ⟨bodyCode, middle, firstBound, nextBound, first, result⟩
    cases result
    exact tr_stmt.tr_label _ _ _ (sprintStatement ce body first)
termination_by sizeOf source

private theorem sprintLabels (ce : composite_env) (sources : clabeled_statements)
    {initial finalState : generator} {code : labeled_statements} {bound}
    (success : transl_lblstmt ce sources initial = .Res code finalState bound) :
    tr_lblstmts ce sources code := by
  cases sources with
  | LSnil => cases success; exact tr_lblstmts.tr_ls_nil
  | LScons label source sources =>
    rcases sprintBind success with ⟨bodyCode, middle, firstBound, nextBound, first, rest⟩
    rcases sprintBind rest with ⟨labelCode, lastState, secondBound, endBound, second, result⟩
    cases result
    exact tr_lblstmts.tr_ls_cons _ _ _ _ _ (sprintStatement ce source first) (sprintLabels ce sources second)
termination_by sizeOf sources
end

theorem transl_stmt_meets_spec : transl_stmt_meets_specStatement := by
  intro ce source initial code finalState bound success
  exact sprintStatement ce source success

end

end CompCert4Lean.Cfrontend.SimplExprspec

namespace CompCert4Lean.Cfrontend.SimplExprspec

theorem transl_function_spec
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_function_specStatement := by
  intro context composites source translated success
  unfold SimplExpr.transl_function at success
  cases body : SimplExpr.transl_stmt composites source.fn_body
      (SimplExpr.initial_generator context ()) with
  | Err message => simp [body] at success
  | Res code generated monotone =>
    simp only [body] at success
    cases success
    exact tr_function.tr_function_intro _ _
      (transl_stmt_meets_spec _ _ _ _ _ _ body) rfl rfl rfl rfl

end CompCert4Lean.Cfrontend.SimplExprspec

namespace CompCert4Lean.Cfrontend.SimplExprspec

theorem transl_fundef_spec
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_fundef_specStatement := by
  intro context program source translated success
  cases source with
  | Internal source =>
    unfold SimplExpr.transl_fundef at success
    cases translation : SimplExpr.transl_function context program.prog_comp_env source with
    | Error message => simp [translation] at success
    | OK target =>
      simp only [translation] at success
      cases success
      exact tr_fundef.tr_internal _ _ (transl_function_spec _ _ _ _ translation)
  | External external argumentTypes returnType convention =>
    cases success
    exact tr_fundef.tr_external _ _ _ _

end CompCert4Lean.Cfrontend.SimplExprspec
