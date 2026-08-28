import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Values
import CompCert4Lean.Cfrontend.Cop
import CompCert4Lean.Cfrontend.Csyntax
import CompCert4Lean.Cfrontend.Clight
import CompCert4Lean.Cfrontend.Ctypes
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps

/-!
# Translation from CompCert C to Clight

Definition-bearing translation of CompCert's `cfrontend/SimplExpr.v`.
Side effects are pulled out of CompCert C expressions.  The extracted
fresh-identifier service is represented explicitly by `FreshIdentContext`.
-/

namespace CompCert4Lean.Cfrontend.SimplExpr

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Clight

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev errmsg := CompCert4Lean.Common.Errors.errmsg
private abbrev errorsRes := CompCert4Lean.Common.Errors.res
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev memory_chunk := CompCert4Lean.Common.AST.memory_chunk
private abbrev type := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev composite_env := CompCert4Lean.Cfrontend.Ctypes.composite_env
private abbrev members := CompCert4Lean.Cfrontend.Ctypes.members
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev intsize := CompCert4Lean.Cfrontend.Ctypes.intsize
private abbrev signedness := CompCert4Lean.Cfrontend.Ctypes.signedness
private abbrev expr := CompCert4Lean.Cfrontend.Clight.expr
private abbrev statement := CompCert4Lean.Cfrontend.Clight.statement
private abbrev labeled_statements := CompCert4Lean.Cfrontend.Clight.labeled_statements
private abbrev function := CompCert4Lean.Cfrontend.Clight.function
private abbrev fundef := CompCert4Lean.Cfrontend.Clight.fundef
private abbrev program := CompCert4Lean.Cfrontend.Clight.program

private abbrev zOne : Z := .Zpos .xH
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev two_p := ZArith.Zpower.two_p
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

private def rocqStringOfBytes :
    List UInt8 →
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
  | [] => .EmptyString
  | byte :: rest => .String byte (rocqStringOfBytes rest)

private def unknownCompositeText :=
  rocqStringOfBytes
    [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 109, 112, 111, 115,
      105, 116, 101, 32]

private def unknownFieldText :=
  rocqStringOfBytes
    [117, 110, 107, 110, 111, 119, 110, 32, 102, 105, 101, 108, 100, 32]

private def bitfieldAccessText :=
  rocqStringOfBytes
    [105, 115, 95, 98, 105, 116, 102, 105, 101, 108, 100, 95, 97, 99, 99,
      101, 115, 115]

private def translExprElocText :=
  rocqStringOfBytes
    [83, 105, 109, 112, 108, 69, 120, 112, 114, 46, 116, 114, 97, 110, 115,
      108, 95, 101, 120, 112, 114, 58, 32, 69, 108, 111, 99]

private def translExprEvalText :=
  rocqStringOfBytes
    [83, 105, 109, 112, 108, 69, 120, 112, 114, 46, 116, 114, 97, 110, 115,
      108, 95, 101, 120, 112, 114, 58, 32, 69, 118, 97, 108]

private def translExprParenText :=
  rocqStringOfBytes
    [83, 105, 109, 112, 108, 69, 120, 112, 114, 46, 116, 114, 97, 110, 115,
      108, 95, 101, 120, 112, 114, 58, 32, 112, 97, 114, 101, 110]

/-! ## Fresh-name state and error monad -/

structure generator : Type where
  gen_next : ident
  gen_trail : List (ident × type)

export generator (gen_next gen_trail)

inductive result (A : Type) (g : generator) : Type where
  | Err (message : errmsg)
  | Res (value : A) (next : generator)
      (monotone : CompCert4Lean.Lib.Coqlib.Ple g.gen_next next.gen_next)

export result (Err Res)

def mon (A : Type) : Type :=
  (g : generator) → result A g

def ret {A : Type} (x : A) : mon A :=
  fun g => .Res x g (Nat.le_refl _)

def error {A : Type} (message : errmsg) : mon A :=
  fun _ => .Err message

def bind {A B : Type} (x : mon A) (f : A → mon B) : mon B :=
  fun g =>
    match x g with
    | .Err message => .Err message
    | .Res a g' h =>
        match f a g' with
        | .Err message => .Err message
        | .Res b g'' h' => .Res b g'' (Nat.le_trans h h')

def bind2 {A B C : Type} (x : mon (A × B)) (f : A → B → mon C) : mon C :=
  bind x (fun p => f p.1 p.2)

private instance monMonad : Monad mon where
  pure := @ret
  bind := @bind

/-!
The reference implementation obtains this value from Camlcoq's atom table.
The accepted Lean interface makes that immutable per-compilation input
explicit.  Canonical atom numbering reserves identifiers below 128.
-/

inductive AtomNumbering : Type where
  | sequential (nextAtom : ident)
  | canonical

structure FreshIdentContext : Type where
  numbering : AtomNumbering

def first_unused_ident (ctx : FreshIdentContext) (_ : Unit) : ident :=
  match ctx.numbering with
  | .sequential nextAtom => nextAtom
  | .canonical => PArith.BinPos.Pos.of_nat 128

def initial_generator (ctx : FreshIdentContext) (x : Unit) : generator :=
  { gen_next := first_unused_ident ctx x, gen_trail := [] }

private theorem posToNatSucc (p : positive) :
    PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p) =
      PArith.BinPos.Pos.to_nat p + 1 := by
  induction p with
  | xH => rfl
  | xI p ih =>
      change 2 * PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p) =
        2 * PArith.BinPos.Pos.to_nat p + 2
      omega
  | xO p ih => rfl

private theorem pleSucc (p : positive) :
    CompCert4Lean.Lib.Coqlib.Ple p (PArith.BinPos.Pos.succ p) := by
  change PArith.BinPos.Pos.to_nat p ≤
    PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p)
  rw [posToNatSucc]
  omega

def gensym (ty : type) : mon ident :=
  fun g =>
    .Res g.gen_next
      { gen_next := PArith.BinPos.Pos.succ g.gen_next
        gen_trail := (g.gen_next, ty) :: g.gen_trail }
      (pleSucc g.gen_next)

/-! ## Statement and expression smart constructors -/

def makeseq_rec (s : statement) : List statement → statement
  | [] => s
  | s' :: rest => makeseq_rec (.Ssequence s s') rest

def makeseq (statements : List statement) : statement :=
  makeseq_rec .Sskip statements

def eval_simpl_expr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    expr → Option val
  | .Econst_int n _ => some (.Vint n)
  | .Econst_float n _ => some (.Vfloat n)
  | .Econst_single n _ => some (.Vsingle n)
  | .Econst_long n _ => some (.Vlong n)
  | .Ecast b ty =>
      match eval_simpl_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) b with
      | none => none
      | some v =>
          CompCert4Lean.Cfrontend.Cop.sem_cast v
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (CompCert4Lean.Cfrontend.Clight.typeof b) ty
            CompCert4Lean.Common.Memory.Mem.empty
  | _ => none

def makeif
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (a : expr) (s1 s2 : statement) : statement :=
  match eval_simpl_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) a with
  | some v =>
      match CompCert4Lean.Cfrontend.Cop.bool_val v
          (CompCert4Lean.Cfrontend.Clight.typeof a)
          CompCert4Lean.Common.Memory.Mem.empty with
      | some b => if b then s1 else s2
      | none => .Sifthenelse a s1 s2
  | none => .Sifthenelse a s1 s2

private def typeEq (t1 t2 : type) : Bool :=
  CompCert4Lean.Lib.Coqlib.proj_sumbool
    (CompCert4Lean.Cfrontend.Ctypes.type_eq t1 t2)

private def typeListEq (ts1 ts2 : List type) : Bool :=
  CompCert4Lean.Lib.Coqlib.proj_sumbool
    (CompCert4Lean.Cfrontend.Ctypes.typelist_eq ts1 ts2)

def Ederef' (a : expr) (t : type) : expr :=
  match a with
  | .Eaddrof a' _ =>
      if typeEq t (CompCert4Lean.Cfrontend.Clight.typeof a') then a'
      else .Ederef a t
  | _ => .Ederef a t

def Eaddrof' (a : expr) (t : type) : expr :=
  match a with
  | .Ederef a' _ =>
      if typeEq t (CompCert4Lean.Cfrontend.Clight.typeof a') then a'
      else .Eaddrof a t
  | _ => .Eaddrof a t

def transl_incrdecr
    (id : CompCert4Lean.Cfrontend.Cop.incr_or_decr) (a : expr) (ty : type) : expr :=
  match id with
  | .Incr =>
      .Ebinop .Oadd a
        (.Econst_int CompCert4Lean.Lib.Integers.Int.one type_int32s)
        (CompCert4Lean.Cfrontend.Cop.incrdecr_type ty)
  | .Decr =>
      .Ebinop .Osub a
        (.Econst_int CompCert4Lean.Lib.Integers.Int.one type_int32s)
        (CompCert4Lean.Cfrontend.Cop.incrdecr_type ty)

def is_bitfield_access_aux (ce : composite_env)
    (fn : composite_env → ident → members → errorsRes (Z × bitfield))
    (id fld : ident) : mon bitfield :=
  match CompCert4Lean.Lib.Maps.PTree.get id ce with
  | none => error (.MSG unknownCompositeText :: .CTX id :: [])
  | some co =>
      match fn ce fld co.co_members with
      | .OK (_, bf) => ret bf
      | .Error _ => error (.MSG unknownFieldText :: .CTX fld :: [])

def is_bitfield_access (ce : composite_env) (l : expr) : mon bitfield :=
  match l with
  | .Efield r f _ =>
      match CompCert4Lean.Cfrontend.Clight.typeof r with
      | .Tstruct id _ => is_bitfield_access_aux ce field_offset id f
      | .Tunion id _ => is_bitfield_access_aux ce union_field_offset id f
      | _ => error (CompCert4Lean.Common.Errors.msg bitfieldAccessText)
  | _ => ret .Full

def chunk_for_volatile_type (ty : type) (bf : bitfield) : Option memory_chunk :=
  if type_is_volatile ty then
    match access_mode ty with
    | .By_value chunk =>
        match bf with
        | .Full => some chunk
        | .Bits _ _ _ _ => none
    | _ => none
  else
    none

def make_set (bf : bitfield) (id : ident) (l : expr) : statement :=
  match chunk_for_volatile_type (CompCert4Lean.Cfrontend.Clight.typeof l) bf with
  | none => .Sset id l
  | some chunk =>
      let typtr := .Tpointer (CompCert4Lean.Cfrontend.Clight.typeof l) noattr
      .Sbuiltin (some id) (.EF_vload chunk) [typtr] [.Eaddrof l typtr]

def transl_valof (ce : composite_env) (ty : type) (l : expr) : mon (List statement × expr) :=
  if type_is_volatile ty then do
    let t ← gensym ty
    let bf ← is_bitfield_access ce l
    pure ([make_set bf t l], .Etempvar t ty)
  else
    ret ([], l)

def make_assign (bf : bitfield) (l r : expr) : statement :=
  match chunk_for_volatile_type (CompCert4Lean.Cfrontend.Clight.typeof l) bf with
  | none => .Sassign l r
  | some chunk =>
      let ty := CompCert4Lean.Cfrontend.Clight.typeof l
      let typtr := .Tpointer ty noattr
      .Sbuiltin none (.EF_vstore chunk) [typtr, ty] [.Eaddrof l typtr, r]

def make_normalize (sz : intsize) (sg : signedness) (width : Z) (r : expr) : expr :=
  let intconst (n : Z) :=
    expr.Econst_int (CompCert4Lean.Lib.Integers.Int.repr n) type_int32s
  if sz == .IBool || sg == .Unsigned then
    let mask := zSub (two_p width) zOne
    .Ebinop .Oand r (intconst mask) (CompCert4Lean.Cfrontend.Clight.typeof r)
  else
    let amount := zSub CompCert4Lean.Lib.Integers.Int.zwordsize width
    .Ebinop .Oshr
      (.Ebinop .Oshl r (intconst amount) type_int32s)
      (intconst amount)
      (CompCert4Lean.Cfrontend.Clight.typeof r)

def make_assign_value (bf : bitfield) (r : expr) : expr :=
  match bf with
  | .Full => r
  | .Bits sz sg _ width => make_normalize sz sg width r

/-! ## Expression destinations -/

inductive set_destination : Type where
  | SDbase (tycast ty : type) (tmp : ident)
  | SDcons (tycast ty : type) (tmp : ident) (sd : set_destination)

export set_destination (SDbase SDcons)

inductive destination : Type where
  | For_val
  | For_effects
  | For_set (sd : set_destination)

export destination (For_val For_effects For_set)

def dummy_expr : expr :=
  .Econst_int CompCert4Lean.Lib.Integers.Int.zero type_int32s

def do_set : set_destination → expr → List statement
  | .SDbase tycast _ tmp, a => [.Sset tmp (.Ecast a tycast)]
  | .SDcons tycast ty tmp sd, a =>
      .Sset tmp (.Ecast a tycast) :: do_set sd (.Etempvar tmp ty)

def finish (dst : destination) (sl : List statement) (a : expr) : List statement × expr :=
  match dst with
  | .For_val => (sl, a)
  | .For_effects => (sl, a)
  | .For_set sd => (sl ++ do_set sd a, a)

def sd_temp : set_destination → ident
  | .SDbase _ _ tmp => tmp
  | .SDcons _ _ tmp _ => tmp

def sd_head_type : set_destination → type
  | .SDbase _ ty _ => ty
  | .SDcons _ ty _ _ => ty

def temp_for_sd (ty : type) (sd : set_destination) : mon ident :=
  if typeEq ty (sd_head_type sd) then ret (sd_temp sd) else gensym ty

/-! ## Translation of expressions -/

mutual
  def transl_expr
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ce : composite_env) (dst : destination) :
      CompCert4Lean.Cfrontend.Csyntax.expr → mon (List statement × expr)
    | .Eloc _ _ _ _ => error (CompCert4Lean.Common.Errors.msg translExprElocText)
    | .Evar x ty => ret (finish dst [] (.Evar x ty))
    | .Ederef r ty => do
        let (sl, a) ← transl_expr ce .For_val r
        pure (finish dst sl (Ederef' a ty))
    | .Efield r f ty => do
        let (sl, a) ← transl_expr ce .For_val r
        pure (finish dst sl (.Efield a f ty))
    | .Eval (.Vint n) ty => ret (finish dst [] (.Econst_int n ty))
    | .Eval (.Vfloat n) ty => ret (finish dst [] (.Econst_float n ty))
    | .Eval (.Vsingle n) ty => ret (finish dst [] (.Econst_single n ty))
    | .Eval (.Vlong n) ty => ret (finish dst [] (.Econst_long n ty))
    | .Eval _ _ => error (CompCert4Lean.Common.Errors.msg translExprEvalText)
    | .Esizeof ty' ty => ret (finish dst [] (.Esizeof ty' ty))
    | .Ealignof ty' ty => ret (finish dst [] (.Ealignof ty' ty))
    | .Evalof l _ => do
        let (sl1, a1) ← transl_expr ce .For_val l
        let (sl2, a2) ← transl_valof ce (CompCert4Lean.Cfrontend.Csyntax.typeof l) a1
        pure (finish dst (sl1 ++ sl2) a2)
    | .Eaddrof l ty => do
        let (sl, a) ← transl_expr ce .For_val l
        pure (finish dst sl (Eaddrof' a ty))
    | .Eunop op r1 ty => do
        let (sl1, a1) ← transl_expr ce .For_val r1
        pure (finish dst sl1 (.Eunop op a1 ty))
    | .Ebinop op r1 r2 ty => do
        let (sl1, a1) ← transl_expr ce .For_val r1
        let (sl2, a2) ← transl_expr ce .For_val r2
        pure (finish dst (sl1 ++ sl2) (.Ebinop op a1 a2 ty))
    | .Ecast r1 ty =>
        match dst with
        | .For_val | .For_set _ => do
            let (sl1, a1) ← transl_expr ce .For_val r1
            pure (finish dst sl1 (.Ecast a1 ty))
        | .For_effects => transl_expr ce .For_effects r1
    | .Eseqand r1 r2 ty => do
        let (sl1, a1) ← transl_expr ce .For_val r1
        match dst with
        | .For_val => do
            let t ← gensym ty
            let sd := .SDbase type_bool ty t
            let (sl2, _) ← transl_expr ce (.For_set sd) r2
            pure
              (sl1 ++ [makeif
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) a1 (makeseq sl2)
                (.Sset t (.Econst_int CompCert4Lean.Lib.Integers.Int.zero ty))],
               .Etempvar t ty)
        | .For_effects => do
            let (sl2, _) ← transl_expr ce .For_effects r2
            pure (sl1 ++ [makeif
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) a1 (makeseq sl2) .Sskip], dummy_expr)
        | .For_set sd => do
            let t ← temp_for_sd ty sd
            let sd' := .SDcons type_bool ty t sd
            let (sl2, _) ← transl_expr ce (.For_set sd') r2
            pure
              (sl1 ++ [makeif
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) a1 (makeseq sl2)
                (makeseq (do_set sd (.Econst_int CompCert4Lean.Lib.Integers.Int.zero ty)))],
               dummy_expr)
    | .Eseqor r1 r2 ty => do
        let (sl1, a1) ← transl_expr ce .For_val r1
        match dst with
        | .For_val => do
            let t ← gensym ty
            let sd := .SDbase type_bool ty t
            let (sl2, _) ← transl_expr ce (.For_set sd) r2
            pure
              (sl1 ++ [makeif
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) a1
                (.Sset t (.Econst_int CompCert4Lean.Lib.Integers.Int.one ty))
                (makeseq sl2)],
               .Etempvar t ty)
        | .For_effects => do
            let (sl2, _) ← transl_expr ce .For_effects r2
            pure (sl1 ++ [makeif
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) a1 .Sskip (makeseq sl2)], dummy_expr)
        | .For_set sd => do
            let t ← temp_for_sd ty sd
            let sd' := .SDcons type_bool ty t sd
            let (sl2, _) ← transl_expr ce (.For_set sd') r2
            pure
              (sl1 ++ [makeif
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) a1
                (makeseq (do_set sd (.Econst_int CompCert4Lean.Lib.Integers.Int.one ty)))
                (makeseq sl2)],
               dummy_expr)
    | .Econdition r1 r2 r3 ty => do
        let (sl1, a1) ← transl_expr ce .For_val r1
        match dst with
        | .For_val => do
            let t ← gensym ty
            let sd := .SDbase ty ty t
            let (sl2, _) ← transl_expr ce (.For_set sd) r2
            let (sl3, _) ← transl_expr ce (.For_set sd) r3
            pure (sl1 ++ [makeif
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) a1 (makeseq sl2) (makeseq sl3)], .Etempvar t ty)
        | .For_effects => do
            let (sl2, _) ← transl_expr ce .For_effects r2
            let (sl3, _) ← transl_expr ce .For_effects r3
            pure (sl1 ++ [makeif
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) a1 (makeseq sl2) (makeseq sl3)], dummy_expr)
        | .For_set sd => do
            let t ← temp_for_sd ty sd
            let sd' := .SDcons ty ty t sd
            let (sl2, _) ← transl_expr ce (.For_set sd') r2
            let (sl3, _) ← transl_expr ce (.For_set sd') r3
            pure (sl1 ++ [makeif
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) a1 (makeseq sl2) (makeseq sl3)], dummy_expr)
    | .Eassign l1 r2 _ => do
        let (sl1, a1) ← transl_expr ce .For_val l1
        let (sl2, a2) ← transl_expr ce .For_val r2
        let bf ← is_bitfield_access ce a1
        let ty1 := CompCert4Lean.Cfrontend.Csyntax.typeof l1
        match dst with
        | .For_val | .For_set _ => do
            let t ← gensym ty1
            pure
              (finish dst
                (sl1 ++ sl2 ++
                  [.Sset t (.Ecast a2 ty1), make_assign bf a1 (.Etempvar t ty1)])
                (make_assign_value bf (.Etempvar t ty1)))
        | .For_effects =>
            ret (sl1 ++ sl2 ++ [make_assign bf a1 a2], dummy_expr)
    | .Eassignop op l1 r2 tyres _ => do
        let ty1 := CompCert4Lean.Cfrontend.Csyntax.typeof l1
        let (sl1, a1) ← transl_expr ce .For_val l1
        let (sl2, a2) ← transl_expr ce .For_val r2
        let (sl3, a3) ← transl_valof ce ty1 a1
        let bf ← is_bitfield_access ce a1
        match dst with
        | .For_val | .For_set _ => do
            let t ← gensym ty1
            pure
              (finish dst
                (sl1 ++ sl2 ++ sl3 ++
                  [.Sset t (.Ecast (.Ebinop op a3 a2 tyres) ty1),
                   make_assign bf a1 (.Etempvar t ty1)])
                (make_assign_value bf (.Etempvar t ty1)))
        | .For_effects =>
            ret
              (sl1 ++ sl2 ++ sl3 ++ [make_assign bf a1 (.Ebinop op a3 a2 tyres)],
               dummy_expr)
    | .Epostincr id l1 _ => do
        let ty1 := CompCert4Lean.Cfrontend.Csyntax.typeof l1
        let (sl1, a1) ← transl_expr ce .For_val l1
        let bf ← is_bitfield_access ce a1
        match dst with
        | .For_val | .For_set _ => do
            let t ← gensym ty1
            pure
              (finish dst
                (sl1 ++
                  [make_set bf t a1,
                   make_assign bf a1 (transl_incrdecr id (.Etempvar t ty1) ty1)])
                (.Etempvar t ty1))
        | .For_effects => do
            let (sl2, a2) ← transl_valof ce ty1 a1
            pure
              (sl1 ++ sl2 ++ [make_assign bf a1 (transl_incrdecr id a2 ty1)],
               dummy_expr)
    | .Ecomma r1 r2 _ => do
        let (sl1, _) ← transl_expr ce .For_effects r1
        let (sl2, a2) ← transl_expr ce dst r2
        pure (sl1 ++ sl2, a2)
    | .Ecall r1 rl2 ty => do
        let (sl1, a1) ← transl_expr ce .For_val r1
        let (sl2, al2) ← transl_exprlist ce rl2
        match dst with
        | .For_val | .For_set _ => do
            let t ← gensym ty
            pure (finish dst (sl1 ++ sl2 ++ [.Scall (some t) a1 al2]) (.Etempvar t ty))
        | .For_effects =>
            ret (sl1 ++ sl2 ++ [.Scall none a1 al2], dummy_expr)
    | .Ebuiltin ef tyargs rl ty => do
        let (sl, al) ← transl_exprlist ce rl
        match dst with
        | .For_val | .For_set _ => do
            let t ← gensym ty
            pure (finish dst (sl ++ [.Sbuiltin (some t) ef tyargs al]) (.Etempvar t ty))
        | .For_effects =>
            ret (sl ++ [.Sbuiltin none ef tyargs al], dummy_expr)
    | .Eparen _ _ _ => error (CompCert4Lean.Common.Errors.msg translExprParenText)

  def transl_exprlist
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ce : composite_env) :
      CompCert4Lean.Cfrontend.Csyntax.exprlist → mon (List statement × List expr)
    | .Enil => ret ([], [])
    | .Econs r1 rl2 => do
        let (sl1, a1) ← transl_expr ce .For_val r1
        let (sl2, al2) ← transl_exprlist ce rl2
        pure (sl1 ++ sl2, a1 :: al2)
end

def transl_expression
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ce : composite_env)
    (r : CompCert4Lean.Cfrontend.Csyntax.expr) : mon (statement × expr) := do
  let (sl, a) ← transl_expr ce .For_val r
  pure (makeseq sl, a)

def transl_expr_stmt
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ce : composite_env)
    (r : CompCert4Lean.Cfrontend.Csyntax.expr) : mon statement := do
  let (sl, _) ← transl_expr ce .For_effects r
  pure (makeseq sl)

def transl_if
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ce : composite_env) (r : CompCert4Lean.Cfrontend.Csyntax.expr)
    (s1 s2 : statement) : mon statement := do
  let (sl, a) ← transl_expr ce .For_val r
  pure (makeseq (sl ++ [makeif
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) a s1 s2]))

/-! ## Translation of statements -/

def is_Sskip :
    (s : CompCert4Lean.Cfrontend.Csyntax.statement) →
      Sumbool (s = .Sskip) (s ≠ .Sskip)
  | .Sskip => .left rfl
  | .Sdo _ => .right (by intro h; cases h)
  | .Ssequence _ _ => .right (by intro h; cases h)
  | .Sifthenelse _ _ _ => .right (by intro h; cases h)
  | .Swhile _ _ => .right (by intro h; cases h)
  | .Sdowhile _ _ => .right (by intro h; cases h)
  | .Sfor _ _ _ _ => .right (by intro h; cases h)
  | .Sbreak => .right (by intro h; cases h)
  | .Scontinue => .right (by intro h; cases h)
  | .Sreturn _ => .right (by intro h; cases h)
  | .Sswitch _ _ => .right (by intro h; cases h)
  | .Slabel _ _ => .right (by intro h; cases h)
  | .Sgoto _ => .right (by intro h; cases h)

private def skipBool (s : CompCert4Lean.Cfrontend.Csyntax.statement) : Bool :=
  match is_Sskip s with
  | .left _ => true
  | .right _ => false

mutual
  def transl_stmt
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ce : composite_env) :
      CompCert4Lean.Cfrontend.Csyntax.statement → mon statement
    | .Sskip => ret .Sskip
    | .Sdo e => transl_expr_stmt ce e
    | .Ssequence s1 s2 => do
        let ts1 ← transl_stmt ce s1
        let ts2 ← transl_stmt ce s2
        pure (.Ssequence ts1 ts2)
    | .Sifthenelse e s1 s2 => do
        let ts1 ← transl_stmt ce s1
        let ts2 ← transl_stmt ce s2
        let (s', a) ← transl_expression ce e
        if skipBool s1 && skipBool s2 then
          pure (.Ssequence s' .Sskip)
        else
          pure (.Ssequence s' (.Sifthenelse a ts1 ts2))
    | .Swhile e s1 => do
        let s' ← transl_if ce e .Sskip .Sbreak
        let ts1 ← transl_stmt ce s1
        pure (.Sloop (.Ssequence s' ts1) .Sskip)
    | .Sdowhile e s1 => do
        let s' ← transl_if ce e .Sskip .Sbreak
        let ts1 ← transl_stmt ce s1
        pure (.Sloop ts1 s')
    | .Sfor s1 e2 s3 s4 => do
        let ts1 ← transl_stmt ce s1
        let s' ← transl_if ce e2 .Sskip .Sbreak
        let ts3 ← transl_stmt ce s3
        let ts4 ← transl_stmt ce s4
        if skipBool s1 then
          pure (.Sloop (.Ssequence s' ts4) ts3)
        else
          pure (.Ssequence ts1 (.Sloop (.Ssequence s' ts4) ts3))
    | .Sbreak => ret .Sbreak
    | .Scontinue => ret .Scontinue
    | .Sreturn none => ret (.Sreturn none)
    | .Sreturn (some e) => do
        let (s', a) ← transl_expression ce e
        pure (.Ssequence s' (.Sreturn (some a)))
    | .Sswitch e ls => do
        let (s', a) ← transl_expression ce e
        let tls ← transl_lblstmt ce ls
        pure (.Ssequence s' (.Sswitch a tls))
    | .Slabel lbl s1 => do
        let ts1 ← transl_stmt ce s1
        pure (.Slabel lbl ts1)
    | .Sgoto lbl => ret (.Sgoto lbl)

  def transl_lblstmt
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ce : composite_env) :
      CompCert4Lean.Cfrontend.Csyntax.labeled_statements → mon labeled_statements
    | .LSnil => ret .LSnil
    | .LScons c s rest => do
        let ts ← transl_stmt ce s
        let tls ← transl_lblstmt ce rest
        pure (.LScons c ts tls)
end

/-! ## Translation of functions and programs -/

def transl_function
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ctx : FreshIdentContext) (ce : composite_env)
    (f : CompCert4Lean.Cfrontend.Csyntax.function) : errorsRes function :=
  match transl_stmt ce f.fn_body (initial_generator ctx ()) with
  | .Err message => .Error message
  | .Res tbody g _ =>
      .OK
        { fn_return := f.fn_return
          fn_callconv := f.fn_callconv
          fn_params := f.fn_params
          fn_vars := f.fn_vars
          fn_temps := g.gen_trail
          fn_body := tbody }

def transl_fundef
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ctx : FreshIdentContext) (ce : composite_env)
    (fd : CompCert4Lean.Cfrontend.Csyntax.fundef) : errorsRes fundef :=
  match fd with
  | .Internal f =>
      match transl_function ctx ce f with
      | .OK tf => .OK (.Internal tf)
      | .Error message => .Error message
  | .External ef targs tres cc => .OK (.External ef targs tres cc)

def transl_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ctx : FreshIdentContext)
    (p : CompCert4Lean.Cfrontend.Csyntax.program) : errorsRes program :=
  match CompCert4Lean.Common.AST.transform_partial_program
      (transl_fundef ctx p.prog_comp_env)
      (CompCert4Lean.Cfrontend.Ctypes.program_of_program p) with
  | .Error message => .Error message
  | .OK p1 =>
      .OK
        { prog_defs := p1.prog_defs
          prog_public := p1.prog_public
          prog_main := p1.prog_main
          prog_types := p.prog_types
          prog_comp_env := p.prog_comp_env
          prog_comp_env_eq := p.prog_comp_env_eq }

end CompCert4Lean.Cfrontend.SimplExpr
