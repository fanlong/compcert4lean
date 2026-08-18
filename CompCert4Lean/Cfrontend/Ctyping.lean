import CompCert4Lean.Cfrontend.Cop

/-!
# CompCert C typing predicates

Definition-bearing translation of the selected declarations from
`cfrontend/Ctyping.v`.  The source `wt_val` constructors are represented by
their exact, non-recursive proposition, and proofs assigned to the later proof
phase are recorded as exact proposition descriptors.
-/

namespace CompCert4Lean.Cfrontend.Ctyping

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values

private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

def wt_int (n : CCInt) (sz : intsize) (sg : signedness) : Prop :=
  match sz, sg with
  | .IBool, _ =>
      n = CompCert4Lean.Lib.Integers.Int.zero ∨
        n = CompCert4Lean.Lib.Integers.Int.one
  | .I8, .Unsigned =>
      CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 8) n = n
  | .I8, .Signed =>
      cast_int_int .I8 .Signed n = n
  | .I16, .Unsigned =>
      CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) n = n
  | .I16, .Signed =>
      cast_int_int .I16 .Signed n = n
  | .I32, _ => True

def wt_val (v : val) (ty : type) : Prop :=
  match v, ty with
  | _, .Tvoid => True
  | .Vundef, _ => True
  | .Vint n, .Tint sz sg _ => wt_int n sz sg
  | .Vptr _ _, .Tint .I32 _ _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | .Vlong _, .Tlong _ _ => True
  | .Vptr _ _, .Tlong _ _ => CompCert4Lean.X86_64.Archi.ptr64 = true
  | .Vfloat _, .Tfloat .F64 _ => True
  | .Vsingle _, .Tfloat .F32 _ => True
  | .Vptr _ _, .Tpointer _ _ => True
  | .Vint _, .Tpointer _ _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | .Vlong _, .Tpointer _ _ => CompCert4Lean.X86_64.Archi.ptr64 = true
  | .Vptr _ _, .Tarray _ _ _ => True
  | .Vptr _ _, .Tfunction _ _ _ => True
  | .Vptr _ _, .Tstruct _ _ => True
  | .Vptr _ _, .Tunion _ _ => True
  | _, _ => False

def pres_cast_int_intStatement : Prop :=
  ∀ (sz : intsize) (sg : signedness) (n : CCInt),
    wt_int (cast_int_int sz sg n) sz sg

def wt_val_castedStatement : Prop :=
  ∀ (v : val) (ty : type), val_casted v ty → wt_val v ty

def has_rettype_wt_valStatement : Prop :=
  ∀ (v : val) (ty : type),
    CompCert4Lean.Common.Values.Val.has_rettype v (rettype_of_type ty) → wt_val v ty

end CompCert4Lean.Cfrontend.Ctyping
