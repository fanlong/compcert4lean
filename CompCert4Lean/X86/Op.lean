import CompCert4Lean.Common.Events
import CompCert4Lean.Lib.BoolEqual

/-!
# x86 operators and addressing modes

Definition-bearing translation of CompCert's `x86/Op.v`.  Proof declarations
assigned to later proof migration are represented by exact transparent
proposition descriptors.
-/

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Events
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Floats

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev CCComparison := CompCert4Lean.Lib.Integers.comparison
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj

private abbrev z0 : Z := .Z0
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zOpp := ZArith.BinInt.Z.opp
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

private def boolOfSumbool {P Q : Prop} (d : Sumbool P Q) : Bool :=
  match d with
  | .left _ => true
  | .right _ => false

private def decEqSumbool {A : Type} [DecidableEq A] (x y : A) :
    Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

/-! ## Conditions, addressing modes, and operations -/

inductive condition : Type where
  | Ccomp (c : CCComparison)
  | Ccompu (c : CCComparison)
  | Ccompimm (c : CCComparison) (n : CCInt)
  | Ccompuimm (c : CCComparison) (n : CCInt)
  | Ccompl (c : CCComparison)
  | Ccomplu (c : CCComparison)
  | Ccomplimm (c : CCComparison) (n : CCInt64)
  | Ccompluimm (c : CCComparison) (n : CCInt64)
  | Ccompf (c : CCComparison)
  | Cnotcompf (c : CCComparison)
  | Ccompfs (c : CCComparison)
  | Cnotcompfs (c : CCComparison)
  | Cmaskzero (n : CCInt)
  | Cmasknotzero (n : CCInt)
deriving DecidableEq

export condition (Ccomp Ccompu Ccompimm Ccompuimm Ccompl Ccomplu Ccomplimm
  Ccompluimm Ccompf Cnotcompf Ccompfs Cnotcompfs Cmaskzero Cmasknotzero)

inductive addressing : Type where
  | Aindexed (ofs : Z)
  | Aindexed2 (ofs : Z)
  | Ascaled (scale ofs : Z)
  | Aindexed2scaled (scale ofs : Z)
  | Aglobal (id : ident) (ofs : Ptrofs)
  | Abased (id : ident) (ofs : Ptrofs)
  | Abasedscaled (scale : Z) (id : ident) (ofs : Ptrofs)
  | Ainstack (ofs : Ptrofs)
deriving DecidableEq

export addressing (Aindexed Aindexed2 Ascaled Aindexed2scaled Aglobal Abased
  Abasedscaled Ainstack)

inductive operation : Type where
  | Omove
  | Ointconst (n : CCInt)
  | Olongconst (n : CCInt64)
  | Ofloatconst (n : CCFloat)
  | Osingleconst (n : CCFloat32)
  | Oindirectsymbol (id : ident)
  | Ocast8signed
  | Ocast8unsigned
  | Ocast16signed
  | Ocast16unsigned
  | Oneg
  | Osub
  | Omul
  | Omulimm (n : CCInt)
  | Omulhs
  | Omulhu
  | Odiv
  | Odivu
  | Omod
  | Omodu
  | Oand
  | Oandimm (n : CCInt)
  | Oor
  | Oorimm (n : CCInt)
  | Oxor
  | Oxorimm (n : CCInt)
  | Onot
  | Oshl
  | Oshlimm (n : CCInt)
  | Oshr
  | Oshrimm (n : CCInt)
  | Oshrximm (n : CCInt)
  | Oshru
  | Oshruimm (n : CCInt)
  | Ororimm (n : CCInt)
  | Oshldimm (n : CCInt)
  | Olea (addr : addressing)
  | Omakelong
  | Olowlong
  | Ohighlong
  | Ocast32signed
  | Ocast32unsigned
  | Onegl
  | Oaddlimm (n : CCInt64)
  | Osubl
  | Omull
  | Omullimm (n : CCInt64)
  | Omullhs
  | Omullhu
  | Odivl
  | Odivlu
  | Omodl
  | Omodlu
  | Oandl
  | Oandlimm (n : CCInt64)
  | Oorl
  | Oorlimm (n : CCInt64)
  | Oxorl
  | Oxorlimm (n : CCInt64)
  | Onotl
  | Oshll
  | Oshllimm (n : CCInt)
  | Oshrl
  | Oshrlimm (n : CCInt)
  | Oshrxlimm (n : CCInt)
  | Oshrlu
  | Oshrluimm (n : CCInt)
  | Ororlimm (n : CCInt)
  | Oleal (addr : addressing)
  | Onegf
  | Oabsf
  | Oaddf
  | Osubf
  | Omulf
  | Odivf
  | Omaxf
  | Ominf
  | Onegfs
  | Oabsfs
  | Oaddfs
  | Osubfs
  | Omulfs
  | Odivfs
  | Osingleoffloat
  | Ofloatofsingle
  | Ointoffloat
  | Ofloatofint
  | Ointofsingle
  | Osingleofint
  | Olongoffloat
  | Ofloatoflong
  | Olongofsingle
  | Osingleoflong
  | Ocmp (cond : condition)
  | Osel (cond : condition) (ty : typ)
deriving DecidableEq

export operation (Omove Ointconst Olongconst Ofloatconst Osingleconst
  Oindirectsymbol Ocast8signed Ocast8unsigned Ocast16signed Ocast16unsigned
  Oneg Osub Omul Omulimm Omulhs Omulhu Odiv Odivu Omod Omodu Oand Oandimm
  Oor Oorimm Oxor Oxorimm Onot Oshl Oshlimm Oshr Oshrimm Oshrximm Oshru
  Oshruimm Ororimm Oshldimm Olea Omakelong Olowlong Ohighlong Ocast32signed
  Ocast32unsigned Onegl Oaddlimm Osubl Omull Omullimm Omullhs Omullhu Odivl
  Odivlu Omodl Omodlu Oandl Oandlimm Oorl Oorlimm Oxorl Oxorlimm Onotl Oshll
  Oshllimm Oshrl Oshrlimm Oshrxlimm Oshrlu Oshrluimm Ororlimm Oleal Onegf
  Oabsf Oaddf Osubf Omulf Odivf Omaxf Ominf Onegfs Oabsfs Oaddfs Osubfs
  Omulfs Odivfs Osingleoffloat Ofloatofsingle Ointoffloat Ofloatofint
  Ointofsingle Osingleofint Olongoffloat Ofloatoflong Olongofsingle
  Osingleoflong Ocmp Osel)

/-! ## Equality and floating-point min/max helpers -/

def eq_condition (x y : condition) : Sumbool (x = y) (x ≠ y) :=
  decEqSumbool x y

def eq_addressing (x y : addressing) : Sumbool (x = y) (x ≠ y) :=
  decEqSumbool x y

def beq_operation (x y : operation) : Bool :=
  decide (x = y)

def eq_operation (x y : operation) : Sumbool (x = y) (x ≠ y) :=
  decEqSumbool x y

def float_max (f1 f2 : CCFloat) : CCFloat :=
  match Float.compare f1 f2 with
  | some .Gt => f1
  | some .Eq | some .Lt | none => f2

def maxf (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (float_max f1 f2)
  | _, _ => .Vundef

def float_min (f1 f2 : CCFloat) : CCFloat :=
  match Float.compare f1 f2 with
  | some .Lt => f1
  | some .Eq | some .Gt | none => f2

def minf (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (float_min f1 f2)
  | _, _ => .Vundef

/-! ## Addressing validity -/

def offset_in_range (n : Z) : Bool :=
  boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle Int.min_signed n) &&
    boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle n Int.max_signed)

def ptroffset_min : Z :=
  zOpp (zOfNat 16777216)

def ptroffset_max : Z :=
  zOfNat 16777215

def ptroffset_in_range (n : Ptrofs) : Bool :=
  let signed := Ptrofs.signed n
  boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle ptroffset_min signed) &&
    boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle signed ptroffset_max)

def addressing_valid (a : addressing) : Bool :=
  if CompCert4Lean.X86_64.Archi.ptr64 then
    match a with
    | .Aindexed n => offset_in_range n
    | .Aindexed2 n => offset_in_range n
    | .Ascaled _ ofs => offset_in_range ofs
    | .Aindexed2scaled _ ofs => offset_in_range ofs
    | .Aglobal _ ofs => ptroffset_in_range ofs
    | .Abased _ ofs => ptroffset_in_range ofs
    | .Abasedscaled _ _ ofs => ptroffset_in_range ofs
    | .Ainstack ofs => offset_in_range (Ptrofs.signed ofs)
  else true

/-! ## Evaluation -/

def eval_condition (cond : condition) (vl : List val) (m : mem) : Option Bool :=
  match cond, vl with
  | .Ccomp c, [v1, v2] => Val.cmp_bool c v1 v2
  | .Ccompu c, [v1, v2] => Val.cmpu_bool (Mem.valid_pointer m) c v1 v2
  | .Ccompimm c n, [v1] => Val.cmp_bool c v1 (.Vint n)
  | .Ccompuimm c n, [v1] => Val.cmpu_bool (Mem.valid_pointer m) c v1 (.Vint n)
  | .Ccompl c, [v1, v2] => Val.cmpl_bool c v1 v2
  | .Ccomplu c, [v1, v2] => Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
  | .Ccomplimm c n, [v1] => Val.cmpl_bool c v1 (.Vlong n)
  | .Ccompluimm c n, [v1] => Val.cmplu_bool (Mem.valid_pointer m) c v1 (.Vlong n)
  | .Ccompf c, [v1, v2] => Val.cmpf_bool c v1 v2
  | .Cnotcompf c, [v1, v2] => (Val.cmpf_bool c v1 v2).map (!·)
  | .Ccompfs c, [v1, v2] => Val.cmpfs_bool c v1 v2
  | .Cnotcompfs c, [v1, v2] => (Val.cmpfs_bool c v1 v2).map (!·)
  | .Cmaskzero n, [v1] => Val.maskzero_bool v1 n
  | .Cmasknotzero n, [v1] => (Val.maskzero_bool v1 n).map (!·)
  | _, _ => none

def eval_addressing32 {F V : Type} (genv : Genv.t F V) (sp : val)
    (addr : addressing) (vl : List val) : Option val :=
  match addr, vl with
  | .Aindexed n, [v1] =>
      some (Val.add v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr n)))
  | .Aindexed2 n, [v1, v2] =>
      some (Val.add (Val.add v1 v2) (.Vint (CompCert4Lean.Lib.Integers.Int.repr n)))
  | .Ascaled scale ofs, [v1] =>
      some (Val.add
        (Val.mul v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr scale)))
        (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs)))
  | .Aindexed2scaled scale ofs, [v1, v2] =>
      some (Val.add v1
        (Val.add
          (Val.mul v2 (.Vint (CompCert4Lean.Lib.Integers.Int.repr scale)))
          (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))))
  | .Aglobal id ofs, [] =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else some (Genv.symbol_address genv id ofs)
  | .Abased id ofs, [v1] =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else some (Val.add (Genv.symbol_address genv id ofs) v1)
  | .Abasedscaled scale id ofs, [v1] =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else some (Val.add (Genv.symbol_address genv id ofs)
        (Val.mul v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr scale))))
  | .Ainstack ofs, [] =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else some (Val.offset_ptr sp ofs)
  | _, _ => none

def eval_addressing64 {F V : Type} (genv : Genv.t F V) (sp : val)
    (addr : addressing) (vl : List val) : Option val :=
  match addr, vl with
  | .Aindexed n, [v1] =>
      some (Val.addl v1 (.Vlong (Int64.repr n)))
  | .Aindexed2 n, [v1, v2] =>
      some (Val.addl (Val.addl v1 v2) (.Vlong (Int64.repr n)))
  | .Ascaled scale ofs, [v1] =>
      some (Val.addl (Val.mull v1 (.Vlong (Int64.repr scale)))
        (.Vlong (Int64.repr ofs)))
  | .Aindexed2scaled scale ofs, [v1, v2] =>
      some (Val.addl v1
        (Val.addl (Val.mull v2 (.Vlong (Int64.repr scale)))
          (.Vlong (Int64.repr ofs))))
  | .Aglobal id ofs, [] =>
      if CompCert4Lean.X86_64.Archi.ptr64 then some (Genv.symbol_address genv id ofs)
      else none
  | .Ainstack ofs, [] =>
      if CompCert4Lean.X86_64.Archi.ptr64 then some (Val.offset_ptr sp ofs)
      else none
  | _, _ => none

def eval_addressing {F V : Type} (genv : Genv.t F V) (sp : val)
    (addr : addressing) (vl : List val) : Option val :=
  if CompCert4Lean.X86_64.Archi.ptr64 then eval_addressing64 genv sp addr vl
  else eval_addressing32 genv sp addr vl

def eval_operation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    {F V : Type} (genv : Genv.t F V) (sp : val)
    (op : operation) (vl : List val) (m : mem) : Option val :=
  match op, vl with
  | .Omove, [v1] => some v1
  | .Ointconst n, [] => some (.Vint n)
  | .Olongconst n, [] => some (.Vlong n)
  | .Ofloatconst n, [] => some (.Vfloat n)
  | .Osingleconst n, [] => some (.Vsingle n)
  | .Oindirectsymbol id, [] => some (Genv.symbol_address genv id Ptrofs.zero)
  | .Ocast8signed, [v1] => some (Val.sign_ext (zOfNat 8) v1)
  | .Ocast8unsigned, [v1] => some (Val.zero_ext (zOfNat 8) v1)
  | .Ocast16signed, [v1] => some (Val.sign_ext (zOfNat 16) v1)
  | .Ocast16unsigned, [v1] => some (Val.zero_ext (zOfNat 16) v1)
  | .Oneg, [v1] => some (Val.neg v1)
  | .Osub, [v1, v2] => some (Val.sub v1 v2)
  | .Omul, [v1, v2] => some (Val.mul v1 v2)
  | .Omulimm n, [v1] => some (Val.mul v1 (.Vint n))
  | .Omulhs, [v1, v2] => some (Val.mulhs v1 v2)
  | .Omulhu, [v1, v2] => some (Val.mulhu v1 v2)
  | .Odiv, [v1, v2] => Val.divs v1 v2
  | .Odivu, [v1, v2] => Val.divu v1 v2
  | .Omod, [v1, v2] => Val.mods v1 v2
  | .Omodu, [v1, v2] => Val.modu v1 v2
  | .Oand, [v1, v2] => some (Val.and v1 v2)
  | .Oandimm n, [v1] => some (Val.and v1 (.Vint n))
  | .Oor, [v1, v2] => some (Val.or v1 v2)
  | .Oorimm n, [v1] => some (Val.or v1 (.Vint n))
  | .Oxor, [v1, v2] => some (Val.xor v1 v2)
  | .Oxorimm n, [v1] => some (Val.xor v1 (.Vint n))
  | .Onot, [v1] => some (Val.notint v1)
  | .Oshl, [v1, v2] => some (Val.shl v1 v2)
  | .Oshlimm n, [v1] => some (Val.shl v1 (.Vint n))
  | .Oshr, [v1, v2] => some (Val.shr v1 v2)
  | .Oshrimm n, [v1] => some (Val.shr v1 (.Vint n))
  | .Oshrximm n, [v1] => Val.shrx v1 (.Vint n)
  | .Oshru, [v1, v2] => some (Val.shru v1 v2)
  | .Oshruimm n, [v1] => some (Val.shru v1 (.Vint n))
  | .Ororimm n, [v1] => some (Val.ror v1 (.Vint n))
  | .Oshldimm n, [v1, v2] =>
      some (Val.or (Val.shl v1 (.Vint n))
        (Val.shru v2 (.Vint
          (CompCert4Lean.Lib.Integers.Int.sub
            CompCert4Lean.Lib.Integers.Int.iwordsize n))))
  | .Olea addr, _ => eval_addressing32 genv sp addr vl
  | .Omakelong, [v1, v2] => some (Val.longofwords v1 v2)
  | .Olowlong, [v1] => some (Val.loword v1)
  | .Ohighlong, [v1] => some (Val.hiword v1)
  | .Ocast32signed, [v1] => some (Val.longofint v1)
  | .Ocast32unsigned, [v1] => some (Val.longofintu v1)
  | .Onegl, [v1] => some (Val.negl v1)
  | .Oaddlimm n, [v1] => some (Val.addl v1 (.Vlong n))
  | .Osubl, [v1, v2] => some (Val.subl v1 v2)
  | .Omull, [v1, v2] => some (Val.mull v1 v2)
  | .Omullimm n, [v1] => some (Val.mull v1 (.Vlong n))
  | .Omullhs, [v1, v2] => some (Val.mullhs v1 v2)
  | .Omullhu, [v1, v2] => some (Val.mullhu v1 v2)
  | .Odivl, [v1, v2] => Val.divls v1 v2
  | .Odivlu, [v1, v2] => Val.divlu v1 v2
  | .Omodl, [v1, v2] => Val.modls v1 v2
  | .Omodlu, [v1, v2] => Val.modlu v1 v2
  | .Oandl, [v1, v2] => some (Val.andl v1 v2)
  | .Oandlimm n, [v1] => some (Val.andl v1 (.Vlong n))
  | .Oorl, [v1, v2] => some (Val.orl v1 v2)
  | .Oorlimm n, [v1] => some (Val.orl v1 (.Vlong n))
  | .Oxorl, [v1, v2] => some (Val.xorl v1 v2)
  | .Oxorlimm n, [v1] => some (Val.xorl v1 (.Vlong n))
  | .Onotl, [v1] => some (Val.notl v1)
  | .Oshll, [v1, v2] => some (Val.shll v1 v2)
  | .Oshllimm n, [v1] => some (Val.shll v1 (.Vint n))
  | .Oshrl, [v1, v2] => some (Val.shrl v1 v2)
  | .Oshrlimm n, [v1] => some (Val.shrl v1 (.Vint n))
  | .Oshrxlimm n, [v1] => Val.shrxl v1 (.Vint n)
  | .Oshrlu, [v1, v2] => some (Val.shrlu v1 v2)
  | .Oshrluimm n, [v1] => some (Val.shrlu v1 (.Vint n))
  | .Ororlimm n, [v1] => some (Val.rorl v1 (.Vint n))
  | .Oleal addr, _ => eval_addressing64 genv sp addr vl
  | .Onegf, [v1] => some (Val.negf v1)
  | .Oabsf, [v1] => some (Val.absf v1)
  | .Oaddf, [v1, v2] => some (Val.addf v1 v2)
  | .Osubf, [v1, v2] => some (Val.subf v1 v2)
  | .Omulf, [v1, v2] => some (Val.mulf v1 v2)
  | .Odivf, [v1, v2] => some (Val.divf v1 v2)
  | .Omaxf, [v1, v2] => some (maxf v1 v2)
  | .Ominf, [v1, v2] => some (minf v1 v2)
  | .Onegfs, [v1] => some (Val.negfs v1)
  | .Oabsfs, [v1] => some (Val.absfs v1)
  | .Oaddfs, [v1, v2] => some (Val.addfs v1 v2)
  | .Osubfs, [v1, v2] => some (Val.subfs v1 v2)
  | .Omulfs, [v1, v2] => some (Val.mulfs v1 v2)
  | .Odivfs, [v1, v2] => some (Val.divfs v1 v2)
  | .Osingleoffloat, [v1] => some (Val.singleoffloat v1)
  | .Ofloatofsingle, [v1] => some (Val.floatofsingle v1)
  | .Ointoffloat, [v1] => Val.intoffloat v1
  | .Ofloatofint, [v1] =>
      Val.floatofint (binary64_certificate := binary64_certificate) v1
  | .Ointofsingle, [v1] => Val.intofsingle v1
  | .Osingleofint, [v1] =>
      Val.singleofint (binary32_certificate := binary32_certificate) v1
  | .Olongoffloat, [v1] => Val.longoffloat v1
  | .Ofloatoflong, [v1] =>
      Val.floatoflong (binary64_certificate := binary64_certificate) v1
  | .Olongofsingle, [v1] => Val.longofsingle v1
  | .Osingleoflong, [v1] =>
      Val.singleoflong (binary32_certificate := binary32_certificate) v1
  | .Ocmp c, _ => some (Val.of_optbool (eval_condition c vl m))
  | .Osel c ty, v1 :: v2 :: rest =>
      some (Val.select (eval_condition c rest m) v1 v2 ty)
  | _, _ => none

/-! ## Static typing -/

def type_of_condition : condition → List typ
  | .Ccomp _ | .Ccompu _ => [Tint, Tint]
  | .Ccompimm _ _ | .Ccompuimm _ _ => [Tint]
  | .Ccompl _ | .Ccomplu _ => [Tlong, Tlong]
  | .Ccomplimm _ _ | .Ccompluimm _ _ => [Tlong]
  | .Ccompf _ | .Cnotcompf _ => [Tfloat, Tfloat]
  | .Ccompfs _ | .Cnotcompfs _ => [Tsingle, Tsingle]
  | .Cmaskzero _ | .Cmasknotzero _ => [Tint]

def type_of_addressing_gen (tyA : typ) : addressing → List typ
  | .Aindexed _ => [tyA]
  | .Aindexed2 _ => [tyA, tyA]
  | .Ascaled _ _ => [tyA]
  | .Aindexed2scaled _ _ => [tyA, tyA]
  | .Aglobal _ _ => []
  | .Abased _ _ => [tyA]
  | .Abasedscaled _ _ _ => [tyA]
  | .Ainstack _ => []

def type_of_addressing : addressing → List typ :=
  type_of_addressing_gen Tptr

def type_of_addressing32 : addressing → List typ :=
  type_of_addressing_gen Tint

def type_of_addressing64 : addressing → List typ :=
  type_of_addressing_gen Tlong

def type_of_operation : operation → List typ × typ
  | .Omove => ([], Tint)
  | .Ointconst _ => ([], Tint)
  | .Olongconst _ => ([], Tlong)
  | .Ofloatconst _ => ([], Tfloat)
  | .Osingleconst _ => ([], Tsingle)
  | .Oindirectsymbol _ => ([], Tptr)
  | .Ocast8signed | .Ocast8unsigned | .Ocast16signed | .Ocast16unsigned
  | .Oneg => ([Tint], Tint)
  | .Osub | .Omul | .Omulhs | .Omulhu | .Odiv | .Odivu | .Omod | .Omodu
  | .Oand | .Oor | .Oxor | .Oshl | .Oshr | .Oshru => ([Tint, Tint], Tint)
  | .Omulimm _ | .Oandimm _ | .Oorimm _ | .Oxorimm _ | .Onot
  | .Oshlimm _ | .Oshrimm _ | .Oshrximm _ | .Oshruimm _ | .Ororimm _ =>
      ([Tint], Tint)
  | .Oshldimm _ => ([Tint, Tint], Tint)
  | .Olea addr => (type_of_addressing32 addr, Tint)
  | .Omakelong => ([Tint, Tint], Tlong)
  | .Olowlong | .Ohighlong => ([Tlong], Tint)
  | .Ocast32signed | .Ocast32unsigned => ([Tint], Tlong)
  | .Onegl | .Oaddlimm _ => ([Tlong], Tlong)
  | .Osubl | .Omull | .Omullhs | .Omullhu | .Odivl | .Odivlu | .Omodl
  | .Omodlu | .Oandl | .Oorl | .Oxorl => ([Tlong, Tlong], Tlong)
  | .Omullimm _ | .Oandlimm _ | .Oorlimm _ | .Oxorlimm _ | .Onotl =>
      ([Tlong], Tlong)
  | .Oshll | .Oshrl | .Oshrlu => ([Tlong, Tint], Tlong)
  | .Oshllimm _ | .Oshrlimm _ | .Oshrxlimm _ | .Oshrluimm _ | .Ororlimm _ =>
      ([Tlong], Tlong)
  | .Oleal addr => (type_of_addressing64 addr, Tlong)
  | .Onegf | .Oabsf => ([Tfloat], Tfloat)
  | .Oaddf | .Osubf | .Omulf | .Odivf | .Omaxf | .Ominf =>
      ([Tfloat, Tfloat], Tfloat)
  | .Onegfs | .Oabsfs => ([Tsingle], Tsingle)
  | .Oaddfs | .Osubfs | .Omulfs | .Odivfs => ([Tsingle, Tsingle], Tsingle)
  | .Osingleoffloat => ([Tfloat], Tsingle)
  | .Ofloatofsingle => ([Tsingle], Tfloat)
  | .Ointoffloat => ([Tfloat], Tint)
  | .Ofloatofint => ([Tint], Tfloat)
  | .Ointofsingle => ([Tsingle], Tint)
  | .Osingleofint => ([Tint], Tsingle)
  | .Olongoffloat => ([Tfloat], Tlong)
  | .Ofloatoflong => ([Tlong], Tfloat)
  | .Olongofsingle => ([Tsingle], Tlong)
  | .Osingleoflong => ([Tlong], Tsingle)
  | .Ocmp c => (type_of_condition c, Tint)
  | .Osel c ty => (ty :: ty :: type_of_condition c, ty)

/-! ## Operation transformations and queries -/

def is_move_operation {A : Type} (op : operation) (args : List A) : Option A :=
  match op, args with
  | .Omove, [arg] => some arg
  | _, _ => none

def negate_condition : condition → condition
  | .Ccomp c => .Ccomp (negate_comparison c)
  | .Ccompu c => .Ccompu (negate_comparison c)
  | .Ccompimm c n => .Ccompimm (negate_comparison c) n
  | .Ccompuimm c n => .Ccompuimm (negate_comparison c) n
  | .Ccompl c => .Ccompl (negate_comparison c)
  | .Ccomplu c => .Ccomplu (negate_comparison c)
  | .Ccomplimm c n => .Ccomplimm (negate_comparison c) n
  | .Ccompluimm c n => .Ccompluimm (negate_comparison c) n
  | .Ccompf c => .Cnotcompf c
  | .Cnotcompf c => .Ccompf c
  | .Ccompfs c => .Cnotcompfs c
  | .Cnotcompfs c => .Ccompfs c
  | .Cmaskzero n => .Cmasknotzero n
  | .Cmasknotzero n => .Cmaskzero n

def shift_stack_addressing (delta : Z) : addressing → addressing
  | .Ainstack ofs => .Ainstack (Ptrofs.add ofs (Ptrofs.repr delta))
  | addr => addr

def shift_stack_operation (delta : Z) : operation → operation
  | .Olea addr => .Olea (shift_stack_addressing delta addr)
  | .Oleal addr => .Oleal (shift_stack_addressing delta addr)
  | op => op

def offset_addressing_total (addr : addressing) (delta : Z) : addressing :=
  match addr with
  | .Aindexed n => .Aindexed (zAdd n delta)
  | .Aindexed2 n => .Aindexed2 (zAdd n delta)
  | .Ascaled scale n => .Ascaled scale (zAdd n delta)
  | .Aindexed2scaled scale n => .Aindexed2scaled scale (zAdd n delta)
  | .Aglobal id n => .Aglobal id (Ptrofs.add n (Ptrofs.repr delta))
  | .Abased id n => .Abased id (Ptrofs.add n (Ptrofs.repr delta))
  | .Abasedscaled scale id n =>
      .Abasedscaled scale id (Ptrofs.add n (Ptrofs.repr delta))
  | .Ainstack n => .Ainstack (Ptrofs.add n (Ptrofs.repr delta))

def offset_addressing (addr : addressing) (delta : Z) : Option addressing :=
  let addr' := offset_addressing_total addr delta
  if addressing_valid addr' then some addr' else none

def is_trivial_op : operation → Bool
  | .Omove | .Ointconst _ | .Olongconst _ => true
  | .Olea (.Aglobal _ _) | .Olea (.Ainstack _) => true
  | .Oleal (.Aglobal _ _) | .Oleal (.Ainstack _) => true
  | _ => false

def condition_depends_on_memory : condition → Bool
  | .Ccompu _ => !CompCert4Lean.X86_64.Archi.ptr64
  | .Ccompuimm _ _ => !CompCert4Lean.X86_64.Archi.ptr64
  | .Ccomplu _ => CompCert4Lean.X86_64.Archi.ptr64
  | .Ccompluimm _ _ => CompCert4Lean.X86_64.Archi.ptr64
  | _ => false

def op_depends_on_memory : operation → Bool
  | .Ocmp c | .Osel c _ => condition_depends_on_memory c
  | _ => false

def globals_addressing : addressing → List ident
  | .Aglobal id _ | .Abased id _ | .Abasedscaled _ id _ => [id]
  | _ => []

def globals_operation : operation → List ident
  | .Oindirectsymbol id => [id]
  | .Olea addr | .Oleal addr => globals_addressing addr
  | _ => []

/-! ## Builtin-argument constraints -/

def builtin_arg_ok_1 {A : Type} (ba : builtin_arg A)
    (c : builtin_arg_constraint) : Bool :=
  match c, ba with
  | .OK_all, _ => true
  | .OK_const, .BA_int _ => true
  | .OK_const, .BA_long _ => true
  | .OK_const, .BA_float _ => true
  | .OK_const, .BA_single _ => true
  | .OK_addrstack, .BA_addrstack _ => true
  | .OK_addressing, .BA_addrstack _ => true
  | .OK_addressing, .BA_addrglobal _ _ => true
  | .OK_addressing, .BA_addptr (.BA _) (.BA_int _) => true
  | .OK_addressing, .BA_addptr (.BA _) (.BA_long _) => true
  | _, _ => false

def builtin_arg_ok {A : Type} (ba : builtin_arg A)
    (c : builtin_arg_constraint) : Bool :=
  match ba with
  | .BA _ | .BA_splitlong (.BA _) (.BA _) => true
  | _ => builtin_arg_ok_1 ba c

/-! ## Exact statement descriptors for later proof migration -/

def eval_addressing_AglobalStatement : Prop :=
  ∀ (F V : Type) (genv : Genv.t F V) (sp : val) (id : ident) (ofs : Ptrofs),
    eval_addressing genv sp (.Aglobal id ofs) [] =
      some (Genv.symbol_address genv id ofs)

def eval_addressing_AinstackStatement : Prop :=
  ∀ (F V : Type) (genv : Genv.t F V) (sp : val) (ofs : Ptrofs),
    eval_addressing genv sp (.Ainstack ofs) [] = some (Val.offset_ptr sp ofs)

def eval_addressing_Ainstack_invStatement : Prop :=
  ∀ (F V : Type) (genv : Genv.t F V) (sp : val) (ofs : Ptrofs)
      (vl : List val) (v : val),
    eval_addressing genv sp (.Ainstack ofs) vl = some v →
      vl = [] ∧ v = Val.offset_ptr sp ofs

def type_addStatement : Prop :=
  ∀ v1 v2 : val, Val.has_type (Val.add v1 v2) Tint

def type_addlStatement : Prop :=
  ∀ v1 v2 : val, Val.has_type (Val.addl v1 v2) Tlong

def type_of_addressing64_soundStatement : Prop :=
  ∀ (A V : Type) (genv : Genv.t A V) (addr : addressing) (vl : List val)
      (sp v : val),
    eval_addressing64 genv sp addr vl = some v → Val.has_type v Tlong

def type_of_addressing32_soundStatement : Prop :=
  ∀ (A V : Type) (genv : Genv.t A V) (addr : addressing) (vl : List val)
      (sp v : val),
    eval_addressing32 genv sp addr vl = some v → Val.has_type v Tint

def type_of_operation_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (A V : Type) (genv : Genv.t A V) (op : operation) (vl : List val)
      (sp v : val) (m : mem),
    op ≠ Omove →
    eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) genv sp op vl m = some v →
    Val.has_type v (type_of_operation op).2

def is_move_operation_correctStatement : Prop :=
  ∀ (A : Type) (op : operation) (args : List A) (a : A),
    is_move_operation op args = some a → op = Omove ∧ args = [a]

def eval_negate_conditionStatement : Prop :=
  ∀ (cond : condition) (vl : List val) (m : mem),
    eval_condition (negate_condition cond) vl m = (eval_condition cond vl m).map (!·)

def eval_shift_stack_addressing32Statement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) (sp : block) (addr : addressing)
      (vl : List val) (delta : Z),
    eval_addressing32 ge (.Vptr sp Ptrofs.zero) (shift_stack_addressing delta addr) vl =
      eval_addressing32 ge (.Vptr sp (Ptrofs.repr delta)) addr vl

def eval_shift_stack_addressing64Statement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) (sp : block) (addr : addressing)
      (vl : List val) (delta : Z),
    eval_addressing64 ge (.Vptr sp Ptrofs.zero) (shift_stack_addressing delta addr) vl =
      eval_addressing64 ge (.Vptr sp (Ptrofs.repr delta)) addr vl

def eval_shift_stack_addressingStatement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) (sp : block) (addr : addressing)
      (vl : List val) (delta : Z),
    eval_addressing ge (.Vptr sp Ptrofs.zero) (shift_stack_addressing delta addr) vl =
      eval_addressing ge (.Vptr sp (Ptrofs.repr delta)) addr vl

def eval_shift_stack_operationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) (sp : block) (op : operation)
      (vl : List val) (m : mem) (delta : Z),
    eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge (.Vptr sp Ptrofs.zero) (shift_stack_operation delta op) vl m =
      eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge (.Vptr sp (Ptrofs.repr delta)) op vl m

def eval_offset_addressing_total_32Statement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) (sp : val) (addr : addressing)
      (args : List val) (delta : Z) (v : val),
    eval_addressing32 ge sp addr args = some v →
    eval_addressing32 ge sp (offset_addressing_total addr delta) args =
      some (Val.add v (.Vint (CompCert4Lean.Lib.Integers.Int.repr delta)))

def eval_offset_addressing_total_64Statement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) (sp : val) (addr : addressing)
      (args : List val) (delta : Z) (v : val),
    eval_addressing64 ge sp addr args = some v →
    eval_addressing64 ge sp (offset_addressing_total addr delta) args =
      some (Val.addl v (.Vlong (Int64.repr delta)))

def eval_offset_addressingStatement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) (sp : val) (addr : addressing)
      (args : List val) (delta : Z) (addr' : addressing) (v : val),
    offset_addressing addr delta = some addr' →
    eval_addressing ge sp addr args = some v →
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    eval_addressing ge sp addr' args =
      some (Val.add v (.Vint (CompCert4Lean.Lib.Integers.Int.repr delta)))

def condition_depends_on_memory_correctStatement : Prop :=
  ∀ (c : condition) (args : List val) (m1 m2 : mem),
    condition_depends_on_memory c = false →
      eval_condition c args m1 = eval_condition c args m2

def op_depends_on_memory_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) (sp : val) (op : operation)
      (args : List val) (m1 m2 : mem),
    op_depends_on_memory op = false →
      eval_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge sp op args m1 =
        eval_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge sp op args m2

def eval_addressing32_preservedStatement : Prop :=
  ∀ (F1 F2 V1 V2 : Type) (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2),
    (∀ s : ident, Genv.find_symbol ge2 s = Genv.find_symbol ge1 s) →
    ∀ (sp : val) (addr : addressing) (vl : List val),
      eval_addressing32 ge2 sp addr vl = eval_addressing32 ge1 sp addr vl

def eval_addressing64_preservedStatement : Prop :=
  ∀ (F1 F2 V1 V2 : Type) (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2),
    (∀ s : ident, Genv.find_symbol ge2 s = Genv.find_symbol ge1 s) →
    ∀ (sp : val) (addr : addressing) (vl : List val),
      eval_addressing64 ge2 sp addr vl = eval_addressing64 ge1 sp addr vl

def eval_addressing_preservedStatement : Prop :=
  ∀ (F1 F2 V1 V2 : Type) (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2),
    (∀ s : ident, Genv.find_symbol ge2 s = Genv.find_symbol ge1 s) →
    ∀ (sp : val) (addr : addressing) (vl : List val),
      eval_addressing ge2 sp addr vl = eval_addressing ge1 sp addr vl

def eval_operation_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (F1 F2 V1 V2 : Type) (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2),
    (∀ s : ident, Genv.find_symbol ge2 s = Genv.find_symbol ge1 s) →
    ∀ (sp : val) (op : operation) (vl : List val) (m : mem),
      eval_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge2 sp op vl m =
        eval_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge1 sp op vl m

def eval_condition_injStatement : Prop :=
  ∀ (f : meminj) (m1 m2 : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true →
      Mem.valid_pointer m2 b2
        (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m2 b2
        (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))
        Ptrofs.max_unsigned) →
    (∀ b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
      b1 ≠ b2 →
      Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true →
      Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ (cond : condition) (vl1 vl2 : List val) (b : Bool),
      Val.inject_list f vl1 vl2 →
      eval_condition cond vl1 m1 = some b →
      eval_condition cond vl2 m2 = some b

def eval_addressing32_injStatement : Prop :=
  ∀ (F1 F2 V1 V2 : Type) (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2)
      (f : meminj) (addr : addressing) (sp1 : val) (vl1 : List val)
      (sp2 : val) (vl2 : List val) (v1 : val),
    (∀ id ofs,
      id ∈ globals_addressing addr →
      Val.inject f (Genv.symbol_address ge1 id ofs) (Genv.symbol_address ge2 id ofs)) →
    Val.inject f sp1 sp2 →
    Val.inject_list f vl1 vl2 →
    eval_addressing32 ge1 sp1 addr vl1 = some v1 →
    ∃ v2, eval_addressing32 ge2 sp2 addr vl2 = some v2 ∧ Val.inject f v1 v2

def eval_addressing64_injStatement : Prop :=
  ∀ (F1 F2 V1 V2 : Type) (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2)
      (f : meminj) (addr : addressing) (sp1 : val) (vl1 : List val)
      (sp2 : val) (vl2 : List val) (v1 : val),
    (∀ id ofs,
      id ∈ globals_addressing addr →
      Val.inject f (Genv.symbol_address ge1 id ofs) (Genv.symbol_address ge2 id ofs)) →
    Val.inject f sp1 sp2 →
    Val.inject_list f vl1 vl2 →
    eval_addressing64 ge1 sp1 addr vl1 = some v1 →
    ∃ v2, eval_addressing64 ge2 sp2 addr vl2 = some v2 ∧ Val.inject f v1 v2

def eval_addressing_injStatement : Prop :=
  ∀ (F1 F2 V1 V2 : Type) (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2)
      (f : meminj) (addr : addressing) (sp1 : val) (vl1 : List val)
      (sp2 : val) (vl2 : List val) (v1 : val),
    (∀ id ofs,
      id ∈ globals_addressing addr →
      Val.inject f (Genv.symbol_address ge1 id ofs) (Genv.symbol_address ge2 id ofs)) →
    Val.inject f sp1 sp2 →
    Val.inject_list f vl1 vl2 →
    eval_addressing ge1 sp1 addr vl1 = some v1 →
    ∃ v2, eval_addressing ge2 sp2 addr vl2 = some v2 ∧ Val.inject f v1 v2

def eval_operation_injStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (F1 F2 V1 V2 : Type) (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2)
      (f : meminj) (m1 m2 : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true →
      Mem.valid_pointer m2 b2
        (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m2 b2
        (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))
        Ptrofs.max_unsigned) →
    (∀ b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
      b1 ≠ b2 →
      Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true →
      Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ (op : operation) (sp1 : val) (vl1 : List val) (sp2 : val)
        (vl2 : List val) (v1 : val),
      (∀ id ofs,
        id ∈ globals_operation op →
        Val.inject f (Genv.symbol_address ge1 id ofs)
          (Genv.symbol_address ge2 id ofs)) →
      Val.inject f sp1 sp2 →
      Val.inject_list f vl1 vl2 →
      eval_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge1 sp1 op vl1 m1 = some v1 →
      ∃ v2,
        eval_operation
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) ge2 sp2 op vl2 m2 = some v2 ∧
          Val.inject f v1 v2

def valid_pointer_extendsStatement : Prop :=
  ∀ (m1 m2 : mem), Mem.extends m1 m2 →
    ∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      some (b1, z0) = some (b2, delta) →
      Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true →
      Mem.valid_pointer m2 b2
        (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true

def weak_valid_pointer_extendsStatement : Prop :=
  ∀ (m1 m2 : mem), Mem.extends m1 m2 →
    ∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      some (b1, z0) = some (b2, delta) →
      Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m2 b2
        (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true

def weak_valid_pointer_no_overflow_extendsStatement : Prop :=
  ∀ (m1 : mem) (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
    some (b1, z0) = some (b2, delta) →
    Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true →
    zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))
        Ptrofs.max_unsigned

def valid_different_pointers_extendsStatement : Prop :=
  ∀ (m1 : mem) (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
      (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
    b1 ≠ b2 →
    Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true →
    Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true →
    some (b1, z0) = some (b1', delta1) →
    some (b2, z0) = some (b2', delta2) →
    b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))

def eval_condition_lessdefStatement : Prop :=
  ∀ (cond : condition) (vl1 vl2 : List val) (b : Bool) (m1 m2 : mem),
    Val.lessdef_list vl1 vl2 →
    Mem.extends m1 m2 →
    eval_condition cond vl1 m1 = some b →
    eval_condition cond vl2 m2 = some b

def eval_operation_lessdefStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (F V : Type) (genv : Genv.t F V) (sp : val) (op : operation)
      (vl1 vl2 : List val) (v1 : val) (m1 m2 : mem),
    Val.lessdef_list vl1 vl2 →
    Mem.extends m1 m2 →
    eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) genv sp op vl1 m1 = some v1 →
    ∃ v2,
      eval_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) genv sp op vl2 m2 = some v2 ∧
        Val.lessdef v1 v2

def eval_addressing_lessdefStatement : Prop :=
  ∀ (F V : Type) (genv : Genv.t F V) (sp : val) (addr : addressing)
      (vl1 vl2 : List val) (v1 : val),
    Val.lessdef_list vl1 vl2 →
    eval_addressing genv sp addr vl1 = some v1 →
    ∃ v2, eval_addressing genv sp addr vl2 = some v2 ∧ Val.lessdef v1 v2

def symbol_address_injectStatement : Prop :=
  ∀ (F V : Type) (genv : Genv.t F V) (f : meminj),
    meminj_preserves_globals F V genv f →
    ∀ (id : ident) (ofs : Ptrofs),
      Val.inject f (Genv.symbol_address genv id ofs) (Genv.symbol_address genv id ofs)

def eval_condition_injectStatement : Prop :=
  ∀ (f : meminj) (cond : condition) (vl1 vl2 : List val) (b : Bool)
      (m1 m2 : mem),
    Val.inject_list f vl1 vl2 →
    Mem.inject f m1 m2 →
    eval_condition cond vl1 m1 = some b →
    eval_condition cond vl2 m2 = some b

def eval_addressing_injectStatement : Prop :=
  ∀ (F V : Type) (genv : Genv.t F V) (f : meminj),
    meminj_preserves_globals F V genv f →
    ∀ (sp1 sp2 : block) (delta : Z),
      f sp1 = some (sp2, delta) →
      ∀ (addr : addressing) (vl1 vl2 : List val) (v1 : val),
        Val.inject_list f vl1 vl2 →
        eval_addressing genv (.Vptr sp1 Ptrofs.zero) addr vl1 = some v1 →
        ∃ v2,
          eval_addressing genv (.Vptr sp2 Ptrofs.zero)
            (shift_stack_addressing delta addr) vl2 = some v2 ∧
          Val.inject f v1 v2

def eval_operation_injectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (F V : Type) (genv : Genv.t F V) (f : meminj),
    meminj_preserves_globals F V genv f →
    ∀ (sp1 sp2 : block) (delta : Z),
      f sp1 = some (sp2, delta) →
      ∀ (op : operation) (vl1 vl2 : List val) (v1 : val) (m1 m2 : mem),
        Val.inject_list f vl1 vl2 →
        Mem.inject f m1 m2 →
        eval_operation
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            genv (.Vptr sp1 Ptrofs.zero) op vl1 m1 = some v1 →
        ∃ v2,
          eval_operation
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              genv (.Vptr sp2 Ptrofs.zero)
              (shift_stack_operation delta op) vl2 m2 = some v2 ∧
          Val.inject f v1 v2

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem eval_addressing_Aglobal : eval_addressing_AglobalStatement := by
  intro F V genv sp id ofs
  simp [eval_addressing, eval_addressing32, eval_addressing64,
    CompCert4Lean.X86_64.Archi.ptr64]

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem eval_addressing_Ainstack : eval_addressing_AinstackStatement := by
  intro F V genv sp ofs
  simp [eval_addressing, eval_addressing64,
    CompCert4Lean.X86_64.Archi.ptr64]

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

private theorem cmp_bool_neg (c : CCComparison) (x y : val) :
    Val.cmp_bool (negate_comparison c) x y =
      (Val.cmp_bool c x y).map Bool.not := by
  cases c <;> cases x <;> cases y <;>
    simp [Val.cmp_bool, negate_comparison, CompCert4Lean.Lib.Integers.Int.cmp,
      CompCert4Lean.Lib.Integers.WordCore.cmp]

private theorem cmpu_bool_neg
    (valid_ptr : CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool)
    (c : CCComparison) (x y : val) :
    Val.cmpu_bool valid_ptr (negate_comparison c) x y =
      (Val.cmpu_bool valid_ptr c x y).map Bool.not := by
  cases c <;> cases x <;> cases y <;>
    simp [Val.cmpu_bool, negate_comparison, Val.cmp_different_blocks,
      CompCert4Lean.Lib.Integers.Int.cmp,
      CompCert4Lean.Lib.Integers.Int.cmpu,
      CompCert4Lean.Lib.Integers.Int64.cmp,
      CompCert4Lean.Lib.Integers.Int64.cmpu,
      CompCert4Lean.Lib.Integers.Ptrofs.cmpu,
      CompCert4Lean.Lib.Integers.WordCore.cmp,
      CompCert4Lean.Lib.Integers.WordCore.cmpu,
      CompCert4Lean.X86_64.Archi.ptr64]

private theorem cmpl_bool_neg (c : CCComparison) (x y : val) :
    Val.cmpl_bool (negate_comparison c) x y =
      (Val.cmpl_bool c x y).map Bool.not := by
  cases c <;> cases x <;> cases y <;>
    simp [Val.cmpl_bool, negate_comparison, CompCert4Lean.Lib.Integers.Int64.cmp,
      CompCert4Lean.Lib.Integers.WordCore.cmp]

private theorem cmplu_bool_neg
    (valid_ptr : CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool)
    (c : CCComparison) (x y : val) :
    Val.cmplu_bool valid_ptr (negate_comparison c) x y =
      (Val.cmplu_bool valid_ptr c x y).map Bool.not := by
  cases c <;> cases x <;> cases y <;>
    simp [Val.cmplu_bool, negate_comparison, Val.cmp_different_blocks,
      CompCert4Lean.Lib.Integers.Int64.cmp,
      CompCert4Lean.Lib.Integers.Int64.cmpu,
      CompCert4Lean.Lib.Integers.Ptrofs.cmpu,
      CompCert4Lean.Lib.Integers.WordCore.cmp,
      CompCert4Lean.Lib.Integers.WordCore.cmpu,
      CompCert4Lean.X86_64.Archi.ptr64] <;>
    split <;> simp_all [CompCert4Lean.Lib.Integers.Ptrofs.cmpu]

theorem eval_negate_condition : eval_negate_conditionStatement := by
  intro cond vl m
  cases vl with
  | nil => cases cond <;> rfl
  | cons v1 vl =>
      cases vl with
      | nil =>
          cases cond with
          | Ccomp c => simp [eval_condition, negate_condition]
          | Ccompu c => simp [eval_condition, negate_condition]
          | Ccompimm c n => exact cmp_bool_neg c v1 (.Vint n)
          | Ccompuimm c n =>
              exact cmpu_bool_neg (CompCert4Lean.Common.Memory.Mem.valid_pointer m) c v1 (.Vint n)
          | Ccompl c => simp [eval_condition, negate_condition]
          | Ccomplu c => simp [eval_condition, negate_condition]
          | Ccomplimm c n => exact cmpl_bool_neg c v1 (.Vlong n)
          | Ccompluimm c n =>
              exact cmplu_bool_neg (CompCert4Lean.Common.Memory.Mem.valid_pointer m) c v1 (.Vlong n)
          | Ccompf c => simp [eval_condition, negate_condition]
          | Cnotcompf c => simp [eval_condition, negate_condition]
          | Ccompfs c => simp [eval_condition, negate_condition]
          | Cnotcompfs c => simp [eval_condition, negate_condition]
          | Cmaskzero n => simp [eval_condition, negate_condition]
          | Cmasknotzero n =>
              simp [eval_condition, negate_condition, Function.comp_def]
      | cons v2 vl =>
          cases vl with
          | nil =>
              cases cond with
              | Ccomp c => exact cmp_bool_neg c v1 v2
              | Ccompu c =>
                  exact cmpu_bool_neg (CompCert4Lean.Common.Memory.Mem.valid_pointer m) c v1 v2
              | Ccompimm c n => simp [eval_condition, negate_condition]
              | Ccompuimm c n => simp [eval_condition, negate_condition]
              | Ccompl c => exact cmpl_bool_neg c v1 v2
              | Ccomplu c =>
                  exact cmplu_bool_neg (CompCert4Lean.Common.Memory.Mem.valid_pointer m) c v1 v2
              | Ccomplimm c n => simp [eval_condition, negate_condition]
              | Ccompluimm c n => simp [eval_condition, negate_condition]
              | Ccompf c => rfl
              | Cnotcompf c =>
                  cases h : Val.cmpf_bool c v1 v2 <;>
                    simp [eval_condition, negate_condition, h]
              | Ccompfs c => rfl
              | Cnotcompfs c =>
                  cases h : Val.cmpfs_bool c v1 v2 <;>
                    simp [eval_condition, negate_condition, h]
              | Cmaskzero n => simp [eval_condition, negate_condition]
              | Cmasknotzero n => simp [eval_condition, negate_condition, Function.comp_def]
          | cons v3 vl => cases cond <;> rfl

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Common.Values

theorem type_add : type_addStatement := by
  intro v1 v2
  cases v1 <;> cases v2 <;>
    simp [Val.add, Val.has_type, CompCert4Lean.X86_64.Archi.ptr64]

theorem type_addl : type_addlStatement := by
  intro v1 v2
  cases v1 <;> cases v2 <;>
    simp [Val.addl, Val.has_type, CompCert4Lean.X86_64.Archi.ptr64]

theorem eval_addressing_Ainstack_inv : eval_addressing_Ainstack_invStatement := by
  intro F V genv sp ofs vl v h
  cases vl with
  | nil =>
      simp [eval_addressing, eval_addressing64,
        CompCert4Lean.X86_64.Archi.ptr64] at h
      exact ⟨rfl, h ▸ rfl⟩
  | cons x xs =>
      simp [eval_addressing, eval_addressing64,
        CompCert4Lean.X86_64.Archi.ptr64] at h

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem is_move_operation_correct : is_move_operation_correctStatement := by
  intro A op args a h
  cases op <;> cases args with
  | nil => simp [is_move_operation] at h
  | cons x xs =>
      cases xs with
      | nil => simpa [is_move_operation] using h
      | cons y ys => simp [is_move_operation] at h

theorem eval_shift_stack_addressing32 : eval_shift_stack_addressing32Statement := by
  intro F V ge sp addr vl delta
  cases addr <;> cases vl <;>
    simp [eval_addressing32, shift_stack_addressing,
      CompCert4Lean.X86_64.Archi.ptr64]

theorem type_of_addressing32_sound : type_of_addressing32_soundStatement := by
  intro A V genv addr vl sp v h
  have type_add_local : ∀ v1 v2 : val,
      CompCert4Lean.Common.Values.Val.has_type
        (CompCert4Lean.Common.Values.Val.add v1 v2)
        CompCert4Lean.Common.AST.Tint := by
    intro v1 v2
    cases v1 <;> cases v2 <;>
      simp [CompCert4Lean.Common.Values.Val.add,
        CompCert4Lean.Common.Values.Val.has_type,
        CompCert4Lean.X86_64.Archi.ptr64]
  cases addr with
  | Aindexed ofs =>
      cases vl with
      | nil => simp [eval_addressing32] at h
      | cons v1 vl =>
          cases vl with
          | nil =>
              simp [eval_addressing32] at h
              cases h
              exact type_add_local _ _
          | cons v2 vl => simp [eval_addressing32] at h
  | Aindexed2 ofs =>
      cases vl with
      | nil => simp [eval_addressing32] at h
      | cons v1 vl =>
          cases vl with
          | nil => simp [eval_addressing32] at h
          | cons v2 vl =>
              cases vl with
              | nil =>
                  simp [eval_addressing32] at h
                  cases h
                  exact type_add_local _ _
              | cons v3 vl => simp [eval_addressing32] at h
  | Ascaled scale ofs =>
      cases vl with
      | nil => simp [eval_addressing32] at h
      | cons v1 vl =>
          cases vl with
          | nil =>
              simp [eval_addressing32] at h
              cases h
              exact type_add_local _ _
          | cons v2 vl => simp [eval_addressing32] at h
  | Aindexed2scaled scale ofs =>
      cases vl with
      | nil => simp [eval_addressing32] at h
      | cons v1 vl =>
          cases vl with
          | nil => simp [eval_addressing32] at h
          | cons v2 vl =>
              cases vl with
              | nil =>
                  simp [eval_addressing32] at h
                  cases h
                  exact type_add_local _ _
              | cons v3 vl => simp [eval_addressing32] at h
  | Aglobal id ofs =>
      cases vl <;> simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at h
  | Abased id ofs =>
      cases vl with
      | nil => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at h
      | cons v1 vl =>
          cases vl <;> simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at h
  | Abasedscaled scale id ofs =>
      cases vl with
      | nil => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at h
      | cons v1 vl =>
          cases vl <;> simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at h
  | Ainstack ofs =>
      cases vl <;> simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at h

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open Lean Elab Tactic Meta

private def suffixPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem suffixWordValRepr (bits : Nat) (i : Int) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let iF := (lctx.findFromUserName? `i).get!
    let bitsE := mkFVar bitsF.fvarId
    let iE := mkFVar iF.fvarId
    let e ← mkAppM
      (suffixPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr")
      #[bitsE, iE]
    closeMainGoal Name.anonymous e

private theorem suffixPtrofsReprUnsigned (x : Ptrofs) :
    CompCert4Lean.Lib.Integers.Ptrofs.repr
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) = x := by
  have hx0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z0
      (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  have hxlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      (Int.ofNat (2 ^ CompCert4Lean.Lib.Integers.Ptrofs.wordsize)) := by
    have h := x.intrange.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Ptrofs.modulus at h
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      (Int.ofNat (2 ^ CompCert4Lean.Lib.Integers.Ptrofs.wordsize)) at h
    exact h
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Ptrofs.wordsize x.intval).val = x.val
  have hz :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval) = x.intval :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ _
  rw [← hz, suffixWordValRepr]
  have hmod :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval %
          ((2 ^ CompCert4Lean.Lib.Integers.Ptrofs.wordsize : Nat) : Int) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval :=
    Int.emod_eq_of_lt (show 0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval by exact hx0) hxlt
  rw [hmod]
  have hvalz :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat x.intval) =
        x.intval :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id x.intval (by
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
      exact hx0)
  have hint :
      Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat x.intval) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval := by
    have h := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hvalz
    simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using h
  have hnat :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat x.intval =
        Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval) := by
    rw [← Int.toNat_of_nonneg (show 0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval by exact hx0)] at hint
    exact Int.ofNat.inj hint
  change Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat x.intval
  exact hnat.symm

private theorem suffixPtrofsAddZero (x : Ptrofs) :
    CompCert4Lean.Lib.Integers.Ptrofs.add x
        CompCert4Lean.Lib.Integers.Ptrofs.zero = x := by
  rw [CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api]
  change CompCert4Lean.Lib.Integers.Ptrofs.repr
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned
          CompCert4Lean.Lib.Integers.Ptrofs.zero)
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x)) = x
  have hzero :
      CompCert4Lean.Lib.Integers.Ptrofs.unsigned
          CompCert4Lean.Lib.Integers.Ptrofs.zero =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z0 := by
    rfl
  rw [hzero,
    show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z0
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) =
      CompCert4Lean.Lib.Integers.Ptrofs.unsigned x by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z0 +
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval) = x.intval
      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z0 =
            (0 : Int) by rfl, Int.zero_add]
      exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ _]
  exact suffixPtrofsReprUnsigned x

theorem eval_shift_stack_addressing64 : eval_shift_stack_addressing64Statement := by
  intro F V ge sp addr vl delta
  have hzero (i : Ptrofs) :
      CompCert4Lean.Lib.Integers.Ptrofs.add
          CompCert4Lean.Lib.Integers.Ptrofs.zero
          (CompCert4Lean.Lib.Integers.Ptrofs.add i
            (CompCert4Lean.Lib.Integers.Ptrofs.repr delta)) =
        CompCert4Lean.Lib.Integers.Ptrofs.add
          (CompCert4Lean.Lib.Integers.Ptrofs.repr delta) i := by
    rw [CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api]
    rw [suffixPtrofsAddZero]
    exact CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api _ _
  cases addr <;>
    induction vl with
    | nil =>
        simp [eval_addressing64, shift_stack_addressing,
          CompCert4Lean.X86_64.Archi.ptr64, CompCert4Lean.Common.Values.Val.offset_ptr,
          hzero]
    | cons v vl ih =>
        cases vl with
        | nil =>
            simp [eval_addressing64, shift_stack_addressing,
              CompCert4Lean.X86_64.Archi.ptr64, CompCert4Lean.Common.Values.Val.offset_ptr,
              hzero]
        | cons v2 vl =>
            cases vl <;>
              simp [eval_addressing64, shift_stack_addressing,
                CompCert4Lean.X86_64.Archi.ptr64, CompCert4Lean.Common.Values.Val.offset_ptr,
                hzero]

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem eval_shift_stack_addressing : eval_shift_stack_addressingStatement := by
  intro F V ge sp addr vl delta
  simp [eval_addressing, CompCert4Lean.X86_64.Archi.ptr64]
  exact eval_shift_stack_addressing64 F V ge sp addr vl delta

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem eval_shift_stack_operation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_shift_stack_operationStatement := by
  intro F V ge sp op vl m delta
  cases op with
  | Olea addr =>
      change eval_addressing32 ge
          (.Vptr sp CompCert4Lean.Lib.Integers.Ptrofs.zero)
          (shift_stack_addressing delta addr) vl =
        eval_addressing32 ge
          (.Vptr sp (CompCert4Lean.Lib.Integers.Ptrofs.repr delta)) addr vl
      exact eval_shift_stack_addressing32 F V ge sp addr vl delta
  | Oleal addr =>
      change eval_addressing64 ge
          (.Vptr sp CompCert4Lean.Lib.Integers.Ptrofs.zero)
          (shift_stack_addressing delta addr) vl =
        eval_addressing64 ge
          (.Vptr sp (CompCert4Lean.Lib.Integers.Ptrofs.repr delta)) addr vl
      exact eval_shift_stack_addressing64 F V ge sp addr vl delta
  | _ =>
      simp only [shift_stack_operation]
      cases vl with
      | nil => rfl
      | cons v tail =>
          cases tail with
          | nil => rfl
          | cons v2 tail =>
              cases tail <;> rfl

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem eval_offset_addressing : eval_offset_addressingStatement := by
  intro F V ge sp addr args delta addr' v hoff heval hptr
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem eval_addressing32_preserved : eval_addressing32_preservedStatement := by
  intro F1 F2 V1 V2 ge1 ge2 hfind sp addr vl
  cases addr <;>
    induction vl with
    | nil => simp [eval_addressing32, CompCert4Lean.Common.Globalenvs.Genv.symbol_address, hfind]
    | cons v vl ih =>
        cases vl with
        | nil => simp [eval_addressing32, CompCert4Lean.Common.Globalenvs.Genv.symbol_address, hfind]
        | cons v2 vl =>
            cases vl <;> simp [eval_addressing32, CompCert4Lean.Common.Globalenvs.Genv.symbol_address, hfind]

theorem eval_addressing64_preserved : eval_addressing64_preservedStatement := by
  intro F1 F2 V1 V2 ge1 ge2 hfind sp addr vl
  cases addr <;>
    induction vl with
    | nil => simp [eval_addressing64, CompCert4Lean.Common.Globalenvs.Genv.symbol_address, hfind]
    | cons v vl ih =>
        cases vl with
        | nil => simp [eval_addressing64, CompCert4Lean.Common.Globalenvs.Genv.symbol_address, hfind]
        | cons v2 vl =>
            cases vl <;> simp [eval_addressing64, CompCert4Lean.Common.Globalenvs.Genv.symbol_address, hfind]

theorem condition_depends_on_memory_correct : condition_depends_on_memory_correctStatement := by
  intro c args m1 m2 h
  cases c <;>
    cases args with
    | nil =>
        simp [condition_depends_on_memory, eval_condition,
          CompCert4Lean.X86_64.Archi.ptr64,
          CompCert4Lean.Common.Values.Val.cmpu_bool,
          CompCert4Lean.Common.Values.Val.cmplu_bool] at h ⊢
    | cons a rest =>
        cases rest with
        | nil =>
            simp [condition_depends_on_memory, eval_condition,
              CompCert4Lean.X86_64.Archi.ptr64,
              CompCert4Lean.Common.Values.Val.cmpu_bool,
              CompCert4Lean.Common.Values.Val.cmplu_bool] at h ⊢
        | cons b rest2 =>
            cases rest2 with
            | nil =>
                cases a <;> cases b <;>
                  simp [condition_depends_on_memory, eval_condition,
                    CompCert4Lean.X86_64.Archi.ptr64,
                    CompCert4Lean.Common.Values.Val.cmpu_bool,
                    CompCert4Lean.Common.Values.Val.cmplu_bool] at h ⊢
            | cons d rest3 =>
                simp [condition_depends_on_memory, eval_condition,
                  CompCert4Lean.X86_64.Archi.ptr64,
                  CompCert4Lean.Common.Values.Val.cmpu_bool,
                  CompCert4Lean.Common.Values.Val.cmplu_bool] at h ⊢

theorem op_depends_on_memory_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    op_depends_on_memory_correctStatement := by
  intro F V ge sp op args m1 m2 h
  cases op with
  | Ocmp c =>
      have hc := condition_depends_on_memory_correct c args m1 m2 h
      change some (CompCert4Lean.Common.Values.Val.of_optbool (eval_condition c args m1)) =
        some (CompCert4Lean.Common.Values.Val.of_optbool (eval_condition c args m2))
      rw [hc]
  | Osel c ty =>
      cases args with
      | nil => rfl
      | cons v1 rest =>
          cases rest with
          | nil => rfl
          | cons v2 rest2 =>
              have hc := condition_depends_on_memory_correct c rest2 m1 m2 h
              change some (CompCert4Lean.Common.Values.Val.select
                  (eval_condition c rest2 m1) v1 v2 ty) =
                some (CompCert4Lean.Common.Values.Val.select
                  (eval_condition c rest2 m2) v1 v2 ty)
              rw [hc]
  | _ =>
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b rest2 =>
              cases rest2 <;> rfl

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Common.Values

private theorem suffix_add_inject (f : meminj) (v1 v1' v2 v2' : val) :
    Val.inject f v1 v1' → Val.inject f v2 v2' →
      Val.inject f (Val.add v1 v2) (Val.add v1' v2') := by
  intro h1 h2
  cases h1 <;> cases h2 <;>
    simp [CompCert4Lean.Common.Values.Val.add,
      CompCert4Lean.X86_64.Archi.ptr64] <;>
    constructor <;> try assumption
  all_goals
    subst_vars
    rw [CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api,
      CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api]

private theorem suffix_mul_inject (f : meminj) (v1 v1' v2 v2' : val) :
    Val.inject f v1 v1' → Val.inject f v2 v2' →
      Val.inject f (Val.mul v1 v2) (Val.mul v1' v2') := by
  intro h1 h2
  cases h1 <;> cases h2 <;>
    simp [CompCert4Lean.Common.Values.Val.mul] <;> constructor

theorem eval_addressing32_inj : eval_addressing32_injStatement := by
  intro F1 F2 V1 V2 ge1 ge2 f addr sp1 vl1 sp2 vl2 v1 hglobals hsp hvl heval
  cases hvl with
  | inject_list_nil =>
      cases addr <;>
        simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
  | inject_list_cons a a' ta ta' ha htail =>
      cases htail with
      | inject_list_nil =>
          cases addr with
          | Aindexed n =>
              simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
              subst v1
              exact suffix_add_inject f a a' _ _ ha (Val.inject.inject_int _)
          | Ascaled scale ofs =>
              simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
              subst v1
              apply suffix_add_inject f _ _ _ _
              · exact suffix_mul_inject f a a' _ _ ha (Val.inject.inject_int _)
              · exact Val.inject.inject_int _
          | Abased id ofs =>
              simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
          | Abasedscaled scale id ofs =>
              simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
          | Ainstack ofs =>
              simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
          | _ => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | inject_list_cons b b' tb tb' hb htail2 =>
          cases htail2 with
          | inject_list_nil =>
              cases addr with
              | Aindexed2 n =>
                  simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
                  subst v1
                  apply suffix_add_inject f _ _ _ _
                  · apply suffix_add_inject f a a' b b' ha hb
                  · exact Val.inject.inject_int _
              | Aindexed2scaled scale ofs =>
                  simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
                  subst v1
                  apply suffix_add_inject f _ _ _ _
                  · exact ha
                  · apply suffix_add_inject f _ _ _ _
                    · exact suffix_mul_inject f b b' _ _ hb (Val.inject.inject_int _)
                    · exact Val.inject.inject_int _
              | _ => simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | inject_list_cons c c' tc tc' hc htail3 =>
              cases addr <;>
                simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at heval

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem eval_addressing_preserved : eval_addressing_preservedStatement := by
  intro F1 F2 V1 V2 ge1 ge2 hfind sp addr vl
  unfold eval_addressing
  by_cases hptr : CompCert4Lean.X86_64.Archi.ptr64
  · simp [hptr]
    exact eval_addressing64_preserved F1 F2 V1 V2 ge1 ge2 hfind sp addr vl
  · simp [hptr]
    exact eval_addressing32_preserved F1 F2 V1 V2 ge1 ge2 hfind sp addr vl

theorem eval_operation_preserved
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_operation_preservedStatement := by
  intro F1 F2 V1 V2 ge1 ge2 hfind sp op vl m
  cases op with
  | Oindirectsymbol id =>
      cases vl with
      | nil =>
          change some (CompCert4Lean.Common.Globalenvs.Genv.symbol_address ge2 id
              CompCert4Lean.Lib.Integers.Ptrofs.zero) =
            some (CompCert4Lean.Common.Globalenvs.Genv.symbol_address ge1 id
              CompCert4Lean.Lib.Integers.Ptrofs.zero)
          congr 1
          unfold CompCert4Lean.Common.Globalenvs.Genv.symbol_address
          rw [hfind]
      | cons v tail => rfl
  | Olea addr =>
      change eval_addressing32 ge2 sp addr vl = eval_addressing32 ge1 sp addr vl
      exact eval_addressing32_preserved F1 F2 V1 V2 ge1 ge2 hfind sp addr vl
  | Oleal addr =>
      change eval_addressing64 ge2 sp addr vl = eval_addressing64 ge1 sp addr vl
      exact eval_addressing64_preserved F1 F2 V1 V2 ge1 ge2 hfind sp addr vl
  | _ =>
      cases vl with
      | nil => rfl
      | cons v tail =>
          cases tail with
          | nil => rfl
          | cons v2 tail =>
              cases tail with
              | nil => rfl
              | cons v3 tail => rfl

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Common.Values

private theorem suffix_mull_inject (f : meminj) (v1 v1' v2 v2' : val) :
    Val.inject f v1 v1' → Val.inject f v2 v2' →
      Val.inject f (Val.mull v1 v2) (Val.mull v1' v2') := by
  intro h1 h2
  cases h1 <;> cases h2 <;>
    simp [CompCert4Lean.Common.Values.Val.mull] <;> constructor

private theorem suffix_offset_ptr_inject (f : meminj) (v v' : val) (ofs : Ptrofs) :
    Val.inject f v v' → Val.inject f (Val.offset_ptr v ofs) (Val.offset_ptr v' ofs) := by
  intro h
  cases h with
  | inject_int i => simpa [Val.offset_ptr] using (Val.val_inject_undef f (Val.offset_ptr (Vint i) ofs))
  | inject_long i => simpa [Val.offset_ptr] using (Val.val_inject_undef f (Val.offset_ptr (Vlong i) ofs))
  | inject_float x => simpa [Val.offset_ptr] using (Val.val_inject_undef f (Val.offset_ptr (Vfloat x) ofs))
  | inject_single x => simpa [Val.offset_ptr] using (Val.val_inject_undef f (Val.offset_ptr (Vsingle x) ofs))
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      simp [Val.offset_ptr]
      apply Val.inject.inject_ptr b1 _ b2 _ delta hmap
      subst ofs2
      simp only [CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api,
        CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api]
  | val_inject_undef v =>
      simpa [Val.offset_ptr] using (Val.val_inject_undef f (Val.offset_ptr v' ofs))

theorem eval_addressing64_inj : eval_addressing64_injStatement := by
  intro F1 F2 V1 V2 ge1 ge2 f addr sp1 vl1 sp2 vl2 v1 hglobals hsp hvl heval
  cases hvl with
  | inject_list_nil =>
      cases addr with
      | Aglobal id ofs =>
          simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
          subst v1
          exact hglobals id ofs (by simp [globals_addressing])
      | Ainstack ofs =>
          simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
          subst v1
          exact suffix_offset_ptr_inject f sp1 sp2 ofs hsp
      | _ => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
  | inject_list_cons a a' ta ta' ha htail =>
      cases htail with
      | inject_list_nil =>
          cases addr with
          | Aindexed n =>
              simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
              subst v1
              exact Val.addl_inject f a a' _ _ ha (Val.inject.inject_long _)
          | Ascaled scale ofs =>
              simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
              subst v1
              apply Val.addl_inject f _ _ _ _
              · exact suffix_mull_inject f a a' _ _ ha (Val.inject.inject_long _)
              · exact Val.inject.inject_long _
          | Abased id ofs =>
              simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | Abasedscaled scale id ofs =>
              simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | _ => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
      | inject_list_cons b b' tb tb' hb htail2 =>
          cases htail2 with
          | inject_list_nil =>
              cases addr with
              | Aindexed2 n =>
                  simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
                  subst v1
                  apply Val.addl_inject f _ _ _ _
                  · exact Val.addl_inject f a a' b b' ha hb
                  · exact Val.inject.inject_long _
              | Aindexed2scaled scale ofs =>
                  simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval ⊢
                  subst v1
                  apply Val.addl_inject f _ _ _ _
                  · exact ha
                  · apply Val.addl_inject f _ _ _ _
                    · exact suffix_mull_inject f b b' _ _ hb (Val.inject.inject_long _)
                    · exact Val.inject.inject_long _
              | _ => simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval
          | inject_list_cons c c' tc tc' hc htail3 =>
              cases addr <;>
                simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at heval

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem eval_addressing_inj : eval_addressing_injStatement := by
  intro F1 F2 V1 V2 ge1 ge2 f addr sp1 vl1 sp2 vl2 v1 hglobals hsp hvl heval
  unfold eval_addressing at heval ⊢
  by_cases hptr : CompCert4Lean.X86_64.Archi.ptr64
  · simp [hptr] at heval ⊢
    exact eval_addressing64_inj F1 F2 V1 V2 ge1 ge2 f addr sp1 vl1 sp2 vl2 v1
      hglobals hsp hvl heval
  · simp [hptr] at heval ⊢
    exact eval_addressing32_inj F1 F2 V1 V2 ge1 ge2 f addr sp1 vl1 sp2 vl2 v1
      hglobals hsp hvl heval

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open Lean Elab Tactic Meta
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem valid_pointer_extends : valid_pointer_extendsStatement := by
  intro m1 m2 hext b1 ofs b2 delta hmap hp
  have hpair :
      (b1, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0) =
        (b2, delta) :=
    Option.some.inj hmap
  cases hpair
  have hp1 :
      CompCert4Lean.Common.Memory.Mem.perm m1 b1
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
        CompCert4Lean.Common.Memtype.perm_kind.Cur
        CompCert4Lean.Common.Memtype.permission.Nonempty :=
    (CompCert4Lean.Common.Memory.Mem.valid_pointer_nonempty_perm m1 b1
      (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)).mp hp
  have hp2 := hext.mext_inj.mi_perm b1 b1
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0
      (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
      CompCert4Lean.Common.Memtype.perm_kind.Cur
      CompCert4Lean.Common.Memtype.permission.Nonempty (by rfl) hp1
  have hrepr :
      CompCert4Lean.Lib.Integers.Ptrofs.repr
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
        CompCert4Lean.Lib.Integers.Ptrofs.zero := by
    rfl
  have hzadd :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
          (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
        CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs := by
    change zOfInt (intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) +
      intOfZ CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0) =
      CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs
    rw [show intOfZ
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
          (0 : Int) by rfl, Int.add_zero]
    exact zOfInt_intOfZ _
  have hadd (x : CompCert4Lean.Lib.Integers.Ptrofs.int) :
      CompCert4Lean.Lib.Integers.Ptrofs.add x
          CompCert4Lean.Lib.Integers.Ptrofs.zero = x := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "suffixPtrofsAddZero")
        | throwError "frozen helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `x
      evalTactic (← `(tactic| exact $stx $arg))
  rw [hrepr, hadd]
  have hp2' :
      CompCert4Lean.Common.Memory.Mem.perm m2 b1
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
        CompCert4Lean.Common.Memtype.perm_kind.Cur
        CompCert4Lean.Common.Memtype.permission.Nonempty := by
    change CompCert4Lean.Common.Memory.Mem.perm m2 b1
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)
      CompCert4Lean.Common.Memtype.perm_kind.Cur
      CompCert4Lean.Common.Memtype.permission.Nonempty at hp2
    rw [hzadd] at hp2
    exact hp2
  apply (CompCert4Lean.Common.Memory.Mem.valid_pointer_nonempty_perm m2 b1
      (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)).mpr
  exact hp2'

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem valid_different_pointers_extends : valid_different_pointers_extendsStatement := by
  intro m1 b1 ofs1 b2 ofs2 b1' delta1 b2' delta2 hneq hp1 hp2 hmap1 hmap2
  have hpair1 := Option.some.inj hmap1
  have hpair2 := Option.some.inj hmap2
  cases hpair1
  cases hpair2
  exact Or.inl hneq

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem weak_valid_pointer_no_overflow_extends :
    weak_valid_pointer_no_overflow_extendsStatement := by
  intro m1 b1 ofs b2 delta hmap hp
  have hpair := Option.some.inj hmap
  cases hpair
  have hrepr :
      CompCert4Lean.Lib.Integers.Ptrofs.repr
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
        CompCert4Lean.Lib.Integers.Ptrofs.zero := by
    rfl
  have huzero :
      CompCert4Lean.Lib.Integers.Ptrofs.unsigned
          CompCert4Lean.Lib.Integers.Ptrofs.zero =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 := by
    rfl
  rw [hrepr, huzero]
  have hzadd :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
          (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
        CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs := by
    change zOfInt (intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) +
      intOfZ CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0) =
      CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs
    rw [show intOfZ
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
          (0 : Int) by rfl, Int.add_zero]
    exact zOfInt_intOfZ _
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0) ∧
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)
      CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned
  rw [hzadd]
  constructor
  · have h := ofs.intrange.1
    change (-1 : Int) <
      intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) at h
    change 0 ≤ intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
    omega
  · have h := ofs.intrange.2
    change intOfZ ofs.intval <
      intOfZ CompCert4Lean.Lib.Integers.Ptrofs.modulus at h
    change intOfZ ofs.intval ≤ _
    change intOfZ ofs.intval ≤
      intOfZ CompCert4Lean.Lib.Integers.Ptrofs.modulus - 1
    omega

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

open Lean Elab Tactic Meta

private theorem suffix_mem_valid_pointer_extends_z
    (m1 m2 : CompCert4Lean.Common.Memory.mem)
    (hext : CompCert4Lean.Common.Memory.Mem.extends m1 m2)
    (b : CompCert4Lean.Common.Values.block) (ofs : Z)
    (hp : CompCert4Lean.Common.Memory.Mem.valid_pointer m1 b ofs = true) :
    CompCert4Lean.Common.Memory.Mem.valid_pointer m2 b ofs = true := by
  have hp1 :
      CompCert4Lean.Common.Memory.Mem.perm m1 b ofs
        CompCert4Lean.Common.Memtype.perm_kind.Cur
        CompCert4Lean.Common.Memtype.permission.Nonempty :=
    (CompCert4Lean.Common.Memory.Mem.valid_pointer_nonempty_perm m1 b ofs).mp hp
  have hp2 := hext.mext_inj.mi_perm b b
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 ofs
      CompCert4Lean.Common.Memtype.perm_kind.Cur
      CompCert4Lean.Common.Memtype.permission.Nonempty (by rfl) hp1
  have hzadd :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 = ofs := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs + 0)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
    rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    simp
  change CompCert4Lean.Common.Memory.Mem.perm m2 b
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)
      CompCert4Lean.Common.Memtype.perm_kind.Cur
      CompCert4Lean.Common.Memtype.permission.Nonempty at hp2
  rw [hzadd] at hp2
  exact (CompCert4Lean.Common.Memory.Mem.valid_pointer_nonempty_perm m2 b ofs).mpr hp2

theorem weak_valid_pointer_extends : weak_valid_pointer_extendsStatement := by
  intro m1 m2 hext b1 ofs b2 delta hmap hp
  have hpair :
      (b1, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0) =
        (b2, delta) :=
    Option.some.inj hmap
  cases hpair
  have hadd (x : CompCert4Lean.Lib.Integers.Ptrofs.int) :
      CompCert4Lean.Lib.Integers.Ptrofs.add x
          CompCert4Lean.Lib.Integers.Ptrofs.zero = x := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "suffixPtrofsAddZero")
        | throwError "frozen helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `x
      evalTactic (← `(tactic| exact $stx $arg))
  have hrepr :
      CompCert4Lean.Lib.Integers.Ptrofs.repr
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
        CompCert4Lean.Lib.Integers.Ptrofs.zero := by
    rfl
  rw [hrepr, hadd]
  unfold CompCert4Lean.Common.Memory.Mem.weak_valid_pointer at hp ⊢
  cases hfirst : CompCert4Lean.Common.Memory.Mem.valid_pointer m1 b1
      (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) with
  | false =>
      cases hsecond : CompCert4Lean.Common.Memory.Mem.valid_pointer m1 b1
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
            (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
              (.xH))) with
      | false => simp [hfirst, hsecond] at hp
      | true =>
          have hb := suffix_mem_valid_pointer_extends_z m1 m2 hext b1
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
              (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
                (.xH)))
            (by simpa [hsecond])
          simp [hfirst, hsecond, hb]
  | true =>
      have hb := suffix_mem_valid_pointer_extends_z m1 m2 hext b1
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
        (by simpa [hfirst])
      simp [hfirst, hb]

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open Lean Elab Tactic Meta

private theorem suffix_val_inject_lessdef (v1 v2 : CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.lessdef v1 v2 →
      CompCert4Lean.Common.Values.Val.inject
        (fun b => some (b, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)) v1 v2 := by
  intro h
  cases h with
  | lessdef_refl =>
      cases v1 with
      | Vint n => exact CompCert4Lean.Common.Values.Val.inject.inject_int _
      | Vlong n => exact CompCert4Lean.Common.Values.Val.inject.inject_long _
      | Vfloat f => exact CompCert4Lean.Common.Values.Val.inject.inject_float _
      | Vsingle f => exact CompCert4Lean.Common.Values.Val.inject.inject_single _
      | Vptr b ofs =>
          have hofs : ofs = CompCert4Lean.Lib.Integers.Ptrofs.add ofs
              (CompCert4Lean.Lib.Integers.Ptrofs.repr
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0) := by
            have hrepr :
                CompCert4Lean.Lib.Integers.Ptrofs.repr
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
                  CompCert4Lean.Lib.Integers.Ptrofs.zero := by
              rfl
            have hadd (x : CompCert4Lean.Lib.Integers.Ptrofs.int) :
                CompCert4Lean.Lib.Integers.Ptrofs.add x
                    CompCert4Lean.Lib.Integers.Ptrofs.zero = x := by
              run_tac
                let env ← getEnv
                let some (n, _) := env.constants.toList.find?
                    (fun (n, _) => (toString n).endsWith "suffixPtrofsAddZero")
                  | throwError "frozen helper not found"
                let stx := Lean.mkIdent n
                let arg := Lean.mkIdent `x
                evalTactic (← `(tactic| exact $stx $arg))
            rw [hrepr, hadd]
          exact CompCert4Lean.Common.Values.Val.inject.inject_ptr b ofs b ofs
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0
            (by rfl) hofs
      | Vundef => exact CompCert4Lean.Common.Values.Val.inject.val_inject_undef _
  | lessdef_undef =>
      exact CompCert4Lean.Common.Values.Val.inject.val_inject_undef _

private theorem suffix_val_inject_list_lessdef
    (vl1 vl2 : List CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.lessdef_list vl1 vl2 →
      CompCert4Lean.Common.Values.Val.inject_list
        (fun b => some (b, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)) vl1 vl2 := by
  intro h
  induction h with
  | lessdef_list_nil =>
      exact @CompCert4Lean.Common.Values.Val.inject_list.inject_list_nil
        (fun b => some (b, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0))
  | lessdef_list_cons v1 v2 vl1 vl2 hhead htail ih =>
      exact @CompCert4Lean.Common.Values.Val.inject_list.inject_list_cons
        (fun b => some (b, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)) v1 v2 vl1 vl2
        (suffix_val_inject_lessdef v1 v2 hhead) ih

private theorem suffix_weak_valid_pointer_extends_z
    (m1 m2 : CompCert4Lean.Common.Memory.mem)
    (hext : CompCert4Lean.Common.Memory.Mem.extends m1 m2)
    (b : CompCert4Lean.Common.Values.block) (ofs : Z)
    (hp : CompCert4Lean.Common.Memory.Mem.weak_valid_pointer m1 b ofs = true) :
    CompCert4Lean.Common.Memory.Mem.weak_valid_pointer m2 b ofs = true := by
  have hvalid : ∀ (q : CompCert4Lean.Common.Values.block) (r : Z),
      CompCert4Lean.Common.Memory.Mem.valid_pointer m1 q r = true →
      CompCert4Lean.Common.Memory.Mem.valid_pointer m2 q r = true := by
    intro q r h
    exact suffix_mem_valid_pointer_extends_z m1 m2 hext q r h
  unfold CompCert4Lean.Common.Memory.Mem.weak_valid_pointer at hp ⊢
  cases h1 : CompCert4Lean.Common.Memory.Mem.valid_pointer m1 b ofs with
  | false =>
      cases h2 : CompCert4Lean.Common.Memory.Mem.valid_pointer m1 b
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub ofs
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos (.xH))) with
      | false => simp [h1, h2] at hp
      | true =>
          have h := hvalid b
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub ofs
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos (.xH)))
            (by simpa [h2])
          simp [h1, h2, h]
  | true =>
      have h := hvalid b ofs (by simpa [h1])
      simp [h1, h]

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

private theorem suffix_cmp_bool_lessdef
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v1' v2 v2' : CompCert4Lean.Common.Values.val) (b : Bool)
    (h1 : CompCert4Lean.Common.Values.Val.lessdef v1 v1')
    (h2 : CompCert4Lean.Common.Values.Val.lessdef v2 v2') :
    CompCert4Lean.Common.Values.Val.cmp_bool c v1 v2 = some b →
      CompCert4Lean.Common.Values.Val.cmp_bool c v1' v2' = some b := by
  cases h1 <;> cases h2 <;>
    simp [CompCert4Lean.Common.Values.Val.cmp_bool] at *

private theorem suffix_cmpl_bool_lessdef
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v1' v2 v2' : CompCert4Lean.Common.Values.val) (b : Bool)
    (h1 : CompCert4Lean.Common.Values.Val.lessdef v1 v1')
    (h2 : CompCert4Lean.Common.Values.Val.lessdef v2 v2') :
    CompCert4Lean.Common.Values.Val.cmpl_bool c v1 v2 = some b →
      CompCert4Lean.Common.Values.Val.cmpl_bool c v1' v2' = some b := by
  cases h1 <;> cases h2 <;>
    simp [CompCert4Lean.Common.Values.Val.cmpl_bool] at *

private theorem suffix_cmpu_bool_lessdef
    (valid_ptr valid_ptr' : CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool)
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v1' v2 v2' : CompCert4Lean.Common.Values.val) (b : Bool)
    (h1 : CompCert4Lean.Common.Values.Val.lessdef v1 v1')
    (h2 : CompCert4Lean.Common.Values.Val.lessdef v2 v2')
    (hvalid : ∀ b ofs, valid_ptr b ofs = true → valid_ptr' b ofs = true) :
    CompCert4Lean.Common.Values.Val.cmpu_bool valid_ptr c v1 v2 = some b →
      CompCert4Lean.Common.Values.Val.cmpu_bool valid_ptr' c v1' v2' = some b := by
  cases h1 <;> cases h2 <;>
    simp [CompCert4Lean.Common.Values.Val.cmpu_bool,
      CompCert4Lean.X86_64.Archi.ptr64] at *

private theorem suffix_cmplu_bool_lessdef
    (valid_ptr valid_ptr' : CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool)
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v1' v2 v2' : CompCert4Lean.Common.Values.val) (b : Bool)
    (h1 : CompCert4Lean.Common.Values.Val.lessdef v1 v1')
    (h2 : CompCert4Lean.Common.Values.Val.lessdef v2 v2')
    (hvalid : ∀ b ofs, valid_ptr b ofs = true → valid_ptr' b ofs = true)
    (hweak : ∀ b ofs,
      (valid_ptr b ofs || valid_ptr b
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub ofs
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.positive.xH))) = true →
      (valid_ptr' b ofs || valid_ptr' b
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub ofs
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.positive.xH))) = true) :
    CompCert4Lean.Common.Values.Val.cmplu_bool valid_ptr c v1 v2 = some b →
      CompCert4Lean.Common.Values.Val.cmplu_bool valid_ptr' c v1' v2' = some b := by
  cases h1 <;> cases h2
  all_goals simp [CompCert4Lean.Common.Values.Val.cmplu_bool,
    CompCert4Lean.X86_64.Archi.ptr64] at *
  all_goals cases v1 <;> cases v2 <;>
    simp [CompCert4Lean.Common.Values.Val.cmplu_bool,
      CompCert4Lean.X86_64.Archi.ptr64] at *
  all_goals
    repeat first | split
    all_goals simp_all [hvalid, hweak]

private theorem suffix_cmpf_bool_lessdef
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v1' v2 v2' : CompCert4Lean.Common.Values.val) (b : Bool)
    (h1 : CompCert4Lean.Common.Values.Val.lessdef v1 v1')
    (h2 : CompCert4Lean.Common.Values.Val.lessdef v2 v2') :
    CompCert4Lean.Common.Values.Val.cmpf_bool c v1 v2 = some b →
      CompCert4Lean.Common.Values.Val.cmpf_bool c v1' v2' = some b := by
  cases h1 <;> cases h2 <;>
    simp [CompCert4Lean.Common.Values.Val.cmpf_bool] at *

private theorem suffix_cmpfs_bool_lessdef
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v1' v2 v2' : CompCert4Lean.Common.Values.val) (b : Bool)
    (h1 : CompCert4Lean.Common.Values.Val.lessdef v1 v1')
    (h2 : CompCert4Lean.Common.Values.Val.lessdef v2 v2') :
    CompCert4Lean.Common.Values.Val.cmpfs_bool c v1 v2 = some b →
      CompCert4Lean.Common.Values.Val.cmpfs_bool c v1' v2' = some b := by
  cases h1 <;> cases h2 <;>
    simp [CompCert4Lean.Common.Values.Val.cmpfs_bool] at *

private theorem suffix_maskzero_bool_lessdef
    (v1 v2 : CompCert4Lean.Common.Values.val)
    (mask : CompCert4Lean.Lib.Integers.int) (b : Bool)
    (h : CompCert4Lean.Common.Values.Val.lessdef v1 v2) :
    CompCert4Lean.Common.Values.Val.maskzero_bool v1 mask = some b →
      CompCert4Lean.Common.Values.Val.maskzero_bool v2 mask = some b := by
  cases h <;> simp [CompCert4Lean.Common.Values.Val.maskzero_bool] at *

private theorem suffix_cmp_bool_lessdef_right
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v2 x : CompCert4Lean.Common.Values.val) (b : Bool)
    (h : CompCert4Lean.Common.Values.Val.lessdef v1 v2) :
    CompCert4Lean.Common.Values.Val.cmp_bool c v1 x = some b →
      CompCert4Lean.Common.Values.Val.cmp_bool c v2 x = some b := by
  exact suffix_cmp_bool_lessdef c v1 v2 x x b h
    (CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _)

private theorem suffix_cmpu_bool_lessdef_right
    (valid_ptr valid_ptr' : CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool)
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v2 x : CompCert4Lean.Common.Values.val) (b : Bool)
    (h : CompCert4Lean.Common.Values.Val.lessdef v1 v2)
    (hvalid : ∀ b ofs, valid_ptr b ofs = true → valid_ptr' b ofs = true) :
    CompCert4Lean.Common.Values.Val.cmpu_bool valid_ptr c v1 x = some b →
      CompCert4Lean.Common.Values.Val.cmpu_bool valid_ptr' c v2 x = some b := by
  exact suffix_cmpu_bool_lessdef valid_ptr valid_ptr' c v1 v2 x x b h
    (CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _) hvalid

private theorem suffix_cmpl_bool_lessdef_right
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v2 x : CompCert4Lean.Common.Values.val) (b : Bool)
    (h : CompCert4Lean.Common.Values.Val.lessdef v1 v2) :
    CompCert4Lean.Common.Values.Val.cmpl_bool c v1 x = some b →
      CompCert4Lean.Common.Values.Val.cmpl_bool c v2 x = some b := by
  exact suffix_cmpl_bool_lessdef c v1 v2 x x b h
    (CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _)

private theorem suffix_cmplu_bool_lessdef_right
    (valid_ptr valid_ptr' : CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool)
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v2 x : CompCert4Lean.Common.Values.val) (b : Bool)
    (h : CompCert4Lean.Common.Values.Val.lessdef v1 v2)
    (hvalid : ∀ b ofs, valid_ptr b ofs = true → valid_ptr' b ofs = true)
    (hweak : ∀ b ofs,
      (valid_ptr b ofs || valid_ptr b
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub ofs
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.xH))) = true →
      (valid_ptr' b ofs || valid_ptr' b
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub ofs
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.xH))) = true) :
    CompCert4Lean.Common.Values.Val.cmplu_bool valid_ptr c v1 x = some b →
      CompCert4Lean.Common.Values.Val.cmplu_bool valid_ptr' c v2 x = some b := by
  exact suffix_cmplu_bool_lessdef valid_ptr valid_ptr' c v1 v2 x x b h
    (CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _) hvalid hweak

private theorem suffix_cmpf_bool_lessdef_right
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v2 x : CompCert4Lean.Common.Values.val) (b : Bool)
    (h : CompCert4Lean.Common.Values.Val.lessdef v1 v2) :
    CompCert4Lean.Common.Values.Val.cmpf_bool c v1 x = some b →
      CompCert4Lean.Common.Values.Val.cmpf_bool c v2 x = some b := by
  exact suffix_cmpf_bool_lessdef c v1 v2 x x b h
    (CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _)

private theorem suffix_cmpfs_bool_lessdef_right
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v2 x : CompCert4Lean.Common.Values.val) (b : Bool)
    (h : CompCert4Lean.Common.Values.Val.lessdef v1 v2) :
    CompCert4Lean.Common.Values.Val.cmpfs_bool c v1 x = some b →
      CompCert4Lean.Common.Values.Val.cmpfs_bool c v2 x = some b := by
  exact suffix_cmpfs_bool_lessdef c v1 v2 x x b h
    (CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _)

private theorem suffix_maskzero_bool_lessdef_right
    (v1 v2 : CompCert4Lean.Common.Values.val)
    (mask : CompCert4Lean.Lib.Integers.int) (b : Bool)
    (h : CompCert4Lean.Common.Values.Val.lessdef v1 v2) :
    CompCert4Lean.Common.Values.Val.maskzero_bool v1 mask = some b →
      CompCert4Lean.Common.Values.Val.maskzero_bool v2 mask = some b :=
  suffix_maskzero_bool_lessdef v1 v2 mask b h

theorem eval_condition_lessdef : eval_condition_lessdefStatement := by
  intro cond vl1 vl2 b m1 m2 hvl hm heval
  have hvalid : ∀ (b : CompCert4Lean.Common.Values.block)
      (ofs : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z),
      CompCert4Lean.Common.Memory.Mem.valid_pointer m1 b ofs = true →
      CompCert4Lean.Common.Memory.Mem.valid_pointer m2 b ofs = true := by
    intro b ofs h
    exact suffix_mem_valid_pointer_extends_z m1 m2 hm b ofs h
  have hweak : ∀ (b : CompCert4Lean.Common.Values.block)
      (ofs : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z),
      (CompCert4Lean.Common.Memory.Mem.valid_pointer m1 b ofs ||
        CompCert4Lean.Common.Memory.Mem.valid_pointer m1 b
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub ofs
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.xH))) = true →
      (CompCert4Lean.Common.Memory.Mem.valid_pointer m2 b ofs ||
        CompCert4Lean.Common.Memory.Mem.valid_pointer m2 b
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub ofs
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.xH))) = true := by
    intro b ofs h
    exact suffix_weak_valid_pointer_extends_z m1 m2 hm b ofs h
  cases hvl with
  | lessdef_list_nil =>
      cases cond <;> simp [eval_condition] at heval ⊢
  | lessdef_list_cons v1 v2 vl1 vl2 h1 ht =>
      cases ht with
      | lessdef_list_nil =>
          cases cond <;> simp [eval_condition] at heval ⊢
          all_goals
            first
            | apply suffix_cmp_bool_lessdef_right <;> assumption
            | apply suffix_cmpu_bool_lessdef_right <;> assumption
            | apply suffix_cmpl_bool_lessdef_right <;> assumption
            | apply suffix_cmplu_bool_lessdef_right <;> assumption
            | apply suffix_cmpf_bool_lessdef_right <;> assumption
            | apply suffix_cmpfs_bool_lessdef_right <;> assumption
            | apply suffix_maskzero_bool_lessdef_right <;> assumption
      | lessdef_list_cons v1' v2' vl1' vl2' h2 ht2 =>
          cases ht2 with
          | lessdef_list_nil =>
              cases cond <;> simp [eval_condition] at heval ⊢
              all_goals
                first
                | apply suffix_cmp_bool_lessdef <;> assumption
                | apply suffix_cmpu_bool_lessdef <;> assumption
                | apply suffix_cmpl_bool_lessdef <;> assumption
                | apply suffix_cmplu_bool_lessdef <;> assumption
                | apply suffix_cmpf_bool_lessdef <;> assumption
                | apply suffix_cmpfs_bool_lessdef <;> assumption
          | lessdef_list_cons v1'' v2'' vl1'' vl2'' h3 ht3 =>
              cases cond <;> simp [eval_condition] at heval ⊢

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open Lean Elab Tactic Meta

private theorem suffix_eval_addressing_lessdef_ptrofs_add_zero
    (x : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add x
        CompCert4Lean.Lib.Integers.Ptrofs.zero = x := by
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "suffixPtrofsAddZero")
      | throwError "frozen helper not found"
    let stx := Lean.mkIdent n
    let arg := Lean.mkIdent `x
    evalTactic (← `(tactic| exact $stx $arg))

private theorem suffix_eval_addressing_lessdef_to_inject
    (v1 v2 : CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.lessdef v1 v2 →
      CompCert4Lean.Common.Values.Val.inject
        (fun b => some (b,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)) v1 v2 := by
  intro h
  cases h with
  | lessdef_refl =>
      cases v1 with
      | Vint n => exact CompCert4Lean.Common.Values.Val.inject.inject_int n
      | Vlong n => exact CompCert4Lean.Common.Values.Val.inject.inject_long n
      | Vfloat f => exact CompCert4Lean.Common.Values.Val.inject.inject_float f
      | Vsingle f => exact CompCert4Lean.Common.Values.Val.inject.inject_single f
      | Vptr b ofs =>
          apply CompCert4Lean.Common.Values.Val.inject.inject_ptr b ofs b ofs
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0
          · rfl
          · rw [show CompCert4Lean.Lib.Integers.Ptrofs.repr
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
              CompCert4Lean.Lib.Integers.Ptrofs.zero by rfl,
              suffix_eval_addressing_lessdef_ptrofs_add_zero]
      | Vundef =>
          exact CompCert4Lean.Common.Values.Val.inject.val_inject_undef _
  | lessdef_undef =>
      exact CompCert4Lean.Common.Values.Val.inject.val_inject_undef _

private theorem suffix_eval_addressing_lessdef_list_to_inject
    (vl1 vl2 : List CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.lessdef_list vl1 vl2 →
      CompCert4Lean.Common.Values.Val.inject_list
        (fun b => some (b,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)) vl1 vl2 := by
  intro h
  induction h with
  | lessdef_list_nil =>
      exact CompCert4Lean.Common.Values.Val.inject_list.inject_list_nil
  | lessdef_list_cons v1 v2 vl1 vl2 hhead htail ih =>
      exact CompCert4Lean.Common.Values.Val.inject_list.inject_list_cons
        v1 v2 vl1 vl2 (suffix_eval_addressing_lessdef_to_inject v1 v2 hhead) ih

private theorem suffix_eval_addressing_lessdef_of_inject
    (v1 v2 : CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.inject
        (fun b => some (b,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)) v1 v2 →
      CompCert4Lean.Common.Values.Val.lessdef v1 v2 := by
  intro h
  cases h with
  | inject_int i => exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _
  | inject_long i => exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _
  | inject_float f => exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _
  | inject_single f => exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      have hpair :
          (b1, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0) =
            (b2, delta) := Option.some.inj hmap
      cases hpair
      rw [show CompCert4Lean.Lib.Integers.Ptrofs.repr
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
              CompCert4Lean.Lib.Integers.Ptrofs.zero by rfl,
          suffix_eval_addressing_lessdef_ptrofs_add_zero] at hofs
      subst ofs2
      exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _
  | val_inject_undef v =>
      exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_undef _

theorem eval_addressing_lessdef : eval_addressing_lessdefStatement := by
  intro F V genv sp addr vl1 vl2 v1 hvl heval
  let f : CompCert4Lean.Common.Values.Val.meminj :=
    fun b => some (b,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)
  have hglobals : ∀ id ofs,
      id ∈ globals_addressing addr →
        CompCert4Lean.Common.Values.Val.inject f
          (CompCert4Lean.Common.Globalenvs.Genv.symbol_address genv id ofs)
          (CompCert4Lean.Common.Globalenvs.Genv.symbol_address genv id ofs) := by
    intro id ofs _
    exact suffix_eval_addressing_lessdef_to_inject _ _
      (CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _)
  have hsp : CompCert4Lean.Common.Values.Val.inject f sp sp :=
    suffix_eval_addressing_lessdef_to_inject _ _
      (CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _)
  have hvl' : CompCert4Lean.Common.Values.Val.inject_list f vl1 vl2 :=
    suffix_eval_addressing_lessdef_list_to_inject vl1 vl2 hvl
  obtain ⟨v2, heval2, hinj⟩ :=
    eval_addressing_inj F F V V genv genv f addr sp vl1 sp vl2 v1
      hglobals hsp hvl' heval
  exact ⟨v2, heval2, suffix_eval_addressing_lessdef_of_inject v1 v2 hinj⟩

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem symbol_address_inject : symbol_address_injectStatement := by
  intro F V genv f globals id ofs
  unfold CompCert4Lean.Common.Globalenvs.Genv.symbol_address
  split
  next b hfind =>
    apply CompCert4Lean.Common.Values.Val.inject.inject_ptr b ofs b ofs
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0
    · exact globals.1 id b hfind
    · rw [show CompCert4Lean.Lib.Integers.Ptrofs.repr
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
            CompCert4Lean.Lib.Integers.Ptrofs.zero by rfl,
          suffixPtrofsAddZero]
  next hfind =>
    exact CompCert4Lean.Common.Values.Val.inject.val_inject_undef _

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

theorem eval_addressing_inject : eval_addressing_injectStatement := by
  intro F V genv f globals sp1 sp2 delta hsp addr vl1 vl2 v1 hvl heval
  rw [eval_shift_stack_addressing]
  have hsp' :
      CompCert4Lean.Common.Values.Val.inject f
        (.Vptr sp1 CompCert4Lean.Lib.Integers.Ptrofs.zero)
        (.Vptr sp2 (CompCert4Lean.Lib.Integers.Ptrofs.repr delta)) :=
    CompCert4Lean.Common.Values.Val.inject.inject_ptr sp1
      CompCert4Lean.Lib.Integers.Ptrofs.zero sp2
      (CompCert4Lean.Lib.Integers.Ptrofs.repr delta) delta hsp (by
        rw [CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api]
        exact (suffixPtrofsAddZero _).symm)
  exact eval_addressing_inj F F V V genv genv f addr
    (.Vptr sp1 CompCert4Lean.Lib.Integers.Ptrofs.zero) vl1
    (.Vptr sp2 (CompCert4Lean.Lib.Integers.Ptrofs.repr delta)) vl2 v1
    (by
      intro id ofs haddr
      exact symbol_address_inject F V genv f globals id ofs)
    hsp' hvl heval

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private abbrev suffixZAdd :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
private abbrev suffixZMod :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo

private theorem suffix_int_repr_add
    (x y : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    CompCert4Lean.Lib.Integers.Int.repr (suffixZAdd x y) =
      CompCert4Lean.Lib.Integers.Int.add
        (CompCert4Lean.Lib.Integers.Int.repr x)
        (CompCert4Lean.Lib.Integers.Int.repr y) := by
  have hx : CompCert4Lean.Lib.Integers.Int.eqm x
      (CompCert4Lean.Lib.Integers.Int.unsigned
        (CompCert4Lean.Lib.Integers.Int.repr x)) :=
    CompCert4Lean.Lib.Integers.Int.eqm_unsigned_repr_r_proof x x
      (CompCert4Lean.Lib.Integers.Int.eqm_refl_proof x)
  have hy : CompCert4Lean.Lib.Integers.Int.eqm y
      (CompCert4Lean.Lib.Integers.Int.unsigned
        (CompCert4Lean.Lib.Integers.Int.repr y)) :=
    CompCert4Lean.Lib.Integers.Int.eqm_unsigned_repr_r_proof y y
      (CompCert4Lean.Lib.Integers.Int.eqm_refl_proof y)
  rw [CompCert4Lean.Lib.Integers.Int.unsigned_repr_eq_proof] at hx hy
  have hxy := CompCert4Lean.Lib.Integers.Int.eqm_add_proof x
    (suffixZMod x CompCert4Lean.Lib.Integers.Int.modulus) y
    (suffixZMod y CompCert4Lean.Lib.Integers.Int.modulus) hx hy
  rw [CompCert4Lean.Lib.Integers.Int.eqm_samerepr_proof _ _ hxy]
  rw [CompCert4Lean.Lib.Integers.Int.add_unsigned_proof]
  rw [CompCert4Lean.Lib.Integers.Int.unsigned_repr_eq_proof]
  rw [CompCert4Lean.Lib.Integers.Int.unsigned_repr_eq_proof]

theorem eval_offset_addressing_total_32 : eval_offset_addressing_total_32Statement := by
  intro F V ge sp addr args delta v h
  cases addr with
  | Aindexed ofs =>
      cases args with
      | nil => simp [eval_addressing32, offset_addressing_total] at h ⊢
      | cons a tail =>
          cases tail with
          | nil =>
              simp [eval_addressing32, offset_addressing_total] at h ⊢
              rw [← h, suffix_int_repr_add]
              exact (CompCert4Lean.Common.Values.Val.add_assoc a
                (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))
                (.Vint (CompCert4Lean.Lib.Integers.Int.repr delta))).symm
          | cons b tail => simp [eval_addressing32, offset_addressing_total] at h ⊢
  | Aindexed2 ofs =>
      cases args with
      | nil => simp [eval_addressing32, offset_addressing_total] at h ⊢
      | cons a tail =>
          cases tail with
          | nil => simp [eval_addressing32, offset_addressing_total] at h ⊢
          | cons b tail =>
              cases tail with
              | nil =>
                  simp [eval_addressing32, offset_addressing_total] at h ⊢
                  rw [← h, suffix_int_repr_add]
                  exact (CompCert4Lean.Common.Values.Val.add_assoc
                    (CompCert4Lean.Common.Values.Val.add a b)
                    (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))
                    (.Vint (CompCert4Lean.Lib.Integers.Int.repr delta))).symm
              | cons c tail => simp [eval_addressing32, offset_addressing_total] at h ⊢
  | Ascaled scale ofs =>
      cases args with
      | nil => simp [eval_addressing32, offset_addressing_total] at h ⊢
      | cons a tail =>
          cases tail with
          | nil =>
              simp [eval_addressing32, offset_addressing_total] at h ⊢
              rw [← h, suffix_int_repr_add]
              exact (CompCert4Lean.Common.Values.Val.add_assoc
                (CompCert4Lean.Common.Values.Val.mul a
                  (.Vint (CompCert4Lean.Lib.Integers.Int.repr scale)))
                (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))
                (.Vint (CompCert4Lean.Lib.Integers.Int.repr delta))).symm
          | cons b tail => simp [eval_addressing32, offset_addressing_total] at h ⊢
  | Aindexed2scaled scale ofs =>
      cases args with
      | nil => simp [eval_addressing32, offset_addressing_total] at h ⊢
      | cons a tail =>
          cases tail with
          | nil => simp [eval_addressing32, offset_addressing_total] at h ⊢
          | cons b tail =>
              cases tail with
              | nil =>
                  simp [eval_addressing32, offset_addressing_total] at h ⊢
                  rw [← h, suffix_int_repr_add]
                  change CompCert4Lean.Common.Values.Val.add a
                      (CompCert4Lean.Common.Values.Val.add
                        (CompCert4Lean.Common.Values.Val.mul b
                          (.Vint (CompCert4Lean.Lib.Integers.Int.repr scale)))
                        (CompCert4Lean.Common.Values.Val.add
                          (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))
                          (.Vint (CompCert4Lean.Lib.Integers.Int.repr delta)))) = _
                  calc
                    _ = CompCert4Lean.Common.Values.Val.add a
                        (CompCert4Lean.Common.Values.Val.add
                          (CompCert4Lean.Common.Values.Val.add
                            (CompCert4Lean.Common.Values.Val.mul b
                              (.Vint (CompCert4Lean.Lib.Integers.Int.repr scale)))
                            (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs)))
                          (.Vint (CompCert4Lean.Lib.Integers.Int.repr delta))) := by
                          rw [← CompCert4Lean.Common.Values.Val.add_assoc
                            (CompCert4Lean.Common.Values.Val.mul b
                              (.Vint (CompCert4Lean.Lib.Integers.Int.repr scale)))
                            (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))
                            (.Vint (CompCert4Lean.Lib.Integers.Int.repr delta))]
                    _ = _ := (CompCert4Lean.Common.Values.Val.add_assoc a
                      (CompCert4Lean.Common.Values.Val.add
                        (CompCert4Lean.Common.Values.Val.mul b
                          (.Vint (CompCert4Lean.Lib.Integers.Int.repr scale)))
                        (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs)))
                      (.Vint (CompCert4Lean.Lib.Integers.Int.repr delta))).symm
              | cons c tail => simp [eval_addressing32, offset_addressing_total] at h ⊢
  | Aglobal id ofs =>
      cases args <;> simp [eval_addressing32, offset_addressing_total,
        CompCert4Lean.X86_64.Archi.ptr64] at h ⊢
  | Abased id ofs =>
      cases args with
      | nil => simp [eval_addressing32, offset_addressing_total,
          CompCert4Lean.X86_64.Archi.ptr64] at h ⊢
      | cons a tail =>
          cases tail <;> simp [eval_addressing32, offset_addressing_total,
            CompCert4Lean.X86_64.Archi.ptr64] at h ⊢
  | Abasedscaled scale id ofs =>
      cases args with
      | nil => simp [eval_addressing32, offset_addressing_total,
          CompCert4Lean.X86_64.Archi.ptr64] at h ⊢
      | cons a tail =>
          cases tail <;> simp [eval_addressing32, offset_addressing_total,
            CompCert4Lean.X86_64.Archi.ptr64] at h ⊢
  | Ainstack ofs =>
      cases args <;> simp [eval_addressing32, offset_addressing_total,
        CompCert4Lean.X86_64.Archi.ptr64] at h ⊢

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private abbrev suffix64_Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev suffix64_zMod := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
private abbrev suffix64_zAdd := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
private abbrev suffix64_zMul := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
private abbrev suffix64_zOfNat := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
private abbrev suffix64_intOfZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
private theorem suffix64_val_repr (i : Int) :
    (WordCore.repr 64 (zOfInt i)).val =
      Int.toNat (i % ((2 ^ 64 : Nat) : Int)) := by
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "WordCore.val_repr")
      | throwError "frozen WordCore.val_repr helper not found"
    let stx := Lean.mkIdent n
    let arg := Lean.mkIdent `i
    evalTactic (← `(tactic| exact $stx 64 $arg))
private theorem suffix64_intval (w : WordCore.Word 64) :
    w.intval = suffix64_zOfNat w.val := by
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "WordCore.intval_eq_zOfNat_val")
      | throwError "frozen WordCore.intval_eq_zOfNat_val helper not found"
    let stx := Lean.mkIdent n
    let arg := Lean.mkIdent `w
    evalTactic (← `(tactic| exact $stx $arg))
private theorem suffix64_unsigned_repr (x : suffix64_Z) :
    CompCert4Lean.Lib.Integers.Int64.unsigned
      (CompCert4Lean.Lib.Integers.Int64.repr x) =
      suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus := by
  change (WordCore.repr 64 x).intval = suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus
  rw [show x = zOfInt (suffix64_intOfZ x) by exact (zOfInt_intOfZ x).symm]
  change (WordCore.repr 64 (zOfInt (suffix64_intOfZ x))).intval = _
  have hval : (WordCore.repr 64 (zOfInt (suffix64_intOfZ x))).val =
      Int.toNat (suffix64_intOfZ x % ((2 ^ 64 : Nat) : Int)) := by
    exact suffix64_val_repr (suffix64_intOfZ x)
  have hwi : (WordCore.repr 64 (zOfInt (suffix64_intOfZ x))).intval =
      suffix64_zOfNat (WordCore.repr 64 (zOfInt (suffix64_intOfZ x))).val := by
    exact suffix64_intval _
  rw [hwi, hval]
  apply intOfZ_injective
  have hmpos : (0 : Int) < suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := by
    change (0 : Int) < (2 ^ 64 : Int)
    exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hm : suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus = (2 ^ 64 : Int) := by
    rfl
  simp only [suffix64_zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  have hmod : suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus) =
      suffix64_intOfZ x % (2 ^ 64 : Int) := by
    have hrange := ZArith.BinInt.Z.modulo_range x CompCert4Lean.Lib.Integers.Int64.modulus (by
      change (0 : Int) < suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus
      exact hmpos)
    have hr0 : (0 : Int) ≤ suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus) := hrange.1
    have hrlt : suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus) <
        suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := hrange.2
    have hd := ZArith.Zdiv.Z_div_mod_eq_full x CompCert4Lean.Lib.Integers.Int64.modulus
    have hdInt := congrArg suffix64_intOfZ hd
    simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt] at hdInt
    let q := suffix64_intOfZ (ZArith.BinInt.Z.div x CompCert4Lean.Lib.Integers.Int64.modulus)
    let r := suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus)
    let m := suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus
    have hcalc : suffix64_intOfZ x % m = r := by
      calc
        suffix64_intOfZ x % m = (m * q + r) % m := congrArg (fun a => a % m) hdInt
        _ = (r + q * m) % m := by rw [Int.add_comm, Int.mul_comm]
        _ = r % m := Int.add_mul_emod_self_right r q m
        _ = r := Int.emod_eq_of_lt hr0 hrlt
    simpa [m, r, hm] using hcalc.symm
  rw [zOfInt_intOfZ]
  change Int.ofNat (Int.toNat (suffix64_intOfZ x % (2 ^ 64 : Int))) = suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus)
  have hnonneg : 0 ≤ suffix64_intOfZ x % (2 ^ 64 : Int) := Int.emod_nonneg _ (by decide)
  have hto : (Int.toNat (suffix64_intOfZ x % (2 ^ 64 : Int)) : Int) = suffix64_intOfZ x % (2 ^ 64 : Int) := Int.toNat_of_nonneg hnonneg
  calc
    Int.ofNat (Int.toNat (suffix64_intOfZ x % (2 ^ 64 : Int))) = suffix64_intOfZ x % (2 ^ 64 : Int) := hto
    _ = suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus) := hmod.symm

private theorem suffix64_mod_int (x : suffix64_Z) :
    suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus) =
      suffix64_intOfZ x % suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := by
  have hmpos : (0 : Int) < suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := by
    change (0 : Int) < (2 ^ 64 : Int)
    exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hrange := ZArith.BinInt.Z.modulo_range x CompCert4Lean.Lib.Integers.Int64.modulus (by
    change (0 : Int) < suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus
    exact hmpos)
  have hr0 : (0 : Int) ≤ suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus) := hrange.1
  have hrlt : suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus) <
      suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := hrange.2
  have hd := ZArith.Zdiv.Z_div_mod_eq_full x CompCert4Lean.Lib.Integers.Int64.modulus
  have hdInt := congrArg suffix64_intOfZ hd
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt] at hdInt
  let q := suffix64_intOfZ (ZArith.BinInt.Z.div x CompCert4Lean.Lib.Integers.Int64.modulus)
  let r := suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus)
  let m := suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus
  have hcalc : suffix64_intOfZ x % m = r := by
    calc
      suffix64_intOfZ x % m = (m * q + r) % m := congrArg (fun a => a % m) hdInt
      _ = (r + q * m) % m := by rw [Int.add_comm, Int.mul_comm]
      _ = r % m := Int.add_mul_emod_self_right r q m
      _ = r := Int.emod_eq_of_lt hr0 hrlt
  simpa [m, r] using hcalc.symm

private theorem suffix64_repr_add (x y : suffix64_Z) :
    CompCert4Lean.Lib.Integers.Int64.repr (suffix64_zAdd x y) =
      CompCert4Lean.Lib.Integers.Int64.add
        (CompCert4Lean.Lib.Integers.Int64.repr x)
        (CompCert4Lean.Lib.Integers.Int64.repr y) := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  change CompCert4Lean.Lib.Integers.Int64.unsigned
      (CompCert4Lean.Lib.Integers.Int64.repr (suffix64_zAdd x y)) =
    CompCert4Lean.Lib.Integers.Int64.unsigned
      (CompCert4Lean.Lib.Integers.Int64.add
        (CompCert4Lean.Lib.Integers.Int64.repr x)
        (CompCert4Lean.Lib.Integers.Int64.repr y))
  rw [suffix64_unsigned_repr]
  unfold CompCert4Lean.Lib.Integers.Int64.add
  unfold CompCert4Lean.Lib.Integers.WordCore.add
  change suffix64_zMod (suffix64_zAdd x y) CompCert4Lean.Lib.Integers.Int64.modulus =
    CompCert4Lean.Lib.Integers.Int64.unsigned
      (CompCert4Lean.Lib.Integers.Int64.repr
        (suffix64_zAdd
          (CompCert4Lean.Lib.Integers.Int64.unsigned
            (CompCert4Lean.Lib.Integers.Int64.repr x))
          (CompCert4Lean.Lib.Integers.Int64.unsigned
            (CompCert4Lean.Lib.Integers.Int64.repr y))))
  rw [suffix64_unsigned_repr, suffix64_unsigned_repr, suffix64_unsigned_repr]
  apply intOfZ_injective
  have hx := suffix64_mod_int x
  have hy := suffix64_mod_int y
  have hxy := suffix64_mod_int (suffix64_zAdd x y)
  have hzadd : suffix64_intOfZ (suffix64_zAdd x y) = suffix64_intOfZ x + suffix64_intOfZ y := by
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  have hr := suffix64_mod_int (suffix64_zAdd
    (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus)
    (suffix64_zMod y CompCert4Lean.Lib.Integers.Int64.modulus))
  have hsum : suffix64_intOfZ (suffix64_zAdd
      (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus)
      (suffix64_zMod y CompCert4Lean.Lib.Integers.Int64.modulus)) =
      suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus) +
        suffix64_intOfZ (suffix64_zMod y CompCert4Lean.Lib.Integers.Int64.modulus) := by
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  calc
    suffix64_intOfZ (suffix64_zMod (suffix64_zAdd x y) CompCert4Lean.Lib.Integers.Int64.modulus) =
        suffix64_intOfZ (suffix64_zAdd x y) % suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := hxy
    _ = (suffix64_intOfZ x % suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus +
          suffix64_intOfZ y % suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus) %
          suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := by
      rw [hzadd, Int.add_emod]
    _ = (suffix64_intOfZ (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus) +
          suffix64_intOfZ (suffix64_zMod y CompCert4Lean.Lib.Integers.Int64.modulus)) %
          suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := by rw [hx, hy]
    _ = suffix64_intOfZ (suffix64_zAdd
          (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus)
          (suffix64_zMod y CompCert4Lean.Lib.Integers.Int64.modulus)) %
          suffix64_intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := by rw [hsum]
    _ = suffix64_intOfZ (suffix64_zMod (suffix64_zAdd
          (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus)
          (suffix64_zMod y CompCert4Lean.Lib.Integers.Int64.modulus))
          CompCert4Lean.Lib.Integers.Int64.modulus) := hr.symm

private theorem suffix64_repr_mod (x : suffix64_Z) :
    CompCert4Lean.Lib.Integers.Int64.repr x =
      CompCert4Lean.Lib.Integers.Int64.repr
        (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus) := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  change CompCert4Lean.Lib.Integers.Int64.unsigned
      (CompCert4Lean.Lib.Integers.Int64.repr x) =
    CompCert4Lean.Lib.Integers.Int64.unsigned
      (CompCert4Lean.Lib.Integers.Int64.repr
        (suffix64_zMod x CompCert4Lean.Lib.Integers.Int64.modulus))
  rw [suffix64_unsigned_repr, suffix64_unsigned_repr]
  exact (ZArith.BinInt.Z.mod_small _ _
    (ZArith.Zdiv.Z_mod_lt x CompCert4Lean.Lib.Integers.Int64.modulus (by
      change (0 : Int) < (2 ^ 64 : Int)
      exact Int.natCast_pos.mpr (Nat.two_pow_pos _)))).symm

private theorem suffix64_ptrofs_repr_of_int64 (x : suffix64_Z) :
    CompCert4Lean.Lib.Integers.Ptrofs.repr x =
      CompCert4Lean.Lib.Integers.Ptrofs.of_int64
        (CompCert4Lean.Lib.Integers.Int64.repr x) := by
  unfold CompCert4Lean.Lib.Integers.Ptrofs.of_int64
  change CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Ptrofs.wordsize x =
    CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Ptrofs.wordsize
      (CompCert4Lean.Lib.Integers.Int64.unsigned
        (CompCert4Lean.Lib.Integers.Int64.repr x))
  simp [CompCert4Lean.Lib.Integers.Ptrofs.wordsize,
    CompCert4Lean.Lib.Integers.Wordsize_Ptrofs.wordsize,
    CompCert4Lean.Lib.Integers.Int64.wordsize,
    CompCert4Lean.X86_64.Archi.ptr64]
  rw [suffix64_unsigned_repr]
  exact suffix64_repr_mod x

theorem eval_offset_addressing_total_64 :
    CompCert4Lean.X86.Op.eval_offset_addressing_total_64Statement := by
  intro F V ge sp addr args delta v h
  cases addr with
  | Aindexed ofs =>
      cases args with
      | nil => simp [eval_addressing64, offset_addressing_total] at h ⊢
      | cons a tail =>
          cases tail with
          | nil =>
              simp [eval_addressing64, offset_addressing_total] at h ⊢
              rw [← h, suffix64_repr_add]
              exact (CompCert4Lean.Common.Values.Val.addl_assoc a
                (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))
                (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr delta))).symm
          | cons b tail => simp [eval_addressing64, offset_addressing_total] at h ⊢
  | Aindexed2 ofs =>
      cases args with
      | nil => simp [eval_addressing64, offset_addressing_total] at h ⊢
      | cons a tail =>
          cases tail with
          | nil => simp [eval_addressing64, offset_addressing_total] at h ⊢
          | cons b tail =>
              cases tail with
              | nil =>
                  simp [eval_addressing64, offset_addressing_total] at h ⊢
                  rw [← h, suffix64_repr_add]
                  exact (CompCert4Lean.Common.Values.Val.addl_assoc
                    (CompCert4Lean.Common.Values.Val.addl a b)
                    (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))
                    (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr delta))).symm
              | cons c tail => simp [eval_addressing64, offset_addressing_total] at h ⊢
  | Ascaled scale ofs =>
      cases args with
      | nil => simp [eval_addressing64, offset_addressing_total] at h ⊢
      | cons a tail =>
          cases tail with
          | nil =>
              simp [eval_addressing64, offset_addressing_total] at h ⊢
              rw [← h, suffix64_repr_add]
              exact (CompCert4Lean.Common.Values.Val.addl_assoc
                (CompCert4Lean.Common.Values.Val.mull a
                  (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr scale)))
                (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))
                (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr delta))).symm
          | cons b tail => simp [eval_addressing64, offset_addressing_total] at h ⊢
  | Aindexed2scaled scale ofs =>
      cases args with
      | nil => simp [eval_addressing64, offset_addressing_total] at h ⊢
      | cons a tail =>
          cases tail with
          | nil => simp [eval_addressing64, offset_addressing_total] at h ⊢
          | cons b tail =>
              cases tail with
              | nil =>
                  simp [eval_addressing64, offset_addressing_total] at h ⊢
                  rw [← h, suffix64_repr_add]
                  change CompCert4Lean.Common.Values.Val.addl a
                      (CompCert4Lean.Common.Values.Val.addl
                        (CompCert4Lean.Common.Values.Val.mull b
                          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr scale)))
                        (CompCert4Lean.Common.Values.Val.addl
                          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))
                          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr delta)))) = _
                  calc
                    _ = CompCert4Lean.Common.Values.Val.addl a
                        (CompCert4Lean.Common.Values.Val.addl
                          (CompCert4Lean.Common.Values.Val.addl
                            (CompCert4Lean.Common.Values.Val.mull b
                              (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr scale)))
                            (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs)))
                          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr delta))) := by
                          rw [← CompCert4Lean.Common.Values.Val.addl_assoc
                            (CompCert4Lean.Common.Values.Val.mull b
                              (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr scale)))
                            (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))
                            (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr delta))]
                    _ = _ := (CompCert4Lean.Common.Values.Val.addl_assoc a
                      (CompCert4Lean.Common.Values.Val.addl
                        (CompCert4Lean.Common.Values.Val.mull b
                          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr scale)))
                        (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs)))
                      (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr delta))).symm
              | cons c tail => simp [eval_addressing64, offset_addressing_total] at h ⊢
  | Aglobal id ofs =>
      cases args with
      | nil =>
          simp [eval_addressing64, offset_addressing_total,
            CompCert4Lean.X86_64.Archi.ptr64] at h ⊢
          rw [← h]
          rw [show CompCert4Lean.Lib.Integers.Ptrofs.repr delta =
              CompCert4Lean.Lib.Integers.Ptrofs.of_int64
                (CompCert4Lean.Lib.Integers.Int64.repr delta) by
            exact suffix64_ptrofs_repr_of_int64 delta]
          exact CompCert4Lean.Common.Globalenvs.Genv.shift_symbol_address_64
            F V ge id ofs (CompCert4Lean.Lib.Integers.Int64.repr delta) rfl
      | cons a tail =>
          cases tail <;> simp [eval_addressing64, offset_addressing_total,
            CompCert4Lean.X86_64.Archi.ptr64] at h ⊢
  | Abased id ofs =>
      cases args <;> simp [eval_addressing64, offset_addressing_total,
        CompCert4Lean.X86_64.Archi.ptr64] at h ⊢
  | Abasedscaled scale id ofs =>
      cases args <;> simp [eval_addressing64, offset_addressing_total,
        CompCert4Lean.X86_64.Archi.ptr64] at h ⊢
  | Ainstack ofs =>
      cases args with
      | nil =>
          simp [eval_addressing64, offset_addressing_total,
            CompCert4Lean.X86_64.Archi.ptr64] at h ⊢
          rw [← h]
          cases sp <;>
            simp [CompCert4Lean.Common.Values.Val.offset_ptr,
              CompCert4Lean.Common.Values.Val.addl,
              CompCert4Lean.X86_64.Archi.ptr64]
          · rw [CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api]
            rw [show CompCert4Lean.Lib.Integers.Ptrofs.repr delta =
                CompCert4Lean.Lib.Integers.Ptrofs.of_int64
                  (CompCert4Lean.Lib.Integers.Int64.repr delta) by
              exact suffix64_ptrofs_repr_of_int64 delta]
      | cons a tail =>
          cases tail <;> simp [eval_addressing64, offset_addressing_total,
            CompCert4Lean.X86_64.Archi.ptr64] at h ⊢

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs

theorem type_of_addressing64_sound : type_of_addressing64_soundStatement := by
  intro A V genv addr vl sp v h
  cases addr with
  | Aindexed ofs =>
      cases vl with
      | nil => simp [eval_addressing64] at h
      | cons v1 vl =>
          cases vl with
          | nil =>
              simp [eval_addressing64] at h
              cases h
              exact type_addl _ _
          | cons v2 vl => simp [eval_addressing64] at h
  | Aindexed2 ofs =>
      cases vl with
      | nil => simp [eval_addressing64] at h
      | cons v1 vl =>
          cases vl with
          | nil => simp [eval_addressing64] at h
          | cons v2 vl =>
              cases vl with
              | nil =>
                  simp [eval_addressing64] at h
                  cases h
                  exact type_addl _ _
              | cons v3 vl => simp [eval_addressing64] at h
  | Ascaled scale ofs =>
      cases vl with
      | nil => simp [eval_addressing64] at h
      | cons v1 vl =>
          cases vl with
          | nil =>
              simp [eval_addressing64] at h
              cases h
              exact type_addl _ _
          | cons v2 vl => simp [eval_addressing64] at h
  | Aindexed2scaled scale ofs =>
      cases vl with
      | nil => simp [eval_addressing64] at h
      | cons v1 vl =>
          cases vl with
          | nil => simp [eval_addressing64] at h
          | cons v2 vl =>
              cases vl with
              | nil =>
                  simp [eval_addressing64] at h
                  cases h
                  exact type_addl _ _
              | cons v3 vl => simp [eval_addressing64] at h
  | Aglobal id ofs =>
      cases vl with
      | nil =>
          simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at h
          cases h
          unfold Genv.symbol_address
          cases Genv.find_symbol genv id <;>
            simp [Val.has_type, CompCert4Lean.X86_64.Archi.ptr64]
      | cons v1 vl => simp [eval_addressing64] at h
  | Abased id ofs =>
      simp [eval_addressing64] at h
  | Abasedscaled scale id ofs =>
      simp [eval_addressing64] at h
  | Ainstack ofs =>
      cases vl with
      | nil =>
          simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at h
          cases h
          cases sp <;>
            simp [Val.offset_ptr, Val.has_type, CompCert4Lean.X86_64.Archi.ptr64]
      | cons v1 vl => simp [eval_addressing64] at h

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers

set_option maxHeartbeats 2000000

private theorem suffix_operation_shl_inj (f : meminj) (a a' b b' : val)
    (ha : Val.inject f a a') (hb : Val.inject f b b') :
    Val.inject f (Val.shl a b) (Val.shl a' b') := by
  cases ha <;> cases hb <;> simp only [Val.shl] <;>
    first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor)

private theorem suffix_operation_shru_inj (f : meminj) (a a' b b' : val)
    (ha : Val.inject f a a') (hb : Val.inject f b b') :
    Val.inject f (Val.shru a b) (Val.shru a' b') := by
  cases ha <;> cases hb <;> simp only [Val.shru] <;>
    first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor)

private theorem suffix_operation_or_inj (f : meminj) (a a' b b' : val)
    (ha : Val.inject f a a') (hb : Val.inject f b b') :
    Val.inject f (Val.or a b) (Val.or a' b') := by
  cases ha <;> cases hb <;> simp only [Val.or] <;>
    first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor)

private theorem suffix_operation_inj_of_condition
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (hcond : eval_condition_injStatement) :
    @eval_operation_injStatement binary64_certificate binary32_certificate := by
  intro F1 F2 V1 V2 ge1 ge2 f m1 m2
  intro hvalid hweak hbound hdiff op sp1 vl1 sp2 vl2 v1 hglobals hsp hvl heval
  have hc := hcond f m1 m2 hvalid hweak hbound hdiff
  cases op with
  | Omove =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some a = some v1 at heval
              cases heval
              refine ⟨a', rfl, ?_⟩
              exact ha
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ointconst n =>
      cases hvl with
      | inject_list_nil =>
          change some (.Vint n) = some v1 at heval
          cases heval
          refine ⟨(.Vint n), rfl, ?_⟩
          constructor
      | inject_list_cons =>
          change none = some v1 at heval
          contradiction
  | Olongconst n =>
      cases hvl with
      | inject_list_nil =>
          change some (.Vlong n) = some v1 at heval
          cases heval
          refine ⟨(.Vlong n), rfl, ?_⟩
          constructor
      | inject_list_cons =>
          change none = some v1 at heval
          contradiction
  | Ofloatconst n =>
      cases hvl with
      | inject_list_nil =>
          change some (.Vfloat n) = some v1 at heval
          cases heval
          refine ⟨(.Vfloat n), rfl, ?_⟩
          constructor
      | inject_list_cons =>
          change none = some v1 at heval
          contradiction
  | Osingleconst n =>
      cases hvl with
      | inject_list_nil =>
          change some (.Vsingle n) = some v1 at heval
          cases heval
          refine ⟨(.Vsingle n), rfl, ?_⟩
          constructor
      | inject_list_cons =>
          change none = some v1 at heval
          contradiction
  | Oindirectsymbol id =>
      cases hvl with
      | inject_list_nil =>
          change some (Genv.symbol_address ge1 id Ptrofs.zero) = some v1 at heval
          cases heval
          refine ⟨(Genv.symbol_address ge2 id Ptrofs.zero), rfl, ?_⟩
          exact hglobals id Ptrofs.zero (by simp [globals_operation])
      | inject_list_cons =>
          change none = some v1 at heval
          contradiction
  | Ocast8signed =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.sign_ext (zOfNat 8) a) = some v1 at heval
              cases heval
              refine ⟨(Val.sign_ext (zOfNat 8) a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.sign_ext] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ocast8unsigned =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.zero_ext (zOfNat 8) a) = some v1 at heval
              cases heval
              refine ⟨(Val.zero_ext (zOfNat 8) a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.zero_ext] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ocast16signed =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.sign_ext (zOfNat 16) a) = some v1 at heval
              cases heval
              refine ⟨(Val.sign_ext (zOfNat 16) a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.sign_ext] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ocast16unsigned =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.zero_ext (zOfNat 16) a) = some v1 at heval
              cases heval
              refine ⟨(Val.zero_ext (zOfNat 16) a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.zero_ext] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oneg =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.neg a) = some v1 at heval
              cases heval
              refine ⟨(Val.neg a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.neg] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Osub =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.sub a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.sub a' b'), rfl, ?_⟩
                  exact Val.sub_inject f _ _ _ _ ha hb
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omul =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.mul a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.mul a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.mul] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omulimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.mul a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.mul a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.mul] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Omulhs =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.mulhs a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.mulhs a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.mulhs] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omulhu =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.mulhu a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.mulhu a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.mulhu] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Odiv =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.divs a b = some v1 at heval
                  change ∃ v2, Val.divs a' b' = some v2 ∧ Val.inject f v1 v2
                  cases ha <;> cases hb <;>
                    simp only [Val.divs] at heval ⊢ <;> try contradiction
                  all_goals
                    first
                    | (cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Odivu =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.divu a b = some v1 at heval
                  change ∃ v2, Val.divu a' b' = some v2 ∧ Val.inject f v1 v2
                  cases ha <;> cases hb <;>
                    simp only [Val.divu] at heval ⊢ <;> try contradiction
                  all_goals
                    first
                    | (cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omod =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.mods a b = some v1 at heval
                  change ∃ v2, Val.mods a' b' = some v2 ∧ Val.inject f v1 v2
                  cases ha <;> cases hb <;>
                    simp only [Val.mods] at heval ⊢ <;> try contradiction
                  all_goals
                    first
                    | (cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omodu =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.modu a b = some v1 at heval
                  change ∃ v2, Val.modu a' b' = some v2 ∧ Val.inject f v1 v2
                  cases ha <;> cases hb <;>
                    simp only [Val.modu] at heval ⊢ <;> try contradiction
                  all_goals
                    first
                    | (cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oand =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.and a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.and a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.and] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oandimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.and a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.and a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.and] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oor =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.or a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.or a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.or] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oorimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.or a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.or a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.or] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oxor =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.xor a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.xor a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.xor] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oxorimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.xor a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.xor a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.xor] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Onot =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.notint a) = some v1 at heval
              cases heval
              refine ⟨(Val.notint a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.notint] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oshl =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.shl a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.shl a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.shl] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oshlimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.shl a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.shl a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.shl] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oshr =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.shr a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.shr a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.shr] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oshrimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.shr a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.shr a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.shr] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oshrximm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.shrx a (.Vint n) = some v1 at heval
              change ∃ v2, Val.shrx a' (.Vint n) = some v2 ∧ Val.inject f v1 v2
              cases ha <;>
                simp only [Val.shrx] at heval ⊢ <;> try contradiction
              all_goals
                first
                | (cases heval; exact ⟨_, rfl, by constructor⟩)
                | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oshru =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.shru a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.shru a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.shru] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oshruimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.shru a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.shru a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.shru] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ororimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.ror a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.ror a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.ror] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oshldimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.or (Val.shl a (.Vint n))
        (Val.shru b (.Vint
          (CompCert4Lean.Lib.Integers.Int.sub
            CompCert4Lean.Lib.Integers.Int.iwordsize n)))) = some v1 at heval
                  cases heval
                  refine ⟨(Val.or (Val.shl a' (.Vint n))
        (Val.shru b' (.Vint
          (CompCert4Lean.Lib.Integers.Int.sub
            CompCert4Lean.Lib.Integers.Int.iwordsize n)))), rfl, ?_⟩
                  apply suffix_operation_or_inj
                  · exact suffix_operation_shl_inj f _ _ _ _ ha (Val.inject_int f n)
                  · exact suffix_operation_shru_inj f _ _ _ _ hb (Val.inject_int f _)
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Olea addr =>
      exact eval_addressing32_inj F1 F2 V1 V2 ge1 ge2 f addr sp1 vl1 sp2 vl2 v1
        hglobals hsp hvl heval
  | Omakelong =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.longofwords a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.longofwords a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.longofwords] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Olowlong =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.loword a) = some v1 at heval
              cases heval
              refine ⟨(Val.loword a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.loword] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ohighlong =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.hiword a) = some v1 at heval
              cases heval
              refine ⟨(Val.hiword a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.hiword] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ocast32signed =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.longofint a) = some v1 at heval
              cases heval
              refine ⟨(Val.longofint a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.longofint] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ocast32unsigned =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.longofintu a) = some v1 at heval
              cases heval
              refine ⟨(Val.longofintu a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.longofintu] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Onegl =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.negl a) = some v1 at heval
              cases heval
              refine ⟨(Val.negl a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.negl] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oaddlimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.addl a (.Vlong n)) = some v1 at heval
              cases heval
              refine ⟨(Val.addl a' (.Vlong n)), rfl, ?_⟩
              exact Val.addl_inject f _ _ _ _ ha (Val.inject_long f n)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Osubl =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.subl a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.subl a' b'), rfl, ?_⟩
                  exact Val.subl_inject f _ _ _ _ ha hb
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omull =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.mull a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.mull a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.mull] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omullimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.mull a (.Vlong n)) = some v1 at heval
              cases heval
              refine ⟨(Val.mull a' (.Vlong n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.mull] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Omullhs =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.mullhs a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.mullhs a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.mullhs] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omullhu =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.mullhu a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.mullhu a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.mullhu] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Odivl =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.divls a b = some v1 at heval
                  change ∃ v2, Val.divls a' b' = some v2 ∧ Val.inject f v1 v2
                  cases ha <;> cases hb <;>
                    simp only [Val.divls] at heval ⊢ <;> try contradiction
                  all_goals
                    first
                    | (cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Odivlu =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.divlu a b = some v1 at heval
                  change ∃ v2, Val.divlu a' b' = some v2 ∧ Val.inject f v1 v2
                  cases ha <;> cases hb <;>
                    simp only [Val.divlu] at heval ⊢ <;> try contradiction
                  all_goals
                    first
                    | (cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omodl =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.modls a b = some v1 at heval
                  change ∃ v2, Val.modls a' b' = some v2 ∧ Val.inject f v1 v2
                  cases ha <;> cases hb <;>
                    simp only [Val.modls] at heval ⊢ <;> try contradiction
                  all_goals
                    first
                    | (cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omodlu =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.modlu a b = some v1 at heval
                  change ∃ v2, Val.modlu a' b' = some v2 ∧ Val.inject f v1 v2
                  cases ha <;> cases hb <;>
                    simp only [Val.modlu] at heval ⊢ <;> try contradiction
                  all_goals
                    first
                    | (cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                    | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oandl =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.andl a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.andl a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.andl] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oandlimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.andl a (.Vlong n)) = some v1 at heval
              cases heval
              refine ⟨(Val.andl a' (.Vlong n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.andl] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oorl =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.orl a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.orl a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.orl] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oorlimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.orl a (.Vlong n)) = some v1 at heval
              cases heval
              refine ⟨(Val.orl a' (.Vlong n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.orl] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oxorl =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.xorl a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.xorl a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.xorl] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oxorlimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.xorl a (.Vlong n)) = some v1 at heval
              cases heval
              refine ⟨(Val.xorl a' (.Vlong n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.xorl] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Onotl =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.notl a) = some v1 at heval
              cases heval
              refine ⟨(Val.notl a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.notl] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oshll =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.shll a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.shll a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.shll] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oshllimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.shll a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.shll a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.shll] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oshrl =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.shrl a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.shrl a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.shrl] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oshrlimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.shrl a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.shrl a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.shrl] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oshrxlimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.shrxl a (.Vint n) = some v1 at heval
              change ∃ v2, Val.shrxl a' (.Vint n) = some v2 ∧ Val.inject f v1 v2
              cases ha <;>
                simp only [Val.shrxl] at heval ⊢ <;> try contradiction
              all_goals
                first
                | (cases heval; exact ⟨_, rfl, by constructor⟩)
                | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oshrlu =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.shrlu a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.shrlu a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.shrlu] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Oshrluimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.shrlu a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.shrlu a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.shrlu] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ororlimm n =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.rorl a (.Vint n)) = some v1 at heval
              cases heval
              refine ⟨(Val.rorl a' (.Vint n)), rfl, ?_⟩
              cases ha <;>
                simp only [Val.rorl] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oleal addr =>
      exact eval_addressing64_inj F1 F2 V1 V2 ge1 ge2 f addr sp1 vl1 sp2 vl2 v1
        hglobals hsp hvl heval
  | Onegf =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.negf a) = some v1 at heval
              cases heval
              refine ⟨(Val.negf a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.negf] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oabsf =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.absf a) = some v1 at heval
              cases heval
              refine ⟨(Val.absf a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.absf] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oaddf =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.addf a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.addf a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.addf] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Osubf =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.subf a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.subf a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.subf] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omulf =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.mulf a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.mulf a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.mulf] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Odivf =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.divf a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.divf a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.divf] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omaxf =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (maxf a b) = some v1 at heval
                  cases heval
                  refine ⟨(maxf a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [maxf] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Ominf =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (minf a b) = some v1 at heval
                  cases heval
                  refine ⟨(minf a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [minf] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Onegfs =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.negfs a) = some v1 at heval
              cases heval
              refine ⟨(Val.negfs a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.negfs] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oabsfs =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.absfs a) = some v1 at heval
              cases heval
              refine ⟨(Val.absfs a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.absfs] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Oaddfs =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.addfs a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.addfs a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.addfs] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Osubfs =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.subfs a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.subfs a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.subfs] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Omulfs =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.mulfs a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.mulfs a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.mulfs] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Odivfs =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some v1 at heval
              contradiction
          | inject_list_cons b b' l1 l1' hb hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change some (Val.divfs a b) = some v1 at heval
                  cases heval
                  refine ⟨(Val.divfs a' b'), rfl, ?_⟩
                  cases ha <;> cases hb <;>
                    simp only [Val.divfs] <;>
                    (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
              | inject_list_cons =>
                  change none = some v1 at heval
                  contradiction
  | Osingleoffloat =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.singleoffloat a) = some v1 at heval
              cases heval
              refine ⟨(Val.singleoffloat a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.singleoffloat] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ofloatofsingle =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change some (Val.floatofsingle a) = some v1 at heval
              cases heval
              refine ⟨(Val.floatofsingle a'), rfl, ?_⟩
              cases ha <;>
                simp only [Val.floatofsingle] <;>
                (first | exact Val.val_inject_undef _ _ | constructor | (split <;> constructor))
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ointoffloat =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.intoffloat a = some v1 at heval
              change ∃ v2, Val.intoffloat a' = some v2 ∧ Val.inject f v1 v2
              cases ha <;>
                simp only [Val.intoffloat] at heval ⊢ <;> try contradiction
              all_goals
                first
                | (cases heval; exact ⟨_, rfl, by constructor⟩)
                | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ofloatofint =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.floatofint (binary64_certificate := binary64_certificate) a = some v1 at heval
              change ∃ v2, Val.floatofint (binary64_certificate := binary64_certificate) a' = some v2 ∧ Val.inject f v1 v2
              cases ha <;>
                simp only [Val.floatofint] at heval ⊢ <;> try contradiction
              all_goals
                first
                | (cases heval; exact ⟨_, rfl, by constructor⟩)
                | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ointofsingle =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.intofsingle a = some v1 at heval
              change ∃ v2, Val.intofsingle a' = some v2 ∧ Val.inject f v1 v2
              cases ha <;>
                simp only [Val.intofsingle] at heval ⊢ <;> try contradiction
              all_goals
                first
                | (cases heval; exact ⟨_, rfl, by constructor⟩)
                | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Osingleofint =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.singleofint (binary32_certificate := binary32_certificate) a = some v1 at heval
              change ∃ v2, Val.singleofint (binary32_certificate := binary32_certificate) a' = some v2 ∧ Val.inject f v1 v2
              cases ha <;>
                simp only [Val.singleofint] at heval ⊢ <;> try contradiction
              all_goals
                first
                | (cases heval; exact ⟨_, rfl, by constructor⟩)
                | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Olongoffloat =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.longoffloat a = some v1 at heval
              change ∃ v2, Val.longoffloat a' = some v2 ∧ Val.inject f v1 v2
              cases ha <;>
                simp only [Val.longoffloat] at heval ⊢ <;> try contradiction
              all_goals
                first
                | (cases heval; exact ⟨_, rfl, by constructor⟩)
                | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ofloatoflong =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.floatoflong (binary64_certificate := binary64_certificate) a = some v1 at heval
              change ∃ v2, Val.floatoflong (binary64_certificate := binary64_certificate) a' = some v2 ∧ Val.inject f v1 v2
              cases ha <;>
                simp only [Val.floatoflong] at heval ⊢ <;> try contradiction
              all_goals
                first
                | (cases heval; exact ⟨_, rfl, by constructor⟩)
                | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Olongofsingle =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.longofsingle a = some v1 at heval
              change ∃ v2, Val.longofsingle a' = some v2 ∧ Val.inject f v1 v2
              cases ha <;>
                simp only [Val.longofsingle] at heval ⊢ <;> try contradiction
              all_goals
                first
                | (cases heval; exact ⟨_, rfl, by constructor⟩)
                | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Osingleoflong =>
      cases hvl with
      | inject_list_nil =>
          change none = some v1 at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.singleoflong (binary32_certificate := binary32_certificate) a = some v1 at heval
              change ∃ v2, Val.singleoflong (binary32_certificate := binary32_certificate) a' = some v2 ∧ Val.inject f v1 v2
              cases ha <;>
                simp only [Val.singleoflong] at heval ⊢ <;> try contradiction
              all_goals
                first
                | (cases heval; exact ⟨_, rfl, by constructor⟩)
                | (split at heval <;> simp_all only [Option.some.injEq, reduceCtorEq]; cases heval; exact ⟨_, rfl, by constructor⟩)
                | (obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.mp heval; cases hv; exact ⟨_, heval, by constructor⟩)
          | inject_list_cons =>
              change none = some v1 at heval
              contradiction
  | Ocmp c =>
      change some (Val.of_optbool (eval_condition c vl1 m1)) = some v1 at heval
      cases heval
      refine ⟨_, rfl, ?_⟩
      cases he : eval_condition c vl1 m1 with
      | none => exact Val.val_inject_undef _ _
      | some b =>
        rw [hc c vl1 vl2 b hvl he]
        cases b <;> exact Val.inject_int _ _
  | Osel c ty =>
      cases hvl with
      | inject_list_nil => contradiction
      | inject_list_cons a a' l l' ha hl =>
        cases hl with
        | inject_list_nil => contradiction
        | inject_list_cons b b' rest rest' hb hr =>
          change some (Val.select (eval_condition c rest m1) a b ty) = some v1 at heval
          cases heval
          refine ⟨_, rfl, Val.select_inject f _ _ _ _ _ _ ty ?_ ha hb⟩
          cases he : eval_condition c rest m1 with
          | none => exact Or.inl rfl
          | some r => exact Or.inr (hc c rest rest' r hr he).symm

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers

private theorem suffix_operation_unsigned_add (x d : Ptrofs)
    (h : zLe z0 (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d)) ∧
      zLe (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d)) Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.add x d) = zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d) := by
  change Int64.unsigned (Int64.repr (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d))) = _
  rw [suffix64_unsigned_repr]
  apply ZArith.BinInt.Z.mod_small
  refine ⟨h.1, ?_⟩
  have hh := h.2
  change intOfZ (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d)) ≤
    intOfZ Int64.modulus - 1 at hh
  change intOfZ (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d)) < intOfZ Int64.modulus
  omega

private theorem suffix_operation_cmpu_shift (c : CompCert4Lean.Lib.Integers.comparison) (x y d : Ptrofs)
    (hx : zLe z0 (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d)) ∧
      zLe (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d)) Ptrofs.max_unsigned)
    (hy : zLe z0 (zAdd (Ptrofs.unsigned y) (Ptrofs.unsigned d)) ∧
      zLe (zAdd (Ptrofs.unsigned y) (Ptrofs.unsigned d)) Ptrofs.max_unsigned) :
    Ptrofs.cmpu c (Ptrofs.add x d) (Ptrofs.add y d) = Ptrofs.cmpu c x y := by
  have heq : Ptrofs.eq (Ptrofs.add x d) (Ptrofs.add y d) = Ptrofs.eq x y := by
    change decide (Ptrofs.unsigned (Ptrofs.add x d) = Ptrofs.unsigned (Ptrofs.add y d)) =
      decide (Ptrofs.unsigned x = Ptrofs.unsigned y)
    rw [suffix_operation_unsigned_add x d hx, suffix_operation_unsigned_add y d hy]
    congr 1
    apply propext
    constructor
    · intro h
      apply intOfZ_injective
      have h' := congrArg intOfZ h
      simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at h'
      omega
    · intro h; rw [h]
  have he (a b : Ptrofs) : Ptrofs.ltu a b =
      decide (intOfZ (Ptrofs.unsigned a) < intOfZ (Ptrofs.unsigned b)) := by
    by_cases h : intOfZ (Ptrofs.unsigned a) < intOfZ (Ptrofs.unsigned b)
    · rw [show decide (intOfZ (Ptrofs.unsigned a) < intOfZ (Ptrofs.unsigned b)) = true by simp [h]]
      exact CompCert4Lean.Lib.Coqlib.zlt_true Bool _ _ true false h
    · rw [show decide (intOfZ (Ptrofs.unsigned a) < intOfZ (Ptrofs.unsigned b)) = false by simp [h]]
      exact CompCert4Lean.Lib.Coqlib.zlt_false Bool _ _ true false (Int.le_of_not_gt h)
  have hlt (a b : Ptrofs)
      (ha : Ptrofs.unsigned (Ptrofs.add a d) = zAdd (Ptrofs.unsigned a) (Ptrofs.unsigned d))
      (hb : Ptrofs.unsigned (Ptrofs.add b d) = zAdd (Ptrofs.unsigned b) (Ptrofs.unsigned d)) :
      Ptrofs.ltu (Ptrofs.add a d) (Ptrofs.add b d) = Ptrofs.ltu a b := by
    rw [he, he, ha, hb]
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt, Int.add_lt_add_iff_right]
  cases c <;> simp only [Ptrofs.cmpu, heq,
    hlt x y (suffix_operation_unsigned_add x d hx) (suffix_operation_unsigned_add y d hy),
    hlt y x (suffix_operation_unsigned_add y d hy) (suffix_operation_unsigned_add x d hx)]

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers

private theorem suffix_operation_cmplu_inj : Val.cmplu_bool_injectStatement := by
  intro f vp1 vp2
  dsimp only
  intro hv hw hb hd c v1 v2 v1' v2' b h1 h2 heval
  cases h1 <;> cases h2 <;>
    simp only [Val.cmplu_bool, CompCert4Lean.X86_64.Archi.ptr64,
      Bool.true_and, if_true] at heval ⊢ <;> try contradiction
  case inject_long.inject_long => exact heval
  case inject_long.inject_ptr i b1 o1 b2 o2 d hm ho =>
    subst o2
    split at heval
    · rename_i h
      obtain ⟨hz, hp⟩ := Bool.and_eq_true_iff.mp h
      rw [hz, hw b1 o1 b2 d hm hp]
      exact heval
    · contradiction
  case inject_ptr.inject_long b1 o1 b2 o2 d hm ho i =>
    subst o2
    split at heval
    · rename_i h
      obtain ⟨hz, hp⟩ := Bool.and_eq_true_iff.mp h
      rw [hz, hw b1 o1 b2 d hm hp]
      exact heval
    · contradiction
  case inject_ptr.inject_ptr b1 o1 b1' o1' d1 hm1 ho1 b2 o2 b2' o2' d2 hm2 ho2 =>
    subst o1' o2'
    cases hs : eq_block b1 b2 with
    | left heq =>
      subst b2
      have hh := Option.some.inj (hm1.symm.trans hm2)
      cases hh
      cases ht : eq_block b1' b1' with
      | left heq' =>
        simp only [hs, ht] at heval ⊢
        run_tac
          let env ← Lean.getEnv
          let some (n, _) := env.constants.toList.find?
            (fun (n, _) => (toString n).endsWith "Common.Values.boolOfSumbool")
            | throwError "boolean projection helper unavailable"
          Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent n) at $(Lean.mkIdent `heval):ident ⊢))
        simp only [if_true] at heval ⊢
        split at heval
        · rename_i hp
          obtain ⟨hp1, hp2⟩ := Bool.and_eq_true_iff.mp hp
          rw [hw b1 o1 b1' d1 hm1 hp1, hw b1 o2 b1' d1 hm1 hp2]
          rw [suffix_operation_cmpu_shift c o1 o2 (Ptrofs.repr d1)
            (hb b1 o1 b1' d1 hm1 hp1) (hb b1 o2 b1' d1 hm1 hp2)]
          exact heval
        · contradiction
      | right hne => exact (hne rfl).elim
    | right hne =>
      simp only [hs] at heval
      run_tac
        let env ← Lean.getEnv
        let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "Common.Values.boolOfSumbool")
          | throwError "boolean projection helper unavailable"
        Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent n) at $(Lean.mkIdent `heval):ident))
      simp only [Bool.false_eq_true, if_false] at heval
      split at heval
      · rename_i hp
        obtain ⟨hp1, hp2⟩ := Bool.and_eq_true_iff.mp hp
        have hp1' := hv b1 o1 b1' d1 hm1 hp1
        have hp2' := hv b2 o2 b2' d2 hm2 hp2
        cases ht : eq_block b1' b2' with
        | right hne' =>
          simp only [ht, hp1', hp2', Bool.true_and, if_true]
          run_tac
            let env ← Lean.getEnv
            let some (n, _) := env.constants.toList.find?
              (fun (n, _) => (toString n).endsWith "Common.Values.boolOfSumbool")
              | throwError "boolean projection helper unavailable"
            Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent n)))
          simp only [Bool.false_eq_true, if_false, if_true]
          exact heval
        | left heq' =>
          subst b2'
          have hd' := hd b1 o1 b2 o2 b1' d1 b1' d2 hne hp1 hp2 hm1 hm2
          have hofs : Ptrofs.unsigned (Ptrofs.add o1 (Ptrofs.repr d1)) ≠
              Ptrofs.unsigned (Ptrofs.add o2 (Ptrofs.repr d2)) :=
            hd'.resolve_left (fun h => h rfl)
          simp only [ht, hp1', hp2', Bool.true_or, Bool.true_and, if_true]
          run_tac
            let env ← Lean.getEnv
            let some (n, _) := env.constants.toList.find?
              (fun (n, _) => (toString n).endsWith "Common.Values.boolOfSumbool")
              | throwError "boolean projection helper unavailable"
            Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent n)))
          simp only [Bool.false_eq_true, if_false, if_true]
          cases c <;> simp only [Val.cmp_different_blocks, Option.some.injEq] at heval <;>
            try contradiction
          all_goals subst b
          all_goals simp [Ptrofs.cmpu, Ptrofs.eq, WordCore.eq, Ptrofs.unsigned, WordCore.unsigned] at hofs ⊢
          all_goals exact hofs
      · contradiction

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers

private theorem suffix_operation_condition_inj : eval_condition_injStatement := by
  intro f m1 m2 hv hw hb hd cond vl1 vl2 r hvl heval
  have hcu := Val.cmpu_bool_inject f (Mem.valid_pointer m1) (Mem.valid_pointer m2) hv hw hb hd
  have hclu := suffix_operation_cmplu_inj f (Mem.valid_pointer m1) (Mem.valid_pointer m2) hv hw hb hd
  cases cond with
  | Ccomp c =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some r at heval
              contradiction
          | inject_list_cons b b' l1 l1' hbv hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.cmp_bool c a b = some r at heval
                  change Val.cmp_bool c a' b' = some r
                  cases ha <;> cases hbv <;>
                    simp only [Val.cmp_bool, Option.map_none, reduceCtorEq] at heval ⊢ <;> exact heval
              | inject_list_cons =>
                  change none = some r at heval
                  contradiction
  | Ccompu c =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some r at heval
              contradiction
          | inject_list_cons b b' l1 l1' hbv hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.cmpu_bool (Mem.valid_pointer m1) c a b = some r at heval
                  change Val.cmpu_bool (Mem.valid_pointer m2) c a' b' = some r
                  exact hcu c a b a' b' r ha hbv heval
              | inject_list_cons =>
                  change none = some r at heval
                  contradiction
  | Ccompimm c n =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.cmp_bool c a (.Vint n) = some r at heval
              change Val.cmp_bool c a' (.Vint n) = some r
              cases ha <;>
                simp only [Val.cmp_bool, Option.map_none, reduceCtorEq] at heval ⊢ <;> exact heval
          | inject_list_cons =>
              change none = some r at heval
              contradiction
  | Ccompuimm c n =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.cmpu_bool (Mem.valid_pointer m1) c a (.Vint n) = some r at heval
              change Val.cmpu_bool (Mem.valid_pointer m2) c a' (.Vint n) = some r
              exact hcu c a (.Vint n) a' (.Vint n) r ha (Val.inject_int f n) heval
          | inject_list_cons =>
              change none = some r at heval
              contradiction
  | Ccompl c =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some r at heval
              contradiction
          | inject_list_cons b b' l1 l1' hbv hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.cmpl_bool c a b = some r at heval
                  change Val.cmpl_bool c a' b' = some r
                  cases ha <;> cases hbv <;>
                    simp only [Val.cmpl_bool, Option.map_none, reduceCtorEq] at heval ⊢ <;> exact heval
              | inject_list_cons =>
                  change none = some r at heval
                  contradiction
  | Ccomplu c =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some r at heval
              contradiction
          | inject_list_cons b b' l1 l1' hbv hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.cmplu_bool (Mem.valid_pointer m1) c a b = some r at heval
                  change Val.cmplu_bool (Mem.valid_pointer m2) c a' b' = some r
                  exact hclu c a b a' b' r ha hbv heval
              | inject_list_cons =>
                  change none = some r at heval
                  contradiction
  | Ccomplimm c n =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.cmpl_bool c a (.Vlong n) = some r at heval
              change Val.cmpl_bool c a' (.Vlong n) = some r
              cases ha <;>
                simp only [Val.cmpl_bool, Option.map_none, reduceCtorEq] at heval ⊢ <;> exact heval
          | inject_list_cons =>
              change none = some r at heval
              contradiction
  | Ccompluimm c n =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.cmplu_bool (Mem.valid_pointer m1) c a (.Vlong n) = some r at heval
              change Val.cmplu_bool (Mem.valid_pointer m2) c a' (.Vlong n) = some r
              exact hclu c a (.Vlong n) a' (.Vlong n) r ha (Val.inject_long f n) heval
          | inject_list_cons =>
              change none = some r at heval
              contradiction
  | Ccompf c =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some r at heval
              contradiction
          | inject_list_cons b b' l1 l1' hbv hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.cmpf_bool c a b = some r at heval
                  change Val.cmpf_bool c a' b' = some r
                  cases ha <;> cases hbv <;>
                    simp only [Val.cmpf_bool, Option.map_none, reduceCtorEq] at heval ⊢ <;> exact heval
              | inject_list_cons =>
                  change none = some r at heval
                  contradiction
  | Cnotcompf c =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some r at heval
              contradiction
          | inject_list_cons b b' l1 l1' hbv hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change (Val.cmpf_bool c a b).map (!·) = some r at heval
                  change (Val.cmpf_bool c a' b').map (!·) = some r
                  cases ha <;> cases hbv <;>
                    simp only [Val.cmpf_bool, Option.map_none, reduceCtorEq] at heval ⊢ <;> exact heval
              | inject_list_cons =>
                  change none = some r at heval
                  contradiction
  | Ccompfs c =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some r at heval
              contradiction
          | inject_list_cons b b' l1 l1' hbv hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change Val.cmpfs_bool c a b = some r at heval
                  change Val.cmpfs_bool c a' b' = some r
                  cases ha <;> cases hbv <;>
                    simp only [Val.cmpfs_bool, Option.map_none, reduceCtorEq] at heval ⊢ <;> exact heval
              | inject_list_cons =>
                  change none = some r at heval
                  contradiction
  | Cnotcompfs c =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l2 l2' ha hl2 =>
          cases hl2 with
          | inject_list_nil =>
              change none = some r at heval
              contradiction
          | inject_list_cons b b' l1 l1' hbv hl1 =>
              cases hl1 with
              | inject_list_nil =>
                  change (Val.cmpfs_bool c a b).map (!·) = some r at heval
                  change (Val.cmpfs_bool c a' b').map (!·) = some r
                  cases ha <;> cases hbv <;>
                    simp only [Val.cmpfs_bool, Option.map_none, reduceCtorEq] at heval ⊢ <;> exact heval
              | inject_list_cons =>
                  change none = some r at heval
                  contradiction
  | Cmaskzero n =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change Val.maskzero_bool a n = some r at heval
              change Val.maskzero_bool a' n = some r
              cases ha <;>
                simp only [Val.maskzero_bool, Option.map_none, reduceCtorEq] at heval ⊢ <;> exact heval
          | inject_list_cons =>
              change none = some r at heval
              contradiction
  | Cmasknotzero n =>
      cases hvl with
      | inject_list_nil =>
          change none = some r at heval
          contradiction
      | inject_list_cons a a' l1 l1' ha hl1 =>
          cases hl1 with
          | inject_list_nil =>
              change (Val.maskzero_bool a n).map (!·) = some r at heval
              change (Val.maskzero_bool a' n).map (!·) = some r
              cases ha <;>
                simp only [Val.maskzero_bool, Option.map_none, reduceCtorEq] at heval ⊢ <;> exact heval
          | inject_list_cons =>
              change none = some r at heval
              contradiction

theorem eval_operation_inj
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_operation_injStatement binary64_certificate binary32_certificate :=
  suffix_operation_inj_of_condition suffix_operation_condition_inj

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Common.Values

theorem eval_operation_lessdef
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_operation_lessdefStatement binary64_certificate binary32_certificate := by
  intro F V genv sp op vl1 vl2 v1 m1 m2 hvl hext heval
  let f : meminj := fun b => some (b, z0)
  have hglobals : ∀ id ofs,
      id ∈ globals_operation op →
        Val.inject f
          (CompCert4Lean.Common.Globalenvs.Genv.symbol_address genv id ofs)
          (CompCert4Lean.Common.Globalenvs.Genv.symbol_address genv id ofs) := by
    intro id ofs _
    exact suffix_val_inject_lessdef _ _ (Val.lessdef.lessdef_refl _)
  have hsp : Val.inject f sp sp :=
    suffix_val_inject_lessdef _ _ (Val.lessdef.lessdef_refl _)
  have hvl' : Val.inject_list f vl1 vl2 :=
    suffix_val_inject_list_lessdef vl1 vl2 hvl
  obtain ⟨v2, heval2, hinj⟩ :=
    eval_operation_inj F F V V genv genv f m1 m2
      (valid_pointer_extends m1 m2 hext)
      (weak_valid_pointer_extends m1 m2 hext)
      (weak_valid_pointer_no_overflow_extends m1)
      (valid_different_pointers_extends m1)
      op sp vl1 sp vl2 v1 hglobals hsp hvl' heval
  exact ⟨v2, heval2, suffix_eval_addressing_lessdef_of_inject v1 v2 hinj⟩

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Integers

private theorem suffix_condition_inject_repr (z : Z)
    (hz : zLe z0 z ∧ zLe z Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.repr z) = z := by
  change Int64.unsigned (Int64.repr z) = z
  rw [suffix64_unsigned_repr]
  apply ZArith.BinInt.Z.mod_small
  refine ⟨hz.1, ?_⟩
  have h := hz.2
  change intOfZ z ≤ intOfZ Int64.modulus - 1 at h
  change intOfZ z < intOfZ Int64.modulus
  omega

private theorem suffix_condition_inject_bounds
    (f : meminj) (m1 m2 : mem) (hinj : Mem.inject f m1 m2)
    (b : block) (ofs : Ptrofs) (b' : block) (delta : Z)
    (hmap : f b = some (b', delta))
    (hp : Mem.weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true) :
    Ptrofs.unsigned (Ptrofs.repr delta) = delta ∧
      zLe z0 (zAdd (Ptrofs.unsigned ofs) delta) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) delta) Ptrofs.max_unsigned := by
  have hperm := (Mem.weak_valid_pointer_spec m1 b (Ptrofs.unsigned ofs)).mp hp
  have hmax :
      Mem.perm m1 b (Ptrofs.unsigned ofs) Max Nonempty ∨
      Mem.perm m1 b (ZArith.BinInt.Z.sub (Ptrofs.unsigned ofs) (zOfNat 1)) Max Nonempty := by
    rcases hperm with h | h
    · exact Or.inl (Mem.perm_cur_max m1 b _ Nonempty
        ((Mem.valid_pointer_nonempty_perm m1 b _).mp h))
    · exact Or.inr (Mem.perm_cur_max m1 b _ Nonempty
        ((Mem.valid_pointer_nonempty_perm m1 b _).mp h))
  obtain ⟨hd, hs⟩ := hinj.mi_representable b b' delta ofs hmap hmax
  have hu : 0 ≤ intOfZ (Ptrofs.unsigned ofs) := by
    have h := ofs.intrange.1
    change (-1 : _root_.Int) < intOfZ (Ptrofs.unsigned ofs) at h
    omega
  have hdmax : zLe delta Ptrofs.max_unsigned := by
    have h := hs.2
    change intOfZ (zAdd (Ptrofs.unsigned ofs) delta) ≤ intOfZ Ptrofs.max_unsigned at h
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at h
    change intOfZ delta ≤ intOfZ Ptrofs.max_unsigned
    omega
  exact ⟨suffix_condition_inject_repr delta ⟨hd, hdmax⟩, hs⟩

private theorem suffix_condition_inject_address
    (f : meminj) (m1 m2 : mem) (hinj : Mem.inject f m1 m2)
    (b : block) (ofs : Ptrofs) (b' : block) (delta : Z)
    (hmap : f b = some (b', delta))
    (hp : Mem.weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true) :
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) =
      zAdd (Ptrofs.unsigned ofs) delta := by
  obtain ⟨hd, hs⟩ := suffix_condition_inject_bounds f m1 m2 hinj b ofs b' delta hmap hp
  change Ptrofs.unsigned (Ptrofs.repr
    (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))) = _
  rw [hd]
  exact suffix_condition_inject_repr _ hs

theorem eval_condition_inject : eval_condition_injectStatement := by
  intro f cond vl1 vl2 r m1 m2 hvl hinj heval
  have hv (b : block) (ofs : Z) (b' : block) (delta : Z)
      (hmap : f b = some (b', delta))
      (hp : Mem.valid_pointer m1 b ofs = true) :
      Mem.valid_pointer m2 b' (zAdd ofs delta) = true := by
    apply (Mem.valid_pointer_nonempty_perm m2 b' _).mpr
    exact hinj.mi_inj.mi_perm b b' delta ofs Cur Nonempty hmap
      ((Mem.valid_pointer_nonempty_perm m1 b ofs).mp hp)
  apply suffix_operation_condition_inj f m1 m2 _ _ _ _ cond vl1 vl2 r hvl heval
  · intro b ofs b' delta hmap hp
    rw [suffix_condition_inject_address f m1 m2 hinj b ofs b' delta hmap
      (Mem.valid_pointer_implies m1 b _ hp)]
    exact hv b _ b' delta hmap hp
  · intro b ofs b' delta hmap hp
    rw [suffix_condition_inject_address f m1 m2 hinj b ofs b' delta hmap hp]
    apply (Mem.weak_valid_pointer_spec m2 b' _).mpr
    rcases (Mem.weak_valid_pointer_spec m1 b _).mp hp with h | h
    · exact Or.inl (hv b _ b' delta hmap h)
    · apply Or.inr
      have hshift :
          ZArith.BinInt.Z.sub (zAdd (Ptrofs.unsigned ofs) delta) (zOfNat 1) =
          zAdd (ZArith.BinInt.Z.sub (Ptrofs.unsigned ofs) (zOfNat 1)) delta := by
        apply intOfZ_injective
        simp only [zAdd, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        omega
      change Mem.valid_pointer m2 b'
        (ZArith.BinInt.Z.sub (zAdd (Ptrofs.unsigned ofs) delta) (zOfNat 1)) = true
      rw [hshift]
      exact hv b _ b' delta hmap h
  · intro b ofs b' delta hmap hp
    obtain ⟨hd, hs⟩ := suffix_condition_inject_bounds f m1 m2 hinj b ofs b' delta hmap hp
    rw [hd]
    exact hs
  · intro b1 ofs1 b2 ofs2 b1' delta1 b2' delta2 hne hp1 hp2 hmap1 hmap2
    rw [suffix_condition_inject_address f m1 m2 hinj b1 ofs1 b1' delta1 hmap1
        (Mem.valid_pointer_implies m1 b1 _ hp1),
      suffix_condition_inject_address f m1 m2 hinj b2 ofs2 b2' delta2 hmap2
        (Mem.valid_pointer_implies m1 b2 _ hp2)]
    exact hinj.mi_no_overlap b1 b1' delta1 b2 b2' delta2
      (Ptrofs.unsigned ofs1) (Ptrofs.unsigned ofs2) hne hmap1 hmap2
      (Mem.perm_cur_max m1 b1 _ Nonempty
        ((Mem.valid_pointer_nonempty_perm m1 b1 _).mp hp1))
      (Mem.perm_cur_max m1 b2 _ Nonempty
        ((Mem.valid_pointer_nonempty_perm m1 b2 _).mp hp2))

end CompCert4Lean.X86.Op

namespace CompCert4Lean.X86.Op

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Integers

 theorem eval_operation_inject
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_operation_injectStatement binary64_certificate binary32_certificate := by
  intro F V genv f hglobals sp1 sp2 delta hsp op vl1 vl2 v1 m1 m2 hvl hinj heval
  rw [eval_shift_stack_operation]
  have hvalid : ∀ b ofs b' d,
      f b = some (b', d) →
      Mem.valid_pointer m1 b (Ptrofs.unsigned ofs) = true →
      Mem.valid_pointer m2 b' (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr d))) = true := by
    intro b ofs b' d hmap hp
    rw [suffix_condition_inject_address f m1 m2 hinj b ofs b' d hmap
      (Mem.valid_pointer_implies m1 b _ hp)]
    apply (Mem.valid_pointer_nonempty_perm m2 b' _).mpr
    exact hinj.mi_inj.mi_perm b b' d (Ptrofs.unsigned ofs) Cur Nonempty hmap
      ((Mem.valid_pointer_nonempty_perm m1 b _).mp hp)
  have hweak : ∀ b ofs b' d,
      f b = some (b', d) →
      Mem.weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m2 b' (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr d))) = true := by
    intro b ofs b' d hmap hp
    rw [suffix_condition_inject_address f m1 m2 hinj b ofs b' d hmap hp]
    apply (Mem.weak_valid_pointer_spec m2 b' _).mpr
    rcases (Mem.weak_valid_pointer_spec m1 b _).mp hp with h | h
    · apply Or.inl
      apply (Mem.valid_pointer_nonempty_perm m2 b' _).mpr
      exact hinj.mi_inj.mi_perm b b' d (Ptrofs.unsigned ofs) Cur Nonempty hmap
        ((Mem.valid_pointer_nonempty_perm m1 b _).mp h)
    · apply Or.inr
      have hshift :
          ZArith.BinInt.Z.sub (zAdd (Ptrofs.unsigned ofs) d) (zOfNat 1) =
          zAdd (ZArith.BinInt.Z.sub (Ptrofs.unsigned ofs) (zOfNat 1)) d := by
        apply intOfZ_injective
        simp only [zAdd, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        omega
      change Mem.valid_pointer m2 b'
        (ZArith.BinInt.Z.sub (zAdd (Ptrofs.unsigned ofs) d) (zOfNat 1)) = true
      rw [hshift]
      apply (Mem.valid_pointer_nonempty_perm m2 b' _).mpr
      exact hinj.mi_inj.mi_perm b b' d
        (ZArith.BinInt.Z.sub (Ptrofs.unsigned ofs) (zOfNat 1)) Cur Nonempty hmap
        ((Mem.valid_pointer_nonempty_perm m1 b _).mp h)
  have hbound : ∀ b ofs b' d,
      f b = some (b', d) →
      Mem.weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr d))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr d)))
        Ptrofs.max_unsigned := by
    intro b ofs b' d hmap hp
    obtain ⟨hd, hs⟩ := suffix_condition_inject_bounds f m1 m2 hinj b ofs b' d hmap hp
    rw [hd]
    exact hs
  have hdiff : ∀ b1 ofs1 b2 ofs2 b1' d1 b2' d2,
      b1 ≠ b2 →
      Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true →
      Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', d1) →
      f b2 = some (b2', d2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr d1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr d2)) := by
    intro b1 ofs1 b2 ofs2 b1' d1 b2' d2 hne hp1 hp2 hmap1 hmap2
    rw [suffix_condition_inject_address f m1 m2 hinj b1 ofs1 b1' d1 hmap1
        (Mem.valid_pointer_implies m1 b1 _ hp1),
      suffix_condition_inject_address f m1 m2 hinj b2 ofs2 b2' d2 hmap2
        (Mem.valid_pointer_implies m1 b2 _ hp2)]
    exact hinj.mi_no_overlap b1 b1' d1 b2 b2' d2
      (Ptrofs.unsigned ofs1) (Ptrofs.unsigned ofs2) hne hmap1 hmap2
      (Mem.perm_cur_max m1 b1 _ Nonempty
        ((Mem.valid_pointer_nonempty_perm m1 b1 _).mp hp1))
      (Mem.perm_cur_max m1 b2 _ Nonempty
        ((Mem.valid_pointer_nonempty_perm m1 b2 _).mp hp2))
  have hsp' :
      Val.inject f (.Vptr sp1 Ptrofs.zero)
        (.Vptr sp2 (Ptrofs.repr delta)) :=
    Val.inject.inject_ptr sp1 Ptrofs.zero sp2 (Ptrofs.repr delta) delta hsp (by
      rw [CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api]
      exact (suffixPtrofsAddZero _).symm)
  exact eval_operation_inj F F V V genv genv f m1 m2
    hvalid hweak hbound hdiff op
    (.Vptr sp1 Ptrofs.zero) vl1
    (.Vptr sp2 (Ptrofs.repr delta)) vl2 v1
    (by
      intro id ofs _
      exact symbol_address_inject F V genv f hglobals id ofs)
    hsp' hvl heval

end CompCert4Lean.X86.Op
