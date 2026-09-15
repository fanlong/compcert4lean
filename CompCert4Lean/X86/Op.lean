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
