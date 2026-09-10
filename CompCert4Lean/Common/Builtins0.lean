import CompCert4Lean.Common.Memdata
import CompCert4Lean.Foundation.RocqString

/-!
# Semantics of built-in functions

Definition-bearing translation of `common/Builtins0.v`.  Proof declarations
assigned to the later proof-migration phase are represented by transparent
proposition descriptors.
-/

namespace CompCert4Lean.Common.Builtins0

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Floats

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev intZero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev intOne := CompCert4Lean.Lib.Integers.Int.one

set_option maxHeartbeats 1000000

private def ofString (s : String) : RocqString :=
  (String.toUTF8 s).toList.foldr
    (fun b tail =>
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.String b tail)
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.EmptyString

def val_opt_has_rettype (ov : Option val) (t : xtype) : Prop :=
  match ov with
  | some v => Val.has_rettype v t
  | none => True

def val_opt_inject (j : meminj) (ov ov' : Option val) : Prop :=
  match ov, ov' with
  | none, _ => True
  | some v, some v' => Val.inject j v v'
  | some _, none => False

structure builtin_sem (tret : xtype) : Type where
  bs_sem : List val → Option val
  bs_well_typed : ∀ vl, val_opt_has_rettype (bs_sem vl) tret
  bs_inject : ∀ j vl vl',
    Val.inject_list j vl vl' → val_opt_inject j (bs_sem vl) (bs_sem vl')

export builtin_sem (bs_sem bs_well_typed bs_inject)

instance (tret : xtype) : CoeFun (builtin_sem tret) (fun _ => List val → Option val) :=
  ⟨builtin_sem.bs_sem⟩

def mkbuiltin_v1t
    (tret : xtype) (f : val → val)
    (WT : ∀ v1, Val.has_rettype (f v1) tret)
    (INJ : ∀ j v1 v1', Val.inject j v1 v1' → Val.inject j (f v1) (f v1')) :
    builtin_sem tret where
  bs_sem := fun vl =>
    match vl with
    | [v1] => some (f v1)
    | _ => none
  bs_well_typed := by
    intro vl
    cases vl with
    | nil => trivial
    | cons v1 tail =>
        cases tail with
        | nil => exact WT v1
        | cons _ _ => trivial
  bs_inject := by
    intro j vl vl' h
    rcases h with ⟨⟩ | ⟨_, _, _, _, h1, ht⟩
    · trivial
    · rcases ht with ⟨⟩ | ⟨_, _, _, _, _, _⟩
      · exact INJ j _ _ h1
      · trivial

def mkbuiltin_v2t
    (tret : xtype) (f : val → val → val)
    (WT : ∀ v1 v2, Val.has_rettype (f v1 v2) tret)
    (INJ : ∀ j v1 v1' v2 v2',
      Val.inject j v1 v1' → Val.inject j v2 v2' →
      Val.inject j (f v1 v2) (f v1' v2')) : builtin_sem tret where
  bs_sem := fun vl =>
    match vl with
    | [v1, v2] => some (f v1 v2)
    | _ => none
  bs_well_typed := by
    intro vl
    cases vl with
    | nil => trivial
    | cons v1 tail =>
        cases tail with
        | nil => trivial
        | cons v2 tail =>
            cases tail with
            | nil => exact WT v1 v2
            | cons _ _ => trivial
  bs_inject := by
    intro j vl vl' h
    rcases h with ⟨⟩ | ⟨_, _, _, _, h1, ht⟩
    · trivial
    · rcases ht with ⟨⟩ | ⟨_, _, _, _, h2, ht⟩
      · trivial
      · rcases ht with ⟨⟩ | ⟨_, _, _, _, _, _⟩
        · exact INJ j _ _ _ _ h1 h2
        · trivial

def mkbuiltin_v1p
    (tret : xtype) (f : val → Option val)
    (WT : ∀ v1, val_opt_has_rettype (f v1) tret)
    (INJ : ∀ j v1 v1', Val.inject j v1 v1' →
      val_opt_inject j (f v1) (f v1')) : builtin_sem tret where
  bs_sem := fun vl =>
    match vl with
    | [v1] => f v1
    | _ => none
  bs_well_typed := by
    intro vl
    cases vl with
    | nil => trivial
    | cons v1 tail =>
        cases tail with
        | nil => exact WT v1
        | cons _ _ => trivial
  bs_inject := by
    intro j vl vl' h
    rcases h with ⟨⟩ | ⟨_, _, _, _, h1, ht⟩
    · trivial
    · rcases ht with ⟨⟩ | ⟨_, _, _, _, _, _⟩
      · exact INJ j _ _ h1
      · trivial

def mkbuiltin_v2p
    (tret : xtype) (f : val → val → Option val)
    (WT : ∀ v1 v2, val_opt_has_rettype (f v1 v2) tret)
    (INJ : ∀ j v1 v1' v2 v2',
      Val.inject j v1 v1' → Val.inject j v2 v2' →
      val_opt_inject j (f v1 v2) (f v1' v2')) : builtin_sem tret where
  bs_sem := fun vl =>
    match vl with
    | [v1, v2] => f v1 v2
    | _ => none
  bs_well_typed := by
    intro vl
    cases vl with
    | nil => trivial
    | cons v1 tail =>
        cases tail with
        | nil => trivial
        | cons v2 tail =>
            cases tail with
            | nil => exact WT v1 v2
            | cons _ _ => trivial
  bs_inject := by
    intro j vl vl' h
    rcases h with ⟨⟩ | ⟨_, _, _, _, h1, ht⟩
    · trivial
    · rcases ht with ⟨⟩ | ⟨_, _, _, _, h2, ht⟩
      · trivial
      · rcases ht with ⟨⟩ | ⟨_, _, _, _, _, _⟩
        · exact INJ j _ _ _ _ h1 h2
        · trivial

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := ZArith.BinInt.Z.of_nat 1
private abbrev z8 : Z := ZArith.BinInt.Z.of_nat 8
private abbrev z16 : Z := ZArith.BinInt.Z.of_nat 16
private abbrev zSub := ZArith.BinInt.Z.sub

private abbrev intZeroExt := CompCert4Lean.Lib.Integers.Int.zero_ext

private abbrev intSignExt := CompCert4Lean.Lib.Integers.Int.sign_ext

def valty : typ → Type
  | Tint => CCInt
  | Tlong => CCInt64
  | Tfloat => CCFloat
  | Tsingle => CCFloat32
  | Tany32 | Tany64 => Empty

def valxty : xtype → Type
  | Xbool => {n : CCInt // n = intZero ∨ n = intOne}
  | Xint8signed => {n : CCInt // n = intSignExt z8 n}
  | Xint8unsigned => {n : CCInt // n = intZeroExt z8 n}
  | Xint16signed => {n : CCInt // n = intSignExt z16 n}
  | Xint16unsigned => {n : CCInt // n = intZeroExt z16 n}
  | Xint => CCInt
  | Xlong => CCInt64
  | Xfloat => CCFloat
  | Xsingle => CCFloat32
  | Xptr | Xany32 | Xany64 => Empty
  | Xvoid => Unit

def inj_num (t : xtype) : valxty t → val :=
  match t with
  | Xbool | Xint8signed | Xint8unsigned | Xint16signed | Xint16unsigned =>
      fun n => Vint n.1
  | Xint => Vint
  | Xlong => Vlong
  | Xfloat => Vfloat
  | Xsingle => Vsingle
  | _ => fun _ => Vundef

def proj_num {A : Type} (t : typ) (k0 : A) (v : val) : (valty t → A) → A :=
  match t with
  | Tint => fun k1 => match v with | Vint n => k1 n | _ => k0
  | Tlong => fun k1 => match v with | Vlong n => k1 n | _ => k0
  | Tfloat => fun k1 => match v with | Vfloat n => k1 n | _ => k0
  | Tsingle => fun k1 => match v with | Vsingle n => k1 n | _ => k0
  | Tany32 | Tany64 => fun _ => k0

def inj_num_wtStatement : Prop :=
  ∀ t x, Val.has_rettype (inj_num t x) t

def inj_num_injectStatement : Prop :=
  ∀ j t x, Val.inject j (inj_num t x) (inj_num t x)

def inj_num_opt_wtStatement : Prop :=
  ∀ t x, val_opt_has_rettype (Option.map (inj_num t) x) t

def inj_num_opt_injectStatement : Prop :=
  ∀ j t x, val_opt_inject j (Option.map (inj_num t) x) (Option.map (inj_num t) x)

def proj_num_wtStatement : Prop :=
  ∀ tres t k1 v,
    (∀ x, Val.has_rettype (k1 x) tres) →
      Val.has_rettype (proj_num t Vundef v k1) tres

def proj_num_injectStatement : Prop :=
  ∀ j t k1 v k1' v',
    (∀ x, Val.inject j (k1 x) (k1' x)) →
      Val.inject j v v' →
        Val.inject j (proj_num t Vundef v k1) (proj_num t Vundef v' k1')

def proj_num_opt_wtStatement : Prop :=
  ∀ tres t k0 k1 v,
    (k0 = none ∨ k0 = some Vundef) →
      (∀ x, val_opt_has_rettype (k1 x) tres) →
        val_opt_has_rettype (proj_num t k0 v k1) tres

def proj_num_opt_injectStatement : Prop :=
  ∀ j k0 t k1 v k1' v',
    (∀ ov, val_opt_inject j k0 ov) →
      (∀ x, val_opt_inject j (k1 x) (k1' x)) →
        Val.inject j v v' →
          val_opt_inject j (proj_num t k0 v k1) (proj_num t k0 v' k1')

private def vundefHasRettype (t : xtype) : Val.has_rettype Vundef t := by
  cases t <;> trivial

private def injNumWellTyped (t : xtype) (x : valxty t) :
    Val.has_rettype (inj_num t x) t := by
  cases t with
  | Xbool => exact x.2
  | Xint8signed => exact x.2
  | Xint8unsigned => exact x.2
  | Xint16signed => exact x.2
  | Xint16unsigned => exact x.2
  | Xint => trivial
  | Xlong => trivial
  | Xfloat => trivial
  | Xsingle => trivial
  | Xptr => exact nomatch x
  | Xany32 => exact nomatch x
  | Xany64 => exact nomatch x
  | Xvoid => trivial

private def injNumInject (j : meminj) (t : xtype) (x : valxty t) :
    Val.inject j (inj_num t x) (inj_num t x) := by
  cases t with
  | Xbool | Xint8signed | Xint8unsigned | Xint16signed | Xint16unsigned =>
      exact Val.inject_int j x.1
  | Xint => exact Val.inject_int j x
  | Xlong => exact Val.inject_long j x
  | Xfloat => exact Val.inject_float j x
  | Xsingle => exact Val.inject_single j x
  | Xptr => exact nomatch x
  | Xany32 => exact nomatch x
  | Xany64 => exact nomatch x
  | Xvoid => exact Val.val_inject_undef j Vundef

private def projNumWellTyped
    (tres : xtype) (t : typ) (k1 : valty t → val) (v : val)
    (h : ∀ x, Val.has_rettype (k1 x) tres) :
    Val.has_rettype (proj_num t Vundef v k1) tres := by
  cases t <;> cases v <;> simp [proj_num]
  all_goals first | apply h | apply vundefHasRettype

private def projNumInject
    (j : meminj) (t : typ) (k1 : valty t → val) (v : val)
    (k1' : valty t → val) (v' : val)
    (hk : ∀ x, Val.inject j (k1 x) (k1' x))
    (hv : Val.inject j v v') :
    Val.inject j (proj_num t Vundef v k1) (proj_num t Vundef v' k1') := by
  cases t <;> cases hv <;> simp [proj_num]
  all_goals first | apply hk | apply Val.val_inject_undef

private def projNumOptWellTyped
    (tres : xtype) (t : typ) (k0 : Option val) (k1 : valty t → Option val) (v : val)
    (h0 : k0 = none ∨ k0 = some Vundef)
    (hk : ∀ x, val_opt_has_rettype (k1 x) tres) :
    val_opt_has_rettype (proj_num t k0 v k1) tres := by
  have hk0 : val_opt_has_rettype k0 tres := by
    rcases h0 with rfl | rfl
    · trivial
    · exact vundefHasRettype tres
  cases t <;> cases v <;> simp [proj_num]
  all_goals first | apply hk | apply hk0

private def projNumOptInject
    (j : meminj) (k0 : Option val) (t : typ)
    (k1 : valty t → Option val) (v : val)
    (k1' : valty t → Option val) (v' : val)
    (h0 : ∀ ov, val_opt_inject j k0 ov)
    (hk : ∀ x, val_opt_inject j (k1 x) (k1' x))
    (hv : Val.inject j v v') :
    val_opt_inject j (proj_num t k0 v k1) (proj_num t k0 v' k1') := by
  cases t <;> cases hv <;> simp [proj_num]
  all_goals first | apply hk | apply h0

def mkbuiltin_n1t
    (targ1 : typ) (tres : xtype) (f : valty targ1 → valxty tres) :
    builtin_sem tres :=
  mkbuiltin_v1t tres
    (fun v1 => proj_num targ1 Vundef v1 (fun x => inj_num tres (f x)))
    (by intro v1; exact projNumWellTyped tres targ1 _ v1 (fun x => injNumWellTyped tres (f x)))
    (by
      intro j v1 v1' hv
      exact projNumInject j targ1 _ v1 _ v1'
        (fun x => injNumInject j tres (f x)) hv)

def mkbuiltin_n2t
    (targ1 targ2 : typ) (tres : xtype)
    (f : valty targ1 → valty targ2 → valxty tres) : builtin_sem tres :=
  mkbuiltin_v2t tres
    (fun v1 v2 =>
      proj_num targ1 Vundef v1 (fun x1 =>
      proj_num targ2 Vundef v2 (fun x2 => inj_num tres (f x1 x2))))
    (by
      intro v1 v2
      exact projNumWellTyped tres targ1 _ v1 (fun x1 =>
        projNumWellTyped tres targ2 _ v2 (fun x2 => injNumWellTyped tres (f x1 x2))))
    (by
      intro j v1 v1' v2 v2' h1 h2
      exact projNumInject j targ1 _ v1 _ v1' (fun x1 =>
        projNumInject j targ2 _ v2 _ v2' (fun x2 => injNumInject j tres (f x1 x2)) h2) h1)

def mkbuiltin_n1p
    (targ1 : typ) (tres : xtype)
    (f : valty targ1 → Option (valxty tres)) : builtin_sem tres :=
  mkbuiltin_v1p tres
    (fun v1 => proj_num targ1 none v1 (fun x => Option.map (inj_num tres) (f x)))
    (by
      intro v1
      exact projNumOptWellTyped tres targ1 none _ v1 (Or.inl rfl) (fun x => by
        cases f x with
        | none => trivial
        | some y => exact injNumWellTyped tres y))
    (by
      intro j v1 v1' hv
      exact projNumOptInject j none targ1 _ v1 _ v1'
        (fun _ => trivial)
        (fun x => by
          cases f x with
          | none => trivial
          | some y => exact injNumInject j tres y)
        hv)

def lookup_builtin {A : Type} (sig_of : A → signature)
    (name : RocqString) (sg : signature) : List (RocqString × A) → Option A
  | [] => none
  | (n, b) :: rest =>
      match
        CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string_dec name n,
        signature_eq sg (sig_of b) with
      | .left _, .left _ => some b
      | _, _ => lookup_builtin sig_of name sg rest

def lookup_builtin_sigStatement : Prop :=
  ∀ (A : Type) (sig_of : A → signature) name sg b l,
    lookup_builtin sig_of name sg l = some b → sig_of b = sg

inductive standard_builtin : Type where
  | BI_select (t : typ)
  | BI_fabs
  | BI_fabsf
  | BI_fsqrt
  | BI_negl
  | BI_addl
  | BI_subl
  | BI_mull
  | BI_i16_bswap
  | BI_i32_bswap
  | BI_i64_bswap
  | BI_unreachable
  | BI_i64_umulh
  | BI_i64_smulh
  | BI_i64_sdiv
  | BI_i64_udiv
  | BI_i64_smod
  | BI_i64_umod
  | BI_i64_shl
  | BI_i64_shr
  | BI_i64_sar
  | BI_i64_dtos
  | BI_i64_dtou
  | BI_i64_stod
  | BI_i64_utod
  | BI_i64_stof
  | BI_i64_utof
deriving DecidableEq

export standard_builtin (BI_select BI_fabs BI_fabsf BI_fsqrt BI_negl BI_addl BI_subl
  BI_mull BI_i16_bswap BI_i32_bswap BI_i64_bswap BI_unreachable BI_i64_umulh
  BI_i64_smulh BI_i64_sdiv BI_i64_udiv BI_i64_smod BI_i64_umod BI_i64_shl BI_i64_shr
  BI_i64_sar BI_i64_dtos BI_i64_dtou BI_i64_stod BI_i64_utod BI_i64_stof BI_i64_utof)

def eq_standard_builtin (x y : standard_builtin) : Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

def standard_builtin_table : List (RocqString × standard_builtin) :=
  [ (ofString "__builtin_sel", BI_select Tint)
  , (ofString "__builtin_sel", BI_select Tlong)
  , (ofString "__builtin_sel", BI_select Tfloat)
  , (ofString "__builtin_sel", BI_select Tsingle)
  , (ofString "__builtin_fabs", BI_fabs)
  , (ofString "__builtin_fabsf", BI_fabsf)
  , (ofString "__builtin_fsqrt", BI_fsqrt)
  , (ofString "__builtin_sqrt", BI_fsqrt)
  , (ofString "__builtin_negl", BI_negl)
  , (ofString "__builtin_addl", BI_addl)
  , (ofString "__builtin_subl", BI_subl)
  , (ofString "__builtin_mull", BI_mull)
  , (ofString "__builtin_bswap16", BI_i16_bswap)
  , (ofString "__builtin_bswap", BI_i32_bswap)
  , (ofString "__builtin_bswap32", BI_i32_bswap)
  , (ofString "__builtin_bswap64", BI_i64_bswap)
  , (ofString "__builtin_unreachable", BI_unreachable)
  , (ofString "__compcert_i64_umulh", BI_i64_umulh)
  , (ofString "__compcert_i64_smulh", BI_i64_smulh)
  , (ofString "__compcert_i64_sdiv", BI_i64_sdiv)
  , (ofString "__compcert_i64_udiv", BI_i64_udiv)
  , (ofString "__compcert_i64_smod", BI_i64_smod)
  , (ofString "__compcert_i64_umod", BI_i64_umod)
  , (ofString "__compcert_i64_shl", BI_i64_shl)
  , (ofString "__compcert_i64_shr", BI_i64_shr)
  , (ofString "__compcert_i64_sar", BI_i64_sar)
  , (ofString "__compcert_i64_dtos", BI_i64_dtos)
  , (ofString "__compcert_i64_dtou", BI_i64_dtou)
  , (ofString "__compcert_i64_stod", BI_i64_stod)
  , (ofString "__compcert_i64_utod", BI_i64_utod)
  , (ofString "__compcert_i64_stof", BI_i64_stof)
  , (ofString "__compcert_i64_utof", BI_i64_utof) ]

private def mkSignature (args : List xtype) (res : xtype) : signature :=
  { sig_args := args, sig_res := res, sig_cc := cc_default }

def standard_builtin_sig : standard_builtin → signature
  | BI_select t => mkSignature [Xint, inj_type t, inj_type t] (inj_type t)
  | BI_fabs | BI_fsqrt => mkSignature [Xfloat] Xfloat
  | BI_fabsf => mkSignature [Xsingle] Xsingle
  | BI_negl => mkSignature [Xlong] Xlong
  | BI_addl | BI_subl | BI_i64_umulh | BI_i64_smulh
  | BI_i64_sdiv | BI_i64_udiv | BI_i64_smod | BI_i64_umod =>
      mkSignature [Xlong, Xlong] Xlong
  | BI_mull => mkSignature [Xint, Xint] Xlong
  | BI_i32_bswap => mkSignature [Xint] Xint
  | BI_i64_bswap => mkSignature [Xlong] Xlong
  | BI_i16_bswap => mkSignature [Xint16unsigned] Xint16unsigned
  | BI_unreachable => mkSignature [] Xvoid
  | BI_i64_shl | BI_i64_shr | BI_i64_sar => mkSignature [Xlong, Xint] Xlong
  | BI_i64_dtos | BI_i64_dtou => mkSignature [Xfloat] Xlong
  | BI_i64_stod | BI_i64_utod => mkSignature [Xlong] Xfloat
  | BI_i64_stof | BI_i64_utof => mkSignature [Xlong] Xsingle

private def byteSwap32 (n : CCInt) : CCInt :=
  CompCert4Lean.Lib.Integers.Int.repr
    (CompCert4Lean.Common.Memdata.decode_int
      (List.reverse
        (CompCert4Lean.Common.Memdata.encode_int 4
          (CompCert4Lean.Lib.Integers.Int.unsigned n))))

private def byteSwap64 (n : CCInt64) : CCInt64 :=
  CompCert4Lean.Lib.Integers.Int64.repr
    (CompCert4Lean.Common.Memdata.decode_int
      (List.reverse
        (CompCert4Lean.Common.Memdata.encode_int 8
          (CompCert4Lean.Lib.Integers.Int64.unsigned n))))

private def byteSwap16 (n : CCInt) : valxty Xint16unsigned :=
  let bl := List.reverse
    (CompCert4Lean.Common.Memdata.encode_int 2
      (CompCert4Lean.Lib.Integers.Int.unsigned n))
  let x := CompCert4Lean.Common.Memdata.decode_int bl
  ⟨CompCert4Lean.Lib.Integers.Int.repr x, by
    have hbl : bl.length = 2 := by
      simpa [bl] using
        CompCert4Lean.Common.Memdata.encode_int_length_proof_api 2
          (CompCert4Lean.Lib.Integers.Int.unsigned n)
    have hx := CompCert4Lean.Common.Memdata.int_of_bytes_range_proof_api
      (CompCert4Lean.Common.Memdata.rev_if_be bl)
    have hrev := CompCert4Lean.Common.Memdata.rev_if_be_length_proof_api bl
    have hx16 :
        ZArith.BinInt.Z.le z0 x ∧
          ZArith.BinInt.Z.lt x
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_p z16) := by
      change ZArith.BinInt.Z.le z0
          (CompCert4Lean.Common.Memdata.int_of_bytes
            (CompCert4Lean.Common.Memdata.rev_if_be bl)) ∧
        ZArith.BinInt.Z.lt
          (CompCert4Lean.Common.Memdata.int_of_bytes
            (CompCert4Lean.Common.Memdata.rev_if_be bl))
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_p z16)
      rw [hrev, hbl] at hx
      have h16 :
          ZArith.BinInt.Z.mul (ZArith.BinInt.Z.of_nat 2)
              (ZArith.BinInt.Z.of_nat 8) = z16 := by
        rfl
      change ZArith.BinInt.Z.le z0
          (CompCert4Lean.Common.Memdata.int_of_bytes
            (CompCert4Lean.Common.Memdata.rev_if_be bl)) ∧
        ZArith.BinInt.Z.lt
          (CompCert4Lean.Common.Memdata.int_of_bytes
            (CompCert4Lean.Common.Memdata.rev_if_be bl))
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_p
            (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.of_nat 2)
              (ZArith.BinInt.Z.of_nat 8))) at hx
      rw [h16] at hx
      exact hx
    have hxmax :
        ZArith.BinInt.Z.le z0 x ∧
          ZArith.BinInt.Z.le x CompCert4Lean.Lib.Integers.Int.max_unsigned := by
      constructor
      · exact hx16.1
      · have hxlt := hx16.2
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x ≤ 4294967295
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x < 65536 at hxlt
        omega
    apply CompCert4Lean.Lib.Integers.WordCore.ext
    change CompCert4Lean.Lib.Integers.Int.unsigned
        (CompCert4Lean.Lib.Integers.Int.repr x) =
      CompCert4Lean.Lib.Integers.Int.unsigned
        (CompCert4Lean.Lib.Integers.Int.zero_ext z16
          (CompCert4Lean.Lib.Integers.Int.repr x))
    rw [CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api x hxmax]
    rw [CompCert4Lean.Lib.Integers.Int.zero_ext_mod_proof_api z16
      (CompCert4Lean.Lib.Integers.Int.repr x) (by
        change (0 : _root_.Int) ≤ 16 ∧ (16 : _root_.Int) < 32
        omega)]
    rw [CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api x hxmax]
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mod_small
      x (CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_p z16) hx16).symm⟩

private def mkbuiltin_num_v2tInternal
    (targ1 targ2 : typ) (tres : xtype)
    (f : valty targ1 → valty targ2 → val)
    (hwt : ∀ x1 x2, Val.has_rettype (f x1 x2) tres)
    (hinj : ∀ j x1 x2, Val.inject j (f x1 x2) (f x1 x2)) : builtin_sem tres :=
  mkbuiltin_v2t tres
    (fun v1 v2 =>
      proj_num targ1 Vundef v1 (fun x1 =>
      proj_num targ2 Vundef v2 (fun x2 => f x1 x2)))
    (by
      intro v1 v2
      exact projNumWellTyped tres targ1 _ v1 (fun x1 =>
        projNumWellTyped tres targ2 _ v2 (fun x2 => hwt x1 x2)))
    (by
      intro j v1 v1' v2 v2' h1 h2
      exact projNumInject j targ1 _ v1 _ v1' (fun x1 =>
        projNumInject j targ2 _ v2 _ v2' (fun x2 => hinj j x1 x2) h2) h1)

private def longBinaryTotal
    (f : val → val → val)
    (hwt : ∀ v1 v2, Val.has_rettype (f v1 v2) Xlong)
    (hinj : ∀ j v1 v1' v2 v2', Val.inject j v1 v1' → Val.inject j v2 v2' →
      Val.inject j (f v1 v2) (f v1' v2')) : builtin_sem Xlong :=
  mkbuiltin_v2t Xlong f hwt hinj

private def longBinaryPartial
    (f : val → val → Option val)
    (hwt : ∀ v1 v2, val_opt_has_rettype (f v1 v2) Xlong)
    (hinj : ∀ j v1 v1' v2 v2', Val.inject j v1 v1' → Val.inject j v2 v2' →
      val_opt_inject j (f v1 v2) (f v1' v2')) : builtin_sem Xlong :=
  mkbuiltin_v2p Xlong f hwt hinj

private def ptrofsAddSwap
    (a b c : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add
        (CompCert4Lean.Lib.Integers.Ptrofs.add a b) c =
      CompCert4Lean.Lib.Integers.Ptrofs.add
        (CompCert4Lean.Lib.Integers.Ptrofs.add a c) b := by
  rw [CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api,
    CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api]
  congr 1
  exact CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api b c

private def ptrofsSubAdd
    (a b c : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.sub
        (CompCert4Lean.Lib.Integers.Ptrofs.add a b) c =
      CompCert4Lean.Lib.Integers.Ptrofs.add
        (CompCert4Lean.Lib.Integers.Ptrofs.sub a c) b := by
  exact CompCert4Lean.Lib.Integers.Ptrofs.sub_add_l_proof_api a b c

private def ptrofsSubCancel
    (a b c : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.sub
        (CompCert4Lean.Lib.Integers.Ptrofs.add a c)
        (CompCert4Lean.Lib.Integers.Ptrofs.add b c) =
      CompCert4Lean.Lib.Integers.Ptrofs.sub a b := by
  exact CompCert4Lean.Lib.Integers.Ptrofs.sub_shifted_proof_api a b c

private def divlsBuiltin : builtin_sem Xlong :=
  longBinaryPartial Val.divls
    (by
      intro v1 v2
      cases v1 <;> cases v2
      all_goals simp only [Val.divls]
      all_goals try trivial
      case Vlong.Vlong =>
        split <;> trivial)
    (by
      intro j v1 v1' v2 v2' h1 h2
      cases h1 <;> cases h2
      all_goals simp only [Val.divls]
      all_goals try trivial
      all_goals
        split
        · trivial
        · exact Val.inject_long j _)

private def divluBuiltin : builtin_sem Xlong :=
  longBinaryPartial Val.divlu
    (by
      intro v1 v2
      cases v1 <;> cases v2
      all_goals simp only [Val.divlu]
      all_goals try trivial
      case Vlong.Vlong =>
        split <;> trivial)
    (by
      intro j v1 v1' v2 v2' h1 h2
      cases h1 <;> cases h2
      all_goals simp only [Val.divlu]
      all_goals try trivial
      all_goals
        split
        · trivial
        · exact Val.inject_long j _)

private def modlsBuiltin : builtin_sem Xlong :=
  longBinaryPartial Val.modls
    (by
      intro v1 v2
      cases v1 <;> cases v2
      all_goals simp only [Val.modls]
      all_goals try trivial
      case Vlong.Vlong =>
        split <;> trivial)
    (by
      intro j v1 v1' v2 v2' h1 h2
      cases h1 <;> cases h2
      all_goals simp only [Val.modls]
      all_goals try trivial
      all_goals
        split
        · trivial
        · exact Val.inject_long j _)

private def modluBuiltin : builtin_sem Xlong :=
  longBinaryPartial Val.modlu
    (by
      intro v1 v2
      cases v1 <;> cases v2
      all_goals simp only [Val.modlu]
      all_goals try trivial
      case Vlong.Vlong =>
        split <;> trivial)
    (by
      intro j v1 v1' v2 v2' h1 h2
      cases h1 <;> cases h2
      all_goals simp only [Val.modlu]
      all_goals try trivial
      all_goals
        split
        · trivial
        · exact Val.inject_long j _)

private def shllBuiltin : builtin_sem Xlong :=
  mkbuiltin_num_v2tInternal Tlong Tint Xlong
    (fun n1 n2 =>
      if CompCert4Lean.Lib.Integers.Int.ltu n2 CompCert4Lean.Lib.Integers.Int64.iwordsize' then
        Vlong (CompCert4Lean.Lib.Integers.Int64.shl' n1 n2)
      else Vundef)
    (by intro n1 n2; split <;> trivial)
    (by
      intro j n1 n2
      split
      · exact Val.inject_long j _
      · exact Val.val_inject_undef j Vundef)

private def shrluBuiltin : builtin_sem Xlong :=
  mkbuiltin_num_v2tInternal Tlong Tint Xlong
    (fun n1 n2 =>
      if CompCert4Lean.Lib.Integers.Int.ltu n2 CompCert4Lean.Lib.Integers.Int64.iwordsize' then
        Vlong (CompCert4Lean.Lib.Integers.Int64.shru' n1 n2)
      else Vundef)
    (by intro n1 n2; split <;> trivial)
    (by
      intro j n1 n2
      split
      · exact Val.inject_long j _
      · exact Val.val_inject_undef j Vundef)

private def shrlBuiltin : builtin_sem Xlong :=
  mkbuiltin_num_v2tInternal Tlong Tint Xlong
    (fun n1 n2 =>
      if CompCert4Lean.Lib.Integers.Int.ltu n2 CompCert4Lean.Lib.Integers.Int64.iwordsize' then
        Vlong (CompCert4Lean.Lib.Integers.Int64.shr' n1 n2)
      else Vundef)
    (by intro n1 n2; split <;> trivial)
    (by
      intro j n1 n2
      split
      · exact Val.inject_long j _
      · exact Val.val_inject_undef j Vundef)

private def addlBuiltin : builtin_sem Xlong :=
  longBinaryTotal Val.addl
    (by
      intro v1 v2
      cases v1 <;> cases v2 <;>
        simp [Val.addl, Val.has_rettype, CompCert4Lean.X86_64.Archi.ptr64])
    (by
      intro j v1 v1' v2 v2' h1 h2
      exact Val.addl_inject j v1 v1' v2 v2' h1 h2)

private def sublBuiltin : builtin_sem Xlong :=
  longBinaryTotal Val.subl
    (by
      intro v1 v2
      cases v1 <;> cases v2
      case Vptr.Vptr =>
        simp only [Val.subl, CompCert4Lean.X86_64.Archi.ptr64]
        split
        · simp_all
        · split <;> trivial
      all_goals simp [Val.subl, Val.has_rettype, CompCert4Lean.X86_64.Archi.ptr64])
    (by
      intro j v1 v1' v2 v2' h1 h2
      exact Val.subl_inject j v1 v1' v2 v2' h1 h2)

private def normalizeWellTyped (t : typ) (v : val) :
    Val.has_rettype (Val.normalize v t) (inj_type t) := by
  cases t <;> cases v <;>
    simp [inj_type, Val.normalize, Val.has_rettype, CompCert4Lean.X86_64.Archi.ptr64]

private def normalizeInject (j : meminj) (t : typ) (v v' : val)
    (h : Val.inject j v v') :
    Val.inject j (Val.normalize v t) (Val.normalize v' t) := by
  cases h <;> cases t <;>
    simp [Val.normalize, CompCert4Lean.X86_64.Archi.ptr64]
  all_goals first
    | exact Val.inject_int j _
    | exact Val.inject_long j _
    | exact Val.inject_float j _
    | exact Val.inject_single j _
    | exact Val.val_inject_undef j _
    | apply Val.inject_ptr <;> assumption

private def selectBuiltin (t : typ) : builtin_sem (inj_type t) where
  bs_sem := fun vargs =>
    match vargs with
    | [Vint n, v1, v2] =>
        some (Val.normalize (if CompCert4Lean.Lib.Integers.Int.eq n intZero then v2 else v1) t)
    | _ => none
  bs_well_typed := by
    intro vargs
    cases vargs with
    | nil => trivial
    | cons v0 rest =>
      cases v0 <;> try trivial
      case Vint n =>
        cases rest with
        | nil => trivial
        | cons v1 rest =>
          cases rest with
          | nil => trivial
          | cons v2 rest =>
            cases rest with
            | cons _ _ => trivial
            | nil =>
              simp [val_opt_has_rettype]
              split
              · exact normalizeWellTyped t v2
              · exact normalizeWellTyped t v1
  bs_inject := by
    intro j vargs vargs' h
    rcases h with ⟨⟩ | ⟨_, _, _, _, h0, hs⟩
    · trivial
    · rcases h0 with ⟨n⟩ | ⟨_⟩ | ⟨_⟩ | ⟨_⟩ | ⟨_, _, _, _, _, _, _⟩ | ⟨_⟩
      · rcases hs with ⟨⟩ | ⟨_, _, _, _, h1, hs⟩
        · trivial
        · rcases hs with ⟨⟩ | ⟨_, _, _, _, h2, hs⟩
          · trivial
          · rcases hs with ⟨⟩ | ⟨_, _, _, _, _, _⟩
            · simp [val_opt_inject]
              split
              · exact normalizeInject j t _ _ h2
              · exact normalizeInject j t _ _ h1
            · trivial
      · trivial
      · trivial
      · trivial
      · trivial
      · trivial

private def unreachableBuiltin : builtin_sem Xvoid where
  bs_sem := fun _ => none
  bs_well_typed := by intro _; trivial
  bs_inject := by intro _ _ _ _; trivial

def standard_builtin_sem
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (b : standard_builtin) :
    builtin_sem (standard_builtin_sig b).sig_res :=
  match b with
  | BI_select t => selectBuiltin t
  | BI_fabs => mkbuiltin_n1t Tfloat Xfloat CompCert4Lean.Lib.Floats.Float.abs
  | BI_fabsf => mkbuiltin_n1t Tsingle Xsingle CompCert4Lean.Lib.Floats.Float32.abs
  | BI_fsqrt => mkbuiltin_n1t Tfloat Xfloat CompCert4Lean.Lib.Floats.Float.sqrt
  | BI_negl => mkbuiltin_n1t Tlong Xlong CompCert4Lean.Lib.Integers.Int64.neg
  | BI_addl => addlBuiltin
  | BI_subl => sublBuiltin
  | BI_mull =>
      mkbuiltin_v2t Xlong CompCert4Lean.Common.Values.Val.mull'
        (by
          intro v1 v2
          cases v1 <;> cases v2 <;>
            simp [CompCert4Lean.Common.Values.Val.mull', Val.has_rettype])
        (by
          intro j v1 v1' v2 v2' h1 h2
          cases h1 <;> cases h2 <;>
            simp only [CompCert4Lean.Common.Values.Val.mull']
          all_goals first
          | exact Val.inject_long j _
          | exact Val.val_inject_undef j _)
  | BI_i16_bswap => mkbuiltin_n1t Tint Xint16unsigned byteSwap16
  | BI_i32_bswap => mkbuiltin_n1t Tint Xint byteSwap32
  | BI_i64_bswap => mkbuiltin_n1t Tlong Xlong byteSwap64
  | BI_unreachable => unreachableBuiltin
  | BI_i64_umulh => mkbuiltin_n2t Tlong Tlong Xlong CompCert4Lean.Lib.Integers.Int64.mulhu
  | BI_i64_smulh => mkbuiltin_n2t Tlong Tlong Xlong CompCert4Lean.Lib.Integers.Int64.mulhs
  | BI_i64_sdiv => divlsBuiltin
  | BI_i64_udiv => divluBuiltin
  | BI_i64_smod => modlsBuiltin
  | BI_i64_umod => modluBuiltin
  | BI_i64_shl =>
      mkbuiltin_v2t Xlong CompCert4Lean.Common.Values.Val.shll
        (by
          intro v1 v2
          cases v1 <;> cases v2
          case Vlong.Vint n1 n2 =>
            by_cases h : Int.ltu n2 Int64.iwordsize' = true <;>
              simp [CompCert4Lean.Common.Values.Val.shll, Val.has_rettype, h]
          all_goals simp [CompCert4Lean.Common.Values.Val.shll, Val.has_rettype])
        (by
          intro j v1 v1' v2 v2' h1 h2
          cases h1 <;> cases h2 <;>
            simp only [CompCert4Lean.Common.Values.Val.shll]
          all_goals try split
          all_goals first
          | exact Val.inject_long j _
          | exact Val.val_inject_undef j _)
  | BI_i64_shr =>
      mkbuiltin_v2t Xlong CompCert4Lean.Common.Values.Val.shrlu
        (by
          intro v1 v2
          cases v1 <;> cases v2
          case Vlong.Vint n1 n2 =>
            by_cases h : Int.ltu n2 Int64.iwordsize' = true <;>
              simp [CompCert4Lean.Common.Values.Val.shrlu, Val.has_rettype, h]
          all_goals simp [CompCert4Lean.Common.Values.Val.shrlu, Val.has_rettype])
        (by
          intro j v1 v1' v2 v2' h1 h2
          cases h1 <;> cases h2 <;>
            simp only [CompCert4Lean.Common.Values.Val.shrlu]
          all_goals try split
          all_goals first
          | exact Val.inject_long j _
          | exact Val.val_inject_undef j _)
  | BI_i64_sar =>
      mkbuiltin_v2t Xlong CompCert4Lean.Common.Values.Val.shrl
        (by
          intro v1 v2
          cases v1 <;> cases v2
          case Vlong.Vint n1 n2 =>
            by_cases h : Int.ltu n2 Int64.iwordsize' = true <;>
              simp [CompCert4Lean.Common.Values.Val.shrl, Val.has_rettype, h]
          all_goals simp [CompCert4Lean.Common.Values.Val.shrl, Val.has_rettype])
        (by
          intro j v1 v1' v2 v2' h1 h2
          cases h1 <;> cases h2 <;>
            simp only [CompCert4Lean.Common.Values.Val.shrl]
          all_goals try split
          all_goals first
          | exact Val.inject_long j _
          | exact Val.val_inject_undef j _)
  | BI_i64_dtos => mkbuiltin_n1p Tfloat Xlong CompCert4Lean.Lib.Floats.Float.to_long
  | BI_i64_dtou => mkbuiltin_n1p Tfloat Xlong CompCert4Lean.Lib.Floats.Float.to_longu
  | BI_i64_stod => mkbuiltin_n1t Tlong Xfloat (fun n => CompCert4Lean.Lib.Floats.Float.of_long n)
  | BI_i64_utod => mkbuiltin_n1t Tlong Xfloat (fun n => CompCert4Lean.Lib.Floats.Float.of_longu n)
  | BI_i64_stof => mkbuiltin_n1t Tlong Xsingle (fun n => CompCert4Lean.Lib.Floats.Float32.of_long n)
  | BI_i64_utof => mkbuiltin_n1t Tlong Xsingle (fun n => CompCert4Lean.Lib.Floats.Float32.of_longu n)

end CompCert4Lean.Common.Builtins0

namespace CompCert4Lean.Common.Builtins0

theorem inj_num_wt : inj_num_wtStatement := by
  intro t x
  exact injNumWellTyped t x

theorem inj_num_inject : inj_num_injectStatement := by
  intro j t x
  exact injNumInject j t x

theorem inj_num_opt_wt : inj_num_opt_wtStatement := by
  intro t x
  cases x with
  | none => trivial
  | some x => exact injNumWellTyped t x

theorem inj_num_opt_inject : inj_num_opt_injectStatement := by
  intro j t x
  cases x with
  | none => trivial
  | some x => exact injNumInject j t x

end CompCert4Lean.Common.Builtins0
