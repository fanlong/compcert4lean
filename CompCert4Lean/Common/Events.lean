import CompCert4Lean.Common.Events.Core
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Lib.Coqlib

/-!
# Observable events and external calls

This is the public interface layer for CompCert's `common/Events.v`.  The
dependency-breaking event and external-call property core is imported from
`CompCert4Lean.Common.Events.Core`; the proof-bearing external-call providers
are imported from `CompCert4Lean.Common.ExternalCalls`.
-/

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Builtins0
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Lib.Integers

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev PtrofsT := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zOpp := ZArith.BinInt.Z.opp
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zDivide := ZArith.BinInt.Z.divide

/-! ## Finite and infinite traces -/

def E0_leftStatement : Prop :=
  ∀ t : trace, Eapp E0 t = t

def E0_rightStatement : Prop :=
  ∀ t : trace, Eapp t E0 = t

def Eapp_assocStatement : Prop :=
  ∀ t1 t2 t3 : trace, Eapp (Eapp t1 t2) t3 = Eapp t1 (Eapp t2 t3)

def Eapp_E0_invStatement : Prop :=
  ∀ t1 t2 : trace, Eapp t1 t2 = E0 → t1 = E0 ∧ t2 = E0

def E0_left_infStatement : Prop :=
  ∀ T : traceinf, Eappinf E0 T = T

def Eappinf_assocStatement : Prop :=
  ∀ t1 t2 : trace, ∀ T : traceinf,
    Eappinf (Eapp t1 t2) T = Eappinf t1 (Eappinf t2 T)

structure traceinf' : Type where
  chunk : Nat → trace
  nonempty : ∀ n, chunk n ≠ E0

namespace traceinf'

def cons (t : trace) (T : traceinf') (NE : t ≠ E0) : traceinf' where
  chunk
    | 0 => t
    | n + 1 => T.chunk n
  nonempty
    | 0 => NE
    | n + 1 => T.nonempty n

def headChunk (T : traceinf') : trace := T.chunk 0

def tailChunks (T : traceinf') : traceinf' where
  chunk n := T.chunk (n + 1)
  nonempty n := T.nonempty (n + 1)

end traceinf'

def Econsinf' (t : trace) (T : traceinf') (NE : t ≠ E0) : traceinf' :=
  traceinf'.cons t T NE

def split_traceinf' (t : trace) (T : traceinf') (NE : t ≠ E0) :
    event × traceinf' :=
  match t with
  | [] => False.elim (NE rfl)
  | e :: [] => (e, T)
  | e :: e' :: rest =>
      (e, Econsinf' (e' :: rest) T (by intro h; cases h))

private def traceinf'EventAt : traceinf' → Nat → event
  | T, 0 =>
      (split_traceinf' (traceinf'.headChunk T) (traceinf'.tailChunks T)
        (T.nonempty 0)).1
  | T, n + 1 =>
      traceinf'EventAt
        (split_traceinf' (traceinf'.headChunk T) (traceinf'.tailChunks T)
          (T.nonempty 0)).2 n

def traceinf_of_traceinf' (T : traceinf') : traceinf :=
  fun n => traceinf'EventAt T n

def unroll_traceinf'Statement : Prop :=
  ∀ T : traceinf',
    T = Econsinf' (traceinf'.headChunk T) (traceinf'.tailChunks T)
      (T.nonempty 0)

def unroll_traceinfStatement : Prop :=
  ∀ T : traceinf, T = Econsinf (T 0) (fun n => T (n + 1))

def traceinf_traceinf'_appStatement : Prop :=
  ∀ (t : trace) (T : traceinf') (NE : t ≠ E0),
    traceinf_of_traceinf' (Econsinf' t T NE) =
      Eappinf t (traceinf_of_traceinf' T)

def traceinf_prefix (t1 : trace) (T2 : traceinf) : Prop :=
  ∃ T3, T2 = Eappinf t1 T3

/-! ## Event-value statement surface -/

def eventval_match_typeStatement : Prop :=
  ∀ ge ev ty v, eventval_match ge ev ty v → Val.has_type v ty

def eventval_match_lessdefStatement : Prop :=
  ∀ ge ev ty v1 v2,
    eventval_match ge ev ty v1 →
    Val.lessdef v1 v2 →
    eventval_match ge ev ty v2

def eventval_list_match_lessdefStatement : Prop :=
  ∀ ge evl tyl vl1,
    eventval_list_match ge evl tyl vl1 →
    ∀ vl2, Val.lessdef_list vl1 vl2 → eventval_list_match ge evl tyl vl2

def eventval_match_determ_1Statement : Prop :=
  ∀ ge ev ty v1 v2,
    eventval_match ge ev ty v1 → eventval_match ge ev ty v2 → v1 = v2

def eventval_match_determ_2Statement : Prop :=
  ∀ ge ev1 ev2 ty v,
    eventval_match ge ev1 ty v → eventval_match ge ev2 ty v → ev1 = ev2

def eventval_list_match_determ_2Statement : Prop :=
  ∀ ge evl1 tyl vl,
    eventval_list_match ge evl1 tyl vl →
    ∀ evl2, eventval_list_match ge evl2 tyl vl → evl1 = evl2

def eventval_match_receptiveStatement : Prop :=
  ∀ ge ev1 ty v1 ev2,
    eventval_match ge ev1 ty v1 →
    eventval_valid ge ev1 →
    eventval_valid ge ev2 →
    eventval_type ev1 = eventval_type ev2 →
    ∃ v2, eventval_match ge ev2 ty v2

def eventval_match_validStatement : Prop :=
  ∀ ge ev ty v, eventval_match ge ev ty v → eventval_valid ge ev

def eventval_match_same_typeStatement : Prop :=
  ∀ ge ev1 ty v1 ev2 v2,
    eventval_match ge ev1 ty v1 →
    eventval_match ge ev2 ty v2 →
    eventval_type ev1 = eventval_type ev2

def eventval_valid_preservedStatement : Prop :=
  ∀ ge1 ge2,
    (∀ id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id) →
    ∀ ev, eventval_valid ge1 ev → eventval_valid ge2 ev

def eventval_match_preservedStatement : Prop :=
  ∀ ge1 ge2,
    (∀ id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id) →
    (∀ id, Senv.find_symbol ge2 id = Senv.find_symbol ge1 id) →
    ∀ ev ty v, eventval_match ge1 ev ty v → eventval_match ge2 ev ty v

def eventval_list_match_preservedStatement : Prop :=
  ∀ ge1 ge2,
    (∀ id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id) →
    (∀ id, Senv.find_symbol ge2 id = Senv.find_symbol ge1 id) →
    ∀ evl tyl vl,
      eventval_list_match ge1 evl tyl vl → eventval_list_match ge2 evl tyl vl

def eventval_match_injectStatement : Prop :=
  ∀ f ge1 ge2,
    symbols_inject f ge1 ge2 →
    ∀ ev ty v1 v2,
      eventval_match ge1 ev ty v1 →
      Val.inject f v1 v2 →
      eventval_match ge2 ev ty v2

def eventval_match_inject_2Statement : Prop :=
  ∀ f ge1 ge2,
    symbols_inject f ge1 ge2 →
    ∀ ev ty v1,
      eventval_match ge1 ev ty v1 →
      ∃ v2, eventval_match ge2 ev ty v2 ∧ Val.inject f v1 v2

def eventval_list_match_injectStatement : Prop :=
  ∀ f ge1 ge2,
    symbols_inject f ge1 ge2 →
    ∀ evl tyl vl1,
      eventval_list_match ge1 evl tyl vl1 →
      ∀ vl2, Val.inject_list f vl1 vl2 → eventval_list_match ge2 evl tyl vl2

def match_traces_preservedStatement : Prop :=
  ∀ ge1 ge2,
    (∀ id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id) →
    ∀ t1 t2, match_traces ge1 t1 t2 → match_traces ge2 t1 t2

def output_event (ev : event) : Prop :=
  match ev with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ _ => False
  | Event_vstore _ _ _ _ => True
  | Event_annot _ _ => True

def output_trace : trace → Prop
  | [] => True
  | ev :: t => output_event ev ∧ output_trace t

/-! ## Volatile memory accesses -/

inductive volatile_load (ge : Senv.t) :
    memory_chunk → mem → block → PtrofsT → trace → val → Prop where
  | volatile_load_vol (chunk : memory_chunk) (m : mem) (b : block)
      (ofs : PtrofsT) (id : ident) (ev : eventval) (v : val)
      (is_volatile : Senv.block_is_volatile ge b = true)
      (find_symbol : Senv.find_symbol ge id = some b)
      (eventval_matches : eventval_match ge ev (type_of_chunk chunk) v) :
      volatile_load ge chunk m b ofs [Event_vload chunk id ofs ev]
        (Val.load_result chunk v)
  | volatile_load_nonvol (chunk : memory_chunk) (m : mem) (b : block)
      (ofs : PtrofsT) (v : val)
      (not_volatile : Senv.block_is_volatile ge b = false)
      (load : Mem.load chunk m b (Ptrofs.unsigned ofs) = some v) :
      volatile_load ge chunk m b ofs E0 v

export volatile_load (volatile_load_vol volatile_load_nonvol)

inductive volatile_store (ge : Senv.t) :
    memory_chunk → mem → block → PtrofsT → val → trace → mem → Prop where
  | volatile_store_vol (chunk : memory_chunk) (m : mem) (b : block)
      (ofs : PtrofsT) (id : ident) (ev : eventval) (v : val)
      (is_volatile : Senv.block_is_volatile ge b = true)
      (find_symbol : Senv.find_symbol ge id = some b)
      (eventval_matches :
        eventval_match ge ev (type_of_chunk chunk) (Val.load_result chunk v)) :
      volatile_store ge chunk m b ofs v [Event_vstore chunk id ofs ev] m
  | volatile_store_nonvol (chunk : memory_chunk) (m : mem) (b : block)
      (ofs : PtrofsT) (v : val) (m' : mem)
      (not_volatile : Senv.block_is_volatile ge b = false)
      (store : Mem.store chunk m b (Ptrofs.unsigned ofs) v = some m') :
      volatile_store ge chunk m b ofs v E0 m'

export volatile_store (volatile_store_vol volatile_store_nonvol)

def loc_not_writable (m : mem) (b : block) (ofs : Z) : Prop :=
  ¬ Mem.perm m b ofs Max Writable

inductive volatile_load_sem (chunk : memory_chunk) (ge : Senv.t) :
    List val → mem → trace → val → mem → Prop where
  | volatile_load_sem_intro (b : block) (ofs : PtrofsT) (m : mem)
      (t : trace) (v : val)
      (load : volatile_load ge chunk m b ofs t v) :
      volatile_load_sem chunk ge [Vptr b ofs] m t v m

export volatile_load_sem (volatile_load_sem_intro)

def volatile_load_preservedStatement : Prop :=
  ∀ ge1 ge2 chunk m b ofs t v,
    Senv.equiv ge1 ge2 →
    volatile_load ge1 chunk m b ofs t v →
    volatile_load ge2 chunk m b ofs t v

def volatile_load_extendsStatement : Prop :=
  ∀ ge chunk m b ofs t v m',
    volatile_load ge chunk m b ofs t v →
    Mem.extends m m' →
    ∃ v', volatile_load ge chunk m' b ofs t v' ∧ Val.lessdef v v'

def volatile_load_injectStatement : Prop :=
  ∀ ge1 ge2 f chunk m b ofs t v b' ofs' m',
    symbols_inject f ge1 ge2 →
    volatile_load ge1 chunk m b ofs t v →
    Val.inject f (Vptr b ofs) (Vptr b' ofs') →
    Mem.inject f m m' →
    ∃ v', volatile_load ge2 chunk m' b' ofs' t v' ∧ Val.inject f v v'

def volatile_load_receptiveStatement : Prop :=
  ∀ ge chunk m b ofs t1 t2 v1,
    volatile_load ge chunk m b ofs t1 v1 →
    match_traces ge t1 t2 →
    ∃ v2, volatile_load ge chunk m b ofs t2 v2

def volatile_load_okStatement : Prop :=
  ∀ chunk,
    extcall_properties (volatile_load_sem chunk)
      { sig_args := [Xptr], sig_res := xtype_of_chunk chunk, sig_cc := cc_default }

inductive volatile_store_sem (chunk : memory_chunk) (ge : Senv.t) :
    List val → mem → trace → val → mem → Prop where
  | volatile_store_sem_intro (b : block) (ofs : PtrofsT) (m1 : mem)
      (v : val) (t : trace) (m2 : mem)
      (store : volatile_store ge chunk m1 b ofs v t m2) :
      volatile_store_sem chunk ge [Vptr b ofs, v] m1 t Vundef m2

export volatile_store_sem (volatile_store_sem_intro)

def volatile_store_preservedStatement : Prop :=
  ∀ ge1 ge2 chunk m1 b ofs v t m2,
    Senv.equiv ge1 ge2 →
    volatile_store ge1 chunk m1 b ofs v t m2 →
    volatile_store ge2 chunk m1 b ofs v t m2

def unchanged_on_readonlyStatement : Prop :=
  ∀ m1 m2 b ofs n bytes,
    Mem.unchanged_on (loc_not_writable m1) m1 m2 →
    Mem.valid_block m1 b →
    Mem.loadbytes m2 b ofs n = some bytes →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs n) → ¬ Mem.perm m1 b i Max Writable) →
    Mem.loadbytes m1 b ofs n = some bytes

def volatile_store_readonlyStatement : Prop :=
  ∀ ge chunk m1 b ofs v t m2,
    volatile_store ge chunk m1 b ofs v t m2 →
    Mem.unchanged_on (loc_not_writable m1) m1 m2

def volatile_store_extendsStatement : Prop :=
  ∀ ge chunk m1 b ofs v t m2 m1' v',
    volatile_store ge chunk m1 b ofs v t m2 →
    Mem.extends m1 m1' →
    Val.lessdef v v' →
    ∃ m2',
      volatile_store ge chunk m1' b ofs v' t m2' ∧
      Mem.extends m2 m2' ∧
      Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'

def volatile_store_injectStatement : Prop :=
  ∀ ge1 ge2 f chunk m1 b ofs v t m2 m1' b' ofs' v',
    symbols_inject f ge1 ge2 →
    volatile_store ge1 chunk m1 b ofs v t m2 →
    Val.inject f (Vptr b ofs) (Vptr b' ofs') →
    Val.inject f v v' →
    Mem.inject f m1 m1' →
    ∃ m2',
      volatile_store ge2 chunk m1' b' ofs' v' t m2' ∧
      Mem.inject f m2 m2' ∧
      Mem.unchanged_on (loc_unmapped f) m1 m2 ∧
      Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'

def volatile_store_receptiveStatement : Prop :=
  ∀ ge chunk m b ofs v t1 m1 t2,
    volatile_store ge chunk m b ofs v t1 m1 →
    match_traces ge t1 t2 →
    t1 = t2

def volatile_store_okStatement : Prop :=
  ∀ chunk,
    extcall_properties (volatile_store_sem chunk)
      { sig_args := [Xptr, xtype_of_chunk chunk], sig_res := Xvoid,
        sig_cc := cc_default }

/-! ## Concrete external-call relations -/

inductive extcall_malloc_sem (ge : Senv.t) :
    List val → mem → trace → val → mem → Prop where
  | extcall_malloc_sem_intro (sz : PtrofsT) (m m' : mem) (b : block) (m'' : mem)
      (alloc :
        Mem.alloc m (zOpp (size_chunk Mptr)) (Ptrofs.unsigned sz) = (m', b))
      (store :
        Mem.store Mptr m' b (zOpp (size_chunk Mptr)) (Vptrofs sz) = some m'') :
      extcall_malloc_sem ge [Vptrofs sz] m E0 (Vptr b Ptrofs.zero) m''

export extcall_malloc_sem (extcall_malloc_sem_intro)

def extcall_malloc_okStatement : Prop :=
  extcall_properties extcall_malloc_sem
    { sig_args := [Xsize_t], sig_res := Xptr, sig_cc := cc_default }

inductive extcall_free_sem (ge : Senv.t) :
    List val → mem → trace → val → mem → Prop where
  | extcall_free_sem_ptr (b : block) (lo sz : PtrofsT) (m m' : mem)
      (load :
        Mem.load Mptr m b (zSub (Ptrofs.unsigned lo) (size_chunk Mptr)) =
          some (Vptrofs sz))
      (free :
        Mem.free m b (zSub (Ptrofs.unsigned lo) (size_chunk Mptr))
          (zAdd (Ptrofs.unsigned lo) (Ptrofs.unsigned sz)) = some m') :
      extcall_free_sem ge [Vptr b lo] m E0 Vundef m'
  | extcall_free_sem_null (m : mem) :
      extcall_free_sem ge [Vnullptr] m E0 Vundef m

export extcall_free_sem (extcall_free_sem_ptr extcall_free_sem_null)

def extcall_free_okStatement : Prop :=
  extcall_properties extcall_free_sem
    { sig_args := [Xptr], sig_res := Xvoid, sig_cc := cc_default }

inductive extcall_memcpy_sem (sz al : Z) (ge : Senv.t) :
    List val → mem → trace → val → mem → Prop where
  | extcall_memcpy_sem_intro (bdst : block) (odst : PtrofsT) (bsrc : block)
      (osrc : PtrofsT) (m : mem) (bytes : List memval) (m' : mem)
      (alignment :
        al = z1 ∨ al = ZArith.BinInt.Z.of_nat 2 ∨
          al = ZArith.BinInt.Z.of_nat 4 ∨ al = ZArith.BinInt.Z.of_nat 8)
      (size_nonnegative : zLe z0 sz)
      (size_aligned : zDivide al sz)
      (source_aligned : zLt z0 sz → zDivide al (Ptrofs.unsigned osrc))
      (destination_aligned : zLt z0 sz → zDivide al (Ptrofs.unsigned odst))
      (nonoverlap :
        bsrc ≠ bdst ∨
          Ptrofs.unsigned osrc = Ptrofs.unsigned odst ∨
          zLe (zAdd (Ptrofs.unsigned osrc) sz) (Ptrofs.unsigned odst) ∨
          zLe (zAdd (Ptrofs.unsigned odst) sz) (Ptrofs.unsigned osrc))
      (loadbytes : Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz = some bytes)
      (storebytes : Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = some m') :
      extcall_memcpy_sem sz al ge [Vptr bdst odst, Vptr bsrc osrc] m E0 Vundef m'

export extcall_memcpy_sem (extcall_memcpy_sem_intro)

def extcall_memcpy_okStatement : Prop :=
  ∀ sz al,
    extcall_properties (extcall_memcpy_sem sz al)
      { sig_args := [Xptr, Xptr], sig_res := Xvoid, sig_cc := cc_default }

inductive extcall_annot_sem (text : RocqString) (targs : List typ) (ge : Senv.t) :
    List val → mem → trace → val → mem → Prop where
  | extcall_annot_sem_intro (vargs : List val) (m : mem) (args : List eventval)
      (eventval_matches : eventval_list_match ge args targs vargs) :
      extcall_annot_sem text targs ge vargs m [Event_annot text args] Vundef m

export extcall_annot_sem (extcall_annot_sem_intro)

def extcall_annot_okStatement : Prop :=
  ∀ text targs,
    extcall_properties (extcall_annot_sem text targs)
      { sig_args := List.map inj_type targs, sig_res := Xvoid, sig_cc := cc_default }

inductive extcall_annot_val_sem (text : RocqString) (targ : typ) (ge : Senv.t) :
    List val → mem → trace → val → mem → Prop where
  | extcall_annot_val_sem_intro (varg : val) (m : mem) (arg : eventval)
      (eventval_matches : eventval_match ge arg targ varg) :
      extcall_annot_val_sem text targ ge [varg] m [Event_annot text [arg]] varg m

export extcall_annot_val_sem (extcall_annot_val_sem_intro)

def extcall_annot_val_okStatement : Prop :=
  ∀ text targ,
    extcall_properties (extcall_annot_val_sem text targ)
      { sig_args := [inj_type targ], sig_res := inj_type targ, sig_cc := cc_default }

inductive extcall_debug_sem (ge : Senv.t) :
    List val → mem → trace → val → mem → Prop where
  | extcall_debug_sem_intro (vargs : List val) (m : mem) :
      extcall_debug_sem ge vargs m E0 Vundef m

export extcall_debug_sem (extcall_debug_sem_intro)

def extcall_debug_okStatement : Prop :=
  ∀ targs,
    extcall_properties extcall_debug_sem
      { sig_args := List.map inj_type targs, sig_res := Xvoid, sig_cc := cc_default }

inductive known_builtin_sem
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (bf : builtin_function) (ge : Senv.t) :
    List val → mem → trace → val → mem → Prop where
  | known_builtin_sem_intro (vargs : List val) (vres : val) (m : mem)
      (evaluation :
        builtin_function_sem
        (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) bf vargs = some vres) :
      known_builtin_sem
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) bf ge vargs m E0 vres m

export known_builtin_sem (known_builtin_sem_intro)

def known_builtin_sem_injectStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ bf ge vargs m1 t vres m2 f ge' vargs' m',
    known_builtin_sem
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) bf ge vargs m1 t vres m2 →
    Val.inject_list f vargs vargs' →
    ∃ vres',
      known_builtin_sem
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) bf ge' vargs' m' t vres' m' ∧
      Val.inject f vres vres'

def known_builtin_sem_lessdefStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ bf ge vargs m1 t vres m2 ge' vargs' m',
    known_builtin_sem
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) bf ge vargs m1 t vres m2 →
    Val.lessdef_list vargs vargs' →
    ∃ vres',
      known_builtin_sem
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) bf ge' vargs' m' t vres' m' ∧
      Val.lessdef vres vres'

def known_builtin_okStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ bf,
    extcall_properties
      (known_builtin_sem
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) bf)
      (builtin_function_sig bf)

/-! ## Explicit external-call environment adapters -/

def external_functions_sem (xi : ExternalCalls) (name : RocqString)
    (sg : signature) : extcall_sem :=
  xi.external.sem name sg

def external_functions_properties (xi : ExternalCalls) (name : RocqString)
    (sg : signature) : extcall_properties (external_functions_sem xi name sg) sg :=
  xi.external.properties name sg

def inline_assembly_sem (xi : ExternalCalls) (text : RocqString)
    (sg : signature) : extcall_sem :=
  xi.inlineAssembly.sem text sg

def inline_assembly_properties (xi : ExternalCalls) (text : RocqString)
    (sg : signature) : extcall_properties (inline_assembly_sem xi text sg) sg :=
  xi.inlineAssembly.properties text sg

def builtin_or_external_sem
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (name : RocqString) (sg : signature) : extcall_sem :=
  match lookup_builtin_function name sg with
  | some bf => known_builtin_sem
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) bf
  | none => external_functions_sem xi name sg

def builtin_or_external_sem_okStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ xi name sg,
    extcall_properties
      (builtin_or_external_sem
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi name sg) sg

def external_call
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) : external_function → extcall_sem
  | EF_external name sg => external_functions_sem xi name sg
  | EF_builtin name sg => builtin_or_external_sem
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi name sg
  | EF_runtime name sg => builtin_or_external_sem
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi name sg
  | EF_vload chunk => volatile_load_sem chunk
  | EF_vstore chunk => volatile_store_sem chunk
  | EF_malloc => extcall_malloc_sem
  | EF_free => extcall_free_sem
  | EF_memcpy sz al => extcall_memcpy_sem sz al
  | EF_annot _ text targs => extcall_annot_sem text targs
  | EF_annot_val _ text targ => extcall_annot_val_sem text targ
  | EF_inline_asm text sg _ => inline_assembly_sem xi text sg
  | EF_debug _ _ _ => extcall_debug_sem

def external_call_specStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ xi ef,
    extcall_properties
      (external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef)
      (ef_sig ef)

def external_call_well_typed_gen
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  ∀ ge vargs m1 t vres m2,
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m1 t vres m2 →
    Val.has_rettype vres (ef_sig ef).sig_res

def external_call_well_typed_genStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  external_call_well_typed_gen
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ef

def external_call_symbols_preserved
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  ∀ ge1 ge2 vargs m1 t vres m2,
    Senv.equiv ge1 ge2 →
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge1 vargs m1 t vres m2 →
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge2 vargs m1 t vres m2

def external_call_symbols_preservedStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  external_call_symbols_preserved
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ef

def external_call_valid_block
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  ∀ ge vargs m1 t vres m2 b,
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m1 t vres m2 →
    Mem.valid_block m1 b →
    Mem.valid_block m2 b

def external_call_valid_blockStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  external_call_valid_block
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ef

def external_call_max_perm
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  ∀ ge vargs m1 t vres m2 b ofs p,
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m1 t vres m2 →
    Mem.valid_block m1 b →
    Mem.perm m2 b ofs Max p →
    Mem.perm m1 b ofs Max p

def external_call_max_permStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  external_call_max_perm
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ef

def external_call_readonly
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  ∀ ge vargs m1 t vres m2 b ofs n bytes,
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m1 t vres m2 →
    Mem.valid_block m1 b →
    Mem.loadbytes m2 b ofs n = some bytes →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs n) → ¬ Mem.perm m1 b i Max Writable) →
    Mem.loadbytes m1 b ofs n = some bytes

def external_call_readonlyStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  external_call_readonly
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ef

def external_call_mem_extends
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  ∀ ge vargs m1 t vres m2 m1' vargs',
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m1 t vres m2 →
    Mem.extends m1 m1' →
    Val.lessdef_list vargs vargs' →
    ∃ vres' m2',
      external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ef ge vargs' m1' t vres' m2' ∧
      Val.lessdef vres vres' ∧
      Mem.extends m2 m2' ∧
      Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'

def external_call_mem_extendsStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  external_call_mem_extends
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ef

def external_call_mem_inject_gen
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  ∀ ge1 ge2 vargs m1 t vres m2 f m1' vargs',
    symbols_inject f ge1 ge2 →
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge1 vargs m1 t vres m2 →
    Mem.inject f m1 m1' →
    Val.inject_list f vargs vargs' →
    ∃ f' vres' m2',
      external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ef ge2 vargs' m1' t vres' m2' ∧
      Val.inject f' vres vres' ∧
      Mem.inject f' m2 m2' ∧
      Mem.unchanged_on (loc_unmapped f) m1 m2 ∧
      Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' ∧
      inject_incr f f' ∧
      inject_separated f f' m1 m1'

def external_call_mem_inject_genStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  external_call_mem_inject_gen
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ef

def external_call_trace_length
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  ∀ ge vargs m t vres m',
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m t vres m' →
      t.length ≤ 1

def external_call_trace_lengthStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  external_call_trace_length
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ef

def external_call_receptive
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  ∀ ge vargs m t1 vres1 m1 t2,
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m t1 vres1 m1 →
    match_traces ge t1 t2 →
    ∃ vres2 m2,
      external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m t2 vres2 m2

def external_call_receptiveStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  external_call_receptive
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ef

def external_call_determ
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  ∀ ge vargs m t1 vres1 m1 t2 vres2 m2,
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m t1 vres1 m1 →
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m t2 vres2 m2 →
    match_traces ge t1 t2 ∧ (t1 = t2 → vres1 = vres2 ∧ m1 = m2)

def external_call_determStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) : Prop :=
  external_call_determ
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ef

def external_call_well_typedStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ xi ef ge vargs m1 t vres m2,
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m1 t vres m2 →
    Val.has_type vres (proj_sig_res (ef_sig ef))

def external_call_nextblockStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ xi ef ge vargs m1 t vres m2,
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef ge vargs m1 t vres m2 →
    CompCert4Lean.Lib.Coqlib.Ple m1.nextblock m2.nextblock

def meminj_preserves_globals (F V : Type) (ge : Genv.t F V) (f : meminj) : Prop :=
  (∀ id b, Genv.find_symbol ge id = some b → f b = some (b, z0)) ∧
  (∀ b gv, Genv.find_var_info ge b = some gv → f b = some (b, z0)) ∧
  (∀ b1 b2 delta gv,
    Genv.find_var_info ge b2 = some gv →
    f b1 = some (b2, delta) →
    b2 = b1)

def external_call_mem_injectStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ xi ef F V (ge : Genv.t F V) vargs m1 t vres m2 f m1' vargs',
    meminj_preserves_globals F V ge f →
    external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ef (Genv.to_senv ge)
        vargs m1 t vres m2 →
    Mem.inject f m1 m1' →
    Val.inject_list f vargs vargs' →
    ∃ f' vres' m2',
      external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ef (Genv.to_senv ge)
          vargs' m1' t vres' m2' ∧
      Val.inject f' vres vres' ∧
      Mem.inject f' m2 m2' ∧
      Mem.unchanged_on (loc_unmapped f) m1 m2 ∧
      Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' ∧
      inject_incr f f' ∧
      inject_separated f f' m1 m1'

/-! ## Evaluation of builtin arguments -/

inductive eval_builtin_arg {A : Type} (ge : Senv.t) (e : A → val)
    (sp : val) (m : mem) : builtin_arg A → val → Prop where
  | eval_BA (x : A) :
      eval_builtin_arg ge e sp m (BA x) (e x)
  | eval_BA_int (n : CCInt) :
      eval_builtin_arg ge e sp m (BA_int n) (Vint n)
  | eval_BA_long (n : CCInt64) :
      eval_builtin_arg ge e sp m (BA_long n) (Vlong n)
  | eval_BA_float (n : CCFloat) :
      eval_builtin_arg ge e sp m (BA_float n) (Vfloat n)
  | eval_BA_single (n : CCFloat32) :
      eval_builtin_arg ge e sp m (BA_single n) (Vsingle n)
  | eval_BA_loadstack (chunk : memory_chunk) (ofs : PtrofsT) (v : val)
      (load : Mem.loadv chunk m (Val.offset_ptr sp ofs) = some v) :
      eval_builtin_arg ge e sp m (BA_loadstack chunk ofs) v
  | eval_BA_addrstack (ofs : PtrofsT) :
      eval_builtin_arg ge e sp m (BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal (chunk : memory_chunk) (id : ident) (ofs : PtrofsT) (v : val)
      (load : Mem.loadv chunk m (Senv.symbol_address ge id ofs) = some v) :
      eval_builtin_arg ge e sp m (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal (id : ident) (ofs : PtrofsT) :
      eval_builtin_arg ge e sp m (BA_addrglobal id ofs) (Senv.symbol_address ge id ofs)
  | eval_BA_splitlong (hi lo : builtin_arg A) (vhi vlo : val)
      (eval_hi : eval_builtin_arg ge e sp m hi vhi)
      (eval_lo : eval_builtin_arg ge e sp m lo vlo) :
      eval_builtin_arg ge e sp m (BA_splitlong hi lo) (Val.longofwords vhi vlo)
  | eval_BA_addptr (a1 a2 : builtin_arg A) (v1 v2 : val)
      (eval_a1 : eval_builtin_arg ge e sp m a1 v1)
      (eval_a2 : eval_builtin_arg ge e sp m a2 v2) :
      eval_builtin_arg ge e sp m (BA_addptr a1 a2)
        (if CompCert4Lean.X86_64.Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2)

export eval_builtin_arg
  (eval_BA eval_BA_int eval_BA_long eval_BA_float eval_BA_single
    eval_BA_loadstack eval_BA_addrstack eval_BA_loadglobal eval_BA_addrglobal
    eval_BA_splitlong eval_BA_addptr)

def eval_builtin_args {A : Type} (ge : Senv.t) (e : A → val)
    (sp : val) (m : mem) (al : List (builtin_arg A)) (vl : List val) : Prop :=
  CompCert4Lean.Lib.Coqlib.list_forall2 (eval_builtin_arg ge e sp m) al vl

def eval_builtin_arg_determStatement : Prop :=
  ∀ (A : Type) ge (e : A → val) sp m a v,
    eval_builtin_arg ge e sp m a v →
    ∀ v', eval_builtin_arg ge e sp m a v' → v' = v

def eval_builtin_args_determStatement : Prop :=
  ∀ (A : Type) ge (e : A → val) sp m al vl,
    eval_builtin_args ge e sp m al vl →
    ∀ vl', eval_builtin_args ge e sp m al vl' → vl' = vl

def builtin_arg_depends_on_memory {A : Type} : builtin_arg A → Bool
  | BA_loadstack _ _ | BA_loadglobal _ _ _ => true
  | BA_splitlong a1 a2 | BA_addptr a1 a2 =>
      builtin_arg_depends_on_memory a1 || builtin_arg_depends_on_memory a2
  | _ => false

def builtin_arg_depends_on_memory_correctStatement : Prop :=
  ∀ (A : Type) m' ge (e : A → val) sp m (ba : builtin_arg A) v,
    eval_builtin_arg ge e sp m ba v →
    builtin_arg_depends_on_memory ba = false →
    eval_builtin_arg ge e sp m' ba v

def builtin_args_depends_on_memory {A : Type} : List (builtin_arg A) → Bool
  | [] => false
  | ba :: rest =>
      builtin_arg_depends_on_memory ba || builtin_args_depends_on_memory rest

def builtin_args_depends_on_memory_correctStatement : Prop :=
  ∀ (A : Type) m' ge (e : A → val) sp m (bal : List (builtin_arg A)) vl,
    eval_builtin_args ge e sp m bal vl →
    builtin_args_depends_on_memory bal = false →
    eval_builtin_args ge e sp m' bal vl

def eval_builtin_arg_preservedStatement : Prop :=
  ∀ (A F1 V1 F2 V2 : Type)
    (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2)
    (e : A → val) sp m,
    (∀ id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) →
    ∀ a v,
      eval_builtin_arg (Genv.to_senv ge1) e sp m a v →
      eval_builtin_arg (Genv.to_senv ge2) e sp m a v

def eval_builtin_args_preservedStatement : Prop :=
  ∀ (A F1 V1 F2 V2 : Type)
    (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2)
    (e : A → val) sp m,
    (∀ id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) →
    ∀ al vl,
      eval_builtin_args (Genv.to_senv ge1) e sp m al vl →
      eval_builtin_args (Genv.to_senv ge2) e sp m al vl

def eval_builtin_arg_lessdefStatement : Prop :=
  ∀ (A : Type) ge (e1 e2 : A → val) sp m1 m2,
    (∀ x, Val.lessdef (e1 x) (e2 x)) →
    Mem.extends m1 m2 →
    ∀ a v1,
      eval_builtin_arg ge e1 sp m1 a v1 →
      ∃ v2, eval_builtin_arg ge e2 sp m2 a v2 ∧ Val.lessdef v1 v2

def eval_builtin_args_lessdefStatement : Prop :=
  ∀ (A : Type) ge (e1 e2 : A → val) sp m1 m2,
    (∀ x, Val.lessdef (e1 x) (e2 x)) →
    Mem.extends m1 m2 →
    ∀ al vl1,
      eval_builtin_args ge e1 sp m1 al vl1 →
      ∃ vl2, eval_builtin_args ge e2 sp m2 al vl2 ∧ Val.lessdef_list vl1 vl2

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem eventval_match_preserved : eventval_match_preservedStatement := by
  intro ge1 ge2 hp hs ev ty v h
  cases h with
  | ev_match_int => exact ev_match_int _
  | ev_match_long => exact ev_match_long _
  | ev_match_float => exact ev_match_float _
  | ev_match_single => exact ev_match_single _
  | ev_match_ptr id b ofs pub find =>
      exact ev_match_ptr id b ofs (by rw [hp]; exact pub) (by rw [hs]; exact find)

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem eventval_match_lessdef : eventval_match_lessdefStatement := by
  intro ge ev ty v1 v2 hmatch hld
  cases hmatch <;> cases hld <;> constructor <;> assumption

theorem eventval_match_determ_2 : eventval_match_determ_2Statement := by
  intro ge ev1 ev2 ty v h1 h2
  cases h1 <;> cases h2 <;> try rfl
  case ev_match_ptr.ev_match_ptr =>
    rename_i id1 b ofs1 pub1 find1 id2 pub2 find2
    have hid : id1 = id2 := ge.find_symbol_injective id1 id2 find1 find2
    subst_vars
    rfl

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

private abbrev eventZAdd :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
private abbrev eventZToNat :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
private abbrev eventZOfNat :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
private abbrev eventIntOfZ :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
private abbrev eventZOne :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z := .Zpos .xH

theorem unchanged_on_readonly : unchanged_on_readonlyStatement := by
  intro m1 m2 b ofs n bytes hunch hvalid hload2 hnot
  cases hd2 : CompCert4Lean.Common.Memory.Mem.range_perm_dec m2 b ofs
      (eventZAdd ofs n) CompCert4Lean.Common.Memtype.Cur
        CompCert4Lean.Common.Memtype.Readable with
  | right hn2 =>
      have hnone : CompCert4Lean.Common.Memory.Mem.loadbytes m2 b ofs n = none := by
        rw [CompCert4Lean.Common.Memory.Mem.loadbytes, hd2]
        rfl
      rw [hnone] at hload2
      cases hload2
  | left hr2 =>
    have hbytes : CompCert4Lean.Common.Memory.Mem.getN
          (eventZToNat n) ofs
          (CompCert4Lean.Lib.Maps.PMap.get b m2.mem_contents) = bytes := by
      rw [CompCert4Lean.Common.Memory.Mem.loadbytes, hd2] at hload2
      exact Option.some.inj hload2
    have hr1 : CompCert4Lean.Common.Memory.Mem.range_perm m1 b ofs
        (eventZAdd ofs n) CompCert4Lean.Common.Memtype.Cur
          CompCert4Lean.Common.Memtype.Readable := by
      intro i hi
      exact (hunch.unchanged_on_perm b i
          CompCert4Lean.Common.Memtype.Cur CompCert4Lean.Common.Memtype.Readable
          (hnot i hi) hvalid).mpr
        (hr2 i hi)
    have hgetN : ∀ (start k : Nat) (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z),
        p = eventZAdd ofs (eventZOfNat start) →
        start + k ≤ eventZToNat n →
        CompCert4Lean.Common.Memory.Mem.getN k
            p
            (CompCert4Lean.Lib.Maps.PMap.get b m1.mem_contents) =
          CompCert4Lean.Common.Memory.Mem.getN k
            p
            (CompCert4Lean.Lib.Maps.PMap.get b m2.mem_contents) := by
      intro start k p hp hsk
      induction k generalizing start p with
      | zero => rfl
      | succ k ih =>
          have hstart : start < eventZToNat n := by omega
          have hnnonneg : 0 ≤ eventIntOfZ n := by
            by_cases hn : 0 ≤ eventIntOfZ n
            · exact hn
            · have hnlt : ¬ 0 < eventIntOfZ n := by
                intro h
                exact hn (Int.le_of_lt h)
              have hnle : eventIntOfZ n ≤ 0 := Int.le_of_not_gt hnlt
              have hnzero : eventZToNat n = 0 := by
                change Int.toNat (eventIntOfZ n) = 0
                exact Int.toNat_of_nonpos hnle
              omega
          have hnpos : 0 < eventIntOfZ n := by
            have hcast : (Int.ofNat (eventZToNat n) : Int) = eventIntOfZ n := by
              change Int.ofNat (Int.toNat (eventIntOfZ n)) = eventIntOfZ n
              exact Int.toNat_of_nonneg hnnonneg
            have hnNat : 0 < eventZToNat n := by omega
            have hzpos : (0 : Int) < Int.ofNat (eventZToNat n) :=
              (Int.ofNat_lt).mpr hnNat
            rw [hcast] at hzpos
            exact hzpos
          have hstartZ : Int.toNat (Int.ofNat start) < Int.toNat (eventIntOfZ n) := by
            have h := hstart
            change Int.toNat (Int.ofNat start) < Int.toNat (eventIntOfZ n) at h
            exact h
          have hstartInt : (Int.ofNat start : Int) < eventIntOfZ n :=
            (Int.toNat_lt_toNat hnpos).mp hstartZ
          have hinterval : zLe ofs p ∧ zLt p (eventZAdd ofs n) := by
            rw [hp]
            constructor
            · change eventIntOfZ ofs ≤ eventIntOfZ
                (eventZAdd ofs (eventZOfNat start))
              have hadd : eventIntOfZ (eventZAdd ofs (eventZOfNat start)) =
                  eventIntOfZ ofs + Int.ofNat start := by
                simp only [eventZAdd,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                  eventZOfNat,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
              rw [hadd]
              have hstartNonneg : (0 : Int) ≤ Int.ofNat start := Int.natCast_nonneg _
              omega
            · change eventIntOfZ (eventZAdd ofs (eventZOfNat start)) <
                eventIntOfZ (eventZAdd ofs n)
              have hadd1 : eventIntOfZ (eventZAdd ofs (eventZOfNat start)) =
                  eventIntOfZ ofs + Int.ofNat start := by
                simp only [eventZAdd,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                  eventZOfNat,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
              have hadd2 : eventIntOfZ (eventZAdd ofs n) =
                  eventIntOfZ ofs + eventIntOfZ n := by
                simp only [eventZAdd,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
              rw [hadd1, hadd2]
              omega
          have hperm1 := hr1 p hinterval
          have hcont := hunch.unchanged_on_contents
            b p
            (hnot _ hinterval) hperm1
          have hpnext : eventZAdd p eventZOne =
              eventZAdd ofs (eventZOfNat (start + 1)) := by
            rw [hp]
            apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
            simp only [eventZAdd,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              eventZOfNat, eventZOne,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            change eventIntOfZ ofs + Int.ofNat start + (1 : Int) =
              eventIntOfZ ofs + Int.ofNat (start + 1)
            simp
            omega
          have htail := ih (start + 1) (eventZAdd p eventZOne) hpnext (by omega)
          simp only [CompCert4Lean.Common.Memory.Mem.getN]
          rw [hcont.symm]
          exact congrArg
            (fun tl => List.cons
              (CompCert4Lean.Lib.Maps.ZMap.get p
                (CompCert4Lean.Lib.Maps.PMap.get b m2.mem_contents)) tl) htail
    have hget :
        CompCert4Lean.Common.Memory.Mem.getN (eventZToNat n) ofs
            (CompCert4Lean.Lib.Maps.PMap.get b m1.mem_contents) =
          CompCert4Lean.Common.Memory.Mem.getN (eventZToNat n) ofs
            (CompCert4Lean.Lib.Maps.PMap.get b m2.mem_contents) := by
      have hp0 : ofs = eventZAdd ofs (eventZOfNat 0) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [eventZAdd, eventZOfNat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        simp
      exact hgetN 0 (eventZToNat n) ofs hp0 (by omega)
    cases hd1 : CompCert4Lean.Common.Memory.Mem.range_perm_dec m1 b ofs
        (eventZAdd ofs n) CompCert4Lean.Common.Memtype.Cur
          CompCert4Lean.Common.Memtype.Readable with
    | left hr1' =>
        rw [CompCert4Lean.Common.Memory.Mem.loadbytes, hd1]
        exact congrArg Option.some (hget.trans hbytes)
    | right hn1 =>
        exact False.elim (hn1 hr1)

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem eventval_match_receptive : eventval_match_receptiveStatement := by
  intro ge ev1 ty v1 ev2 hm hv1 hv2 hty
  cases hm with
  | ev_match_int i =>
      cases ev2 <;> simp [eventval_type, CompCert4Lean.Common.AST.Tptr,
        CompCert4Lean.X86_64.Archi.ptr64] at hty
      · exact ⟨CompCert4Lean.Common.Values.Vint _, ev_match_int _⟩
  | ev_match_long i =>
      cases ev2 <;> simp [eventval_type, CompCert4Lean.Common.AST.Tptr,
        CompCert4Lean.X86_64.Archi.ptr64] at hty
      · exact ⟨CompCert4Lean.Common.Values.Vlong _, ev_match_long _⟩
      · rcases ge.public_symbol_exists _ hv2 with ⟨b, hb⟩
        exact ⟨CompCert4Lean.Common.Values.Vptr b _, ev_match_ptr _ _ _ hv2 hb⟩
  | ev_match_float f =>
      cases ev2 <;> simp [eventval_type, CompCert4Lean.Common.AST.Tptr,
        CompCert4Lean.X86_64.Archi.ptr64] at hty
      · exact ⟨CompCert4Lean.Common.Values.Vfloat _, ev_match_float _⟩
  | ev_match_single f =>
      cases ev2 <;> simp [eventval_type, CompCert4Lean.Common.AST.Tptr,
        CompCert4Lean.X86_64.Archi.ptr64] at hty
      · exact ⟨CompCert4Lean.Common.Values.Vsingle _, ev_match_single _⟩
  | ev_match_ptr id b ofs pub find =>
      cases ev2 <;> simp [eventval_type, CompCert4Lean.Common.AST.Tptr,
        CompCert4Lean.X86_64.Archi.ptr64] at hty
      · exact ⟨CompCert4Lean.Common.Values.Vlong _, ev_match_long _⟩
      · rcases ge.public_symbol_exists _ hv2 with ⟨b', hb'⟩
        exact ⟨CompCert4Lean.Common.Values.Vptr b' _, ev_match_ptr _ _ _ hv2 hb'⟩

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem known_builtin_sem_inject
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)] :
    known_builtin_sem_injectStatement := by
  intro bf ge vargs m1 t vres m2 f ge' vargs' m' hsem hinj
  cases hsem with
  | known_builtin_sem_intro vargs vres evaluation =>
      obtain ⟨vres', evaluation', hinj'⟩ :=
        CompCert4Lean.Common.Builtins.builtin_function_sem_inject
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          bf vargs vres f vargs' evaluation hinj
      exact ⟨vres', known_builtin_sem_intro vargs' vres' m' evaluation', hinj'⟩

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem eventval_match_type : eventval_match_typeStatement := by
  intro ge ev ty v h
  cases h <;> unfold CompCert4Lean.Common.Values.Val.has_type <;>
    simp [CompCert4Lean.Common.AST.Tptr, CompCert4Lean.X86_64.Archi.ptr64]

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events
theorem eventval_match_determ_1 : eventval_match_determ_1Statement := by
  intro ge ev ty v1 v2 h1 h2
  cases h1 <;> cases h2 <;> simp_all
theorem eventval_match_valid : eventval_match_validStatement := by
  intro ge ev ty v h
  cases h <;> simp [eventval_valid] <;> assumption
theorem eventval_list_match_lessdef : eventval_list_match_lessdefStatement := by
  intro ge evl tyl vl1 hmatch
  induction hmatch with
  | evl_match_nil => intro vl2 h; cases h; exact evl_match_nil
  | evl_match_cons ev1 evl ty1 tyl v1 vl1 hm ht ih =>
      intro vl2 hld
      cases hld with
      | lessdef_list_cons _ v2 _ vl2 hh htld =>
          exact evl_match_cons _ _ _ _ _ _ (by cases hm <;> cases hh <;> constructor <;> assumption) (ih vl2 htld)
end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem eventval_list_match_determ_2 : eventval_list_match_determ_2Statement := by
  intro ge evl1 tyl vl h1
  induction h1 with
  | evl_match_nil =>
      intro evl2 h2
      cases h2
      rfl
  | evl_match_cons ev1 evl ty1 tyl v1 vl hm ht ih =>
      intro evl2 h2
      cases h2 with
      | evl_match_cons ev2 evl2 ty2 tyl2 v2 vl2 hm2 ht2 =>
          have hev : ev1 = ev2 := eventval_match_determ_2 ge ev1 ev2 ty1 v1 hm hm2
          have htail : evl = evl2 := ih evl2 ht2
          cases hev
          cases htail
          rfl

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem eventval_match_same_type : eventval_match_same_typeStatement := by
  intro ge ev1 ty v1 ev2 v2 h1 h2
  cases h1 <;> cases h2 <;> rfl

theorem eventval_list_match_preserved : eventval_list_match_preservedStatement := by
  intro ge1 ge2 hp hs evl tyl vl h
  induction h with
  | evl_match_nil => exact evl_match_nil
  | evl_match_cons ev1 evl ty1 tyl v1 vl hm ht ih =>
      exact evl_match_cons _ _ _ _ _ _
        (eventval_match_preserved ge1 ge2 hp hs ev1 ty1 v1 hm) ih

theorem volatile_load_preserved : volatile_load_preservedStatement := by
  intro ge1 ge2 chunk m b ofs t v heq hload
  cases hload with
  | volatile_load_vol id ev v hvol hfind hmatch =>
      apply volatile_load_vol
      · rw [heq.2.2 b]
        exact hvol
      · rw [heq.1 id]
        exact hfind
      · exact eventval_match_preserved ge1 ge2 heq.2.1 heq.1 ev (CompCert4Lean.Common.AST.type_of_chunk chunk) v hmatch
  | volatile_load_nonvol v hnot hload =>
      apply volatile_load_nonvol
      · rw [heq.2.2 b]
        exact hnot
      · exact hload

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem volatile_load_receptive : volatile_load_receptiveStatement := by
  intro ge chunk m b ofs t1 t2 v1 hload htr
  cases hload with
  | volatile_load_vol id ev v hvol hfind hmatch =>
      cases htr with
      | match_traces_vload chunk id ofs ev1 ev2 hv1 hv2 hty =>
          obtain ⟨v', hm'⟩ :=
            eventval_match_receptive ge ev (CompCert4Lean.Common.AST.type_of_chunk chunk)
              v ev2 hmatch hv1 hv2 hty
          refine ⟨CompCert4Lean.Common.Values.Val.load_result chunk v', ?_⟩
          apply volatile_load_vol
          · exact hvol
          · exact hfind
          · exact hm'
  | volatile_load_nonvol v hnot hload =>
      cases htr
      refine ⟨v1, ?_⟩
      apply volatile_load_nonvol
      · exact hnot
      · exact hload

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem volatile_store_preserved : volatile_store_preservedStatement := by
  intro ge1 ge2 chunk m1 b ofs v t m2 heq hstore
  cases hstore with
  | volatile_store_vol id ev v hvol hfind hmatch =>
      apply volatile_store_vol
      · rw [heq.2.2 b]
        exact hvol
      · rw [heq.1 id]
        exact hfind
      · exact eventval_match_preserved ge1 ge2 heq.2.1 heq.1 ev
          (CompCert4Lean.Common.AST.type_of_chunk chunk)
          (CompCert4Lean.Common.Values.Val.load_result chunk v) hmatch
  | volatile_store_nonvol =>
      rename_i hnot hstore
      apply volatile_store_nonvol
      · rw [heq.2.2 b]
        exact hnot
      · exact hstore

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem volatile_store_pmap_same {A : Type}
    (i : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) (x : A)
    (m : PMap.t A) : PMap.get i (PMap.set i x m) = x := by
  change (match PTree.get i (PTree.set i x m.2) with
    | some y => y
    | none => m.1) = x
  rw [PTree.gsspec_proof]
  cases h : CompCert4Lean.Lib.Coqlib.peq i i with
  | left _ => simp [h]
  | right hn => exact False.elim (hn rfl)

private theorem volatile_store_pmap_other {A : Type}
    (i j : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) (x : A)
    (m : PMap.t A) (hij : i ≠ j) :
    PMap.get i (PMap.set j x m) = PMap.get i m := by
  change (match PTree.get i (PTree.set j x m.2) with
    | some y => y
    | none => m.1) =
    (match PTree.get i m.2 with
    | some y => y
    | none => m.1)
  rw [PTree.gsspec_proof]
  cases h : CompCert4Lean.Lib.Coqlib.peq i j with
  | left heq => exact False.elim (hij heq)
  | right _ => simp [h]

theorem volatile_store_readonly : volatile_store_readonlyStatement := by
  intro ge chunk m1 b ofs v t m2 hstore
  cases hstore with
  | volatile_store_vol id ev v hvol hfind hmatch =>
      exact {
        unchanged_on_nextblock := CompCert4Lean.Lib.Coqlib.Ple_refl _
        unchanged_on_perm := by
          intro b ofs k p _ _
          rfl
        unchanged_on_contents := by
          intro b ofs _ _
          rfl }
  | volatile_store_nonvol =>
      rename_i hnot hstore
      unfold CompCert4Lean.Common.Memory.Mem.store at hstore
      cases hdec : CompCert4Lean.Common.Memory.Mem.valid_access_dec m1 chunk b
          (Ptrofs.unsigned ofs) Writable with
      | left hvalid =>
        simp [hdec] at hstore
        have hm2 := hstore.2
        subst m2
        let contents := CompCert4Lean.Common.Memory.Mem.setN (Memdata.encode_val chunk v)
          (Ptrofs.unsigned ofs) (PMap.get b m1.mem_contents)
        refine {
          unchanged_on_nextblock := CompCert4Lean.Lib.Coqlib.Ple_refl _
          unchanged_on_perm := by
            intro b' ofs' k p _ _
            rfl
          unchanged_on_contents := by
            intro b' ofs' hP hReadable
            by_cases hbb : b' = b
            · subst b'
              change ZMap.get ofs'
                (PMap.get b (PMap.set b contents m1.mem_contents)) =
                ZMap.get ofs' (PMap.get b m1.mem_contents)
              have hbget :
                  PMap.get b (PMap.set b contents m1.mem_contents) = contents :=
                volatile_store_pmap_same b contents m1.mem_contents
              rw [hbget]
              apply CompCert4Lean.Common.Memory.Mem.setN_other
              intro i hi hEq
              subst i
              have hi' := hi
              rw [Memdata.encode_val_length chunk v] at hi'
              have hi'' :
                  zLe (Ptrofs.unsigned ofs) ofs' ∧
                    zLt ofs'
                      (zAdd (Ptrofs.unsigned ofs) (Memdata.size_chunk chunk)) := by
                cases chunk <;>
                  simpa [Memdata.size_chunk, Memdata.size_chunk_nat] using hi'
              exact hP (CompCert4Lean.Common.Memory.Mem.perm_cur_max m1 b ofs'
                Writable (hvalid.1 _ hi''))
            · have hbget : PMap.get b' (PMap.set b contents m1.mem_contents) =
                  PMap.get b' m1.mem_contents :=
                volatile_store_pmap_other b' b contents m1.mem_contents hbb
              rw [hbget] }
      | right hinvalid =>
        simp [hdec] at hstore
        have hbad := hstore.1
        have hfalse : (false : Bool) = true := by
          change (false : Bool) = true at hbad
          exact hbad
        cases hfalse

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem volatile_store_receptive : volatile_store_receptiveStatement := by
  intro ge chunk m b ofs v t1 m1 t2 hstore hmatch
  cases hstore with
  | volatile_store_vol id ev v hvol hfind hmatch' =>
      cases hmatch with
      | match_traces_vstore => rfl
  | volatile_store_nonvol v hnot hstore' =>
      cases hmatch
      rfl

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers

private theorem extcall_debug_unchanged_on_refl (P : block → Z → Prop) (m : mem) :
    Mem.unchanged_on P m m := by
  exact {
    unchanged_on_nextblock := CompCert4Lean.Lib.Coqlib.Ple_refl _
    unchanged_on_perm := by
      intro b ofs k p _ _
      rfl
    unchanged_on_contents := by
      intro b ofs _ _
      rfl }

theorem extcall_debug_ok : extcall_debug_okStatement := by
  intro targs
  refine {
    ec_well_typed := ?_
    ec_symbols_preserved := ?_
    ec_valid_block := ?_
    ec_max_perm := ?_
    ec_readonly := ?_
    ec_mem_extends := ?_
    ec_mem_inject := ?_
    ec_trace_length := ?_
    ec_receptive := ?_
    ec_determ := ?_ }
  · intro ge vargs m1 t vres m2 hsem
    cases hsem
    simp [Val.has_rettype]
  · intro ge1 ge2 vargs m1 t vres m2 _ hsem
    cases hsem
    exact extcall_debug_sem_intro _ _
  · intro ge vargs m1 t vres m2 b hsem hb
    cases hsem
    exact hb
  · intro ge vargs m1 t vres m2 b ofs p hsem hb hp
    cases hsem
    exact hp
  · intro ge vargs m1 t vres m2 b ofs n bytes hsem hb hload hreadonly
    cases hsem
    exact hload
  · intro ge vargs m1 t vres m2 m1' vargs' hsem hext hless
    cases hsem
    refine ⟨.Vundef, m1', extcall_debug_sem_intro _ _, .lessdef_refl _, hext, ?_⟩
    exact extcall_debug_unchanged_on_refl (loc_out_of_bounds m1) m1'
  · intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hsymbols hsem hinj hvlist
    cases hsem
    refine ⟨f, .Vundef, m1', extcall_debug_sem_intro _ _, .val_inject_undef _, hinj, ?_, ?_, ?_, ?_⟩
    · exact extcall_debug_unchanged_on_refl (loc_unmapped f) m1
    · exact extcall_debug_unchanged_on_refl (loc_out_of_reach f m1) m1'
    · intro b b' delta h
      exact h
    · intro b1 b2 delta hnone hsome
      rw [hnone] at hsome
      cases hsome
  · intro ge vargs m t vres m' hsem
    cases hsem
    simp [E0]
  · intro ge vargs m t1 vres1 m1 t2 hsem hmatch
    cases hsem
    cases hmatch
    exact ⟨.Vundef, m, extcall_debug_sem_intro _ _⟩
  · intro ge vargs m t1 vres1 m1 t2 vres2 m2 hsem1 hsem2
    cases hsem1
    cases hsem2
    exact ⟨match_traces_E0, by intro; exact ⟨rfl, rfl⟩⟩

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem unroll_traceinf : unroll_traceinfStatement := by
  intro T
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem eventval_valid_preserved : eventval_valid_preservedStatement := by
  intro ge1 ge2 hp ev hev
  cases ev with
  | EVint i => simp [eventval_valid]
  | EVlong i => simp [eventval_valid]
  | EVfloat f => simp [eventval_valid]
  | EVsingle f => simp [eventval_valid]
  | EVptr_global id ofs =>
      simp only [eventval_valid] at hev ⊢
      rw [hp id]
      exact hev

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem eval_builtin_arg_determ : eval_builtin_arg_determStatement := by
  intro A ge e sp m a v h
  induction h with
  | eval_BA x =>
      intro v' h'; cases h'; rfl
  | eval_BA_int n =>
      intro v' h'; cases h'; rfl
  | eval_BA_long n =>
      intro v' h'; cases h'; rfl
  | eval_BA_float n =>
      intro v' h'; cases h'; rfl
  | eval_BA_single n =>
      intro v' h'; cases h'; rfl
  | eval_BA_loadstack chunk ofs v load =>
      intro v' h'
      cases h' with
      | eval_BA_loadstack _ _ _ load' =>
          exact Option.some.inj (load'.symm.trans load)
  | eval_BA_addrstack ofs =>
      intro v' h'; cases h'; rfl
  | eval_BA_loadglobal chunk id ofs v load =>
      intro v' h'
      cases h' with
      | eval_BA_loadglobal _ _ _ _ load' =>
          exact Option.some.inj (load'.symm.trans load)
  | eval_BA_addrglobal id ofs =>
      intro v' h'; cases h'; rfl
  | @eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      intro v' h'
      cases h' with
      | eval_BA_splitlong _ _ _ _ hhi' hlo' =>
          have h1 := ihhi _ hhi'
          have h2 := ihlo _ hlo'
          rw [h1, h2]

  | @eval_BA_addptr a1 a2 v1 v2 ha1 ha2 iha1 iha2 =>
      intro v' h'
      cases h' with
      | eval_BA_addptr _ _ _ _ ha1' ha2' =>
          have h1 := iha1 _ ha1'
          have h2 := iha2 _ ha2'
          rw [h1, h2]

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem E0_left : E0_leftStatement := by
  intro t
  rfl

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem builtin_arg_depends_on_memory_correct : builtin_arg_depends_on_memory_correctStatement := by
  intro A m' ge e sp m ba v hev
  induction hev with
  | eval_BA x => intro _; exact eval_BA x
  | eval_BA_int n => intro _; exact eval_BA_int n
  | eval_BA_long n => intro _; exact eval_BA_long n
  | eval_BA_float n => intro _; exact eval_BA_float n
  | eval_BA_single n => intro _; exact eval_BA_single n
  | eval_BA_loadstack chunk ofs v load =>
      intro hdep
      simp only [builtin_arg_depends_on_memory] at hdep
      cases hdep
  | eval_BA_addrstack ofs => intro _; exact eval_BA_addrstack ofs
  | eval_BA_loadglobal chunk id ofs v load =>
      intro hdep
      simp only [builtin_arg_depends_on_memory] at hdep
      cases hdep
  | eval_BA_addrglobal id ofs => intro _; exact eval_BA_addrglobal id ofs
  | @eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      intro hdep
      simp only [builtin_arg_depends_on_memory] at hdep
      have h1dep : builtin_arg_depends_on_memory hi = false := by
        cases hhi : builtin_arg_depends_on_memory hi <;>
          cases hlo : builtin_arg_depends_on_memory lo <;>
            simp [hhi, hlo] at hdep ⊢
      have h2dep : builtin_arg_depends_on_memory lo = false := by
        cases hhi : builtin_arg_depends_on_memory hi <;>
          cases hlo : builtin_arg_depends_on_memory lo <;>
            simp [hhi, hlo] at hdep ⊢
      have h1 := ihhi h1dep
      have h2 := ihlo h2dep
      exact eval_BA_splitlong _ _ _ _ h1 h2
  | @eval_BA_addptr a1 a2 v1 v2 ha1 ha2 iha1 iha2 =>
      intro hdep
      simp only [builtin_arg_depends_on_memory] at hdep
      have h1dep : builtin_arg_depends_on_memory a1 = false := by
        cases h1' : builtin_arg_depends_on_memory a1 <;>
          cases h2' : builtin_arg_depends_on_memory a2 <;>
            simp [h1', h2'] at hdep ⊢
      have h2dep : builtin_arg_depends_on_memory a2 = false := by
        cases h1' : builtin_arg_depends_on_memory a1 <;>
          cases h2' : builtin_arg_depends_on_memory a2 <;>
            simp [h1', h2'] at hdep ⊢
      have h1 := iha1 h1dep
      have h2 := iha2 h2dep
      exact eval_BA_addptr _ _ _ _ h1 h2

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem eval_builtin_arg_preserved : eval_builtin_arg_preservedStatement := by
  intro A F1 V1 F2 V2 ge1 ge2 e sp m hsymbols a v hev
  have haddr : ∀ id ofs,
      CompCert4Lean.Common.Globalenvs.Senv.symbol_address (CompCert4Lean.Common.Globalenvs.Genv.to_senv ge2) id ofs =
        CompCert4Lean.Common.Globalenvs.Senv.symbol_address (CompCert4Lean.Common.Globalenvs.Genv.to_senv ge1) id ofs := by
    intro id ofs
    simp only [CompCert4Lean.Common.Globalenvs.Senv.symbol_address, CompCert4Lean.Common.Globalenvs.Genv.to_senv]
    rw [hsymbols]
  induction hev with
  | eval_BA x => exact eval_BA x
  | eval_BA_int n => exact eval_BA_int n
  | eval_BA_long n => exact eval_BA_long n
  | eval_BA_float n => exact eval_BA_float n
  | eval_BA_single n => exact eval_BA_single n
  | eval_BA_loadstack chunk ofs v load =>
      exact eval_BA_loadstack chunk ofs v load
  | eval_BA_addrstack ofs => exact eval_BA_addrstack ofs
  | eval_BA_loadglobal chunk id ofs v load =>
      rw [← haddr id ofs] at load
      exact eval_BA_loadglobal chunk id ofs v load
  | eval_BA_addrglobal id ofs =>
      rw [← haddr id ofs]
      exact eval_BA_addrglobal id ofs
  | @eval_BA_splitlong hi lo vhi vlo hhi hlo ihi ilo =>
      exact eval_BA_splitlong hi lo vhi vlo ihi ilo
  | @eval_BA_addptr a1 a2 v1 v2 ha1 ha2 iha1 iha2 =>
      exact eval_BA_addptr a1 a2 v1 v2 iha1 iha2

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem E0_right : E0_rightStatement := by
  intro t
  induction t with
  | nil => rfl
  | cons e t ih =>
      change e :: Eapp t E0 = e :: t
      rw [ih]

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem Eapp_assoc : Eapp_assocStatement := by
  intro t1 t2 t3
  induction t1 with
  | nil => rfl
  | cons e t ih =>
      change e :: Eapp (Eapp t t2) t3 = e :: Eapp t (Eapp t2 t3)
      rw [ih]

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem Eapp_E0_inv : Eapp_E0_invStatement := by
  intro t1 t2 h
  change List.append t1 t2 = [] at h
  exact List.eq_nil_of_append_eq_nil h

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem E0_left_inf : E0_left_infStatement := by
  intro T
  rfl

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem Eappinf_assoc : Eappinf_assocStatement := by
  intro t1 t2 T
  induction t1 with
  | nil => rfl
  | cons e t1 ih =>
      exact congrArg (Econsinf e) ih

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem unroll_traceinf' : unroll_traceinf'Statement := by
  intro T
  cases T with
  | mk chunk nonempty =>
      apply (traceinf'.mk.injEq chunk nonempty _ _).mpr
      funext n
      cases n <;> rfl

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem traceinf_traceinf'_app : traceinf_traceinf'_appStatement := by
  intro t T NE
  funext n
  induction t generalizing n with
  | nil => exact False.elim (NE rfl)
  | cons e t ih =>
      cases t with
      | nil =>
          cases n with
          | zero => rfl
          | succ n => rfl
      | cons e' t =>
          cases n with
          | zero => rfl
          | succ n =>
              exact ih (by intro h; cases h) n

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem match_traces_preserved : match_traces_preservedStatement := by
  intro ge1 ge2 hp t1 t2 h
  induction h with
  | match_traces_E0 => exact match_traces_E0
  | match_traces_syscall id args res1 res2 valid1 valid2 same_type =>
      exact match_traces_syscall id args res1 res2
        (eventval_valid_preserved ge1 ge2 hp res1 valid1)
        (eventval_valid_preserved ge1 ge2 hp res2 valid2) same_type
  | match_traces_vload chunk id ofs res1 res2 valid1 valid2 same_type =>
      exact match_traces_vload chunk id ofs res1 res2
        (eventval_valid_preserved ge1 ge2 hp res1 valid1)
        (eventval_valid_preserved ge1 ge2 hp res2 valid2) same_type
  | match_traces_vstore chunk id ofs arg =>
      exact match_traces_vstore chunk id ofs arg
  | match_traces_annot id args =>
      exact match_traces_annot id args

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

theorem eval_builtin_args_determ : eval_builtin_args_determStatement := by
  intro A ge e sp m al vl h
  intro vl' h'
  induction h generalizing vl' with
  | nil =>
      cases h'
      rfl
  | cons a1 b1 hp ht ih =>
      cases h' with
      | cons _ b1' hp' ht' =>
          have hb : b1' = b1 := eval_builtin_arg_determ A ge e sp m a1 b1 hp b1' hp'
          have ht_eq : _ := ih _ ht'
          cases hb
          cases ht_eq
          rfl

theorem builtin_args_depends_on_memory_correct :
    builtin_args_depends_on_memory_correctStatement := by
  intro A m' ge e sp m bal vl hEval hDep
  unfold eval_builtin_args at hEval ⊢
  induction bal generalizing vl with
  | nil =>
      cases hEval
      exact CompCert4Lean.Lib.Coqlib.list_forall2.nil _
  | cons ba bal ih =>
      cases hEval with
      | cons _ _ hba hrest =>
          simp only [builtin_args_depends_on_memory] at hDep
          have hbaDep : builtin_arg_depends_on_memory ba = false := by
            cases h1 : builtin_arg_depends_on_memory ba <;>
              cases h2 : builtin_args_depends_on_memory bal <;>
                simp [h1, h2] at hDep ⊢
          have hrestDep : builtin_args_depends_on_memory bal = false := by
            cases h1 : builtin_arg_depends_on_memory ba <;>
              cases h2 : builtin_args_depends_on_memory bal <;>
                simp [h1, h2] at hDep ⊢
          exact CompCert4Lean.Lib.Coqlib.list_forall2.cons ba _
            (builtin_arg_depends_on_memory_correct A m' ge e sp m ba _ hba hbaDep)
            (ih _ hrest hrestDep)

theorem eval_builtin_args_preserved : eval_builtin_args_preservedStatement := by
  intro A F1 V1 F2 V2 ge1 ge2 e sp m hsymbols al vl hEval
  unfold eval_builtin_args at hEval ⊢
  induction al generalizing vl with
  | nil =>
      cases hEval
      exact CompCert4Lean.Lib.Coqlib.list_forall2.nil _
  | cons ba al ih =>
      cases hEval with
      | cons _ _ hba hrest =>
          exact CompCert4Lean.Lib.Coqlib.list_forall2.cons ba _
            (eval_builtin_arg_preserved A F1 V1 F2 V2 ge1 ge2 e sp m hsymbols ba _ hba)
            (ih _ hrest)

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private def eventsIntegersPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem events_ptrofs_add_zero (ofs : Ptrofs.int) :
    Ptrofs.add ofs (Ptrofs.repr (.Z0 : Z)) = ofs := by
  change WordCore.add ofs (WordCore.zero Ptrofs.wordsize) = ofs
  apply WordCore.ext_of_val_eq
  have hadd : (WordCore.add ofs (WordCore.zero Ptrofs.wordsize)).val =
      (ofs.val + (WordCore.zero Ptrofs.wordsize).val) % (2 ^ Ptrofs.wordsize) := by
    run_tac
      let lctx ← getLCtx
      let ofsF := (lctx.findFromUserName? `ofs).get!
      let zF := mkConst ``CompCert4Lean.Lib.Integers.Ptrofs.wordsize
      let z0F := mkApp (mkConst ``CompCert4Lean.Lib.Integers.WordCore.zero) zF
      let e ← mkAppM (eventsIntegersPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
        #[mkFVar ofsF.fvarId, z0F]
      closeMainGoal Name.anonymous e
  rw [hadd]
  simp [WordCore.zero]
  have hlt : ofs.val < 2 ^ Ptrofs.wordsize := by
    run_tac
      let lctx ← getLCtx
      let ofsF := (lctx.findFromUserName? `ofs).get!
      let e ← mkAppM (eventsIntegersPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt")
        #[mkFVar ofsF.fvarId]
      closeMainGoal Name.anonymous e
  exact Nat.mod_eq_of_lt hlt

theorem eventval_match_inject : eventval_match_injectStatement := by
  intro f ge1 ge2 hsymbols ev ty v1 v2 hmatch hinj
  cases hmatch with
  | ev_match_int i =>
      cases hinj
      exact ev_match_int _
  | ev_match_long i =>
      cases hinj
      exact ev_match_long _
  | ev_match_float x =>
      cases hinj
      exact ev_match_float _
  | ev_match_single x =>
      cases hinj
      exact ev_match_single _
  | ev_match_ptr id b ofs hpub hfind =>
      cases hinj with
      | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
          have hpub' : Senv.public_symbol ge2 id = true := by
            rw [hsymbols.1 id]
            exact hpub
          obtain ⟨b3, hmap3, hfind3⟩ := hsymbols.2.2.1 id b hpub hfind
          have hpair : (b2, delta) = (b3, .Z0) :=
            Option.some.inj (hmap.symm.trans hmap3)
          have hb : b2 = b3 := congrArg Prod.fst hpair
          have hdelta : delta = (.Z0 : Z) := congrArg Prod.snd hpair
          subst b3
          rw [hdelta] at hofs
          subst delta
          rw [events_ptrofs_add_zero ofs] at hofs
          subst ofs2
          exact ev_match_ptr id b2 ofs hpub' hfind3

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs

theorem eventval_match_inject_2 : eventval_match_inject_2Statement := by
  intro f ge1 ge2 hsymbols ev ty v1 hmatch
  cases hmatch with
  | ev_match_int i =>
      exact ⟨Vint i, ev_match_int i, Val.inject.inject_int i⟩
  | ev_match_long i =>
      exact ⟨Vlong i, ev_match_long i, Val.inject.inject_long i⟩
  | ev_match_float x =>
      exact ⟨Vfloat x, ev_match_float x, Val.inject.inject_float x⟩
  | ev_match_single x =>
      exact ⟨Vsingle x, ev_match_single x, Val.inject.inject_single x⟩
  | ev_match_ptr id b ofs hpub hfind =>
      obtain ⟨b2, hmap, hfind2⟩ := hsymbols.2.2.1 id b hpub hfind
      have hpub2 : Senv.public_symbol ge2 id = true := by
        rw [hsymbols.1 id]
        exact hpub
      refine ⟨Vptr b2 ofs, ev_match_ptr id b2 ofs hpub2 hfind2, ?_⟩
      exact Val.inject.inject_ptr b ofs b2 ofs .Z0 hmap
        (events_ptrofs_add_zero ofs).symm

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Values

theorem known_builtin_sem_lessdef
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    known_builtin_sem_lessdefStatement := by
  intro bf ge vargs m1 t vres m2 ge' vargs' m' hsem hless
  cases hsem with
  | known_builtin_sem_intro vargs vres heval =>
      obtain ⟨vres', heval', hres⟩ :=
        builtin_function_sem_lessdef bf vargs vres vargs' heval hless
      exact ⟨vres', known_builtin_sem_intro vargs' vres' m' heval', hres⟩

theorem eventval_list_match_inject : eventval_list_match_injectStatement := by
  intro f ge1 ge2 hsymbols evl tyl vl1 hmatch
  induction hmatch with
  | evl_match_nil =>
      intro vl2 hinj
      cases hinj
      exact evl_match_nil
  | evl_match_cons ev evl ty tyl v vl hhead htail ih =>
      intro vl2 hinj
      cases hinj with
      | inject_list_cons v v' vl vl' hhead' htail' =>
          exact evl_match_cons ev evl ty tyl v' vl'
            (eventval_match_inject f ge1 ge2 hsymbols ev ty v v' hhead hhead')
            (ih vl' htail')

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private theorem events_unsigned_repr_bounded (z : Z)
    (hz : zLe z0 z ∧ zLe z Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.repr z) = z := by
  have heq : Ptrofs.unsigned (Ptrofs.repr z) =
      ZArith.BinInt.Z.modulo z Ptrofs.modulus := by
    run_tac
      let lctx ← getLCtx
      let zF := (lctx.findFromUserName? `z).get!
      let e ← mkAppM
        (eventsIntegersPrivateName
          "CompCert4Lean.Lib.Integers.Int64.suffix_int64_unsigned_repr_eq_exact")
        #[mkFVar zF.fvarId]
      closeMainGoal Name.anonymous e
  rw [heq]
  apply ZArith.BinInt.Z.mod_small
  refine ⟨hz.1, ?_⟩
  have h := hz.2
  change intOfZ z ≤ 18446744073709551615 at h
  change intOfZ z < 18446744073709551616
  omega

private theorem events_address_inject
    (f : Val.meminj) (m m' : mem) (b b' : block) (ofs : Ptrofs.int)
    (delta : Z) (p : permission)
    (hinj : Mem.inject f m m')
    (hperm : Mem.perm m b (Ptrofs.unsigned ofs) Cur p)
    (hmap : f b = some (b', delta)) :
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) =
      zAdd (Ptrofs.unsigned ofs) delta := by
  have hnonempty := Mem.perm_cur_max m b (Ptrofs.unsigned ofs) Nonempty
    (Mem.perm_implies m b (Ptrofs.unsigned ofs) Cur p Nonempty hperm (perm_any_N p))
  obtain ⟨hdelta, hsum⟩ := hinj.mi_representable b b' delta ofs hmap (Or.inl hnonempty)
  have hu : 0 ≤ intOfZ (Ptrofs.unsigned ofs) := by
    have h := ofs.intrange.1
    change (-1 : _root_.Int) < intOfZ (Ptrofs.unsigned ofs) at h
    omega
  have hdmax : zLe delta Ptrofs.max_unsigned := by
    have h := hsum.2
    change intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) delta) ≤
      intOfZ Ptrofs.max_unsigned at h
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at h
    change intOfZ delta ≤ intOfZ Ptrofs.max_unsigned
    omega
  change Ptrofs.unsigned (Ptrofs.repr
    (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))) = _
  rw [events_unsigned_repr_bounded delta ⟨hdelta, hdmax⟩]
  exact events_unsigned_repr_bounded _ hsum

private theorem events_valid_access_perm (m : mem) (chunk : memory_chunk)
    (b : block) (ofs : Z) (p : permission)
    (hvalid : Mem.valid_access m chunk b ofs p) : Mem.perm m b ofs Cur p := by
  apply hvalid.1 ofs
  constructor
  · exact _root_.Int.le_refl _
  · have hsize := size_chunk_pos chunk
    change 0 < intOfZ (size_chunk chunk) at hsize
    change intOfZ ofs < intOfZ (ZArith.BinInt.Z.add ofs (size_chunk chunk))
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
    omega

theorem volatile_load_inject : volatile_load_injectStatement := by
  intro ge1 ge2 f chunk m b ofs t v b' ofs' m' hsymbols hload hptr hmem
  cases hload with
  | volatile_load_vol id ev v hvol hfind hmatch =>
      cases hptr with
      | inject_ptr b ofs b' ofs' delta hmap heq =>
          obtain ⟨hzero, hfind'⟩ := hsymbols.2.1 id b b' delta hmap hfind
          subst delta
          rw [events_ptrofs_add_zero] at heq
          subst ofs'
          obtain ⟨v', hmatch', hval⟩ :=
            eventval_match_inject_2 f ge1 ge2 hsymbols ev (type_of_chunk chunk) v hmatch
          refine ⟨Val.load_result chunk v', ?_, Val.load_result_inject f chunk v v' hval⟩
          apply volatile_load_vol chunk m' b' ofs id ev v' _ hfind' hmatch'
          rw [hsymbols.2.2.2 b b' .Z0 hmap]
          exact hvol
  | volatile_load_nonvol v hvol hload =>
      cases hptr with
      | inject_ptr b ofs b' ofs' delta hmap heq =>
          obtain ⟨v', hload', hval⟩ := Mem.load_inj f m m' chunk b
            (Ptrofs.unsigned ofs) b' delta v hmem.mi_inj hload hmap
          have haddr := events_address_inject f m m' b b' ofs delta Readable hmem
            (events_valid_access_perm m chunk b (Ptrofs.unsigned ofs) Readable
              (Mem.load_valid_access m chunk b (Ptrofs.unsigned ofs) v hload)) hmap
          change Mem.load chunk m' b' (zAdd (Ptrofs.unsigned ofs) delta) = some v' at hload'
          rw [← haddr, ← heq] at hload'
          refine ⟨v', volatile_load_nonvol chunk m' b' ofs' v' ?_ hload', hval⟩
          rw [hsymbols.2.2.2 b b' delta hmap]
          exact hvol

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

private theorem events_store_injection_transport
    (f : Val.meminj) (chunk : memory_chunk)
    (m1 m2 n1 n2 : mem) (b1 b2 : block) (ofs1 ofs2 : Z) (v1 v2 : val)
    (hinj : Mem.inject f m1 m2)
    (hstore1 : Mem.store chunk m1 b1 ofs1 v1 = some n1)
    (hstore2 : Mem.store chunk m2 b2 ofs2 v2 = some n2)
    (hmem : Mem.mem_inj f n1 n2) : Mem.inject f n1 n2 := by
  have hp1 := Mem.perm_store_1 chunk m1 b1 ofs1 v1 n1 hstore1
  have hp2 := Mem.perm_store_2 chunk m1 b1 ofs1 v1 n1 hstore1
  have hq2 := Mem.perm_store_2 chunk m2 b2 ofs2 v2 n2 hstore2
  constructor
  · exact hmem
  · intro b hb
    apply hinj.mi_freeblocks b
    intro hv
    exact hb (Mem.store_valid_block_1 chunk m1 b1 ofs1 v1 n1 hstore1 b hv)
  · intro b b' delta hmap
    exact Mem.store_valid_block_1 chunk m2 b2 ofs2 v2 n2 hstore2 b'
      (hinj.mi_mappedblocks b b' delta hmap)
  · intro b b' delta c c' delta' ofs ofs' hne hmap hmap' hp hq
    exact hinj.mi_no_overlap b b' delta c c' delta' ofs ofs' hne hmap hmap'
      (hp2 b ofs Max Nonempty hp) (hp2 c ofs' Max Nonempty hq)
  · intro b b' delta ofs hmap hp
    apply hinj.mi_representable b b' delta ofs hmap
    exact hp.elim (fun h => Or.inl (hp2 _ _ _ _ h))
      (fun h => Or.inr (hp2 _ _ _ _ h))
  · intro b ofs b' delta k p hmap hp
    obtain hp | hn := hinj.mi_perm_inv b ofs b' delta k p hmap (hq2 _ _ _ _ hp)
    · exact Or.inl (hp1 _ _ _ _ hp)
    · exact Or.inr (fun h => hn (hp2 _ _ _ _ h))

private theorem events_store_unchanged
    (P : block → Z → Prop) (chunk : memory_chunk) (m : mem)
    (b : block) (ofs : Z) (v : val) (m' : mem)
    (hstore : Mem.store chunk m b ofs v = some m')
    (hout : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) → ¬ P b i) :
    Mem.unchanged_on P m m' := by
  constructor
  · rw [Mem.nextblock_store chunk m b ofs v m' hstore]
    exact Ple_refl _
  · intro b' ofs' k p _ _
    exact ⟨Mem.perm_store_1 chunk m b ofs v m' hstore b' ofs' k p,
      Mem.perm_store_2 chunk m b ofs v m' hstore b' ofs' k p⟩
  · intro b' ofs' hP _
    rw [Mem.store_mem_contents chunk m b ofs v m' hstore]
    by_cases hb : b' = b
    · subst b'
      erw [PMap.gss]
      apply Mem.setN_other
      intro r hr heq
      subst r
      apply hout ofs' _ hP
      have hsize : ZArith.BinInt.Z.of_nat (encode_val chunk v).length =
          size_chunk chunk := by
        rw [encode_val_length]
        exact (size_chunk_conv chunk).symm
      change zLe ofs ofs' ∧ zLt ofs'
        (zAdd ofs (ZArith.BinInt.Z.of_nat (encode_val chunk v).length)) at hr
      rw [hsize] at hr
      exact hr
    · erw [PMap.gso _ _ hb]

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers

theorem volatile_store_inject : volatile_store_injectStatement := by
  intro ge1 ge2 f chunk m1 b ofs v t m2 m1' b' ofs' v'
    hsymbols hstore hptr hval hmem
  cases hstore with
  | volatile_store_vol id ev v hvol hfind hmatch =>
      cases hptr with
      | inject_ptr b ofs b' ofs' delta hmap heq =>
          obtain ⟨hzero, hfind'⟩ := hsymbols.2.1 id b b' delta hmap hfind
          subst delta
          rw [events_ptrofs_add_zero] at heq
          subst ofs'
          refine ⟨m1', ?_, hmem, extcall_debug_unchanged_on_refl _ _,
            extcall_debug_unchanged_on_refl _ _⟩
          refine volatile_store_vol chunk m1' b' ofs id ev v' ?_ hfind' ?_
          · rw [hsymbols.2.2.2 b b' .Z0 hmap]
            exact hvol
          · exact eventval_match_inject f ge1 ge2 hsymbols ev (type_of_chunk chunk)
              (Val.load_result chunk v) (Val.load_result chunk v') hmatch
              (Val.load_result_inject f chunk v v' hval)
  | volatile_store_nonvol v m2 hvol hstore =>
      cases hptr with
      | inject_ptr b ofs b' ofs' delta hmap heq =>
          obtain ⟨m2', hstore', hmem'⟩ := Mem.store_mapped_inj f chunk m1 b
            (Ptrofs.unsigned ofs) v m2 m1' b' delta v' hmem.mi_inj hstore
            hmem.mi_no_overlap hmap hval
          change Mem.store chunk m1' b' (zAdd (Ptrofs.unsigned ofs) delta) v' =
            some m2' at hstore'
          have hvalid := Mem.store_valid_access_3 chunk m1 b (Ptrofs.unsigned ofs)
            v m2 hstore
          have haddr := events_address_inject f m1 m1' b b' ofs delta Writable hmem
            (events_valid_access_perm m1 chunk b (Ptrofs.unsigned ofs) Writable hvalid) hmap
          have hfull := events_store_injection_transport f chunk m1 m1' m2 m2' b b'
            (Ptrofs.unsigned ofs) (zAdd (Ptrofs.unsigned ofs) delta) v v'
            hmem hstore hstore' hmem'
          refine ⟨m2', ?_, hfull, ?_, ?_⟩
          · apply volatile_store_nonvol chunk m1' b' ofs' v' m2'
            · rw [hsymbols.2.2.2 b b' delta hmap]
              exact hvol
            · rw [heq, haddr]
              exact hstore'
          · apply events_store_unchanged _ chunk m1 b (Ptrofs.unsigned ofs) v m2 hstore
            intro i _ hunmapped
            change f b = none at hunmapped
            rw [hmap] at hunmapped
            cases hunmapped
          · apply events_store_unchanged _ chunk m1' b'
              (zAdd (Ptrofs.unsigned ofs) delta) v' m2' hstore'
            intro i hi hout
            apply hout b delta hmap
            apply Mem.perm_cur_max m1 b (zSub i delta) Nonempty
            apply Mem.perm_implies m1 b (zSub i delta) Cur Writable Nonempty
              _ (perm_any_N Writable)
            apply hvalid.1 (zSub i delta)
            change intOfZ (zAdd (Ptrofs.unsigned ofs) delta) ≤ intOfZ i ∧
              intOfZ i < intOfZ (zAdd (zAdd (Ptrofs.unsigned ofs) delta)
                (size_chunk chunk)) at hi
            change intOfZ (Ptrofs.unsigned ofs) ≤ intOfZ (zSub i delta) ∧
              intOfZ (zSub i delta) < intOfZ (zAdd (Ptrofs.unsigned ofs)
                (size_chunk chunk))
            simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
              intOfZ_zOfInt] at hi ⊢
            omega

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers

theorem volatile_load_extends : volatile_load_extendsStatement := by
  intro ge chunk m b ofs t v m' hload hext
  cases hload with
  | volatile_load_vol id ev v hvol hfind hmatch =>
      exact ⟨Val.load_result chunk v,
        volatile_load_vol chunk m' b ofs id ev v hvol hfind hmatch,
        Val.lessdef_refl _⟩
  | volatile_load_nonvol v hvol hload =>
      obtain ⟨v', hload', hless⟩ :=
        Mem.load_extends chunk m m' b (Ptrofs.unsigned ofs) v hext hload
      exact ⟨v', volatile_load_nonvol chunk m' b ofs v' hvol hload', hless⟩

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Integers

theorem volatile_store_extends : volatile_store_extendsStatement := by
  intro ge chunk m1 b ofs v t m2 m1' v' hstore hext hless
  cases hstore with
  | volatile_store_vol id ev v hvol hfind hmatch =>
      refine ⟨m1', ?_, hext, extcall_debug_unchanged_on_refl _ _⟩
      exact volatile_store_vol chunk m1' b ofs id ev v' hvol hfind
        (eventval_match_lessdef ge ev (type_of_chunk chunk)
          (Val.load_result chunk v) (Val.load_result chunk v') hmatch
          (Val.load_result_lessdef chunk v v' hless))
  | volatile_store_nonvol v m2 hvol hstore =>
      have hno : Mem.meminj_no_overlap inject_id m1 := by
        intro b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne hmap1 hmap2 _ _
        have hpair1 : (b1, (.Z0 : Z)) = (b1', delta1) := Option.some.inj hmap1
        have hpair2 : (b2, (.Z0 : Z)) = (b2', delta2) := Option.some.inj hmap2
        cases hpair1
        cases hpair2
        exact Or.inl hne
      obtain ⟨m2', hstore', hinj⟩ := Mem.store_mapped_inj inject_id chunk m1 b
        (Ptrofs.unsigned ofs) v m2 m1' b (.Z0 : Z) v' hext.mext_inj hstore hno
        rfl ((val_inject_id v v').mpr hless)
      have hzadd : zAdd (Ptrofs.unsigned ofs) (.Z0 : Z) = Ptrofs.unsigned ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ (Ptrofs.unsigned ofs) + 0)) = _
        rw [intOfZ_zOfInt]
        simp
      change Mem.store chunk m1' b (zAdd (Ptrofs.unsigned ofs) (.Z0 : Z)) v' =
        some m2' at hstore'
      rw [hzadd] at hstore'
      refine ⟨m2', volatile_store_nonvol chunk m1' b ofs v' m2' hvol hstore', ?_, ?_⟩
      · constructor
        · rw [Mem.nextblock_store chunk m1 b (Ptrofs.unsigned ofs) v m2 hstore,
            Mem.nextblock_store chunk m1' b (Ptrofs.unsigned ofs) v' m2' hstore']
          exact hext.mext_next
        · exact hinj
        · intro b' ofs' k p hp
          have hp' := Mem.perm_store_2 chunk m1' b (Ptrofs.unsigned ofs) v' m2'
            hstore' b' ofs' k p hp
          obtain hpold | hn := hext.mext_perm_inv b' ofs' k p hp'
          · exact Or.inl (Mem.perm_store_1 chunk m1 b (Ptrofs.unsigned ofs) v m2
              hstore b' ofs' k p hpold)
          · exact Or.inr (fun hpnew => hn (Mem.perm_store_2 chunk m1 b
              (Ptrofs.unsigned ofs) v m2 hstore b' ofs' Max Nonempty hpnew))
      · apply events_store_unchanged _ chunk m1' b (Ptrofs.unsigned ofs) v' m2' hstore'
        intro i hi hout
        apply hout
        apply Mem.perm_cur_max m1 b i Nonempty
        apply Mem.perm_implies m1 b i Cur Writable Nonempty _ (perm_any_N Writable)
        exact (Mem.store_valid_access_3 chunk m1 b (Ptrofs.unsigned ofs) v m2
          hstore).1 i hi

end CompCert4Lean.Common.Events
namespace CompCert4Lean.Common.Events

theorem extcall_annot_ok : extcall_annot_okStatement := by
  intro text targs
  refine {
    ec_well_typed := ?_
    ec_symbols_preserved := ?_
    ec_valid_block := ?_
    ec_max_perm := ?_
    ec_readonly := ?_
    ec_mem_extends := ?_
    ec_mem_inject := ?_
    ec_trace_length := ?_
    ec_receptive := ?_
    ec_determ := ?_ }
  · intro ge vargs m1 t vres m2 hsem
    cases hsem
    simp [CompCert4Lean.Common.Values.Val.has_rettype]
  · intro ge1 ge2 vargs m1 t vres m2 heq hsem
    cases hsem with
    | extcall_annot_sem_intro args hmatch =>
        apply extcall_annot_sem_intro
        exact eventval_list_match_preserved ge1 ge2 heq.2.1 heq.1 args targs vargs hmatch
  · intro ge vargs m1 t vres m2 b hsem hb
    cases hsem
    exact hb
  · intro ge vargs m1 t vres m2 b ofs p hsem hb hp
    cases hsem
    exact hp
  · intro ge vargs m1 t vres m2 b ofs n bytes hsem hb hload hreadonly
    cases hsem
    exact hload
  · intro ge vargs m1 t vres m2 m1' vargs' hsem hext hless
    cases hsem with
    | extcall_annot_sem_intro args hmatch =>
      refine ⟨.Vundef, m1', ?_, .lessdef_refl _, hext, ?_⟩
      · apply extcall_annot_sem_intro
        exact eventval_list_match_lessdef ge args targs vargs hmatch vargs' hless
      · exact extcall_debug_unchanged_on_refl (loc_out_of_bounds m1) m1'
  · intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hsymbols hsem hinj hvlist
    cases hsem with
    | extcall_annot_sem_intro args hmatch =>
      refine ⟨f, .Vundef, m1', ?_, .val_inject_undef _, hinj, ?_, ?_, ?_, ?_⟩
      · apply extcall_annot_sem_intro
        exact eventval_list_match_inject f ge1 ge2 hsymbols args targs vargs hmatch vargs' hvlist
      · exact extcall_debug_unchanged_on_refl (loc_unmapped f) m1
      · exact extcall_debug_unchanged_on_refl (loc_out_of_reach f m1) m1'
      · intro b b' delta h
        exact h
      · intro b1 b2 delta hnone hsome
        rw [hnone] at hsome
        cases hsome
  · intro ge vargs m t vres m' hsem
    cases hsem
    simp [E0]
  · intro ge vargs m t1 vres1 m1 t2 hsem hmatch
    cases hsem with
    | extcall_annot_sem_intro args hmatch' =>
      cases hmatch
      exact ⟨.Vundef, m, extcall_annot_sem_intro vargs m args hmatch'⟩
  · intro ge vargs m t1 vres1 m1 t2 vres2 m2 hsem1 hsem2
    cases hsem1 with
    | extcall_annot_sem_intro args1 hmatch1 =>
      cases hsem2 with
      | extcall_annot_sem_intro args2 hmatch2 =>
        have hargs := eventval_list_match_determ_2 ge args1 targs vargs hmatch1 args2 hmatch2
        subst args2
        exact ⟨match_traces_annot _ _, by intro; exact ⟨rfl, rfl⟩⟩

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Builtins0
open CompCert4Lean.Common.Values

theorem known_builtin_ok
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    known_builtin_okStatement := by
  intro bf
  refine {
    ec_well_typed := ?_
    ec_symbols_preserved := ?_
    ec_valid_block := ?_
    ec_max_perm := ?_
    ec_readonly := ?_
    ec_mem_extends := ?_
    ec_mem_inject := ?_
    ec_trace_length := ?_
    ec_receptive := ?_
    ec_determ := ?_ }
  · intro ge vargs m1 t vres m2 hsem
    cases hsem with
    | known_builtin_sem_intro vargs vres evaluation =>
        have ht := (builtin_function_sem bf).bs_well_typed vargs
        change val_opt_has_rettype (builtin_function_sem bf vargs)
          (builtin_function_sig bf).sig_res at ht
        rw [evaluation] at ht
        exact ht
  · intro ge1 ge2 vargs m1 t vres m2 _ hsem
    cases hsem with
    | known_builtin_sem_intro vargs vres evaluation =>
        exact known_builtin_sem_intro vargs vres m1 evaluation
  · intro ge vargs m1 t vres m2 b hsem hb
    cases hsem
    exact hb
  · intro ge vargs m1 t vres m2 b ofs p hsem hb hp
    cases hsem
    exact hp
  · intro ge vargs m1 t vres m2 b ofs n bytes hsem hb hload hreadonly
    cases hsem
    exact hload
  · intro ge vargs m1 t vres m2 m1' vargs' hsem hext hless
    cases hsem with
    | known_builtin_sem_intro vargs vres evaluation =>
        obtain ⟨vres', evaluation', hres⟩ :=
          builtin_function_sem_lessdef bf vargs vres vargs' evaluation hless
        exact ⟨vres', m1', known_builtin_sem_intro vargs' vres' m1' evaluation',
          hres, hext, extcall_debug_unchanged_on_refl (loc_out_of_bounds m1) m1'⟩
  · intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hsymbols hsem hinj hvlist
    cases hsem with
    | known_builtin_sem_intro vargs vres evaluation =>
        obtain ⟨vres', evaluation', hres⟩ :=
          builtin_function_sem_inject bf vargs vres f vargs' evaluation hvlist
        refine ⟨f, vres', m1', known_builtin_sem_intro vargs' vres' m1' evaluation',
          hres, hinj, ?_, ?_, ?_, ?_⟩
        · exact extcall_debug_unchanged_on_refl (loc_unmapped f) m1
        · exact extcall_debug_unchanged_on_refl (loc_out_of_reach f m1) m1'
        · intro b b' delta h
          exact h
        · intro b1 b2 delta hnone hsome
          rw [hnone] at hsome
          cases hsome
  · intro ge vargs m t vres m' hsem
    cases hsem
    simp [E0]
  · intro ge vargs m t1 vres1 m1 t2 hsem hmatch
    cases hsem with
    | known_builtin_sem_intro vargs vres evaluation =>
        cases hmatch
        exact ⟨vres1, m, known_builtin_sem_intro vargs vres1 m evaluation⟩
  · intro ge vargs m t1 vres1 m1 t2 vres2 m2 hsem1 hsem2
    cases hsem1 with
    | known_builtin_sem_intro vargs vres1 evaluation1 =>
      cases hsem2 with
      | known_builtin_sem_intro vargs vres2 evaluation2 =>
        have hv : vres1 = vres2 := Option.some.inj (evaluation1.symm.trans evaluation2)
        subst vres2
        exact ⟨match_traces_E0, by intro; exact ⟨rfl, rfl⟩⟩

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers

theorem volatile_load_ok : volatile_load_okStatement := by
  intro chunk
  refine {
    ec_well_typed := ?_
    ec_symbols_preserved := ?_
    ec_valid_block := ?_
    ec_max_perm := ?_
    ec_readonly := ?_
    ec_mem_extends := ?_
    ec_mem_inject := ?_
    ec_trace_length := ?_
    ec_receptive := ?_
    ec_determ := ?_ }
  · intro ge vargs m1 t vres m2 hsem
    cases hsem with
    | volatile_load_sem_intro b ofs _ _ _ hload =>
        cases hload with
        | volatile_load_vol id ev _ hvol hfind hmatch =>
            exact Val.load_result_xtype chunk _
        | volatile_load_nonvol _ hnot hload =>
            exact Mem.load_xtype m1 chunk b (Ptrofs.unsigned ofs) _ hload
  · intro ge1 ge2 vargs m1 t vres m2 heq hsem
    cases hsem with
    | volatile_load_sem_intro b ofs _ _ _ hload =>
        apply volatile_load_sem_intro
        exact volatile_load_preserved ge1 ge2 chunk m1 b ofs t vres heq hload
  · intro ge vargs m1 t vres m2 b hsem hb
    cases hsem
    exact hb
  · intro ge vargs m1 t vres m2 b ofs p hsem hb hp
    cases hsem
    exact hp
  · intro ge vargs m1 t vres m2 b ofs n bytes hsem hb hload hreadonly
    cases hsem
    exact hload
  · intro ge vargs m1 t vres m2 m1' vargs' hsem hext hless
    cases hsem with
    | volatile_load_sem_intro b ofs _ _ _ hload =>
        have hvargs : vargs' = [Vptr b ofs] := by
          cases hless with
          | lessdef_list_cons _ _ _ _ hhead htail =>
              cases htail
              cases hhead
              rfl
        subst vargs'
        obtain ⟨v', hload', hval⟩ :=
          volatile_load_extends ge chunk m1 b ofs t vres m1' hload hext
        refine ⟨v', m1', ?_, hval, hext, extcall_debug_unchanged_on_refl _ _⟩
        apply volatile_load_sem_intro
        exact hload'
  · intro ge1 ge2 vargs m1 t vres m2 f m1' vargs'
      hsymbols hsem hmem hvlist
    cases hsem with
    | volatile_load_sem_intro b ofs _ _ _ hload =>
        cases hvlist with
        | inject_list_cons _ v2 _ _ hptr htail =>
            cases htail
            cases hptr with
            | inject_ptr _ _ b2 ofs2 delta hmap hofs =>
                obtain ⟨v', hload', hval⟩ :=
                  volatile_load_inject ge1 ge2 f chunk m1 b ofs t vres
                    b2 ofs2 m1' hsymbols hload
                    (Val.inject.inject_ptr b ofs b2 ofs2 delta hmap hofs) hmem
                refine ⟨f, v', m1', ?_, hval, hmem,
                  extcall_debug_unchanged_on_refl _ _,
                  extcall_debug_unchanged_on_refl _ _, ?_, ?_⟩
                · apply volatile_load_sem_intro
                  exact hload'
                · intro b0 b' delta' hmap'
                  exact hmap'
                · intro b0 b' delta' hnone hsome
                  rw [hnone] at hsome
                  cases hsome
  · intro ge vargs m t vres m' hsem
    cases hsem with
    | volatile_load_sem_intro _ _ _ _ _ hload =>
        cases hload with
        | volatile_load_vol => simp
        | volatile_load_nonvol =>
            change List.length ([] : List event) ≤ 1
            simp
  · intro ge vargs m t1 vres1 m1 t2 hsem hmatch
    cases hsem with
    | volatile_load_sem_intro b ofs _ _ _ hload =>
        obtain ⟨v2, hload2⟩ :=
          volatile_load_receptive ge chunk m b ofs t1 t2 vres1 hload hmatch
        refine ⟨v2, m, ?_⟩
        apply volatile_load_sem_intro
        exact hload2
  · intro ge vargs m t1 vres1 m1 t2 vres2 m2 hsem1 hsem2
    cases hsem1 with
    | volatile_load_sem_intro b1 ofs1 _ _ _ hload1 =>
        cases hsem2 with
        | volatile_load_sem_intro b2 ofs2 _ _ _ hload2 =>
            cases hload1 with
            | volatile_load_vol id ev _ hvol hfind hmatch =>
                cases hload2 with
                | volatile_load_vol id0 ev0 _ hvol0 hfind0 hmatch0 =>
                    have hid : id = id0 :=
                      ge.find_symbol_injective id id0 hfind hfind0
                    subst id0
                    refine ⟨match_traces_vload chunk id ofs1 ev ev0
                      (eventval_match_valid ge ev (type_of_chunk chunk) _ hmatch)
                      (eventval_match_valid ge ev0 (type_of_chunk chunk) _ hmatch0)
                      (eventval_match_same_type ge ev (type_of_chunk chunk) _ ev0 _ hmatch hmatch0), ?_⟩
                    intro heq
                    cases heq
                    have hv : _ = _ :=
                      eventval_match_determ_1 ge ev (type_of_chunk chunk) _ _ hmatch hmatch0
                    subst_vars
                    exact ⟨rfl, rfl⟩
                | volatile_load_nonvol _ hnot0 hload0 =>
                    rw [hvol] at hnot0
                    cases hnot0
            | volatile_load_nonvol _ hnot hload =>
                cases hload2 with
                | volatile_load_vol id0 ev0 _ hvol0 hfind0 hmatch0 =>
                    rw [hvol0] at hnot
                    cases hnot
                | volatile_load_nonvol _ hnot0 hload0 =>
                    refine ⟨match_traces_E0, ?_⟩
                    intro heq
                    have hv : _ = _ := Option.some.inj (hload.symm.trans hload0)
                    subst_vars
                    exact ⟨rfl, rfl⟩

end CompCert4Lean.Common.Events


namespace CompCert4Lean.Common.Events

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers

theorem volatile_store_ok : volatile_store_okStatement := by
  intro chunk
  refine {
    ec_well_typed := ?_
    ec_symbols_preserved := ?_
    ec_valid_block := ?_
    ec_max_perm := ?_
    ec_readonly := ?_
    ec_mem_extends := ?_
    ec_mem_inject := ?_
    ec_trace_length := ?_
    ec_receptive := ?_
    ec_determ := ?_ }
  · intro ge vargs m1 t vres m2 hsem
    cases hsem with
    | volatile_store_sem_intro b ofs _ _ _ _ hstore =>
        simp [CompCert4Lean.Common.Values.Val.has_rettype]
  · intro ge1 ge2 vargs m1 t vres m2 heq hsem
    cases hsem with
    | volatile_store_sem_intro b ofs _ _ _ _ hstore =>
        apply volatile_store_sem_intro
        exact volatile_store_preserved ge1 ge2 chunk m1 b ofs _ t m2 heq hstore
  · intro ge vargs m1 t vres m2 b hsem hb
    cases hsem with
    | volatile_store_sem_intro b0 ofs _ _ _ _ hstore =>
        cases hstore with
        | volatile_store_vol => exact hb
        | volatile_store_nonvol =>
            rename_i v hnot hstore'
            exact Mem.store_valid_block_1 chunk m1 b0 (Ptrofs.unsigned ofs) v m2 hstore' b hb
  · intro ge vargs m1 t vres m2 b ofs p hsem hb hp
    cases hsem with
    | volatile_store_sem_intro b0 ofs0 _ _ _ _ hstore =>
        cases hstore with
        | volatile_store_vol => exact hp
        | volatile_store_nonvol =>
            rename_i v hnot hstore'
            exact Mem.perm_store_2 chunk m1 b0 (Ptrofs.unsigned ofs0) v m2 hstore' b ofs Max p hp
  · intro ge vargs m1 t vres m2 b ofs n bytes hsem hb hload hreadonly
    cases hsem with
    | volatile_store_sem_intro b0 ofs0 _ _ _ _ hstore =>
        apply unchanged_on_readonly m1 m2 b ofs n bytes
        · exact volatile_store_readonly ge chunk m1 b0 ofs0 _ t m2 hstore
        · exact hb
        · exact hload
        · exact hreadonly
  · intro ge vargs m1 t vres m2 m1' vargs' hsem hext hless
    cases hsem with
    | volatile_store_sem_intro b ofs _ _ _ _ hstore =>
        cases hless with
        | lessdef_list_cons _ vptr _ vl hptr htail =>
            cases htail with
            | lessdef_list_cons _ v' _ vl' hv hnil =>
                cases hnil
                cases hptr
                obtain ⟨m2', hstore', hext', hunch⟩ :=
                  volatile_store_extends ge chunk m1 b ofs _ t m2 m1' v' hstore hext hv
                refine ⟨.Vundef, m2', ?_, .lessdef_refl _, hext', hunch⟩
                exact volatile_store_sem_intro b ofs m1' v' t m2' hstore'
  · intro ge1 ge2 vargs m1 t vres m2 f m1' vargs'
      hsymbols hsem hmem hvlist
    cases hsem with
    | volatile_store_sem_intro b ofs _ _ _ _ hstore =>
        cases hvlist with
        | inject_list_cons _ vptr _ vl hptr htail =>
            cases htail with
            | inject_list_cons _ v' _ vl' hv hnil =>
                cases hnil
                cases hptr with
                | inject_ptr b0 ofs0 b' ofs' delta hmap hofs =>
                    obtain ⟨m2', hstore', hmem', hunch1, hunch2⟩ :=
                      volatile_store_inject ge1 ge2 f chunk m1 b ofs _ t m2 m1' b' ofs' v'
                        hsymbols hstore
                        (Val.inject.inject_ptr b ofs b' ofs' delta hmap hofs) hv hmem
                    refine ⟨f, .Vundef, m2', ?_, .val_inject_undef _, hmem',
                      hunch1, hunch2, ?_, ?_⟩
                    · exact volatile_store_sem_intro b' ofs' m1' v' t m2' hstore'
                    · intro b0 b' delta' hmap'
                      exact hmap'
                    · intro b0 b' delta' hnone hsome
                      rw [hnone] at hsome
                      cases hsome
  · intro ge vargs m t vres m' hsem
    cases hsem with
    | volatile_store_sem_intro _ _ _ _ _ _ hstore =>
        cases hstore with
        | volatile_store_vol => simp
        | volatile_store_nonvol => simp [E0]
  · intro ge vargs m t1 vres1 m1 t2 hsem hmatch
    cases hsem with
    | volatile_store_sem_intro b ofs _ _ _ _ hstore =>
        have ht := volatile_store_receptive ge chunk m b ofs _ t1 m1 t2 hstore hmatch
        subst t2
        exact ⟨.Vundef, m1, volatile_store_sem_intro b ofs m _ t1 m1 hstore⟩
  · intro ge vargs m t1 vres1 m1 t2 vres2 m2 hsem1 hsem2
    cases hsem1 with
    | volatile_store_sem_intro b1 ofs1 _ _ _ _ hstore1 =>
        cases hsem2 with
        | volatile_store_sem_intro b2 ofs2 _ _ _ _ hstore2 =>
            cases hstore1 with
            | volatile_store_vol id ev _ hvol hfind hmatch1 =>
                cases hstore2 with
                | volatile_store_vol id0 ev0 _ hvol0 hfind0 hmatch2 =>
                    have hid : id = id0 :=
                      ge.find_symbol_injective id id0 hfind hfind0
                    subst id0
                    have hev : ev = ev0 :=
                      eventval_match_determ_2 ge ev ev0 (type_of_chunk chunk)
                        (Val.load_result chunk _) hmatch1 hmatch2
                    subst ev0
                    refine ⟨match_traces_vstore chunk id ofs1 ev, ?_⟩
                    intro heq
                    cases heq
                    exact ⟨rfl, rfl⟩
                | volatile_store_nonvol v0 m20 hnot0 hstore0 =>
                    rw [hvol] at hnot0
                    cases hnot0
            | volatile_store_nonvol v m2 hnot hstore =>
                cases hstore2 with
                | volatile_store_vol id0 ev0 _ hvol0 hfind0 hmatch0 =>
                    rw [hvol0] at hnot
                    cases hnot
                | volatile_store_nonvol v0 m20 hnot0 hstore0 =>
                    refine ⟨match_traces_E0, ?_⟩
                    intro heq
                    cases heq
                    have hm : _ = _ := Option.some.inj (hstore.symm.trans hstore0)
                    subst_vars
                    exact ⟨rfl, rfl⟩

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Builtins0
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps


private theorem memcpy_aux_storebytes_unchanged
    (P : block → Z → Prop) (m : mem) (b : block) (ofs : Z)
    (bytes : List memval) (m' : mem)
    (hstore : Mem.storebytes m b ofs bytes = some m')
    (hout : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs (ZArith.BinInt.Z.of_nat bytes.length)) → ¬ P b i) :
    Mem.unchanged_on P m m' := by
  constructor
  · rw [Mem.nextblock_storebytes _ _ _ _ _ hstore]
    exact Ple_refl _
  · intro b' ofs' k p _ _
    exact ⟨Mem.perm_storebytes_1 _ _ _ _ _ hstore b' ofs' k p,
      Mem.perm_storebytes_2 _ _ _ _ _ hstore b' ofs' k p⟩
  · intro b' ofs' hP _
    rw [Mem.storebytes_mem_contents _ _ _ _ _ hstore]
    by_cases hb : b' = b
    · subst b'
      erw [PMap.gss]
      apply Mem.setN_other
      intro r hr heq
      subst r
      exact hout ofs' (by exact hr) hP
    · erw [PMap.gso _ _ hb]


private theorem memcpy_aux_zadd_zero (x : Z) : zAdd x (ZArith.BinInt.Z.Z0) = x := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [zAdd, ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change intOfZ x + 0 = intOfZ x
  omega

private theorem memcpy_aux_loadbytes_extends : Mem.loadbytes_extendsStatement := by
  intro m1 m2 b ofs len bytes1 hext hload
  obtain ⟨bytes2, hload2, hbytes⟩ := Mem.loadbytes_inj inject_id m1 m2 len b ofs b .Z0 bytes1
    hext.mext_inj hload rfl
  refine ⟨bytes2, ?_, ?_⟩
  · change Mem.loadbytes m2 b (zAdd ofs (ZArith.BinInt.Z.Z0)) len = some bytes2 at hload2
    rw [memcpy_aux_zadd_zero] at hload2
    exact hload2
  · exact hbytes

private theorem memcpy_aux_storebytes_within_extends : Mem.storebytes_within_extendsStatement := by
  intro m1 m2 b ofs bytes1 n1 bytes2 hext hs hv
  obtain ⟨n2, hs2, hi⟩ := Mem.storebytes_mapped_inj inject_id m1 b ofs bytes1 n1
    m2 b .Z0 bytes2 hext.mext_inj hs (by
      intro b1 b1' d1 b2 b2' d2 ofs1 ofs2 hne h1 h2 hp1 hp2
      have h1' : (b1, (.Z0 : Z)) = (b1', d1) := Option.some.inj h1
      have h2' : (b2, (.Z0 : Z)) = (b2', d2) := Option.some.inj h2
      cases h1'; cases h2'; exact Or.inl hne) rfl hv
  change Mem.storebytes m2 b (zAdd ofs (ZArith.BinInt.Z.Z0)) bytes2 = some n2 at hs2
  rw [memcpy_aux_zadd_zero] at hs2
  have hs2' : Mem.storebytes m2 b ofs bytes2 = some n2 := hs2
  refine ⟨n2, hs2', ?_⟩
  constructor
  · rw [Mem.nextblock_storebytes _ _ _ _ _ hs, Mem.nextblock_storebytes _ _ _ _ _ hs2']
    exact hext.mext_next
  · exact hi
  · intro b' ofs' k p hp
    obtain hp' | hn := hext.mext_perm_inv b' ofs' k p
      (Mem.perm_storebytes_2 _ _ _ _ _ hs2' _ _ _ _ hp)
    · exact Or.inl (Mem.perm_storebytes_1 _ _ _ _ _ hs _ _ _ _ hp')
    · exact Or.inr (fun h => hn (Mem.perm_storebytes_2 _ _ _ _ _ hs _ _ _ _ h))

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private theorem memcpy_aux_injection_transport
    (f : Val.meminj) (m1 m2 n1 n2 : mem) (b1 b2 : block)
    (ofs1 ofs2 : Z) (bytes1 bytes2 : List memval)
    (hinj : Mem.inject f m1 m2)
    (hs1 : Mem.storebytes m1 b1 ofs1 bytes1 = some n1)
    (hs2 : Mem.storebytes m2 b2 ofs2 bytes2 = some n2)
    (hmem : Mem.mem_inj f n1 n2) : Mem.inject f n1 n2 := by
  have hp1 := Mem.perm_storebytes_1 _ _ _ _ _ hs1
  have hp2 := Mem.perm_storebytes_2 _ _ _ _ _ hs1
  have hq2 := Mem.perm_storebytes_2 _ _ _ _ _ hs2
  constructor
  · exact hmem
  · intro b hb
    apply hinj.mi_freeblocks b
    intro hv
    exact hb (Mem.storebytes_valid_block_1 _ _ _ _ _ hs1 b hv)
  · intro b b' delta hmap
    exact Mem.storebytes_valid_block_1 _ _ _ _ _ hs2 b'
      (hinj.mi_mappedblocks b b' delta hmap)
  · intro b b' delta c c' delta' ofs ofs' hne hmap hmap' hp hq
    exact hinj.mi_no_overlap b b' delta c c' delta' ofs ofs' hne hmap hmap'
      (hp2 b ofs Max Nonempty hp) (hp2 c ofs' Max Nonempty hq)
  · intro b b' delta ofs hmap hp
    apply hinj.mi_representable b b' delta ofs hmap
    exact hp.elim (fun h => Or.inl (hp2 _ _ _ _ h))
      (fun h => Or.inr (hp2 _ _ _ _ h))
  · intro b ofs b' delta k p hmap hp
    obtain hp | hn := hinj.mi_perm_inv b ofs b' delta k p hmap (hq2 _ _ _ _ hp)
    · exact Or.inl (hp1 _ _ _ _ hp)
    · exact Or.inr (fun h => hn (hp2 _ _ _ _ h))

private theorem memcpy_aux_aligned : Mem.aligned_area_injectStatement := by
  intro f m m' b ofs al sz b' delta hinj hal hpos hdiv hrange hof hmap
  have hbound : zLe al sz := by
    obtain ⟨k, hk⟩ := hdiv
    have hk' := congrArg intOfZ hk
    change 0 < intOfZ sz at hpos
    change intOfZ al ≤ intOfZ sz
    simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt] at hk'
    rcases hal with rfl | rfl | rfl | rfl
    · change intOfZ sz = 1 * intOfZ k at hk'
      change 1 ≤ intOfZ sz
      omega
    · change intOfZ sz = 2 * intOfZ k at hk'
      change 2 ≤ intOfZ sz
      omega
    · change intOfZ sz = 4 * intOfZ k at hk'
      change 4 ≤ intOfZ sz
      omega
    · change intOfZ sz = 8 * intOfZ k at hk'
      change 8 ≤ intOfZ sz
      omega
  have hchunk : ∃ chunk, al = align_chunk chunk ∧ al = size_chunk chunk := by
    rcases hal with rfl | rfl | rfl | rfl
    · exact ⟨Mint8unsigned, rfl, rfl⟩
    · exact ⟨Mint16unsigned, rfl, rfl⟩
    · exact ⟨Mint32, rfl, rfl⟩
    · exact ⟨Mint64, rfl, rfl⟩
  obtain ⟨chunk, halign, hsize⟩ := hchunk
  have hd : zDivide al delta := by
    rw [halign]
    apply hinj.mi_inj.mi_align b b' delta chunk ofs Nonempty hmap
    intro i hi
    apply Mem.perm_cur_max m b i Nonempty
    apply hrange i
    rw [← hsize] at hi
    change intOfZ ofs ≤ intOfZ i ∧ intOfZ i < intOfZ (zAdd ofs al) at hi
    change intOfZ al ≤ intOfZ sz at hbound
    change intOfZ ofs ≤ intOfZ i ∧ intOfZ i < intOfZ (zAdd ofs sz)
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hi ⊢
    omega
  exact ZArith.BinInt.Z.divide_add_r al ofs delta hof hd

private theorem memcpy_aux_disjoint : Mem.disjoint_or_equal_injectStatement := by
  intro f m m' b1 b1' d1 b2 b2' d2 o1 o2 sz hinj hm1 hm2 hr1 hr2 hpos hno
  by_cases hb : b1 = b2
  · subst b2
    have heq := Option.some.inj (hm1.symm.trans hm2)
    cases heq
    rcases hno with hne | heq | hle | hle
    · exact False.elim (hne rfl)
    · exact Or.inr (Or.inl (congrArg (fun o => zAdd o d1) heq))
    · right; right; left
      change intOfZ (zAdd o1 sz) ≤ intOfZ o2 at hle
      change intOfZ (zAdd (zAdd o1 d1) sz) ≤ intOfZ (zAdd o2 d1)
      simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hle ⊢
      omega
    · right; right; right
      change intOfZ (zAdd o2 sz) ≤ intOfZ o1 at hle
      change intOfZ (zAdd (zAdd o2 d1) sz) ≤ intOfZ (zAdd o1 d1)
      simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hle ⊢
      omega
  · by_cases ht : b1' = b2'
    · subst b2'
      right; right
      by_cases hleft : zLe (zAdd (zAdd o1 d1) sz) (zAdd o2 d2)
      · exact Or.inl hleft
      by_cases hright : zLe (zAdd (zAdd o2 d2) sz) (zAdd o1 d1)
      · exact Or.inr hright
      exfalso
      let x := zOfInt (max (intOfZ o1 + intOfZ d1) (intOfZ o2 + intOfZ d2))
      have hxp : ∀ o d,
          (o = o1 ∧ d = d1) ∨ (o = o2 ∧ d = d2) →
          zLe o (zSub x d) ∧ zLt (zSub x d) (zAdd o sz) := by
        intro o d heq
        change ¬ (intOfZ (zAdd (zAdd o1 d1) sz) ≤ intOfZ (zAdd o2 d2)) at hleft
        change ¬ (intOfZ (zAdd (zAdd o2 d2) sz) ≤ intOfZ (zAdd o1 d1)) at hright
        change 0 < intOfZ sz at hpos
        change intOfZ o ≤ intOfZ (zSub x d) ∧
          intOfZ (zSub x d) < intOfZ (zAdd o sz)
        simp only [x, zSub, zAdd, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
          intOfZ_zOfInt] at hleft hright ⊢
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      have hneq := hinj.mi_no_overlap b1 b1' d1 b2 b1' d2
        (zSub x d1) (zSub x d2) hb hm1 hm2
        (hr1 _ (hxp o1 d1 (Or.inl ⟨rfl, rfl⟩)))
        (hr2 _ (hxp o2 d2 (Or.inr ⟨rfl, rfl⟩)))
      rcases hneq with hneq | hneq
      · exact hneq rfl
      · apply hneq
        apply intOfZ_injective
        simp only [zSub, zAdd, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt]
        omega
    · exact Or.inl ht

end CompCert4Lean.Common.Events

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

theorem extcall_memcpy_ok : extcall_memcpy_okStatement := by
  intro sz al
  refine {
    ec_well_typed := ?_
    ec_symbols_preserved := ?_
    ec_valid_block := ?_
    ec_max_perm := ?_
    ec_readonly := ?_
    ec_mem_extends := ?_
    ec_mem_inject := ?_
    ec_trace_length := ?_
    ec_receptive := ?_
    ec_determ := ?_ }
  · intro ge vargs m1 t vres m2 hsem
    cases hsem
    simp [Val.has_rettype]
  · intro ge1 ge2 vargs m1 t vres m2 heq hsem
    cases hsem with
    | extcall_memcpy_sem_intro bd od bs os m bytes m' hal hsz hsa hsrc hdst hno hl hs =>
      apply extcall_memcpy_sem_intro <;> assumption
  · intro ge vargs m1 t vres m2 b hsem hb
    cases hsem with
    | extcall_memcpy_sem_intro bd od bs os m bytes m' hal hsz hsa hsrc hdst hno hl hs =>
      exact Mem.storebytes_valid_block_1 _ _ _ _ _ hs b hb
  · intro ge vargs m1 t vres m2 b ofs p hsem hb hp
    cases hsem with
    | extcall_memcpy_sem_intro bd od bs os m bytes m' hal hsz hsa hsrc hdst hno hl hs =>
      exact Mem.perm_storebytes_2 _ _ _ _ _ hs _ _ _ _ hp
  · intro ge vargs m1 t vres m2 b ofs n bytes hsem hb hload hreadonly
    cases hsem with
    | extcall_memcpy_sem_intro bd od bs os m bytes0 m' hal hsz hsa hsrc hdst hno hl hs =>
      apply unchanged_on_readonly m1 m2 b ofs n bytes
        (memcpy_aux_storebytes_unchanged (loc_not_writable m1) m1 bd
          (Ptrofs.unsigned od) bytes0 m2 hs (by
            intro i hi hnw
            apply hnw
            exact Mem.perm_cur_max m1 bd i Writable
              (Mem.storebytes_range_perm _ _ _ _ _ hs i hi))) hb hload hreadonly
  · intro ge vargs m1 t vres m2 m1' vargs' hsem hext hvlist
    cases hsem with
    | extcall_memcpy_sem_intro bd od bs os m bytes n hal hsz hsa hsrc hdst hno hl hs =>
      cases hvlist with
      | lessdef_list_cons _ vptr _ vl hptr htail =>
          cases htail with
          | lessdef_list_cons _ v' _ vl' hv hnil =>
              cases hnil
              cases hptr
              cases hv
              obtain ⟨bytes', hl', hbytes⟩ := memcpy_aux_loadbytes_extends m1 m1' bs (Ptrofs.unsigned os) sz bytes hext hl
              obtain ⟨n', hs', hext'⟩ := memcpy_aux_storebytes_within_extends m1 m1' bd (Ptrofs.unsigned od) bytes m2 bytes' hext hs
                hbytes
              refine ⟨.Vundef, n', ?_, .lessdef_refl _, hext', ?_⟩
              · apply extcall_memcpy_sem_intro
                · exact hal
                · exact hsz
                · exact hsa
                · exact hsrc
                · exact hdst
                · exact hno
                · exact hl'
                · exact hs'
              · have hlen : bytes'.length = bytes.length :=
                  (list_forall2_length _ _ _ bytes bytes' hbytes).symm
                apply memcpy_aux_storebytes_unchanged (loc_out_of_bounds m1) m1' bd
                  (Ptrofs.unsigned od) bytes' n' hs'
                intro i hi hout
                apply hout
                apply Mem.perm_cur_max m1 bd i Nonempty
                apply Mem.perm_implies m1 bd i Cur Writable Nonempty
                · apply Mem.storebytes_range_perm m1 bd (Ptrofs.unsigned od)
                    bytes m2 hs i
                  have hi' : zLe (Ptrofs.unsigned od) i ∧
                      zLt i (zAdd (Ptrofs.unsigned od) (ZArith.BinInt.Z.of_nat bytes.length)) := by
                    rw [← hlen]
                    exact hi
                  exact hi'
                · exact perm_any_N Writable
  · intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hsymbols hsem hmem hvlist
    cases hsem with
    | extcall_memcpy_sem_intro bd od bs os m bytes n hal hsz hsa hsrc hdst hno hl hs =>
      cases hvlist with
      | inject_list_cons _ vd _ vl hpd htail =>
        cases htail with
        | inject_list_cons _ vs _ vl' hps hnil =>
          cases hnil
          cases hpd with
          | inject_ptr _ _ bd' od' dd hmd hod =>
            cases hps with
            | inject_ptr _ _ bs' os' ds hms hos =>
              subst od'
              subst os'
              by_cases hz : sz = (.Z0 : Z)
              · subst sz
                have hnil : bytes = [] := by
                  have hlen := Mem.loadbytes_length _ _ _ _ _ hl
                  change bytes.length = 0 at hlen
                  cases bytes with
                  | nil => rfl
                  | cons v vs => simp at hlen
                subst bytes
                obtain ⟨n', hs'⟩ := Mem.range_perm_storebytes m1' bd'
                  (Ptrofs.unsigned (Ptrofs.add od (Ptrofs.repr dd))) [] (by
                    intro i hi
                    change intOfZ (Ptrofs.unsigned (Ptrofs.add od (Ptrofs.repr dd))) ≤ intOfZ i ∧
                      intOfZ i < intOfZ (zAdd
                        (Ptrofs.unsigned (Ptrofs.add od (Ptrofs.repr dd))) (.Z0 : Z)) at hi
                    rw [memcpy_aux_zadd_zero] at hi
                    omega)
                have hfull := memcpy_aux_injection_transport f m1 m1' m2 n' bd bd'
                  (Ptrofs.unsigned od) (Ptrofs.unsigned (Ptrofs.add od (Ptrofs.repr dd)))
                  [] [] hmem hs hs'
                  (Mem.storebytes_empty_inj _ _ _ _ _ _ _ _ _ hmem.mi_inj hs hs')
                refine ⟨f, Vundef, n', ?_, .val_inject_undef _, hfull, ?_, ?_,
                  inject_incr_refl f, ?_⟩
                · apply extcall_memcpy_sem_intro
                    bd' (Ptrofs.add od (Ptrofs.repr dd))
                    bs' (Ptrofs.add os (Ptrofs.repr ds)) m1' [] n'
                    hal hsz hsa
                  · intro h; change (0 : _root_.Int) < 0 at h; omega
                  · intro h; change (0 : _root_.Int) < 0 at h; omega
                  · right; right
                    change intOfZ (zAdd (Ptrofs.unsigned (Ptrofs.add os (Ptrofs.repr ds))) .Z0) ≤
                        intOfZ (Ptrofs.unsigned (Ptrofs.add od (Ptrofs.repr dd))) ∨
                      intOfZ (zAdd (Ptrofs.unsigned (Ptrofs.add od (Ptrofs.repr dd))) .Z0) ≤
                        intOfZ (Ptrofs.unsigned (Ptrofs.add os (Ptrofs.repr ds)))
                    rw [memcpy_aux_zadd_zero, memcpy_aux_zadd_zero]
                    omega
                  · exact Mem.loadbytes_empty _ _ _ _ (by exact _root_.Int.le_refl 0)
                  · exact hs'
                · apply memcpy_aux_storebytes_unchanged _ _ _ _ _ _ hs
                  intro i hi hu
                  change f bd = none at hu
                  rw [hmd] at hu
                  cases hu
                · apply memcpy_aux_storebytes_unchanged _ _ _ _ _ _ hs'
                  intro i hi _
                  change intOfZ (Ptrofs.unsigned (Ptrofs.add od (Ptrofs.repr dd))) ≤ intOfZ i ∧
                    intOfZ i < intOfZ (zAdd
                      (Ptrofs.unsigned (Ptrofs.add od (Ptrofs.repr dd))) (.Z0 : Z)) at hi
                  rw [memcpy_aux_zadd_zero] at hi
                  omega
                · intro b b' delta hn hm
                  rw [hn] at hm
                  cases hm
              · have hpos : zLt z0 sz := by
                  have hn : intOfZ sz ≠ 0 := by
                    intro h
                    apply hz
                    apply intOfZ_injective
                    exact h
                  change 0 ≤ intOfZ sz at hsz
                  change 0 < intOfZ sz
                  omega
                have hlen : ZArith.BinInt.Z.of_nat bytes.length = sz := by
                  rw [Mem.loadbytes_length _ _ _ _ _ hl]
                  apply intOfZ_injective
                  simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
                  exact _root_.Int.toNat_of_nonneg hsz
                have hrs : Mem.range_perm m1 bs (Ptrofs.unsigned os)
                    (zAdd (Ptrofs.unsigned os) sz) Cur Nonempty :=
                  Mem.range_perm_implies _ _ _ _ _ Readable Nonempty
                    (Mem.loadbytes_range_perm _ _ _ _ _ hl) (perm_any_N Readable)
                have hrd : Mem.range_perm m1 bd (Ptrofs.unsigned od)
                    (zAdd (Ptrofs.unsigned od) sz) Cur Nonempty := by
                  rw [← hlen]
                  exact Mem.range_perm_implies _ _ _ _ _ Writable Nonempty
                    (Mem.storebytes_range_perm _ _ _ _ _ hs) (perm_any_N Writable)
                have hps0 : Mem.perm m1 bs (Ptrofs.unsigned os) Cur Nonempty := by
                  apply hrs
                  change intOfZ (Ptrofs.unsigned os) ≤ intOfZ (Ptrofs.unsigned os) ∧
                    intOfZ (Ptrofs.unsigned os) < intOfZ (zAdd (Ptrofs.unsigned os) sz)
                  simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
                  change 0 < intOfZ sz at hpos
                  omega
                have hpd0 : Mem.perm m1 bd (Ptrofs.unsigned od) Cur Nonempty := by
                  apply hrd
                  change intOfZ (Ptrofs.unsigned od) ≤ intOfZ (Ptrofs.unsigned od) ∧
                    intOfZ (Ptrofs.unsigned od) < intOfZ (zAdd (Ptrofs.unsigned od) sz)
                  simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
                  change 0 < intOfZ sz at hpos
                  omega
                have has := events_address_inject f m1 m1' bs bs' os ds Nonempty hmem hps0 hms
                have had := events_address_inject f m1 m1' bd bd' od dd Nonempty hmem hpd0 hmd
                obtain ⟨bytes', hl', hbytes⟩ := Mem.loadbytes_inj f m1 m1' sz bs
                  (Ptrofs.unsigned os) bs' ds bytes hmem.mi_inj hl hms
                obtain ⟨n', hs', hinj'⟩ := Mem.storebytes_mapped_inj f m1 bd
                  (Ptrofs.unsigned od) bytes m2 m1' bd' dd bytes'
                  hmem.mi_inj hs hmem.mi_no_overlap hmd hbytes
                have hfull := memcpy_aux_injection_transport f m1 m1' m2 n' bd bd'
                  (Ptrofs.unsigned od) (zAdd (Ptrofs.unsigned od) dd) bytes bytes'
                  hmem hs hs' hinj'
                refine ⟨f, Vundef, n', ?_, .val_inject_undef _, hfull, ?_, ?_,
                  inject_incr_refl f, ?_⟩
                · apply extcall_memcpy_sem_intro
                    bd' (Ptrofs.add od (Ptrofs.repr dd))
                    bs' (Ptrofs.add os (Ptrofs.repr ds)) m1' bytes' n'
                    hal hsz hsa
                  · intro _
                    rw [has]
                    exact memcpy_aux_aligned f m1 m1' bs (Ptrofs.unsigned os)
                      al sz bs' ds hmem hal hpos hsa hrs (hsrc hpos) hms
                  · intro _
                    rw [had]
                    exact memcpy_aux_aligned f m1 m1' bd (Ptrofs.unsigned od)
                      al sz bd' dd hmem hal hpos hsa hrd (hdst hpos) hmd
                  · rw [has, had]
                    exact memcpy_aux_disjoint f m1 m1' bs bs' ds bd bd' dd
                      (Ptrofs.unsigned os) (Ptrofs.unsigned od) sz hmem hms hmd
                      (Mem.range_perm_max _ _ _ _ _ _ hrs)
                      (Mem.range_perm_max _ _ _ _ _ _ hrd) hpos hno
                  · rw [has]
                    exact hl'
                  · rw [had]
                    exact hs'
                · apply memcpy_aux_storebytes_unchanged _ _ _ _ _ _ hs
                  intro i hi hu
                  change f bd = none at hu
                  rw [hmd] at hu
                  cases hu
                · apply memcpy_aux_storebytes_unchanged _ _ _ _ _ _ hs'
                  intro i hi hout
                  apply hout bd dd hmd
                  apply Mem.perm_cur_max m1 bd (zSub i dd) Nonempty
                  apply Mem.perm_implies m1 bd (zSub i dd) Cur Writable Nonempty
                    _ (perm_any_N Writable)
                  apply Mem.storebytes_range_perm _ _ _ _ _ hs
                  have hlength := list_forall2_length _ _ _ bytes bytes' hbytes
                  change zLe (zAdd (Ptrofs.unsigned od) dd) i ∧
                    zLt i (zAdd (zAdd (Ptrofs.unsigned od) dd)
                      (ZArith.BinInt.Z.of_nat bytes'.length)) at hi
                  change zLe (Ptrofs.unsigned od) (zSub i dd) ∧
                    zLt (zSub i dd) (zAdd (Ptrofs.unsigned od)
                      (ZArith.BinInt.Z.of_nat bytes.length))
                  rw [hlength]
                  change intOfZ (zAdd (Ptrofs.unsigned od) dd) ≤ intOfZ i ∧
                    intOfZ i < intOfZ (zAdd (zAdd (Ptrofs.unsigned od) dd)
                      (ZArith.BinInt.Z.of_nat bytes'.length)) at hi
                  change intOfZ (Ptrofs.unsigned od) ≤ intOfZ (zSub i dd) ∧
                    intOfZ (zSub i dd) < intOfZ (zAdd (Ptrofs.unsigned od)
                      (ZArith.BinInt.Z.of_nat bytes'.length))
                  simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
                    intOfZ_zOfInt] at hi ⊢
                  omega
                · intro b b' delta hn hm
                  rw [hn] at hm
                  cases hm
  · intro ge vargs m t vres m' hsem
    cases hsem
    simp [E0]
  · intro ge vargs m t1 vres1 m1 t2 hsem hmatch
    cases hsem
    cases hmatch
    refine ⟨.Vundef, m1, ?_⟩
    apply extcall_memcpy_sem_intro <;> assumption
  · intro ge vargs m t1 vres1 m1 t2 vres2 m2 hsem1 hsem2
    cases hsem1 with
    | extcall_memcpy_sem_intro bd1 od1 bs1 os1 m0 bytes1 m1' ha1 hsza1 hsa1 hsrc1 hdst1 hno1 hl1 hst1 =>
      cases hsem2 with
      | extcall_memcpy_sem_intro bd2 od2 bs2 os2 m0' bytes2 m2' ha2 hsza2 hsa2 hsrc2 hdst2 hno2 hl2 hst2 =>
        refine ⟨match_traces_E0, ?_⟩
        intro _
        have hb : bytes1 = bytes2 := Option.some.inj (hl1.symm.trans hl2)
        subst bytes2
        have hm : m1 = m2 := Option.some.inj (hst1.symm.trans hst2)
        subst m2
        constructor <;> rfl
end CompCert4Lean.Common.Events
