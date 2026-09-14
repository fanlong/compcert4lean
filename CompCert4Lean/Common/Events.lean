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
