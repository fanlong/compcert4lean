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

structure NonemptyTrace : Type where
  head : event
  tail : trace

namespace NonemptyTrace

def toTrace (chunk : NonemptyTrace) : trace :=
  chunk.head :: chunk.tail

def ofTrace (t : trace) (h : t ≠ E0) : NonemptyTrace :=
  match t with
  | [] => False.elim (h rfl)
  | e :: rest => ⟨e, rest⟩

end NonemptyTrace

abbrev traceinf' : Type := Nat → NonemptyTrace

namespace traceinf'

def cons (chunk : NonemptyTrace) (T : traceinf') : traceinf'
  | 0 => chunk
  | n + 1 => T n

def headChunk (T : traceinf') : NonemptyTrace := T 0

def tailChunks (T : traceinf') : traceinf' := fun n => T (n + 1)

end traceinf'

def Econsinf' (t : trace) (T : traceinf') (NE : t ≠ E0) : traceinf' :=
  traceinf'.cons (NonemptyTrace.ofTrace t NE) T

def split_traceinf' (t : trace) (T : traceinf') (NE : t ≠ E0) :
    event × traceinf' :=
  match t with
  | [] => False.elim (NE rfl)
  | e :: [] => (e, T)
  | e :: e' :: rest =>
      (e, Econsinf' (e' :: rest) T (by intro h; cases h))

private structure TraceChunkCursor : Type where
  current : NonemptyTrace
  rest : traceinf'

private def TraceChunkCursor.ofChunks (T : traceinf') : TraceChunkCursor where
  current := traceinf'.headChunk T
  rest := traceinf'.tailChunks T

private def TraceChunkCursor.next (cursor : TraceChunkCursor) : TraceChunkCursor :=
  match cursor.current.tail with
  | [] => TraceChunkCursor.ofChunks cursor.rest
  | e :: rest => { current := ⟨e, rest⟩, rest := cursor.rest }

private def TraceChunkCursor.nth : TraceChunkCursor → Nat → event
  | cursor, 0 => cursor.current.head
  | cursor, n + 1 => TraceChunkCursor.nth cursor.next n

def traceinf_of_traceinf' (T : traceinf') : traceinf :=
  TraceChunkCursor.nth (TraceChunkCursor.ofChunks T)

def unroll_traceinf'Statement : Prop :=
  ∀ T : traceinf',
    T = Econsinf' (NonemptyTrace.toTrace (traceinf'.headChunk T))
      (traceinf'.tailChunks T) (by intro h; cases h)

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

def volatile_load_sem (chunk : memory_chunk) : extcall_sem :=
  fun ge vargs m t v m' =>
    ∃ b ofs, vargs = [Vptr b ofs] ∧ m' = m ∧ volatile_load ge chunk m b ofs t v

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

def volatile_store_sem (chunk : memory_chunk) : extcall_sem :=
  fun ge vargs m1 t vres m2 =>
    ∃ b ofs v,
      vargs = [Vptr b ofs, v] ∧
      vres = Vundef ∧
      volatile_store ge chunk m1 b ofs v t m2

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

def extcall_malloc_sem : extcall_sem :=
  fun _ vargs m t vres m'' =>
    ∃ sz m' b,
      vargs = [Vptrofs sz] ∧
      Mem.alloc m (zOpp (size_chunk Mptr)) (Ptrofs.unsigned sz) = (m', b) ∧
      Mem.store Mptr m' b (zOpp (size_chunk Mptr)) (Vptrofs sz) = some m'' ∧
      t = E0 ∧
      vres = Vptr b Ptrofs.zero

def extcall_malloc_okStatement : Prop :=
  extcall_properties extcall_malloc_sem
    { sig_args := [Xsize_t], sig_res := Xptr, sig_cc := cc_default }

def extcall_free_sem : extcall_sem :=
  fun _ vargs m t vres m' =>
    (∃ b lo sz,
      vargs = [Vptr b lo] ∧
      Mem.load Mptr m b (zSub (Ptrofs.unsigned lo) (size_chunk Mptr)) =
        some (Vptrofs sz) ∧
      Mem.free m b (zSub (Ptrofs.unsigned lo) (size_chunk Mptr))
          (zAdd (Ptrofs.unsigned lo) (Ptrofs.unsigned sz)) = some m' ∧
      t = E0 ∧
      vres = Vundef) ∨
    (vargs = [Vnullptr] ∧ t = E0 ∧ vres = Vundef ∧ m' = m)

def extcall_free_sem_ptr (ge : Senv.t) (b : block) (lo sz : PtrofsT)
    (m m' : mem)
    (LOAD : Mem.load Mptr m b (zSub (Ptrofs.unsigned lo) (size_chunk Mptr)) =
      some (Vptrofs sz))
    (FREE : Mem.free m b (zSub (Ptrofs.unsigned lo) (size_chunk Mptr))
      (zAdd (Ptrofs.unsigned lo) (Ptrofs.unsigned sz)) = some m') :
    extcall_free_sem ge [Vptr b lo] m E0 Vundef m' :=
  Or.inl ⟨b, lo, sz, rfl, LOAD, FREE, rfl, rfl⟩

def extcall_free_okStatement : Prop :=
  extcall_properties extcall_free_sem
    { sig_args := [Xptr], sig_res := Xvoid, sig_cc := cc_default }

def extcall_memcpy_sem (sz al : Z) : extcall_sem :=
  fun _ vargs m t vres m' =>
    ∃ bdst odst bsrc osrc bytes,
      vargs = [Vptr bdst odst, Vptr bsrc osrc] ∧
      (al = z1 ∨ al = ZArith.BinInt.Z.of_nat 2 ∨
        al = ZArith.BinInt.Z.of_nat 4 ∨ al = ZArith.BinInt.Z.of_nat 8) ∧
      zLe z0 sz ∧
      zDivide al sz ∧
      (zLt z0 sz → zDivide al (Ptrofs.unsigned osrc)) ∧
      (zLt z0 sz → zDivide al (Ptrofs.unsigned odst)) ∧
      (bsrc ≠ bdst ∨
        Ptrofs.unsigned osrc = Ptrofs.unsigned odst ∨
        zLe (zAdd (Ptrofs.unsigned osrc) sz) (Ptrofs.unsigned odst) ∨
        zLe (zAdd (Ptrofs.unsigned odst) sz) (Ptrofs.unsigned osrc)) ∧
      Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz = some bytes ∧
      Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = some m' ∧
      t = E0 ∧
      vres = Vundef

def extcall_memcpy_okStatement : Prop :=
  ∀ sz al,
    extcall_properties (extcall_memcpy_sem sz al)
      { sig_args := [Xptr, Xptr], sig_res := Xvoid, sig_cc := cc_default }

def extcall_annot_sem (text : RocqString) (targs : List typ) : extcall_sem :=
  fun ge vargs m t vres m' =>
    ∃ args,
      eventval_list_match ge args targs vargs ∧
      t = [Event_annot text args] ∧
      vres = Vundef ∧
      m' = m

def extcall_annot_okStatement : Prop :=
  ∀ text targs,
    extcall_properties (extcall_annot_sem text targs)
      { sig_args := List.map inj_type targs, sig_res := Xvoid, sig_cc := cc_default }

def extcall_annot_val_sem (text : RocqString) (targ : typ) : extcall_sem :=
  fun ge vargs m t vres m' =>
    ∃ varg arg,
      vargs = [varg] ∧
      eventval_match ge arg targ varg ∧
      t = [Event_annot text [arg]] ∧
      vres = varg ∧
      m' = m

def extcall_annot_val_okStatement : Prop :=
  ∀ text targ,
    extcall_properties (extcall_annot_val_sem text targ)
      { sig_args := [inj_type targ], sig_res := inj_type targ, sig_cc := cc_default }

def extcall_debug_sem : extcall_sem :=
  fun _ _ m t vres m' => t = E0 ∧ vres = Vundef ∧ m' = m

def extcall_debug_okStatement : Prop :=
  ∀ targs,
    extcall_properties extcall_debug_sem
      { sig_args := List.map inj_type targs, sig_res := Xvoid, sig_cc := cc_default }

def known_builtin_sem
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (bf : builtin_function) : extcall_sem :=
  fun _ vargs m t vres m' =>
    builtin_function_sem
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) bf vargs = some vres ∧
      t = E0 ∧ m' = m

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

def eval_builtin_arg {A : Type} (ge : Senv.t) (e : A → val)
    (sp : val) (m : mem) : builtin_arg A → val → Prop
  | BA x, v => v = e x
  | BA_int n, v => v = Vint n
  | BA_long n, v => v = Vlong n
  | BA_float f, v => v = Vfloat f
  | BA_single f, v => v = Vsingle f
  | BA_loadstack chunk ofs, v =>
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = some v
  | BA_addrstack ofs, v => v = Val.offset_ptr sp ofs
  | BA_loadglobal chunk id ofs, v =>
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) = some v
  | BA_addrglobal id ofs, v => v = Senv.symbol_address ge id ofs
  | BA_splitlong hi lo, v =>
      ∃ vhi vlo,
        eval_builtin_arg ge e sp m hi vhi ∧
        eval_builtin_arg ge e sp m lo vlo ∧
        v = Val.longofwords vhi vlo
  | BA_addptr a1 a2, v =>
      ∃ v1 v2,
        eval_builtin_arg ge e sp m a1 v1 ∧
        eval_builtin_arg ge e sp m a2 v2 ∧
        v = if CompCert4Lean.X86_64.Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2

def eval_BA {A : Type} (ge : Senv.t) (e : A → val) (sp : val) (m : mem)
    (x : A) : eval_builtin_arg ge e sp m (BA x) (e x) :=
  rfl

def eval_builtin_args {A : Type} (ge : Senv.t) (e : A → val)
    (sp : val) (m : mem) : List (builtin_arg A) → List val → Prop
  | [], [] => True
  | a :: al, v :: vl =>
      eval_builtin_arg ge e sp m a v ∧ eval_builtin_args ge e sp m al vl
  | _, _ => False

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
