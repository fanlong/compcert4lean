import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Values
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Globalenvs

/-!
# Observable events and the external-call semantic core

This module is the dependency-breaking core of CompCert's `common/Events.v`.
It contains only the canonical declarations needed to type the external-call
provider.  The remaining Events interface belongs to
`CompCert4Lean.Common.Events`.
-/

namespace CompCert4Lean.Common.Events

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Globalenvs

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj

private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt

/-! ## Events and traces -/

inductive eventval : Type where
  | EVint : CCInt → eventval
  | EVlong : CCInt64 → eventval
  | EVfloat : CCFloat → eventval
  | EVsingle : CCFloat32 → eventval
  | EVptr_global : ident → Ptrofs → eventval

export eventval (EVint EVlong EVfloat EVsingle EVptr_global)

inductive event : Type where
  | Event_syscall : RocqString → List eventval → eventval → event
  | Event_vload : memory_chunk → ident → Ptrofs → eventval → event
  | Event_vstore : memory_chunk → ident → Ptrofs → eventval → event
  | Event_annot : RocqString → List eventval → event

export event (Event_syscall Event_vload Event_vstore Event_annot)

def trace : Type := List event

def E0 : trace := []

def Eapp (t1 t2 : trace) : trace := List.append t1 t2

/-!
CompCert's Type-valued coinductive trace is represented by its total stream of
finite observations.  This is the accepted observational-coinduction mapping.
-/
abbrev traceinf := Nat → event

def Econsinf (ev : event) (T : traceinf) : traceinf
  | 0 => ev
  | n + 1 => T n

def Eappinf : trace → traceinf → traceinf
  | [], T => T
  | ev :: t, T => Econsinf ev (Eappinf t T)

/-! ## Translation between semantic values and event values -/

inductive eventval_match (ge : Senv.t) : eventval → typ → val → Prop where
  | ev_match_int (i : CCInt) :
      eventval_match ge (EVint i) Tint (Vint i)
  | ev_match_long (i : CCInt64) :
      eventval_match ge (EVlong i) Tlong (Vlong i)
  | ev_match_float (f : CCFloat) :
      eventval_match ge (EVfloat f) Tfloat (Vfloat f)
  | ev_match_single (f : CCFloat32) :
      eventval_match ge (EVsingle f) Tsingle (Vsingle f)
  | ev_match_ptr (id : ident) (b : block) (ofs : Ptrofs)
      (public_symbol : Senv.public_symbol ge id = true)
      (find_symbol : Senv.find_symbol ge id = some b) :
      eventval_match ge (EVptr_global id ofs) Tptr (Vptr b ofs)

export eventval_match
  (ev_match_int ev_match_long ev_match_float ev_match_single ev_match_ptr)

inductive eventval_list_match (ge : Senv.t) :
    List eventval → List typ → List val → Prop where
  | evl_match_nil : eventval_list_match ge [] [] []
  | evl_match_cons (ev1 : eventval) (evl : List eventval)
      (ty1 : typ) (tyl : List typ) (v1 : val) (vl : List val)
      (head : eventval_match ge ev1 ty1 v1)
      (tail : eventval_list_match ge evl tyl vl) :
      eventval_list_match ge (ev1 :: evl) (ty1 :: tyl) (v1 :: vl)

export eventval_list_match (evl_match_nil evl_match_cons)

def eventval_valid (ge : Senv.t) (ev : eventval) : Prop :=
  match ev with
  | EVint _ => True
  | EVlong _ => True
  | EVfloat _ => True
  | EVsingle _ => True
  | EVptr_global id _ => Senv.public_symbol ge id = true

def eventval_type (ev : eventval) : typ :=
  match ev with
  | EVint _ => Tint
  | EVlong _ => Tlong
  | EVfloat _ => Tfloat
  | EVsingle _ => Tsingle
  | EVptr_global _ _ => Tptr

/-! ## Compatibility with memory injections -/

def symbols_inject (f : meminj) (ge1 ge2 : Senv.t) : Prop :=
  (∀ id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id) ∧
  (∀ id b1 b2 delta,
    f b1 = some (b2, delta) →
    Senv.find_symbol ge1 id = some b1 →
    delta = ZArith.BinInt.Z.Z0 ∧ Senv.find_symbol ge2 id = some b2) ∧
  (∀ id b1,
    Senv.public_symbol ge1 id = true →
    Senv.find_symbol ge1 id = some b1 →
    ∃ b2, f b1 = some (b2, ZArith.BinInt.Z.Z0) ∧
      Senv.find_symbol ge2 id = some b2) ∧
  (∀ b1 b2 delta,
    f b1 = some (b2, delta) →
    Senv.block_is_volatile ge2 b2 = Senv.block_is_volatile ge1 b1)

/-! ## Matching traces -/

inductive match_traces (ge : Senv.t) : trace → trace → Prop where
  | match_traces_E0 : match_traces ge [] []
  | match_traces_syscall (id : RocqString) (args : List eventval)
      (res1 res2 : eventval)
      (valid1 : eventval_valid ge res1)
      (valid2 : eventval_valid ge res2)
      (same_type : eventval_type res1 = eventval_type res2) :
      match_traces ge [Event_syscall id args res1] [Event_syscall id args res2]
  | match_traces_vload (chunk : memory_chunk) (id : ident) (ofs : Ptrofs)
      (res1 res2 : eventval)
      (valid1 : eventval_valid ge res1)
      (valid2 : eventval_valid ge res2)
      (same_type : eventval_type res1 = eventval_type res2) :
      match_traces ge [Event_vload chunk id ofs res1] [Event_vload chunk id ofs res2]
  | match_traces_vstore (chunk : memory_chunk) (id : ident) (ofs : Ptrofs)
      (arg : eventval) :
      match_traces ge [Event_vstore chunk id ofs arg] [Event_vstore chunk id ofs arg]
  | match_traces_annot (id : RocqString) (args : List eventval) :
      match_traces ge [Event_annot id args] [Event_annot id args]

export match_traces
  (match_traces_E0 match_traces_syscall match_traces_vload
    match_traces_vstore match_traces_annot)

/-! ## External-call semantics -/

def extcall_sem : Type :=
  Senv.t → List val → mem → trace → val → mem → Prop

def loc_out_of_bounds (m : mem) (b : block) (ofs : Z) : Prop :=
  ¬ Mem.perm m b ofs Max Nonempty

def loc_unmapped (f : meminj) (b : block) (_ofs : Z) : Prop :=
  f b = none

def loc_out_of_reach (f : meminj) (m : mem) (b : block) (ofs : Z) : Prop :=
  ∀ b0 delta,
    f b0 = some (b, delta) →
    ¬ Mem.perm m b0 (zSub ofs delta) Max Nonempty

def inject_separated (f f' : meminj) (m1 m2 : mem) : Prop :=
  ∀ b1 b2 delta,
    f b1 = none →
    f' b1 = some (b2, delta) →
    ¬ Mem.valid_block m1 b1 ∧ ¬ Mem.valid_block m2 b2

structure extcall_properties (sem : extcall_sem) (sg : signature) : Prop where
  ec_well_typed :
    ∀ ge vargs m1 t vres m2,
      sem ge vargs m1 t vres m2 →
      Val.has_rettype vres sg.sig_res

  ec_symbols_preserved :
    ∀ ge1 ge2 vargs m1 t vres m2,
      Senv.equiv ge1 ge2 →
      sem ge1 vargs m1 t vres m2 →
      sem ge2 vargs m1 t vres m2

  ec_valid_block :
    ∀ ge vargs m1 t vres m2 b,
      sem ge vargs m1 t vres m2 →
      Mem.valid_block m1 b →
      Mem.valid_block m2 b

  ec_max_perm :
    ∀ ge vargs m1 t vres m2 b ofs p,
      sem ge vargs m1 t vres m2 →
      Mem.valid_block m1 b →
      Mem.perm m2 b ofs Max p →
      Mem.perm m1 b ofs Max p

  ec_readonly :
    ∀ ge vargs m1 t vres m2 b ofs n bytes,
      sem ge vargs m1 t vres m2 →
      Mem.valid_block m1 b →
      Mem.loadbytes m2 b ofs n = some bytes →
      (∀ i, zLe ofs i ∧ zLt i (zAdd ofs n) →
        ¬ Mem.perm m1 b i Max Writable) →
      Mem.loadbytes m1 b ofs n = some bytes

  ec_mem_extends :
    ∀ ge vargs m1 t vres m2 m1' vargs',
      sem ge vargs m1 t vres m2 →
      Mem.«extends» m1 m1' →
      Val.lessdef_list vargs vargs' →
      ∃ vres' m2',
        sem ge vargs' m1' t vres' m2' ∧
        Val.lessdef vres vres' ∧
        Mem.«extends» m2 m2' ∧
        Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'

  ec_mem_inject :
    ∀ ge1 ge2 vargs m1 t vres m2 f m1' vargs',
      symbols_inject f ge1 ge2 →
      sem ge1 vargs m1 t vres m2 →
      Mem.inject f m1 m1' →
      Val.inject_list f vargs vargs' →
      ∃ f' vres' m2',
        sem ge2 vargs' m1' t vres' m2' ∧
        Val.inject f' vres vres' ∧
        Mem.inject f' m2 m2' ∧
        Mem.unchanged_on (loc_unmapped f) m1 m2 ∧
        Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' ∧
        inject_incr f f' ∧
        inject_separated f f' m1 m1'

  ec_trace_length :
    ∀ ge vargs m t vres m',
      sem ge vargs m t vres m' →
      t.length ≤ 1

  ec_receptive :
    ∀ ge vargs m t1 vres1 m1 t2,
      sem ge vargs m t1 vres1 m1 →
      match_traces ge t1 t2 →
      ∃ vres2 m2, sem ge vargs m t2 vres2 m2

  ec_determ :
    ∀ ge vargs m t1 vres1 m1 t2 vres2 m2,
      sem ge vargs m t1 vres1 m1 →
      sem ge vargs m t2 vres2 m2 →
      match_traces ge t1 t2 ∧
        (t1 = t2 → vres1 = vres2 ∧ m1 = m2)

export extcall_properties
  (ec_well_typed ec_symbols_preserved ec_valid_block ec_max_perm ec_readonly
    ec_mem_extends ec_mem_inject ec_trace_length ec_receptive ec_determ)

end CompCert4Lean.Common.Events
