import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Stacking
import CompCert4Lean.Backend.Lineartyping
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Separation
import CompCert4Lean.Common.Linking

/-!
# Correctness surface for the Linear-to-Mach stacking pass

The executable declarations in this module are the source-shaped data and
relations owned by the stacking proof packet.  Proof-bearing source lemmas
are reserved below as transparent proposition descriptors for the later proof
migration phase.
-/

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Lineartyping
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Separation
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Conventions1
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.Stacklayout

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev locset := CompCert4Lean.Backend.Linear.locset
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev z0 : Z := .Z0
private abbrev z4 : Z := ZArith.BinInt.Z.of_nat 4
private abbrev z8 : Z := ZArith.BinInt.Z.of_nat 8
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zDivide := ZArith.BinInt.Z.divide

private theorem validBlockOfPerm {m : mem} {b : block} {ofs : Z}
    {k : CompCert4Lean.Common.Memtype.perm_kind}
    {p : CompCert4Lean.Common.Memtype.permission} (h : Mem.perm m b ofs k p) :
    Mem.valid_block m b := by
  by_cases hb : Mem.valid_block m b
  · exact hb
  · have hn := m.nextblock_noaccess b ofs k hb
    have : False := by simpa [Mem.perm, Mem.perm_order', hn] using h
    exact this.elim

private theorem locationChunkSize (ty : typ) :
    intOfZ (size_chunk (chunk_of_type ty)) =
      4 * intOfZ (CompCert4Lean.Backend.Locations.typesize ty) := by
  cases ty <;> rfl

private theorem locationAddrNonneg (pos ofs : Z)
    (hpos : zLe z0 pos) (hofs : zLe z0 ofs) :
    zLe z0 (zAdd pos (zMul z4 ofs)) := by
  unfold zLe ZArith.BinInt.Z.le at hpos hofs ⊢
  unfold zAdd ZArith.BinInt.Z.add
  unfold zMul ZArith.BinInt.Z.mul
  repeat rw [intOfZ_zOfInt]
  have hz0 : intOfZ z0 = 0 := rfl
  have hz4 : intOfZ z4 = 4 := rfl
  rw [hz0] at hpos hofs ⊢
  rw [hz4]
  omega

private theorem locationAddrMax (pos bound ofs : Z) (ty : typ)
    (hover : zLe (zAdd pos (zMul z4 bound)) Ptrofs.modulus)
    (hbound : zLe
      (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) bound) :
    zLe (zAdd pos (zMul z4 ofs)) Ptrofs.max_unsigned := by
  change intOfZ (zAdd pos (zMul z4 ofs)) ≤
    intOfZ (ZArith.BinInt.Z.sub Ptrofs.modulus (ZArith.BinInt.Z.of_nat 1))
  unfold ZArith.BinInt.Z.sub
  rw [intOfZ_zOfInt]
  change intOfZ (zAdd pos (zMul z4 ofs)) ≤ intOfZ Ptrofs.modulus - 1
  unfold zLe ZArith.BinInt.Z.le at hover hbound
  unfold zAdd ZArith.BinInt.Z.add at hover hbound ⊢
  unfold zMul ZArith.BinInt.Z.mul at hover ⊢
  rw [intOfZ_zOfInt] at hover hbound ⊢
  rw [intOfZ_zOfInt] at hover ⊢
  have hz1 : intOfZ (ZArith.BinInt.Z.of_nat 1) = 1 := rfl
  have hz2 : intOfZ (ZArith.BinInt.Z.of_nat 2) = 2 := rfl
  have hz4 : intOfZ z4 = 4 := rfl
  rw [hz4] at hover ⊢
  cases ty <;>
    simp only [CompCert4Lean.Backend.Locations.typesize] at hbound
  all_goals first | rw [hz1] at hbound | rw [hz2] at hbound
  all_goals omega

private theorem locationChunkRange (pos bound ofs i : Z) (ty : typ)
    (hofs : zLe z0 ofs)
    (hbound : zLe
      (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) bound)
    (hi : zLe (zAdd pos (zMul z4 ofs)) i ∧
      zLt i (zAdd (zAdd pos (zMul z4 ofs))
        (size_chunk (chunk_of_type ty)))) :
    zLe pos i ∧ zLt i (zAdd pos (zMul z4 bound)) := by
  rcases hi with ⟨hlo, hhi⟩
  have hz0 : intOfZ z0 = 0 := rfl
  have hz4 : intOfZ z4 = 4 := rfl
  constructor
  · unfold zLe ZArith.BinInt.Z.le at hlo ⊢
    unfold zAdd ZArith.BinInt.Z.add at hlo
    unfold zMul ZArith.BinInt.Z.mul at hlo
    repeat rw [intOfZ_zOfInt] at hlo
    rw [hz4] at hlo
    unfold zLe ZArith.BinInt.Z.le at hofs
    rw [hz0] at hofs
    omega
  · unfold zLt ZArith.BinInt.Z.lt at hhi ⊢
    unfold zAdd ZArith.BinInt.Z.add at hhi ⊢
    unfold zMul ZArith.BinInt.Z.mul at hhi ⊢
    repeat rw [intOfZ_zOfInt] at hhi ⊢
    rw [hz4] at hhi ⊢
    rw [locationChunkSize ty] at hhi
    repeat rw [intOfZ_zOfInt] at hhi
    unfold zLe ZArith.BinInt.Z.le at hbound
    unfold zAdd ZArith.BinInt.Z.add at hbound
    rw [intOfZ_zOfInt] at hbound
    omega

private theorem locationAligned (pos ofs : Z) (ty : typ)
    (hpos : zDivide z8 pos)
    (hofs : zDivide (CompCert4Lean.Backend.Locations.typealign ty) ofs) :
    zDivide (align_chunk (chunk_of_type ty)) (zAdd pos (zMul z4 ofs)) := by
  rcases hpos with ⟨k, hk⟩
  rcases hofs with ⟨q, hq⟩
  have hk' := congrArg intOfZ hk
  unfold ZArith.BinInt.Z.mul at hk'
  rw [intOfZ_zOfInt] at hk'
  change intOfZ pos = 8 * intOfZ k at hk'
  have hz2 : intOfZ (ZArith.BinInt.Z.of_nat 2) = 2 := rfl
  have hz4 : intOfZ z4 = 4 := rfl
  have hz8 : intOfZ z8 = 8 := rfl
  cases ty
  case Tlong =>
    change zDivide z8 _
    change ofs = zMul (ZArith.BinInt.Z.of_nat 2) q at hq
    have hq' := congrArg intOfZ hq
    unfold zMul ZArith.BinInt.Z.mul at hq'
    rw [intOfZ_zOfInt, hz2] at hq'
    refine ⟨zAdd k q, ?_⟩
    apply intOfZ_injective
    unfold zAdd zMul ZArith.BinInt.Z.add ZArith.BinInt.Z.mul
    repeat rw [intOfZ_zOfInt]
    rw [hz4, hz8]
    omega
  all_goals
    change zDivide z4 _
    refine ⟨zAdd (zMul (ZArith.BinInt.Z.of_nat 2) k) ofs, ?_⟩
    apply intOfZ_injective
    unfold zAdd zMul ZArith.BinInt.Z.add ZArith.BinInt.Z.mul
    repeat rw [intOfZ_zOfInt]
    rw [hz2, hz4]
    omega

/-! Program matching -/

def match_prog (cfg : CompilerConfig) (p : Linear.program) (tp : Mach.program) : Prop :=
  @match_program Linear.fundef Unit Mach.fundef Unit
    (Linker_fundef Linear.function) Linker_unit
    (fun _ f tf => transf_fundef cfg f = .OK tf)
    (fun x y : Unit => x = y) p tp

/-! Memory assertions used by the frame relation. -/

def contains_locations
    (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) (j : meminj) (sp : block) (pos bound : Z)
    (sl : slot) (ls : locset) : massert :=
  { m_pred := fun m =>
      zDivide z8 pos ∧ zLe z0 pos ∧
      zLe (zAdd pos (zMul z4 bound)) Ptrofs.modulus ∧
      Mem.range_perm m sp pos (zAdd pos (zMul z4 bound)) Cur Freeable ∧
      ∀ ofs ty, zLe z0 ofs →
        zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) bound →
        zDivide (CompCert4Lean.Backend.Locations.typealign ty) ofs →
        ∃ v,
          Mem.load (chunk_of_type ty) m sp (zAdd pos (zMul z4 ofs)) = some v ∧
          Val.inject j (ls (S sl ofs ty)) v
    m_footprint := fun b ofs =>
      b = sp ∧ zLe pos ofs ∧ zLt ofs (zAdd pos (zMul z4 bound))
    m_invar := by
      intro m m' h hunch
      rcases h with ⟨hdiv, hpos, hover, hperm, hload⟩
      refine ⟨hdiv, hpos, hover, ?_, ?_⟩
      · intro ofs hofs
        have hp := hperm ofs hofs
        have hb := validBlockOfPerm hp
        exact (hunch.unchanged_on_perm sp ofs Cur Freeable
          ⟨rfl, hofs.1, hofs.2⟩ hb).mp hp
      · intro ofs ty hofs hbound halign
        rcases hload ofs ty hofs hbound halign with ⟨v, hv, hinj⟩
        let addr := zAdd pos (zMul z4 ofs)
        let spec : val → Prop := fun v' => Val.inject j (ls (S sl ofs ty)) v'
        have haddr0 : zLe z0 addr := locationAddrNonneg pos ofs hpos hofs
        have haddrmax : zLe addr Ptrofs.max_unsigned :=
          locationAddrMax pos bound ofs ty hover hbound
        have hvalid : Mem.valid_access m (chunk_of_type ty) sp addr Freeable := by
          refine ⟨?_, ?_⟩
          · intro i hi
            exact hperm i (locationChunkRange pos bound ofs i ty hofs hbound hi)
          · exact locationAligned pos ofs ty hdiv halign
        have hc : (contains (chunk_of_type ty) sp addr spec).m_pred m :=
          ⟨⟨haddr0, haddrmax⟩, hvalid, v, hv, hinj⟩
        have hunch' : Mem.unchanged_on
            (contains (chunk_of_type ty) sp addr spec).m_footprint m m' := by
          exact {
            unchanged_on_nextblock := hunch.unchanged_on_nextblock
            unchanged_on_perm := by
              intro b i k p hi hb
              exact hunch.unchanged_on_perm b i k p (by
                rcases hi with ⟨rfl, hlo, hhi⟩
                exact ⟨rfl, locationChunkRange pos bound ofs i ty hofs hbound
                  ⟨hlo, hhi⟩⟩) hb
            unchanged_on_contents := by
              intro b i hi hp
              exact hunch.unchanged_on_contents b i (by
                rcases hi with ⟨rfl, hlo, hhi⟩
                exact ⟨rfl, locationChunkRange pos bound ofs i ty hofs hbound
                  ⟨hlo, hhi⟩⟩) hp
          }
        rcases (contains (chunk_of_type ty) sp addr spec).m_invar m m' hc hunch' with
          ⟨⟨_, _⟩, _, v', hv', hinj'⟩
        exact ⟨v', hv', hinj'⟩
    m_valid := by
      intro m b ofs h hfoot
      rcases hfoot with ⟨rfl, hlo, hhi⟩
      exact validBlockOfPerm (h.2.2.2.1 ofs ⟨hlo, hhi⟩) }

/-! Rocq `Program` obligations retained as exact proposition surfaces.  The
executable assertion above owns the carrier; these names keep its two
generated proof duties available to the later proof phase. -/

def contains_locations_obligation_1Statement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) j sp pos bound sl ls m m',
    (contains_locations return_address_offset tprog j sp pos bound sl ls).m_pred m →
    Mem.unchanged_on
      (fun b ofs =>
        b = sp ∧ zLe pos ofs ∧ zLt ofs (zAdd pos (zMul z4 bound))) m m' →
    (contains_locations return_address_offset tprog j sp pos bound sl ls).m_pred m'

def contains_locations_obligation_2Statement : Prop :=
  ∀ (j : meminj) (sp : block) (pos bound : Z) (sl : slot) (ls : locset)
    (m : mem) (b : block) (ofs : Z),
    (zDivide z8 pos ∧ zLe z0 pos ∧
      zLe (zAdd pos (zMul z4 bound)) Ptrofs.modulus ∧
      Mem.range_perm m sp pos (zAdd pos (zMul z4 bound)) Cur Freeable ∧
      ∀ ofs ty, zLe z0 ofs →
        zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) bound →
        zDivide (CompCert4Lean.Backend.Locations.typealign ty) ofs →
        ∃ v,
          Mem.load (chunk_of_type ty) m sp (zAdd pos (zMul z4 ofs)) = some v ∧
          Val.inject j (ls (S sl ofs ty)) v) →
    (b = sp ∧ zLe pos ofs ∧ zLt ofs (zAdd pos (zMul z4 bound))) →
    Mem.valid_block m b

def contains_callee_saves (j : meminj) (sp : block) (pos : Z)
    (rl : List mreg) (ls : locset) : massert :=
  match rl with
  | [] => pure True
  | r :: rs =>
      let ty := mreg_type r
      let sz := CompCert4Lean.Common.AST.typesize ty
      let pos' := align pos sz
      sepconj
        (contains (chunk_of_type ty) sp pos'
          (fun v => Val.inject j (ls (R r)) v))
        (contains_callee_saves j sp (ZArith.BinInt.Z.add pos' sz) rs ls)

/-! Frame assertions.  The configuration and source function are explicit in
Lean because the target ABI is an immutable parameter. -/

def frame_contents_1
    (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) (cfg : CompilerConfig) (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    (j : meminj) (sp : block) (ls ls0 : locset) (parent retaddr : val) : massert :=
  let b := function_bounds cfg f
  let fe := make_env cfg b
  sepconj (contains_locations return_address_offset tprog j sp fe.fe_ofs_local b.bound_local Local ls)
    (sepconj (contains_locations return_address_offset tprog j sp (fe_ofs_arg cfg) b.bound_outgoing Outgoing ls)
      (sepconj (hasvalue Mptr sp fe.fe_ofs_link parent)
        (sepconj (hasvalue Mptr sp fe.fe_ofs_retaddr retaddr)
          (contains_callee_saves j sp fe.fe_ofs_callee_save
            b.used_callee_save ls0))))

def frame_contents
    (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) (cfg : CompilerConfig) (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    (j : meminj) (sp : block) (ls ls0 : locset) (parent retaddr : val) : massert :=
  let b := function_bounds cfg f
  let fe := make_env cfg b
  mconj (frame_contents_1 return_address_offset tprog cfg f
    _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
    _used_callee_save_norepet _used_callee_save_prop j sp ls ls0 parent retaddr)
    (sepconj (range sp .Z0 fe.fe_stack_data)
      (range sp (ZArith.BinInt.Z.add fe.fe_stack_data b.bound_stack_data) fe.fe_size))

/-! Agreement relations. -/

def agree_regs (j : meminj) (ls : locset) (rs : regset) : Prop :=
  ∀ r, Val.inject j (ls (R r)) (rs r)

/-! The source record is declared inside `FRAME_PROPERTIES`, where `f` is a
section variable and `b` is the local definition `function_bounds f`; it is
not an independent carrier parameter.  The immutable ABI configuration is
explicit here, so every field and descriptor below closes over the same
source-shaped `cfg`/`f` carrier.  The exported `agree_unused_reg` projection
and `mk_agree_locs` constructor are the generated surfaces owned by this
carrier (source `backend/Stackingproof.v`, lines 563--570; projection span
21461--21667).  Out-of-closure proof declarations remain deferred rather than
being materialized as carrier implementations or statement descriptors here. -/

structure agree_locs (cfg : CompilerConfig) (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    (ls ls0 : locset) : Prop where
  agree_unused_reg :
    ∀ r, ¬ mreg_within_bounds cfg (function_bounds cfg f) r →
      ls (R r) = ls0 (R r)
  agree_incoming :
    ∀ ofs ty,
      S Incoming ofs ty ∈ regs_of_rpairs (loc_parameters cfg f.fn_sig) →
      ls (S Incoming ofs ty) = ls0 (S Outgoing ofs ty)

export agree_locs (agree_unused_reg agree_incoming)

/-! Stable top-level identity for Rocq's record constructor. -/

abbrev mk_agree_locs (f : Linear.function)
    {cfg : CompilerConfig}
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    (ls ls0 : locset)
    (agree_unused_reg : ∀ r,
      ¬ mreg_within_bounds cfg (function_bounds cfg f) r →
      ls (R r) = ls0 (R r))
    (agree_incoming : ∀ ofs ty,
      S Incoming ofs ty ∈ regs_of_rpairs (loc_parameters cfg f.fn_sig) →
      ls (S Incoming ofs ty) = ls0 (S Outgoing ofs ty)) :
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop ls ls0 :=
  @agree_locs.mk cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
    _used_callee_save_norepet _used_callee_save_prop ls ls0 agree_unused_reg agree_incoming

/-! `agree_unused` is declared in the nested `RESTORE_CALLEE_SAVE` section
while still generalized over the outer `f`/`b := function_bounds f`; keep
that source section parameter explicit and do not expose a free `bounds`
argument.  The restore descriptors below retain this same carrier identity;
the separately deferred restore proofs remain statement surfaces only. -/

def agree_unused (cfg : CompilerConfig) (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    (j : meminj) (ls0 : locset) (rs : regset) : Prop :=
  ∀ r, ¬ mreg_within_bounds cfg (function_bounds cfg f) r →
    Val.inject j (ls0 (R r)) (rs r)

def no_callee_saves (cfg : CompilerConfig) (l : List mreg) : Prop :=
  List.any l (fun r => is_callee_save cfg r) = false

/-! Call-stack and state relations. -/

def stack_contents
    (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) (cfg : CompilerConfig) (j : meminj) (cs : List Linear.stackframe)
    (cs' : List Mach.stackframe)
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)) : massert :=
  match cs, cs' with
  | [], [] => pure True
  | Linear.Stackframe f _ ls _ :: cs,
      Mach.Stackframe _ (Vptr sp' _) _ _ :: cs' =>
      sepconj
        (frame_contents return_address_offset tprog cfg f
          (_bound_local_pos f) (_bound_outgoing_pos f) (_bound_stack_data_pos f)
          (_used_callee_save_norepet f) (_used_callee_save_prop f)
          j sp' ls (Linear.parent_locset cs)
          (Mach.parent_sp cs') (Mach.parent_ra cs'))
        (stack_contents return_address_offset tprog cfg j cs cs'
          _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
          _used_callee_save_norepet _used_callee_save_prop)
  | _, _ => pure False

inductive match_stacks (cfg : CompilerConfig) (tprog : Mach.program) (j : meminj)
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)) :
    List Linear.stackframe → List Mach.stackframe → signature → Prop where
  | match_stacks_empty (sg : signature)
      (htail : tailcall_possible cfg sg) :
      match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
        _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop [] [] sg
  | match_stacks_cons (f : Linear.function) (sp : block) (ls : locset)
      (c : Linear.code) (cs : List Linear.stackframe) (fb sp' : block)
      (ra : val) (c' : Mach.code) (cs' : List Mach.stackframe)
      (sg : signature) (trf : Mach.function)
      (htail : is_tail c f.fn_code)
      (hfind : Genv.find_funct_ptr (Genv.globalenv tprog) fb = some (.Internal trf))
      (htransf : transf_function cfg f = .OK trf)
      (hcode : transl_code cfg (make_env cfg (function_bounds cfg f)) c = c')
      (hinj : j sp = some (sp', (make_env cfg (function_bounds cfg f)).fe_stack_data))
      (hra : Val.has_type ra Tptr)
      (hlocs : agree_locs cfg f (_bound_local_pos f) (_bound_outgoing_pos f)
        (_bound_stack_data_pos f) (_used_callee_save_norepet f) (_used_callee_save_prop f)
        ls (Linear.parent_locset cs))
      (hargs : ∀ ofs ty,
        S Outgoing ofs ty ∈ regs_of_rpairs (loc_arguments cfg sg) →
          slot_within_bounds (function_bounds cfg f) Outgoing ofs ty)
      (hstacks : match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
        _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' f.fn_sig) :
      match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
        _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop
        (Linear.Stackframe f (Vptr sp Ptrofs.zero) ls c :: cs)
        (Mach.Stackframe fb (Vptr sp' Ptrofs.zero) ra c' :: cs') sg

/-! Stable top-level identities for the two source constructors. -/

abbrev match_stacks_empty {cfg : CompilerConfig} {tprog : Mach.program}
    {j : meminj}
    (bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f))
    (sg : signature) (htail : tailcall_possible cfg sg) :
    match_stacks cfg tprog j bound_local_pos bound_outgoing_pos
      bound_stack_data_pos used_callee_save_norepet used_callee_save_prop [] [] sg :=
  @match_stacks.match_stacks_empty cfg tprog j bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop sg htail

abbrev match_stacks_cons {cfg : CompilerConfig} {tprog : Mach.program}
    {j : meminj}
    (bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f))
    (f : Linear.function) (sp : block) (ls : locset)
    (c : Linear.code) (cs : List Linear.stackframe) (fb sp' : block)
    (ra : val) (c' : Mach.code) (cs' : List Mach.stackframe)
    (sg : signature) (trf : Mach.function)
    (htail : is_tail c f.fn_code)
    (hfind : Genv.find_funct_ptr (Genv.globalenv tprog) fb = some (.Internal trf))
    (htransf : transf_function cfg f = .OK trf)
    (hcode : transl_code cfg (make_env cfg (function_bounds cfg f)) c = c')
    (hinj : j sp = some (sp', (make_env cfg (function_bounds cfg f)).fe_stack_data))
    (hra : Val.has_type ra Tptr)
    (hlocs : agree_locs cfg f (bound_local_pos f) (bound_outgoing_pos f)
      (bound_stack_data_pos f) (used_callee_save_norepet f) (used_callee_save_prop f)
      ls (Linear.parent_locset cs))
    (hargs : ∀ ofs ty,
      S Outgoing ofs ty ∈ regs_of_rpairs (loc_arguments cfg sg) →
        slot_within_bounds (function_bounds cfg f) Outgoing ofs ty)
    (hstacks : match_stacks cfg tprog j bound_local_pos bound_outgoing_pos
      bound_stack_data_pos used_callee_save_norepet used_callee_save_prop cs cs' f.fn_sig) :
    match_stacks cfg tprog j bound_local_pos bound_outgoing_pos
      bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
      (Linear.Stackframe f (Vptr sp Ptrofs.zero) ls c :: cs)
      (Mach.Stackframe fb (Vptr sp' Ptrofs.zero) ra c' :: cs') sg :=
  @match_stacks.match_stacks_cons cfg tprog j bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
    f sp ls c cs fb sp' ra c' cs' sg trf
    htail hfind htransf hcode hinj hra hlocs hargs hstacks

inductive match_states (cfg : CompilerConfig)
    (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (prog : Linear.program) (tprog : Mach.program)
    (bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)) :
    Linear.state → Mach.state → Prop where
  | match_states_intro (cs : List Linear.stackframe) (f : Linear.function)
      (sp : block) (c : Linear.code) (ls : locset) (m : mem)
      (cs' : List Mach.stackframe) (fb sp' : block) (rs : regset) (m' : mem)
      (j : meminj) (tf : Mach.function)
      (hstacks : match_stacks cfg tprog j bound_local_pos bound_outgoing_pos
        bound_stack_data_pos used_callee_save_norepet used_callee_save_prop cs cs' f.fn_sig)
      (htransf : transf_function cfg f = .OK tf)
      (hfind : Genv.find_funct_ptr (Genv.globalenv tprog) fb = some (.Internal tf))
      (hregs : agree_regs j ls rs)
      (hlocs : agree_locs cfg f (bound_local_pos f) (bound_outgoing_pos f)
        (bound_stack_data_pos f) (used_callee_save_norepet f) (used_callee_save_prop f)
        ls (Linear.parent_locset cs))
      (hinj : j sp = some (sp', (make_env cfg (function_bounds cfg f)).fe_stack_data))
      (htail : is_tail c f.fn_code)
      (hsep : (sepconj
          (frame_contents return_address_offset tprog cfg f
            (bound_local_pos f) (bound_outgoing_pos f) (bound_stack_data_pos f)
            (used_callee_save_norepet f) (used_callee_save_prop f)
            j sp' ls (Linear.parent_locset cs)
            (Mach.parent_sp cs') (Mach.parent_ra cs'))
        (sepconj (stack_contents return_address_offset tprog cfg j cs cs'
            bound_local_pos bound_outgoing_pos bound_stack_data_pos
            used_callee_save_norepet used_callee_save_prop)
          (sepconj (minjection j m)
            (globalenv_inject (Genv.globalenv prog) j)))).m_pred m') :
      match_states cfg return_address_offset prog tprog bound_local_pos bound_outgoing_pos
        bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
        (Linear.State cs f (Vptr sp Ptrofs.zero) c ls m)
        (Mach.State cs' fb (Vptr sp' Ptrofs.zero)
          (transl_code cfg (make_env cfg (function_bounds cfg f)) c) rs m')
  | match_states_call (cs : List Linear.stackframe) (f : Linear.fundef)
      (ls : locset) (m : mem) (cs' : List Mach.stackframe) (fb : block)
      (rs : regset) (m' : mem) (j : meminj) (tf : Mach.fundef)
      (hstacks : match_stacks cfg tprog j bound_local_pos bound_outgoing_pos
        bound_stack_data_pos used_callee_save_norepet used_callee_save_prop cs cs'
        (Linear.funsig f))
      (htransf : transf_fundef cfg f = .OK tf)
      (hfind : Genv.find_funct_ptr (Genv.globalenv tprog) fb = some tf)
      (hregs : agree_regs j ls rs)
      (hsep : (sepconj (stack_contents return_address_offset tprog cfg j cs cs'
          bound_local_pos bound_outgoing_pos bound_stack_data_pos
          used_callee_save_norepet used_callee_save_prop)
        (sepconj (minjection j m)
          (globalenv_inject (Genv.globalenv prog) j))).m_pred m') :
      match_states cfg return_address_offset prog tprog bound_local_pos bound_outgoing_pos
        bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
        (Linear.Callstate cs f ls m) (Mach.Callstate cs' fb rs m')
  | match_states_return (cs : List Linear.stackframe) (ls : locset) (m : mem)
      (cs' : List Mach.stackframe) (rs : regset) (m' : mem) (j : meminj)
      (sg : signature)
      (hstacks : match_stacks cfg tprog j bound_local_pos bound_outgoing_pos
        bound_stack_data_pos used_callee_save_norepet used_callee_save_prop cs cs' sg)
      (hregs : agree_regs j ls rs)
      (hsep : (sepconj (stack_contents return_address_offset tprog cfg j cs cs'
          bound_local_pos bound_outgoing_pos bound_stack_data_pos
          used_callee_save_norepet used_callee_save_prop)
        (sepconj (minjection j m)
          (globalenv_inject (Genv.globalenv prog) j))).m_pred m') :
      match_states cfg return_address_offset prog tprog bound_local_pos bound_outgoing_pos
        bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
        (Linear.Returnstate cs ls m) (Mach.Returnstate cs' rs m')

export match_states (match_states_intro match_states_call match_states_return)

/-! Exact declaration identities reserved for later proof migration. -/

def LTL_undef_regs_othersStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ r rl ls, r ∉ rl → LTL.undef_regs rl ls (R r) = ls (R r)

def LTL_undef_regs_sameStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ r rl ls, r ∈ rl → LTL.undef_regs rl ls (R r) = Vundef

def LTL_undef_regs_slotStatement : Prop :=
  ∀ sl ofs ty rl ls,
    LTL.undef_regs rl ls (S sl ofs ty) = ls (S sl ofs ty)

def agree_locs_returnStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ls ls0 ls',
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop ls ls0 →
    agree_callee_save cfg ls' ls →
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop ls' ls0

def agree_locs_set_regStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ls ls0 r v,
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop ls ls0 →
    mreg_within_bounds cfg (function_bounds cfg f) r →
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop (Locmap.set (R r) v ls) ls0

def agree_locs_set_resStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ls0 res v ls,
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop ls ls0 →
    (∀ r, r ∈ params_of_builtin_res res →
      mreg_within_bounds cfg (function_bounds cfg f) r) →
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop (Locmap.setres res v ls) ls0

def agree_locs_set_slotStatement : Prop :=
  ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ls ls0 sl ofs ty v,
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop ls ls0 →
    slot_writable sl = true →
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      (Locmap.set (S sl ofs ty) v ls) ls0

def agree_locs_undef_locsStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ls0 regs ls,
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop ls ls0 →
    List.any regs (is_callee_save cfg) = false →
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop (LTL.undef_regs regs ls) ls0

def agree_locs_undef_locs_1Statement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ls0 regs ls,
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop ls ls0 →
    (∀ r, r ∈ regs → is_callee_save cfg r = false) →
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop (LTL.undef_regs regs ls) ls0

def agree_locs_undef_regsStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ls0 regs ls,
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop ls ls0 →
    (∀ r, r ∈ regs →
      mreg_within_bounds cfg (function_bounds cfg f) r) →
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop (LTL.undef_regs regs ls) ls0

def agree_regStatement : Prop :=
  ∀ j ls rs r, agree_regs j ls rs → Val.inject j (ls (R r)) (rs r)

def agree_reglistStatement : Prop :=
  ∀ j ls rs rl, agree_regs j ls rs →
    Val.inject_list j (LTL.reglist ls rl) (rl.map rs)

def agree_regs_call_regsStatement : Prop :=
  ∀ j ls rs, agree_regs j ls rs → agree_regs j (LTL.call_regs ls) rs

def agree_regs_inject_incrStatement : Prop :=
  ∀ j ls rs j', agree_regs j ls rs → inject_incr j j' →
    agree_regs j' ls rs

def agree_regs_set_pairStatement : Prop :=
  ∀ j p v v' ls rs, agree_regs j ls rs → Val.inject j v v' →
    agree_regs j (Locmap.setpair p v ls) (Mach.set_pair p v' rs)

def agree_regs_set_regStatement : Prop :=
  ∀ j ls rs r v v', agree_regs j ls rs → Val.inject j v v' →
    agree_regs j (Locmap.set (R r) v ls) (Mach.Regmap.set r v' rs)

def agree_regs_set_resStatement : Prop :=
  ∀ j res v v' ls rs, agree_regs j ls rs → Val.inject j v v' →
    agree_regs j (Locmap.setres res v ls) (Mach.set_res res v' rs)

def agree_regs_set_slotStatement : Prop :=
  ∀ j ls rs sl ofs ty v, agree_regs j ls rs →
    agree_regs j (Locmap.set (S sl ofs ty) v ls) rs

def agree_regs_undef_caller_save_regsStatement : Prop :=
  ∀ cfg j ls rs, agree_regs j ls rs →
    agree_regs j (LTL.undef_caller_save_regs cfg ls)
      (Mach.undef_caller_save_regs cfg rs)

def agree_regs_undef_regsStatement : Prop :=
  ∀ j rl ls rs, agree_regs j ls rs →
    agree_regs j (LTL.undef_regs rl ls) (Mach.undef_regs rl rs)

def align_type_chunkStatement : Prop :=
  ∀ ty, align_chunk (chunk_of_type ty) =
    zMul z4 (CompCert4Lean.Backend.Locations.typealign ty)

def caller_save_reg_within_boundsStatement : Prop :=
  ∀ cfg f r, is_callee_save cfg r = false →
    mreg_within_bounds cfg (function_bounds cfg f) r

def contains_callee_saves_extenStatement : Prop :=
  ∀ j sp ls ls' rl pos,
    (∀ r, r ∈ rl → ls' (R r) = ls (R r)) →
    massert_eqv (contains_callee_saves j sp pos rl ls)
      (contains_callee_saves j sp pos rl ls')

def contains_callee_saves_incrStatement : Prop :=
  ∀ j j' sp ls, inject_incr j j' → ∀ rl pos,
    massert_imp (contains_callee_saves j sp pos rl ls)
      (contains_callee_saves j' sp pos rl ls)

def contains_get_stackStatement : Prop :=
  ∀ (spec : val → Prop) m ty sp ofs,
    (contains (chunk_of_type ty) sp ofs spec).m_pred m →
    ∃ v, Mach.load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) = some v ∧
      spec v

def contains_locations_extenStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ ls ls' j sp pos bound sl,
    (∀ ofs ty, Val.lessdef (ls' (S sl ofs ty)) (ls (S sl ofs ty))) →
    massert_imp (contains_locations return_address_offset tprog j sp pos bound sl ls)
      (contains_locations return_address_offset tprog j sp pos bound sl ls')

def contains_locations_incrStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ j j' sp pos bound sl ls, inject_incr j j' →
    massert_imp (contains_locations return_address_offset tprog j sp pos bound sl ls)
      (contains_locations return_address_offset tprog j' sp pos bound sl ls)

def contains_set_stackStatement : Prop :=
  ∀ (spec : val → Prop) v (spec1 : val → Prop) m ty sp ofs P,
    (sepconj (contains (chunk_of_type ty) sp ofs spec1) P).m_pred m →
    spec (Val.load_result (chunk_of_type ty) v) →
    ∃ m', Mach.store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) v = some m' ∧
      (sepconj (contains (chunk_of_type ty) sp ofs spec) P).m_pred m'

def destroyed_at_function_entry_caller_saveStatement : Prop :=
  ∀ cfg, no_callee_saves cfg destroyed_at_function_entry

def destroyed_by_cond_caller_saveStatement : Prop :=
  ∀ cfg cond, no_callee_saves cfg (destroyed_by_cond cond)

def destroyed_by_jumptable_caller_saveStatement : Prop :=
  ∀ cfg, no_callee_saves cfg destroyed_by_jumptable

def destroyed_by_load_caller_saveStatement : Prop :=
  ∀ cfg chunk addr, no_callee_saves cfg (destroyed_by_load chunk addr)

def destroyed_by_op_caller_saveStatement : Prop :=
  ∀ cfg op, no_callee_saves cfg (destroyed_by_op op)

def destroyed_by_setstack_caller_saveStatement : Prop :=
  ∀ cfg ty, no_callee_saves cfg (destroyed_by_setstack ty)

def destroyed_by_setstack_function_entryStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ ty r, r ∈ destroyed_by_setstack ty → r ∈ destroyed_at_function_entry

def destroyed_by_store_caller_saveStatement : Prop :=
  ∀ cfg chunk addr, no_callee_saves cfg (destroyed_by_store chunk addr)
def find_function_translatedStatement : Prop :=
  ∀ cfg (prog : Linear.program) (tprog : Mach.program),
    match_prog cfg prog tprog → ∀ j ls rs m ros f,
    agree_regs j ls rs →
    (globalenv_inject (Genv.globalenv prog) j).m_pred m →
    Linear.find_function (Genv.globalenv prog) ros ls = some f →
    ∃ bf tf,
      Mach.find_function_ptr (Genv.globalenv tprog) ros rs = some bf ∧
      Genv.find_funct_ptr (Genv.globalenv tprog) bf = some tf ∧
      transf_fundef cfg f = .OK tf

def find_label_restore_callee_saveStatement : Prop :=
  ∀ lbl l ofs k,
    Mach.find_label lbl (restore_callee_save_rec l ofs k) = Mach.find_label lbl k

def find_label_save_callee_saveStatement : Prop :=
  ∀ lbl l ofs k,
    Mach.find_label lbl (save_callee_save_rec l ofs k) = Mach.find_label lbl k

def find_label_tailStatement : Prop :=
  ∀ lbl c c', Linear.find_label lbl c = some c' → is_tail c' c

def find_label_transl_codeStatement : Prop :=
  ∀ cfg fe lbl c,
    Mach.find_label lbl (transl_code cfg fe c) =
      Option.map (transl_code cfg fe) (Linear.find_label lbl c)

def frame_contents_extenStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ls ls0 ls' ls0' j sp parent retaddr P m,
    (∀ ofs ty, Val.lessdef (ls' (S Local ofs ty)) (ls (S Local ofs ty))) →
    (∀ ofs ty, Val.lessdef (ls' (S Outgoing ofs ty)) (ls (S Outgoing ofs ty))) →
    (∀ r, r ∈ (function_bounds cfg f).used_callee_save →
      ls0' (R r) = ls0 (R r)) →
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 parent retaddr) P).m_pred m →
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls' ls0' parent retaddr) P).m_pred m

def frame_contents_incrStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    j sp ls ls0 parent retaddr m P j',
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 parent retaddr) P).m_pred m →
    inject_incr j j' →
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j' sp ls ls0 parent retaddr) P).m_pred m

def frame_get_localStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ofs ty j sp ls ls0 parent retaddr m P,
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 parent retaddr) P).m_pred m →
    slot_within_bounds (function_bounds cfg f) Local ofs ty →
    slot_valid cfg f Local ofs ty = true →
    ∃ v,
      Mach.load_stack m (Vptr sp Ptrofs.zero) ty
        (Ptrofs.repr (offset_local (make_env cfg (function_bounds cfg f)) ofs)) = some v ∧
      Val.inject j (ls (S Local ofs ty)) v

def frame_get_outgoingStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ofs ty j sp ls ls0 parent retaddr m P,
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 parent retaddr) P).m_pred m →
    slot_within_bounds (function_bounds cfg f) Outgoing ofs ty →
    slot_valid cfg f Outgoing ofs ty = true →
    ∃ v,
      Mach.load_stack m (Vptr sp Ptrofs.zero) ty
        (Ptrofs.repr (offset_arg cfg ofs)) = some v ∧
      Val.inject j (ls (S Outgoing ofs ty)) v

def frame_get_parentStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    j sp ls ls0 parent retaddr m P,
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 parent retaddr) P).m_pred m →
    Mach.load_stack m (Vptr sp Ptrofs.zero) Tptr
      (Ptrofs.repr (make_env cfg (function_bounds cfg f)).fe_ofs_link) = some parent

def frame_set_localStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ofs ty v v' j sp ls ls0 parent retaddr m P,
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 parent retaddr) P).m_pred m →
    slot_within_bounds (function_bounds cfg f) Local ofs ty →
    slot_valid cfg f Local ofs ty = true → Val.inject j v v' →
    ∃ m',
      Mach.store_stack m (Vptr sp Ptrofs.zero) ty
        (Ptrofs.repr (offset_local (make_env cfg (function_bounds cfg f)) ofs)) v' = some m' ∧
      (sepconj (frame_contents return_address_offset tprog cfg f
        _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
        _used_callee_save_norepet _used_callee_save_prop j sp
        (Locmap.set (S Local ofs ty) v ls) ls0 parent retaddr) P).m_pred m'

def frame_set_outgoingStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    ofs ty v v' j sp ls ls0 parent retaddr m P,
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 parent retaddr) P).m_pred m →
    slot_within_bounds (function_bounds cfg f) Outgoing ofs ty →
    slot_valid cfg f Outgoing ofs ty = true → Val.inject j v v' →
    ∃ m',
      Mach.store_stack m (Vptr sp Ptrofs.zero) ty
        (Ptrofs.repr (offset_arg cfg ofs)) v' = some m' ∧
      (sepconj (frame_contents return_address_offset tprog cfg f
        _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
        _used_callee_save_norepet _used_callee_save_prop j sp
        (Locmap.set (S Outgoing ofs ty) v ls) ls0 parent retaddr) P).m_pred m'

def frame_set_regStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    r v j sp ls ls0 parent retaddr m P,
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 parent retaddr) P).m_pred m →
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop j sp
      (Locmap.set (R r) v ls) ls0 parent retaddr) P).m_pred m

def frame_set_resStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    j sp ls0 parent retaddr m P res v ls,
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 parent retaddr) P).m_pred m →
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop j sp
      (Locmap.setres res v ls) ls0 parent retaddr) P).m_pred m

def frame_undef_regsStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg f
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    j sp ls ls0 parent retaddr m P rl,
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 parent retaddr) P).m_pred m →
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop j sp
      (LTL.undef_regs rl ls) ls0 parent retaddr) P).m_pred m
def function_epilogue_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cfg xi (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    (tf : Mach.function),
    transf_function cfg f = .OK tf →
    ∀ m' j sp' ls ls0 pa ra P m rs sp m1 k cs fb,
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp' ls ls0 pa ra)
      (sepconj (minjection j m) P)).m_pred m' →
    agree_regs j ls rs →
    agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop ls ls0 →
    j sp = some (sp', (make_env cfg (function_bounds cfg f)).fe_stack_data) →
    Mem.free m sp z0 f.fn_stacksize = some m1 →
    ∃ rs1 m1',
      Mach.load_stack m' (Vptr sp' Ptrofs.zero) Tptr tf.fn_link_ofs = some pa ∧
      Mach.load_stack m' (Vptr sp' Ptrofs.zero) Tptr tf.fn_retaddr_ofs = some ra ∧
      Mem.free m' sp' z0 tf.fn_stacksize = some m1' ∧
      star (Mach.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi return_address_offset) (Genv.globalenv tprog)
        (Mach.State cs fb (Vptr sp' Ptrofs.zero)
          (restore_callee_save (make_env cfg (function_bounds cfg f)) k) rs m')
        E0 (Mach.State cs fb (Vptr sp' Ptrofs.zero) k rs1 m') ∧
      agree_regs j (LTL.return_regs cfg ls0 ls) rs1 ∧
      agree_callee_save cfg (LTL.return_regs cfg ls0 ls) ls0 ∧
      (sepconj (minjection j m1) P).m_pred m1'

def function_prologue_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cfg xi (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (prog : Linear.program) (tprog : Mach.program)
    (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    (tf : Mach.function),
    transf_function cfg f = .OK tf →
    ∀ j ls ls0 ls1 rs rs1 m1 m1' m2 sp parent ra cs fb k P,
    agree_regs j ls rs →
    agree_callee_save cfg ls ls0 →
    agree_outgoing_arguments cfg f.fn_sig ls ls0 →
    (∀ r, Val.has_type (ls (R r)) (mreg_type r)) →
    ls1 = LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) →
    rs1 = Mach.undef_regs destroyed_at_function_entry rs →
    Mem.alloc m1 z0 f.fn_stacksize = (m2, sp) →
    Val.has_type parent Tptr → Val.has_type ra Tptr →
    (sepconj (minjection j m1)
      (sepconj (globalenv_inject (Genv.globalenv prog) j) P)).m_pred m1' →
    ∃ j' rs' m2' sp' m3' m4' m5',
      Mem.alloc m1' z0 tf.fn_stacksize = (m2', sp') ∧
      Mach.store_stack m2' (Vptr sp' Ptrofs.zero) Tptr tf.fn_link_ofs parent =
        some m3' ∧
      Mach.store_stack m3' (Vptr sp' Ptrofs.zero) Tptr tf.fn_retaddr_ofs ra =
        some m4' ∧
      star (Mach.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi return_address_offset) (Genv.globalenv tprog)
        (Mach.State cs fb (Vptr sp' Ptrofs.zero)
          (save_callee_save (make_env cfg (function_bounds cfg f)) k) rs1 m4')
        E0 (Mach.State cs fb (Vptr sp' Ptrofs.zero) k rs' m5') ∧
      agree_regs j' ls1 rs' ∧
      agree_locs cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
        _used_callee_save_norepet _used_callee_save_prop ls1 ls0 ∧
      (sepconj (frame_contents return_address_offset tprog cfg f
        _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
        _used_callee_save_norepet _used_callee_save_prop
        j' sp' ls1 ls0 parent ra)
        (sepconj (minjection j' m2)
          (sepconj (globalenv_inject (Genv.globalenv prog) j') P))).m_pred m5' ∧
      j' sp = some (sp', (make_env cfg (function_bounds cfg f)).fe_stack_data) ∧
      inject_incr j j'
def function_ptr_translatedStatement : Prop :=
  ∀ cfg (prog : Linear.program) (tprog : Mach.program),
    match_prog cfg prog tprog → ∀ b f,
    Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
    ∃ tf, Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
      transf_fundef cfg f = .OK tf

def get_locationStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ m j sp pos bound sl ls ofs ty,
    (contains_locations return_address_offset tprog j sp pos bound sl ls).m_pred m →
    zLe z0 ofs →
    zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) bound →
    zDivide (CompCert4Lean.Backend.Locations.typealign ty) ofs →
    ∃ v,
      Mach.load_stack m (Vptr sp Ptrofs.zero) ty
        (Ptrofs.repr (zAdd pos (zMul z4 ofs))) = some v ∧
      Val.inject j (ls (S sl ofs ty)) v

def hasvalue_get_stackStatement : Prop :=
  ∀ ty m sp ofs v,
    (hasvalue (chunk_of_type ty) sp ofs v).m_pred m →
    Mach.load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) = some v

def initial_locationsStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ j sp pos bound P sl ls m,
    (sepconj (range sp pos (zAdd pos (zMul z4 bound))) P).m_pred m →
    zDivide z8 pos →
    (∀ ofs ty, ls (S sl ofs ty) = Vundef) →
    (sepconj (contains_locations return_address_offset tprog j sp pos bound sl ls) P).m_pred m

def is_tail_restore_callee_saveStatement : Prop :=
  ∀ l ofs k, is_tail k (restore_callee_save_rec l ofs k)

def is_tail_save_callee_saveStatement : Prop :=
  ∀ l ofs k, is_tail k (save_callee_save_rec l ofs k)

def is_tail_transf_functionStatement : Prop :=
  ∀ cfg f tf c, transf_function cfg f = .OK tf →
    is_tail c f.fn_code →
    is_tail (transl_code cfg (make_env cfg (function_bounds cfg f)) c) tf.fn_code

def is_tail_transl_codeStatement : Prop :=
  ∀ cfg fe c1 c2, is_tail c1 c2 →
    is_tail (transl_code cfg fe c1) (transl_code cfg fe c2)

def is_tail_transl_instrStatement : Prop :=
  ∀ cfg fe i k, is_tail k (transl_instr cfg fe i k)

def load_result_injectStatement : Prop :=
  ∀ j ty v v', Val.inject j v v' → Val.has_type v ty →
    Val.inject j v (Val.load_result (chunk_of_type ty) v')

def match_stacks_change_meminjStatement : Prop :=
  ∀ cfg tprog j j'
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    inject_incr j j' → ∀ cs cs' sg,
    match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
      _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' sg →
    match_stacks cfg tprog j' _bound_local_pos _bound_outgoing_pos
      _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' sg

def match_stacks_change_sigStatement : Prop :=
  ∀ cfg tprog sg1 j
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    ∀ cs cs' sg,
    match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
      _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' sg →
    tailcall_possible cfg sg1 →
    match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
      _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' sg1

def match_stacks_type_retaddrStatement : Prop :=
  ∀ cfg tprog j
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    ∀ cs cs' sg,
    match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
      _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' sg →
    Val.has_type (Mach.parent_ra cs') Tptr

def match_stacks_type_spStatement : Prop :=
  ∀ cfg tprog j
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    ∀ cs cs' sg,
    match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
      _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' sg →
    Val.has_type (Mach.parent_sp cs') Tptr
def restore_callee_save_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cfg xi (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    m j sp ls ls0 pa ra P rs k cs fb,
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp ls ls0 pa ra) P).m_pred m →
    agree_unused cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop j ls0 rs →
    ∃ rs',
      star (Mach.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi return_address_offset) (Genv.globalenv tprog)
        (Mach.State cs fb (Vptr sp Ptrofs.zero)
          (restore_callee_save (make_env cfg (function_bounds cfg f)) k) rs m)
        E0 (Mach.State cs fb (Vptr sp Ptrofs.zero) k rs' m) ∧
      (∀ r, is_callee_save cfg r = true → Val.inject j (ls0 (R r)) (rs' r)) ∧
      (∀ r, is_callee_save cfg r = false → rs' r = rs r)

def restore_callee_save_rec_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cfg xi (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    j cs fb sp ls0 m l ofs rs k,
    (contains_callee_saves j sp ofs l ls0).m_pred m →
    agree_unused cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop j ls0 rs →
    (∀ r, r ∈ l → mreg_within_bounds cfg (function_bounds cfg f) r) →
    ∃ rs',
      star (Mach.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi return_address_offset) (Genv.globalenv tprog)
        (Mach.State cs fb (Vptr sp Ptrofs.zero)
          (restore_callee_save_rec l ofs k) rs m)
        E0 (Mach.State cs fb (Vptr sp Ptrofs.zero) k rs' m) ∧
      (∀ r, r ∈ l → Val.inject j (ls0 (R r)) (rs' r)) ∧
      (∀ r, r ∉ l → rs' r = rs r) ∧
      agree_unused cfg f _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
        _used_callee_save_norepet _used_callee_save_prop j ls0 rs'

def save_callee_save_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cfg xi (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    j ls ls0 rs sp cs fb k m P,
    (sepconj
      (range sp (make_env cfg (function_bounds cfg f)).fe_ofs_callee_save
        (size_callee_save_area cfg (function_bounds cfg f)
          (make_env cfg (function_bounds cfg f)).fe_ofs_callee_save)) P).m_pred m →
    (∀ r, Val.has_type (ls (R r)) (mreg_type r)) →
    agree_callee_save cfg ls ls0 → agree_regs j ls rs →
    let ls1 := LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls)
    let rs1 := Mach.undef_regs destroyed_at_function_entry rs
    ∃ rs' m',
      star (Mach.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi return_address_offset) (Genv.globalenv tprog)
        (Mach.State cs fb (Vptr sp Ptrofs.zero)
          (save_callee_save (make_env cfg (function_bounds cfg f)) k) rs1 m)
        E0 (Mach.State cs fb (Vptr sp Ptrofs.zero) k rs' m') ∧
      (sepconj (contains_callee_saves j sp
        (make_env cfg (function_bounds cfg f)).fe_ofs_callee_save
        (function_bounds cfg f).used_callee_save ls0) P).m_pred m' ∧
      (∀ ofs k p, Mem.perm m sp ofs k p → Mem.perm m' sp ofs k p) ∧
      agree_regs j ls1 rs'

def save_callee_save_rec_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cfg xi (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) j cs fb sp ls,
    (∀ ty r, r ∈ destroyed_by_setstack ty → ls (R r) = Vundef) →
    (∀ r, Val.has_type (ls (R r)) (mreg_type r)) →
    ∀ k l pos rs m P,
    (∀ r, r ∈ l → is_callee_save cfg r = true) →
    (sepconj (range sp pos (size_callee_save_area_rec l pos)) P).m_pred m →
    agree_regs j ls rs →
    ∃ rs' m',
      star (Mach.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi return_address_offset) (Genv.globalenv tprog)
        (Mach.State cs fb (Vptr sp Ptrofs.zero)
          (save_callee_save_rec l pos k) rs m)
        E0 (Mach.State cs fb (Vptr sp Ptrofs.zero) k rs' m') ∧
      (sepconj (contains_callee_saves j sp pos l ls) P).m_pred m' ∧
      (∀ ofs k p, Mem.perm m sp ofs k p → Mem.perm m' sp ofs k p) ∧
      agree_regs j ls rs'
def senv_preservedStatement : Prop :=
  ∀ cfg (prog : Linear.program) (tprog : Mach.program),
    match_prog cfg prog tprog →
    Senv.equiv (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def set_locationStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ m j sp pos bound sl ls P ofs ty v v',
    (sepconj (contains_locations return_address_offset tprog j sp pos bound sl ls) P).m_pred m →
    zLe z0 ofs →
    zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) bound →
    zDivide (CompCert4Lean.Backend.Locations.typealign ty) ofs →
    Val.inject j v v' →
    ∃ m',
      Mach.store_stack m (Vptr sp Ptrofs.zero) ty
        (Ptrofs.repr (zAdd pos (zMul z4 ofs))) v' = some m' ∧
      (sepconj (contains_locations return_address_offset tprog j sp pos bound sl
        (Locmap.set (S sl ofs ty) v ls)) P).m_pred m'

def simplify_load_correctStatement : Prop :=
  ∀ chunk m a v, Mem.loadv chunk m a = some v →
    ∃ v', Mem.loadv (simplify_load chunk) m a = some v' ∧ Val.lessdef v v'

def simplify_load_destroyedStatement : Prop :=
  ∀ chunk addr,
    destroyed_by_load (simplify_load chunk) addr = destroyed_by_load chunk addr

def simplify_store_correctStatement : Prop :=
  ∀ chunk m a v m', Mem.storev chunk m a v = some m' →
    Mem.storev (simplify_store chunk) m a v = some m'

def simplify_store_destroyedStatement : Prop :=
  ∀ chunk addr,
    destroyed_by_store (simplify_store chunk) addr = destroyed_by_store chunk addr

def size_no_overflowStatement : Prop :=
  ∀ cfg f tf, transf_function cfg f = .OK tf →
    zLe (make_env cfg (function_bounds cfg f)).fe_size Ptrofs.max_unsigned

def size_type_chunkStatement : Prop :=
  ∀ ty, size_chunk (chunk_of_type ty) = CompCert4Lean.Common.AST.typesize ty

def slot_outgoing_argument_validStatement : Prop :=
  ∀ cfg f ofs ty sg,
    S Outgoing ofs ty ∈ regs_of_rpairs (loc_arguments cfg sg) →
    slot_valid cfg f Outgoing ofs ty = true

def stack_contents_change_meminjStatement : Prop :=
  ∀ (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program),
    ∀ cfg m j j'
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    inject_incr j j' → ∀ cs cs' P,
    (sepconj (stack_contents return_address_offset tprog cfg j cs cs'
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop) P).m_pred m →
    (sepconj (stack_contents return_address_offset tprog cfg j' cs cs'
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop) P).m_pred m

def symbols_preservedStatement : Prop :=
  ∀ cfg (prog : Linear.program) (tprog : Mach.program),
    match_prog cfg prog tprog → ∀ s,
    Genv.find_symbol (Genv.globalenv tprog) s =
      Genv.find_symbol (Genv.globalenv prog) s
def transf_final_statesStatement : Prop :=
  ∀ cfg (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (prog : Linear.program) (tprog : Mach.program)
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f))
    st1 st2 r,
    match_states cfg return_address_offset prog tprog
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop st1 st2 →
    Linear.final_state st1 r →
    Mach.final_state st2 r

def transf_initial_statesStatement : Prop :=
  ∀ cfg (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (prog : Linear.program) (tprog : Mach.program)
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    match_prog cfg prog tprog → ∀ st1,
    Linear.initial_state prog st1 →
    ∃ st2, Mach.initial_state tprog st2 ∧
      match_states cfg return_address_offset prog tprog
        _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
        _used_callee_save_norepet _used_callee_save_prop st1 st2

def transf_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cfg xi (return_address_offset : Mach.function → Mach.code → ptrofs → Prop),
    (∀ f sg ros c, is_tail (.Mcall sg ros :: c) f.fn_code →
      ∃ ofs, return_address_offset f c ofs) →
    ∀ (prog : Linear.program) (tprog : Mach.program)
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    match_prog cfg prog tprog →
    forward_simulation
      (Linear.semantics cfg xi prog)
      (Mach.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi return_address_offset tprog)
def transf_program_matchStatement : Prop :=
  ∀ cfg p tp, transf_program cfg p = .OK tp → match_prog cfg p tp
def transf_step_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cfg xi (return_address_offset : Mach.function → Mach.code → ptrofs → Prop),
    (∀ f sg ros c, is_tail (.Mcall sg ros :: c) f.fn_code →
      ∃ ofs, return_address_offset f c ofs) →
    ∀ (prog : Linear.program) (tprog : Mach.program)
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    match_prog cfg prog tprog → ∀ s1 t s2,
    Linear.step cfg xi (Genv.globalenv prog) s1 t s2 →
    wt_state cfg s1 → ∀ s1',
    match_states cfg return_address_offset prog tprog
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop s1 s1' →
    ∃ s2',
      plus (Mach.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi return_address_offset) (Genv.globalenv tprog) s1' t s2' ∧
      match_states cfg return_address_offset prog tprog
        _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
        _used_callee_save_norepet _used_callee_save_prop s2 s2'

def transl_builtin_arg_correctStatement : Prop :=
  ∀ cfg (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (prog : Linear.program) (tprog : Mach.program) (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f)),
    ∀ j m m' ls ls0 rs sp sp' parent retaddr,
    j sp = some (sp', (make_env cfg (function_bounds cfg f)).fe_stack_data) →
    agree_regs j ls rs →
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp' ls ls0 parent retaddr)
      (sepconj (minjection j m)
        (globalenv_inject (Genv.globalenv prog) j))).m_pred m' → ∀ a v,
    eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) ls
      (Vptr sp Ptrofs.zero) m a v →
    (∀ l, l ∈ params_of_builtin_arg a → loc_valid cfg f l = true) →
    (∀ sl ofs ty, S sl ofs ty ∈ params_of_builtin_arg a →
      slot_within_bounds (function_bounds cfg f) sl ofs ty) →
    ∃ v',
      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) rs
        (Vptr sp' Ptrofs.zero) m'
        (transl_builtin_arg (make_env cfg (function_bounds cfg f)) a) v' ∧
      Val.inject j v v'

def transl_builtin_args_correctStatement : Prop :=
  ∀ cfg (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (prog : Linear.program) (tprog : Mach.program) (f : Linear.function)
    (_bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f)),
    ∀ j m m' ls ls0 rs sp sp' parent retaddr,
    j sp = some (sp', (make_env cfg (function_bounds cfg f)).fe_stack_data) →
    agree_regs j ls rs →
    (sepconj (frame_contents return_address_offset tprog cfg f
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop
      j sp' ls ls0 parent retaddr)
      (sepconj (minjection j m)
        (globalenv_inject (Genv.globalenv prog) j))).m_pred m' → ∀ al vl,
    eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) ls
      (Vptr sp Ptrofs.zero) m al vl →
    (∀ l, l ∈ params_of_builtin_args al → loc_valid cfg f l = true) →
    (∀ sl ofs ty, S sl ofs ty ∈ params_of_builtin_args al →
      slot_within_bounds (function_bounds cfg f) sl ofs ty) →
    ∃ vl',
      eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) rs
        (Vptr sp' Ptrofs.zero) m'
        (al.map (transl_builtin_arg (make_env cfg (function_bounds cfg f)))) vl' ∧
      Val.inject_list j vl vl'
def transl_code_eqStatement : Prop :=
  ∀ cfg fe i c,
    transl_code cfg fe (i :: c) = transl_instr cfg fe i (transl_code cfg fe c)

def transl_destroyed_by_loadStatement : Prop :=
  ∀ chunk addr fe,
    destroyed_by_load chunk (transl_addr fe addr) = destroyed_by_load chunk addr

def transl_destroyed_by_opStatement : Prop :=
  ∀ op fe, destroyed_by_op (transl_op fe op) = destroyed_by_op op

def transl_destroyed_by_storeStatement : Prop :=
  ∀ chunk addr fe,
    destroyed_by_store chunk (transl_addr fe addr) = destroyed_by_store chunk addr
def transl_external_argumentStatement : Prop :=
  ∀ cfg (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) j cs cs' sg
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
      _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' sg → ∀ ls rs,
    agree_regs j ls rs →
    agree_callee_save cfg ls (Linear.parent_locset cs) →
    agree_outgoing_arguments cfg sg ls (Linear.parent_locset cs) → ∀ m',
    (stack_contents return_address_offset tprog cfg j cs cs'
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop).m_pred m' → ∀ l,
    l ∈ regs_of_rpairs (loc_arguments cfg sg) →
    ∃ v, Mach.extcall_arg cfg rs m' (Mach.parent_sp cs') l v ∧
      Val.inject j (ls l) v

def transl_external_argument_2Statement : Prop :=
  ∀ cfg (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) j cs cs' sg
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
      _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' sg → ∀ ls rs,
    agree_regs j ls rs →
    agree_callee_save cfg ls (Linear.parent_locset cs) →
    agree_outgoing_arguments cfg sg ls (Linear.parent_locset cs) → ∀ m',
    (stack_contents return_address_offset tprog cfg j cs cs'
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop).m_pred m' → ∀ p,
    p ∈ loc_arguments cfg sg →
    ∃ v, Mach.extcall_arg_pair cfg rs m' (Mach.parent_sp cs') p v ∧
      Val.inject j (Locmap.getpair p ls) v

def transl_external_argumentsStatement : Prop :=
  ∀ cfg (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) j cs cs' sg
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
      _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' sg → ∀ ls rs,
    agree_regs j ls rs →
    agree_callee_save cfg ls (Linear.parent_locset cs) →
    agree_outgoing_arguments cfg sg ls (Linear.parent_locset cs) → ∀ m',
    (stack_contents return_address_offset tprog cfg j cs cs'
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop).m_pred m' →
    ∃ vl, Mach.extcall_arguments cfg rs m' (Mach.parent_sp cs') sg vl ∧
      Val.inject_list j ((loc_arguments cfg sg).map (fun p => Locmap.getpair p ls)) vl

def transl_external_arguments_recStatement : Prop :=
  ∀ cfg (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) j cs cs' sg
    (_bound_local_pos : ∀ f : Linear.function,
      bound_local_pos cfg (function_bounds cfg f))
    (_bound_outgoing_pos : ∀ f : Linear.function,
      bound_outgoing_pos cfg (function_bounds cfg f))
    (_bound_stack_data_pos : ∀ f : Linear.function,
      bound_stack_data_pos cfg (function_bounds cfg f))
    (_used_callee_save_norepet : ∀ f : Linear.function,
      used_callee_save_norepet cfg (function_bounds cfg f))
    (_used_callee_save_prop : ∀ f : Linear.function,
      used_callee_save_prop cfg (function_bounds cfg f)),
    match_stacks cfg tprog j _bound_local_pos _bound_outgoing_pos
      _bound_stack_data_pos _used_callee_save_norepet _used_callee_save_prop cs cs' sg → ∀ ls rs,
    agree_regs j ls rs →
    agree_callee_save cfg ls (Linear.parent_locset cs) →
    agree_outgoing_arguments cfg sg ls (Linear.parent_locset cs) → ∀ m',
    (stack_contents return_address_offset tprog cfg j cs cs'
      _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
      _used_callee_save_norepet _used_callee_save_prop).m_pred m' → ∀ locs,
    (∀ p, p ∈ locs → p ∈ loc_arguments cfg sg) →
    ∃ vl,
      list_forall2 (Mach.extcall_arg_pair cfg rs m' (Mach.parent_sp cs')) locs vl ∧
      Val.inject_list j (locs.map (fun p => Locmap.getpair p ls)) vl
def transl_find_labelStatement : Prop :=
  ∀ cfg f tf lbl c, transf_function cfg f = .OK tf →
    Linear.find_label lbl f.fn_code = some c →
    Mach.find_label lbl tf.fn_code =
      some (transl_code cfg (make_env cfg (function_bounds cfg f)) c)

def typesize_typesizeStatement : Prop :=
  ∀ ty, CompCert4Lean.Common.AST.typesize ty =
    zMul z4 (CompCert4Lean.Backend.Locations.typesize ty)

def undef_regs_typeStatement : Prop :=
  ∀ ty l rl ls, Val.has_type (ls l) ty →
    Val.has_type (LTL.undef_regs rl ls l) ty

def unfold_transf_functionStatement : Prop :=
  ∀ cfg f tf, transf_function cfg f = .OK tf →
    tf = {
      fn_sig := f.fn_sig
      fn_code := transl_body cfg f (make_env cfg (function_bounds cfg f))
      fn_stacksize := (make_env cfg (function_bounds cfg f)).fe_size
      fn_link_ofs := Ptrofs.repr (make_env cfg (function_bounds cfg f)).fe_ofs_link
      fn_retaddr_ofs := Ptrofs.repr
        (make_env cfg (function_bounds cfg f)).fe_ofs_retaddr }

def valid_access_locationStatement : Prop :=
  ∀ m sp pos bound ofs ty p,
    zDivide z8 pos →
    Mem.range_perm m sp pos (zAdd pos (zMul z4 bound)) Cur Freeable →
    zLe z0 ofs →
    zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) bound →
    zDivide (CompCert4Lean.Backend.Locations.typealign ty) ofs →
    Mem.valid_access m (chunk_of_type ty) sp (zAdd pos (zMul z4 ofs)) p

def wt_progStatement : Prop :=
  ∀ cfg (prog : Linear.program) (tprog : Mach.program),
    match_prog cfg prog tprog → ∀ i fd,
    (i, .Gfun fd) ∈ prog.prog_defs → wt_fundef cfg fd

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking

theorem transf_program_match : transf_program_matchStatement := by
  letI : Linker Linear.fundef := by
    change Linker (CompCert4Lean.Common.AST.fundef Linear.function)
    exact Linker_fundef Linear.function
  letI : Linker Mach.fundef := by
    change Linker (CompCert4Lean.Common.AST.fundef Mach.function)
    exact Linker_fundef Mach.function
  letI : Linker Linear.program := by
    change Linker (CompCert4Lean.Common.AST.program
      (CompCert4Lean.Common.AST.fundef Linear.function) Unit)
    exact Linker_prog (CompCert4Lean.Common.AST.fundef Linear.function) Unit
  intro cfg p tp htrans
  rcases p with ⟨pdefs, ppub, pmain⟩
  unfold CompCert4Lean.Backend.Stacking.transf_program at htrans
  unfold CompCert4Lean.Common.AST.transform_partial_program at htrans
  unfold CompCert4Lean.Common.AST.transform_partial_program2 at htrans
  cases hdefs : CompCert4Lean.Common.AST.transf_globdefs
      (fun _ f => CompCert4Lean.Backend.Stacking.transf_fundef cfg f)
      (fun _ v => .OK v) pdefs with
  | Error msg =>
      simp [hdefs] at htrans
  | OK defs =>
      simp [hdefs] at htrans
      cases htrans
      unfold match_prog
      constructor
      · let ctx : Linear.program :=
          { prog_defs := pdefs, prog_public := ppub, prog_main := pmain }
        have hlist : ∀ (xs : List (ident × globdef Linear.fundef Unit))
            (ys : List (ident × globdef Mach.fundef Unit)),
            CompCert4Lean.Common.AST.transf_globdefs
                (fun _ f => CompCert4Lean.Backend.Stacking.transf_fundef cfg f)
                (fun _ v => .OK v) xs = .OK ys →
              CompCert4Lean.Lib.Coqlib.list_forall2
                (match_ident_globdef
                  (fun _ f tf => CompCert4Lean.Backend.Stacking.transf_fundef cfg f = .OK tf)
                  (fun x y : Unit => x = y) ctx) xs ys := by
          intro xs
          induction xs with
          | nil =>
              intro ys h
              change CompCert4Lean.Common.Errors.OK [] =
                CompCert4Lean.Common.Errors.OK ys at h
              cases h
              exact CompCert4Lean.Lib.Coqlib.list_forall2.nil _
          | cons hd tl ih =>
              cases hd with
              | mk id gd =>
                  cases gd with
                  | Gfun f =>
                      change CompCert4Lean.Backend.Linear.fundef at f
                      cases htf : CompCert4Lean.Backend.Stacking.transf_fundef cfg f with
                      | Error msg =>
                          intro ys h
                          simp [CompCert4Lean.Common.AST.transf_globdefs, htf] at h
                      | OK tf =>
                          cases htail : CompCert4Lean.Common.AST.transf_globdefs
                              (fun _ f => CompCert4Lean.Backend.Stacking.transf_fundef cfg f)
                              (fun _ v => .OK v) tl with
                          | Error msg =>
                              intro ys h
                              simp [CompCert4Lean.Common.AST.transf_globdefs, htf, htail] at h
                          | OK ys' =>
                              intro ys h
                              simp [CompCert4Lean.Common.AST.transf_globdefs, htf, htail] at h
                              cases h
                              apply CompCert4Lean.Lib.Coqlib.list_forall2.cons
                              · constructor
                                · rfl
                                · apply match_globdef.match_globdef_fun (ctx' := ctx)
                                  · exact linkorder_refl _
                                  · exact htf
                              · exact ih ys' htail
                  | Gvar v =>
                      cases htail : CompCert4Lean.Common.AST.transf_globdefs
                          (fun _ f => CompCert4Lean.Backend.Stacking.transf_fundef cfg f)
                          (fun _ v => .OK v) tl with
                      | Error msg =>
                          intro ys h
                          simp [CompCert4Lean.Common.AST.transf_globdefs,
                            CompCert4Lean.Common.AST.transf_globvar, htail] at h
                      | OK ys' =>
                          intro ys h
                          simp [CompCert4Lean.Common.AST.transf_globdefs, htail] at h
                          cases h
                          apply CompCert4Lean.Lib.Coqlib.list_forall2.cons
                          · constructor
                            · rfl
                            · apply match_globdef.match_globdef_var
                              exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                          · exact ih ys' htail
        exact hlist pdefs defs hdefs
      · exact ⟨rfl, rfl⟩

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem typesize_typesize : typesize_typesizeStatement := by
  intro ty
  cases ty <;> rfl

theorem size_type_chunk : size_type_chunkStatement := by
  intro ty
  cases ty <;> rfl

theorem align_type_chunk : align_type_chunkStatement := by
  intro ty
  cases ty <;> rfl

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Lineartyping
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST

private theorem stackingproof_typealign_pos (ty : CompCert4Lean.Common.AST.typ) :
    0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Backend.Locations.typealign ty) := by
  cases ty <;>
    simp [CompCert4Lean.Backend.Locations.typealign,
      ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem stackingproof_modulo_zero_of_divide
    (a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (ha : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a)
    (h : ZArith.BinInt.Z.divide a b) :
    ZArith.BinInt.Z.modulo b a = ZArith.BinInt.Z.Z0 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [ZArith.BinInt.Z.modulo,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  run_tac
    Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
      let target ← goal.getType
      let target' ← Lean.Meta.transform target (pre := fun e => do
        match e.getAppFn.constName? with
        | some name =>
            if Lean.Name.isPrefixOf `_private name then
              let e' ← Lean.Meta.withTransparency .all <| Lean.Meta.whnf e
              return Lean.TransformStep.done e'
            else
              return Lean.TransformStep.continue
        | none => return Lean.TransformStep.continue)
      let goal ← Lean.Meta.withTransparency .all <| goal.change target'
      return [goal]
  generalize hdec : (Int.instDecidableEq
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a) 0) = d
  cases d with
  | isTrue hz =>
      omega
  | isFalse hz =>
      simp only [Decidable.rec]
      have hdvd :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ∣
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
        rcases h with ⟨k, hk⟩
        refine ⟨CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k, ?_⟩
        have hk' := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hk
        simp only [ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hk'
        exact hk'
      have ha0 :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≠ 0 := by omega
      simp only [if_pos ha]
      change (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b).emod
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a) = 0
      exact Int.emod_eq_zero_of_dvd hdvd

theorem slot_outgoing_argument_valid : slot_outgoing_argument_validStatement := by
  intro cfg f ofs ty sg h
  have hacc := CompCert4Lean.Backend.Conventions.loc_arguments_acceptable_2
    cfg sg (S Outgoing ofs ty) h
  change ZArith.BinInt.Z.le ZArith.BinInt.Z.Z0 ofs ∧
    ZArith.BinInt.Z.divide
      (CompCert4Lean.Backend.Locations.typealign ty) ofs at hacc
  have hnonneg := hacc.1
  have hdiv := hacc.2
  unfold CompCert4Lean.Backend.Lineartyping.slot_valid
  run_tac
    Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
      let target ← goal.getType
      let target' ← Lean.Meta.transform target (pre := fun e => do
        match e.getAppFn.constName? with
        | some name =>
            if Lean.Name.isPrefixOf `_private name then
              let e' ← Lean.Meta.withTransparency .all <| Lean.Meta.whnf e
              return Lean.TransformStep.done e'
            else
              return Lean.TransformStep.continue
        | none => return Lean.TransformStep.continue)
      let goal ← Lean.Meta.withTransparency .all <| goal.change target'
      return [goal]
  simp only [Bool.and_eq_true]
  constructor
  · generalize hle : CompCert4Lean.Lib.Coqlib.zle
      ZArith.BinInt.Z.Z0 ofs = d
    cases d with
    | left hp => rfl
    | right hp =>
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            ZArith.BinInt.Z.Z0 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs at hnonneg
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              ZArith.BinInt.Z.Z0 at hp
        omega
  · have hmod : ZArith.BinInt.Z.modulo ofs
        (CompCert4Lean.Backend.Locations.typealign ty) =
          ZArith.BinInt.Z.Z0 := by
      apply stackingproof_modulo_zero_of_divide
      · exact stackingproof_typealign_pos ty
      · exact hdiv
    generalize hz : CompCert4Lean.Lib.Coqlib.zeq
        (ZArith.BinInt.Z.modulo ofs
          (CompCert4Lean.Backend.Locations.typealign ty))
        ZArith.BinInt.Z.Z0 = d
    cases d with
    | left hp => rfl
    | right hp => exact False.elim (hp hmod)

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem load_result_inject : load_result_injectStatement := by
  intro j ty v v' hinj hty
  cases hinj with
  | inject_int i =>
      cases ty <;>
        simp [CompCert4Lean.Common.AST.chunk_of_type,
          CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Common.Values.Val.has_type] at hty ⊢ <;>
        first | contradiction | exact CompCert4Lean.Common.Values.Val.inject_int j i
  | inject_long i =>
      cases ty <;>
        simp [CompCert4Lean.Common.AST.chunk_of_type,
          CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Common.Values.Val.has_type] at hty ⊢ <;>
        first | contradiction | exact CompCert4Lean.Common.Values.Val.inject_long j i
  | inject_float f =>
      cases ty <;>
        simp [CompCert4Lean.Common.AST.chunk_of_type,
          CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Common.Values.Val.has_type] at hty ⊢ <;>
        first | contradiction | exact CompCert4Lean.Common.Values.Val.inject_float j f
  | inject_single f =>
      cases ty <;>
        simp [CompCert4Lean.Common.AST.chunk_of_type,
          CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Common.Values.Val.has_type] at hty ⊢ <;>
        first | contradiction | exact CompCert4Lean.Common.Values.Val.inject_single j f
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      cases ty <;>
        simp [CompCert4Lean.Common.AST.chunk_of_type,
          CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Common.Values.Val.has_type, hty] at hty ⊢ <;>
        first | contradiction | exact CompCert4Lean.Common.Values.Val.inject_ptr j b1 ofs1 b2 ofs2 delta hmap hofs
  | val_inject_undef v =>
      exact CompCert4Lean.Common.Values.Val.val_inject_undef j _

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem unfold_transf_function : unfold_transf_functionStatement := by
  intro cfg f tf htf
  unfold CompCert4Lean.Backend.Stacking.transf_function at htf
  dsimp at htf
  split at htf
  · contradiction
  · split at htf
    · contradiction
    · cases htf
      rfl

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem size_no_overflow : size_no_overflowStatement := by
  intro cfg f tf htf
  unfold CompCert4Lean.Backend.Stacking.transf_function at htf
  dsimp at htf
  split at htf
  · contradiction
  · split at htf
    · contradiction
    · cases htf
      rename_i hnot x hge heq
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ _ ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ _
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ _ ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ _ at hge
      exact hge

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof
theorem contains_locations_obligation_1 : contains_locations_obligation_1Statement := by
  intro return_address_offset tprog j sp pos bound sl ls m m' hm hunch
  exact (contains_locations return_address_offset tprog j sp pos bound sl ls).m_invar m m' hm hunch
theorem contains_locations_obligation_2 : contains_locations_obligation_2Statement := by
  intro j sp pos bound sl ls m b ofs hm hfoot
  rcases hfoot with ⟨rfl, hlo, hhi⟩
  exact validBlockOfPerm (hm.2.2.2.1 ofs ⟨hlo, hhi⟩)
end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem valid_access_location : valid_access_locationStatement := by
  intro m sp pos bound ofs ty p hpos hperm hofs hbound halign
  refine ⟨?_, ?_⟩
  · intro i hi
    exact Mem.perm_implies m sp i Cur Freeable p
      (hperm i (locationChunkRange pos bound ofs i ty hofs hbound hi))
      (perm_F_any p)
  · exact locationAligned pos ofs ty hpos halign

theorem initial_locations : initial_locationsStatement := by
  intro return_address_offset tprog j sp pos bound P sl ls m hmem hpos hls
  rcases hmem with ⟨hrange, hP, hdisj⟩
  rcases hrange with ⟨hpos0, hmax, hperm⟩
  refine ⟨⟨hpos, hpos0, ?_, ?_, ?_⟩, hP, ?_⟩
  · exact hmax
  · intro i hi
    exact hperm i Cur Freeable hi
  · intro ofs ty hofs hbound halign
    have hvalid : Mem.valid_access m (chunk_of_type ty) sp
        (zAdd pos (zMul z4 ofs)) Freeable := by
      exact valid_access_location m sp pos bound ofs ty Freeable hpos
        (fun i hi => hperm i Cur Freeable hi) hofs hbound halign
    have hvalidR : Mem.valid_access m (chunk_of_type ty) sp
        (zAdd pos (zMul z4 ofs)) Readable := by
      exact Mem.valid_access_implies m (chunk_of_type ty) sp
        (zAdd pos (zMul z4 ofs)) Freeable Readable hvalid (perm_F_any Readable)
    generalize hdecEq : Mem.valid_access_dec m (chunk_of_type ty) sp
      (zAdd pos (zMul z4 ofs)) Readable = hdec
    cases hdec with
    | left hd =>
        let v0 := decode_val (chunk_of_type ty)
          (Mem.getN (size_chunk_nat (chunk_of_type ty))
            (zAdd pos (zMul z4 ofs))
            (CompCert4Lean.Lib.Maps.PMap.get sp m.mem_contents))
        refine ⟨v0, ?_, ?_⟩
        · unfold Mem.load
          rw [hdecEq]
          change (if true then some v0 else none) = some v0
          rfl
        · rw [hls]
          exact Val.val_inject_undef j _
    | right hnd => exact (hnd hvalidR).elim
  · exact hdisj

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.X86.Machregs
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.Separation
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem contains_callee_saves_exten : contains_callee_saves_extenStatement := by
  intro j sp ls ls' rl
  induction rl with
  | nil =>
      intro pos hls
      constructor <;> constructor
      · intro m h
        exact h
      · intro b ofs h
        exact h
      · intro m h
        exact h
      · intro b ofs h
        exact h
  | cons r rs ih =>
      intro pos hls
      let ty := mreg_type r
      let sz := CompCert4Lean.Common.AST.typesize ty
      let pos' := align pos sz
      have hls_tail : ∀ r', r' ∈ rs → ls' (R r') = ls (R r') := by
        intro r' hr'
        exact hls r' (by simp [hr'])
      have htail : massert_eqv
          (contains_callee_saves j sp (ZArith.BinInt.Z.add pos' sz) rs ls)
          (contains_callee_saves j sp (ZArith.BinInt.Z.add pos' sz) rs ls') :=
        ih (ZArith.BinInt.Z.add pos' sz) hls_tail
      constructor
      · constructor
        · intro m hpred
          rcases hpred with ⟨hhead, hrest, hdisj⟩
          refine ⟨?_, htail.1.1 m hrest, ?_⟩
          · simpa [hls r (by simp)] using hhead
          · intro b ofs hhead' hrest'
            exact hdisj b ofs hhead' (htail.1.2 b ofs hrest')
        · intro b ofs hfoot
          cases hfoot with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr (htail.1.2 b ofs h)
      · constructor
        · intro m hpred
          rcases hpred with ⟨hhead, hrest, hdisj⟩
          refine ⟨?_, htail.2.1 m hrest, ?_⟩
          · simpa [hls r (by simp)] using hhead
          · intro b ofs hhead' hrest'
            exact hdisj b ofs hhead' (htail.2.2 b ofs hrest')
        · intro b ofs hfoot
          cases hfoot with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr (htail.2.2 b ofs h)

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Separation

private theorem stackingproof_val_inject_incr
    (j j' : CompCert4Lean.Common.Values.Val.meminj)
    (v v' : CompCert4Lean.Common.Values.val)
    (hinc : inject_incr j j') (hval : Val.inject j v v') :
    Val.inject j' v v' := by
  cases hval with
  | inject_int i => exact Val.inject.inject_int i
  | inject_long i => exact Val.inject.inject_long i
  | inject_float f => exact Val.inject.inject_float f
  | inject_single f => exact Val.inject.inject_single f
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      exact Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta (hinc b1 b2 delta hmap) hofs
  | val_inject_undef v' => exact Val.inject.val_inject_undef v'

private theorem stackingproof_lessdef_inject
    (j : CompCert4Lean.Common.Values.Val.meminj)
    (a b v : CompCert4Lean.Common.Values.val)
    (hless : Val.lessdef a b) (hinj : Val.inject j b v) :
    Val.inject j a v := by
  cases hless with
  | lessdef_refl a => exact hinj
  | lessdef_undef b => exact Val.inject.val_inject_undef v

theorem contains_locations_exten : contains_locations_extenStatement := by
  intro return_address_offset tprog ls ls' j sp pos bound sl hls
  constructor
  · intro m hpred
    rcases hpred with ⟨hdiv, hpos, hover, hperm, hload⟩
    refine ⟨hdiv, hpos, hover, hperm, ?_⟩
    intro ofs ty hofs hbound halign
    rcases hload ofs ty hofs hbound halign with ⟨v, hv, hinj⟩
    exact ⟨v, hv, stackingproof_lessdef_inject j _ _ _ (hls ofs ty) hinj⟩
  · intro b ofs hfoot
    exact hfoot

theorem contains_locations_incr : contains_locations_incrStatement := by
  intro return_address_offset tprog j j' sp pos bound sl ls hinc
  constructor
  · intro m hpred
    rcases hpred with ⟨hdiv, hpos, hover, hperm, hload⟩
    refine ⟨hdiv, hpos, hover, hperm, ?_⟩
    intro ofs ty hofs hbound halign
    rcases hload ofs ty hofs hbound halign with ⟨v, hv, hinj⟩
    exact ⟨v, hv, stackingproof_val_inject_incr j j' _ _ hinc hinj⟩
  · intro b ofs hfoot
    exact hfoot

theorem contains_callee_saves_incr : contains_callee_saves_incrStatement := by
  intro j j' sp ls hinc rl
  induction rl with
  | nil =>
      intro pos
      constructor
      · intro m h
        exact h
      · intro b ofs hfoot
        exact hfoot
  | cons r rs ih =>
      intro pos
      let ty := CompCert4Lean.X86.Machregs.mreg_type r
      let sz := CompCert4Lean.Common.AST.typesize ty
      let pos' := CompCert4Lean.Lib.Coqlib.align pos sz
      have htail := ih (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add pos' sz)
      constructor
      · intro m hpred
        rcases hpred with ⟨hhead, hrest, hdisj⟩
        refine ⟨?_, htail.1 m hrest, ?_⟩
        · rcases hhead with ⟨hrange, hvalid, v, hload, hinj⟩
          refine ⟨hrange, hvalid, v, hload, ?_⟩
          exact stackingproof_val_inject_incr j j' _ _ hinc hinj
        · intro b ofs hhead' hrest'
          exact hdisj b ofs hhead' (htail.2 b ofs hrest')
      · intro b ofs hfoot
        cases hfoot with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (htail.2 b ofs h)

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Common.Separation
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.X86.Stacklayout
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata

private theorem stackingproof_massert_imp_sepconj
    {P P' Q Q' : massert}
    (hP : massert_imp P P') (hQ : massert_imp Q Q') :
    massert_imp (sepconj P Q) (sepconj P' Q') := by
  constructor
  · intro m h
    refine ⟨hP.1 m h.1, hQ.1 m h.2.1, ?_⟩
    intro b ofs hP'foot hQ'foot
    exact h.2.2 b ofs (hP.2 b ofs hP'foot) (hQ.2 b ofs hQ'foot)
  · intro b ofs hfoot
    cases hfoot with
    | inl h => exact Or.inl (hP.2 b ofs h)
    | inr h => exact Or.inr (hQ.2 b ofs h)

private theorem stackingproof_massert_imp_mconj
    {P P' Q Q' : massert}
    (hP : massert_imp P P') (hQ : massert_imp Q Q') :
    massert_imp (mconj P Q) (mconj P' Q') := by
  constructor
  · intro m h
    exact ⟨hP.1 m h.1, hQ.1 m h.2⟩
  · intro b ofs hfoot
    cases hfoot with
    | inl h => exact Or.inl (hP.2 b ofs h)
    | inr h => exact Or.inr (hQ.2 b ofs h)

theorem frame_contents_exten : frame_contents_extenStatement := by
  intro return_address_offset tprog cfg f bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
    ls ls0 ls' ls0' j sp parent retaddr P m hlocal hout hcallee hm
  let b := function_bounds cfg f
  let fe := make_env cfg b
  have hlocal' : massert_imp
      (contains_locations return_address_offset tprog j sp fe.fe_ofs_local
        b.bound_local Local ls)
      (contains_locations return_address_offset tprog j sp fe.fe_ofs_local
        b.bound_local Local ls') :=
    contains_locations_exten return_address_offset tprog ls ls' j sp
      fe.fe_ofs_local b.bound_local Local hlocal
  have hout' : massert_imp
      (contains_locations return_address_offset tprog j sp (fe_ofs_arg cfg)
        b.bound_outgoing Outgoing ls)
      (contains_locations return_address_offset tprog j sp (fe_ofs_arg cfg)
        b.bound_outgoing Outgoing ls') :=
    contains_locations_exten return_address_offset tprog ls ls' j sp
      (fe_ofs_arg cfg) b.bound_outgoing Outgoing hout
  have hcallee' : massert_imp
      (contains_callee_saves j sp fe.fe_ofs_callee_save b.used_callee_save ls0)
      (contains_callee_saves j sp fe.fe_ofs_callee_save b.used_callee_save ls0') :=
    (contains_callee_saves_exten j sp ls0 ls0' b.used_callee_save
      fe.fe_ofs_callee_save hcallee).1
  have hlink : massert_imp
      (hasvalue Mptr sp fe.fe_ofs_link parent)
      (hasvalue Mptr sp fe.fe_ofs_link parent) := by
    constructor
    · intro m hm
      exact hm
    · intro b' ofs' hfoot
      exact hfoot
  have hret : massert_imp
      (hasvalue Mptr sp fe.fe_ofs_retaddr retaddr)
      (hasvalue Mptr sp fe.fe_ofs_retaddr retaddr) := by
    constructor
    · intro m hm
      exact hm
    · intro b' ofs' hfoot
      exact hfoot
  have hframe1 : massert_imp
      (frame_contents_1 return_address_offset tprog cfg f
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop j sp ls ls0 parent retaddr)
      (frame_contents_1 return_address_offset tprog cfg f
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop j sp ls' ls0' parent retaddr) := by
    exact stackingproof_massert_imp_sepconj hlocal'
      (stackingproof_massert_imp_sepconj hout'
        (stackingproof_massert_imp_sepconj hlink
          (stackingproof_massert_imp_sepconj hret hcallee')))
  have hframe : massert_imp
      (frame_contents return_address_offset tprog cfg f
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop j sp ls ls0 parent retaddr)
      (frame_contents return_address_offset tprog cfg f
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop j sp ls' ls0' parent retaddr) := by
    exact stackingproof_massert_imp_mconj hframe1 (by
      constructor
      · intro x hx
        exact hx
      · intro b' ofs' hfoot
        exact hfoot)
  exact (stackingproof_massert_imp_sepconj hframe (by
    constructor
    · intro x hx
      exact hx
    · intro b' ofs' hfoot
      exact hfoot)).1 m hm

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

theorem frame_set_reg : frame_set_regStatement := by
  intro return_address_offset tprog cfg f bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
    r v j sp ls ls0 parent retaddr m P hm
  refine frame_contents_exten return_address_offset tprog cfg f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop ls ls0
    (Locmap.set (R r) v ls) ls0 j sp parent retaddr P m ?_ ?_ ?_ hm
  · intro ofs ty
    rw [show Locmap.set (R r) v ls (S Local ofs ty) = ls (S Local ofs ty) by
      apply Locmap.gso
      simp [Loc.diff]]
    exact Val.lessdef_refl _
  · intro ofs ty
    rw [show Locmap.set (R r) v ls (S Outgoing ofs ty) = ls (S Outgoing ofs ty) by
      apply Locmap.gso
      simp [Loc.diff]]
    exact Val.lessdef_refl _
  · intro r' hr'
    rfl

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.LTL

theorem frame_undef_regs : frame_undef_regsStatement := by
  intro return_address_offset tprog cfg f bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
    j sp ls ls0 parent retaddr m P rl hm
  induction rl with
  | nil =>
      simpa [CompCert4Lean.Backend.LTL.undef_regs] using hm
  | cons r rl ih =>
      have htail := ih
      have hset := frame_set_reg return_address_offset tprog cfg f
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop r
        CompCert4Lean.Common.Values.Vundef j sp
        (CompCert4Lean.Backend.LTL.undef_regs rl ls) ls0 parent retaddr m P htail
      simpa [CompCert4Lean.Backend.LTL.undef_regs] using hset

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

 theorem agree_reg : agree_regStatement := by
  intro j ls rs r h
  exact h r

 theorem agree_reglist : agree_reglistStatement := by
  intro j ls rs rl h
  induction rl with
  | nil => exact Val.inject_list_nil j
  | cons r rl ih =>
      simp [CompCert4Lean.Backend.LTL.reglist]
      exact Val.inject_list_cons j (ls (R r)) (rs r)
        (LTL.reglist ls rl) (rl.map rs)
        (CompCert4Lean.Backend.Stackingproof.agree_reg j ls rs r h) (ih)

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

private theorem stackingproof_loword_inject :
    ∀ (j : Val.meminj) v v', Val.inject j v v' →
      Val.inject j (Val.loword v) (Val.loword v') := by
  intro j v v' h
  cases h with
  | inject_int i => exact Val.val_inject_undef _ _
  | inject_long i => exact Val.inject_int _ _
  | inject_float f => exact Val.val_inject_undef _ _
  | inject_single f => exact Val.val_inject_undef _ _
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      exact Val.val_inject_undef _ _
  | val_inject_undef v => exact Val.val_inject_undef _ _

private theorem stackingproof_hiword_inject :
    ∀ (j : Val.meminj) v v', Val.inject j v v' →
      Val.inject j (Val.hiword v) (Val.hiword v') := by
  intro j v v' h
  cases h with
  | inject_int i => exact Val.val_inject_undef _ _
  | inject_long i => exact Val.inject_int _ _
  | inject_float f => exact Val.val_inject_undef _ _
  | inject_single f => exact Val.val_inject_undef _ _
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      exact Val.val_inject_undef _ _
  | val_inject_undef v => exact Val.val_inject_undef _ _

private theorem stackingproof_agree_regs_set_reg :
    ∀ (j : Val.meminj) ls rs r v v',
      agree_regs j ls rs → Val.inject j v v' →
      agree_regs j (Locmap.set (R r) v ls) (Regmap.set r v' rs) := by
  intro j ls rs r v v' hagree hv r'
  change Locmap.t at ls
  by_cases heq : r' = r
  · subst r'
    have hloc : Locmap.set (R r) v ls (R r) = v := by
      simpa using (Locmap.gss (R r) v ls)
    have hreg : Regmap.set r v' rs r = v' := by
      simpa [Regmap.get] using (Regmap.gss_proof val r v' rs)
    rw [hloc, hreg]
    exact hv
  · have hdiff : Loc.diff (R r) (R r') := by
      have hne : r ≠ r' := by
        intro h
        exact heq h.symm
      exact hne
    have hloc : Locmap.set (R r) v ls (R r') = ls (R r') :=
      Locmap.gso (R r) v ls (R r') hdiff
    have hreg : Regmap.set r v' rs r' = rs r' := by
      change Regmap.get r' (Regmap.set r v' rs) = Regmap.get r' rs
      simpa using (Regmap.gso_proof val r' r v' rs heq)
    rw [hloc, hreg]
    exact hagree r'

theorem agree_regs_set_res : agree_regs_set_resStatement := by
  intro j res
  induction res with
  | BR r =>
      intro v v' ls rs hagree hv
      exact stackingproof_agree_regs_set_reg j ls rs r v v' hagree hv
  | BR_none =>
      intro v v' ls rs hagree hv
      simpa [Locmap.setres, Mach.set_res] using hagree
  | BR_splitlong hi lo ih_hi ih_lo =>
      intro v v' ls rs hagree hv
      have hhi := ih_hi (Val.hiword v) (Val.hiword v') ls rs hagree
        (stackingproof_hiword_inject j v v' hv)
      have hlo := ih_lo (Val.loword v) (Val.loword v')
        (Locmap.setres hi (Val.hiword v) ls)
        (Mach.set_res hi (Val.hiword v') rs) hhi
        (stackingproof_loword_inject j v v' hv)
      simpa [Locmap.setres, Mach.set_res] using hlo

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.Values

theorem agree_regs_undef_regs : agree_regs_undef_regsStatement := by
  intro j rl ls rs hagree
  induction rl with
  | nil =>
      simpa [LTL.undef_regs, Mach.undef_regs] using hagree
  | cons r rl ih =>
      intro r0
      by_cases heq : r0 = r
      · subst r0
        change Val.inject j
          (Locmap.set (R r) Vundef (LTL.undef_regs rl ls) (R r))
          (Regmap.set r Vundef (Mach.undef_regs rl rs) r)
        have hloc :
            Locmap.set (R r) Vundef (LTL.undef_regs rl ls) (R r) = Vundef := by
          simpa using (Locmap.gss (R r) Vundef (LTL.undef_regs rl ls))
        have hreg :
            Regmap.set r Vundef (Mach.undef_regs rl rs) r = Vundef := by
          change Regmap.get r (Regmap.set r Vundef (Mach.undef_regs rl rs)) = Vundef
          simpa using (Regmap.gss_proof val r Vundef (Mach.undef_regs rl rs))
        rw [hloc, hreg]
        exact Val.val_inject_undef _ _
      · have hdiff : Loc.diff (R r) (R r0) := by
          have hne : r ≠ r0 := by
            intro h
            exact heq h.symm
          exact hne
        change Val.inject j
          (Locmap.set (R r) Vundef (LTL.undef_regs rl ls) (R r0))
          (Regmap.set r Vundef (Mach.undef_regs rl rs) r0)
        have hloc :
            Locmap.set (R r) Vundef (LTL.undef_regs rl ls) (R r0) =
              (LTL.undef_regs rl ls) (R r0) := by
          exact Locmap.gso (R r) Vundef (LTL.undef_regs rl ls) (R r0) hdiff
        have hreg :
            Regmap.set r Vundef (Mach.undef_regs rl rs) r0 =
              (Mach.undef_regs rl rs) r0 := by
          change Regmap.get r0 (Regmap.set r Vundef (Mach.undef_regs rl rs)) =
            Regmap.get r0 (Mach.undef_regs rl rs)
          simpa using
            (Regmap.gso_proof val r0 r Vundef (Mach.undef_regs rl rs) heq)
        rw [hloc, hreg]
        exact ih r0

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.Values

theorem agree_regs_undef_caller_save_regs :
    agree_regs_undef_caller_save_regsStatement := by
  intro cfg j ls rs hagree r
  change Val.inject j
    (LTL.undef_caller_save_regs cfg ls (R r))
    (Mach.undef_caller_save_regs cfg rs r)
  simp only [LTL.undef_caller_save_regs, Mach.undef_caller_save_regs]
  split
  · exact hagree r
  · exact Val.val_inject_undef _ _

theorem agree_regs_set_slot : agree_regs_set_slotStatement := by
  intro j ls rs sl ofs ty v hagree r
  change Val.inject j
    (Locmap.set (S sl ofs ty) v ls (R r)) (rs r)
  rw [show Locmap.set (S sl ofs ty) v ls (R r) = ls (R r) by
    apply Locmap.gso
    simp [Loc.diff]]
  exact hagree r

theorem agree_regs_inject_incr : agree_regs_inject_incrStatement := by
  intro j ls rs j' hagree hinc r
  have hincr_val : ∀ (v v' : CompCert4Lean.Common.Values.val),
      Val.inject j v v' → Val.inject j' v v' := by
    intro v v' hval
    cases hval with
    | inject_int i => exact Val.inject.inject_int i
    | inject_long i => exact Val.inject.inject_long i
    | inject_float f => exact Val.inject.inject_float f
    | inject_single f => exact Val.inject.inject_single f
    | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
        exact Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta
          (hinc b1 b2 delta hmap) hofs
    | val_inject_undef v' => exact Val.inject.val_inject_undef v'
  exact hincr_val _ _ (hagree r)

theorem agree_regs_call_regs : agree_regs_call_regsStatement := by
  intro j ls rs hagree r
  change Val.inject j (LTL.call_regs ls (R r)) (rs r)
  simpa [LTL.call_regs] using hagree r

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Locations

theorem agree_locs_set_reg : agree_locs_set_regStatement := by
  intro return_address_offset tprog cfg f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop ls ls0 r v hagree hbound
  constructor
  · intro r' hn
    by_cases heq : r' = r
    · subst r'
      exact (hn hbound).elim
    · have hdiff : Loc.diff (R r) (R r') := by
        have hne : r ≠ r' := by
          intro h
          exact heq h.symm
        exact hne
      rw [Locmap.gso (R r) v ls (R r') hdiff]
      exact agree_unused_reg hagree r' hn
  · intro ofs ty hin
    rw [show Locmap.set (R r) v ls (S Incoming ofs ty) = ls (S Incoming ofs ty) by
      apply Locmap.gso
      simp [Loc.diff]]
    exact agree_incoming hagree ofs ty hin

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem caller_save_reg_within_bounds :
    caller_save_reg_within_boundsStatement := by
  intro cfg f r hsave
  unfold CompCert4Lean.Backend.Bounds.mreg_within_bounds
  intro hcallee
  have hfalse : False :=
    Bool.noConfusion (P := False) (hsave.symm.trans hcallee)
  exact hfalse.elim

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

theorem agree_locs_set_res : agree_locs_set_resStatement := by
  intro return_address_offset tprog cfg f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop ls0 res
  induction res with
  | BR r =>
      intro v ls hagree hbound
      exact agree_locs_set_reg return_address_offset tprog cfg f
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop ls ls0 r v hagree
        (hbound r List.mem_cons_self)
  | BR_none =>
      intro v ls hagree hbound
      simpa [Locmap.setres] using hagree
  | BR_splitlong hi lo ih_hi ih_lo =>
      intro v ls hagree hbound
      apply ih_lo (v := Val.loword v)
        (ls := Locmap.setres hi (Val.hiword v) ls)
      · apply ih_hi (v := Val.hiword v) (ls := ls) hagree
        intro r hr
        exact hbound r (by simp [params_of_builtin_res, List.mem_append, hr])
      · intro r hr
        exact hbound r (by simp [params_of_builtin_res, List.mem_append, hr])

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Locations

theorem agree_locs_undef_regs : agree_locs_undef_regsStatement := by
  intro return_address_offset tprog cfg f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop ls0 regs ls
  induction regs with
  | nil =>
      intro hagree hbound
      simpa [LTL.undef_regs] using hagree
  | cons r regs ih =>
      intro hagree hbound
      apply agree_locs_set_reg return_address_offset tprog cfg f
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop
        (LTL.undef_regs regs ls) ls0 r CompCert4Lean.Common.Values.Vundef
      · apply ih hagree
        intro r' hr'
        exact hbound r' (by simp [hr'])
      · exact hbound r (by simp)

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds

theorem agree_locs_undef_locs_1 : agree_locs_undef_locs_1Statement := by
  intro return_address_offset tprog cfg f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop ls0 regs ls hagree hcaller
  apply agree_locs_undef_regs return_address_offset tprog cfg f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop ls0 regs ls hagree
  intro r hr
  exact caller_save_reg_within_bounds cfg f r (hcaller r hr)

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds

theorem agree_locs_undef_locs : agree_locs_undef_locsStatement := by
  intro return_address_offset tprog cfg f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop ls0 regs ls hagree hnone
  apply agree_locs_undef_locs_1 return_address_offset tprog cfg f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop ls0 regs ls hagree
  intro r hr
  simp at hnone
  exact hnone r hr

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Lineartyping

theorem agree_locs_set_slot : agree_locs_set_slotStatement := by
  intro cfg f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop ls ls0 sl ofs ty v
    hagree hwritable
  constructor
  · intro r hn
    rw [show Locmap.set (S sl ofs ty) v ls (R r) = ls (R r) by
      apply Locmap.gso
      simp [Loc.diff]]
    exact agree_unused_reg hagree r hn
  · intro ofs' ty' hin
    rw [show Locmap.set (S sl ofs ty) v ls (S Incoming ofs' ty') =
        ls (S Incoming ofs' ty') by
      apply Locmap.gso
      cases sl <;> simp_all [slot_writable, Loc.diff]]
    exact agree_incoming hagree ofs' ty' hin

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Locations

theorem agree_locs_return : agree_locs_returnStatement := by
  intro return_address_offset tprog cfg f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop ls ls0 ls' hagree hcallee
  constructor
  · intro r hnot
    have hsave : CompCert4Lean.X86.Conventions1.is_callee_save cfg r = true := by
      unfold mreg_within_bounds at hnot
      cases h : CompCert4Lean.X86.Conventions1.is_callee_save cfg r with
      | false =>
          exfalso
          apply hnot
          intro hsave'
          rw [h] at hsave'
          cases hsave'
      | true => rfl
    have hls : ls (R r) = ls0 (R r) :=
      agree_unused_reg hagree r hnot
    have hls' : ls' (R r) = ls (R r) := by
      apply hcallee
      simp [CompCert4Lean.Backend.Conventions.callee_save_loc, hsave]
    exact hls'.trans hls
  · intro ofs ty hin
    have hls : ls (S Incoming ofs ty) = ls0 (S Outgoing ofs ty) :=
      agree_incoming hagree ofs ty hin
    have hls' : ls' (S Incoming ofs ty) = ls (S Incoming ofs ty) := by
      apply hcallee
      simp [CompCert4Lean.Backend.Conventions.callee_save_loc]
    exact hls'.trans hls

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem destroyed_by_op_caller_save : destroyed_by_op_caller_saveStatement := by
  intro cfg op
  unfold no_callee_saves
  cases op <;> simp [CompCert4Lean.X86.Machregs.destroyed_by_op,
    CompCert4Lean.X86.Conventions1.is_callee_save]

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem destroyed_by_load_caller_save : destroyed_by_load_caller_saveStatement := by
  intro cfg chunk addr
  unfold no_callee_saves
  rfl

theorem destroyed_by_store_caller_save : destroyed_by_store_caller_saveStatement := by
  intro cfg chunk addr
  unfold no_callee_saves
  by_cases hptr : CompCert4Lean.X86_64.Archi.ptr64 = true <;>
    cases chunk <;>
      simp [hptr, CompCert4Lean.X86.Machregs.destroyed_by_store,
        CompCert4Lean.X86.Conventions1.is_callee_save]

theorem destroyed_by_cond_caller_save : destroyed_by_cond_caller_saveStatement := by
  intro cfg cond
  unfold no_callee_saves
  rfl

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem destroyed_by_jumptable_caller_save :
    destroyed_by_jumptable_caller_saveStatement := by
  intro cfg
  unfold no_callee_saves
  simp [CompCert4Lean.X86.Machregs.destroyed_by_jumptable,
    CompCert4Lean.X86.Conventions1.is_callee_save]

theorem destroyed_by_setstack_caller_save :
    destroyed_by_setstack_caller_saveStatement := by
  intro cfg ty
  unfold no_callee_saves
  cases ty <;>
    simp [CompCert4Lean.X86.Machregs.destroyed_by_setstack,
      CompCert4Lean.X86.Conventions1.is_callee_save]

theorem destroyed_at_function_entry_caller_save :
    destroyed_at_function_entry_caller_saveStatement := by
  intro cfg
  unfold no_callee_saves
  simp [CompCert4Lean.X86.Machregs.destroyed_at_function_entry,
    CompCert4Lean.X86.Conventions1.is_callee_save]

theorem destroyed_by_setstack_function_entry :
    destroyed_by_setstack_function_entryStatement := by
  intro _ _ ty r hr
  cases ty <;>
    simp [CompCert4Lean.X86.Machregs.destroyed_by_setstack,
      CompCert4Lean.X86.Machregs.destroyed_at_function_entry] at hr ⊢
  · exact Or.inr hr
  · exact Or.inr hr

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem transl_destroyed_by_op : transl_destroyed_by_opStatement := by
  intro op fe
  cases op <;> rfl

theorem transl_destroyed_by_load : transl_destroyed_by_loadStatement := by
  intro chunk addr fe
  rfl

theorem transl_destroyed_by_store : transl_destroyed_by_storeStatement := by
  intro chunk addr fe
  cases chunk <;> rfl

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.Values

theorem LTL_undef_regs_same : LTL_undef_regs_sameStatement := by
  intro _return_address_offset _tprog r rl ls hin
  induction rl generalizing ls with
  | nil => simp at hin
  | cons r1 rl ih =>
      simp only [List.mem_cons] at hin
      rcases hin with heq | htail
      · cases heq
        change Locmap.set (R r) Vundef (LTL.undef_regs rl ls) (R r) = Vundef
        simpa using (Locmap.gss (R r) Vundef (LTL.undef_regs rl ls))
      · by_cases heq : r = r1
        · subst r
          change Locmap.set (R r1) Vundef (LTL.undef_regs rl ls) (R r1) = Vundef
          simpa using (Locmap.gss (R r1) Vundef (LTL.undef_regs rl ls))
        · change Locmap.set (R r1) Vundef (LTL.undef_regs rl ls) (R r) = Vundef
          rw [Locmap.gso (R r1) Vundef (LTL.undef_regs rl ls) (R r)
            (fun h => heq h.symm)]
          exact ih ls htail

theorem LTL_undef_regs_others : LTL_undef_regs_othersStatement := by
  intro _return_address_offset _tprog r rl ls hnot
  induction rl generalizing ls with
  | nil => rfl
  | cons r1 rl ih =>
      have hne : r ≠ r1 := by
        intro heq
        apply hnot
        simp [heq]
      have htail : r ∉ rl := by
        intro hin
        apply hnot
        exact List.mem_cons_of_mem r1 hin
      change Locmap.set (R r1) Vundef (LTL.undef_regs rl ls) (R r) = ls (R r)
      rw [Locmap.gso (R r1) Vundef (LTL.undef_regs rl ls) (R r)
        (fun h => hne h.symm)]
      exact ih ls htail

theorem LTL_undef_regs_slot : LTL_undef_regs_slotStatement := by
  intro sl ofs ty rl ls
  induction rl generalizing ls with
  | nil => rfl
  | cons r rl ih =>
      change Locmap.set (R r) Vundef (LTL.undef_regs rl ls) (S sl ofs ty) =
        ls (S sl ofs ty)
      rw [Locmap.gso (R r) Vundef (LTL.undef_regs rl ls) (S sl ofs ty) trivial]
      exact ih ls

theorem undef_regs_type : undef_regs_typeStatement := by
  intro ty l rl ls htype
  induction rl generalizing ls with
  | nil => exact htype
  | cons r rl ih =>
      change Val.has_type (Locmap.set (R r) Vundef (LTL.undef_regs rl ls) l) ty
      unfold Locmap.set
      cases Loc.eq (R r) l with
      | left heq =>
          cases heq
          exact True.intro
      | right _hne =>
          cases Loc.diff_dec (R r) l with
          | left _hdiff => exact ih ls htype
          | right _hnotdiff => exact True.intro

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Integers

private theorem pgo_norm_bool_is_lessdef (v : CompCert4Lean.Common.Values.val) :
    Val.lessdef (Val.norm_bool v) v := by
  unfold Val.norm_bool
  split
  · exact Val.lessdef_refl _
  · exact Val.lessdef_undef _

theorem simplify_load_correct : simplify_load_correctStatement := by
  intro chunk m a v h
  cases a with
  | Vundef => simp [Mem.loadv] at h
  | Vint n => simp [Mem.loadv] at h
  | Vlong n => simp [Mem.loadv] at h
  | Vfloat n => simp [Mem.loadv] at h
  | Vsingle n => simp [Mem.loadv] at h
  | Vptr b ofs =>
      cases chunk with
      | Mbool =>
          change Mem.load Mbool m b (Ptrofs.unsigned ofs) = some v at h
          have hbool := Mem.load_bool_int8_unsigned m b (Ptrofs.unsigned ofs)
          rw [hbool] at h
          cases hload : Mem.load Mint8unsigned m b (Ptrofs.unsigned ofs) with
          | none => simp [hload, CompCert4Lean.Lib.Coqlib.option_map] at h
          | some v' =>
              refine ⟨v', ?_, ?_⟩
              · change Mem.load Mint8unsigned m b (Ptrofs.unsigned ofs) = some v'
                exact hload
              · have hv : Val.norm_bool v' = v := by
                  simpa [hload, CompCert4Lean.Lib.Coqlib.option_map] using h
                rw [← hv]
                exact pgo_norm_bool_is_lessdef v'
      | Mint8signed => exact ⟨v, h, Val.lessdef_refl _⟩
      | Mint8unsigned => exact ⟨v, h, Val.lessdef_refl _⟩
      | Mint16signed => exact ⟨v, h, Val.lessdef_refl _⟩
      | Mint16unsigned => exact ⟨v, h, Val.lessdef_refl _⟩
      | Mint32 => exact ⟨v, h, Val.lessdef_refl _⟩
      | Mint64 => exact ⟨v, h, Val.lessdef_refl _⟩
      | Mfloat32 => exact ⟨v, h, Val.lessdef_refl _⟩
      | Mfloat64 => exact ⟨v, h, Val.lessdef_refl _⟩
      | Many32 => exact ⟨v, h, Val.lessdef_refl _⟩
      | Many64 => exact ⟨v, h, Val.lessdef_refl _⟩

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

open CompCert4Lean.Backend.Stacking

theorem simplify_store_correct : simplify_store_correctStatement := by
  intro chunk m a v m' hstore
  cases a with
  | Vundef => simp [Mem.storev] at hstore
  | Vint n => simp [Mem.storev] at hstore
  | Vlong n => simp [Mem.storev] at hstore
  | Vfloat f => simp [Mem.storev] at hstore
  | Vsingle f => simp [Mem.storev] at hstore
  | Vptr b ofs =>
      rw [← hstore]
      symm
      cases chunk with
      | Mbool => exact Mem.store_bool_unsigned_8 m b (Ptrofs.unsigned ofs) v
      | Mint8signed => exact Mem.store_signed_unsigned_8 m b (Ptrofs.unsigned ofs) v
      | Mint8unsigned => rfl
      | Mint16signed => exact Mem.store_signed_unsigned_16 m b (Ptrofs.unsigned ofs) v
      | Mint16unsigned => rfl
      | Mint32 => rfl
      | Mint64 => rfl
      | Mfloat32 => rfl
      | Mfloat64 => rfl
      | Many32 => rfl
      | Many64 => rfl

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Stacking
open CompCert4Lean.X86.Machregs

theorem simplify_load_destroyed : simplify_load_destroyedStatement := by
  intro chunk addr
  cases chunk <;> rfl

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.Separation
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.X86.Stacklayout

theorem simplify_store_destroyed : simplify_store_destroyedStatement := by
  intro chunk addr
  cases chunk <;> rfl

theorem match_stacks_change_meminj : match_stacks_change_meminjStatement := by
  intro cfg tprog j j' bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop hincr cs cs' sg hmatch
  induction hmatch with
  | match_stacks_empty sg htail =>
      exact match_stacks.match_stacks_empty sg htail
  | @match_stacks_cons f sp ls c cs fb sp' ra c' cs' sg trf htail hfind htransf
      hcode hinj hra hlocs hargs hstacks ih =>
      exact match_stacks.match_stacks_cons f sp ls c cs fb sp' ra c' cs' sg trf
        htail hfind htransf hcode (hincr _ _ _ hinj) hra hlocs hargs ih

theorem match_stacks_change_sig : match_stacks_change_sigStatement := by
  intro cfg tprog sg1 j bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop cs cs' sg hmatch htail1
  induction hmatch with
  | match_stacks_empty sg htail =>
      exact match_stacks.match_stacks_empty sg1 htail1
  | @match_stacks_cons f sp ls c cs fb sp' ra c' cs' sg trf htail hfind htransf
      hcode hinj hra hlocs hargs hstacks ih =>
      apply match_stacks.match_stacks_cons f sp ls c cs fb sp' ra c' cs' sg1 trf
        htail hfind htransf hcode hinj hra hlocs
      intro ofs ty harg
      exact (htail1 (S Outgoing ofs ty) harg).elim
      exact hstacks

private theorem stackingproof_massert_imp_refl (P : massert) : massert_imp P P := by
  constructor
  · intro m h
    exact h
  · intro b ofs h
    exact h

private theorem stackingproof_frame_contents_incr
    (return_address_offset : Mach.function → Mach.code →
      CompCert4Lean.Lib.Integers.ptrofs → Prop)
    (tprog : Mach.program) (cfg : CompilerConfig) (f : Linear.function)
    (bound_local_pos : bound_local_pos cfg (function_bounds cfg f))
    (bound_outgoing_pos : bound_outgoing_pos cfg (function_bounds cfg f))
    (bound_stack_data_pos : bound_stack_data_pos cfg (function_bounds cfg f))
    (used_callee_save_norepet : used_callee_save_norepet cfg (function_bounds cfg f))
    (used_callee_save_prop : used_callee_save_prop cfg (function_bounds cfg f))
    (j j' : meminj) (sp : block) (ls ls0 : locset) (parent retaddr : val)
    (hinc : inject_incr j j') :
    massert_imp
      (frame_contents return_address_offset tprog cfg f bound_local_pos
        bound_outgoing_pos bound_stack_data_pos used_callee_save_norepet
        used_callee_save_prop j sp ls ls0 parent retaddr)
      (frame_contents return_address_offset tprog cfg f bound_local_pos
        bound_outgoing_pos bound_stack_data_pos used_callee_save_norepet
        used_callee_save_prop j' sp ls ls0 parent retaddr) := by
  let b := function_bounds cfg f
  let fe := make_env cfg b
  have hlocal : massert_imp
      (contains_locations return_address_offset tprog j sp fe.fe_ofs_local
        b.bound_local Local ls)
      (contains_locations return_address_offset tprog j' sp fe.fe_ofs_local
        b.bound_local Local ls) :=
    contains_locations_incr return_address_offset tprog j j' sp fe.fe_ofs_local
      b.bound_local Local ls hinc
  have hout : massert_imp
      (contains_locations return_address_offset tprog j sp (fe_ofs_arg cfg)
        b.bound_outgoing Outgoing ls)
      (contains_locations return_address_offset tprog j' sp (fe_ofs_arg cfg)
        b.bound_outgoing Outgoing ls) :=
    contains_locations_incr return_address_offset tprog j j' sp (fe_ofs_arg cfg)
      b.bound_outgoing Outgoing ls hinc
  have hlink : massert_imp
      (hasvalue CompCert4Lean.Common.AST.Mptr sp fe.fe_ofs_link parent)
      (hasvalue CompCert4Lean.Common.AST.Mptr sp fe.fe_ofs_link parent) :=
    stackingproof_massert_imp_refl _
  have hret : massert_imp
      (hasvalue CompCert4Lean.Common.AST.Mptr sp fe.fe_ofs_retaddr retaddr)
      (hasvalue CompCert4Lean.Common.AST.Mptr sp fe.fe_ofs_retaddr retaddr) :=
    stackingproof_massert_imp_refl _
  have hcallee : massert_imp
      (contains_callee_saves j sp fe.fe_ofs_callee_save b.used_callee_save ls0)
      (contains_callee_saves j' sp fe.fe_ofs_callee_save b.used_callee_save ls0) :=
    contains_callee_saves_incr j j' sp ls0 hinc b.used_callee_save
      fe.fe_ofs_callee_save
  have hframe1 : massert_imp
      (frame_contents_1 return_address_offset tprog cfg f bound_local_pos
        bound_outgoing_pos bound_stack_data_pos used_callee_save_norepet
        used_callee_save_prop j sp ls ls0 parent retaddr)
      (frame_contents_1 return_address_offset tprog cfg f bound_local_pos
        bound_outgoing_pos bound_stack_data_pos used_callee_save_norepet
        used_callee_save_prop j' sp ls ls0 parent retaddr) := by
    exact stackingproof_massert_imp_sepconj hlocal
      (stackingproof_massert_imp_sepconj hout
        (stackingproof_massert_imp_sepconj hlink
          (stackingproof_massert_imp_sepconj hret hcallee)))
  exact stackingproof_massert_imp_mconj hframe1
    (stackingproof_massert_imp_sepconj
      (stackingproof_massert_imp_refl _) (stackingproof_massert_imp_refl _))

theorem stack_contents_change_meminj : stack_contents_change_meminjStatement := by
  intro return_address_offset tprog cfg m j j' bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop hincr cs cs' P
  have hstack : massert_imp
      (stack_contents return_address_offset tprog cfg j cs cs'
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop)
      (stack_contents return_address_offset tprog cfg j' cs cs'
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop) := by
    induction cs generalizing cs' with
    | nil =>
        cases cs' with
        | nil =>
            simpa [stack_contents] using
              (stackingproof_massert_imp_refl (pure True))
        | cons sf cs' =>
            simpa [stack_contents] using
              (stackingproof_massert_imp_refl (pure False))
    | cons sf cs ih =>
        cases sf with
        | Stackframe f fsp ls c =>
            cases cs' with
            | nil =>
                simpa [stack_contents] using
                  (stackingproof_massert_imp_refl (pure False))
            | cons sf' cs' =>
                cases sf' with
                | Stackframe fb sptarget ra c' =>
                    cases sptarget with
                    | Vptr sp' ofs' =>
                        have hframe := stackingproof_frame_contents_incr
                          return_address_offset tprog cfg f
                          (bound_local_pos f) (bound_outgoing_pos f)
                          (bound_stack_data_pos f)
                          (used_callee_save_norepet f)
                          (used_callee_save_prop f) j j' sp' ls
                          (Linear.parent_locset cs) (Mach.parent_sp cs')
                          (Mach.parent_ra cs') hincr
                        have htail := ih (cs' := cs')
                        simpa [stack_contents] using
                          (stackingproof_massert_imp_sepconj hframe htail)
                    | Vundef =>
                        simpa [stack_contents] using
                          (stackingproof_massert_imp_refl (pure False))
                    | Vint n =>
                        simpa [stack_contents] using
                          (stackingproof_massert_imp_refl (pure False))
                    | Vlong n =>
                        simpa [stack_contents] using
                          (stackingproof_massert_imp_refl (pure False))
                    | Vfloat n =>
                        simpa [stack_contents] using
                          (stackingproof_massert_imp_refl (pure False))
                    | Vsingle n =>
                        simpa [stack_contents] using
                          (stackingproof_massert_imp_refl (pure False))
  intro hpred
  exact (stackingproof_massert_imp_sepconj hstack
    (stackingproof_massert_imp_refl P)).1 m hpred

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

theorem find_label_save_callee_save : find_label_save_callee_saveStatement := by
  intro lbl l ofs k
  induction l generalizing ofs with
  | nil => rfl
  | cons r rl ih =>
      simp [save_callee_save_rec, Mach.find_label, Mach.is_label, ih]

theorem find_label_restore_callee_save : find_label_restore_callee_saveStatement := by
  intro lbl l ofs k
  induction l generalizing ofs with
  | nil => rfl
  | cons r rl ih =>
      simp [restore_callee_save_rec, Mach.find_label, Mach.is_label, ih]

theorem match_stacks_type_sp : match_stacks_type_spStatement := by
  intro cfg tprog j bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop cs cs' sg hmatch
  cases hmatch with
  | match_stacks_empty sg htail =>
      exact Val.Vnullptr_has_type
  | @match_stacks_cons f sp ls c cs fb sp' ra c' cs' sg trf
      htail hfind htransf hcode hinj hra hlocs hargs hstacks =>
      exact Val.Vptr_has_type sp' Ptrofs.zero

theorem match_stacks_type_retaddr : match_stacks_type_retaddrStatement := by
  intro cfg tprog j bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop cs cs' sg hmatch
  cases hmatch with
  | match_stacks_empty sg htail =>
      exact Val.Vnullptr_has_type
  | @match_stacks_cons f sp ls c cs fb sp' ra c' cs' sg trf
      htail hfind htransf hcode hinj hra hlocs hargs hstacks =>
      exact hra

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Lib.Coqlib

private theorem stackingproof_list_fold_left_append
    {A B : Type} (f : A → B → B) (acc : B) (xs ys : List A) :
    CompCert4Lean.Lib.Coqlib.list_fold_left f acc (xs ++ ys) =
      CompCert4Lean.Lib.Coqlib.list_fold_left f
        (CompCert4Lean.Lib.Coqlib.list_fold_left f acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, CompCert4Lean.Lib.Coqlib.list_fold_left]
      exact ih (f x acc)

private theorem stackingproof_list_fold_right_cons
    {A B : Type} (f : A → B → B) (x : A) (xs : List A) (acc : B) :
    CompCert4Lean.Lib.Coqlib.list_fold_right f (x :: xs) acc =
      f x (CompCert4Lean.Lib.Coqlib.list_fold_right f xs acc) := by
  unfold CompCert4Lean.Lib.Coqlib.list_fold_right
  rw [List.reverse_cons, stackingproof_list_fold_left_append]
  rfl

theorem transl_code_eq : transl_code_eqStatement := by
  intro cfg fe i c
  unfold transl_code
  exact stackingproof_list_fold_right_cons (transl_instr cfg fe) i c []

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Lib.Coqlib

theorem find_label_transl_code : find_label_transl_codeStatement := by
  intro cfg fe lbl c
  induction c with
  | nil => rfl
  | cons i c ih =>
      rw [transl_code_eq]
      cases i with
      | Lgetstack sl ofs ty dst =>
          cases sl <;>
            simp [transl_instr, Mach.find_label, Mach.is_label,
              Linear.is_label, Linear.find_label, ih]
      | Lsetstack src sl ofs ty =>
          cases sl <;>
            simp [transl_instr, Mach.find_label, Mach.is_label,
              Linear.is_label, Linear.find_label, ih]
      | Lop op args res =>
          simp [transl_instr, Mach.find_label, Mach.is_label,
            Linear.is_label, Linear.find_label, ih]
      | Lload chunk addr args dst =>
          simp [transl_instr, Mach.find_label, Mach.is_label,
            Linear.is_label, Linear.find_label, ih]
      | Lstore chunk addr args src =>
          simp [transl_instr, Mach.find_label, Mach.is_label,
            Linear.is_label, Linear.find_label, ih]
      | Lcall sig ros =>
          simp [transl_instr, Mach.find_label, Mach.is_label,
            Linear.is_label, Linear.find_label, ih]
      | Ltailcall sig ros =>
          simp only [transl_instr, restore_callee_save]
          rw [find_label_restore_callee_save lbl fe.fe_used_callee_save
            fe.fe_ofs_callee_save (Mtailcall sig ros :: transl_code cfg fe c)]
          simp [Mach.find_label, Mach.is_label, Linear.is_label,
            Linear.find_label, ih]
      | Lbuiltin ef args res =>
          simp [transl_instr, Mach.find_label, Mach.is_label,
            Linear.is_label, Linear.find_label, ih]
      | Llabel lbl' =>
          cases h : peq lbl lbl' <;>
            simp [transl_instr, Mach.find_label, Mach.is_label,
              Linear.is_label, Linear.find_label, Option.map, h, ih]
      | Lgoto lbl' =>
          simp [transl_instr, Mach.find_label, Mach.is_label,
            Linear.is_label, Linear.find_label, ih]
      | Lcond cond args lbl' =>
          simp [transl_instr, Mach.find_label, Mach.is_label,
            Linear.is_label, Linear.find_label, ih]
      | Ljumptable arg tbl =>
          simp [transl_instr, Mach.find_label, Mach.is_label,
            Linear.is_label, Linear.find_label, ih]
      | Lreturn =>
          simp only [transl_instr, restore_callee_save]
          rw [find_label_restore_callee_save lbl fe.fe_used_callee_save
            fe.fe_ofs_callee_save (Mreturn :: transl_code cfg fe c)]
          simp [Mach.find_label, Mach.is_label, Linear.is_label,
            Linear.find_label, ih]

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.X86.Stacklayout

theorem transl_find_label : transl_find_labelStatement := by
  intro cfg f tf lbl c htrans hfind
  rw [unfold_transf_function cfg f tf htrans]
  change Mach.find_label lbl
      (save_callee_save (make_env cfg (function_bounds cfg f))
        (transl_code cfg (make_env cfg (function_bounds cfg f)) f.fn_code)) = _
  unfold CompCert4Lean.Backend.Linear.label at lbl
  change CompCert4Lean.Backend.Mach.label at lbl
  unfold save_callee_save
  rw [find_label_save_callee_save]
  change Mach.find_label lbl
      (transl_code cfg (make_env cfg (function_bounds cfg f))
        (show List CompCert4Lean.Backend.Linear.instruction from f.fn_code)) = _
  rw [find_label_transl_code]
  rw [hfind]
  rfl

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Lib.Coqlib

theorem find_label_tail : find_label_tailStatement := by
  intro lbl c c' h
  induction c with
  | nil =>
      simp [Linear.find_label] at h
  | cons i c ih =>
      cases hlabel : Linear.is_label lbl i with
      | true =>
          simp [Linear.find_label, hlabel] at h
          cases h
          exact is_tail.cons _ (is_tail.refl _)
      | false =>
          simp [Linear.find_label, hlabel] at h
          exact is_tail.cons _ (ih h)

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Lib.Coqlib

theorem is_tail_save_callee_save : is_tail_save_callee_saveStatement := by
  intro l ofs k
  induction l generalizing ofs with
  | nil => exact is_tail.refl k
  | cons r l ih =>
      simp only [save_callee_save_rec]
      exact is_tail.cons _ (ih
        (ofs := zAdd (align ofs (CompCert4Lean.Common.AST.typesize
          (CompCert4Lean.X86.Machregs.mreg_type r)))
          (CompCert4Lean.Common.AST.typesize (CompCert4Lean.X86.Machregs.mreg_type r)))
        )

theorem is_tail_restore_callee_save : is_tail_restore_callee_saveStatement := by
  intro l ofs k
  induction l generalizing ofs with
  | nil => exact is_tail.refl k
  | cons r l ih =>
      simp only [restore_callee_save_rec]
      exact is_tail.cons _ (ih
        (ofs := zAdd (align ofs (CompCert4Lean.Common.AST.typesize
          (CompCert4Lean.X86.Machregs.mreg_type r)))
          (CompCert4Lean.Common.AST.typesize (CompCert4Lean.X86.Machregs.mreg_type r)))
        )

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Lib.Coqlib

theorem is_tail_transl_instr : is_tail_transl_instrStatement := by
  intro cfg fe i k
  cases i with
  | Lgetstack sl ofs ty dst =>
      cases sl <;> exact is_tail.cons _ (is_tail.refl k)
  | Lsetstack src sl ofs ty =>
      cases sl
      · exact is_tail.cons _ (is_tail.refl k)
      · exact is_tail.refl k
      · exact is_tail.cons _ (is_tail.refl k)
  | Lop op args res => exact is_tail.cons _ (is_tail.refl k)
  | Lload chunk addr args dst => exact is_tail.cons _ (is_tail.refl k)
  | Lstore chunk addr args src => exact is_tail.cons _ (is_tail.refl k)
  | Lcall sig ros => exact is_tail.cons _ (is_tail.refl k)
  | Ltailcall sig ros =>
      simp only [transl_instr, restore_callee_save]
      exact is_tail_trans _ k (Mtailcall sig ros :: k)
        (is_tail.cons _ (is_tail.refl k)) _
        (is_tail_restore_callee_save fe.fe_used_callee_save fe.fe_ofs_callee_save
          (Mtailcall sig ros :: k))
  | Lbuiltin ef args res => exact is_tail.cons _ (is_tail.refl k)
  | Llabel lbl => exact is_tail.cons _ (is_tail.refl k)
  | Lgoto lbl => exact is_tail.cons _ (is_tail.refl k)
  | Lcond cond args lbl => exact is_tail.cons _ (is_tail.refl k)
  | Ljumptable arg tbl => exact is_tail.cons _ (is_tail.refl k)
  | Lreturn =>
      simp only [transl_instr, restore_callee_save]
      exact is_tail_trans _ k (Mreturn :: k)
        (is_tail.cons _ (is_tail.refl k)) _
        (is_tail_restore_callee_save fe.fe_used_callee_save fe.fe_ofs_callee_save
          (Mreturn :: k))

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Lib.Coqlib

theorem is_tail_transl_code : is_tail_transl_codeStatement := by
  intro cfg fe c1 c2 h
  induction h with
  | refl c => exact is_tail.refl (transl_code cfg fe c)
  | cons i htail ih =>
      rw [transl_code_eq]
      exact is_tail_trans _ (transl_code cfg fe _) (transl_code cfg fe _)
        ih _ (is_tail_transl_instr cfg fe i (transl_code cfg fe _))

end CompCert4Lean.Backend.Stackingproof
