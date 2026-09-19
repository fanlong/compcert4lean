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

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem is_tail_transf_function : is_tail_transf_functionStatement := by
  intro cfg f tf c htf htail
  rw [unfold_transf_function cfg f tf htf]
  unfold transl_body
  exact is_tail_trans _
    (transl_code cfg (CompCert4Lean.X86.Stacklayout.make_env cfg
      (CompCert4Lean.Backend.Bounds.function_bounds cfg f)) c)
    (transl_code cfg (CompCert4Lean.X86.Stacklayout.make_env cfg
      (CompCert4Lean.Backend.Bounds.function_bounds cfg f)) f.fn_code)
    (is_tail_transl_code cfg (CompCert4Lean.X86.Stacklayout.make_env cfg
      (CompCert4Lean.Backend.Bounds.function_bounds cfg f)) c f.fn_code htail)
    _ (is_tail_save_callee_save
      (CompCert4Lean.X86.Stacklayout.make_env cfg
        (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_used_callee_save
      (CompCert4Lean.X86.Stacklayout.make_env cfg
        (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_ofs_callee_save
      (transl_code cfg (CompCert4Lean.X86.Stacklayout.make_env cfg
        (CompCert4Lean.Backend.Bounds.function_bounds cfg f)) f.fn_code))

theorem symbols_preserved : symbols_preservedStatement := by
  intro cfg prog tprog hm s
  unfold match_prog at hm
  exact @CompCert4Lean.Common.Globalenvs.Genv.find_symbol_transf_partial
    Linear.fundef Mach.fundef Unit
    (Linker_fundef Linear.function) Linker_unit
    (transf_fundef cfg)
    prog tprog hm s

theorem senv_preserved : senv_preservedStatement := by
  intro cfg prog tprog hm
  unfold match_prog at hm
  exact @CompCert4Lean.Common.Globalenvs.Genv.senv_transf_partial
    Linear.fundef Mach.fundef Unit
    (Linker_fundef Linear.function) Linker_unit
    (transf_fundef cfg)
    prog tprog hm

theorem function_ptr_translated : function_ptr_translatedStatement := by
  intro cfg prog tprog hm b f hfind
  unfold match_prog at hm
  exact @CompCert4Lean.Common.Globalenvs.Genv.find_funct_ptr_transf_partial
    Linear.fundef Mach.fundef Unit
    (Linker_fundef Linear.function) Linker_unit
    (transf_fundef cfg)
    prog tprog hm b f hfind

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Separation
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers

private theorem stackingproof_ptrofs_zero_add_zero :
    Ptrofs.add Ptrofs.zero (Ptrofs.repr (.Z0 : Z)) = Ptrofs.zero := by
  rfl

theorem find_function_translated : find_function_translatedStatement := by
  intro cfg prog tprog hmatch j ls rs m ros f hregs hge hfind
  cases ros with
  | inl r =>
      unfold Linear.find_function at hfind
      have hinv := Genv.find_funct_inv (F := Linear.fundef) (V := Unit)
        (Genv.globalenv prog) (ls (.R r)) f hfind
      rcases hinv with ⟨b, hb⟩
      have hfun : Genv.find_funct (Genv.globalenv prog)
          (.Vptr b Ptrofs.zero) = some f := by
        rw [← hb]
        exact hfind
      have hptr : Genv.find_funct_ptr (Genv.globalenv prog) b = some f := by
        rw [Genv.find_funct_find_funct_ptr] at hfun
        exact hfun
      rcases function_ptr_translated cfg prog tprog hmatch b f hptr with
        ⟨tf, htf, htransf⟩
      rcases hge with ⟨bound, _, hpres⟩
      rcases hpres with ⟨DOMAIN, _, _, FUNCTIONS, _⟩
      have hbnd : Plt b bound := FUNCTIONS b f hptr
      have hj : j b = some (b, .Z0) := DOMAIN b hbnd
      have hreg := hregs r
      rw [hb] at hreg
      generalize hrs : rs r = vr at hreg
      cases hreg with
      | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
          have hmap' : (b2, delta) = (b, .Z0) := by
            exact Option.some.inj (hmap.symm.trans hj)
          rcases hmap' with ⟨rfl, rfl⟩
          have hofs' : ofs2 = Ptrofs.zero := by
            rw [stackingproof_ptrofs_zero_add_zero] at hofs
            exact hofs
          refine ⟨b, tf, ?_, htf, htransf⟩
          unfold Mach.find_function_ptr
          simp only [Sum.rec]
          rw [hrs, hofs']
          simp [Ptrofs.eq, WordCore.eq]
  | inr symb =>
      unfold Linear.find_function at hfind
      cases hs : Genv.find_symbol (Genv.globalenv prog) symb with
      | none => simp [hs] at hfind
      | some b =>
          have hptr : Genv.find_funct_ptr (Genv.globalenv prog) b = some f := by
            simpa [hs] using hfind
          rcases function_ptr_translated cfg prog tprog hmatch b f hptr with
            ⟨tf, htf, htransf⟩
          have hs' : Genv.find_symbol (Genv.globalenv tprog) symb = some b := by
            exact (symbols_preserved cfg prog tprog hmatch symb).trans hs
          refine ⟨b, tf, ?_, htf, htransf⟩
          unfold Mach.find_function_ptr
          simp [hs']

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Lineartyping
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Separation
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem wt_prog : wt_progStatement := by
  intro cfg prog tprog hmatch
  letI : Linker Linear.fundef := Linker_fundef Linear.function
  letI : Linker Unit := Linker_unit
  letI : Linker Linear.program := Linker_prog Linear.fundef Unit
  intro i fd hmem
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch
  rcases hmatch with ⟨hdefs, _, _⟩
  rcases @list_forall2_in_left _ _ _ _ _ _ hdefs hmem with ⟨ig', _, hrel⟩
  rcases ig' with ⟨i', gd'⟩
  simp only [match_ident_globdef] at hrel
  rcases hrel with ⟨_, hgd⟩
  cases fd with
  | Internal f =>
      change wt_fundef cfg (CompCert4Lean.Common.AST.fundef.Internal f)
      cases gd' with
      | Gfun tf =>
          cases hgd with
          | match_globdef_fun _ _ _ _ hfun =>
              unfold CompCert4Lean.Backend.Stacking.transf_fundef
                CompCert4Lean.Common.AST.transf_partial_fundef at hfun
              unfold CompCert4Lean.Backend.Stacking.transf_function at hfun
              cases hwt : wt_function cfg f with
              | false =>
                  simp [hwt] at hfun
              | true =>
                  simp [hwt] at hfun
                  exact hwt
      | Gvar v => cases hgd
  | External ef =>
      change wt_fundef cfg (CompCert4Lean.Common.AST.fundef.External ef)
      trivial

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Conventions1

private theorem stackingproof_inject_vint_eq (j : Val.meminj)
    (i : CompCert4Lean.Lib.Integers.Int.int) (v : val) :
    Val.inject j (Vint i) v → v = Vint i := by
  intro h
  cases h with
  | inject_int => rfl

theorem transf_final_states : transf_final_statesStatement := by
  intro cfg return_address_offset prog tprog bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
    st1 st2 r hmatch hfinal
  cases hfinal with
  | final_state_intro rs m _ =>
      cases hmatch with
      | match_states_return cs ls m cs' rs' m' j sg hstacks hregs hsep =>
          cases hstacks
          have hresult' : Locmap.getpair
              (map_rpair R (loc_result signature_main)) rs = Vint r := by
            assumption
          have hR : ∃ rres, loc_result signature_main = .One rres := by
            cases h : loc_result signature_main with
            | One rres => exact ⟨rres, rfl⟩
            | Twolong r1 r2 =>
                have hty := loc_result_type signature_main
                rw [h] at hty
                simp [CompCert4Lean.Common.AST.signature_main,
                  CompCert4Lean.Common.AST.proj_sig_res,
                  CompCert4Lean.Common.AST.proj_xtype,
                  CompCert4Lean.Common.AST.subtype,
                  CompCert4Lean.Common.AST.typ_rpair,
                  CompCert4Lean.X86.Machregs.mreg_type,
                  CompCert4Lean.X86_64.Archi.ptr64] at hty
          rcases hR with ⟨rres, hR⟩
          rw [hR] at hresult'
          simp only [Locmap.getpair, map_rpair] at hresult'
          have hagree := hregs rres
          rw [hresult'] at hagree
          have hval : rs' rres = Vint r :=
            stackingproof_inject_vint_eq j r (rs' rres) hagree
          exact Mach.final_state.final_state_intro rs' m' rres r hR hval

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Lineartyping
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Separation
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem transf_initial_states : transf_initial_statesStatement := by
  letI : Linker Linear.fundef := Linker_fundef Linear.function
  letI : Linker Unit := Linker_unit
  letI : Linker Mach.fundef := Linker_fundef Mach.function
  letI : Linker Linear.program := Linker_prog Linear.fundef Unit
  letI : Linker Mach.program := Linker_prog Mach.fundef Unit
  intro cfg return_address_offset prog tprog bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop hmatch st1 hinit
  cases hinit with
  | initial_state_intro b f m0 hmem hsymb hfun hsig =>
      rcases function_ptr_translated cfg prog tprog hmatch b f hfun with
        ⟨tf, hfind, htransf⟩
      refine ⟨Mach.Callstate [] b
        (CompCert4Lean.Backend.Mach.Regmap.init Vundef) m0, ?_, ?_⟩
      · apply Mach.initial_state.initial_state_intro b m0
        · unfold Genv.init_mem at hmem ⊢
          exact Genv.init_mem_transf_partial
            (A := Linear.fundef) (B := Mach.fundef) (V := Unit)
            (transf := fun f => CompCert4Lean.Backend.Stacking.transf_fundef cfg f)
            prog tprog hmatch m0 hmem
        · change Genv.find_symbol (Genv.globalenv tprog) tprog.prog_main = some b
          rw [hmatch.2.1]
          rw [symbols_preserved cfg prog tprog hmatch prog.prog_main]
          exact hsymb
      · apply match_states_call [] f
          (CompCert4Lean.Backend.Locations.Locmap.init Vundef) m0 [] b
          (CompCert4Lean.Backend.Mach.Regmap.init Vundef) m0
          (CompCert4Lean.Common.Memory.Mem.flat_inj
            (CompCert4Lean.Common.Memory.Mem.nextblock m0)) tf
        · apply match_stacks_empty
          rw [hsig]
          unfold tailcall_possible
          have hloc :
              CompCert4Lean.X86.Conventions1.loc_arguments cfg
                CompCert4Lean.Common.AST.signature_main = [] := by
            simp [CompCert4Lean.X86.Conventions1.loc_arguments,
              CompCert4Lean.X86.Conventions1.loc_arguments_32,
              CompCert4Lean.X86.Conventions1.loc_arguments_elf64,
              CompCert4Lean.X86.Conventions1.loc_arguments_win64,
              CompCert4Lean.Common.AST.signature_main,
              CompCert4Lean.Common.AST.proj_sig_args]
          change ∀ l, l ∈ regs_of_rpairs
            (CompCert4Lean.X86.Conventions1.loc_arguments cfg
              CompCert4Lean.Common.AST.signature_main) → _
          rw [hloc]
          intro l hl
          simp [CompCert4Lean.Common.AST.regs_of_rpairs] at hl
        · exact htransf
        · exact hfind
        · intro r
          exact Val.val_inject_undef _ _
        · have hmeminj : Mem.inject
              (Mem.flat_inj (Mem.nextblock m0)) m0 m0 :=
              Genv.initmem_inject (F := Linear.fundef) (V := Unit) prog m0 hmem
          have hgenv : (globalenv_inject (Genv.globalenv prog)
              (Mem.flat_inj (Mem.nextblock m0))).m_pred m0 := by
            refine ⟨Mem.nextblock m0, Ple_refl _, ?_⟩
            apply globalenv_preserved_intro
            · intro b hb
              unfold Mem.flat_inj
              cases hdec : CompCert4Lean.Lib.Coqlib.plt b (Mem.nextblock m0) with
              | left hleft => rfl
              | right hright => exact False.elim (hright hb)
            · intro b1 b2 delta hmap hb
              unfold Mem.flat_inj at hmap
              cases hp : CompCert4Lean.Lib.Coqlib.plt b1 (Mem.nextblock m0) with
              | left hleft =>
                  rw [show CompCert4Lean.Lib.Coqlib.plt b1 (Mem.nextblock m0) =
                    .left hleft from hp] at hmap
                  cases hmap
                  rfl
              | right hright =>
                  rw [show CompCert4Lean.Lib.Coqlib.plt b1 (Mem.nextblock m0) =
                    .right hright from hp] at hmap
                  cases hmap
            · intro id b hfind
              change Mem.valid_block m0 b
              exact Genv.find_symbol_not_fresh Linear.fundef Unit prog id b m0 hmem hfind
            · intro b fd hfind
              change Mem.valid_block m0 b
              exact Genv.find_funct_ptr_not_fresh Linear.fundef Unit prog b fd m0 hmem hfind
            · intro b gv hfind
              change Mem.valid_block m0 b
              exact Genv.find_var_info_not_fresh Linear.fundef Unit prog b gv m0 hmem hfind
          simp only [stack_contents, sepconj, CompCert4Lean.Common.Separation.pure,
            minjection, globalenv_inject]
          refine ⟨trivial, ⟨hmeminj, hgenv, ?_⟩, ?_⟩
          · intro b ofs _ hfalse
            exact hfalse.elim
          · intro b ofs _ _
            exact False.elim (by assumption)

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Separation
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private def stackingproofPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem stackingproof_wordcore_add_val {bits : Nat}
    (x y : WordCore.Word bits) :
    (WordCore.add x y).val = (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (stackingproofPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem stackingproof_wordcore_zero_val (bits : Nat) :
    (WordCore.zero bits).val = 0 := by
  unfold WordCore.zero
  run_tac
    let lctx ← getLCtx
    let bF := (lctx.findFromUserName? `bits).get!
    let e ← mkAppM
      (stackingproofPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")
      #[mkFVar bF.fvarId,
        mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0]
    closeMainGoal Name.anonymous e

private theorem stackingproof_wordcore_val_lt {bits : Nat}
    (x : WordCore.Word bits) : x.val < 2 ^ bits := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (stackingproofPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e

private theorem stackingproof_ptrofs_unsigned_repr (z : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hz : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 z ∧
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le z Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.repr z) = z := by
  have hzi : z = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) :=
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ z).symm
  rw [hzi]
  change (CompCert4Lean.Lib.Integers.WordCore.repr Ptrofs.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z))).intval = _
  let w := CompCert4Lean.Lib.Integers.WordCore.repr Ptrofs.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z))
  have hi : w.val = Int.toNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z %
        ((2 ^ Ptrofs.wordsize : Nat) : Int)) := by
    dsimp [w]
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "WordCore.val_repr")
        | throwError "frozen WordCore.val_repr helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `z
      evalTactic
        (← `(tactic| exact $stx Ptrofs.wordsize
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ $arg)))
  have hwi : w.intval =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat w.val := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith
            "WordCore.intval_eq_zOfNat_val")
        | throwError "frozen WordCore.intval_eq_zOfNat_val helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `w
      evalTactic (← `(tactic| exact $stx $arg))
  change w.intval = _
  rw [hwi, hi]
  have hznonneg : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z := hz.1
  have hzmax := hz.2
  have hmodpow : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ptrofs.modulus =
      (2 ^ Ptrofs.wordsize : Nat) := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith
            "WordCore.twoPowerNat_eq_zOfNat_twoPow")
        | throwError "frozen WordCore.twoPowerNat_eq_zOfNat_twoPow helper not found"
      let stx := Lean.mkIdent n
      evalTactic
        (← `(tactic| exact congrArg
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          ($stx Ptrofs.wordsize)))
  have hzlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z <
      (2 ^ Ptrofs.wordsize : Nat) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ptrofs.max_unsigned at hzmax
    unfold Ptrofs.max_unsigned at hzmax
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
          Ptrofs.modulus
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1)) at hzmax
    unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub at hzmax
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hzmax
    rw [hmodpow] at hzmax
    have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1) =
        (1 : Int) := by rfl
    rw [hone, Int.natCast_pow] at hzmax
    have hzmax' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
        (2 : Int) ^ Ptrofs.wordsize - 1 := by
      exact hzmax
    omega
  rw [Int.emod_eq_of_lt hznonneg hzlt]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (Int.ofNat (Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z))) = _
  exact congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
    (Int.toNat_of_nonneg hznonneg)

theorem contains_get_stack : contains_get_stackStatement := by
  intro spec m ty sp ofs h
  rcases h with ⟨⟨hlo, hhi⟩, hvalid, v, hload, hspec⟩
  refine ⟨v, ?_, hspec⟩
  unfold Mach.load_stack Mem.loadv
  simp only [Val.offset_ptr]
  have hadd : Ptrofs.add Ptrofs.zero (Ptrofs.repr ofs) = Ptrofs.repr ofs := by
    change WordCore.add (WordCore.zero Ptrofs.wordsize)
      (WordCore.repr Ptrofs.wordsize ofs) =
      WordCore.repr Ptrofs.wordsize ofs
    apply WordCore.ext_of_val_eq
    rw [stackingproof_wordcore_add_val]
    have hzero : (WordCore.zero Ptrofs.wordsize).val = 0 := by
      rfl
    rw [hzero, Nat.zero_add]
    exact Nat.mod_eq_of_lt (stackingproof_wordcore_val_lt _)
  rw [hadd]
  change Mem.load (chunk_of_type ty) m sp (Ptrofs.unsigned (Ptrofs.repr ofs)) = some v
  rw [stackingproof_ptrofs_unsigned_repr ofs ⟨hlo, hhi⟩]
  exact hload

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem hasvalue_get_stack : hasvalue_get_stackStatement := by
  intro ty m sp ofs v h
  obtain ⟨v', hload, heq⟩ := contains_get_stack (fun v' => v' = v) m ty sp ofs h
  exact heq ▸ hload

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Locations

theorem get_location : get_locationStatement := by
  intro return_address_offset tprog m j sp pos bound sl ls ofs ty hcontains hofs hbound halign
  rcases hcontains with ⟨hdiv, hpos, hover, hperm, hload⟩
  rcases hload ofs ty hofs hbound halign with ⟨v, hv, hinj⟩
  refine ⟨v, ?_, hinj⟩
  unfold Mach.load_stack Mem.loadv
  simp only [Val.offset_ptr]
  have hadd : Ptrofs.add Ptrofs.zero
      (Ptrofs.repr (zAdd pos (zMul z4 ofs))) =
      Ptrofs.repr (zAdd pos (zMul z4 ofs)) := by
    change WordCore.add (WordCore.zero Ptrofs.wordsize)
      (WordCore.repr Ptrofs.wordsize (zAdd pos (zMul z4 ofs))) =
      WordCore.repr Ptrofs.wordsize (zAdd pos (zMul z4 ofs))
    apply WordCore.ext_of_val_eq
    rw [stackingproof_wordcore_add_val]
    have hzero : (WordCore.zero Ptrofs.wordsize).val = 0 := by
      rfl
    rw [hzero, Nat.zero_add]
    exact Nat.mod_eq_of_lt (stackingproof_wordcore_val_lt _)
  rw [hadd]
  change Mem.load (chunk_of_type ty) m sp
      (Ptrofs.unsigned (Ptrofs.repr (zAdd pos (zMul z4 ofs)))) = some v
  have haddr0 : zLe z0 (zAdd pos (zMul z4 ofs)) :=
    locationAddrNonneg pos ofs hpos hofs
  have haddrmax : zLe (zAdd pos (zMul z4 ofs)) Ptrofs.max_unsigned :=
    locationAddrMax pos bound ofs ty hover hbound
  rw [stackingproof_ptrofs_unsigned_repr _ ⟨haddr0, haddrmax⟩]
  exact hv

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Lineartyping
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.X86.Stacklayout

theorem frame_get_local : frame_get_localStatement := by
  intro return_address_offset tprog cfg f hlocal houtgoing hstack hnorepet hcallee
    ofs ty j sp ls ls0 parent retaddr m P hframe hbound hvalid
  have hchecks : zLe z0 ofs ∧ zDivide (typealign ty) ofs := by
    revert hvalid
    unfold slot_valid
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
    generalize hle : CompCert4Lean.Lib.Coqlib.zle ZArith.BinInt.Z.Z0 ofs = d
    cases d with
    | right h => simp
    | left hnonneg =>
      generalize heq : CompCert4Lean.Lib.Coqlib.zeq
        (ZArith.BinInt.Z.modulo ofs (typealign ty)) ZArith.BinInt.Z.Z0 = d
      cases d with
      | right h => simp
      | left hmod =>
        intro _
        refine ⟨hnonneg, ZArith.Znumtheory.Zmod_divide ofs (typealign ty) ?_ hmod⟩
        cases ty <;> decide
  exact get_location return_address_offset tprog m j sp
    (make_env cfg (function_bounds cfg f)).fe_ofs_local
    (function_bounds cfg f).bound_local Local ls ofs ty
    hframe.1.1.1 hchecks.1 hbound hchecks.2

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Lineartyping
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.X86.Stacklayout

theorem frame_get_outgoing : frame_get_outgoingStatement := by
  intro return_address_offset tprog cfg f hlocal houtgoing hstack hnorepet hcallee
    ofs ty j sp ls ls0 parent retaddr m P hframe hbound hvalid
  have hchecks : zLe z0 ofs ∧ zDivide (typealign ty) ofs := by
    revert hvalid
    unfold slot_valid
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
    generalize hle : CompCert4Lean.Lib.Coqlib.zle ZArith.BinInt.Z.Z0 ofs = d
    cases d with
    | right h => simp
    | left hnonneg =>
      generalize heq : CompCert4Lean.Lib.Coqlib.zeq
        (ZArith.BinInt.Z.modulo ofs (typealign ty)) ZArith.BinInt.Z.Z0 = d
      cases d with
      | right h => simp
      | left hmod =>
        intro _
        refine ⟨hnonneg, ZArith.Znumtheory.Zmod_divide ofs (typealign ty) ?_ hmod⟩
        cases ty <;> decide
  exact get_location return_address_offset tprog m j sp
    (fe_ofs_arg cfg)
    (function_bounds cfg f).bound_outgoing Outgoing ls ofs ty
    hframe.1.1.2.1.1 hchecks.1 hbound hchecks.2

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem frame_get_parent : frame_get_parentStatement := by
  intro return_address_offset tprog cfg f hlocal houtgoing hstack hnorepet hcallee
    j sp ls ls0 parent retaddr m P hframe
  exact hasvalue_get_stack _ _ _ _ _ hframe.1.1.2.1.2.1.1

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Separation
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Stacklayout
open CompCert4Lean.Backend.Stacking

private theorem stackingproof_pmap_get_set_same {A : Type} (i : positive) (x : A)
    (m : PMap.t A) : PMap.get i (PMap.set i x m) = x := by
  change (match PTree.get i (PTree.set i x m.2) with
    | some y => y
    | none => m.1) = x
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i i with
  | left _ => simp
  | right hne => exact False.elim (hne rfl)

private theorem stackingproof_pmap_get_set_other {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) (h : i ≠ j) : PMap.get i (PMap.set j x m) = PMap.get i m := by
  change (match PTree.get i (PTree.set j x m.2) with
    | some y => y
    | none => m.1) = PMap.get i m
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i j with
  | left heq => exact False.elim (h heq)
  | right _ => rfl

private theorem stackingproof_store_unchanged_on (P : massert)
    (chunk : memory_chunk) (m : mem) (b : block) (ofs : Z)
    (v : val) (m' : mem)
    (hstore : Mem.store chunk m b ofs v = some m')
    (hout : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) →
      ¬ P.m_footprint b i) :
    Mem.unchanged_on P.m_footprint m m' := by
  have hnext := Mem.nextblock_store chunk m b ofs v m' hstore
  have hcontents := Mem.store_mem_contents chunk m b ofs v m' hstore
  refine ⟨?_, ?_, ?_⟩
  · change CompCert4Lean.Lib.Coqlib.Ple m.nextblock m'.nextblock
    rw [hnext]
    exact CompCert4Lean.Lib.Coqlib.Ple_refl _
  · intro b' ofs' k p hP hvalid
    constructor
    · intro hp
      exact Mem.perm_store_1 chunk m b ofs v m' hstore b' ofs' k p hp
    · intro hp
      exact Mem.perm_store_2 chunk m b ofs v m' hstore b' ofs' k p hp
  · intro b' ofs' hP hp
    rw [hcontents]
    by_cases hb : b' = b
    · subst b'
      have hpmap := stackingproof_pmap_get_set_same b
        (Mem.setN (encode_val chunk v) ofs (PMap.get b m.mem_contents)) m.mem_contents
      rw [hpmap]
      apply Mem.setN_other
      intro i hi heq
      subst i
      have hlen := CompCert4Lean.Common.Memdata.encode_val_length chunk v
      have hi' := hi
      rw [hlen] at hi'
      have hsize' : zOfNat (size_chunk_nat chunk) = size_chunk chunk := by
        cases chunk <;> rfl
      have hrange : zLe ofs ofs' ∧ zLt ofs' (zAdd ofs (size_chunk chunk)) := by
        simpa [hsize'] using hi'
      exact (hout ofs' hrange) hP
    · rw [show PMap.get b' (PMap.set b
          (Mem.setN (encode_val chunk v) ofs (PMap.get b m.mem_contents))
          m.mem_contents) = PMap.get b' m.mem_contents by
            exact stackingproof_pmap_get_set_other b' b _ _ hb]

private theorem stackingproof_set_location
    (return_address_offset : Mach.function → Mach.code → ptrofs → Prop)
    (tprog : Mach.program) (m : mem) (j : meminj) (sp : block)
    (pos bound : Z) (sl : slot) (ls : locset) (P : massert)
    (ofs : Z) (ty : typ) (v v' : val)
    (hm : (sepconj (contains_locations return_address_offset tprog j sp pos bound sl ls) P).m_pred m)
    (hofs : zLe z0 ofs)
    (hbound : zLe (zAdd ofs (Locations.typesize ty)) bound)
    (halign : zDivide (Locations.typealign ty) ofs)
    (hinj : Val.inject j v v') :
    ∃ m',
      Mem.store (chunk_of_type ty) m sp (zAdd pos (zMul z4 ofs)) v' = some m' ∧
      Mach.store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (zAdd pos (zMul z4 ofs))) v' = some m' ∧
      (sepconj (contains_locations return_address_offset tprog j sp pos bound sl
        (Locmap.set (S sl ofs ty) v ls)) P).m_pred m' := by
  rcases hm with ⟨hc, hP, hdisj⟩
  rcases hc with ⟨hdiv, hpos, hmax, hperm, hload⟩
  have hvalid : Mem.valid_access m (chunk_of_type ty) sp
      (zAdd pos (zMul z4 ofs)) Writable := by
    refine ⟨?_, locationAligned pos ofs ty hdiv halign⟩
    intro i hi
    exact Mem.perm_implies m sp i Cur Freeable Writable
      (hperm i (locationChunkRange pos bound ofs i ty hofs hbound hi))
      (perm_F_any Writable)
  rcases Mem.valid_access_store m (chunk_of_type ty) sp
      (zAdd pos (zMul z4 ofs)) v' hvalid with ⟨m', hstore⟩
  have hstore_stack : Mach.store_stack m (Vptr sp Ptrofs.zero) ty
      (Ptrofs.repr (zAdd pos (zMul z4 ofs))) v' = some m' := by
    unfold Mach.store_stack Mem.storev
    simp only [Val.offset_ptr]
    have hadd : Ptrofs.add Ptrofs.zero
        (Ptrofs.repr (zAdd pos (zMul z4 ofs))) =
        Ptrofs.repr (zAdd pos (zMul z4 ofs)) := by
      change WordCore.add (WordCore.zero Ptrofs.wordsize)
        (WordCore.repr Ptrofs.wordsize (zAdd pos (zMul z4 ofs))) = _
      apply WordCore.ext_of_val_eq
      rw [stackingproof_wordcore_add_val]
      have hzero : (WordCore.zero Ptrofs.wordsize).val = 0 := by rfl
      rw [hzero, Nat.zero_add]
      exact Nat.mod_eq_of_lt (stackingproof_wordcore_val_lt _)
    rw [hadd]
    change Mem.store (chunk_of_type ty) m sp
      (Ptrofs.unsigned (Ptrofs.repr (zAdd pos (zMul z4 ofs)))) v' = some m'
    have haddr0 : zLe z0 (zAdd pos (zMul z4 ofs)) :=
      locationAddrNonneg pos ofs hpos hofs
    have haddrmax : zLe (zAdd pos (zMul z4 ofs)) Ptrofs.max_unsigned :=
      locationAddrMax pos bound ofs ty hmax hbound
    rw [stackingproof_ptrofs_unsigned_repr _ ⟨haddr0, haddrmax⟩]
    exact hstore
  refine ⟨m', hstore, hstore_stack, ?_⟩
  let ls' := Locmap.set (S sl ofs ty) v ls
  have hc' : (contains_locations return_address_offset tprog j sp pos bound sl ls').m_pred m' := by
    refine ⟨hdiv, hpos, hmax, ?_, ?_⟩
    · intro i hi
      exact Mem.perm_store_1 (chunk_of_type ty) m sp
        (zAdd pos (zMul z4 ofs)) v' m' hstore sp i Cur Freeable (hperm i hi)
    · intro ofs0 ty0 hofs0 hbound0 halign0
      have haddr0 : zLe z0 (zAdd pos (zMul z4 ofs0)) :=
        locationAddrNonneg pos ofs0 hpos hofs0
      have haddrmax : zLe (zAdd pos (zMul z4 ofs0)) Ptrofs.max_unsigned :=
        locationAddrMax pos bound ofs0 ty0 hmax hbound0
      have hvalid0 : Mem.valid_access m' (chunk_of_type ty0) sp
          (zAdd pos (zMul z4 ofs0)) Readable := by
        apply Mem.store_valid_access_1 (chunk_of_type ty) m sp
          (zAdd pos (zMul z4 ofs)) v' m' hstore
          (chunk_of_type ty0) sp (zAdd pos (zMul z4 ofs0)) Readable
        refine ⟨?_, locationAligned pos ofs0 ty0 hdiv halign0⟩
        intro i hi
        exact Mem.perm_implies m sp i Cur Freeable Readable
          (hperm i (locationChunkRange pos bound ofs0 i ty0 hofs0 hbound0 hi))
          (perm_F_any Readable)
      have hload0 := hload ofs0 ty0 hofs0 hbound0 halign0
      rcases hload0 with ⟨v0, hv0, hinj0⟩
      by_cases heq : S sl ofs ty = S sl ofs0 ty0
      · injection heq with hofsEq htyEq
        subst ofs0
        subst ty0
        refine ⟨Val.load_result (chunk_of_type ty) v', ?_, ?_⟩
        · exact Mem.load_store_same (chunk_of_type ty) m sp
            (zAdd pos (zMul z4 ofs)) v' m' hstore
        · rw [show ls' (S sl ofs ty) =
              Val.load_result (chunk_of_type ty) v by
                exact Locmap.gss (S sl ofs ty) v ls]
          exact CompCert4Lean.Common.Values.Val.load_result_inject j
            (chunk_of_type ty) v v' hinj
      · cases hd : Loc.diff_dec (S sl ofs ty) (S sl ofs0 ty0) with
          | left hdiff =>
              refine ⟨v0, ?_, ?_⟩
              · rw [Mem.load_store_other (chunk_of_type ty) m sp
                  (zAdd pos (zMul z4 ofs)) v' m'
                  hstore (chunk_of_type ty0) sp
                  (zAdd pos (zMul z4 ofs0)) (by
                right
                rcases hdiff with hslot | hleft | hright
                · exact False.elim (hslot rfl)
                · right
                  change intOfZ (zAdd ofs (Locations.typesize ty)) ≤ intOfZ ofs0 at hleft
                  change intOfZ (zAdd (zAdd pos (zMul z4 ofs))
                    (size_chunk (chunk_of_type ty))) ≤ intOfZ (zAdd pos (zMul z4 ofs0))
                  simp only [zAdd, zMul, ZArith.BinInt.Z.add,
                    ZArith.BinInt.Z.mul, intOfZ_zOfInt, locationChunkSize] at hleft ⊢
                  have hz4 : intOfZ z4 = 4 := rfl
                  rw [hz4]
                  omega
                · left
                  change intOfZ (zAdd ofs0 (Locations.typesize ty0)) ≤ intOfZ ofs at hright
                  change intOfZ (zAdd (zAdd pos (zMul z4 ofs0))
                    (size_chunk (chunk_of_type ty0))) ≤ intOfZ (zAdd pos (zMul z4 ofs))
                  simp only [zAdd, zMul, ZArith.BinInt.Z.add,
                    ZArith.BinInt.Z.mul, intOfZ_zOfInt, locationChunkSize] at hright ⊢
                  have hz4 : intOfZ z4 = 4 := rfl
                  rw [hz4]
                  omega)]
                exact hv0
              · rw [show ls' (S sl ofs0 ty0) = ls (S sl ofs0 ty0) by
                    exact Locmap.gso (S sl ofs ty) v ls (S sl ofs0 ty0) hdiff]
                exact hinj0
          | right hndiff =>
              rcases Mem.valid_access_load m' (chunk_of_type ty0) sp
                  (zAdd pos (zMul z4 ofs0)) hvalid0 with ⟨v1, hv1⟩
              refine ⟨v1, hv1, ?_⟩
              unfold ls' Locmap.set
              cases Loc.eq (S sl ofs ty) (S sl ofs0 ty0) with
              | left heq' => exact (heq heq').elim
              | right _ =>
                  cases Loc.diff_dec (S sl ofs ty) (S sl ofs0 ty0) with
                  | left hd' => exact (hndiff hd').elim
                  | right _ => exact Val.val_inject_undef j _
  have hunch : Mem.unchanged_on P.m_footprint m m' :=
    stackingproof_store_unchanged_on P (chunk_of_type ty) m sp
      (zAdd pos (zMul z4 ofs)) v' m' hstore (by
        intro i hi hPi
        apply hdisj sp i
        · exact ⟨rfl,
            (locationChunkRange pos bound ofs i ty hofs hbound hi).1,
            (locationChunkRange pos bound ofs i ty hofs hbound hi).2⟩
        · exact hPi)
  refine ⟨hc', P.m_invar m m' hP hunch, ?_⟩
  intro b ofs0 hfoot hPfoot
  apply hdisj b ofs0 hfoot
  exact hPfoot

theorem frame_set_outgoing : frame_set_outgoingStatement := by
  intro return_address_offset tprog cfg f bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
    ofs ty v v' j sp ls ls0 parent retaddr m P hm hwithin hvalid hinj
  unfold frame_contents at hm
  have hframe := mconj_proj1 _ _ _ m hm
  have hout := sep_pick2 _ _ _ m hframe.1
  have houtP : (sepconj
      (contains_locations return_address_offset tprog j sp
        (CompCert4Lean.X86.Stacklayout.fe_ofs_arg cfg)
        (CompCert4Lean.Backend.Bounds.function_bounds cfg f).bound_outgoing
        Outgoing ls) P).m_pred m := by
    refine ⟨hout, hframe.2.1, ?_⟩
    intro b ofs0 ho hp
    exact hframe.2.2 b ofs0 (Or.inr (Or.inl ho)) hp
  have hchecks : zLe z0 ofs ∧ zDivide (typealign ty) ofs := by
    revert hvalid
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
    generalize hle : CompCert4Lean.Lib.Coqlib.zle
      ZArith.BinInt.Z.Z0 ofs = d
    cases d with
    | right h => simp
    | left hnonneg =>
      generalize heq : CompCert4Lean.Lib.Coqlib.zeq
        (ZArith.BinInt.Z.modulo ofs (typealign ty)) ZArith.BinInt.Z.Z0 = d
      cases d with
      | right h => simp
      | left hmod =>
        intro _
        refine ⟨hnonneg, ZArith.Znumtheory.Zmod_divide ofs (typealign ty) ?_ hmod⟩
        cases ty <;> decide
  have hset := stackingproof_set_location return_address_offset tprog m j sp
    (CompCert4Lean.X86.Stacklayout.fe_ofs_arg cfg)
    (CompCert4Lean.Backend.Bounds.function_bounds cfg f).bound_outgoing
    Outgoing ls P ofs ty v v' houtP hchecks.1 hwithin hchecks.2 hinj
  rcases hset with ⟨m', hstore_mem, hstore, hnew⟩
  refine ⟨m', ?_, ?_⟩
  · simpa [CompCert4Lean.Backend.Stacking.offset_arg] using hstore
  · have hrangesP := mconj_proj2 _ _ _ m hm
    have hranges := hrangesP.1
    have hrange1 := range_preserved m m' sp .Z0
        (CompCert4Lean.X86.Stacklayout.make_env cfg
          (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_stack_data hranges.1
        (by
          intro i k p hi hp
          exact Mem.perm_store_1 (chunk_of_type ty) m sp
            (zAdd (CompCert4Lean.X86.Stacklayout.fe_ofs_arg cfg) (zMul z4 ofs))
            v' m' hstore_mem sp i k p hp)
    have hrange2 := range_preserved m m' sp
        (ZArith.BinInt.Z.add
          (CompCert4Lean.X86.Stacklayout.make_env cfg
            (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_stack_data
          (CompCert4Lean.Backend.Bounds.function_bounds cfg f).bound_stack_data)
        (CompCert4Lean.X86.Stacklayout.make_env cfg
          (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_size hranges.2.1
        (by
          intro i k p hi hp
          exact Mem.perm_store_1 (chunk_of_type ty) m sp
            (zAdd (CompCert4Lean.X86.Stacklayout.fe_ofs_arg cfg) (zMul z4 ofs))
            v' m' hstore_mem sp i k p hp)
    have hranges' : (sepconj
        (range sp .Z0
          (CompCert4Lean.X86.Stacklayout.make_env cfg
            (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_stack_data)
        (range sp (ZArith.BinInt.Z.add
          (CompCert4Lean.X86.Stacklayout.make_env cfg
            (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_stack_data
          (CompCert4Lean.Backend.Bounds.function_bounds cfg f).bound_stack_data)
          (CompCert4Lean.X86.Stacklayout.make_env cfg
            (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_size)).m_pred m' := by
      exact ⟨hrange1, hrange2, hranges.2.2⟩
    let localarea := contains_locations return_address_offset tprog j sp
      (make_env cfg (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_ofs_local
      (CompCert4Lean.Backend.Bounds.function_bounds cfg f).bound_local Local ls
    let rest := sepconj
      (hasvalue Mptr sp (make_env cfg (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_ofs_link parent)
      (sepconj
        (hasvalue Mptr sp (make_env cfg (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_ofs_retaddr retaddr)
        (contains_callee_saves j sp
          (make_env cfg (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_ofs_callee_save
          (CompCert4Lean.Backend.Bounds.function_bounds cfg f).used_callee_save ls0))
    have hfoot : ∀ i,
        zLe (zAdd (fe_ofs_arg cfg) (zMul z4 ofs)) i ∧
        zLt i (zAdd (zAdd (fe_ofs_arg cfg) (zMul z4 ofs)) (size_chunk (chunk_of_type ty))) →
        (contains_locations return_address_offset tprog j sp (fe_ofs_arg cfg)
          (CompCert4Lean.Backend.Bounds.function_bounds cfg f).bound_outgoing Outgoing ls).m_footprint sp i := by
      intro i hi
      exact ⟨rfl, locationChunkRange _ _ _ _ _ hchecks.1 hwithin hi⟩
    have hlocal_mem : localarea.m_pred m' :=
      localarea.m_invar m m' hframe.1.1
        (stackingproof_store_unchanged_on localarea _ _ _ _ _ _ hstore_mem (by
          intro i hi hl
          exact hframe.1.2.2 sp i hl (Or.inl (hfoot i hi))))
    have hrest_mem : rest.m_pred m' :=
      rest.m_invar m m' hframe.1.2.1.2.1
        (stackingproof_store_unchanged_on rest _ _ _ _ _ _ hstore_mem (by
          intro i hi hr
          exact hframe.1.2.1.2.2 sp i (hfoot i hi) hr))
    have hlocal_new := (contains_locations_exten return_address_offset tprog ls
      (Locmap.set (S Outgoing ofs ty) v ls) j sp
      (make_env cfg (CompCert4Lean.Backend.Bounds.function_bounds cfg f)).fe_ofs_local
      (CompCert4Lean.Backend.Bounds.function_bounds cfg f).bound_local Local (by
        intro ofs0 ty0
        rw [Locmap.gso (S Outgoing ofs ty) v ls (S Local ofs0 ty0)
          (Or.inl (by intro h; cases h))]
        exact Val.lessdef_refl _)).1 m' hlocal_mem
    have hframe1' : (frame_contents_1 return_address_offset tprog cfg f
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop j sp
        (Locmap.set (S Outgoing ofs ty) v ls) ls0 parent retaddr).m_pred m' :=
      ⟨hlocal_new, ⟨hnew.1, hrest_mem, hframe.1.2.1.2.2⟩, hframe.1.2.2⟩
    exact frame_mconj _ _ _ _ _ _ hm
      ⟨hframe1', hnew.2.1, hframe.2.2⟩ hranges'

end CompCert4Lean.Backend.Stackingproof


namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

theorem frame_set_res : frame_set_resStatement := by
  intro return_address_offset tprog cfg f bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
    j sp ls0 parent retaddr m P res v ls hm
  induction res generalizing v ls with
  | BR r =>
      exact frame_set_reg return_address_offset tprog cfg f
        bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop r v j sp ls ls0
        parent retaddr m P hm
  | BR_none =>
      simpa [Locmap.setres] using hm
  | BR_splitlong hi lo ih_hi ih_lo =>
      have hhi := ih_hi (Val.hiword v) ls hm
      have hlo := ih_lo (Val.loword v)
        (Locmap.setres hi (Val.hiword v) ls) hhi
      simpa [Locmap.setres] using hlo

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem frame_contents_incr : frame_contents_incrStatement := by
  intro return_address_offset tprog cfg f bound_local_pos bound_outgoing_pos
    bound_stack_data_pos used_callee_save_norepet used_callee_save_prop
    j sp ls ls0 parent retaddr m P j' hm hincr
  exact (stackingproof_massert_imp_sepconj
    (stackingproof_frame_contents_incr return_address_offset tprog cfg f
      bound_local_pos bound_outgoing_pos bound_stack_data_pos
      used_callee_save_norepet used_callee_save_prop j j' sp ls ls0 parent
      retaddr hincr)
    (stackingproof_massert_imp_refl P)).1 m hm

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

theorem agree_regs_set_reg : agree_regs_set_regStatement := by
  intro j ls rs r v v' hagree hv
  exact stackingproof_agree_regs_set_reg j ls rs r v v' hagree hv

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

theorem agree_regs_set_pair : agree_regs_set_pairStatement := by
  intro j p v v' ls rs hagree hv
  cases p with
  | One r =>
      simpa [Locmap.setpair, Mach.set_pair] using
        (stackingproof_agree_regs_set_reg j ls rs r v v' hagree hv)
  | Twolong rhi rlo =>
      have hhi := stackingproof_agree_regs_set_reg j ls rs rhi
        (Val.hiword v) (Val.hiword v') hagree
        (stackingproof_hiword_inject j v v' hv)
      have hlo := stackingproof_agree_regs_set_reg j
        (Locmap.set (R rhi) (Val.hiword v) ls)
        (Regmap.set rhi (Val.hiword v') rs)
        rlo (Val.loword v) (Val.loword v') hhi
        (stackingproof_loword_inject j v v' hv)
      simpa [Locmap.setpair, Mach.set_pair] using hlo

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Separation
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Machregs

private theorem stackingproof_contains_set_stack
    (spec : val → Prop) (v : val) (spec1 : val → Prop)
    (m : mem) (ty : typ) (sp : block) (ofs : Z) (P : massert)
    (hm : (sepconj (contains (chunk_of_type ty) sp ofs spec1) P).m_pred m)
    (hspec : spec (Val.load_result (chunk_of_type ty) v)) :
    ∃ m', Mach.store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) v = some m' ∧
      (sepconj (contains (chunk_of_type ty) sp ofs spec) P).m_pred m' := by
  rcases hm with ⟨hc, hP, hdisj⟩
  rcases hc with ⟨hbounds, hvalid, vold, hload, hspec1⟩
  have hvalidW : Mem.valid_access m (chunk_of_type ty) sp ofs Writable :=
    Mem.valid_access_implies m (chunk_of_type ty) sp ofs Freeable Writable hvalid
      (perm_F_any Writable)
  rcases Mem.valid_access_store m (chunk_of_type ty) sp ofs v hvalidW with ⟨m', hstore⟩
  have hstore_stack : Mach.store_stack m (Vptr sp Ptrofs.zero) ty
      (Ptrofs.repr ofs) v = some m' := by
    unfold Mach.store_stack Mem.storev
    simp only [Val.offset_ptr]
    have hadd : Ptrofs.add Ptrofs.zero (Ptrofs.repr ofs) = Ptrofs.repr ofs := by
      change WordCore.add (WordCore.zero Ptrofs.wordsize)
        (WordCore.repr Ptrofs.wordsize ofs) = _
      apply WordCore.ext_of_val_eq
      rw [stackingproof_wordcore_add_val]
      have hzero : (WordCore.zero Ptrofs.wordsize).val = 0 := by rfl
      rw [hzero, Nat.zero_add]
      exact Nat.mod_eq_of_lt (stackingproof_wordcore_val_lt _)
    rw [hadd]
    change Mem.store (chunk_of_type ty) m sp
      (Ptrofs.unsigned (Ptrofs.repr ofs)) v = some m'
    have hrepr : Ptrofs.unsigned (Ptrofs.repr ofs) = ofs := by
      apply stackingproof_ptrofs_unsigned_repr
      exact hbounds
    rw [hrepr]
    exact hstore
  refine ⟨m', hstore_stack, ?_⟩
  have hc' : (contains (chunk_of_type ty) sp ofs spec).m_pred m' := by
    refine ⟨hbounds, Mem.store_valid_access_1 (chunk_of_type ty) m sp ofs v m'
      hstore (chunk_of_type ty) sp ofs Freeable hvalid, ?_⟩
    exact ⟨Val.load_result (chunk_of_type ty) v,
      Mem.load_store_same (chunk_of_type ty) m sp ofs v m' hstore, hspec⟩
  have hunch : Mem.unchanged_on P.m_footprint m m' :=
    stackingproof_store_unchanged_on P (chunk_of_type ty) m sp ofs v m' hstore (by
      intro i hi hPi
      exact hdisj sp i (by
        exact ⟨rfl, hi.1, hi.2⟩) hPi)
  refine ⟨hc', P.m_invar m m' hP hunch, ?_⟩
  intro b ofs' hfoot hPfoot
  exact hdisj b ofs' hfoot hPfoot

theorem save_callee_save_rec_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    save_callee_save_rec_correctStatement := by
  intro cfg xi return_address_offset
    tprog j cs fb sp ls hls_temp_undef wt_ls k l pos rs m P hcallee hsep hagree
  induction l generalizing pos rs m P with
  | nil =>
      refine ⟨rs, m, ?_, ?_, ?_, hagree⟩
      · exact star_refl _ _ (Mach.State cs fb (Vptr sp Ptrofs.zero) k rs m)
      · have hP : P.m_pred m := hsep.2.1
        refine ⟨True.intro, hP, ?_⟩
        intro b ofs hfoot hPfoot
        exact False.elim hfoot
      · intro ofs k' p hp
        exact hp
  | cons r l ih =>
      let ty := mreg_type r
      let sz := CompCert4Lean.Common.AST.typesize ty
      let pos1 := align pos sz
      have hty := CompCert4Lean.Common.AST.typesize_pos ty
      have hadd : ZArith.BinInt.Z.le pos1 (zAdd pos1 sz) := by
        unfold ZArith.BinInt.Z.le at *
        unfold zAdd ZArith.BinInt.Z.add
        rw [intOfZ_zOfInt]
        have hty' : 0 ≤ intOfZ sz := by
          exact Int.le_of_lt (show 0 < intOfZ sz from hty)
        omega
      have hstep0 := size_callee_save_area_rec_incr l (zAdd pos1 sz)
      have hstep : ZArith.BinInt.Z.le pos1 (size_callee_save_area_rec l (zAdd pos1 sz)) :=
        ZArith.BinInt.Z.le_trans pos1 (zAdd pos1 sz)
          (size_callee_save_area_rec l (zAdd pos1 sz)) hadd hstep0
      have hpos : zLe pos pos1 := by
        exact align_le pos sz hty
      have hsep1 := range_drop_left sp pos
        (size_callee_save_area_rec (r :: l) pos) P pos1 m
        ⟨hpos, by
          simp [size_callee_save_area_rec, pos1, ty, sz]
          exact hstep⟩ hsep
      have hsep2 := range_split sp pos1
        (size_callee_save_area_rec l (zAdd pos1 sz)) P
        (zAdd pos1 sz) m
        ⟨hadd, hstep0⟩ hsep1
      have hszdiv : zDivide (align_chunk (chunk_of_type ty)) sz := by
        change ZArith.BinInt.Z.divide (align_chunk (chunk_of_type ty))
          (CompCert4Lean.Common.AST.typesize ty)
        rw [← size_type_chunk ty]
        exact align_size_chunk_divides (chunk_of_type ty)
      have halign : zDivide (align_chunk (chunk_of_type ty)) pos1 := by
        apply ZArith.BinInt.Z.divide_trans (align_chunk (chunk_of_type ty)) sz pos1
        · exact hszdiv
        · simpa [pos1] using (align_divides pos sz hty)
      have hsep2' : (sepconj (range sp pos1
          (zAdd pos1 (size_chunk (chunk_of_type ty))))
          (sepconj (range sp (zAdd pos1 sz)
            (size_callee_save_area_rec l (zAdd pos1 sz))) P)).m_pred m := by
        simpa [size_type_chunk ty] using hsep2
      have hcontains0 := range_contains (chunk_of_type ty) sp pos1
        (sepconj (range sp (zAdd pos1 sz)
          (size_callee_save_area_rec l (zAdd pos1 sz))) P) m hsep2' halign
      have hspec : Val.inject j (ls (R r)) (Val.load_result (chunk_of_type ty) (rs r)) :=
        load_result_inject j (mreg_type r) (ls (R r)) (rs r) (hagree r) (wt_ls r)
      have hset := stackingproof_contains_set_stack
        (fun v => Val.inject j (ls (R r)) v) (rs r)
        (fun _ => True) m ty sp pos1
        (sepconj (range sp (zAdd pos1 sz)
          (size_callee_save_area_rec l (zAdd pos1 sz))) P)
        hcontains0 hspec
      rcases hset with ⟨m1, hstore, hnew⟩
      let rs1 := undef_regs (destroyed_by_setstack ty) rs
      have hagree1 : agree_regs j ls rs1 := by
        intro r0
        by_cases hr0 : r0 ∈ destroyed_by_setstack ty
        · change Val.inject j (ls (R r0))
            (Mach.undef_regs (destroyed_by_setstack ty) rs r0)
          rw [Mach.undef_regs_same_proof r0 (destroyed_by_setstack ty) rs hr0]
          rw [hls_temp_undef ty r0 hr0]
          exact Val.val_inject_undef j _
        · have hother := Mach.undef_regs_other_proof r0
            (destroyed_by_setstack ty) rs hr0
          rw [show rs1 r0 = rs r0 by exact hother]
          exact hagree r0
      have hswap := (sep_swap
        (contains (chunk_of_type ty) sp pos1
          (fun v => Val.inject j (ls (R r)) v))
        (range sp (zAdd pos1 sz) (size_callee_save_area_rec l (zAdd pos1 sz))) P).1.1 m1 hnew
      have hih := ih (P := sepconj
          (contains (chunk_of_type ty) sp pos1
            (fun v => Val.inject j (ls (R r)) v)) P)
        (pos := zAdd pos1 sz) (rs := rs1) (m := m1)
        (by intro r0 hr0; exact hcallee r0 (by simp [hr0])) hswap hagree1
      rcases hih with ⟨rs2, m2, hstar, hpred, hperm, hagree2⟩
      have hposmax : zLe pos1 Ptrofs.max_unsigned := by
        have hh := hsep2.1.2.1
        change intOfZ (zAdd pos1 sz) ≤ intOfZ Ptrofs.modulus at hh
        unfold zAdd ZArith.BinInt.Z.add at hh
        rw [intOfZ_zOfInt] at hh
        change intOfZ pos1 ≤ intOfZ Ptrofs.max_unsigned
        have hm : intOfZ Ptrofs.max_unsigned = intOfZ Ptrofs.modulus - 1 := by rfl
        rw [hm]
        have hszi : 0 < intOfZ sz := hty
        omega
      refine ⟨rs2, m2, ?_, ?_, ?_, hagree2⟩
      · exact star_left _ _ _ _ _ _ _ _ _ _
          (Mach.exec_Msetstack cs fb (Vptr sp Ptrofs.zero) r
            (Ptrofs.repr pos1) ty
            (save_callee_save_rec l (zAdd pos1 sz) k) rs m m1 rs1
            hstore rfl) hstar rfl
      · have hfinal := (sep_swap
          (contains_callee_saves j sp (zAdd pos1 sz) l ls)
          (contains (chunk_of_type ty) sp pos1
            (fun v => Val.inject j (ls (R r)) v)) P).1.1 m2 hpred
        have hfinal2 := (sep_assoc_2
          (contains (chunk_of_type ty) sp pos1
            (fun v => Val.inject j (ls (R r)) v))
          (contains_callee_saves j sp (zAdd pos1 sz) l ls) P).1 m2 hfinal
        simpa [contains_callee_saves, pos1, ty, sz] using hfinal2
      · intro ofs k' p hp
        exact hperm ofs k' p (Mem.perm_store_1 (chunk_of_type ty) m sp
          pos1 (rs r) m1 (by
            unfold Mach.store_stack Mem.storev at hstore
            simp only [Val.offset_ptr] at hstore
            have hadd' : Ptrofs.add Ptrofs.zero (Ptrofs.repr pos1) = Ptrofs.repr pos1 := by
              change WordCore.add (WordCore.zero Ptrofs.wordsize)
                (WordCore.repr Ptrofs.wordsize pos1) = _
              apply WordCore.ext_of_val_eq
              rw [stackingproof_wordcore_add_val]
              have hzero : (WordCore.zero Ptrofs.wordsize).val = 0 := by rfl
              rw [hzero, Nat.zero_add]
              exact Nat.mod_eq_of_lt (stackingproof_wordcore_val_lt _)
            rw [hadd'] at hstore
            change Mem.store (chunk_of_type ty) m sp
              (Ptrofs.unsigned (Ptrofs.repr pos1)) (rs r) = some m1 at hstore
            rw [stackingproof_ptrofs_unsigned_repr pos1 ⟨hsep2.1.1, hposmax⟩] at hstore
            exact hstore) sp ofs k' p hp)

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Separation
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Conventions1
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Stacklayout

theorem save_callee_save_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    save_callee_save_correctStatement := by
  intro cfg xi return_address_offset tprog f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop
    j ls ls0 rs sp cs fb k m P hsep wt_ls hcallee hagree
  let ls1 := LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls)
  let rs1 := Mach.undef_regs destroyed_at_function_entry rs
  have htemp : ∀ ty r, r ∈ destroyed_by_setstack ty → ls1 (R r) = Vundef := by
    intro ty r hr
    exact LTL_undef_regs_same return_address_offset tprog r
      destroyed_at_function_entry (LTL.call_regs ls)
      (destroyed_by_setstack_function_entry return_address_offset tprog ty r hr)
  have htype : ∀ r, Val.has_type (ls1 (R r)) (mreg_type r) := by
    intro r
    apply undef_regs_type (mreg_type r) (R r)
      destroyed_at_function_entry (LTL.call_regs ls)
    change Val.has_type (LTL.call_regs ls (R r)) (mreg_type r)
    simpa [LTL.call_regs] using wt_ls r
  have hused : ∀ r, r ∈ (function_bounds cfg f).used_callee_save →
      is_callee_save cfg r = true := by
    intro r hr
    exact used_callee_save_prop r hr
  have hrec := save_callee_save_rec_correct
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    cfg xi return_address_offset tprog j cs fb sp ls1
    htemp htype
    k (function_bounds cfg f).used_callee_save
    (make_env cfg (function_bounds cfg f)).fe_ofs_callee_save
    rs1 m P hused hsep (agree_regs_undef_regs j destroyed_at_function_entry
      (LTL.call_regs ls) rs
      (agree_regs_call_regs j ls rs hagree))
  rcases hrec with ⟨rs', m', hstar, hpred, hperm, hagree'⟩
  have hls_eq : ∀ r, r ∈ (function_bounds cfg f).used_callee_save →
      ls1 (R r) = ls0 (R r) := by
    intro r hr
    have hsave : is_callee_save cfg r = true := hused r hr
    have hcallee' : ls (R r) = ls0 (R r) :=
      hcallee (R r) (by simp [callee_save_loc, hsave])
    have hnot : r ∉ destroyed_at_function_entry := by
      intro hmem
      have hnone := (destroyed_at_function_entry_caller_save cfg)
      have hn : ¬ is_callee_save cfg r = true :=
        (List.any_eq_false.mp hnone) r hmem
      exact hn hsave
    have hls1 : ls1 (R r) = ls (R r) := by
      dsimp [ls1]
      rw [LTL_undef_regs_others return_address_offset tprog r
        destroyed_at_function_entry (LTL.call_regs ls) hnot]
      simp [LTL.call_regs]
    exact hls1.trans hcallee'
  have hpred' :
      (sepconj (contains_callee_saves j sp
        (make_env cfg (function_bounds cfg f)).fe_ofs_callee_save
        (function_bounds cfg f).used_callee_save ls0) P).m_pred m' := by
    have heq := contains_callee_saves_exten j sp ls1 ls0
      (function_bounds cfg f).used_callee_save
      (make_env cfg (function_bounds cfg f)).fe_ofs_callee_save
      (fun r hr => (hls_eq r hr).symm)
    refine ⟨heq.1.1 m' hpred.1, hpred.2.1, ?_⟩
    intro b ofs hfoot hPfoot
    exact hpred.2.2 b ofs (heq.1.2 b ofs hfoot) hPfoot
  refine ⟨rs', m', ?_, hpred', hperm, ?_⟩
  · simpa [save_callee_save, make_env, rs1] using hstar
  · simpa [ls1, rs1] using hagree'

end CompCert4Lean.Backend.Stackingproof

namespace CompCert4Lean.Backend.Stackingproof

open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Backend.Stacking
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Separation
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Conventions1
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Stacklayout

theorem restore_callee_save_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    restore_callee_save_correctStatement := by
  intro cfg xi return_address_offset tprog f
    bound_local_pos bound_outgoing_pos bound_stack_data_pos
    used_callee_save_norepet used_callee_save_prop
    m j sp ls ls0 pa ra P rs k cs fb hframe hagree
  have hrec : ∀ (l : List mreg) (ofs : Z) (rs : regset) (k : Mach.code),
      (contains_callee_saves j sp ofs l ls0).m_pred m →
      agree_unused cfg f bound_local_pos bound_outgoing_pos bound_stack_data_pos
        used_callee_save_norepet used_callee_save_prop j ls0 rs →
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
        agree_unused cfg f bound_local_pos bound_outgoing_pos bound_stack_data_pos
          used_callee_save_norepet used_callee_save_prop j ls0 rs' := by
    intro l
    induction l with
    | nil =>
        intro ofs rs k hcontains hagree hbounds
        refine ⟨rs, ?_, ?_, ?_, hagree⟩
        · simpa [restore_callee_save_rec] using
            (star_refl (Mach.step
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              cfg xi return_address_offset)
              (Genv.globalenv tprog)
              (Mach.State cs fb (Vptr sp Ptrofs.zero) k rs m))
        · simp
        · simp
    | cons r l ih =>
        intro ofs rs k hcontains hagree hbounds
        let ty := mreg_type r
        let sz := CompCert4Lean.Common.AST.typesize ty
        let ofs1 := align ofs sz
        rcases hcontains with ⟨hhead, htail, hdisj⟩
        obtain ⟨v, hload, hspec⟩ :=
          contains_get_stack (fun v' => Val.inject j (ls0 (R r)) v')
            m ty sp ofs1 hhead
        have hbounds_tail : ∀ r0, r0 ∈ l →
            mreg_within_bounds cfg (function_bounds cfg f) r0 := by
          intro r0 hr0
          exact hbounds r0 (by simp [hr0])
        have hagree1 :
            agree_unused cfg f bound_local_pos bound_outgoing_pos bound_stack_data_pos
              used_callee_save_norepet used_callee_save_prop j ls0
                (Regmap.set r v rs) := by
          intro r0 hr0
          by_cases heq : r0 = r
          · subst r0
            have hreg : Regmap.set r v rs r = v := by
              simpa [Regmap.get] using (Regmap.gss_proof val r v rs)
            rw [hreg]
            exact hspec
          · have hreg : Regmap.set r v rs r0 = rs r0 := by
              change Regmap.get r0 (Regmap.set r v rs) = Regmap.get r0 rs
              simpa using (Regmap.gso_proof val r0 r v rs heq)
            rw [hreg]
            exact hagree r0 hr0
        have hih := ih (ofs := zAdd ofs1 sz) (rs := Regmap.set r v rs) (k := k)
          htail hagree1 hbounds_tail
        rcases hih with ⟨rs', hstar, hin, hnot, hunused⟩
        refine ⟨rs', ?_, ?_, ?_, hunused⟩
        · exact star_left _ _ _ _ _ _ _ _ _ _
            (Mach.exec_Mgetstack cs fb (Vptr sp Ptrofs.zero)
              (Ptrofs.repr ofs1) ty r
              (restore_callee_save_rec l (zAdd ofs1 sz) k) rs m v hload)
            hstar rfl
        · intro r0 hr0
          by_cases hmem : r0 ∈ l
          · exact hin r0 hmem
          · have heq : r0 = r := by
              simp at hr0
              exact (hr0.resolve_right hmem)
            subst r0
            rw [hnot r (by exact hmem)]
            have hreg : Regmap.set r v rs r = v := by
              simpa [Regmap.get] using (Regmap.gss_proof val r v rs)
            rw [hreg]
            exact hspec
        · intro r0 hr0
          have hmem : r0 ∉ l := by
            intro hm
            exact hr0 (by simp [hm])
          rw [hnot r0 hmem]
          have hreg : Regmap.set r v rs r0 = rs r0 := by
            change Regmap.get r0 (Regmap.set r v rs) = Regmap.get r0 rs
            have hne : r0 ≠ r := by
              intro heq
              exact hr0 (by simp [heq])
            simpa using (Regmap.gso_proof val r0 r v rs hne)
          exact hreg
  unfold frame_contents at hframe
  unfold frame_contents_1 at hframe
  have hframe' := mconj_proj1 _ _ _ m hframe
  have hframe1 := hframe'.1
  have hcallee := hframe1.2.1.2.1.2.1.2.1
  have hbounds : ∀ r, r ∈ (function_bounds cfg f).used_callee_save →
      mreg_within_bounds cfg (function_bounds cfg f) r := by
    intro r hr _
    exact hr
  obtain ⟨rs', hstar, hsave, hnosave, _⟩ :=
    hrec (function_bounds cfg f).used_callee_save
      (make_env cfg (function_bounds cfg f)).fe_ofs_callee_save rs k
      hcallee hagree hbounds
  refine ⟨rs', ?_, ?_, ?_⟩
  · simpa [restore_callee_save, make_env] using hstar
  · intro r hr
    by_cases hmem : r ∈ (function_bounds cfg f).used_callee_save
    · exact hsave r hmem
    · rw [hnosave r hmem]
      apply hagree r
      intro hbound
      exact hmem (hbound hr)
  · intro r hr
    apply hnosave r
    intro hmem
    have hcallee := used_callee_save_prop r hmem
    simpa [hr] using hcallee

end CompCert4Lean.Backend.Stackingproof
