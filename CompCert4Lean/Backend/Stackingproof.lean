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
