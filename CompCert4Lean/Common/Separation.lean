import CompCert4Lean.Common.Events

/-!
# Assertions on memory states

Definition-bearing translation of CompCert's `common/Separation.v`. Proofs
assigned to later proof migration are represented by transparent proposition
descriptors.
-/

namespace CompCert4Lean.Common.Separation

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev z8 : Z := ZArith.BinInt.Z.of_nat 8
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zMax := ZArith.BinInt.Z.max
private abbrev zDivide := ZArith.BinInt.Z.divide

structure massert : Type where
  m_pred : mem → Prop
  m_footprint : block → Z → Prop
  m_invar : ∀ m m', m_pred m → Mem.unchanged_on m_footprint m m' → m_pred m'
  m_valid : ∀ m b ofs, m_pred m → m_footprint b ofs → Mem.valid_block m b

export massert (m_pred m_footprint m_invar m_valid)

def massert_imp (P Q : massert) : Prop :=
  (∀ m, P.m_pred m → Q.m_pred m) ∧
    ∀ b ofs, Q.m_footprint b ofs → P.m_footprint b ofs

def massert_eqv (P Q : massert) : Prop :=
  massert_imp P Q ∧ massert_imp Q P

private theorem validBlockOfPerm {m : mem} {b : block} {ofs : Z}
    {k : perm_kind} {p : permission} (h : Mem.perm m b ofs k p) :
    Mem.valid_block m b := by
  by_cases hb : Mem.valid_block m b
  · exact hb
  · have hn := m.nextblock_noaccess b ofs k hb
    have : False := by simpa [Mem.perm, Mem.perm_order', hn] using h
    exact this.elim

private theorem zSubAddCancel (x y : Z) : zSub (zAdd x y) y = x := by
  apply intOfZ_injective
  unfold zSub zAdd ZArith.BinInt.Z.sub ZArith.BinInt.Z.add
  repeat rw [intOfZ_zOfInt]
  omega

private theorem intOfZZ1 : intOfZ z1 = 1 := by
  rfl

private theorem permMaxNonemptyOfPerm {m : mem} {b : block} {ofs : Z}
    {k : perm_kind} {p : permission} (h : Mem.perm m b ofs k p) :
    Mem.perm m b ofs Max Nonempty := by
  cases k with
  | Max =>
      unfold Mem.perm Mem.perm_order' at h ⊢
      cases hx : (PMap.get b m.mem_access) ofs Max with
      | none => simp [hx] at h
      | some actual =>
          rw [hx] at h
          change Memtype.perm_order actual p at h
          change Memtype.perm_order actual Nonempty
          exact perm_any_N actual
  | Cur =>
      have hmax := m.access_max b ofs
      unfold Mem.perm Mem.perm_order' at h ⊢
      cases hx : (PMap.get b m.mem_access) ofs Max with
      | none =>
          cases hy : (PMap.get b m.mem_access) ofs Cur with
          | none => simp [hy] at h
          | some actual => simp [Mem.perm_order'', hx, hy] at hmax
      | some maxp =>
          change Memtype.perm_order maxp Nonempty
          exact perm_any_N maxp

private theorem accessFreeableOfPerm {m : mem} {b : block} {ofs : Z}
    {k : perm_kind} (h : Mem.perm m b ofs k Freeable) :
    (PMap.get b m.mem_access) ofs k = some Freeable := by
  unfold Mem.perm Mem.perm_order' at h
  cases hx : (PMap.get b m.mem_access) ofs k with
  | none => simp [hx] at h
  | some p =>
      rw [hx] at h
      cases h <;> rfl

private theorem permReadableOfFreeable {m : mem} {b : block} {ofs : Z}
    {k : perm_kind} (h : Mem.perm m b ofs k Freeable) :
    Mem.perm m b ofs k Readable := by
  unfold Mem.perm
  rw [accessFreeableOfPerm h]
  exact perm_F_any Readable

private def validAccessBool (m : mem) (chunk : memory_chunk) (b : block) (ofs : Z)
    (p : permission) : Bool :=
  match Mem.valid_access_dec m chunk b ofs p with
  | .left _ => true
  | .right _ => false

private theorem load_eq (chunk : memory_chunk) (m : mem) (b : block) (ofs : Z) :
    Mem.load chunk m b ofs =
      if validAccessBool m chunk b ofs Readable then
        some (decode_val chunk (Mem.getN (size_chunk_nat chunk) ofs
          (PMap.get b m.mem_contents)))
      else none := by
  rfl'

private theorem chunkSpanInt (chunk : memory_chunk) (ofs : Z) :
    intOfZ (zAdd ofs (size_chunk chunk)) =
      intOfZ ofs + Int.ofNat (size_chunk_nat chunk) := by
  unfold zAdd ZArith.BinInt.Z.add
  rw [intOfZ_zOfInt]
  congr 1
  cases chunk <;> rfl

private theorem getNCongr
    (m1 m2 : mem) (b : block) (root finish current : Z) (n : Nat)
    (hContents : ∀ i, zLe root i ∧ zLt i finish →
      ZMap.get i (PMap.get b m2.mem_contents) =
        ZMap.get i (PMap.get b m1.mem_contents))
    (hroot : zLe root current)
    (hfinish : intOfZ finish = intOfZ current + Int.ofNat n) :
    Mem.getN n current (PMap.get b m2.mem_contents) =
      Mem.getN n current (PMap.get b m1.mem_contents) := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih =>
      have hnpos : (0 : Int) < Int.ofNat (n + 1) :=
        Int.ofNat_lt.mpr (Nat.succ_pos n)
      have hlt : zLt current finish := by
        unfold zLt ZArith.BinInt.Z.lt
        omega
      have hContentsCurrent := hContents current ⟨hroot, hlt⟩
      simp only [Mem.getN]
      rw [hContentsCurrent]
      apply congrArg (List.cons (ZMap.get current (PMap.get b m1.mem_contents)))
      apply ih (zAdd current z1)
      · unfold zLe ZArith.BinInt.Z.le at hroot ⊢
        unfold zAdd ZArith.BinInt.Z.add
        simp only [intOfZ_zOfInt, intOfZZ1]
        have hone : (0 : Int) < Int.ofNat 1 := by decide
        omega
      · unfold zAdd ZArith.BinInt.Z.add
        simp only [intOfZ_zOfInt, intOfZZ1]
        have hsucc : Int.ofNat (n + 1) = Int.ofNat n + 1 := by
          change Int.ofNat (Nat.succ n) = Int.ofNat n + 1
          exact (Int.ofNat_add_one_out n).symm
        rw [hsucc] at hfinish
        change intOfZ finish = intOfZ current + (1 : Int) + Int.ofNat n
        calc
          intOfZ finish = intOfZ current + (Int.ofNat n + 1) := hfinish
          _ = intOfZ current + (1 + Int.ofNat n) := by
            rw [Int.add_comm (Int.ofNat n) 1]
          _ = intOfZ current + 1 + Int.ofNat n := by
            rw [Int.add_assoc]

private def unchangedOnRestrict {P Q : block → Z → Prop} {m m' : mem}
    (hPQ : ∀ b ofs, P b ofs → Q b ofs) (h : Mem.unchanged_on Q m m') :
    Mem.unchanged_on P m m' where
  unchanged_on_nextblock := h.unchanged_on_nextblock
  unchanged_on_perm := by
    intro b ofs k p hP hb
    exact h.unchanged_on_perm b ofs k p (hPQ b ofs hP) hb
  unchanged_on_contents := by
    intro b ofs hP hp
    exact h.unchanged_on_contents b ofs (hPQ b ofs hP) hp

def disjoint_footprint (P Q : massert) : Prop :=
  ∀ b ofs, P.m_footprint b ofs → Q.m_footprint b ofs → False

def sepconj (P Q : massert) : massert where
  m_pred := fun m => P.m_pred m ∧ Q.m_pred m ∧ disjoint_footprint P Q
  m_footprint := fun b ofs => P.m_footprint b ofs ∨ Q.m_footprint b ofs
  m_invar := by
    intro m m' hpred hunch
    exact ⟨
      P.m_invar m m' hpred.1
        (unchangedOnRestrict (fun b ofs h => Or.inl h) hunch),
      Q.m_invar m m' hpred.2.1
        (unchangedOnRestrict (fun b ofs h => Or.inr h) hunch),
      hpred.2.2
    ⟩
  m_valid := by
    intro m b ofs hpred hfoot
    cases hfoot with
    | inl h => exact P.m_valid m b ofs hpred.1 h
    | inr h => exact Q.m_valid m b ofs hpred.2.1 h

/-! Rocq `Program` obligations retained as exact proposition surfaces. -/

def sepconj_obligation_1Statement : Prop :=
  ∀ (P Q : massert) (m m' : mem),
    (sepconj P Q).m_pred m →
    Mem.unchanged_on (sepconj P Q).m_footprint m m' →
    (sepconj P Q).m_pred m'

def sepconj_obligation_2Statement : Prop :=
  ∀ (P Q : massert) (m : mem) (b : block) (ofs : Z),
    (sepconj P Q).m_pred m →
    (sepconj P Q).m_footprint b ofs →
    Mem.valid_block m b

def sep_impStatement : Prop :=
  ∀ P P' Q Q' m,
    (sepconj P Q).m_pred m →
    massert_imp P P' →
    massert_imp Q Q' →
    (sepconj P' Q').m_pred m

def sep_comm_1Statement : Prop :=
  ∀ P Q, massert_imp (sepconj P Q) (sepconj Q P)

def sep_commStatement : Prop :=
  ∀ P Q, massert_eqv (sepconj P Q) (sepconj Q P)

def sep_assoc_1Statement : Prop :=
  ∀ P Q R,
    massert_imp (sepconj (sepconj P Q) R) (sepconj P (sepconj Q R))

def sep_assoc_2Statement : Prop :=
  ∀ P Q R,
    massert_imp (sepconj P (sepconj Q R)) (sepconj (sepconj P Q) R)

def sep_assocStatement : Prop :=
  ∀ P Q R,
    massert_eqv (sepconj (sepconj P Q) R) (sepconj P (sepconj Q R))

def sep_swapStatement : Prop :=
  ∀ P Q R,
    massert_eqv (sepconj P (sepconj Q R)) (sepconj Q (sepconj P R))

theorem sep_swap : sep_swapStatement := by
  intro P Q R
  constructor
  · constructor
    · intro m h
      refine ⟨h.2.1.1, ⟨h.1, h.2.1.2.1, ?_⟩, ?_⟩
      · intro b ofs hP hR
        exact h.2.2 b ofs hP (Or.inr hR)
      · intro b ofs hQ hPR
        cases hPR with
        | inl hP => exact h.2.2 b ofs hP (Or.inl hQ)
        | inr hR => exact h.2.1.2.2 b ofs hQ hR
    · intro b ofs h
      cases h with
      | inl hQ => exact Or.inr (Or.inl hQ)
      | inr hPR =>
          cases hPR with
          | inl hP => exact Or.inl hP
          | inr hR => exact Or.inr (Or.inr hR)
  · constructor
    · intro m h
      refine ⟨h.2.1.1, ⟨h.1, h.2.1.2.1, ?_⟩, ?_⟩
      · intro b ofs hQ hR
        exact h.2.2 b ofs hQ (Or.inr hR)
      · intro b ofs hP hQR
        cases hQR with
        | inl hQ => exact h.2.2 b ofs hQ (Or.inl hP)
        | inr hR => exact h.2.1.2.2 b ofs hP hR
    · intro b ofs h
      cases h with
      | inl hP => exact Or.inr (Or.inl hP)
      | inr hQR =>
          cases hQR with
          | inl hQ => exact Or.inl hQ
          | inr hR => exact Or.inr (Or.inr hR)

def sep_swap12 : sep_swapStatement := sep_swap

def sep_swap23Statement : Prop :=
  ∀ P Q R S,
    massert_eqv
      (sepconj P (sepconj Q (sepconj R S)))
      (sepconj P (sepconj R (sepconj Q S)))

def sep_swap34Statement : Prop :=
  ∀ P Q R S T,
    massert_eqv
      (sepconj P (sepconj Q (sepconj R (sepconj S T))))
      (sepconj P (sepconj Q (sepconj S (sepconj R T))))

def sep_swap45Statement : Prop :=
  ∀ P Q R S T U,
    massert_eqv
      (sepconj P (sepconj Q (sepconj R (sepconj S (sepconj T U)))))
      (sepconj P (sepconj Q (sepconj R (sepconj T (sepconj S U)))))

def sep_swap2 : sep_swapStatement := sep_swap

def sep_swap3Statement : Prop :=
  ∀ P Q R S,
    massert_eqv
      (sepconj P (sepconj Q (sepconj R S)))
      (sepconj R (sepconj Q (sepconj P S)))

def sep_swap4Statement : Prop :=
  ∀ P Q R S T,
    massert_eqv
      (sepconj P (sepconj Q (sepconj R (sepconj S T))))
      (sepconj S (sepconj Q (sepconj R (sepconj P T))))

def sep_swap5Statement : Prop :=
  ∀ P Q R S T U,
    massert_eqv
      (sepconj P (sepconj Q (sepconj R (sepconj S (sepconj T U)))))
      (sepconj T (sepconj Q (sepconj R (sepconj S (sepconj P U)))))

def sep_dropStatement : Prop :=
  ∀ P Q m, (sepconj P Q).m_pred m → Q.m_pred m

def sep_drop2Statement : Prop :=
  ∀ P Q R m,
    (sepconj P (sepconj Q R)).m_pred m → (sepconj P R).m_pred m

def sep_proj1Statement : Prop :=
  ∀ Q P m, (sepconj P Q).m_pred m → P.m_pred m

theorem sep_proj1 : sep_proj1Statement := by
  intro Q P m h
  exact h.1

def sep_proj2Statement : Prop :=
  ∀ P Q m, (sepconj P Q).m_pred m → Q.m_pred m

def sep_pick1 : sep_proj1Statement := sep_proj1

def sep_pick2Statement : Prop :=
  ∀ P Q R m, (sepconj P (sepconj Q R)).m_pred m → Q.m_pred m

def sep_pick3Statement : Prop :=
  ∀ P Q R S m,
    (sepconj P (sepconj Q (sepconj R S))).m_pred m → R.m_pred m

def sep_pick4Statement : Prop :=
  ∀ P Q R S T m,
    (sepconj P (sepconj Q (sepconj R (sepconj S T)))).m_pred m → S.m_pred m

def sep_pick5Statement : Prop :=
  ∀ P Q R S T U m,
    (sepconj P (sepconj Q (sepconj R (sepconj S (sepconj T U))))).m_pred m →
      T.m_pred m

def sep_preservedStatement : Prop :=
  ∀ m m' P Q,
    (sepconj P Q).m_pred m →
    (P.m_pred m → P.m_pred m') →
    (Q.m_pred m → Q.m_pred m') →
    (sepconj P Q).m_pred m'

def pure (P : Prop) : massert where
  m_pred := fun _ => P
  m_footprint := fun _ _ => False
  m_invar := by intro _ _ h _; exact h
  m_valid := by intro _ _ _ _ h; exact False.elim h

def pure_obligation_2Statement : Prop :=
  ∀ (m : mem) (b : block), False → Mem.valid_block m b

def sep_pureStatement : Prop :=
  ∀ P Q m, (sepconj (pure P) Q).m_pred m ↔ P ∧ Q.m_pred m

def range (b : block) (lo hi : Z) : massert where
  m_pred := fun m =>
    zLe z0 lo ∧ zLe hi Ptrofs.modulus ∧
      ∀ i k p, zLe lo i ∧ zLt i hi → Mem.perm m b i k p
  m_footprint := fun b' ofs' => b' = b ∧ zLe lo ofs' ∧ zLt ofs' hi
  m_invar := by
    intro m m' hpred hunch
    refine ⟨hpred.1, hpred.2.1, ?_⟩
    intro i k p hi
    have hp := hpred.2.2 i k p hi
    have hb := validBlockOfPerm hp
    exact (hunch.unchanged_on_perm b i k p ⟨rfl, hi⟩ hb).mp hp
  m_valid := by
    intro m b' ofs hpred hfoot
    rw [hfoot.1]
    exact validBlockOfPerm (hpred.2.2 ofs Cur Freeable ⟨hfoot.2.1, hfoot.2.2⟩)

def range_obligation_1Statement : Prop :=
  ∀ (b : block) (lo hi : Z) (m m' : mem),
    (range b lo hi).m_pred m →
    Mem.unchanged_on (range b lo hi).m_footprint m m' →
    (range b lo hi).m_pred m'

def range_obligation_2Statement : Prop :=
  ∀ (b : block) (lo hi : Z) (m : mem) (b' : block) (ofs : Z),
    (range b lo hi).m_pred m →
    (range b lo hi).m_footprint b' ofs →
    Mem.valid_block m b'

def range_splitStatement : Prop :=
  ∀ b lo hi P mid m,
    (zLe lo mid ∧ zLe mid hi) →
    (sepconj (range b lo hi) P).m_pred m →
    (sepconj (range b lo mid) (sepconj (range b mid hi) P)).m_pred m

def range_drop_leftStatement : Prop :=
  ∀ b lo hi P mid m,
    (zLe lo mid ∧ zLe mid hi) →
    (sepconj (range b lo hi) P).m_pred m →
    (sepconj (range b mid hi) P).m_pred m

def range_drop_rightStatement : Prop :=
  ∀ b lo hi P mid m,
    (zLe lo mid ∧ zLe mid hi) →
    (sepconj (range b lo hi) P).m_pred m →
    (sepconj (range b lo mid) P).m_pred m

def range_split_2Statement : Prop :=
  ∀ b lo hi P mid al m,
    (zLe lo (align mid al) ∧ zLe (align mid al) hi) →
    zLt z0 al →
    (sepconj (range b lo hi) P).m_pred m →
    (sepconj (range b lo mid) (sepconj (range b (align mid al) hi) P)).m_pred m

def range_preservedStatement : Prop :=
  ∀ m m' b lo hi,
    (range b lo hi).m_pred m →
    (∀ i k p, zLe lo i ∧ zLt i hi → Mem.perm m b i k p → Mem.perm m' b i k p) →
    (range b lo hi).m_pred m'

def contains (chunk : memory_chunk) (b : block) (ofs : Z) (spec : val → Prop) : massert where
  m_pred := fun m =>
    (zLe z0 ofs ∧ zLe ofs Ptrofs.max_unsigned) ∧
      Mem.valid_access m chunk b ofs Freeable ∧
      ∃ v, Mem.load chunk m b ofs = some v ∧ spec v
  m_footprint := fun b' ofs' =>
    b' = b ∧ zLe ofs ofs' ∧ zLt ofs' (zAdd ofs (size_chunk chunk))
  m_invar := by
    intro m m' hpred hunch
    rcases hpred with ⟨⟨hlo, hhi⟩, hvalid, v, hload, hspec⟩
    have hvalid' : Mem.valid_access m' chunk b ofs Freeable := by
      refine ⟨?_, hvalid.2⟩
      intro i hi
      have hp := hvalid.1 i hi
      have hb := validBlockOfPerm hp
      exact (hunch.unchanged_on_perm b i Cur Freeable ⟨rfl, hi⟩ hb).mp hp
    have hAccess : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) →
        (PMap.get b m'.mem_access) i Cur = (PMap.get b m.mem_access) i Cur := by
      intro i hi
      have hp := hvalid.1 i hi
      have hb := validBlockOfPerm hp
      have hp' := (hunch.unchanged_on_perm b i Cur Freeable ⟨rfl, hi⟩ hb).mp hp
      rw [accessFreeableOfPerm hp', accessFreeableOfPerm hp]
    have hContents : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) →
        ZMap.get i (PMap.get b m'.mem_contents) =
          ZMap.get i (PMap.get b m.mem_contents) := by
      intro i hi
      have hp := hvalid.1 i hi
      exact hunch.unchanged_on_contents b i ⟨rfl, hi⟩ (permReadableOfFreeable hp)
    refine ⟨⟨hlo, hhi⟩, hvalid', v, ?_, hspec⟩
    rw [load_eq] at hload ⊢
    have hValidReadable :
        Mem.valid_access m' chunk b ofs Readable ↔
          Mem.valid_access m chunk b ofs Readable := by
      constructor
      · intro h
        refine ⟨?_, h.2⟩
        intro i hi
        have hp := h.1 i hi
        unfold Mem.perm at hp ⊢
        rw [hAccess i hi] at hp
        exact hp
      · intro h
        refine ⟨?_, h.2⟩
        intro i hi
        have hp := h.1 i hi
        unfold Mem.perm at hp ⊢
        rw [hAccess i hi]
        exact hp
    have hGuard :
        validAccessBool m' chunk b ofs Readable =
          validAccessBool m chunk b ofs Readable := by
      unfold validAccessBool
      cases hm' : Mem.valid_access_dec m' chunk b ofs Readable with
      | left hp' =>
          cases hm : Mem.valid_access_dec m chunk b ofs Readable with
          | left _ => rfl
          | right hn => exact (hn (hValidReadable.mp hp')).elim
      | right hn' =>
          cases hm : Mem.valid_access_dec m chunk b ofs Readable with
          | left hp => exact (hn' (hValidReadable.mpr hp)).elim
          | right _ => rfl
    have hGet :
        Mem.getN (size_chunk_nat chunk) ofs (PMap.get b m'.mem_contents) =
          Mem.getN (size_chunk_nat chunk) ofs (PMap.get b m.mem_contents) :=
      getNCongr m m' b ofs (zAdd ofs (size_chunk chunk)) ofs
        (size_chunk_nat chunk) hContents (by
          unfold zLe ZArith.BinInt.Z.le
          omega) (chunkSpanInt chunk ofs)
    rw [hGuard, hGet]
    exact hload
  m_valid := by
    intro m b' ofs' hpred hfoot
    rw [hfoot.1]
    have hvalid := hpred.2.1
    exact validBlockOfPerm (hvalid.1 ofs' ⟨hfoot.2.1, hfoot.2.2⟩)

def contains_obligation_1Statement : Prop :=
  ∀ (chunk : memory_chunk) (b : block) (ofs : Z) (spec : val → Prop)
    (m m' : mem),
    (contains chunk b ofs spec).m_pred m →
    Mem.unchanged_on (contains chunk b ofs spec).m_footprint m m' →
    (contains chunk b ofs spec).m_pred m'

def contains_obligation_2Statement : Prop :=
  ∀ (chunk : memory_chunk) (b : block) (ofs : Z) (spec : val → Prop)
    (m : mem) (b' : block) (ofs' : Z),
    (contains chunk b ofs spec).m_pred m →
    (contains chunk b ofs spec).m_footprint b' ofs' →
    Mem.valid_block m b'

def contains_no_overflowStatement : Prop :=
  ∀ spec m chunk b ofs,
    (contains chunk b ofs spec).m_pred m → zLe z0 ofs ∧ zLe ofs Ptrofs.max_unsigned

def load_ruleStatement : Prop :=
  ∀ spec m chunk b ofs,
    (contains chunk b ofs spec).m_pred m →
    ∃ v, Mem.load chunk m b ofs = some v ∧ spec v

def loadv_ruleStatement : Prop :=
  ∀ spec m chunk b ofs,
    (contains chunk b ofs spec).m_pred m →
    ∃ v, Mem.loadv chunk m (Vptr b (Ptrofs.repr ofs)) = some v ∧ spec v

def store_ruleStatement : Prop :=
  ∀ chunk m b ofs v spec1 spec P,
    (sepconj (contains chunk b ofs spec1) P).m_pred m →
    spec (Val.load_result chunk v) →
    ∃ m', Mem.store chunk m b ofs v = some m' ∧
      (sepconj (contains chunk b ofs spec) P).m_pred m'

def storev_ruleStatement : Prop :=
  ∀ chunk m b ofs v spec1 spec P,
    (sepconj (contains chunk b ofs spec1) P).m_pred m →
    spec (Val.load_result chunk v) →
    ∃ m', Mem.storev chunk m (Vptr b (Ptrofs.repr ofs)) v = some m' ∧
      (sepconj (contains chunk b ofs spec) P).m_pred m'

def range_containsStatement : Prop :=
  ∀ chunk b ofs P m,
    (sepconj (range b ofs (zAdd ofs (size_chunk chunk))) P).m_pred m →
    zDivide (align_chunk chunk) ofs →
    (sepconj (contains chunk b ofs (fun _ => True)) P).m_pred m

def contains_impStatement : Prop :=
  ∀ spec1 spec2 chunk b ofs,
    (∀ v, spec1 v → spec2 v) →
    massert_imp (contains chunk b ofs spec1) (contains chunk b ofs spec2)

def hasvalue (chunk : memory_chunk) (b : block) (ofs : Z) (v : val) : massert :=
  contains chunk b ofs (fun v' => v' = v)

def mconj (P Q : massert) : massert where
  m_pred := fun m => P.m_pred m ∧ Q.m_pred m
  m_footprint := fun b ofs => P.m_footprint b ofs ∨ Q.m_footprint b ofs
  m_invar := by
    intro m m' hpred hunch
    exact ⟨
      P.m_invar m m' hpred.1
        (unchangedOnRestrict (fun b ofs h => Or.inl h) hunch),
      Q.m_invar m m' hpred.2
        (unchangedOnRestrict (fun b ofs h => Or.inr h) hunch)
    ⟩
  m_valid := by
    intro m b ofs hpred hfoot
    cases hfoot with
    | inl h => exact P.m_valid m b ofs hpred.1 h
    | inr h => exact Q.m_valid m b ofs hpred.2 h

def mconj_obligation_1Statement : Prop :=
  ∀ (P Q : massert) (m m' : mem),
    (mconj P Q).m_pred m →
    Mem.unchanged_on (mconj P Q).m_footprint m m' →
    (mconj P Q).m_pred m'

def mconj_obligation_2Statement : Prop :=
  ∀ (P Q : massert) (m : mem) (b : block) (ofs : Z),
    (mconj P Q).m_pred m →
    (mconj P Q).m_footprint b ofs →
    Mem.valid_block m b

def mconj_introStatement : Prop :=
  ∀ P Q R m,
    (sepconj P R).m_pred m →
    (sepconj Q R).m_pred m →
    (sepconj (mconj P Q) R).m_pred m

def mconj_proj1Statement : Prop :=
  ∀ P Q R m,
    (sepconj (mconj P Q) R).m_pred m → (sepconj P R).m_pred m

def mconj_proj2Statement : Prop :=
  ∀ P Q R m,
    (sepconj (mconj P Q) R).m_pred m → (sepconj Q R).m_pred m

def frame_mconjStatement : Prop :=
  ∀ P P' Q R m m',
    (sepconj (mconj P Q) R).m_pred m →
    (sepconj P' R).m_pred m' →
    Q.m_pred m' →
    (sepconj (mconj P' Q) R).m_pred m'

def minjection (j : meminj) (m0 : mem) : massert where
  m_pred := fun m => Mem.inject j m0 m
  m_footprint := fun b ofs =>
    ∃ b0 delta,
      j b0 = some (b, delta) ∧ Mem.perm m0 b0 (zSub ofs delta) Max Nonempty
  m_invar := by
    intro m m' hinj hunch
    refine {
      mi_inj := {
        mi_perm := ?_,
        mi_align := hinj.mi_inj.mi_align,
        mi_memval := ?_
      },
      mi_freeblocks := hinj.mi_freeblocks,
      mi_mappedblocks := ?_,
      mi_no_overlap := hinj.mi_no_overlap,
      mi_representable := hinj.mi_representable,
      mi_perm_inv := ?_
    }
    · intro b1 b2 delta ofs k p hmap hp
      have hpMax := permMaxNonemptyOfPerm hp
      have htarget := hinj.mi_inj.mi_perm b1 b2 delta ofs k p hmap hp
      have hvalid := hinj.mi_mappedblocks b1 b2 delta hmap
      have hfoot :
          ∃ b0 delta0,
            j b0 = some (b2, delta0) ∧
              Mem.perm m0 b0 (zSub (zAdd ofs delta) delta0) Max Nonempty := by
        exact ⟨b1, delta, hmap, by simpa [zSubAddCancel] using hpMax⟩
      exact (hunch.unchanged_on_perm b2 (zAdd ofs delta) k p hfoot hvalid).mp htarget
    · intro b1 ofs b2 delta hmap hp
      have hpMax := permMaxNonemptyOfPerm hp
      have htarget := hinj.mi_inj.mi_perm b1 b2 delta ofs Cur Readable hmap hp
      have hfoot :
          ∃ b0 delta0,
            j b0 = some (b2, delta0) ∧
              Mem.perm m0 b0 (zSub (zAdd ofs delta) delta0) Max Nonempty := by
        exact ⟨b1, delta, hmap, by simpa [zSubAddCancel] using hpMax⟩
      rw [hunch.unchanged_on_contents b2 (zAdd ofs delta) hfoot htarget]
      exact hinj.mi_inj.mi_memval b1 ofs b2 delta hmap hp
    · intro b b' delta hmap
      exact Nat.lt_of_lt_of_le (hinj.mi_mappedblocks b b' delta hmap)
        hunch.unchanged_on_nextblock
    · intro b1 ofs b2 delta k p hmap hp
      by_cases hsrc : Mem.perm m0 b1 ofs Max Nonempty
      · have hfoot :
            ∃ b0 delta0,
              j b0 = some (b2, delta0) ∧
                Mem.perm m0 b0 (zSub (zAdd ofs delta) delta0) Max Nonempty := by
          exact ⟨b1, delta, hmap, by simpa [zSubAddCancel] using hsrc⟩
        have hvalid := hinj.mi_mappedblocks b1 b2 delta hmap
        have hpOld := (hunch.unchanged_on_perm b2 (zAdd ofs delta) k p hfoot hvalid).mpr hp
        exact hinj.mi_perm_inv b1 ofs b2 delta k p hmap hpOld
      · exact Or.inr hsrc
  m_valid := by
    intro m b ofs hinj hfoot
    rcases hfoot with ⟨b0, delta, hmap, _⟩
    exact hinj.mi_mappedblocks b0 b delta hmap

def minjection_obligation_1Statement : Prop :=
  ∀ (j : meminj) (m0 m m' : mem),
    (minjection j m0).m_pred m →
    Mem.unchanged_on (minjection j m0).m_footprint m m' →
    (minjection j m0).m_pred m'

def minjection_obligation_2Statement : Prop :=
  ∀ (j : meminj) (m0 m : mem) (b : block) (ofs : Z),
    (minjection j m0).m_pred m →
    (minjection j m0).m_footprint b ofs →
    Mem.valid_block m b

def loadv_parallel_ruleStatement : Prop :=
  ∀ j m1 m2 chunk addr1 v1 addr2,
    (minjection j m1).m_pred m2 →
    Mem.loadv chunk m1 addr1 = some v1 →
    Val.inject j addr1 addr2 →
    ∃ v2, Mem.loadv chunk m2 addr2 = some v2 ∧ Val.inject j v1 v2

def storev_parallel_ruleStatement : Prop :=
  ∀ j m1 m2 P chunk addr1 v1 m1' addr2 v2,
    (sepconj (minjection j m1) P).m_pred m2 →
    Mem.storev chunk m1 addr1 v1 = some m1' →
    Val.inject j addr1 addr2 →
    Val.inject j v1 v2 →
    ∃ m2', Mem.storev chunk m2 addr2 v2 = some m2' ∧
      (sepconj (minjection j m1') P).m_pred m2'

def alloc_parallel_ruleStatement : Prop :=
  ∀ m1 sz1 m1' b1 m2 sz2 m2' b2 P j lo hi delta,
    (sepconj (minjection j m1) P).m_pred m2 →
    Mem.alloc m1 z0 sz1 = (m1', b1) →
    Mem.alloc m2 z0 sz2 = (m2', b2) →
    zDivide z8 delta →
    lo = delta →
    hi = zAdd delta (zMax z0 sz1) →
    (zLe z0 sz2 ∧ zLe sz2 Ptrofs.max_unsigned) →
    zLe z0 delta → zLe hi sz2 →
    ∃ j',
      (sepconj (range b2 z0 lo)
        (sepconj (range b2 hi sz2) (sepconj (minjection j' m1') P))).m_pred m2' ∧
      inject_incr j j' ∧
      j' b1 = some (b2, delta) ∧
      (∀ b, b ≠ b1 → j' b = j b)

def free_parallel_ruleStatement : Prop :=
  ∀ j m1 b1 sz1 m1' m2 b2 sz2 lo hi delta P,
    (sepconj (range b2 z0 lo)
      (sepconj (range b2 hi sz2) (sepconj (minjection j m1) P))).m_pred m2 →
    Mem.free m1 b1 z0 sz1 = some m1' →
    j b1 = some (b2, delta) →
    lo = delta → hi = zAdd delta (zMax z0 sz1) →
    ∃ m2', Mem.free m2 b2 z0 sz2 = some m2' ∧
      (sepconj (minjection j m1') P).m_pred m2'

inductive globalenv_preserved {F V : Type} (ge : Genv.t F V) (j : meminj)
    (bound : block) : Prop where
  | globalenv_preserved_intro :
      (∀ b, Plt b bound → j b = some (b, z0)) →
      (∀ b1 b2 delta, j b1 = some (b2, delta) → Plt b2 bound → b1 = b2) →
      (∀ id b, Genv.find_symbol ge id = some b → Plt b bound) →
      (∀ b fd, Genv.find_funct_ptr ge b = some fd → Plt b bound) →
      (∀ b gv, Genv.find_var_info ge b = some gv → Plt b bound) →
      globalenv_preserved ge j bound

export globalenv_preserved (globalenv_preserved_intro)

def globalenv_inject {F V : Type} (ge : Genv.t F V) (j : meminj) : massert where
  m_pred := fun m => ∃ bound, Ple bound m.nextblock ∧ globalenv_preserved ge j bound
  m_footprint := fun _ _ => False
  m_invar := by
    intro m m' hpred hunch
    rcases hpred with ⟨bound, hbound, hge⟩
    exact ⟨bound, Nat.le_trans hbound hunch.unchanged_on_nextblock, hge⟩
  m_valid := by intro _ _ _ _ h; exact False.elim h

def globalenv_inject_obligation_1Statement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) (j : meminj) (m m' : mem),
    (globalenv_inject ge j).m_pred m →
    Mem.unchanged_on (globalenv_inject ge j).m_footprint m m' →
    (globalenv_inject ge j).m_pred m'

def globalenv_inject_obligation_2Statement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) (j : meminj) (m : mem) (b : block),
    (globalenv_inject ge j).m_pred m →
    False →
    Mem.valid_block m b

def globalenv_inject_preserves_globalsStatement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) j m,
    (globalenv_inject ge j).m_pred m → Events.meminj_preserves_globals F V ge j

def globalenv_inject_incrStatement : Prop :=
  ∀ j m0 (F V : Type) (ge : Genv.t F V) m j' P,
    inject_incr j j' →
    Events.inject_separated j j' m0 m →
    (sepconj (globalenv_inject ge j) P).m_pred m →
    (sepconj (globalenv_inject ge j') P).m_pred m

def external_call_parallel_ruleStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ xi (F V : Type) ef (ge : Genv.t F V) vargs1 m1 t vres1 m1' m2 j P vargs2,
    Events.external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs1 m1 t vres1 m1' →
    (sepconj (minjection j m1) (sepconj (globalenv_inject ge j) P)).m_pred m2 →
    Val.inject_list j vargs1 vargs2 →
    ∃ j' vres2 m2',
      Events.external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi ef (Genv.to_senv ge) vargs2 m2 t vres2 m2' ∧
      Val.inject j' vres1 vres2 ∧
      (sepconj (minjection j' m1') (sepconj (globalenv_inject ge j') P)).m_pred m2' ∧
      inject_incr j j' ∧
      Events.inject_separated j j' m1 m2

def alloc_parallel_rule_2Statement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) m1 sz1 m1' b1 m2 sz2 m2' b2 P j lo hi delta,
    (sepconj (minjection j m1) (sepconj (globalenv_inject ge j) P)).m_pred m2 →
    Mem.alloc m1 z0 sz1 = (m1', b1) →
    Mem.alloc m2 z0 sz2 = (m2', b2) →
    zDivide z8 delta →
    lo = delta →
    hi = zAdd delta (zMax z0 sz1) →
    (zLe z0 sz2 ∧ zLe sz2 Ptrofs.max_unsigned) →
    zLe z0 delta → zLe hi sz2 →
    ∃ j',
      (sepconj (range b2 z0 lo)
        (sepconj (range b2 hi sz2)
          (sepconj (minjection j' m1') (sepconj (globalenv_inject ge j') P)))).m_pred m2' ∧
      inject_incr j j' ∧
      j' b1 = some (b2, delta)

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem sep_imp : sep_impStatement := by
  intro P P' Q Q' m hpred hPP' hQQ'
  exact ⟨hPP'.1 m hpred.1, hQQ'.1 m hpred.2.1,
    fun b ofs hP' hQ' => hpred.2.2 b ofs (hPP'.2 b ofs hP') (hQQ'.2 b ofs hQ')⟩

theorem sep_comm_1 : sep_comm_1Statement := by
  intro P Q
  constructor
  · intro m hpred
    exact ⟨hpred.2.1, hpred.1, fun b ofs hQ hP => hpred.2.2 b ofs hP hQ⟩
  · intro b ofs hfoot
    cases hfoot with
    | inl hQ => exact Or.inr hQ
    | inr hP => exact Or.inl hP

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem sepconj_obligation_1 : sepconj_obligation_1Statement := by
  intro P Q m m' hpred hunch
  exact (sepconj P Q).m_invar m m' hpred hunch

theorem sepconj_obligation_2 : sepconj_obligation_2Statement := by
  intro P Q m b ofs hpred hfoot
  exact (sepconj P Q).m_valid m b ofs hpred hfoot

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem sep_comm : sep_commStatement := by
  intro P Q
  constructor
  · exact sep_comm_1 P Q
  · exact sep_comm_1 Q P

theorem sep_assoc_1 : sep_assoc_1Statement := by
  intro P Q R
  constructor
  · intro m h
    refine ⟨h.1.1, ⟨h.1.2.1, h.2.1, ?_⟩, ?_⟩
    · intro b ofs hQ hR
      exact h.2.2 b ofs (Or.inr hQ) hR
    · intro b ofs hP hQR
      cases hQR with
      | inl hQ => exact h.1.2.2 b ofs hP hQ
      | inr hR => exact h.2.2 b ofs (Or.inl hP) hR
  · intro b ofs hfoot
    cases hfoot with
    | inl hP => exact Or.inl (Or.inl hP)
    | inr hQR =>
        cases hQR with
        | inl hQ => exact Or.inl (Or.inr hQ)
        | inr hR => exact Or.inr hR

theorem sep_assoc_2 : sep_assoc_2Statement := by
  intro P Q R
  constructor
  · intro m h
    refine ⟨⟨h.1, h.2.1.1, ?_⟩, h.2.1.2.1, ?_⟩
    · intro b ofs hP hQ
      exact h.2.2 b ofs hP (Or.inl hQ)
    · intro b ofs hPQ hR
      cases hPQ with
      | inl hP => exact h.2.2 b ofs hP (Or.inr hR)
      | inr hQ => exact h.2.1.2.2 b ofs hQ hR
  · intro b ofs hfoot
    cases hfoot with
    | inl hPQ =>
        cases hPQ with
        | inl hP => exact Or.inl hP
        | inr hQ => exact Or.inr (Or.inl hQ)
    | inr hR => exact Or.inr (Or.inr hR)

theorem sep_assoc : sep_assocStatement := by
  intro P Q R
  constructor
  · exact sep_assoc_1 P Q R
  · exact sep_assoc_2 P Q R

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

private theorem massert_eqv_trans_scc085 {P Q R : massert}
    (hPQ : massert_eqv P Q) (hQR : massert_eqv Q R) : massert_eqv P R := by
  constructor
  · constructor
    · intro m h
      exact hQR.1.1 m (hPQ.1.1 m h)
    · intro b ofs h
      exact hPQ.1.2 b ofs (hQR.1.2 b ofs h)
  · constructor
    · intro m h
      exact hPQ.2.1 m (hQR.2.1 m h)
    · intro b ofs h
      exact hQR.2.2 b ofs (hPQ.2.2 b ofs h)

private theorem sepconj_eqv_right_scc085 {P Q R : massert} (hQR : massert_eqv Q R) :
    massert_eqv (sepconj P Q) (sepconj P R) := by
  constructor
  · constructor
    · intro m h
      refine ⟨h.1, hQR.1.1 m h.2.1, ?_⟩
      intro b ofs hP hR
      exact h.2.2 b ofs hP (hQR.1.2 b ofs hR)
    · intro b ofs h
      cases h with
      | inl hP => exact Or.inl hP
      | inr hR => exact Or.inr (hQR.1.2 b ofs hR)
  · constructor
    · intro m h
      refine ⟨h.1, hQR.2.1 m h.2.1, ?_⟩
      intro b ofs hP hQ
      exact h.2.2 b ofs hP (hQR.2.2 b ofs hQ)
    · intro b ofs h
      cases h with
      | inl hP => exact Or.inl hP
      | inr hQ => exact Or.inr (hQR.2.2 b ofs hQ)

theorem sep_swap23 : sep_swap23Statement := by
  intro P Q R S
  exact sepconj_eqv_right_scc085 (P := P) (sep_swap Q R S)

theorem sep_swap34 : sep_swap34Statement := by
  intro P Q R S T
  exact sepconj_eqv_right_scc085 (P := P)
    (sepconj_eqv_right_scc085 (P := Q) (sep_swap R S T))

theorem sep_swap45 : sep_swap45Statement := by
  intro P Q R S T U
  exact sepconj_eqv_right_scc085 (P := P)
    (sepconj_eqv_right_scc085 (P := Q)
      (sepconj_eqv_right_scc085 (P := R) (sep_swap S T U)))

theorem sep_swap3 : sep_swap3Statement := by
  intro P Q R S
  exact massert_eqv_trans_scc085 (sep_swap P Q (sepconj R S))
    (massert_eqv_trans_scc085
      (sepconj_eqv_right_scc085 (P := Q) (sep_swap P R S))
      (sep_swap Q R (sepconj P S)))

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem sep_swap4 : sep_swap4Statement := by
  intro P Q R S T
  exact massert_eqv_trans_scc085 (sep_swap P Q (sepconj R (sepconj S T)))
    (massert_eqv_trans_scc085
      (sepconj_eqv_right_scc085 (P := Q) (sep_swap3 P R S T))
      (sep_swap Q S (sepconj R (sepconj P T))))

theorem sep_swap5 : sep_swap5Statement := by
  intro P Q R S T U
  exact massert_eqv_trans_scc085 (sep_swap P Q (sepconj R (sepconj S (sepconj T U))))
    (massert_eqv_trans_scc085
      (sepconj_eqv_right_scc085 (P := Q) (sep_swap4 P R S T U))
      (sep_swap Q T (sepconj R (sepconj S (sepconj P U)))))

theorem sep_drop : sep_dropStatement := by
  intro P Q m h
  exact h.2.1

theorem sep_drop2 : sep_drop2Statement := by
  intro P Q R m h
  refine ⟨h.1, h.2.1.2.1, ?_⟩
  intro b ofs hP hR
  exact h.2.2 b ofs hP (Or.inr hR)

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem sep_proj2 : sep_proj2Statement := sep_drop

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem sep_pick2 : sep_pick2Statement := by
  intro P Q R m h
  exact h.2.1.1

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem sep_pick3 : sep_pick3Statement := by
  intro P Q R S m h
  exact h.2.1.2.1.1

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem sep_pick4 : sep_pick4Statement := by
  intro P Q R S T m h
  exact h.2.1.2.1.2.1.1

end CompCert4Lean.Common.Separation
