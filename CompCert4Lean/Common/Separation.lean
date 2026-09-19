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

namespace CompCert4Lean.Common.Separation

theorem sep_pick5 : sep_pick5Statement := by
  intro P Q R S T U m h
  exact h.2.1.2.1.2.1.2.1.1

theorem sep_preserved : sep_preservedStatement := by
  intro m m' P Q h hP hQ
  exact ⟨hP h.1, hQ h.2.1, h.2.2⟩

theorem pure_obligation_2 : pure_obligation_2Statement := by
  intro m b h
  exact False.elim h

theorem sep_pure : sep_pureStatement := by
  intro P Q m
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, by
      intro b ofs hP hQ
      exact False.elim hP⟩

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem range_obligation_1 : range_obligation_1Statement := by
  intro b lo hi m m' hpred hunch
  exact (range b lo hi).m_invar m m' hpred hunch

theorem range_obligation_2 : range_obligation_2Statement := by
  intro b lo hi m b' ofs hpred hfoot
  exact (range b lo hi).m_valid m b' ofs hpred hfoot

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers

theorem range_split : range_splitStatement := by
  intro b lo hi P mid m hmid h
  refine ⟨?_, ?_, ?_⟩
  · change zLe z0 lo ∧ zLe mid Ptrofs.modulus ∧
      (∀ i k p, zLe lo i ∧ zLt i mid → Mem.perm m b i k p)
    refine ⟨h.1.1, ?_, ?_⟩
    · have hhi := h.1.2.1
      unfold zLe ZArith.BinInt.Z.le at hmid hhi ⊢
      omega
    · intro i k p hi'
      apply h.1.2.2 i k p
      refine ⟨hi'.1, ?_⟩
      unfold zLe ZArith.BinInt.Z.le at hmid hi'
      unfold zLt ZArith.BinInt.Z.lt at hi' ⊢
      omega
  · change (range b mid hi).m_pred m ∧ P.m_pred m ∧
      disjoint_footprint (range b mid hi) P
    refine ⟨?_, h.2.1, ?_⟩
    · change zLe z0 mid ∧ zLe hi Ptrofs.modulus ∧
        (∀ i k p, zLe mid i ∧ zLt i hi → Mem.perm m b i k p)
      refine ⟨?_, h.1.2.1, ?_⟩
      · have hlo := h.1.1
        unfold zLe ZArith.BinInt.Z.le at hmid hlo ⊢
        omega
      · intro i k p hi'
        apply h.1.2.2 i k p
        refine ⟨?_, hi'.2⟩
        have hmi := hi'.1
        unfold zLe ZArith.BinInt.Z.le at hmid hmi ⊢
        omega
    · intro b' ofs hR hP
      rcases hR with ⟨hb, hmid', hlt⟩
      apply h.2.2 b' ofs
      · refine ⟨hb, ?_, hlt⟩
        unfold zLe ZArith.BinInt.Z.le at hmid hmid' ⊢
        omega
      · exact hP
  · intro b' ofs hleft hright
    cases hright with
    | inl hrightRange =>
        rcases hleft with ⟨hb1, hlo1, hlt1⟩
        rcases hrightRange with ⟨hb2, hmid2, hlt2⟩
        unfold zLe ZArith.BinInt.Z.le at hmid2
        unfold zLt ZArith.BinInt.Z.lt at hlt1
        omega
    | inr hP =>
        rcases hleft with ⟨hb1, hlo1, hlt1⟩
        apply h.2.2 b' ofs
        · refine ⟨hb1, hlo1, ?_⟩
          unfold zLe ZArith.BinInt.Z.le at hmid
          unfold zLt ZArith.BinInt.Z.lt at hlt1 ⊢
          omega
        · exact hP

theorem range_drop_left : range_drop_leftStatement := by
  intro b lo hi P mid m hmid h
  have hs := range_split b lo hi P mid m hmid h
  exact hs.2.1

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers

theorem range_drop_right : range_drop_rightStatement := by
  intro b lo hi P mid m hmid h
  exact sep_drop2 (range b lo mid) (range b mid hi) P m
    (range_split b lo hi P mid m hmid h)

theorem range_preserved : range_preservedStatement := by
  intro m m' b lo hi hpred hperm
  refine ⟨hpred.1, hpred.2.1, ?_⟩
  intro i k p hi'
  exact hperm i k p hi' (hpred.2.2 i k p hi')

theorem contains_obligation_2 : contains_obligation_2Statement := by
  intro chunk b ofs spec m b' ofs' hpred hfoot
  exact (contains chunk b ofs spec).m_valid m b' ofs' hpred hfoot

private theorem scc085_div_eq (a b : Z) :
    ZArith.BinInt.Z.div a b =
      zOfInt (if intOfZ b = 0 then 0 else if 0 < intOfZ b then
        Int.ediv (intOfZ a) (intOfZ b)
      else
        let d := -intOfZ b
        let q := Int.ediv (intOfZ a) d
        let r := Int.emod (intOfZ a) d
        if r = 0 then -q else -(q + 1)) := by
  rfl

private theorem scc085_align_le (x y : Z)
    (hy : ZArith.BinInt.Z.lt ZArith.BinInt.Z.Z0 y) :
    ZArith.BinInt.Z.le x (align x y) := by
  unfold ZArith.BinInt.Z.le align ZArith.BinInt.Z.mul
  rw [scc085_div_eq]
  simp only [intOfZ_zOfInt]
  unfold ZArith.BinInt.Z.sub ZArith.BinInt.Z.add
  simp only [intOfZ_zOfInt]
  have hyInt : 0 < intOfZ y := hy
  have hyNe : intOfZ y ≠ 0 := by omega
  rw [if_neg hyNe, if_pos hyInt]
  have h1 : intOfZ (Zpos xH) = 1 := by rfl
  rw [h1]
  change intOfZ x ≤ ((intOfZ x + intOfZ y - 1) / intOfZ y) * intOfZ y
  have hrem := Int.ediv_mul_add_emod (intOfZ x + intOfZ y - 1) (intOfZ y)
  have hnonneg := Int.emod_nonneg (intOfZ x + intOfZ y - 1) hyNe
  have hlt := Int.emod_lt_of_pos (intOfZ x + intOfZ y - 1) hyInt
  omega

private theorem scc085_range_drop_right_no_lo :
    ∀ b lo hi P mid m,
      ZArith.BinInt.Z.le mid hi →
      (sepconj (range b lo hi) P).m_pred m →
      (sepconj (range b lo mid) P).m_pred m := by
  intro b lo hi P mid m hmid h
  refine ⟨?_, h.2.1, ?_⟩
  · change ZArith.BinInt.Z.le ZArith.BinInt.Z.Z0 lo ∧
      ZArith.BinInt.Z.le mid Ptrofs.modulus ∧
      (∀ i k p, ZArith.BinInt.Z.le lo i ∧
        ZArith.BinInt.Z.lt i mid → Mem.perm m b i k p)
    refine ⟨h.1.1, ?_, ?_⟩
    · have hhi := h.1.2.1
      change intOfZ mid ≤ intOfZ hi at hmid
      change intOfZ hi ≤ intOfZ Ptrofs.modulus at hhi
      change intOfZ mid ≤ intOfZ Ptrofs.modulus
      omega
    · intro i k p hi'
      apply h.1.2.2 i k p
      refine ⟨hi'.1, ?_⟩
      change intOfZ mid ≤ intOfZ hi at hmid
      change intOfZ lo ≤ intOfZ i ∧ intOfZ i < intOfZ mid at hi'
      change intOfZ i < intOfZ hi
      omega
  · intro b' ofs hR hP
    rcases hR with ⟨hb, hlo, hlt⟩
    apply h.2.2 b' ofs
    · refine ⟨hb, hlo, ?_⟩
      change intOfZ mid ≤ intOfZ hi at hmid
      change intOfZ ofs < intOfZ mid at hlt
      change intOfZ ofs < intOfZ hi
      omega
    · exact hP

theorem range_split_2 : range_split_2Statement := by
  intro b lo hi P mid al m hmid hal h
  have hmidAlign : ZArith.BinInt.Z.le mid (align mid al) :=
    scc085_align_le mid al hal
  exact scc085_range_drop_right_no_lo b lo (align mid al)
    (sepconj (range b (align mid al) hi) P) mid m hmidAlign
    (range_split b lo hi P (align mid al) m hmid h)

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem contains_obligation_1 : contains_obligation_1Statement := by
  intro chunk b ofs spec m m' hpred hunch
  exact (contains chunk b ofs spec).m_invar m m' hpred hunch

theorem contains_no_overflow : contains_no_overflowStatement := by
  intro spec m chunk b ofs hpred
  exact hpred.1

theorem load_rule : load_ruleStatement := by
  intro spec m chunk b ofs hpred
  exact hpred.2.2

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem contains_imp : contains_impStatement := by
  intro spec1 spec2 chunk b ofs himp
  constructor
  · intro m hpred
    rcases hpred with ⟨hbounds, hvalid, v, hload, hspec⟩
    exact ⟨hbounds, hvalid, v, hload, himp v hspec⟩
  · intro b' ofs' hfoot
    exact hfoot

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers

theorem range_contains : range_containsStatement := by
  intro chunk b ofs P m hpred hdiv
  have hrange := hpred.1
  have hmax : zLe ofs Ptrofs.max_unsigned := by
    have hupper := hrange.2.1
    have hsize := size_chunk_pos chunk
    unfold zLe ZArith.BinInt.Z.le at hupper ⊢
    change (0 : Int) < intOfZ (size_chunk chunk) at hsize
    unfold zAdd ZArith.BinInt.Z.add at hupper
    rw [intOfZ_zOfInt] at hupper
    change intOfZ ofs ≤ intOfZ Ptrofs.modulus - 1
    omega
  have hfree : Mem.valid_access m chunk b ofs Freeable := by
    refine ⟨?_, hdiv⟩
    intro i hi
    exact hrange.2.2 i Cur Freeable hi
  have hread : Mem.valid_access m chunk b ofs Readable :=
    Mem.valid_access_implies m chunk b ofs Freeable Readable hfree (perm_F_any Readable)
  rcases Mem.valid_access_load m chunk b ofs hread with ⟨v, hload⟩
  refine ⟨⟨⟨hrange.1, hmax⟩, hfree, ⟨v, hload, True.intro⟩⟩, hpred.2.1, ?_⟩
  intro b' ofs' hfoot hP
  exact hpred.2.2 b' ofs' hfoot hP

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem mconj_obligation_1 : mconj_obligation_1Statement := by
  intro P Q m m' hpred hunch
  exact ⟨
    P.m_invar m m' hpred.1
      (unchangedOnRestrict (fun b ofs h => Or.inl h) hunch),
    Q.m_invar m m' hpred.2
      (unchangedOnRestrict (fun b ofs h => Or.inr h) hunch)
  ⟩

theorem mconj_obligation_2 : mconj_obligation_2Statement := by
  intro P Q m b ofs hpred hfoot
  cases hfoot with
  | inl hP => exact P.m_valid m b ofs hpred.1 hP
  | inr hQ => exact Q.m_valid m b ofs hpred.2 hQ

theorem mconj_intro : mconj_introStatement := by
  intro P Q R m hPR hQR
  refine ⟨⟨hPR.1, hQR.1⟩, hPR.2.1, ?_⟩
  intro b ofs hPQ hR
  cases hPQ with
  | inl hP => exact hPR.2.2 b ofs hP hR
  | inr hQ => exact hQR.2.2 b ofs hQ hR

theorem mconj_proj1 : mconj_proj1Statement := by
  intro P Q R m h
  refine ⟨h.1.1, h.2.1, ?_⟩
  intro b ofs hP hR
  exact h.2.2 b ofs (Or.inl hP) hR

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem mconj_proj2 : mconj_proj2Statement := by
  intro P Q R m h
  refine ⟨h.1.2, h.2.1, ?_⟩
  intro b ofs hQ hR
  exact h.2.2 b ofs (Or.inr hQ) hR

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem frame_mconj : frame_mconjStatement := by
  intro P P' Q R m m' h hP' hQ
  refine ⟨⟨hP'.1, hQ⟩, hP'.2.1, ?_⟩
  intro b ofs hfoot hR
  cases hfoot with
  | inl hP'foot => exact hP'.2.2 b ofs hP'foot hR
  | inr hQfoot => exact h.2.2 b ofs (Or.inr hQfoot) hR

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

theorem minjection_obligation_2 : minjection_obligation_2Statement := by
  intro j m0 m b ofs hinj hfoot
  exact (minjection j m0).m_valid m b ofs hinj hfoot

end CompCert4Lean.Common.Separation

namespace CompCert4Lean.Common.Separation

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem scc085_pmap_get_set_same {A : Type} (i : positive) (x : A)
    (m : PMap.t A) : PMap.get i (PMap.set i x m) = x := by
  change (match PTree.get i (PTree.set i x m.2) with
    | some y => y | none => m.1) = x
  rw [PTree.gsspec_proof]
  cases hpeq : peq i i with
  | left h => simp [hpeq]
  | right h => exact False.elim (h rfl)

private theorem scc085_pmap_get_set_other {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) (h : i ≠ j) : PMap.get i (PMap.set j x m) = PMap.get i m := by
  change (match PTree.get i (PTree.set j x m.2) with
    | some y => y | none => m.1) =
    (match PTree.get i m.2 with | some y => y | none => m.1)
  rw [PTree.gsspec_proof]
  cases hpeq : peq i j with
  | left hij => exact False.elim (h hij)
  | right hne => simp [hpeq]

private theorem scc085_free_range_perm (m : mem) (b : positive) (lo hi : Z)
    (m' : mem) (hfree : Mem.free m b lo hi = some m') :
    Mem.range_perm m b lo hi Cur Freeable := by
  unfold Mem.free at hfree
  cases hr : Mem.range_perm_dec m b lo hi Cur Freeable with
  | left hp =>
      simp [hr] at hfree
      cases hfree
      exact hp
  | right hn =>
      simp [hr] at hfree
      cases hfree.1

private theorem scc085_perm_of_free (m m' : mem) (b : positive) (lo hi : Z)
    (hfree : Mem.free m b lo hi = some m') :
    ∀ b' ofs (k : perm_kind) (p : permission),
      Mem.perm m' b' ofs k p → Mem.perm m b' ofs k p := by
  intro b' ofs k p hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    subst m'
    unfold Mem.perm at hp ⊢
    by_cases hb : b' = b
    · subst b'
      change Mem.perm_order' ((PMap.get b (PMap.set b
        (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
      rw [scc085_pmap_get_set_same] at hp
      split at hp
      · change False at hp
        exact False.elim hp
      · exact hp
    · dsimp [Mem.unchecked_free] at hp
      change Mem.perm_order' ((PMap.get b' (PMap.set b
        (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
      rw [scc085_pmap_get_set_other _ _ _ _ hb] at hp
      exact hp
  next hcond => cases hfree

private theorem scc085_perm_free_1 (m m' : mem) (b : positive) (lo hi : Z)
    (hfree : Mem.free m b lo hi = some m') :
    ∀ b' ofs (k : perm_kind) (p : permission),
      (b' ≠ b ∨ zLt ofs lo ∨ zLe hi ofs) →
      Mem.perm m b' ofs k p → Mem.perm m' b' ofs k p := by
  intro b' ofs k p hout hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    rw [← hm']
    unfold Mem.perm at hp ⊢
    dsimp [Mem.unchecked_free] at ⊢
    by_cases hb : b' = b
    · subst b'
      change Mem.perm_order' ((PMap.get b m.mem_access) ofs k) p at hp
      change Mem.perm_order'
        ((PMap.get b (PMap.set b
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p
      rw [scc085_pmap_get_set_same]
      split
      · rename_i hin
        exfalso
        rcases hout with hne | hlt | hge
        · exact hne rfl
        · change (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true at hin
          have hin' := Bool.and_eq_true_iff.mp hin
          have hlo' : intOfZ lo ≤ intOfZ ofs := by
            simpa [ZArith.BinInt.Z.leb] using hin'.1
          change intOfZ ofs < intOfZ lo at hlt
          omega
        · change (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true at hin
          have hin' := Bool.and_eq_true_iff.mp hin
          have hhi' : intOfZ ofs < intOfZ hi := by
            simpa [ZArith.BinInt.Z.ltb] using hin'.2
          change intOfZ hi ≤ intOfZ ofs at hge
          omega
      · exact hp
    · change Mem.perm_order' (PMap.get b' m.mem_access ofs k) p at hp
      change Mem.perm_order'
        ((PMap.get b' (PMap.set b
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p
      rw [scc085_pmap_get_set_other _ _ _ _ hb]
      exact hp
  next hcond => cases hfree

private theorem scc085_perm_free_2 (m m' : mem) (b : positive) (lo hi : Z)
    (hfree : Mem.free m b lo hi = some m') :
    ∀ ofs (k : perm_kind) (p : permission),
      zLe lo ofs → zLt ofs hi → ¬ Mem.perm m' b ofs k p := by
  intro ofs k p hlo hhi hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    rw [← hm'] at hp
    unfold Mem.perm at hp
    dsimp [Mem.unchecked_free] at hp
    change Mem.perm_order'
      ((PMap.get b (PMap.set b
        (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
    rw [scc085_pmap_get_set_same] at hp
    split at hp
    · exact hp
    · rename_i hnot
      exfalso
      apply hnot
      change (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true
      have hlo' : intOfZ lo ≤ intOfZ ofs := by exact hlo
      have hhi' : intOfZ ofs < intOfZ hi := by exact hhi
      simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb, hlo', hhi']
  next hcond => cases hfree

private theorem scc085_outside_interval (x lo hi : Z) :
    ¬ (zLe lo x ∧ zLt x hi) → zLt x lo ∨ zLe hi x := by
  intro h
  by_cases hlt : zLt x lo
  · exact Or.inl hlt
  by_cases hge : zLe hi x
  · exact Or.inr hge
  exfalso
  apply h
  constructor
  · change intOfZ lo ≤ intOfZ x
    change ¬ intOfZ x < intOfZ lo at hlt
    change ¬ intOfZ hi ≤ intOfZ x at hge
    omega
  · change intOfZ x < intOfZ hi
    change ¬ intOfZ hi ≤ intOfZ x at hge
    omega

private theorem scc085_nextblock_free (m : mem) (b : positive) (lo hi : Z)
    (m' : mem) (hfree : Mem.free m b lo hi = some m') :
    m'.nextblock = m.nextblock := by
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    subst m'
    rfl
  next hcond => cases hfree

private theorem scc085_free_contents (m m' : mem) (b : positive) (lo hi : Z)
    (hfree : Mem.free m b lo hi = some m') :
    m'.mem_contents = m.mem_contents := by
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    subst m'
    rfl
  next hcond => cases hfree

private theorem scc085_free_left_inject (f : meminj) (m m' tm : mem)
    (b : positive) (lo hi : Z)
    (hinj : Mem.inject f m tm)
    (hfree : Mem.free m b lo hi = some m') :
    Mem.inject f m' tm := by
  have hnext := scc085_nextblock_free m b lo hi m' hfree
  have hcont := scc085_free_contents m m' b lo hi hfree
  refine {
    mi_inj := ?_,
    mi_freeblocks := ?_,
    mi_mappedblocks := hinj.mi_mappedblocks,
    mi_no_overlap := ?_,
    mi_representable := ?_,
    mi_perm_inv := ?_ }
  · refine { mi_perm := ?_, mi_align := ?_, mi_memval := ?_ }
    · intro b1 b2 delta ofs k p hmap hp
      exact hinj.mi_inj.mi_perm b1 b2 delta ofs k p hmap
        (scc085_perm_of_free m m' b lo hi hfree b1 ofs k p hp)
    · intro b1 b2 delta chunk ofs p hmap hrange
      apply hinj.mi_inj.mi_align b1 b2 delta chunk ofs p hmap
      intro q hq
      exact scc085_perm_of_free m m' b lo hi hfree b1 q Max p (hrange q hq)
    · intro b1 ofs b2 delta hmap hp
      have hp' : Mem.perm m b1 ofs Cur Readable :=
        scc085_perm_of_free m m' b lo hi hfree b1 ofs Cur Readable hp
      have hmv := hinj.mi_inj.mi_memval b1 ofs b2 delta hmap hp'
      simpa [hcont] using hmv
  · intro b' hvalid
    apply hinj.mi_freeblocks b'
    intro hvalid0
    apply hvalid
    change Plt b' m'.nextblock
    rw [hnext]
    exact hvalid0
  · intro b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne hmap1 hmap2 hp1 hp2
    apply hinj.mi_no_overlap b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne hmap1 hmap2
    · exact scc085_perm_of_free m m' b lo hi hfree b1 ofs1 Max Nonempty hp1
    · exact scc085_perm_of_free m m' b lo hi hfree b2 ofs2 Max Nonempty hp2
  · intro b1 b2 delta ofs hmap hperm
    apply hinj.mi_representable b1 b2 delta ofs hmap
    rcases hperm with h | h
    · left
      exact scc085_perm_of_free m m' b lo hi hfree b1
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) Max Nonempty h
    · right
      exact scc085_perm_of_free m m' b lo hi hfree b1
        (zSub (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) z1) Max Nonempty h
  · intro b1 ofs b2 delta k p hmap hp2
    rcases hinj.mi_perm_inv b1 ofs b2 delta k p hmap hp2 with hp1 | hnone
    · by_cases hb : b1 = b
      · subst b1
        by_cases hinside : zLe lo ofs ∧ zLt ofs hi
        · right
          intro hp1'
          exact scc085_perm_free_2 m m' b lo hi hfree ofs Max Nonempty
            hinside.1 hinside.2 hp1'
        · left
          apply scc085_perm_free_1 m m' b lo hi hfree b ofs k p
          · rcases scc085_outside_interval ofs lo hi hinside with hlt | hge
            · exact Or.inr (Or.inl hlt)
            · exact Or.inr (Or.inr hge)
          · exact hp1
      · left
        apply scc085_perm_free_1 m m' b lo hi hfree b1 ofs k p
        · exact Or.inl hb
        · exact hp1
    · right
      intro hp1'
      exact hnone (scc085_perm_of_free m m' b lo hi hfree b1 ofs Max Nonempty hp1')

private theorem scc085_free_right_inject (f : meminj) (m tm tm' : mem)
    (b : positive) (lo hi : Z)
    (hinj : Mem.inject f m tm)
    (hfree : Mem.free tm b lo hi = some tm')
    (hside : ∀ b1 delta ofs (k : perm_kind) (p : permission),
      f b1 = some (b, delta) →
      Mem.perm m b1 ofs k p →
      zLe lo (zAdd ofs delta) ∧ zLt (zAdd ofs delta) hi → False) :
    Mem.inject f m tm' := by
  have hnext := scc085_nextblock_free tm b lo hi tm' hfree
  have hcont := scc085_free_contents tm tm' b lo hi hfree
  refine {
    mi_inj := ?_,
    mi_freeblocks := hinj.mi_freeblocks,
    mi_mappedblocks := ?_,
    mi_no_overlap := hinj.mi_no_overlap,
    mi_representable := hinj.mi_representable,
    mi_perm_inv := ?_ }
  · refine { mi_perm := ?_, mi_align := hinj.mi_inj.mi_align, mi_memval := ?_ }
    · intro b1 b2 delta ofs k p hmap hp
      apply scc085_perm_free_1 tm tm' b lo hi hfree b2
        (zAdd ofs delta) k p
      · by_cases hb : b2 = b
        · subst b2
          by_cases hinside : zLe lo (zAdd ofs delta) ∧ zLt (zAdd ofs delta) hi
          · exact False.elim (hside b1 delta ofs k p hmap hp hinside)
          · rcases scc085_outside_interval (zAdd ofs delta) lo hi hinside with hlt | hge
            · exact Or.inr (Or.inl hlt)
            · exact Or.inr (Or.inr hge)
        · exact Or.inl hb
      · exact hinj.mi_inj.mi_perm b1 b2 delta ofs k p hmap hp
    · intro b1 ofs b2 delta hmap hp
      have hmv := hinj.mi_inj.mi_memval b1 ofs b2 delta hmap hp
      simpa [hcont] using hmv
  · intro b1 b2 delta hmap
    have hv := hinj.mi_mappedblocks b1 b2 delta hmap
    change Plt b2 tm'.nextblock
    rw [hnext]
    exact hv
  · intro b1 ofs b2 delta k p hmap hp2
    exact hinj.mi_perm_inv b1 ofs b2 delta k p hmap
      (scc085_perm_of_free tm tm' b lo hi hfree b2 (zAdd ofs delta) k p hp2)

private theorem scc085_free_unchanged_on (Q : positive → Z → Prop)
    (m : mem) (b : positive) (lo hi : Z) (m' : mem)
    (hfree : Mem.free m b lo hi = some m')
    (hout : ∀ i, zLe lo i ∧ zLt i hi → ¬ Q b i) :
    Mem.unchanged_on Q m m' := by
  have hnext := scc085_nextblock_free m b lo hi m' hfree
  have hcont := scc085_free_contents m m' b lo hi hfree
  refine {
    unchanged_on_nextblock := ?_,
    unchanged_on_perm := ?_,
    unchanged_on_contents := ?_ }
  · change Ple m.nextblock m'.nextblock
    rw [hnext]
    exact Ple_refl _
  · intro b' ofs k p hQ hvalid
    constructor
    · intro hp
      apply scc085_perm_free_1 m m' b lo hi hfree b' ofs k p
      · by_cases hb : b' = b
        · subst b'
          have hnotinside : ¬ (zLe lo ofs ∧ zLt ofs hi) := by
            intro hins
            exact hout ofs hins hQ
          rcases scc085_outside_interval ofs lo hi hnotinside with hlt | hge
          · exact Or.inr (Or.inl hlt)
          · exact Or.inr (Or.inr hge)
        · exact Or.inl hb
      · exact hp
    · intro hp
      exact scc085_perm_of_free m m' b lo hi hfree b' ofs k p hp
  · intro b' ofs hQ hp
    simpa [hcont]

private theorem scc085_range_perm_free (m : mem) (b : positive) (lo hi : Z)
    (hperm : Mem.range_perm m b lo hi Cur Freeable) :
    ∃ m', Mem.free m b lo hi = some m' := by
  cases hr : Mem.range_perm_dec m b lo hi Cur Freeable with
  | left hp =>
      refine ⟨Mem.unchecked_free m b lo hi, ?_⟩
      unfold Mem.free
      rw [hr]
      rfl
  | right hn =>
      exact False.elim (hn hperm)

private theorem scc085_middle_source_bounds (lo hi delta sz x : Z)
    (hlo : lo = delta) (hhi : hi = zAdd delta (zMax z0 sz))
    (hmiddle : zLe lo x ∧ zLt x hi) :
    zLe z0 (zSub x delta) ∧ zLt (zSub x delta) sz := by
  have hlo' : intOfZ lo = intOfZ delta := by simpa [hlo]
  have hhi' : intOfZ hi = intOfZ delta + intOfZ (zMax z0 sz) := by
    rw [hhi]
    change intOfZ (zOfInt (intOfZ delta + intOfZ (zMax z0 sz))) = _
    rw [intOfZ_zOfInt]
  have hxlo : intOfZ lo ≤ intOfZ x := by
    have h := hmiddle.1
    change intOfZ lo ≤ intOfZ x at h
    exact h
  have hxhi : intOfZ x < intOfZ hi := by
    have h := hmiddle.2
    change intOfZ x < intOfZ hi at h
    exact h
  have hsub : intOfZ (ZArith.BinInt.Z.sub x delta) = intOfZ x - intOfZ delta := by
    change intOfZ (zOfInt (intOfZ x - intOfZ delta)) = _
    rw [intOfZ_zOfInt]
  have hz0 : intOfZ z0 = (0 : Int) := rfl
  have hsz : (0 : Int) ≤ intOfZ sz := by
    by_cases hs : (0 : Int) ≤ intOfZ sz
    · exact hs
    · have hmax0 : intOfZ (zMax z0 sz) = (0 : Int) := by
        simp [ZArith.BinInt.Z.max, hz0, hs]
      omega
  constructor
  · change intOfZ z0 ≤ intOfZ (ZArith.BinInt.Z.sub x delta)
    apply (show (0 : Int) ≤ intOfZ (ZArith.BinInt.Z.sub x delta) from ?_)
    exact hsub.symm ▸ (by omega : (0 : Int) ≤ intOfZ x - intOfZ delta)
  · change intOfZ (ZArith.BinInt.Z.sub x delta) < intOfZ sz
    exact hsub ▸ (by
      have hmaxsz : intOfZ (zMax z0 sz) = intOfZ sz := by
        simp [ZArith.BinInt.Z.max, hz0, hsz]
      omega : intOfZ x - intOfZ delta < intOfZ sz)

theorem free_parallel_rule : free_parallel_ruleStatement := by
  intro j m1 b1 sz1 m1' m2 b2 sz2 lo hi delta P hpred hfree hmap hlo hhi
  rcases hpred with ⟨hloPred, hrest, hdisjLo⟩
  rcases hrest with ⟨hhiPred, hrest', hdisjHi⟩
  rcases hrest' with ⟨hinj, hP, hdisjIP⟩
  have hperm : Mem.range_perm m2 b2 z0 sz2 Cur Freeable := by
    intro ofs hofs
    rcases hofs with ⟨hofs0, hofs2⟩
    by_cases hlt : zLt ofs lo
    · exact hloPred.2.2 ofs Cur Freeable ⟨hofs0, hlt⟩
    by_cases hge : zLe hi ofs
    · exact hhiPred.2.2 ofs Cur Freeable ⟨hge, hofs2⟩
    have hsrc : Mem.range_perm m1 b1 z0 (zMax z0 sz1) Cur Freeable := by
      intro q hq
      have hbase := scc085_free_range_perm m1 b1 z0 sz1 m1' hfree
      apply hbase q
      constructor
      · exact hq.1
      · have hq1 := hq.1
        have hq2 := hq.2
        change intOfZ z0 ≤ intOfZ q at hq1
        change intOfZ q < intOfZ (zMax z0 sz1) at hq2
        have hz0 : intOfZ z0 = (0 : Int) := rfl
        by_cases hs : (0 : Int) ≤ intOfZ sz1
        · change intOfZ q < intOfZ sz1
          simpa [ZArith.BinInt.Z.max, hz0, hs] using hq2
        · simp [ZArith.BinInt.Z.max, hz0, hs] at hq2
          omega
    have hbounds : zLe z0 (zSub ofs delta) ∧
        zLt (zSub ofs delta) (zMax z0 sz1) := by
      have hlo' : intOfZ lo = intOfZ delta := by
        simpa [hlo]
      have hhi' : intOfZ hi = intOfZ delta + intOfZ (zMax z0 sz1) := by
        rw [hhi]
        change intOfZ (zOfInt (intOfZ delta + intOfZ (zMax z0 sz1))) = _
        rw [intOfZ_zOfInt]
      have hsub : intOfZ (ZArith.BinInt.Z.sub ofs delta) = intOfZ ofs - intOfZ delta := by
        change intOfZ (zOfInt (intOfZ ofs - intOfZ delta)) = _
        rw [intOfZ_zOfInt]
      have hnotlt : intOfZ lo ≤ intOfZ ofs := by
        change ¬ intOfZ ofs < intOfZ lo at hlt
        omega
      have hnotge : intOfZ ofs < intOfZ hi := by
        change ¬ intOfZ hi ≤ intOfZ ofs at hge
        omega
      constructor
      · change intOfZ z0 ≤ intOfZ (ZArith.BinInt.Z.sub ofs delta)
        apply (show (0 : Int) ≤ intOfZ (ZArith.BinInt.Z.sub ofs delta) from ?_)
        exact hsub.symm ▸ (by omega : (0 : Int) ≤ intOfZ ofs - intOfZ delta)
      · change intOfZ (ZArith.BinInt.Z.sub ofs delta) < intOfZ (zMax z0 sz1)
        exact hsub ▸ (by omega : intOfZ ofs - intOfZ delta < intOfZ (zMax z0 sz1))
    have hsrcperm := hsrc (zSub ofs delta) hbounds
    have htarget := hinj.mi_inj.mi_perm b1 b2 delta (zSub ofs delta)
      Cur Freeable hmap hsrcperm
    have haddsub : zAdd (zSub ofs delta) delta = ofs := by
      apply intOfZ_injective
      change intOfZ (zOfInt
        (intOfZ (zSub ofs delta) + intOfZ delta)) = intOfZ ofs
      simp only [intOfZ_zOfInt]
      change intOfZ (zOfInt (intOfZ ofs - intOfZ delta)) + intOfZ delta = intOfZ ofs
      simp only [intOfZ_zOfInt]
      omega
    simpa [haddsub] using htarget
  rcases scc085_range_perm_free m2 b2 z0 sz2 hperm with ⟨m2', hfree2⟩
  have hinjLeft : Mem.inject j m1' m2 :=
    scc085_free_left_inject j m1 m1' m2 b1 z0 sz1 hinj hfree
  have hside : ∀ b0 delta0 ofs (k : perm_kind) (p : permission),
      j b0 = some (b2, delta0) →
      Mem.perm m1' b0 ofs k p →
      zLe z0 (zAdd ofs delta0) ∧ zLt (zAdd ofs delta0) sz2 → False := by
    intro b0 delta0 ofs k p hmap0 hp hmiddle
    have hpPre : Mem.perm m1 b0 ofs k p :=
      scc085_perm_of_free m1 m1' b1 z0 sz1 hfree b0 ofs k p hp
    have hminOld : (minjection j m1).m_footprint b2 (zAdd ofs delta0) := by
      refine ⟨b0, delta0, hmap0, ?_⟩
      simpa [zSubAddCancel] using
        (permMaxNonemptyOfPerm hpPre)
    by_cases hlt : zLt (zAdd ofs delta0) lo
    · apply hdisjLo b2 (zAdd ofs delta0)
      · exact ⟨rfl, hmiddle.1, hlt⟩
      · exact Or.inr (Or.inl hminOld)
    by_cases hge : zLe hi (zAdd ofs delta0)
    · apply hdisjHi b2 (zAdd ofs delta0)
      · exact ⟨rfl, hge, hmiddle.2⟩
      · exact Or.inl hminOld
    have hmid : zLe lo (zAdd ofs delta0) ∧
        zLt (zAdd ofs delta0) hi := by
      constructor
      · change intOfZ lo ≤ intOfZ (zAdd ofs delta0)
        change ¬ intOfZ (zAdd ofs delta0) < intOfZ lo at hlt
        omega
      · change intOfZ (zAdd ofs delta0) < intOfZ hi
        change ¬ intOfZ hi ≤ intOfZ (zAdd ofs delta0) at hge
        omega
    by_cases hb : b0 = b1
    · subst b0
      have hmapEq := hmap0
      rw [hmap] at hmapEq
      cases hmapEq
      have hbounds0 := scc085_middle_source_bounds lo hi delta sz1
        (zAdd ofs delta) hlo hhi hmid
      have hbounds : zLe z0 ofs ∧ zLt ofs sz1 := by
        simpa [zSubAddCancel] using hbounds0
      exact scc085_perm_free_2 m1 m1' b1 z0 sz1 hfree ofs k p
        hbounds.1 hbounds.2 hp
    · have hp0 : Mem.perm m1 b0 ofs k p :=
        hpPre
      have hbounds := scc085_middle_source_bounds lo hi delta sz1
        (zAdd ofs delta0) hlo hhi hmid
      have hsrc := scc085_free_range_perm m1 b1 z0 sz1 m1' hfree
      have hq : Mem.perm m1 b1
          (zSub (zAdd ofs delta0) delta) Cur Freeable := by
        apply hsrc
        exact hbounds
      have hNo := hinj.mi_no_overlap b0 b2 delta0 b1 b2 delta
        ofs (zSub (zAdd ofs delta0) delta) hb hmap0 hmap
        (permMaxNonemptyOfPerm hp0) (permMaxNonemptyOfPerm hq)
      rcases hNo with hne | hne
      · exact hne rfl
      · apply hne
        have hcancel : zAdd (zSub (zAdd ofs delta0) delta) delta =
            zAdd ofs delta0 := by
          apply intOfZ_injective
          change intOfZ (zOfInt
            (intOfZ (zSub (zAdd ofs delta0) delta) + intOfZ delta)) =
            intOfZ (zAdd ofs delta0)
          simp only [intOfZ_zOfInt]
          change intOfZ (zOfInt
            (intOfZ (zAdd ofs delta0) - intOfZ delta)) + intOfZ delta =
            intOfZ (zAdd ofs delta0)
          simp only [intOfZ_zOfInt]
          omega
        exact hcancel.symm
  have hinjFinal : Mem.inject j m1' m2' :=
    scc085_free_right_inject j m1' m2 m2' b2 z0 sz2 hinjLeft hfree2 hside
  have hP' : P.m_pred m2' := by
    apply P.m_invar m2 m2' hP
    apply scc085_free_unchanged_on (fun b ofs => P.m_footprint b ofs)
      m2 b2 z0 sz2 m2' hfree2
    intro i hrange hPi
    by_cases hlt : zLt i lo
    · apply hdisjLo b2 i
      · refine ⟨rfl, ?_, hlt⟩
        exact hrange.1
      · exact Or.inr (Or.inr hPi)
    by_cases hge : zLe hi i
    · apply hdisjHi b2 i
      · exact ⟨rfl, hge, hrange.2⟩
      · exact Or.inr hPi
    have hmid : zLe lo i ∧ zLt i hi := by
      constructor
      · change intOfZ lo ≤ intOfZ i
        change ¬ intOfZ i < intOfZ lo at hlt
        omega
      · change intOfZ i < intOfZ hi
        change ¬ intOfZ hi ≤ intOfZ i at hge
        omega
    have hbounds := scc085_middle_source_bounds lo hi delta sz1 i hlo hhi hmid
    have hsrc := scc085_free_range_perm m1 b1 z0 sz1 m1' hfree
    have hsrcperm := hsrc (zSub i delta) hbounds
    apply hdisjIP b2 i
    · refine ⟨b1, delta, hmap, ?_⟩
      exact permMaxNonemptyOfPerm hsrcperm
    · exact hPi
  have hdisjFinal : disjoint_footprint (minjection j m1') P := by
    intro b0 ofs hmin hPfoot
    rcases hmin with ⟨bsrc, dsrc, hmapSrc, hpPost⟩
    apply hdisjIP b0 ofs
    · refine ⟨bsrc, dsrc, hmapSrc, ?_⟩
      exact scc085_perm_of_free m1 m1' b1 z0 sz1 hfree
        bsrc (zSub ofs dsrc) Max Nonempty hpPost
    · exact hPfoot
  exact ⟨m2', hfree2, ⟨hinjFinal, hP', hdisjFinal⟩⟩

theorem globalenv_inject_obligation_1 : globalenv_inject_obligation_1Statement := by
  intro F V ge j m m' hpred hunch
  exact (globalenv_inject ge j).m_invar m m' hpred hunch

private theorem scc085_alloc_fresh (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (h : Mem.alloc m lo hi = (m', b)) : b = m.nextblock := by
  unfold Mem.alloc at h
  cases h
  rfl

private theorem scc085_alloc_nextblock (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (h : Mem.alloc m lo hi = (m', b)) :
    m'.nextblock = PArith.BinPos.Pos.succ m.nextblock := by
  unfold Mem.alloc at h
  cases h
  rfl

private theorem scc085_alloc_unchanged_on (Q : block → Z → Prop)
    (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (h : Mem.alloc m lo hi = (m', b)) : Mem.unchanged_on Q m m' := by
  unfold Mem.alloc at h
  cases h
  constructor
  · exact Ple_succ _
  · intro b' ofs k p hQ hvalid
    have hne : b' ≠ m.nextblock := Plt_ne _ _ hvalid
    unfold Mem.perm
    rw [scc085_pmap_get_set_other _ _ _ _ hne]
  · intro b' ofs hQ hread
    have hne : b' ≠ m.nextblock :=
      Plt_ne _ _ (Mem.perm_valid_block m b' ofs Cur Readable hread)
    rw [scc085_pmap_get_set_other _ _ _ _ hne]

private theorem scc085_alloc_perm_new (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (h : Mem.alloc m lo hi = (m', b)) (ofs : Z) (k : perm_kind)
    (hbounds : zLe lo ofs ∧ zLt ofs hi) : Mem.perm m' b ofs k Freeable := by
  unfold Mem.alloc at h
  cases h
  unfold Mem.perm
  rw [scc085_pmap_get_set_same]
  change Mem.perm_order'
    (if (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true
      then some Freeable else none) Freeable
  have hin : (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true := by
    change intOfZ lo ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi at hbounds
    simpa [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb] using hbounds
  rw [if_pos hin]
  exact perm_refl Freeable

private theorem scc085_alloc_perm_new_inv (m : mem) (lo hi : Z) (m' : mem)
    (b : block) (h : Mem.alloc m lo hi = (m', b)) (ofs : Z) (k : perm_kind)
    (p : permission) (hp : Mem.perm m' b ofs k p) : zLe lo ofs ∧ zLt ofs hi := by
  unfold Mem.alloc at h
  cases h
  unfold Mem.perm at hp
  rw [scc085_pmap_get_set_same] at hp
  change Mem.perm_order'
    (if (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true
      then some Freeable else none) p at hp
  by_cases hin : (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true
  · change intOfZ lo ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi
    simpa [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb] using hin
  · simp [hin, Mem.perm_order'] at hp

private theorem scc085_alloc_perm_old (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (h : Mem.alloc m lo hi = (m', b)) (b' : block) (ofs : Z) (k : perm_kind)
    (p : permission) (hne : b' ≠ b) (hp : Mem.perm m b' ofs k p) :
    Mem.perm m' b' ofs k p := by
  unfold Mem.alloc at h
  cases h
  unfold Mem.perm at hp ⊢
  rw [scc085_pmap_get_set_other _ _ _ _ hne]
  exact hp

private theorem scc085_alloc_perm_old_inv (m : mem) (lo hi : Z) (m' : mem)
    (b : block) (h : Mem.alloc m lo hi = (m', b)) (b' : block) (ofs : Z)
    (k : perm_kind) (p : permission) (hne : b' ≠ b) (hp : Mem.perm m' b' ofs k p) :
    Mem.perm m b' ofs k p := by
  unfold Mem.alloc at h
  cases h
  unfold Mem.perm at hp ⊢
  rw [scc085_pmap_get_set_other _ _ _ _ hne] at hp
  exact hp

private theorem scc085_alloc_contents_new (m : mem) (lo hi : Z) (m' : mem)
    (b : block) (h : Mem.alloc m lo hi = (m', b)) (ofs : Z) :
    ZMap.get ofs (PMap.get b m'.mem_contents) =
      CompCert4Lean.Common.Memdata.Undef := by
  unfold Mem.alloc at h
  cases h
  rw [scc085_pmap_get_set_same]
  rfl

private theorem scc085_alloc_contents_old (m : mem) (lo hi : Z) (m' : mem)
    (b : block) (h : Mem.alloc m lo hi = (m', b)) (b' : block) (ofs : Z)
    (hne : b' ≠ b) :
    ZMap.get ofs (PMap.get b' m'.mem_contents) =
      ZMap.get ofs (PMap.get b' m.mem_contents) := by
  unfold Mem.alloc at h
  cases h
  rw [scc085_pmap_get_set_other _ _ _ _ hne]

private theorem scc085_alloc_valid_new (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (h : Mem.alloc m lo hi = (m', b)) : Mem.valid_block m' b := by
  change Plt b m'.nextblock
  rw [scc085_alloc_fresh m lo hi m' b h, scc085_alloc_nextblock m lo hi m' b h]
  exact Plt_succ m.nextblock

private theorem scc085_perm_of_freeable {m : mem} {b : block} {ofs : Z}
    {k : perm_kind} {p : permission} (h : Mem.perm m b ofs k Freeable) :
    Mem.perm m b ofs k p := by
  unfold Mem.perm
  rw [accessFreeableOfPerm h]
  exact perm_F_any p

private def scc085_extend_inj (j : meminj) (b1 b2 : block) (delta : Z) : meminj :=
  fun b => if b = b1 then some (b2, delta) else j b

private theorem scc085_extend_inj_same (j : meminj) (b1 b2 : block) (delta : Z) :
    scc085_extend_inj j b1 b2 delta b1 = some (b2, delta) := by
  simp [scc085_extend_inj]

private theorem scc085_extend_inj_other (j : meminj) (b1 b2 : block) (delta : Z)
    (b : block) (hne : b ≠ b1) :
    scc085_extend_inj j b1 b2 delta b = j b := by
  simp [scc085_extend_inj, hne]

private theorem scc085_align_chunk_divides_eight
    (chunk : CompCert4Lean.Common.AST.memory_chunk) :
    zDivide (CompCert4Lean.Common.Memdata.align_chunk chunk) z8 := by
  cases chunk <;> simp [CompCert4Lean.Common.Memdata.align_chunk, zDivide, z1, z8]
  all_goals first
    | exact ⟨ZArith.BinInt.Z.of_nat 8, by rfl⟩
    | exact ⟨ZArith.BinInt.Z.of_nat 4, by rfl⟩
    | exact ⟨ZArith.BinInt.Z.of_nat 2, by rfl⟩
    | exact ⟨ZArith.BinInt.Z.of_nat 1, by rfl⟩

private theorem scc085_align_chunk_divides_delta (delta : Z)
    (hdiv : zDivide z8 delta) (chunk : CompCert4Lean.Common.AST.memory_chunk) :
    zDivide (CompCert4Lean.Common.Memdata.align_chunk chunk) delta := by
  rcases scc085_align_chunk_divides_eight chunk with ⟨ka, ha⟩
  rcases hdiv with ⟨kd, hd⟩
  refine ⟨ZArith.BinInt.Z.mul ka kd, ?_⟩
  calc
    delta = ZArith.BinInt.Z.mul z8 kd := hd
    _ = ZArith.BinInt.Z.mul
        (ZArith.BinInt.Z.mul (CompCert4Lean.Common.Memdata.align_chunk chunk) ka) kd :=
      congrArg (fun x => ZArith.BinInt.Z.mul x kd) ha
    _ = ZArith.BinInt.Z.mul (CompCert4Lean.Common.Memdata.align_chunk chunk)
        (ZArith.BinInt.Z.mul ka kd) := by
      apply intOfZ_injective
      simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
      exact Int.mul_assoc _ _ _

private theorem scc085_alloc_shift_bounds (sz1 sz2 lo hi delta ofs : Z)
    (hsrc : zLe z0 ofs ∧ zLt ofs sz1)
    (hlo : lo = delta) (hhi : hi = zAdd delta (zMax z0 sz1))
    (hdelta : zLe z0 delta) (hhisz : zLe hi sz2) :
    zLe z0 (zAdd ofs delta) ∧ zLt (zAdd ofs delta) sz2 := by
  have hsz1 : (0 : Int) ≤ intOfZ sz1 := by
    have hloSrc := hsrc.1
    have hhiSrc := hsrc.2
    change (0 : Int) ≤ intOfZ ofs at hloSrc
    change intOfZ ofs < intOfZ sz1 at hhiSrc
    omega
  have hmax : intOfZ (zMax z0 sz1) = intOfZ sz1 := by
    simp [ZArith.BinInt.Z.max, (show intOfZ z0 = (0 : Int) by rfl), hsz1]
  have hhiInt : intOfZ hi = intOfZ delta + intOfZ sz1 := by
    rw [hhi]
    change intOfZ (zOfInt (intOfZ delta + intOfZ (zMax z0 sz1))) = _
    rw [intOfZ_zOfInt, hmax]
  have hadd : intOfZ (zAdd ofs delta) = intOfZ ofs + intOfZ delta := by
    change intOfZ (zOfInt (intOfZ ofs + intOfZ delta)) = _
    rw [intOfZ_zOfInt]
  constructor
  · change (0 : Int) ≤ intOfZ (zAdd ofs delta)
    change (0 : Int) ≤ intOfZ delta at hdelta
    have hsrcLo := hsrc.1
    change (0 : Int) ≤ intOfZ ofs at hsrcLo
    omega
  · change intOfZ (zAdd ofs delta) < intOfZ sz2
    change intOfZ hi ≤ intOfZ sz2 at hhisz
    have hsrcHi := hsrc.2
    change intOfZ ofs < intOfZ sz1 at hsrcHi
    omega

private theorem scc085_alloc_representable_bounds (sz1 sz2 hi delta u : Z)
    (hsrc : (zLe z0 u ∧ zLt u sz1) ∨
      (zLe z0 (zSub u z1) ∧ zLt (zSub u z1) sz1))
    (hu0 : zLe z0 u) (hhi : hi = zAdd delta (zMax z0 sz1))
    (hhisz : zLe hi sz2)
    (hsz2 : zLe sz2 CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned)
    (hdelta : zLe z0 delta) :
    zLe z0 (zAdd u delta) ∧
      zLe (zAdd u delta) CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned := by
  have hsub : intOfZ (zSub u z1) = intOfZ u - 1 := by
    change intOfZ (zOfInt (intOfZ u - intOfZ z1)) = _
    rw [intOfZ_zOfInt, intOfZZ1]
  have hsz1 : (0 : Int) ≤ intOfZ sz1 := by
    rcases hsrc with h | h
    · have hlo := h.1
      have hlt := h.2
      change (0 : Int) ≤ intOfZ u at hlo
      change intOfZ u < intOfZ sz1 at hlt
      omega
    · have hlo := h.1
      have hlt := h.2
      change (0 : Int) ≤ intOfZ (zSub u z1) at hlo
      change intOfZ (zSub u z1) < intOfZ sz1 at hlt
      omega
  have hmax : intOfZ (zMax z0 sz1) = intOfZ sz1 := by
    simp [ZArith.BinInt.Z.max, (show intOfZ z0 = (0 : Int) by rfl), hsz1]
  have hhiInt : intOfZ hi = intOfZ delta + intOfZ sz1 := by
    rw [hhi]
    change intOfZ (zOfInt (intOfZ delta + intOfZ (zMax z0 sz1))) = _
    rw [intOfZ_zOfInt, hmax]
  have hadd : intOfZ (zAdd u delta) = intOfZ u + intOfZ delta := by
    change intOfZ (zOfInt (intOfZ u + intOfZ delta)) = _
    rw [intOfZ_zOfInt]
  constructor
  · change (0 : Int) ≤ intOfZ (zAdd u delta)
    change (0 : Int) ≤ intOfZ u at hu0
    change (0 : Int) ≤ intOfZ delta at hdelta
    omega
  · change intOfZ (zAdd u delta) ≤
      intOfZ CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned
    change intOfZ hi ≤ intOfZ sz2 at hhisz
    change intOfZ sz2 ≤
      intOfZ CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned at hsz2
    rcases hsrc with h | h
    · have hlt := h.2
      change intOfZ u < intOfZ sz1 at hlt
      omega
    · have hlt := h.2
      change intOfZ (zSub u z1) < intOfZ sz1 at hlt
      omega

private theorem scc085_alloc_mapped_inject
    (j : meminj) (m1 m2 m1' m2' : mem) (sz1 sz2 : Z) (b1 b2 : block)
    (hi delta : Z) (hinj : Mem.inject j m1 m2)
    (halloc1 : Mem.alloc m1 z0 sz1 = (m1', b1))
    (halloc2 : Mem.alloc m2 z0 sz2 = (m2', b2))
    (hdiv : zDivide z8 delta)
    (hhi : hi = zAdd delta (zMax z0 sz1))
    (hsz2 : zLe sz2 CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned)
    (hdelta : zLe z0 delta) (hhisz : zLe hi sz2) :
    Mem.inject (scc085_extend_inj j b1 b2 delta) m1' m2' := by
  let j' := scc085_extend_inj j b1 b2 delta
  have hfresh1 : ¬ Mem.valid_block m1 b1 := by
    intro hv
    rw [scc085_alloc_fresh m1 z0 sz1 m1' b1 halloc1] at hv
    exact (Plt_ne _ _ hv) rfl
  have hfresh2 : ¬ Mem.valid_block m2 b2 := by
    intro hv
    rw [scc085_alloc_fresh m2 z0 sz2 m2' b2 halloc2] at hv
    exact (Plt_ne _ _ hv) rfl
  have hjnone : j b1 = none := hinj.mi_freeblocks b1 hfresh1
  have hincr : CompCert4Lean.Common.Values.inject_incr j j' := by
    intro b bt d hmap
    by_cases hb : b = b1
    · subst b
      rw [hjnone] at hmap
      cases hmap
    · change scc085_extend_inj j b1 b2 delta b = some (bt, d)
      rw [scc085_extend_inj_other j b1 b2 delta b hb]
      exact hmap
  have hsourceOld : ∀ b bt d, j b = some (bt, d) → b ≠ b1 := by
    intro b bt d hmap hb
    subst b
    rw [hjnone] at hmap
    cases hmap
  have htargetOld : ∀ b bt d, j b = some (bt, d) → bt ≠ b2 := by
    intro b bt d hmap hbt
    subst bt
    exact hfresh2 (hinj.mi_mappedblocks b b2 d hmap)
  change Mem.inject j' m1' m2'
  refine {
    mi_inj := {
      mi_perm := ?_,
      mi_align := ?_,
      mi_memval := ?_
    },
    mi_freeblocks := ?_,
    mi_mappedblocks := ?_,
    mi_no_overlap := ?_,
    mi_representable := ?_,
    mi_perm_inv := ?_
  }
  · intro b bt d ofs k p hmap hp
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 delta b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      have hsrc := scc085_alloc_perm_new_inv m1 z0 sz1 m1' b1 halloc1
        ofs k p hp
      have htgt := scc085_alloc_shift_bounds sz1 sz2 delta hi delta ofs
        hsrc rfl hhi hdelta hhisz
      exact scc085_perm_of_freeable
        (scc085_alloc_perm_new m2 z0 sz2 m2' b2 halloc2
          (zAdd ofs delta) k htgt)
    · change scc085_extend_inj j b1 b2 delta b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 delta b hb] at hmap
      have hpOld := scc085_alloc_perm_old_inv m1 z0 sz1 m1' b1 halloc1
        b ofs k p hb hp
      have htOld := hinj.mi_inj.mi_perm b bt d ofs k p hmap hpOld
      exact scc085_alloc_perm_old m2 z0 sz2 m2' b2 halloc2 bt
        (zAdd ofs d) k p (htargetOld b bt d hmap) htOld
  · intro b bt d chunk ofs p hmap hrange
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 delta b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      exact scc085_align_chunk_divides_delta delta hdiv chunk
    · change scc085_extend_inj j b1 b2 delta b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 delta b hb] at hmap
      apply hinj.mi_inj.mi_align b bt d chunk ofs p hmap
      intro i hibounds
      exact scc085_alloc_perm_old_inv m1 z0 sz1 m1' b1 halloc1
        b i Max p hb (hrange i hibounds)
  · intro b ofs bt d hmap hp
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 delta b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      rw [scc085_alloc_contents_new m1 z0 sz1 m1' b1 halloc1 ofs]
      exact CompCert4Lean.Common.Memdata.memval_inject.undef j'
        (ZMap.get (zAdd ofs delta) (PMap.get b2 m2'.mem_contents))
    · change scc085_extend_inj j b1 b2 delta b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 delta b hb] at hmap
      have hpOld := scc085_alloc_perm_old_inv m1 z0 sz1 m1' b1 halloc1
        b ofs Cur Readable hb hp
      have hm := hinj.mi_inj.mi_memval b ofs bt d hmap hpOld
      have hm' := CompCert4Lean.Common.Memdata.memval_inject_incr
        j j'
        (ZMap.get ofs (PMap.get b m1.mem_contents))
        (ZMap.get (zAdd ofs d) (PMap.get bt m2.mem_contents)) hm hincr
      rw [scc085_alloc_contents_old m1 z0 sz1 m1' b1 halloc1 b ofs hb,
        scc085_alloc_contents_old m2 z0 sz2 m2' b2 halloc2 bt (zAdd ofs d)
          (htargetOld b bt d hmap)]
      exact hm'
  · intro b hvalid
    by_cases hb : b = b1
    · subst b
      exact False.elim (hvalid (scc085_alloc_valid_new m1 z0 sz1 m1' b1 halloc1))
    · change scc085_extend_inj j b1 b2 delta b = none
      rw [scc085_extend_inj_other j b1 b2 delta b hb]
      apply hinj.mi_freeblocks b
      intro hv
      apply hvalid
      change Plt b m1'.nextblock
      rw [scc085_alloc_nextblock m1 z0 sz1 m1' b1 halloc1]
      exact Plt_trans_succ b m1.nextblock hv
  · intro b bt d hmap
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 delta b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      exact scc085_alloc_valid_new m2 z0 sz2 m2' b2 halloc2
    · change scc085_extend_inj j b1 b2 delta b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 delta b hb] at hmap
      have hv := hinj.mi_mappedblocks b bt d hmap
      change Plt bt m2'.nextblock
      rw [scc085_alloc_nextblock m2 z0 sz2 m2' b2 halloc2]
      exact Plt_trans_succ bt m2.nextblock hv
  · intro a ta da b bt db oa ob hab hma hmb hpa hpb
    by_cases ha : a = b1
    · subst a
      have hb : b ≠ b1 := by exact fun h => hab h.symm
      change scc085_extend_inj j b1 b2 delta b1 = some (ta, da) at hma
      rw [scc085_extend_inj_same] at hma
      cases hma
      change scc085_extend_inj j b1 b2 delta b = some (bt, db) at hmb
      rw [scc085_extend_inj_other j b1 b2 delta b hb] at hmb
      exact Or.inl (fun h => htargetOld b bt db hmb h.symm)
    · by_cases hb : b = b1
      · subst b
        change scc085_extend_inj j b1 b2 delta b1 = some (bt, db) at hmb
        rw [scc085_extend_inj_same] at hmb
        cases hmb
        change scc085_extend_inj j b1 b2 delta a = some (ta, da) at hma
        rw [scc085_extend_inj_other j b1 b2 delta a ha] at hma
        exact Or.inl (htargetOld a ta da hma)
      · change scc085_extend_inj j b1 b2 delta a = some (ta, da) at hma
        rw [scc085_extend_inj_other j b1 b2 delta a ha] at hma
        change scc085_extend_inj j b1 b2 delta b = some (bt, db) at hmb
        rw [scc085_extend_inj_other j b1 b2 delta b hb] at hmb
        apply hinj.mi_no_overlap a ta da b bt db oa ob hab hma hmb
        · exact scc085_alloc_perm_old_inv m1 z0 sz1 m1' b1 halloc1
            a oa Max Nonempty ha hpa
        · exact scc085_alloc_perm_old_inv m1 z0 sz1 m1' b1 halloc1
            b ob Max Nonempty hb hpb
  · intro b bt d ofs hmap hp
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 delta b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      have hu0 : zLe z0 (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) := by
        have h := ofs.intrange.1
        change (-1 : Int) < intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) at h
        change (0 : Int) ≤ intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
        omega
      have hsrc :
          (zLe z0 (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) ∧
            zLt (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) sz1) ∨
          (zLe z0 (zSub (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) z1) ∧
            zLt (zSub (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) z1) sz1) := by
        rcases hp with hp | hp
        · exact Or.inl (scc085_alloc_perm_new_inv m1 z0 sz1 m1' b1 halloc1
            (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) Max Nonempty hp)
        · exact Or.inr (scc085_alloc_perm_new_inv m1 z0 sz1 m1' b1 halloc1
            (zSub (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) z1) Max Nonempty hp)
      have hbounds := scc085_alloc_representable_bounds sz1 sz2 hi delta
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) hsrc hu0 hhi hhisz hsz2 hdelta
      exact ⟨hdelta, hbounds.1, hbounds.2⟩
    · change scc085_extend_inj j b1 b2 delta b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 delta b hb] at hmap
      apply hinj.mi_representable b bt d ofs hmap
      rcases hp with hp | hp
      · exact Or.inl (scc085_alloc_perm_old_inv m1 z0 sz1 m1' b1 halloc1
          b (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) Max Nonempty hb hp)
      · exact Or.inr (scc085_alloc_perm_old_inv m1 z0 sz1 m1' b1 halloc1
          b (zSub (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) z1) Max Nonempty hb hp)
  · intro b ofs bt d k p hmap ht
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 delta b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      by_cases hs : Mem.perm m1' b1 ofs Max Nonempty
      · exact Or.inl (scc085_perm_of_freeable
          (scc085_alloc_perm_new m1 z0 sz1 m1' b1 halloc1 ofs k
            (scc085_alloc_perm_new_inv m1 z0 sz1 m1' b1 halloc1
              ofs Max Nonempty hs)))
      · exact Or.inr hs
    · change scc085_extend_inj j b1 b2 delta b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 delta b hb] at hmap
      have htOld := scc085_alloc_perm_old_inv m2 z0 sz2 m2' b2 halloc2
        bt (zAdd ofs d) k p (htargetOld b bt d hmap) ht
      rcases hinj.mi_perm_inv b ofs bt d k p hmap htOld with hs | hs
      · exact Or.inl (scc085_alloc_perm_old m1 z0 sz1 m1' b1 halloc1
          b ofs k p hb hs)
      · exact Or.inr (fun hp => hs (scc085_alloc_perm_old_inv m1 z0 sz1 m1'
          b1 halloc1 b ofs Max Nonempty hb hp))

private theorem scc085_globalenv_extend_alloc
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (j : meminj) (m2 m2' : mem)
    (b1 b2 : block) (delta sz2 : Z)
    (hge : (globalenv_inject ge j).m_pred m2)
    (hjnone : j b1 = none)
    (halloc2 : Mem.alloc m2 z0 sz2 = (m2', b2)) :
    (globalenv_inject ge (scc085_extend_inj j b1 b2 delta)).m_pred m2' := by
  rcases hge with ⟨bound, hbound, hpres⟩
  cases hpres with
  | globalenv_preserved_intro hdom himage hsym hfun hvar =>
      refine ⟨bound, ?_, globalenv_preserved_intro ?_ ?_ hsym hfun hvar⟩
      · rw [scc085_alloc_nextblock m2 z0 sz2 m2' b2 halloc2]
        exact Ple_trans bound m2.nextblock (PArith.BinPos.Pos.succ m2.nextblock)
          hbound (Ple_succ m2.nextblock)
      · intro b hlt
        by_cases hb : b = b1
        · subst b
          have hcontra := hdom b1 hlt
          rw [hjnone] at hcontra
          cases hcontra
        · rw [scc085_extend_inj_other j b1 b2 delta b hb]
          exact hdom b hlt
      · intro b bt d hmap hlt
        by_cases hb : b = b1
        · subst b
          rw [scc085_extend_inj_same] at hmap
          cases hmap
          have hb2 : Ple bound b2 := by
            rw [scc085_alloc_fresh m2 z0 sz2 m2' b2 halloc2]
            exact hbound
          exact False.elim ((Nat.not_lt_of_ge hb2) hlt)
        · rw [scc085_extend_inj_other j b1 b2 delta b hb] at hmap
          exact himage b bt d hmap hlt

private theorem scc085_minjection_central
    (j : meminj) (m1 m2 m1' m2' : mem) (sz1 sz2 : Z) (b1 b2 : block)
    (lo hi delta : Z) (hinj : Mem.inject j m1 m2)
    (halloc1 : Mem.alloc m1 z0 sz1 = (m1', b1))
    (halloc2 : Mem.alloc m2 z0 sz2 = (m2', b2))
    (hlo : lo = delta) (hhi : hi = zAdd delta (zMax z0 sz1))
    (b : block) (ofs : Z)
    (hfoot : (minjection (scc085_extend_inj j b1 b2 delta) m1').m_footprint b ofs)
    (hb : b = b2) : zLe lo ofs ∧ zLt ofs hi := by
  subst b
  rcases hfoot with ⟨src, d, hmap, hp⟩
  by_cases hs : src = b1
  · subst src
    rw [scc085_extend_inj_same] at hmap
    cases hmap
    have hsrc := scc085_alloc_perm_new_inv m1 z0 sz1 m1' b1 halloc1
      (zSub ofs delta) Max Nonempty hp
    have hsub : intOfZ (zSub ofs delta) = intOfZ ofs - intOfZ delta := by
      change intOfZ (zOfInt (intOfZ ofs - intOfZ delta)) = _
      rw [intOfZ_zOfInt]
    have hsz1 : (0 : Int) ≤ intOfZ sz1 := by
      have hslo := hsrc.1
      have hshi := hsrc.2
      change (0 : Int) ≤ intOfZ (zSub ofs delta) at hslo
      change intOfZ (zSub ofs delta) < intOfZ sz1 at hshi
      omega
    have hmax : intOfZ (zMax z0 sz1) = intOfZ sz1 := by
      simp [ZArith.BinInt.Z.max, (show intOfZ z0 = (0 : Int) by rfl), hsz1]
    have hloInt : intOfZ lo = intOfZ delta := congrArg intOfZ hlo
    have hhiInt : intOfZ hi = intOfZ delta + intOfZ sz1 := by
      rw [hhi]
      change intOfZ (zOfInt (intOfZ delta + intOfZ (zMax z0 sz1))) = _
      rw [intOfZ_zOfInt, hmax]
    constructor
    · change intOfZ lo ≤ intOfZ ofs
      have hslo := hsrc.1
      change (0 : Int) ≤ intOfZ (zSub ofs delta) at hslo
      omega
    · change intOfZ ofs < intOfZ hi
      have hshi := hsrc.2
      change intOfZ (zSub ofs delta) < intOfZ sz1 at hshi
      omega
  · rw [scc085_extend_inj_other j b1 b2 delta src hs] at hmap
    have hfresh2 : ¬ Mem.valid_block m2 b2 := by
      intro hv
      rw [scc085_alloc_fresh m2 z0 sz2 m2' b2 halloc2] at hv
      exact (Plt_ne _ _ hv) rfl
    exact False.elim (hfresh2 (hinj.mi_mappedblocks src b2 d hmap))

theorem alloc_parallel_rule_2 : alloc_parallel_rule_2Statement := by
  intro F V ge m1 sz1 m1' b1 m2 sz2 m2' b2 P j lo hi delta
    hsep halloc1 halloc2 hdiv hlo hhi hsz2 hdelta hhisz
  let j' := scc085_extend_inj j b1 b2 delta
  have hinj0 : Mem.inject j m1 m2 := hsep.1
  have hge0 : (globalenv_inject ge j).m_pred m2 := hsep.2.1.1
  have hP0 : P.m_pred m2 := hsep.2.1.2.1
  have hfresh1 : ¬ Mem.valid_block m1 b1 := by
    intro hv
    rw [scc085_alloc_fresh m1 z0 sz1 m1' b1 halloc1] at hv
    exact (Plt_ne _ _ hv) rfl
  have hfresh2 : ¬ Mem.valid_block m2 b2 := by
    intro hv
    rw [scc085_alloc_fresh m2 z0 sz2 m2' b2 halloc2] at hv
    exact (Plt_ne _ _ hv) rfl
  have hjnone : j b1 = none := hinj0.mi_freeblocks b1 hfresh1
  have hincr : CompCert4Lean.Common.Values.inject_incr j j' := by
    intro b bt d hmap
    by_cases hb : b = b1
    · subst b
      rw [hjnone] at hmap
      cases hmap
    · change scc085_extend_inj j b1 b2 delta b = some (bt, d)
      rw [scc085_extend_inj_other j b1 b2 delta b hb]
      exact hmap
  have hinj' : Mem.inject j' m1' m2' :=
    scc085_alloc_mapped_inject j m1 m2 m1' m2' sz1 sz2 b1 b2 hi delta
      hinj0 halloc1 halloc2 hdiv hhi hsz2.2 hdelta hhisz
  have hge' : (globalenv_inject ge j').m_pred m2' :=
    scc085_globalenv_extend_alloc F V ge j m2 m2' b1 b2 delta sz2
      hge0 hjnone halloc2
  have hP' : P.m_pred m2' := by
    apply P.m_invar m2 m2' hP0
    exact scc085_alloc_unchanged_on P.m_footprint m2 z0 sz2 m2' b2 halloc2
  have hgeP : disjoint_footprint (globalenv_inject ge j') P := by
    intro b ofs hgefoot hPfoot
    exact hgefoot
  have hPNoFresh : ∀ ofs, P.m_footprint b2 ofs → False := by
    intro ofs hPfoot
    exact hfresh2 (P.m_valid m2 b2 ofs hP0 hPfoot)
  have hminInner : disjoint_footprint (minjection j' m1')
      (sepconj (globalenv_inject ge j') P) := by
    intro b ofs hmin hinner
    cases hinner with
    | inl hgefoot => exact hgefoot
    | inr hPfoot =>
        rcases hmin with ⟨src, d, hmap, hp⟩
        by_cases hs : src = b1
        · subst src
          have hnew : j' b1 = some (b2, delta) := by
            change scc085_extend_inj j b1 b2 delta b1 = some (b2, delta)
            exact scc085_extend_inj_same j b1 b2 delta
          rw [hnew] at hmap
          cases hmap
          exact hPNoFresh ofs hPfoot
        · change scc085_extend_inj j b1 b2 delta src = some (b, d) at hmap
          rw [scc085_extend_inj_other j b1 b2 delta src hs] at hmap
          apply hsep.2.2 b ofs
          · refine ⟨src, d, hmap, ?_⟩
            exact scc085_alloc_perm_old_inv m1 z0 sz1 m1' b1 halloc1
              src (zSub ofs d) Max Nonempty hs hp
          · exact Or.inr hPfoot
  have hmaxNonneg : (0 : Int) ≤ intOfZ (zMax z0 sz1) := by
    by_cases hs : (0 : Int) ≤ intOfZ sz1 <;>
      simp [ZArith.BinInt.Z.max, (show intOfZ z0 = (0 : Int) by rfl), hs]
  have hlohi : zLe lo hi := by
    have hloInt : intOfZ lo = intOfZ delta := congrArg intOfZ hlo
    have hhiInt : intOfZ hi = intOfZ delta + intOfZ (zMax z0 sz1) := by
      rw [hhi]
      change intOfZ (zOfInt (intOfZ delta + intOfZ (zMax z0 sz1))) = _
      rw [intOfZ_zOfInt]
    change intOfZ lo ≤ intOfZ hi
    omega
  have hhiNonneg : zLe z0 hi := by
    have hhiInt : intOfZ hi = intOfZ delta + intOfZ (zMax z0 sz1) := by
      rw [hhi]
      change intOfZ (zOfInt (intOfZ delta + intOfZ (zMax z0 sz1))) = _
      rw [intOfZ_zOfInt]
    change (0 : Int) ≤ intOfZ delta at hdelta
    change (0 : Int) ≤ intOfZ hi
    omega
  have hszmod : zLe sz2 CompCert4Lean.Lib.Integers.Ptrofs.modulus := by
    have h := hsz2.2
    unfold CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned at h
    change intOfZ sz2 ≤
      intOfZ CompCert4Lean.Lib.Integers.Ptrofs.modulus - 1 at h
    change intOfZ sz2 ≤ intOfZ CompCert4Lean.Lib.Integers.Ptrofs.modulus
    omega
  have hloMod : zLe lo CompCert4Lean.Lib.Integers.Ptrofs.modulus := by
    change intOfZ lo ≤ intOfZ CompCert4Lean.Lib.Integers.Ptrofs.modulus
    change intOfZ lo ≤ intOfZ hi at hlohi
    change intOfZ hi ≤ intOfZ sz2 at hhisz
    change intOfZ sz2 ≤ intOfZ CompCert4Lean.Lib.Integers.Ptrofs.modulus at hszmod
    omega
  have hRangeLo : (range b2 z0 lo).m_pred m2' := by
    refine ⟨by exact Int.le_refl _, hloMod, ?_⟩
    intro i k p hibounds
    have hiSz : zLt i sz2 := by
      change intOfZ i < intOfZ sz2
      have hiLo := hibounds.2
      change intOfZ i < intOfZ lo at hiLo
      change intOfZ lo ≤ intOfZ hi at hlohi
      change intOfZ hi ≤ intOfZ sz2 at hhisz
      omega
    exact scc085_perm_of_freeable
      (scc085_alloc_perm_new m2 z0 sz2 m2' b2 halloc2 i k
        ⟨hibounds.1, hiSz⟩)
  have hRangeHi : (range b2 hi sz2).m_pred m2' := by
    refine ⟨hhiNonneg, hszmod, ?_⟩
    intro i k p hibounds
    have hi0 : zLe z0 i := by
      change (0 : Int) ≤ intOfZ i
      change (0 : Int) ≤ intOfZ hi at hhiNonneg
      have hboundLo := hibounds.1
      change intOfZ hi ≤ intOfZ i at hboundLo
      omega
    exact scc085_perm_of_freeable
      (scc085_alloc_perm_new m2 z0 sz2 m2' b2 halloc2 i k
        ⟨hi0, hibounds.2⟩)
  have hRangeHiInner : disjoint_footprint (range b2 hi sz2)
      (sepconj (minjection j' m1') (sepconj (globalenv_inject ge j') P)) := by
    intro b ofs hr hinner
    cases hinner with
    | inl hmin =>
        have hc := scc085_minjection_central j m1 m2 m1' m2' sz1 sz2 b1 b2
          lo hi delta hinj0 halloc1 halloc2 hlo hhi b ofs hmin hr.1
        have hrLo := hr.2.1
        have hcHi := hc.2
        change intOfZ hi ≤ intOfZ ofs at hrLo
        change intOfZ ofs < intOfZ hi at hcHi
        omega
    | inr hrest =>
        cases hrest with
        | inl hgefoot => exact hgefoot
        | inr hPfoot =>
            rw [hr.1] at hPfoot
            exact hPNoFresh ofs hPfoot
  have hRangeLoRest : disjoint_footprint (range b2 z0 lo)
      (sepconj (range b2 hi sz2)
        (sepconj (minjection j' m1') (sepconj (globalenv_inject ge j') P))) := by
    intro b ofs hr hrest
    cases hrest with
    | inl hhiFoot =>
        have hrHi := hr.2.2
        have hhiLo := hhiFoot.2.1
        change intOfZ ofs < intOfZ lo at hrHi
        change intOfZ hi ≤ intOfZ ofs at hhiLo
        change intOfZ lo ≤ intOfZ hi at hlohi
        omega
    | inr hinner =>
        cases hinner with
        | inl hmin =>
            have hc := scc085_minjection_central j m1 m2 m1' m2' sz1 sz2 b1 b2
              lo hi delta hinj0 halloc1 halloc2 hlo hhi b ofs hmin hr.1
            have hrHi := hr.2.2
            have hcLo := hc.1
            change intOfZ ofs < intOfZ lo at hrHi
            change intOfZ lo ≤ intOfZ ofs at hcLo
            omega
        | inr htail =>
            cases htail with
            | inl hgefoot => exact hgefoot
            | inr hPfoot =>
                rw [hr.1] at hPfoot
                exact hPNoFresh ofs hPfoot
  refine ⟨j', ?_, hincr, ?_⟩
  · exact ⟨hRangeLo,
      ⟨hRangeHi, ⟨hinj', ⟨hge', hP', hgeP⟩, hminInner⟩, hRangeHiInner⟩,
      hRangeLoRest⟩
  · exact scc085_extend_inj_same j b1 b2 delta

open Lean Elab Tactic Meta
open CompCert4Lean.Lib.Integers

private theorem scc085_ptrofs_unsigned_repr (z : Z)
    (hz : ZArith.BinInt.Z.le Z0 z ∧ ZArith.BinInt.Z.le z Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.repr z) = z := by
  have hzi : z = zOfInt (intOfZ z) := (zOfInt_intOfZ z).symm
  rw [hzi]
  change (CompCert4Lean.Lib.Integers.WordCore.repr Ptrofs.wordsize
      (zOfInt (intOfZ z))).intval = zOfInt (intOfZ z)
  let w := CompCert4Lean.Lib.Integers.WordCore.repr Ptrofs.wordsize
      (zOfInt (intOfZ z))
  have hi : w.val = (Int.toNat (intOfZ z % ((2 ^ Ptrofs.wordsize : Nat) : Int))) := by
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
  have hwi : w.intval = ZArith.BinInt.Z.of_nat w.val := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "WordCore.intval_eq_zOfNat_val")
        | throwError "frozen WordCore.intval_eq_zOfNat_val helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `w
      evalTactic (← `(tactic| exact $stx $arg))
  change w.intval = _
  rw [hwi, hi]
  have hznonneg : 0 ≤ intOfZ z := hz.1
  have hzmax := hz.2
  have hm : intOfZ Ptrofs.max_unsigned = (2 ^ Ptrofs.wordsize : Int) - 1 := by rfl
  have hzlt : intOfZ z < ((2 ^ Ptrofs.wordsize : Nat) : Int) := by
    change intOfZ z ≤ intOfZ Ptrofs.max_unsigned at hzmax
    rw [hm] at hzmax
    have hpcast : ((2 ^ Ptrofs.wordsize : Nat) : Int) = (2 : Int) ^ Ptrofs.wordsize := by
      exact (Int.natCast_pow 2 Ptrofs.wordsize).symm
    rw [hpcast]
    omega
  rw [Int.emod_eq_of_lt hznonneg hzlt]
  change zOfInt (↑(Int.toNat (intOfZ z)) : Int) = _
  rw [Int.toNat_of_nonneg hznonneg]

theorem loadv_rule : loadv_ruleStatement := by
  intro spec m chunk b ofs hpred
  have hbounds := contains_no_overflow spec m chunk b ofs hpred
  have hrepr := scc085_ptrofs_unsigned_repr ofs hbounds
  rw [Mem.loadv, hrepr]
  exact load_rule spec m chunk b ofs hpred

theorem minjection_obligation_1 : minjection_obligation_1Statement := by
  intro j m0 m m' hinj hunch
  exact (minjection j m0).m_invar m m' hinj hunch

theorem loadv_parallel_rule : loadv_parallel_ruleStatement := by
  intro j m1 m2 chunk addr1 v1 addr2 hinj hload hinject
  change Mem.inject j m1 m2 at hinj
  cases hinject with
  | inject_int i =>
      simp [Mem.loadv] at hload
  | inject_long i =>
      simp [Mem.loadv] at hload
  | inject_float f =>
      simp [Mem.loadv] at hload
  | inject_single f =>
      simp [Mem.loadv] at hload
  | val_inject_undef v =>
      simp [Mem.loadv] at hload
  | @inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      have hvalid := Mem.load_valid_access m1 chunk b1
        (Ptrofs.unsigned ofs1) v1 (by simpa [Mem.loadv] using hload)
      have hpmax : Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty :=
        permMaxNonemptyOfPerm (hvalid.1 (Ptrofs.unsigned ofs1) (by
          constructor
          · change intOfZ (Ptrofs.unsigned ofs1) ≤ intOfZ (Ptrofs.unsigned ofs1)
            omega
          · change intOfZ (Ptrofs.unsigned ofs1) <
              intOfZ (zAdd (Ptrofs.unsigned ofs1)
                (CompCert4Lean.Common.Memdata.size_chunk chunk))
            rw [chunkSpanInt]
            have hs := CompCert4Lean.Common.Memdata.size_chunk_pos chunk
            have hsize := CompCert4Lean.Common.Memdata.size_chunk_conv chunk
            have hsize' := congrArg intOfZ hsize
            have hsize'' : intOfZ (CompCert4Lean.Common.Memdata.size_chunk chunk) =
                Int.ofNat (CompCert4Lean.Common.Memdata.size_chunk_nat chunk) := by
              calc
                _ = intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                  (CompCert4Lean.Common.Memdata.size_chunk_nat chunk)) := hsize'
                _ = _ := by
                  change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
                    (Int.ofNat (CompCert4Lean.Common.Memdata.size_chunk_nat chunk))) = _
                  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
            change 0 < intOfZ (CompCert4Lean.Common.Memdata.size_chunk chunk) at hs
            rw [hsize''] at hs
            omega))
      have hrep := hinj.mi_representable b1 b2 delta
        ofs1 hmap (Or.inl hpmax)
      have haddr : Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
          zAdd (Ptrofs.unsigned ofs1) delta := by
        change Ptrofs.unsigned (Ptrofs.repr
          (zAdd (Ptrofs.unsigned ofs1) (Ptrofs.unsigned (Ptrofs.repr delta)))) = _
        have hdelta : zLe z0 delta := hrep.1
        have hofs0 : zLe z0 (Ptrofs.unsigned ofs1) := by
          have h := ofs1.intrange.1
          change (-1 : Int) < intOfZ (Ptrofs.unsigned ofs1) at h
          change (0 : Int) ≤ intOfZ (Ptrofs.unsigned ofs1)
          omega
        have hdeltaMax : zLe delta Ptrofs.max_unsigned := by
          change intOfZ delta ≤ intOfZ Ptrofs.max_unsigned
          have hsum := hrep.2.2
          change intOfZ (zAdd (Ptrofs.unsigned ofs1) delta) ≤
            intOfZ Ptrofs.max_unsigned at hsum
          change (0 : Int) ≤ intOfZ (Ptrofs.unsigned ofs1) at hofs0
          have hadd : intOfZ (zAdd (Ptrofs.unsigned ofs1) delta) =
              intOfZ (Ptrofs.unsigned ofs1) + intOfZ delta := by
            change intOfZ (zOfInt (intOfZ (Ptrofs.unsigned ofs1) + intOfZ delta)) = _
            rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          omega
        rw [scc085_ptrofs_unsigned_repr delta ⟨hdelta, hdeltaMax⟩]
        rw [scc085_ptrofs_unsigned_repr
          (zAdd (Ptrofs.unsigned ofs1) delta) ⟨hrep.2.1, hrep.2.2⟩]
      have hload' := Mem.load_inj j m1 m2 chunk b1
        (Ptrofs.unsigned ofs1) b2 delta v1 hinj.mi_inj
        (by simpa [Mem.loadv] using hload) hmap
      rcases hload' with ⟨v2, hv2, hinjv⟩
      refine ⟨v2, ?_, hinjv⟩
      simpa [Mem.loadv, hofs, haddr] using hv2

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem scc085_store_unchanged_on (P : massert)
    (chunk : AST.memory_chunk) (m : Memory.mem) (b : Values.block) (ofs : Z)
    (v : Values.val) (m' : Memory.mem)
    (hstore : Mem.store chunk m b ofs v = some m')
    (hout : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) →
      ¬ P.m_footprint b i) :
    Mem.unchanged_on P.m_footprint m m' := by
  have hnext := Mem.nextblock_store chunk m b ofs v m' hstore
  have hcontents := Mem.store_mem_contents chunk m b ofs v m' hstore
  refine {
    unchanged_on_nextblock := ?_,
    unchanged_on_perm := ?_,
    unchanged_on_contents := ?_ }
  · change Ple m.nextblock m'.nextblock
    rw [hnext]
    exact Ple_refl _
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
      have hget : PMap.get b (PMap.set b
          (Mem.setN (encode_val chunk v) ofs (PMap.get b m.mem_contents))
          m.mem_contents) =
          Mem.setN (encode_val chunk v) ofs (PMap.get b m.mem_contents) := by
        exact scc085_pmap_get_set_same b _ m.mem_contents
      rw [hget]
      apply Mem.setN_other
      intro i hi heq
      subst i
      apply hout ofs'
      have hlen := CompCert4Lean.Common.Memdata.encode_val_length chunk v
      have hi' := hi
      rw [hlen] at hi'
      have hsize' : ZArith.BinInt.Z.of_nat (size_chunk_nat chunk) = size_chunk chunk :=
        (CompCert4Lean.Common.Memdata.size_chunk_conv chunk).symm
      simpa [hsize'] using hi'
      exact hP
    · rw [scc085_pmap_get_set_other _ _ _ _ hb]

private theorem scc085_store_injection_transport
    (f : meminj) (chunk : AST.memory_chunk)
    (m1 m1' m2 m2' : Memory.mem)
    (sb1 sb2 : Values.block) (sofs1 sofs2 : Z)
    (v1 v2 : Values.val)
    (hinj : Mem.inject f m1 m2)
    (hstore1 : Mem.store chunk m1 sb1 sofs1 v1 = some m1')
    (hstore2 : Mem.store chunk m2 sb2 sofs2 v2 = some m2')
    (hmem : Mem.mem_inj f m1' m2') : Mem.inject f m1' m2' := by
  refine {
    mi_inj := hmem,
    mi_freeblocks := ?_,
    mi_mappedblocks := ?_,
    mi_no_overlap := ?_,
    mi_representable := ?_,
    mi_perm_inv := ?_ }
  · intro b hb
    change ¬ Plt b m1'.nextblock at hb
    apply hinj.mi_freeblocks b
    intro hb1
    apply hb
    rw [Mem.nextblock_store chunk m1 sb1 sofs1 v1 m1' hstore1]
    exact hb1
  · intro b b' delta hmap
    apply Mem.store_valid_block_1 chunk m2 sb2 sofs2 v2 m2' hstore2
    exact hinj.mi_mappedblocks b b' delta hmap
  · intro b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne hmap1 hmap2 hp1 hp2
    apply hinj.mi_no_overlap b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne hmap1 hmap2
    · exact Mem.perm_store_2 chunk m1 sb1 sofs1 v1 m1' hstore1 b1 ofs1 Max Nonempty hp1
    · exact Mem.perm_store_2 chunk m1 sb1 sofs1 v1 m1' hstore1 b2 ofs2 Max Nonempty hp2
  · intro b b' delta ofs hmap hp
    apply hinj.mi_representable b b' delta ofs hmap
    rcases hp with hp | hp
    · exact Or.inl (Mem.perm_store_2 chunk m1 sb1 sofs1 v1 m1' hstore1
        b (Ptrofs.unsigned ofs) Max Nonempty hp)
    · exact Or.inr (Mem.perm_store_2 chunk m1 sb1 sofs1 v1 m1' hstore1
        b (zSub (Ptrofs.unsigned ofs) z1) Max Nonempty hp)
  · intro b ofs b' delta k p hmap hp
    obtain hp2 := Mem.perm_store_2 chunk m2 sb2 sofs2 v2 m2' hstore2
      b' (zAdd ofs delta) k p hp
    obtain hp1 | hn := hinj.mi_perm_inv b ofs b' delta k p hmap hp2
    · exact Or.inl (Mem.perm_store_1 chunk m1 sb1 sofs1 v1 m1' hstore1 b ofs k p hp1)
    · exact Or.inr (fun hp1' => hn
        (Mem.perm_store_2 chunk m1 sb1 sofs1 v1 m1' hstore1 b ofs Max Nonempty hp1'))

 theorem storev_parallel_rule : storev_parallel_ruleStatement := by
  intro j m1 m2 P chunk addr1 v1 m1' addr2 v2 hpred hstore haddrinj hv
  rcases hpred with ⟨hinj, hP, hdisj⟩
  change Mem.inject j m1 m2 at hinj
  cases haddrinj with
  | inject_int i =>
      simp [Mem.storev] at hstore
  | inject_long i =>
      simp [Mem.storev] at hstore
  | inject_float f =>
      simp [Mem.storev] at hstore
  | inject_single f =>
      simp [Mem.storev] at hstore
  | val_inject_undef v =>
      simp [Mem.storev] at hstore
  | @inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      have hsrcstore : Mem.store chunk m1 b1 (Ptrofs.unsigned ofs1) v1 = some m1' := by
        simpa [Mem.storev] using hstore
      have hvalid1 : Mem.valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Writable :=
        Mem.store_valid_access_3 chunk m1 b1 (Ptrofs.unsigned ofs1) v1 m1' hsrcstore
      have hofs_lt : zLt (Ptrofs.unsigned ofs1)
          (zAdd (Ptrofs.unsigned ofs1) (size_chunk chunk)) := by
        have hs := CompCert4Lean.Common.Memdata.size_chunk_pos chunk
        have hadd (x y : Z) : intOfZ (zAdd x y) = intOfZ x + intOfZ y := by
          change intOfZ (zOfInt (intOfZ x + intOfZ y)) = _
          rw [intOfZ_zOfInt]
        change intOfZ (Ptrofs.unsigned ofs1) <
          intOfZ (zAdd (Ptrofs.unsigned ofs1) (size_chunk chunk))
        rw [hadd]
        change (0 : Int) < intOfZ (size_chunk chunk) at hs
        omega
      have hpstore : Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty := by
        apply Mem.perm_implies m1 b1 (Ptrofs.unsigned ofs1) Max Writable Nonempty
          (Mem.perm_cur_max m1 b1 (Ptrofs.unsigned ofs1) Writable
            (hvalid1.1 (Ptrofs.unsigned ofs1)
              ⟨by change intOfZ (Ptrofs.unsigned ofs1) ≤ intOfZ (Ptrofs.unsigned ofs1); omega,
               hofs_lt⟩))
          (perm_any_N Writable)
      have hrep := hinj.mi_representable b1 b2 delta ofs1 hmap
        (Or.inl hpstore)
      have haddr : Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
          zAdd (Ptrofs.unsigned ofs1) delta := by
        change Ptrofs.unsigned (Ptrofs.repr
          (zAdd (Ptrofs.unsigned ofs1) (Ptrofs.unsigned (Ptrofs.repr delta)))) = _
        have hdelta : zLe z0 delta := hrep.1
        have hofs0 : zLe z0 (Ptrofs.unsigned ofs1) := by
          have h := ofs1.intrange.1
          change (-1 : Int) < intOfZ (Ptrofs.unsigned ofs1) at h
          change (0 : Int) ≤ intOfZ (Ptrofs.unsigned ofs1)
          omega
        have hdeltaMax : zLe delta Ptrofs.max_unsigned := by
          change intOfZ delta ≤ intOfZ Ptrofs.max_unsigned
          have hsum := hrep.2.2
          change intOfZ (zAdd (Ptrofs.unsigned ofs1) delta) ≤
            intOfZ Ptrofs.max_unsigned at hsum
          change (0 : Int) ≤ intOfZ (Ptrofs.unsigned ofs1) at hofs0
          have hadd : intOfZ (zAdd (Ptrofs.unsigned ofs1) delta) =
              intOfZ (Ptrofs.unsigned ofs1) + intOfZ delta := by
            change intOfZ (zOfInt (intOfZ (Ptrofs.unsigned ofs1) + intOfZ delta)) = _
            rw [intOfZ_zOfInt]
          omega
        rw [scc085_ptrofs_unsigned_repr delta ⟨hdelta, hdeltaMax⟩]
        rw [scc085_ptrofs_unsigned_repr
          (zAdd (Ptrofs.unsigned ofs1) delta) ⟨hrep.2.1, hrep.2.2⟩]
      rcases Mem.store_mapped_inj j chunk m1 b1 (Ptrofs.unsigned ofs1) v1 m1'
          m2 b2 delta v2 hinj.mi_inj hsrcstore hinj.mi_no_overlap hmap hv with
        ⟨m2', hstore2, hinj2⟩
      have hout : ∀ i, zLe (zAdd (Ptrofs.unsigned ofs1) delta) i ∧
          zLt i (zAdd (zAdd (Ptrofs.unsigned ofs1) delta) (size_chunk chunk)) →
          ¬ P.m_footprint b2 i := by
        intro i hi hPi
        have intOfZ_zsub_local (x y : Z) :
            intOfZ (zSub x y) = intOfZ x - intOfZ y := by
          change intOfZ (zOfInt (intOfZ x - intOfZ y)) = _
          rw [intOfZ_zOfInt]
        have hsrcRange : zLe (Ptrofs.unsigned ofs1) (zSub i delta) ∧
            zLt (zSub i delta)
              (zAdd (Ptrofs.unsigned ofs1) (size_chunk chunk)) := by
          have hi1 := hi.1
          change intOfZ (zAdd (Ptrofs.unsigned ofs1) delta) ≤ intOfZ i at hi1
          have hi2 := hi.2
          change intOfZ i <
            intOfZ (zAdd (zAdd (Ptrofs.unsigned ofs1) delta) (size_chunk chunk)) at hi2
          change intOfZ (Ptrofs.unsigned ofs1) ≤ intOfZ (zSub i delta) ∧
            intOfZ (zSub i delta) <
              intOfZ (zAdd (Ptrofs.unsigned ofs1) (size_chunk chunk))
          simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
            intOfZ_zOfInt] at hi1 hi2 ⊢
          omega
        have hpq := hvalid1.1 (zSub i delta) hsrcRange
        have hpq' : Mem.perm m1 b1 (zSub i delta) Max Nonempty := by
          exact Mem.perm_implies m1 b1 (zSub i delta) Max Writable Nonempty
            (Mem.perm_cur_max m1 b1 (zSub i delta) Writable hpq) (perm_any_N Writable)
        have hfoot : (minjection j m1).m_footprint b2 i :=
          ⟨b1, delta, hmap, hpq'⟩
        exact hdisj b2 i hfoot hPi
      have hinjFinal : Mem.inject j m1' m2' :=
        scc085_store_injection_transport j chunk m1 m1' m2 m2'
          b1 b2 (Ptrofs.unsigned ofs1)
          (zAdd (Ptrofs.unsigned ofs1) delta) v1 v2 hinj
          hsrcstore hstore2 hinj2
      have hP' : P.m_pred m2' :=
        P.m_invar m2 m2' hP
          (scc085_store_unchanged_on P chunk m2 b2
            (zAdd (Ptrofs.unsigned ofs1) delta) v2 m2' hstore2 hout)
      have hdisj' : disjoint_footprint (minjection j m1') P := by
        intro b ofs hfoot hPfoot
        rcases hfoot with ⟨b0, delta0, hmap0, hp⟩
        apply hdisj b ofs
        · exact ⟨b0, delta0, hmap0,
            Mem.perm_store_2 chunk m1 b1 (Ptrofs.unsigned ofs1) v1 m1'
              hsrcstore b0 (zSub ofs delta0) Max Nonempty hp⟩
        · exact hPfoot
      refine ⟨m2', ?_, ?_⟩
      · simpa [Mem.storev, hofs, haddr] using hstore2
      · exact ⟨hinjFinal, hP', hdisj'⟩

theorem alloc_parallel_rule : alloc_parallel_ruleStatement := by
  intro m1 sz1 m1' b1 m2 sz2 m2' b2 P j lo hi delta
    hsep halloc1 halloc2 hdiv hlo hhi hsz2 hdelta hhisz
  let j' := scc085_extend_inj j b1 b2 delta
  have hinj0 : Mem.inject j m1 m2 := hsep.1
  have hP0 : P.m_pred m2 := hsep.2.1
  have hfresh1 : ¬ Mem.valid_block m1 b1 := by
    intro hv
    rw [scc085_alloc_fresh m1 z0 sz1 m1' b1 halloc1] at hv
    exact (Plt_ne _ _ hv) rfl
  have hfresh2 : ¬ Mem.valid_block m2 b2 := by
    intro hv
    rw [scc085_alloc_fresh m2 z0 sz2 m2' b2 halloc2] at hv
    exact (Plt_ne _ _ hv) rfl
  have hjnone : j b1 = none := hinj0.mi_freeblocks b1 hfresh1
  have hincr : CompCert4Lean.Common.Values.inject_incr j j' := by
    intro b bt d hmap
    by_cases hb : b = b1
    · subst b
      rw [hjnone] at hmap
      cases hmap
    · change scc085_extend_inj j b1 b2 delta b = some (bt, d)
      rw [scc085_extend_inj_other j b1 b2 delta b hb]
      exact hmap
  have hinj' : Mem.inject j' m1' m2' :=
    scc085_alloc_mapped_inject j m1 m2 m1' m2' sz1 sz2 b1 b2 hi delta
      hinj0 halloc1 halloc2 hdiv hhi hsz2.2 hdelta hhisz
  have hP' : P.m_pred m2' := by
    apply P.m_invar m2 m2' hP0
    exact scc085_alloc_unchanged_on P.m_footprint m2 z0 sz2 m2' b2 halloc2
  have hPNoFresh : ∀ ofs, P.m_footprint b2 ofs → False := by
    intro ofs hPfoot
    exact hfresh2 (P.m_valid m2 b2 ofs hP0 hPfoot)
  have hminP : disjoint_footprint (minjection j' m1') P := by
    intro b ofs hmin hPfoot
    rcases hmin with ⟨src, d, hmap, hp⟩
    by_cases hs : src = b1
    · subst src
      have hnew : j' b1 = some (b2, delta) :=
        scc085_extend_inj_same j b1 b2 delta
      rw [hnew] at hmap
      cases hmap
      exact hPNoFresh ofs hPfoot
    · change scc085_extend_inj j b1 b2 delta src = some (b, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 delta src hs] at hmap
      apply hsep.2.2 b ofs
      · refine ⟨src, d, hmap, ?_⟩
        exact scc085_alloc_perm_old_inv m1 z0 sz1 m1' b1 halloc1
          src (zSub ofs d) Max Nonempty hs hp
      · exact hPfoot
  have hmaxNonneg : (0 : Int) ≤ intOfZ (zMax z0 sz1) := by
    by_cases hs : (0 : Int) ≤ intOfZ sz1 <;>
      simp [ZArith.BinInt.Z.max, (show intOfZ z0 = (0 : Int) by rfl), hs]
  have hlohi : zLe lo hi := by
    have hloInt : intOfZ lo = intOfZ delta := congrArg intOfZ hlo
    have hhiInt : intOfZ hi = intOfZ delta + intOfZ (zMax z0 sz1) := by
      rw [hhi]
      change intOfZ (zOfInt (intOfZ delta + intOfZ (zMax z0 sz1))) = _
      rw [intOfZ_zOfInt]
    change intOfZ lo ≤ intOfZ hi
    omega
  have hhiNonneg : zLe z0 hi := by
    have hhiInt : intOfZ hi = intOfZ delta + intOfZ (zMax z0 sz1) := by
      rw [hhi]
      change intOfZ (zOfInt (intOfZ delta + intOfZ (zMax z0 sz1))) = _
      rw [intOfZ_zOfInt]
    change (0 : Int) ≤ intOfZ delta at hdelta
    change (0 : Int) ≤ intOfZ hi
    omega
  have hszmod : zLe sz2 CompCert4Lean.Lib.Integers.Ptrofs.modulus := by
    have h := hsz2.2
    unfold CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned at h
    change intOfZ sz2 ≤
      intOfZ CompCert4Lean.Lib.Integers.Ptrofs.modulus - 1 at h
    change intOfZ sz2 ≤ intOfZ CompCert4Lean.Lib.Integers.Ptrofs.modulus
    omega
  have hloMod : zLe lo CompCert4Lean.Lib.Integers.Ptrofs.modulus := by
    change intOfZ lo ≤ intOfZ CompCert4Lean.Lib.Integers.Ptrofs.modulus
    change intOfZ lo ≤ intOfZ hi at hlohi
    change intOfZ hi ≤ intOfZ sz2 at hhisz
    change intOfZ sz2 ≤ intOfZ CompCert4Lean.Lib.Integers.Ptrofs.modulus at hszmod
    omega
  have hRangeLo : (range b2 z0 lo).m_pred m2' := by
    refine ⟨by exact Int.le_refl _, hloMod, ?_⟩
    intro i k p hibounds
    have hiSz : zLt i sz2 := by
      change intOfZ i < intOfZ sz2
      have hiLo := hibounds.2
      change intOfZ i < intOfZ lo at hiLo
      change intOfZ lo ≤ intOfZ hi at hlohi
      change intOfZ hi ≤ intOfZ sz2 at hhisz
      omega
    exact scc085_perm_of_freeable
      (scc085_alloc_perm_new m2 z0 sz2 m2' b2 halloc2 i k
        ⟨hibounds.1, hiSz⟩)
  have hRangeHi : (range b2 hi sz2).m_pred m2' := by
    refine ⟨hhiNonneg, hszmod, ?_⟩
    intro i k p hibounds
    have hi0 : zLe z0 i := by
      change (0 : Int) ≤ intOfZ i
      change (0 : Int) ≤ intOfZ hi at hhiNonneg
      have hboundLo := hibounds.1
      change intOfZ hi ≤ intOfZ i at hboundLo
      omega
    exact scc085_perm_of_freeable
      (scc085_alloc_perm_new m2 z0 sz2 m2' b2 halloc2 i k
        ⟨hi0, hibounds.2⟩)
  have hRangeHiInner : disjoint_footprint (range b2 hi sz2)
      (sepconj (minjection j' m1') P) := by
    intro b ofs hr hinner
    cases hinner with
    | inl hmin =>
        have hc := scc085_minjection_central j m1 m2 m1' m2' sz1 sz2 b1 b2
          lo hi delta hinj0 halloc1 halloc2 hlo hhi b ofs hmin hr.1
        have hrLo := hr.2.1
        have hcHi := hc.2
        change intOfZ hi ≤ intOfZ ofs at hrLo
        change intOfZ ofs < intOfZ hi at hcHi
        omega
    | inr hPfoot =>
        rw [hr.1] at hPfoot
        exact hPNoFresh ofs hPfoot
  have hRangeLoRest : disjoint_footprint (range b2 z0 lo)
      (sepconj (range b2 hi sz2) (sepconj (minjection j' m1') P)) := by
    intro b ofs hr hrest
    cases hrest with
    | inl hhiFoot =>
        have hrHi := hr.2.2
        have hhiLo := hhiFoot.2.1
        change intOfZ ofs < intOfZ lo at hrHi
        change intOfZ hi ≤ intOfZ ofs at hhiLo
        change intOfZ lo ≤ intOfZ hi at hlohi
        omega
    | inr hinner =>
        cases hinner with
        | inl hmin =>
            have hc := scc085_minjection_central j m1 m2 m1' m2' sz1 sz2 b1 b2
              lo hi delta hinj0 halloc1 halloc2 hlo hhi b ofs hmin hr.1
            have hrHi := hr.2.2
            have hcLo := hc.1
            change intOfZ ofs < intOfZ lo at hrHi
            change intOfZ lo ≤ intOfZ ofs at hcLo
            omega
        | inr hPfoot =>
            rw [hr.1] at hPfoot
            exact hPNoFresh ofs hPfoot
  refine ⟨j', ?_, hincr, scc085_extend_inj_same j b1 b2 delta, ?_⟩
  · exact ⟨hRangeLo, ⟨hRangeHi, ⟨hinj', hP', hminP⟩, hRangeHiInner⟩,
      hRangeLoRest⟩
  · intro b hb
    exact scc085_extend_inj_other j b1 b2 delta b hb


theorem globalenv_inject_obligation_2 : globalenv_inject_obligation_2Statement := by
  intro F V ge j m b hpred hfalse
  exact False.elim hfalse

theorem globalenv_inject_preserves_globals : globalenv_inject_preserves_globalsStatement := by
  intro F V ge j m hpred
  rcases hpred with ⟨bound, hbound, hge⟩
  cases hge with
  | globalenv_preserved_intro hdom himg hsym hfun hvar =>
      refine ⟨?_, ?_, ?_⟩
      · intro id b hfind
        exact hdom b (hsym id b hfind)
      · intro b gv hfind
        exact hdom b (hvar b gv hfind)
      · intro b1 b2 delta gv hfind hmap
        exact (himg b1 b2 delta hmap (hvar b2 gv hfind)).symm


theorem globalenv_inject_incr : globalenv_inject_incrStatement := by
  intro j m0 F V ge m j' P hincr hseparate hsep
  have hglobal : (globalenv_inject ge j).m_pred m := hsep.1
  have hP : P.m_pred m := hsep.2.1
  have hdisj : disjoint_footprint (globalenv_inject ge j) P := hsep.2.2
  rcases hglobal with ⟨bound, hbound, hpres⟩
  cases hpres with
  | globalenv_preserved_intro hdom himage hsym hfun hvar =>
      refine ⟨⟨bound, hbound, globalenv_preserved_intro ?_ ?_ hsym hfun hvar⟩, hP, ?_⟩
      · intro b hlt
        exact hincr b b z0 (hdom b hlt)
      · intro b1 b2 delta hmap hlt
        by_cases hb : j b1 = none
        · have hsep' := hseparate b1 b2 delta hb hmap
          have hvalid : Mem.valid_block m b2 := by
            unfold Mem.valid_block
            exact CompCert4Lean.Lib.Coqlib.Plt_Ple_trans b2 bound m.nextblock hlt hbound
          exact False.elim (hsep'.2 hvalid)
        · cases hJ : j b1 with
          | none => exact (hb hJ).elim
          | some x =>
              rcases x with ⟨b0, d0⟩
              have hinc := hincr b1 b0 d0 hJ
              have heq : some (b0, d0) = some (b2, delta) := hinc.symm.trans hmap
              have htarget : b0 = b2 := by
                exact congrArg Prod.fst (Option.some.inj heq)
              have hlt0 : Plt b0 bound := by
                simpa [htarget] using hlt
              exact (himage b1 b0 d0 hJ hlt0).trans htarget
      · exact hdisj

section ExternalCallParallelProof

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Builtins0
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers

private theorem scc085_call_max_perm
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) :
    Events.external_call_max_perm xi ef := by
  cases ef with
  | EF_external name sg =>
      exact (external_functions_properties xi name sg).ec_max_perm
  | EF_builtin name sg | EF_runtime name sg =>
      unfold Events.external_call_max_perm Events.external_call builtin_or_external_sem
      cases hlookup : lookup_builtin_function name sg with
      | none => simpa only [hlookup] using (external_functions_properties xi name sg).ec_max_perm
      | some bf => simpa only [hlookup] using (known_builtin_ok bf).ec_max_perm
  | EF_vload chunk => exact (volatile_load_ok chunk).ec_max_perm
  | EF_vstore chunk => exact (volatile_store_ok chunk).ec_max_perm
  | EF_malloc =>
      intro ge vargs m1 t vres m2 b ofs p hcall hb hp
      cases hcall with
      | extcall_malloc_sem_intro sz m ma fresh mf halloc hstore =>
          apply scc085_alloc_perm_old_inv _ _ _ ma fresh halloc b ofs Max p
          · intro heq
            subst b
            exact Mem.fresh_block_alloc _ _ _ ma fresh halloc hb
          · exact Mem.perm_store_2 Mptr ma fresh _ (Vptrofs sz) _ hstore
              b ofs Max p hp
  | EF_free =>
      intro ge vargs m1 t vres m2 b ofs p hcall hb hp
      cases hcall with
      | extcall_free_sem_ptr b0 lo sz m mf hload hfree =>
          exact scc085_perm_of_free _ _ b0 _ _ hfree b ofs Max p hp
      | extcall_free_sem_null => exact hp
  | EF_memcpy sz al =>
      intro ge vargs m1 t vres m2 b ofs p hcall hb hp
      cases hcall with
      | extcall_memcpy_sem_intro bd od bs os m bytes mf ha hs hal has had hn hl hst =>
          exact Mem.perm_storebytes_2 _ bd (Ptrofs.unsigned od) bytes _ hst
            b ofs Max p hp
  | EF_annot kind text targs => exact (extcall_annot_ok text targs).ec_max_perm
  | EF_annot_val kind text targ =>
      intro ge vargs m1 t vres m2 b ofs p hcall hb hp
      cases hcall
      exact hp
  | EF_inline_asm text sg clobbers =>
      exact (inline_assembly_properties xi text sg).ec_max_perm
  | EF_debug kind text targs => exact (extcall_debug_ok targs).ec_max_perm

private theorem scc085_call_frame (F V : Type) (ge : Genv.t F V)
    (j j' : meminj) (m1 m1' m2 m2' : mem) (P : massert)
    (hsep : (sepconj (minjection j m1)
      (sepconj (globalenv_inject ge j) P)).m_pred m2)
    (hinj : Mem.inject j' m1' m2')
    (hunch : Mem.unchanged_on (loc_out_of_reach j m1) m2 m2')
    (hincr : inject_incr j j')
    (hseparate : inject_separated j j' m1 m2)
    (hmax : ∀ b ofs p, Mem.valid_block m1 b →
      Mem.perm m1' b ofs Max p → Mem.perm m1 b ofs Max p) :
    (sepconj (minjection j' m1')
      (sepconj (globalenv_inject ge j') P)).m_pred m2' := by
  have hrest := globalenv_inject_incr j m1 F V ge m2 j' P hincr hseparate hsep.2.1
  refine ⟨hinj, ?_, ?_⟩
  · apply (sepconj (globalenv_inject ge j') P).m_invar m2 m2' hrest
    apply unchangedOnRestrict (Q := loc_out_of_reach j m1) _ hunch
    intro b ofs hfoot b0 delta hmap hp
    have hfoot0 : (sepconj (globalenv_inject ge j) P).m_footprint b ofs := hfoot
    exact hsep.2.2 b ofs ⟨b0, delta, hmap, hp⟩ hfoot0
  · intro b ofs hmin hfoot
    rcases hmin with ⟨b0, delta, hmap', hp'⟩
    cases hj : j b0 with
    | none =>
        exact (hseparate b0 b delta hj hmap').2
          ((sepconj (globalenv_inject ge j) P).m_valid m2 b ofs hsep.2.1 hfoot)
    | some target =>
        rcases target with ⟨bt, dt⟩
        have heq := Option.some.inj ((hincr b0 bt dt hj).symm.trans hmap')
        cases heq
        have hb : Mem.valid_block m1 b0 := by
          by_cases hv : Mem.valid_block m1 b0
          · exact hv
          · have hnmap := hsep.1.mi_freeblocks b0 hv
            rw [hj] at hnmap
            cases hnmap
        exact hsep.2.2 b ofs ⟨b0, delta, hj, hmax b0 _ Nonempty hb hp'⟩ hfoot

private theorem scc085_symbols_inject (F V : Type) (ge : Genv.t F V)
    (j : meminj) (m : mem) (hge : (globalenv_inject ge j).m_pred m) :
    symbols_inject j (Genv.to_senv ge) (Genv.to_senv ge) := by
  have hglob := globalenv_inject_preserves_globals F V ge j m hge
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro id b1 b2 delta hmap hfind
    have heq := Option.some.inj ((hglob.1 id b1 hfind).symm.trans hmap)
    cases heq
    exact ⟨rfl, hfind⟩
  · intro id b hpublic hfind
    exact ⟨b, hglob.1 id b hfind, hfind⟩
  · intro b1 b2 delta hmap
    change Genv.block_is_volatile ge b2 = Genv.block_is_volatile ge b1
    unfold Genv.block_is_volatile
    cases hv1 : Genv.find_var_info ge b1 with
    | some gv =>
        have heq := Option.some.inj ((hglob.2.1 b1 gv hv1).symm.trans hmap)
        cases heq
        simp only [hv1]
    | none =>
        cases hv2 : Genv.find_var_info ge b2 with
        | none => rfl
        | some gv =>
            have heq := hglob.2.2 b1 b2 delta gv hv2 hmap
            subst b2
            rw [hv1] at hv2
            cases hv2

private theorem scc085_zadd_zero (x : Z) : zAdd x z0 = x := by
  apply intOfZ_injective
  simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  change intOfZ x + 0 = intOfZ x
  omega

private theorem scc085_unchanged_refl (Q : block → Z → Prop) (m : mem) :
    Mem.unchanged_on Q m m := by
  exact ⟨Ple_refl _, fun _ _ _ _ _ _ => Iff.rfl, fun _ _ _ _ => rfl⟩

private theorem scc085_unchanged_trans (Q : block → Z → Prop) (m m' m'' : mem)
    (h1 : Mem.unchanged_on Q m m') (h2 : Mem.unchanged_on Q m' m'') :
    Mem.unchanged_on Q m m'' := by
  refine ⟨Ple_trans _ _ _ h1.1 h2.1, ?_, ?_⟩
  · intro b ofs k p hq hb
    exact (h1.2 b ofs k p hq hb).trans
      (h2.2 b ofs k p hq (Plt_Ple_trans _ _ _ hb h1.1))
  · intro b ofs hq hp
    rw [h2.3 b ofs hq ((h1.2 b ofs Cur Readable hq (validBlockOfPerm hp)).mp hp)]
    exact h1.3 b ofs hq hp

private theorem scc085_address_inject (j : meminj) (m1 m2 : mem)
    (b1 b2 : block) (ofs : Ptrofs.int) (delta : Z)
    (hinj : Mem.inject j m1 m2) (hmap : j b1 = some (b2, delta))
    (hp : Mem.perm m1 b1 (Ptrofs.unsigned ofs) Max Nonempty ∨
      Mem.perm m1 b1 (zSub (Ptrofs.unsigned ofs) z1) Max Nonempty) :
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) =
      zAdd (Ptrofs.unsigned ofs) delta := by
  obtain ⟨hdelta, hsum⟩ := hinj.mi_representable b1 b2 delta ofs hmap hp
  have hu : 0 ≤ intOfZ (Ptrofs.unsigned ofs) := by
    have h := ofs.intrange.1
    change (-1 : _root_.Int) < intOfZ (Ptrofs.unsigned ofs) at h
    omega
  have hdmax : zLe delta Ptrofs.max_unsigned := by
    have h := hsum.2
    change intOfZ (zAdd (Ptrofs.unsigned ofs) delta) ≤ intOfZ Ptrofs.max_unsigned at h
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at h
    change intOfZ delta ≤ intOfZ Ptrofs.max_unsigned
    omega
  change Ptrofs.unsigned (Ptrofs.repr
    (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))) = _
  rw [scc085_ptrofs_unsigned_repr delta ⟨hdelta, hdmax⟩]
  exact scc085_ptrofs_unsigned_repr _ hsum

private theorem scc085_alloc_same_bounds_inject
    (j : meminj) (m1 m2 m1' m2' : mem) (lo hi : Z) (b1 b2 : block) (hinj : Mem.inject j m1 m2)
    (halloc1 : Mem.alloc m1 lo hi = (m1', b1))
    (halloc2 : Mem.alloc m2 lo hi = (m2', b2))
 :
    Mem.inject (scc085_extend_inj j b1 b2 z0) m1' m2' := by
  let j' := scc085_extend_inj j b1 b2 z0
  have hfresh1 : ¬ Mem.valid_block m1 b1 := by
    intro hv
    rw [scc085_alloc_fresh m1 lo hi m1' b1 halloc1] at hv
    exact (Plt_ne _ _ hv) rfl
  have hfresh2 : ¬ Mem.valid_block m2 b2 := by
    intro hv
    rw [scc085_alloc_fresh m2 lo hi m2' b2 halloc2] at hv
    exact (Plt_ne _ _ hv) rfl
  have hjnone : j b1 = none := hinj.mi_freeblocks b1 hfresh1
  have hincr : CompCert4Lean.Common.Values.inject_incr j j' := by
    intro b bt d hmap
    by_cases hb : b = b1
    · subst b
      rw [hjnone] at hmap
      cases hmap
    · change scc085_extend_inj j b1 b2 z0 b = some (bt, d)
      rw [scc085_extend_inj_other j b1 b2 z0 b hb]
      exact hmap
  have hsourceOld : ∀ b bt d, j b = some (bt, d) → b ≠ b1 := by
    intro b bt d hmap hb
    subst b
    rw [hjnone] at hmap
    cases hmap
  have htargetOld : ∀ b bt d, j b = some (bt, d) → bt ≠ b2 := by
    intro b bt d hmap hbt
    subst bt
    exact hfresh2 (hinj.mi_mappedblocks b b2 d hmap)
  change Mem.inject j' m1' m2'
  refine {
    mi_inj := {
      mi_perm := ?_,
      mi_align := ?_,
      mi_memval := ?_
    },
    mi_freeblocks := ?_,
    mi_mappedblocks := ?_,
    mi_no_overlap := ?_,
    mi_representable := ?_,
    mi_perm_inv := ?_
  }
  · intro b bt d ofs k p hmap hp
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 z0 b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      have hsrc := scc085_alloc_perm_new_inv m1 lo hi m1' b1 halloc1
        ofs k p hp
      simpa only [scc085_zadd_zero] using scc085_perm_of_freeable
        (scc085_alloc_perm_new m2 lo hi m2' b2 halloc2 ofs k hsrc)
    · change scc085_extend_inj j b1 b2 z0 b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 z0 b hb] at hmap
      have hpOld := scc085_alloc_perm_old_inv m1 lo hi m1' b1 halloc1
        b ofs k p hb hp
      have htOld := hinj.mi_inj.mi_perm b bt d ofs k p hmap hpOld
      exact scc085_alloc_perm_old m2 lo hi m2' b2 halloc2 bt
        (zAdd ofs d) k p (htargetOld b bt d hmap) htOld
  · intro b bt d chunk ofs p hmap hrange
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 z0 b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      exact ⟨z0, by
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
        change (0 : Int) = intOfZ (align_chunk chunk) * 0
        omega⟩
    · change scc085_extend_inj j b1 b2 z0 b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 z0 b hb] at hmap
      apply hinj.mi_inj.mi_align b bt d chunk ofs p hmap
      intro i hibounds
      exact scc085_alloc_perm_old_inv m1 lo hi m1' b1 halloc1
        b i Max p hb (hrange i hibounds)
  · intro b ofs bt d hmap hp
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 z0 b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      rw [scc085_alloc_contents_new m1 lo hi m1' b1 halloc1 ofs]
      exact CompCert4Lean.Common.Memdata.memval_inject.undef j'
        (ZMap.get (zAdd ofs z0) (PMap.get b2 m2'.mem_contents))
    · change scc085_extend_inj j b1 b2 z0 b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 z0 b hb] at hmap
      have hpOld := scc085_alloc_perm_old_inv m1 lo hi m1' b1 halloc1
        b ofs Cur Readable hb hp
      have hm := hinj.mi_inj.mi_memval b ofs bt d hmap hpOld
      have hm' := CompCert4Lean.Common.Memdata.memval_inject_incr
        j j'
        (ZMap.get ofs (PMap.get b m1.mem_contents))
        (ZMap.get (zAdd ofs d) (PMap.get bt m2.mem_contents)) hm hincr
      rw [scc085_alloc_contents_old m1 lo hi m1' b1 halloc1 b ofs hb,
        scc085_alloc_contents_old m2 lo hi m2' b2 halloc2 bt (zAdd ofs d)
          (htargetOld b bt d hmap)]
      exact hm'
  · intro b hvalid
    by_cases hb : b = b1
    · subst b
      exact False.elim (hvalid (scc085_alloc_valid_new m1 lo hi m1' b1 halloc1))
    · change scc085_extend_inj j b1 b2 z0 b = none
      rw [scc085_extend_inj_other j b1 b2 z0 b hb]
      apply hinj.mi_freeblocks b
      intro hv
      apply hvalid
      change Plt b m1'.nextblock
      rw [scc085_alloc_nextblock m1 lo hi m1' b1 halloc1]
      exact Plt_trans_succ b m1.nextblock hv
  · intro b bt d hmap
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 z0 b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      exact scc085_alloc_valid_new m2 lo hi m2' b2 halloc2
    · change scc085_extend_inj j b1 b2 z0 b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 z0 b hb] at hmap
      have hv := hinj.mi_mappedblocks b bt d hmap
      change Plt bt m2'.nextblock
      rw [scc085_alloc_nextblock m2 lo hi m2' b2 halloc2]
      exact Plt_trans_succ bt m2.nextblock hv
  · intro a ta da b bt db oa ob hab hma hmb hpa hpb
    by_cases ha : a = b1
    · subst a
      have hb : b ≠ b1 := by exact fun h => hab h.symm
      change scc085_extend_inj j b1 b2 z0 b1 = some (ta, da) at hma
      rw [scc085_extend_inj_same] at hma
      cases hma
      change scc085_extend_inj j b1 b2 z0 b = some (bt, db) at hmb
      rw [scc085_extend_inj_other j b1 b2 z0 b hb] at hmb
      exact Or.inl (fun h => htargetOld b bt db hmb h.symm)
    · by_cases hb : b = b1
      · subst b
        change scc085_extend_inj j b1 b2 z0 b1 = some (bt, db) at hmb
        rw [scc085_extend_inj_same] at hmb
        cases hmb
        change scc085_extend_inj j b1 b2 z0 a = some (ta, da) at hma
        rw [scc085_extend_inj_other j b1 b2 z0 a ha] at hma
        exact Or.inl (htargetOld a ta da hma)
      · change scc085_extend_inj j b1 b2 z0 a = some (ta, da) at hma
        rw [scc085_extend_inj_other j b1 b2 z0 a ha] at hma
        change scc085_extend_inj j b1 b2 z0 b = some (bt, db) at hmb
        rw [scc085_extend_inj_other j b1 b2 z0 b hb] at hmb
        apply hinj.mi_no_overlap a ta da b bt db oa ob hab hma hmb
        · exact scc085_alloc_perm_old_inv m1 lo hi m1' b1 halloc1
            a oa Max Nonempty ha hpa
        · exact scc085_alloc_perm_old_inv m1 lo hi m1' b1 halloc1
            b ob Max Nonempty hb hpb
  · intro b bt d ofs hmap hp
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 z0 b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      have hu0 : zLe z0 (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) := by
        have h := ofs.intrange.1
        change (-1 : Int) < intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) at h
        change (0 : Int) ≤ intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
        omega
      have huMax : zLe (Ptrofs.unsigned ofs) Ptrofs.max_unsigned := by
        have h := ofs.intrange.2
        change intOfZ (Ptrofs.unsigned ofs) < 18446744073709551616 at h
        change intOfZ (Ptrofs.unsigned ofs) ≤ 18446744073709551615
        omega
      exact ⟨by exact Int.le_refl 0, by simpa only [scc085_zadd_zero] using hu0,
        by simpa only [scc085_zadd_zero] using huMax⟩
    · change scc085_extend_inj j b1 b2 z0 b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 z0 b hb] at hmap
      apply hinj.mi_representable b bt d ofs hmap
      rcases hp with hp | hp
      · exact Or.inl (scc085_alloc_perm_old_inv m1 lo hi m1' b1 halloc1
          b (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) Max Nonempty hb hp)
      · exact Or.inr (scc085_alloc_perm_old_inv m1 lo hi m1' b1 halloc1
          b (zSub (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) z1) Max Nonempty hb hp)
  · intro b ofs bt d k p hmap ht
    by_cases hb : b = b1
    · subst b
      change scc085_extend_inj j b1 b2 z0 b1 = some (bt, d) at hmap
      rw [scc085_extend_inj_same] at hmap
      cases hmap
      by_cases hs : Mem.perm m1' b1 ofs Max Nonempty
      · exact Or.inl (scc085_perm_of_freeable
          (scc085_alloc_perm_new m1 lo hi m1' b1 halloc1 ofs k
            (scc085_alloc_perm_new_inv m1 lo hi m1' b1 halloc1
              ofs Max Nonempty hs)))
      · exact Or.inr hs
    · change scc085_extend_inj j b1 b2 z0 b = some (bt, d) at hmap
      rw [scc085_extend_inj_other j b1 b2 z0 b hb] at hmap
      have htOld := scc085_alloc_perm_old_inv m2 lo hi m2' b2 halloc2
        bt (zAdd ofs d) k p (htargetOld b bt d hmap) ht
      rcases hinj.mi_perm_inv b ofs bt d k p hmap htOld with hs | hs
      · exact Or.inl (scc085_alloc_perm_old m1 lo hi m1' b1 halloc1
          b ofs k p hb hs)
      · exact Or.inr (fun hp => hs (scc085_alloc_perm_old_inv m1 lo hi m1'
          b1 halloc1 b ofs Max Nonempty hb hp))


private theorem scc085_store_unchanged_pred (P : block → Z → Prop)
    (chunk : AST.memory_chunk) (m : Memory.mem) (b : Values.block) (ofs : Z)
    (v : Values.val) (m' : Memory.mem)
    (hstore : Mem.store chunk m b ofs v = some m')
    (hout : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) →
      ¬ P b i) :
    Mem.unchanged_on P m m' := by
  have hnext := Mem.nextblock_store chunk m b ofs v m' hstore
  have hcontents := Mem.store_mem_contents chunk m b ofs v m' hstore
  refine {
    unchanged_on_nextblock := ?_,
    unchanged_on_perm := ?_,
    unchanged_on_contents := ?_ }
  · change Ple m.nextblock m'.nextblock
    rw [hnext]
    exact Ple_refl _
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
      have hget : PMap.get b (PMap.set b
          (Mem.setN (encode_val chunk v) ofs (PMap.get b m.mem_contents))
          m.mem_contents) =
          Mem.setN (encode_val chunk v) ofs (PMap.get b m.mem_contents) := by
        exact scc085_pmap_get_set_same b _ m.mem_contents
      rw [hget]
      apply Mem.setN_other
      intro i hi heq
      subst i
      apply hout ofs'
      have hlen := CompCert4Lean.Common.Memdata.encode_val_length chunk v
      have hi' := hi
      rw [hlen] at hi'
      have hsize' : ZArith.BinInt.Z.of_nat (size_chunk_nat chunk) = size_chunk chunk :=
        (CompCert4Lean.Common.Memdata.size_chunk_conv chunk).symm
      simpa [hsize'] using hi'
      exact hP
    · rw [scc085_pmap_get_set_other _ _ _ _ hb]

private def scc085_extcall_injection (sem : extcall_sem) : Prop :=
  ∀ ge1 ge2 vargs m1 t vres m1' j m2 vargs2,
    symbols_inject j ge1 ge2 → sem ge1 vargs m1 t vres m1' →
    Mem.inject j m1 m2 → Val.inject_list j vargs vargs2 →
    ∃ j' vres2 m2', sem ge2 vargs2 m2 t vres2 m2' ∧
      Val.inject j' vres vres2 ∧ Mem.inject j' m1' m2' ∧
      Mem.unchanged_on (loc_out_of_reach j m1) m2 m2' ∧
      inject_incr j j' ∧ inject_separated j j' m1 m2

private theorem scc085_injection_of_properties (sem : extcall_sem) (sg : signature)
    (h : extcall_properties sem sg) : scc085_extcall_injection sem := by
  intro ge1 ge2 vargs m1 t vres m1' j m2 vargs2 hsym hcall hinj hargs
  obtain ⟨j', vres2, m2', hc, hv, hi, _, hu, hn, hs⟩ :=
    h.ec_mem_inject ge1 ge2 vargs m1 t vres m1' j m2 vargs2 hsym hcall hinj hargs
  exact ⟨j', vres2, m2', hc, hv, hi, hu, hn, hs⟩

private theorem scc085_alloc_store_unchanged (Q : block → Z → Prop)
    (m ma mf : mem) (b : block) (lo hi : Z) (v : val)
    (ha : Mem.alloc m lo hi = (ma, b))
    (hs : Mem.store Mptr ma b lo v = some mf) : Mem.unchanged_on Q m mf := by
  have halloc := scc085_alloc_unchanged_on (fun b' _ => b' ≠ b) m lo hi ma b ha
  have hstore := scc085_store_unchanged_pred (fun b' _ => b' ≠ b) Mptr ma b lo v mf hs
    (fun _ _ hn => hn rfl)
  have hu := scc085_unchanged_trans _ _ _ _ halloc hstore
  refine ⟨hu.1, ?_, ?_⟩
  · intro b' ofs k p _ hb
    apply hu.2 b' ofs k p
    · intro heq
      subst b'
      exact Mem.fresh_block_alloc m lo hi ma b ha hb
    · exact hb
  · intro b' ofs _ hp
    apply hu.3 b' ofs
    · intro heq
      subst b'
      exact Mem.fresh_block_alloc m lo hi ma b ha (validBlockOfPerm hp)
    · exact hp

private theorem scc085_malloc_injection : scc085_extcall_injection extcall_malloc_sem := by
  intro ge1 ge2 vargs m1 t vres m1' j m2 vargs2 hsym hcall hinj hargs
  cases hcall with
  | extcall_malloc_sem_intro sz _ ma b1 _ ha hs =>
      cases hargs with
      | inject_list_cons v1 v2 l1 l2 hv hl =>
          cases hl
          have heq : v2 = Vptrofs sz := by
            change Val.inject j (Vlong (Ptrofs.to_int64 sz)) v2 at hv
            cases hv
            rfl
          subst v2
          obtain ⟨ma2, b2, ha2⟩ := show ∃ ma2 b2,
              Mem.alloc m2 (ZArith.BinInt.Z.opp (size_chunk Mptr)) (Ptrofs.unsigned sz) =
                (ma2, b2) from ⟨_, _, rfl⟩
          let j' := scc085_extend_inj j b1 b2 z0
          have hnew := scc085_alloc_same_bounds_inject j m1 m2 ma ma2 _ _ b1 b2 hinj ha ha2
          have hmap : j' b1 = some (b2, z0) := scc085_extend_inj_same j b1 b2 z0
          have hvsz : Val.inject j' (Vptrofs sz) (Vptrofs sz) := .inject_long (Ptrofs.to_int64 sz)
          obtain ⟨mf2, hs2, hmem2⟩ := Mem.store_mapped_inj j' Mptr ma b1 _ (Vptrofs sz)
            m1' ma2 b2 z0 (Vptrofs sz) hnew.mi_inj hs hnew.mi_no_overlap hmap hvsz
          change Mem.store Mptr ma2 b2
            (zAdd (ZArith.BinInt.Z.opp (size_chunk Mptr)) z0) (Vptrofs sz) = some mf2 at hs2
          rw [scc085_zadd_zero] at hs2
          have hfull := scc085_store_injection_transport j' Mptr ma m1' ma2 mf2
            b1 b2 _ _ (Vptrofs sz) (Vptrofs sz) hnew hs hs2 hmem2
          refine ⟨j', Vptr b2 Ptrofs.zero, mf2,
            extcall_malloc_sem_intro sz m2 ma2 b2 mf2 ha2 hs2, ?_, hfull,
            scc085_alloc_store_unchanged _ m2 ma2 mf2 b2 _ _ (Vptrofs sz) ha2 hs2, ?_, ?_⟩
          · apply Val.inject.inject_ptr b1 Ptrofs.zero b2 Ptrofs.zero z0 hmap
            rfl
          · intro b bt d hm
            by_cases hb : b = b1
            · subst b
              have hn := hinj.mi_freeblocks b1 (Mem.fresh_block_alloc m1 _ _ ma b1 ha)
              rw [hn] at hm
              cases hm
            · exact (scc085_extend_inj_other j b1 b2 z0 b hb).trans hm
          · intro b bt d hn hm
            by_cases hb : b = b1
            · subst b
              rw [hmap] at hm
              cases hm
              exact ⟨Mem.fresh_block_alloc m1 _ _ ma b1 ha,
                Mem.fresh_block_alloc m2 _ _ ma2 b2 ha2⟩
            · change scc085_extend_inj j b1 b2 z0 b = some (bt, d) at hm
              rw [scc085_extend_inj_other j b1 b2 z0 b hb, hn] at hm
              cases hm

private theorem scc085_free_shift_inject (j : meminj) (m1 m1' m2 : mem)
    (b1 b2 : block) (lo hi delta : Z) (hinj : Mem.inject j m1 m2)
    (hfree : Mem.free m1 b1 lo hi = some m1') (hmap : j b1 = some (b2, delta)) :
    ∃ m2', Mem.free m2 b2 (zAdd lo delta) (zAdd hi delta) = some m2' ∧
      Mem.inject j m1' m2' ∧
      Mem.unchanged_on (loc_out_of_reach j m1) m2 m2' := by
  have hrange := scc085_free_range_perm m1 b1 lo hi m1' hfree
  have hrange2 := Mem.range_perm_inj j m1 m2 b1 lo hi Cur Freeable b2 delta
    hinj.mi_inj hrange hmap
  obtain ⟨m2', hfree2⟩ := scc085_range_perm_free m2 b2 _ _ hrange2
  have hshift : ∀ i, zLe (zAdd lo delta) i ∧ zLt i (zAdd hi delta) →
      zLe lo (zSub i delta) ∧ zLt (zSub i delta) hi := by
    intro i hb
    change intOfZ (zAdd lo delta) ≤ intOfZ i ∧ intOfZ i < intOfZ (zAdd hi delta) at hb
    change intOfZ lo ≤ intOfZ (zSub i delta) ∧ intOfZ (zSub i delta) < intOfZ hi
    simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hb ⊢
    omega
  refine ⟨m2', hfree2, ?_, ?_⟩
  · apply scc085_free_right_inject j m1' m2 m2' b2 _ _
      (scc085_free_left_inject j m1 m1' m2 b1 lo hi hinj hfree) hfree2
    intro b d ofs k p hm hp hb
    have hpoint := hshift (zAdd ofs d) hb
    by_cases heq : b = b1
    · subst b
      rw [hmap] at hm
      cases hm
      rw [zSubAddCancel] at hpoint
      exact scc085_perm_free_2 m1 m1' b1 lo hi hfree ofs k p hpoint.1 hpoint.2 hp
    · have hpold := scc085_perm_of_free m1 m1' b1 lo hi hfree b ofs k p hp
      have hpfirst := hrange _ hpoint
      have hno := hinj.mi_no_overlap b b2 d b1 b2 delta ofs
        (zSub (zAdd ofs d) delta) heq hm hmap
        (permMaxNonemptyOfPerm hpold) (permMaxNonemptyOfPerm hpfirst)
      rcases hno with hne | hne
      · exact hne rfl
      · apply hne
        apply intOfZ_injective
        simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        omega
  · apply scc085_free_unchanged_on _ m2 b2 _ _ m2' hfree2
    intro i hi hout
    exact hout b1 delta hmap (permMaxNonemptyOfPerm (hrange _ (hshift i hi)))

private theorem scc085_inject_separated_refl (j : meminj) (m1 m2 : mem) :
    inject_separated j j m1 m2 := by
  intro b b' d hn hm
  rw [hn] at hm
  cases hm

private theorem scc085_free_injection : scc085_extcall_injection extcall_free_sem := by
  intro ge1 ge2 vargs m1 t vres m1' j m2 vargs2 hsym hcall hinj hargs
  cases hcall with
  | extcall_free_sem_ptr b lo sz _ _ hl hf =>
      cases hargs with
      | inject_list_cons _ v2 _ _ hp hnil =>
          cases hnil
          cases hp with
          | inject_ptr _ _ b2 lo2 delta hm heq =>
              obtain ⟨v, hl2, hv⟩ := Mem.load_inj j m1 m2 Mptr b _ b2 delta
                (Vptrofs sz) hinj.mi_inj hl hm
              have hev : v = Vptrofs sz := by
                change Val.inject j (Vlong (Ptrofs.to_int64 sz)) v at hv
                cases hv
                rfl
              subst v
              have hrange := scc085_free_range_perm m1 b _ _ m1' hf
              have hnear : Mem.perm m1 b (zSub (Ptrofs.unsigned lo) z1) Max Nonempty := by
                apply permMaxNonemptyOfPerm (p := Freeable) (k := Cur)
                apply hrange
                have hsz := sz.intrange.1
                change (-1 : Int) < intOfZ (Ptrofs.unsigned sz) at hsz
                change intOfZ (zSub (Ptrofs.unsigned lo) (size_chunk Mptr)) ≤
                    intOfZ (zSub (Ptrofs.unsigned lo) z1) ∧
                  intOfZ (zSub (Ptrofs.unsigned lo) z1) <
                    intOfZ (zAdd (Ptrofs.unsigned lo) (Ptrofs.unsigned sz))
                simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
                change intOfZ (Ptrofs.unsigned lo) - 8 ≤ intOfZ (Ptrofs.unsigned lo) - 1 ∧
                  intOfZ (Ptrofs.unsigned lo) - 1 <
                    intOfZ (Ptrofs.unsigned lo) + intOfZ (Ptrofs.unsigned sz)
                omega
              have haddr := scc085_address_inject j m1 m2 b b2 lo delta hinj hm (Or.inr hnear)
              have hlo : zSub (Ptrofs.unsigned lo2) (size_chunk Mptr) =
                  zAdd (zSub (Ptrofs.unsigned lo) (size_chunk Mptr)) delta := by
                rw [heq, haddr]
                apply intOfZ_injective
                simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
                omega
              have hhi : zAdd (Ptrofs.unsigned lo2) (Ptrofs.unsigned sz) =
                  zAdd (zAdd (Ptrofs.unsigned lo) (Ptrofs.unsigned sz)) delta := by
                rw [heq, haddr]
                apply intOfZ_injective
                simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
                omega
              obtain ⟨m2', hf2, hi2, hu2⟩ := scc085_free_shift_inject j m1 m1' m2
                b b2 _ _ delta hinj hf hm
              refine ⟨j, Vundef, m2', ?_, .val_inject_undef _, hi2, hu2,
                (fun _ _ _ h => h), scc085_inject_separated_refl _ _ _⟩
              apply extcall_free_sem_ptr b2 lo2 sz m2 m2'
              · change Mem.load Mptr m2 b2 (zSub (Ptrofs.unsigned lo2) (size_chunk Mptr)) = _
                rw [hlo]
                exact hl2
              · change Mem.free m2 b2 (zSub (Ptrofs.unsigned lo2) (size_chunk Mptr))
                  (zAdd (Ptrofs.unsigned lo2) (Ptrofs.unsigned sz)) = _
                rw [hlo, hhi]
                exact hf2
  | extcall_free_sem_null =>
      cases hargs with
      | inject_list_cons _ v2 _ _ hp hnil =>
          cases hnil
          change Val.inject j (Vlong Int64.zero) v2 at hp
          cases hp
          exact ⟨j, Vundef, m2, extcall_free_sem_null m2, .val_inject_undef _, hinj,
            scc085_unchanged_refl _ _, (fun _ _ _ h => h),
            scc085_inject_separated_refl _ _ _⟩

private theorem scc085_storebytes_injection_transport
    (f : meminj)
    (m1 m1' m2 m2' : Memory.mem)
    (sb1 sb2 : Values.block) (sofs1 sofs2 : Z)
    (bytes1 bytes2 : List memval)
    (hinj : Mem.inject f m1 m2)
    (hstore1 : Mem.storebytes m1 sb1 sofs1 bytes1 = some m1')
    (hstore2 : Mem.storebytes m2 sb2 sofs2 bytes2 = some m2')
    (hmem : Mem.mem_inj f m1' m2') : Mem.inject f m1' m2' := by
  refine {
    mi_inj := hmem,
    mi_freeblocks := ?_,
    mi_mappedblocks := ?_,
    mi_no_overlap := ?_,
    mi_representable := ?_,
    mi_perm_inv := ?_ }
  · intro b hb
    change ¬ Plt b m1'.nextblock at hb
    apply hinj.mi_freeblocks b
    intro hb1
    apply hb
    rw [Mem.nextblock_storebytes m1 sb1 sofs1 bytes1 m1' hstore1]
    exact hb1
  · intro b b' delta hmap
    apply Mem.storebytes_valid_block_1 m2 sb2 sofs2 bytes2 m2' hstore2
    exact hinj.mi_mappedblocks b b' delta hmap
  · intro b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne hmap1 hmap2 hp1 hp2
    apply hinj.mi_no_overlap b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne hmap1 hmap2
    · exact Mem.perm_storebytes_2 m1 sb1 sofs1 bytes1 m1' hstore1 b1 ofs1 Max Nonempty hp1
    · exact Mem.perm_storebytes_2 m1 sb1 sofs1 bytes1 m1' hstore1 b2 ofs2 Max Nonempty hp2
  · intro b b' delta ofs hmap hp
    apply hinj.mi_representable b b' delta ofs hmap
    rcases hp with hp | hp
    · exact Or.inl (Mem.perm_storebytes_2 m1 sb1 sofs1 bytes1 m1' hstore1
        b (Ptrofs.unsigned ofs) Max Nonempty hp)
    · exact Or.inr (Mem.perm_storebytes_2 m1 sb1 sofs1 bytes1 m1' hstore1
        b (zSub (Ptrofs.unsigned ofs) z1) Max Nonempty hp)
  · intro b ofs b' delta k p hmap hp
    obtain hp2 := Mem.perm_storebytes_2 m2 sb2 sofs2 bytes2 m2' hstore2
      b' (zAdd ofs delta) k p hp
    obtain hp1 | hn := hinj.mi_perm_inv b ofs b' delta k p hmap hp2
    · exact Or.inl (Mem.perm_storebytes_1 m1 sb1 sofs1 bytes1 m1' hstore1 b ofs k p hp1)
    · exact Or.inr (fun hp1' => hn
        (Mem.perm_storebytes_2 m1 sb1 sofs1 bytes1 m1' hstore1 b ofs Max Nonempty hp1'))

private theorem scc085_storebytes_unchanged (Q : block → Z → Prop)
    (m m' : mem) (b : block) (ofs : Z) (bytes : List memval)
    (hs : Mem.storebytes m b ofs bytes = some m')
    (hout : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs (ZArith.BinInt.Z.of_nat bytes.length)) →
      ¬ Q b i) : Mem.unchanged_on Q m m' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Mem.nextblock_storebytes m b ofs bytes m' hs]
    exact Ple_refl _
  · intro b' ofs' k p _ _
    exact ⟨Mem.perm_storebytes_1 m b ofs bytes m' hs b' ofs' k p,
      Mem.perm_storebytes_2 m b ofs bytes m' hs b' ofs' k p⟩
  · intro b' ofs' hq hp
    rw [Mem.storebytes_mem_contents m b ofs bytes m' hs]
    by_cases hb : b' = b
    · subst b'
      have hget := scc085_pmap_get_set_same b
        (Mem.setN bytes ofs (PMap.get b m.mem_contents)) m.mem_contents
      rw [hget]
      apply Mem.setN_other
      intro i hi heq
      subst i
      exact hout ofs' hi hq
    · rw [scc085_pmap_get_set_other _ _ _ _ hb]

private theorem scc085_aligned_area (j : meminj) (m1 m2 : mem)
    (b1 b2 : block) (ofs delta al sz : Z) (hinj : Mem.inject j m1 m2)
    (hal : al = z1 ∨ al = ZArith.BinInt.Z.of_nat 2 ∨
      al = ZArith.BinInt.Z.of_nat 4 ∨ al = ZArith.BinInt.Z.of_nat 8)
    (hsz : zLt z0 sz) (hdiv : zDivide al sz)
    (hrange : Mem.range_perm m1 b1 ofs (zAdd ofs sz) Max Nonempty)
    (hofs : zDivide al ofs) (hmap : j b1 = some (b2, delta)) :
    zDivide al (zAdd ofs delta) := by
  have hlen : zLe al sz := by
    rcases hdiv with ⟨k, hk⟩
    have heq := congrArg intOfZ hk
    change 0 < intOfZ sz at hsz
    change intOfZ al ≤ intOfZ sz
    simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt] at heq
    rcases hal with ha | ha | ha | ha <;> subst al
    · change intOfZ sz = 1 * intOfZ k at heq
      change (1 : Int) ≤ intOfZ sz
      omega
    · change intOfZ sz = 2 * intOfZ k at heq
      change (2 : Int) ≤ intOfZ sz
      omega
    · change intOfZ sz = 4 * intOfZ k at heq
      change (4 : Int) ≤ intOfZ sz
      omega
    · change intOfZ sz = 8 * intOfZ k at heq
      change (8 : Int) ≤ intOfZ sz
      omega

  obtain ⟨chunk, hsize, halign⟩ : ∃ chunk : memory_chunk,
      size_chunk chunk = al ∧ align_chunk chunk = al := by
    rcases hal with ha | ha | ha | ha <;> subst al
    · exact ⟨Mint8unsigned, rfl, rfl⟩
    · exact ⟨Mint16unsigned, rfl, rfl⟩
    · exact ⟨Mint32, rfl, rfl⟩
    · exact ⟨Mint64, rfl, rfl⟩
  have hdelta : zDivide al delta := by
    rw [← halign]
    apply hinj.mi_inj.mi_align b1 b2 delta chunk ofs Nonempty hmap
    intro i hi
    apply hrange i
    rw [hsize] at hi
    have hi1 := hi.1
    have hi2 := hi.2
    change intOfZ ofs ≤ intOfZ i at hi1
    change intOfZ i < intOfZ (zAdd ofs al) at hi2
    change intOfZ al ≤ intOfZ sz at hlen
    change intOfZ ofs ≤ intOfZ i ∧ intOfZ i < intOfZ (zAdd ofs sz)
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hi2 ⊢
    omega
  obtain ⟨k1, hk1⟩ := hofs
  obtain ⟨k2, hk2⟩ := hdelta
  refine ⟨zAdd k1 k2, ?_⟩
  rw [hk1, hk2]
  apply intOfZ_injective
  simp only [zAdd, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt, Int.mul_add]

private theorem scc085_disjoint_inject (j : meminj) (m1 m2 : mem)
    (b1 b1' b2 b2' : block) (d1 d2 ofs1 ofs2 sz : Z)
    (hinj : Mem.inject j m1 m2)
    (hm1 : j b1 = some (b1', d1)) (hm2 : j b2 = some (b2', d2))
    (hp1 : Mem.range_perm m1 b1 ofs1 (zAdd ofs1 sz) Max Nonempty)
    (hp2 : Mem.range_perm m1 b2 ofs2 (zAdd ofs2 sz) Max Nonempty)
    (hsz : zLt z0 sz)
    (hdisj : b1 ≠ b2 ∨ ofs1 = ofs2 ∨ zLe (zAdd ofs1 sz) ofs2 ∨
      zLe (zAdd ofs2 sz) ofs1) :
    b1' ≠ b2' ∨ zAdd ofs1 d1 = zAdd ofs2 d2 ∨
      zLe (zAdd (zAdd ofs1 d1) sz) (zAdd ofs2 d2) ∨
      zLe (zAdd (zAdd ofs2 d2) sz) (zAdd ofs1 d1) := by
  by_cases hb : b1' = b2'
  · subst b2'
    by_cases hs : b1 = b2
    · subst b2
      have heq := Option.some.inj (hm1.symm.trans hm2)
      have hd : d1 = d2 := congrArg Prod.snd heq
      subst d2
      rcases hdisj with hn | he | hl | hr
      · exact (hn rfl).elim
      · exact Or.inr (Or.inl (congrArg (fun x => zAdd x d1) he))
      · right; right; left
        change intOfZ (zAdd (zAdd ofs1 d1) sz) ≤ intOfZ (zAdd ofs2 d1)
        change intOfZ (zAdd ofs1 sz) ≤ intOfZ ofs2 at hl
        simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hl ⊢
        omega
      · right; right; right
        change intOfZ (zAdd (zAdd ofs2 d1) sz) ≤ intOfZ (zAdd ofs1 d1)
        change intOfZ (zAdd ofs2 sz) ≤ intOfZ ofs1 at hr
        simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hr ⊢
        omega
    · by_cases hl : zLe (zAdd (zAdd ofs1 d1) sz) (zAdd ofs2 d2)
      · exact Or.inr (Or.inr (Or.inl hl))
      by_cases hr : zLe (zAdd (zAdd ofs2 d2) sz) (zAdd ofs1 d1)
      · exact Or.inr (Or.inr (Or.inr hr))
      let q := zOfInt (max (intOfZ ofs1 + intOfZ d1) (intOfZ ofs2 + intOfZ d2))
      have hbounds : (zLe ofs1 (zSub q d1) ∧ zLt (zSub q d1) (zAdd ofs1 sz)) ∧
          (zLe ofs2 (zSub q d2) ∧ zLt (zSub q d2) (zAdd ofs2 sz)) := by
        change 0 < intOfZ sz at hsz
        change ¬ intOfZ (zAdd (zAdd ofs1 d1) sz) ≤ intOfZ (zAdd ofs2 d2) at hl
        change ¬ intOfZ (zAdd (zAdd ofs2 d2) sz) ≤ intOfZ (zAdd ofs1 d1) at hr
        change (intOfZ ofs1 ≤ intOfZ (zSub q d1) ∧
            intOfZ (zSub q d1) < intOfZ (zAdd ofs1 sz)) ∧
          (intOfZ ofs2 ≤ intOfZ (zSub q d2) ∧
            intOfZ (zSub q d2) < intOfZ (zAdd ofs2 sz))
        simp only [q, zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
          intOfZ_zOfInt] at hl hr ⊢
        omega
      have hno := hinj.mi_no_overlap b1 b1' d1 b2 b1' d2 (zSub q d1) (zSub q d2)
        hs hm1 hm2 (hp1 _ hbounds.1) (hp2 _ hbounds.2)
      rcases hno with hn | hn
      · exact (hn rfl).elim
      · apply False.elim
        apply hn
        apply intOfZ_injective
        simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        omega
  · exact Or.inl hb

private theorem scc085_memcpy_injection (sz al : Z) :
    scc085_extcall_injection (extcall_memcpy_sem sz al) := by
  intro ge1 ge2 vargs m1 t vres m1' j m2 vargs2 hsym hcall hinj hargs
  cases hcall with
  | extcall_memcpy_sem_intro bd od bs os _ bytes _ hal hsz hdiv hs hd hdisj hl hst =>
      cases hargs with
      | inject_list_cons _ _ _ _ hpd htail =>
          cases htail with
          | inject_list_cons _ _ _ _ hps hnil =>
              cases hnil
              cases hpd with
              | inject_ptr _ _ bd2 od2 dd hmd hed =>
                  cases hps with
                  | inject_ptr _ _ bs2 os2 ds hms hes =>
                      have hlen : ZArith.BinInt.Z.of_nat bytes.length = sz := by
                        have hh := Mem.loadbytes_length m1 bs (Ptrofs.unsigned os) sz bytes hl
                        apply intOfZ_injective
                        rw [hh]
                        change intOfZ (zOfInt (Int.ofNat (Int.toNat (intOfZ sz)))) = intOfZ sz
                        rw [intOfZ_zOfInt]
                        change (0 : Int) ≤ intOfZ sz at hsz
                        exact Int.toNat_of_nonneg hsz
                      by_cases hz : sz = z0
                      · cases hz
                        have hempty : bytes = [] := by
                          apply List.eq_nil_of_length_eq_zero
                          have hh := congrArg intOfZ hlen
                          change intOfZ (zOfInt (Int.ofNat bytes.length)) = 0 at hh
                          rw [intOfZ_zOfInt] at hh
                          exact Int.ofNat.inj hh
                        subst bytes
                        have hzeroRange : ∀ (m : mem) b ofs,
                            Mem.range_perm m b ofs (zAdd ofs (ZArith.BinInt.Z.of_nat 0)) Cur Writable := by
                          intro m b ofs i hi
                          change intOfZ ofs ≤ intOfZ i ∧
                            intOfZ i < intOfZ (zAdd ofs z0) at hi
                          rw [scc085_zadd_zero] at hi
                          omega
                        obtain ⟨m2', hst2⟩ := Mem.range_perm_storebytes m2 bd2 (Ptrofs.unsigned od2) []
                          (hzeroRange m2 bd2 (Ptrofs.unsigned od2))
                        have himem := Mem.storebytes_empty_inj j m1 bd (Ptrofs.unsigned od) m1'
                          m2 bd2 (Ptrofs.unsigned od2) m2' hinj.mi_inj hst hst2
                        have hi := scc085_storebytes_injection_transport j m1 m1' m2 m2'
                          bd bd2 _ _ [] [] hinj hst hst2 himem
                        refine ⟨j, Vundef, m2', ?_, .val_inject_undef _, hi, ?_,
                          (fun _ _ _ h => h), scc085_inject_separated_refl _ _ _⟩
                        · apply extcall_memcpy_sem_intro bd2 od2 bs2 os2 m2 [] m2'
                            hal hsz hdiv
                          · intro hn
                            exact (Int.lt_irrefl 0 hn).elim
                          · intro hn
                            exact (Int.lt_irrefl 0 hn).elim
                          · right; right
                            by_cases hle : zLe (Ptrofs.unsigned os2) (Ptrofs.unsigned od2)
                            · left
                              simpa only [scc085_zadd_zero] using hle
                            · right
                              change intOfZ (zAdd (Ptrofs.unsigned od2) z0) ≤ intOfZ (Ptrofs.unsigned os2)
                              rw [scc085_zadd_zero]
                              change ¬ intOfZ (Ptrofs.unsigned os2) ≤ intOfZ (Ptrofs.unsigned od2) at hle
                              omega
                          · exact Mem.loadbytes_empty m2 bs2 (Ptrofs.unsigned os2) z0 (Int.le_refl 0)
                          · exact hst2
                        · apply scc085_storebytes_unchanged _ m2 m2' bd2 _ [] hst2
                          intro i hi hout
                          change intOfZ (Ptrofs.unsigned od2) ≤ intOfZ i ∧
                            intOfZ i < intOfZ (zAdd (Ptrofs.unsigned od2) z0) at hi
                          rw [scc085_zadd_zero] at hi
                          omega
                      · have hpos : zLt z0 sz := by
                          change (0 : Int) < intOfZ sz
                          change (0 : Int) ≤ intOfZ sz at hsz
                          have hn : intOfZ sz ≠ 0 := by
                            intro heq
                            exact hz (intOfZ_injective heq)
                          omega
                        have hrs : Mem.range_perm m1 bs (Ptrofs.unsigned os)
                            (zAdd (Ptrofs.unsigned os) sz) Max Nonempty := by
                          intro i hi
                          exact permMaxNonemptyOfPerm
                            (Mem.loadbytes_range_perm m1 bs (Ptrofs.unsigned os) sz bytes hl i hi)
                        have hrd : Mem.range_perm m1 bd (Ptrofs.unsigned od)
                            (zAdd (Ptrofs.unsigned od) sz) Max Nonempty := by
                          intro i hi
                          apply permMaxNonemptyOfPerm
                            (Mem.storebytes_range_perm m1 bd (Ptrofs.unsigned od) bytes m1' hst i _)
                          change zLe (Ptrofs.unsigned od) i ∧
                            zLt i (zAdd (Ptrofs.unsigned od) (ZArith.BinInt.Z.of_nat bytes.length))
                          rw [hlen]
                          exact hi
                        have hstart : ∀ ofs, zLe ofs ofs ∧ zLt ofs (zAdd ofs sz) := by
                          intro ofs
                          change (0 : Int) < intOfZ sz at hpos
                          change intOfZ ofs ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ (zAdd ofs sz)
                          simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
                          omega
                        have had : Ptrofs.unsigned od2 = zAdd (Ptrofs.unsigned od) dd := by
                          rw [hed]
                          exact scc085_address_inject j m1 m2 bd bd2 od dd hinj hmd
                            (Or.inl (hrd _ (hstart _)))
                        have has : Ptrofs.unsigned os2 = zAdd (Ptrofs.unsigned os) ds := by
                          rw [hes]
                          exact scc085_address_inject j m1 m2 bs bs2 os ds hinj hms
                            (Or.inl (hrs _ (hstart _)))
                        obtain ⟨bytes2, hl2, hbytes⟩ := Mem.loadbytes_inj j m1 m2 sz bs
                          (Ptrofs.unsigned os) bs2 ds bytes hinj.mi_inj hl hms
                        obtain ⟨m2', hst2, himem⟩ := Mem.storebytes_mapped_inj j m1 bd
                          (Ptrofs.unsigned od) bytes m1' m2 bd2 dd bytes2 hinj.mi_inj hst
                          hinj.mi_no_overlap hmd hbytes
                        have hi := scc085_storebytes_injection_transport j m1 m1' m2 m2'
                          bd bd2 _ _ bytes bytes2 hinj hst hst2 himem
                        refine ⟨j, Vundef, m2', ?_, .val_inject_undef _, hi, ?_,
                          (fun _ _ _ h => h), scc085_inject_separated_refl _ _ _⟩
                        · apply extcall_memcpy_sem_intro bd2 od2 bs2 os2 m2 bytes2 m2' hal hsz hdiv
                          · intro _
                            rw [has]
                            exact scc085_aligned_area j m1 m2 bs bs2 _ ds al sz hinj hal
                              hpos hdiv hrs (hs hpos) hms
                          · intro _
                            rw [had]
                            exact scc085_aligned_area j m1 m2 bd bd2 _ dd al sz hinj hal
                              hpos hdiv hrd (hd hpos) hmd
                          · change bs2 ≠ bd2 ∨ Ptrofs.unsigned os2 = Ptrofs.unsigned od2 ∨
                              zLe (zAdd (Ptrofs.unsigned os2) sz) (Ptrofs.unsigned od2) ∨
                              zLe (zAdd (Ptrofs.unsigned od2) sz) (Ptrofs.unsigned os2)
                            rw [has, had]
                            exact scc085_disjoint_inject j m1 m2 bs bs2 bd bd2 ds dd
                              _ _ sz hinj hms hmd hrs hrd hpos hdisj
                          · change Mem.loadbytes m2 bs2 (Ptrofs.unsigned os2) sz = _
                            rw [has]
                            exact hl2
                          · change Mem.storebytes m2 bd2 (Ptrofs.unsigned od2) bytes2 = _
                            rw [had]
                            exact hst2
                        · apply scc085_storebytes_unchanged _ m2 m2' bd2 _ bytes2 hst2
                          intro i hi hout
                          apply hout bd dd hmd
                          apply hrd
                          have hlen2 : ZArith.BinInt.Z.of_nat bytes2.length = sz := by
                            rw [← list_forall2_length _ _ _ bytes bytes2 hbytes]
                            exact hlen
                          rw [hlen2] at hi
                          change intOfZ (zAdd (Ptrofs.unsigned od) dd) ≤ intOfZ i ∧
                            intOfZ i < intOfZ (zAdd (zAdd (Ptrofs.unsigned od) dd) sz) at hi
                          change intOfZ (Ptrofs.unsigned od) ≤ intOfZ (zSub i dd) ∧
                            intOfZ (zSub i dd) < intOfZ (zAdd (Ptrofs.unsigned od) sz)
                          simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
                            intOfZ_zOfInt] at hi ⊢
                          omega

private theorem scc085_annot_val_injection (text) (targ) :
    scc085_extcall_injection (extcall_annot_val_sem text targ) := by
  intro ge1 ge2 vargs m1 t vres m1' j m2 vargs2 hsym hcall hinj hargs
  cases hcall with
  | extcall_annot_val_sem_intro varg _ arg hmatch =>
      cases hargs with
      | inject_list_cons _ v2 _ _ hv hnil =>
          cases hnil
          exact ⟨j, v2, m2, extcall_annot_val_sem_intro v2 m2 arg
            (eventval_match_inject j ge1 ge2 hsym arg targ _ v2 hmatch hv),
            hv, hinj, scc085_unchanged_refl _ _, (fun _ _ _ h => h),
            scc085_inject_separated_refl _ _ _⟩

private theorem scc085_external_injection
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) :
    scc085_extcall_injection (Events.external_call xi ef) := by
  cases ef with
  | EF_external name sg =>
      exact scc085_injection_of_properties _ _ (external_functions_properties xi name sg)
  | EF_builtin name sg | EF_runtime name sg =>
      cases hl : lookup_builtin_function name sg with
      | none =>
          simpa only [Events.external_call, builtin_or_external_sem, hl] using
            scc085_injection_of_properties _ _ (external_functions_properties xi name sg)
      | some bf =>
          simpa only [Events.external_call, builtin_or_external_sem, hl] using
            scc085_injection_of_properties _ _ (known_builtin_ok bf)
  | EF_vload chunk => exact scc085_injection_of_properties _ _ (volatile_load_ok chunk)
  | EF_vstore chunk => exact scc085_injection_of_properties _ _ (volatile_store_ok chunk)
  | EF_malloc => exact scc085_malloc_injection
  | EF_free => exact scc085_free_injection
  | EF_memcpy sz al => exact scc085_memcpy_injection sz al
  | EF_annot kind text targs =>
      exact scc085_injection_of_properties _ _ (extcall_annot_ok text targs)
  | EF_annot_val kind text targ => exact scc085_annot_val_injection text targ
  | EF_inline_asm text sg clobbers =>
      exact scc085_injection_of_properties _ _ (inline_assembly_properties xi text sg)
  | EF_debug kind text targs => exact scc085_injection_of_properties _ _ (extcall_debug_ok targs)

theorem external_call_parallel_rule
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    external_call_parallel_ruleStatement := by
  intro xi F V ef ge vargs1 m1 t vres1 m1' m2 j P vargs2 hcall hsep hargs
  have hsymbols := scc085_symbols_inject F V ge j m2 hsep.2.1.1
  obtain ⟨j', vres2, m2', hcall2, hv, hi, hu, hincr, hseparate⟩ :=
    scc085_external_injection xi ef (Genv.to_senv ge) (Genv.to_senv ge)
      vargs1 m1 t vres1 m1' j m2 vargs2 hsymbols hcall hsep.1 hargs
  refine ⟨j', vres2, m2', hcall2, hv, ?_, hincr, hseparate⟩
  apply scc085_call_frame F V ge j j' m1 m1' m2 m2' P hsep hi hu hincr hseparate
  intro b ofs p hb hp
  exact scc085_call_max_perm xi ef (Genv.to_senv ge) vargs1 m1 t vres1 m1'
    b ofs p hcall hb hp

end ExternalCallParallelProof
