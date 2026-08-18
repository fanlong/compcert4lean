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
          cases actual <;> cases p <;> simp [Memtype.perm_order] at h ⊢
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
          cases hy : (PMap.get b m.mem_access) ofs Cur with
          | none => simp [hy] at h
          | some curp =>
            rw [hy] at h
            rw [hx, hy] at hmax
            cases maxp <;> cases curp <;> cases p <;>
                simp [Mem.perm_order'', Memtype.perm_order] at hmax h ⊢

private theorem accessFreeableOfPerm {m : mem} {b : block} {ofs : Z}
    {k : perm_kind} (h : Mem.perm m b ofs k Freeable) :
    (PMap.get b m.mem_access) ofs k = some Freeable := by
  unfold Mem.perm Mem.perm_order' at h
  cases hx : (PMap.get b m.mem_access) ofs k with
  | none => simp [hx] at h
  | some p =>
      rw [hx] at h
      cases p <;> simp [Memtype.perm_order] at h ⊢

private theorem permReadableOfFreeable {m : mem} {b : block} {ofs : Z}
    {k : perm_kind} (h : Mem.perm m b ofs k Freeable) :
    Mem.perm m b ofs k Readable := by
  unfold Mem.perm
  rw [accessFreeableOfPerm h]
  simp [Mem.perm_order', Memtype.perm_order]

private def permissionRank : permission → Nat
  | Freeable => 3
  | Writable => 2
  | Readable => 1
  | Memtype.Nonempty => 0

private def permOrderBool (actual required : permission) : Bool :=
  decide (permissionRank required ≤ permissionRank actual)

private def permBool (m : mem) (b : block) (ofs : Z) (k : perm_kind)
    (p : permission) : Bool :=
  match (PMap.get b m.mem_access) ofs k with
  | none => false
  | some actual => permOrderBool actual p

private def rangePermLoop (m : mem) (b : block) (lo : Z) (k : perm_kind)
    (p : permission) : Nat → Bool
  | 0 => true
  | n + 1 => permBool m b lo k p && rangePermLoop m b (zAdd lo z1) k p n

private def rangePermBool (m : mem) (b : block) (lo hi : Z) (k : perm_kind)
    (p : permission) : Bool :=
  rangePermLoop m b lo k p (ZArith.BinInt.Z.to_nat (zSub hi lo))

private def alignedBool (alignment ofs : Z) : Bool :=
  ZArith.BinInt.Z.eqb (ZArith.BinInt.Z.modulo ofs alignment) z0

private def validAccessBool (m : mem) (chunk : memory_chunk) (b : block) (ofs : Z)
    (p : permission) : Bool :=
  rangePermBool m b ofs (zAdd ofs (size_chunk chunk)) Cur p &&
    alignedBool (align_chunk chunk) ofs

private theorem load_eq (chunk : memory_chunk) (m : mem) (b : block) (ofs : Z) :
    Mem.load chunk m b ofs =
      if validAccessBool m chunk b ofs Readable then
        some (decode_val chunk (Mem.getN (size_chunk_nat chunk) ofs
          (PMap.get b m.mem_contents)))
      else none := by
  rfl'

private theorem chunkSpanNat (chunk : memory_chunk) (ofs : Z) :
    ZArith.BinInt.Z.to_nat (zSub (zAdd ofs (size_chunk chunk)) ofs) =
      size_chunk_nat chunk := by
  rw [show zSub (zAdd ofs (size_chunk chunk)) ofs = size_chunk chunk by
    apply intOfZ_injective
    unfold zSub zAdd ZArith.BinInt.Z.sub ZArith.BinInt.Z.add
    repeat rw [intOfZ_zOfInt]
    omega]
  rfl

private theorem chunkSpanInt (chunk : memory_chunk) (ofs : Z) :
    intOfZ (zAdd ofs (size_chunk chunk)) =
      intOfZ ofs + Int.ofNat (size_chunk_nat chunk) := by
  unfold zAdd ZArith.BinInt.Z.add
  rw [intOfZ_zOfInt]
  congr 1
  cases chunk <;> rfl

private theorem rangePermLoopCongr
    (m1 m2 : mem) (b : block) (root finish current : Z)
    (k : perm_kind) (p : permission) (n : Nat)
    (hAccess : ∀ i, zLe root i ∧ zLt i finish →
      (PMap.get b m2.mem_access) i k = (PMap.get b m1.mem_access) i k)
    (hroot : zLe root current)
    (hfinish : intOfZ finish = intOfZ current + Int.ofNat n) :
    rangePermLoop m2 b current k p n = rangePermLoop m1 b current k p n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih =>
      have hnpos : (0 : Int) < Int.ofNat (n + 1) :=
        Int.ofNat_lt.mpr (Nat.succ_pos n)
      have hlt : zLt current finish := by
        unfold zLt ZArith.BinInt.Z.lt
        omega
      have hAccessCurrent := hAccess current ⟨hroot, hlt⟩
      simp only [rangePermLoop]
      congr 1
      · unfold permBool
        rw [hAccessCurrent]
      · apply ih (zAdd current z1)
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

def sep_swap12 : Prop := sep_swapStatement

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

def sep_swap2 : Prop := sep_swapStatement

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

def sep_proj2Statement : Prop :=
  ∀ P Q m, (sepconj P Q).m_pred m → Q.m_pred m

def sep_pick1 : Prop := sep_proj1Statement

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
    zLe z0 ofs ∧ zLe ofs Ptrofs.max_unsigned ∧
      Mem.valid_access m chunk b ofs Freeable ∧
      ∃ v, Mem.load chunk m b ofs = some v ∧ spec v
  m_footprint := fun b' ofs' =>
    b' = b ∧ zLe ofs ofs' ∧ zLt ofs' (zAdd ofs (size_chunk chunk))
  m_invar := by
    intro m m' hpred hunch
    rcases hpred with ⟨hlo, hhi, hvalid, v, hload, hspec⟩
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
    refine ⟨hlo, hhi, hvalid', v, ?_, hspec⟩
    rw [load_eq] at hload ⊢
    have hLoop :
        rangePermLoop m' b ofs Cur Readable (size_chunk_nat chunk) =
          rangePermLoop m b ofs Cur Readable (size_chunk_nat chunk) :=
      rangePermLoopCongr m m' b ofs (zAdd ofs (size_chunk chunk)) ofs Cur Readable
        (size_chunk_nat chunk) hAccess (by
          unfold zLe ZArith.BinInt.Z.le
          omega) (chunkSpanInt chunk ofs)
    have hGet :
        Mem.getN (size_chunk_nat chunk) ofs (PMap.get b m'.mem_contents) =
          Mem.getN (size_chunk_nat chunk) ofs (PMap.get b m.mem_contents) :=
      getNCongr m m' b ofs (zAdd ofs (size_chunk chunk)) ofs
        (size_chunk_nat chunk) hContents (by
          unfold zLe ZArith.BinInt.Z.le
          omega) (chunkSpanInt chunk ofs)
    unfold validAccessBool rangePermBool at hload ⊢
    rw [chunkSpanNat] at hload ⊢
    rw [hLoop, hGet]
    exact hload
  m_valid := by
    intro m b' ofs' hpred hfoot
    rw [hfoot.1]
    have hvalid := hpred.2.2.1
    exact validBlockOfPerm (hvalid.1 ofs' ⟨hfoot.2.1, hfoot.2.2⟩)

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
      Val.inject_incr j j' ∧
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
  | mk :
      (∀ b, Plt b bound → j b = some (b, z0)) →
      (∀ b1 b2 delta, j b1 = some (b2, delta) → Plt b2 bound → b1 = b2) →
      (∀ id b, Genv.find_symbol ge id = some b → Plt b bound) →
      (∀ b fd, Genv.find_funct_ptr ge b = some fd → Plt b bound) →
      (∀ b gv, Genv.find_var_info ge b = some gv → Plt b bound) →
      globalenv_preserved ge j bound

def globalenv_inject {F V : Type} (ge : Genv.t F V) (j : meminj) : massert where
  m_pred := fun m => ∃ bound, Ple bound m.nextblock ∧ globalenv_preserved ge j bound
  m_footprint := fun _ _ => False
  m_invar := by
    intro m m' hpred hunch
    rcases hpred with ⟨bound, hbound, hge⟩
    exact ⟨bound, Nat.le_trans hbound hunch.unchanged_on_nextblock, hge⟩
  m_valid := by intro _ _ _ _ h; exact False.elim h

def globalenv_inject_preserves_globalsStatement : Prop :=
  ∀ (F V : Type) (ge : Genv.t F V) j m,
    (globalenv_inject ge j).m_pred m → Events.meminj_preserves_globals F V ge j

def globalenv_inject_incrStatement : Prop :=
  ∀ j m0 (F V : Type) (ge : Genv.t F V) m j' P,
    Val.inject_incr j j' →
    Events.inject_separated j j' m0 m →
    (sepconj (globalenv_inject ge j) P).m_pred m →
    (sepconj (globalenv_inject ge j') P).m_pred m

def external_call_parallel_ruleStatement : Prop :=
  ∀ xi (F V : Type) ef (ge : Genv.t F V) vargs1 m1 t vres1 m1' m2 j P vargs2,
    Events.external_call xi ef (Genv.to_senv ge) vargs1 m1 t vres1 m1' →
    (sepconj (minjection j m1) (sepconj (globalenv_inject ge j) P)).m_pred m2 →
    Val.inject_list j vargs1 vargs2 →
    ∃ j' vres2 m2',
      Events.external_call xi ef (Genv.to_senv ge) vargs2 m2 t vres2 m2' ∧
      Val.inject j' vres1 vres2 ∧
      (sepconj (minjection j' m1') (sepconj (globalenv_inject ge j') P)).m_pred m2' ∧
      Val.inject_incr j j' ∧
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
      Val.inject_incr j j' ∧
      j' b1 = some (b2, delta)

end CompCert4Lean.Common.Separation
