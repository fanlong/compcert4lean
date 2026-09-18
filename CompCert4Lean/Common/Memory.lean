import CompCert4Lean.Common.Memdata
import CompCert4Lean.Common.Memtype
import CompCert4Lean.Lib.Intv
import CompCert4Lean.Lib.Maps

/-!
# Concrete memory states

Definition-bearing translation of CompCert's `common/Memory.v`.  Proofs assigned
to later proof migration are exposed as transparent proposition descriptors.
-/

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev block := positive
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zLeb := ZArith.BinInt.Z.leb
private abbrev zLtb := ZArith.BinInt.Z.ltb
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zToNat := ZArith.BinInt.Z.to_nat
private abbrev zDivide := ZArith.BinInt.Z.divide
private abbrev posSucc := PArith.BinPos.Pos.succ
private abbrev posLt := PArith.BinPos.Pos.lt

private theorem intOfZ_add_one (x : Z) :
    intOfZ (zAdd x z1) = intOfZ x + 1 := by
  change intOfZ (ZArith.BinInt.Z.add x z1) = intOfZ x + 1
  change intOfZ (zOfInt (intOfZ x + intOfZ z1)) = intOfZ x + 1
  rw [intOfZ_zOfInt]
  rfl

private def boolOfSumbool {P Q : Prop} (d : Sumbool P Q) : Bool :=
  match d with
  | .left _ => true
  | .right _ => false

private theorem ptreeGetSet0Same {A : Type} (i : positive) (x : A) :
    PTree.get' i (PTree.set0 i x) = some x := by
  induction i <;> simp [PTree.get', PTree.set0, *]

private theorem ptreeGetSet'Same {A : Type} (i : positive) (x : A) (m : PTree.tree' A) :
    PTree.get' i (PTree.set' i x m) = some x := by
  induction i generalizing m <;> cases m <;>
    simp [PTree.get', PTree.set', ptreeGetSet0Same, *]

private theorem ptreeGetSetSame {A : Type} (i : positive) (x : A) (m : PTree.t A) :
    PTree.get i (PTree.set i x m) = some x := by
  cases m <;> simp [PTree.get, PTree.set, ptreeGetSet0Same, ptreeGetSet'Same]

private theorem ptreeGetSet0Other {A : Type} (i j : positive) (x : A) (h : i ≠ j) :
    PTree.get' i (PTree.set0 j x) = none := by
  induction j generalizing i with
  | xH => cases i <;> simp_all [PTree.get', PTree.set0]
  | xI j ih => cases i <;> simp_all [PTree.get', PTree.set0]
  | xO j ih => cases i <;> simp_all [PTree.get', PTree.set0]

private theorem ptreeGetSet'Other {A : Type} (i j : positive) (x : A)
    (m : PTree.tree' A) (h : i ≠ j) :
    PTree.get' i (PTree.set' j x m) = PTree.get' i m := by
  induction j generalizing i m with
  | xH => cases i <;> cases m <;> simp_all [PTree.get', PTree.set']
  | xI j ih =>
      cases i <;> cases m <;>
        simp_all [PTree.get', PTree.set', ptreeGetSet0Other]
  | xO j ih =>
      cases i <;> cases m <;>
        simp_all [PTree.get', PTree.set', ptreeGetSet0Other]

private theorem ptreeGetSetOther {A : Type} (i j : positive) (x : A) (m : PTree.t A)
    (h : i ≠ j) : PTree.get i (PTree.set j x m) = PTree.get i m := by
  cases m <;>
    simp [PTree.get, PTree.set, ptreeGetSet0Other, ptreeGetSet'Other, h]

private theorem pmapGetInit {A : Type} (i : positive) (x : A) :
    PMap.get i (PMap.init x) = x := by
  simp [PMap.get, PMap.init, PTree.get, PTree.empty]

private theorem pmapGetSetSame {A : Type} (i : positive) (x : A) (m : PMap.t A) :
    PMap.get i (PMap.set i x m) = x := by
  simp [PMap.get, PMap.set, ptreeGetSetSame]

private theorem pmapGetSetOther {A : Type} (i j : positive) (x : A) (m : PMap.t A)
    (h : i ≠ j) : PMap.get i (PMap.set j x m) = PMap.get i m := by
  simp [PMap.get, PMap.set, ptreeGetSetOther, h]

private theorem pltSucc (b : positive) : Plt b (posSucc b) := by
  induction b with
  | xH =>
      change 1 < 2
      omega
  | xI b ih =>
      change PArith.BinPos.Pos.to_nat b <
        PArith.BinPos.Pos.to_nat (posSucc b) at ih
      change 2 * PArith.BinPos.Pos.to_nat b + 1 <
        2 * PArith.BinPos.Pos.to_nat (posSucc b)
      omega
  | xO b ih =>
      change 2 * PArith.BinPos.Pos.to_nat b <
        2 * PArith.BinPos.Pos.to_nat b + 1
      omega

namespace Mem

def perm_order' (po : Option permission) (p : permission) : Prop :=
  match po with
  | some p' => perm_order p' p
  | none => False

def perm_order_dec : ∀ p1 p2, Sumbool (perm_order p1 p2) (¬ perm_order p1 p2)
  | Freeable, p => .left (perm_F_any p)
  | Writable, Freeable => .right (by intro h; cases h)
  | Writable, Writable => .left (perm_refl Writable)
  | Writable, Readable => .left perm_W_R
  | Writable, Memtype.Nonempty => .left (perm_any_N Writable)
  | Readable, Freeable => .right (by intro h; cases h)
  | Readable, Writable => .right (by intro h; cases h)
  | Readable, Readable => .left (perm_refl Readable)
  | Readable, Memtype.Nonempty => .left (perm_any_N Readable)
  | Memtype.Nonempty, Freeable => .right (by intro h; cases h)
  | Memtype.Nonempty, Writable => .right (by intro h; cases h)
  | Memtype.Nonempty, Readable => .right (by intro h; cases h)
  | Memtype.Nonempty, Memtype.Nonempty => .left (perm_refl Memtype.Nonempty)

def perm_order'_dec : ∀ op p, Sumbool (perm_order' op p) (¬ perm_order' op p)
  | some p', p => perm_order_dec p' p
  | none, _ => .right (by intro h; exact h)

def perm_order'' (po1 po2 : Option permission) : Prop :=
  match po1, po2 with
  | some p1, some p2 => perm_order p1 p2
  | _, none => True
  | none, some _ => False

structure mem' : Type where
  mem_contents : PMap.t (ZMap.t memval)
  mem_access : PMap.t (Z → perm_kind → Option permission)
  nextblock : block
  access_max : ∀ b ofs,
    perm_order'' ((PMap.get b mem_access) ofs Max) ((PMap.get b mem_access) ofs Cur)
  nextblock_noaccess : ∀ b ofs k,
    ¬ Plt b nextblock → (PMap.get b mem_access) ofs k = none
  contents_default : ∀ b, (PMap.get b mem_contents).1 = Undef

abbrev mem := mem'

export mem' (mem_contents mem_access nextblock access_max nextblock_noaccess contents_default)

def valid_block (m : mem) (b : block) : Prop :=
  Plt b m.nextblock

def perm (m : mem) (b : block) (ofs : Z) (k : perm_kind) (p : permission) : Prop :=
  perm_order' ((PMap.get b m.mem_access) ofs k) p

def perm_dec : ∀ m b ofs k p, Sumbool (perm m b ofs k p) (¬ perm m b ofs k p)
  | m, b, ofs, k, p => perm_order'_dec ((PMap.get b m.mem_access) ofs k) p

def range_perm (m : mem) (b : block) (lo hi : Z) (k : perm_kind)
    (p : permission) : Prop :=
  ∀ ofs, zLe lo ofs ∧ zLt ofs hi → perm m b ofs k p

private theorem range_perm_vacuous (m : mem) (b : block) (lo hi : Z)
    (k : perm_kind) (p : permission) (hge : zLe hi lo) :
    range_perm m b lo hi k p := by
  intro ofs hof
  change intOfZ hi ≤ intOfZ lo at hge
  change intOfZ lo ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi at hof
  exfalso
  omega

private theorem zToNat_sub_succ (lo hi : Z) (hlt : zLt lo hi) :
    zToNat (zSub hi (zAdd lo z1)) + 1 = zToNat (zSub hi lo) := by
  change intOfZ lo < intOfZ hi at hlt
  have hsub_next : intOfZ (zSub hi (zAdd lo z1)) =
      intOfZ hi - (intOfZ lo + 1) := by
    change intOfZ (zOfInt (intOfZ hi - intOfZ (zAdd lo z1))) =
      intOfZ hi - (intOfZ lo + 1)
    rw [intOfZ_zOfInt, intOfZ_add_one]
  have hsub : intOfZ (zSub hi lo) = intOfZ hi - intOfZ lo := by
    change intOfZ (zOfInt (intOfZ hi - intOfZ lo)) = intOfZ hi - intOfZ lo
    rw [intOfZ_zOfInt]
  change Int.toNat (intOfZ (zSub hi (zAdd lo z1))) + 1 =
    Int.toNat (intOfZ (zSub hi lo))
  rw [hsub_next, hsub]
  have hnonneg_next : 0 ≤ intOfZ hi - (intOfZ lo + 1) := by omega
  have hnonneg : 0 ≤ intOfZ hi - intOfZ lo := by omega
  have hn1 := Int.toNat_of_nonneg hnonneg_next
  have hn2 := Int.toNat_of_nonneg hnonneg
  change Int.toNat (intOfZ hi - (intOfZ lo + 1)) + 1 =
    Int.toNat (intOfZ hi - intOfZ lo)
  have hcast1 : (↑(Int.toNat (intOfZ hi - (intOfZ lo + 1))) : Int) =
      intOfZ hi - (intOfZ lo + 1) := hn1
  have hcast2 : (↑(Int.toNat (intOfZ hi - intOfZ lo)) : Int) =
      intOfZ hi - intOfZ lo := hn2
  omega

private def range_perm_dec_aux (m : mem) (b : block) (hi : Z) (k : perm_kind)
    (p : permission) (lo : Z) : (fuel : Nat) →
      zToNat (zSub hi lo) = fuel →
      Sumbool (range_perm m b lo hi k p) (¬ range_perm m b lo hi k p)
  | 0, hfuel =>
      match zlt lo hi with
      | .left hlt =>
          False.elim (by
            have hsub : intOfZ (zSub hi lo) = intOfZ hi - intOfZ lo := by
              change intOfZ (zOfInt (intOfZ hi - intOfZ lo)) = intOfZ hi - intOfZ lo
              rw [intOfZ_zOfInt]
            change Int.toNat (intOfZ (zSub hi lo)) = 0 at hfuel
            rw [hsub] at hfuel
            change intOfZ lo < intOfZ hi at hlt
            have hnonneg : 0 ≤ intOfZ hi - intOfZ lo := by omega
            have hcast := Int.toNat_of_nonneg hnonneg
            change Int.toNat (intOfZ hi - intOfZ lo) = 0 at hfuel
            omega)
      | .right hge => .left (range_perm_vacuous m b lo hi k p hge)
  | n + 1, hfuel =>
      match zlt lo hi with
      | .right hge => .left (range_perm_vacuous m b lo hi k p hge)
      | .left hlt =>
          match perm_dec m b lo k p with
          | .right hn =>
              .right (by
                intro hr
                apply hn
                exact hr lo ⟨by change intOfZ lo ≤ intOfZ lo; omega, hlt⟩)
          | .left hp =>
              have hnext : zToNat (zSub hi (zAdd lo z1)) = n := by
                have hs := zToNat_sub_succ lo hi hlt
                omega
              match range_perm_dec_aux m b hi k p (zAdd lo z1) n hnext with
              | .left hr =>
                  .left (by
                    intro ofs hof
                    change intOfZ lo ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi at hof
                    rcases hof with ⟨hoflo, hofhi⟩
                    by_cases heq : ofs = lo
                    · subst ofs
                      exact hp
                    · apply hr ofs
                      constructor
                      · change intOfZ (zAdd lo z1) ≤ intOfZ ofs
                        rw [intOfZ_add_one]
                        change intOfZ lo ≤ intOfZ ofs at hoflo
                        have hne : intOfZ ofs ≠ intOfZ lo := by
                          intro h
                          apply heq
                          exact intOfZ_injective h
                        omega
                      · exact hofhi)
              | .right hn =>
                  .right (by
                    intro hr
                    apply hn
                    intro ofs hof
                    rcases hof with ⟨hoflo, hofhi⟩
                    change intOfZ (zAdd lo z1) ≤ intOfZ ofs at hoflo
                    rw [intOfZ_add_one] at hoflo
                    change intOfZ ofs < intOfZ hi at hofhi
                    apply hr ofs
                    constructor
                    · change intOfZ lo ≤ intOfZ ofs
                      omega
                    · exact hofhi)

def range_perm_dec : ∀ m b lo hi k p,
    Sumbool (range_perm m b lo hi k p) (¬ range_perm m b lo hi k p) :=
  fun m b lo hi k p => range_perm_dec_aux m b hi k p lo (zToNat (zSub hi lo)) rfl

def valid_access (m : mem) (chunk : memory_chunk) (b : block) (ofs : Z)
    (p : permission) : Prop :=
  range_perm m b ofs (zAdd ofs (size_chunk chunk)) Cur p ∧
    zDivide (align_chunk chunk) ofs

private def zdivide_dec (a b : Z) : Sumbool (zDivide a b) (¬ zDivide a b) := by
  by_cases h : intOfZ b % intOfZ a = 0
  · left
    refine ⟨zOfInt (intOfZ b / intOfZ a), ?_⟩
    apply intOfZ_injective
    change intOfZ b = intOfZ
      (zOfInt (intOfZ a * intOfZ (zOfInt (intOfZ b / intOfZ a))))
    rw [intOfZ_zOfInt, intOfZ_zOfInt]
    exact (Int.mul_ediv_cancel_of_emod_eq_zero h).symm
  · right
    intro hd
    apply h
    apply (Int.dvd_iff_emod_eq_zero).mp
    rcases hd with ⟨q, hq⟩
    refine ⟨intOfZ q, ?_⟩
    have hq' := congrArg intOfZ hq
    change intOfZ b = intOfZ (zOfInt (intOfZ a * intOfZ q)) at hq'
    rw [intOfZ_zOfInt] at hq'
    exact hq'

def valid_access_dec : ∀ m chunk b ofs p,
    Sumbool (valid_access m chunk b ofs p) (¬ valid_access m chunk b ofs p) :=
  fun m chunk b ofs p =>
    match range_perm_dec m b ofs (zAdd ofs (size_chunk chunk)) Cur p with
    | .right hn => .right (by intro h; exact hn h.1)
    | .left hr =>
        match zdivide_dec (align_chunk chunk) ofs with
        | .left hd => .left ⟨hr, hd⟩
        | .right hd => .right (by intro h; exact hd h.2)

def valid_pointer (m : mem) (b : block) (ofs : Z) : Bool :=
  boolOfSumbool (perm_dec m b ofs Cur Nonempty)

def weak_valid_pointer (m : mem) (b : block) (ofs : Z) : Bool :=
  valid_pointer m b ofs || valid_pointer m b (zSub ofs z1)

def empty : mem :=
  { mem_contents := PMap.init (ZMap.init Undef)
    mem_access := PMap.init (fun _ _ => none)
    nextblock := .xH
    access_max := by
      intro b ofs
      rw [pmapGetInit]
      simp [perm_order'']
    nextblock_noaccess := by
      intro b ofs k _
      rw [pmapGetInit]
    contents_default := by
      intro b
      rw [pmapGetInit]
      rfl }

private def inRange (lo hi ofs : Z) : Bool :=
  zLeb lo ofs && zLtb ofs hi

def alloc (m : mem) (lo hi : Z) : mem × block :=
  let fresh := m.nextblock
  let newAccess : Z → perm_kind → Option permission :=
    fun ofs _ => if inRange lo hi ofs then some Freeable else none
  let m' : mem :=
    { mem_contents := PMap.set fresh (ZMap.init Undef) m.mem_contents
      mem_access := PMap.set fresh newAccess m.mem_access
      nextblock := posSucc fresh
      access_max := by
        intro b ofs
        by_cases h : b = fresh
        · subst b
          rw [pmapGetSetSame]
          simp only [newAccess]
          split
          · exact perm_refl Freeable
          · trivial
        · rw [pmapGetSetOther _ _ _ _ h]
          exact m.access_max b ofs
      nextblock_noaccess := by
        intro b ofs k hnot
        by_cases h : b = fresh
        · subst b
          exact False.elim (hnot (pltSucc fresh))
        · rw [pmapGetSetOther _ _ _ _ h]
          apply m.nextblock_noaccess
          intro hlt
          apply hnot
          exact Nat.lt_trans hlt (pltSucc fresh)
      contents_default := by
        intro b
        by_cases h : b = fresh
        · subst b
          rw [pmapGetSetSame]
          rfl
        · rw [pmapGetSetOther _ _ _ _ h]
          exact m.contents_default b }
  (m', fresh)

def unchecked_free (m : mem) (b : block) (lo hi : Z) : mem :=
  let oldAccess := PMap.get b m.mem_access
  let newAccess : Z → perm_kind → Option permission :=
    fun ofs k => if inRange lo hi ofs then none else oldAccess ofs k
  { mem_contents := m.mem_contents
    mem_access := PMap.set b newAccess m.mem_access
    nextblock := m.nextblock
    access_max := by
      intro b' ofs
      by_cases h : b' = b
      · subst b'
        rw [pmapGetSetSame]
        simp only [newAccess]
        split
        · simp [perm_order'']
        · exact m.access_max b ofs
      · rw [pmapGetSetOther _ _ _ _ h]
        exact m.access_max b' ofs
    nextblock_noaccess := by
      intro b' ofs k hnot
      by_cases h : b' = b
      · subst b'
        rw [pmapGetSetSame]
        simp only [newAccess]
        split
        · rfl
        · exact m.nextblock_noaccess b ofs k hnot
      · rw [pmapGetSetOther _ _ _ _ h]
        exact m.nextblock_noaccess b' ofs k hnot
    contents_default := m.contents_default }

def free (m : mem) (b : block) (lo hi : Z) : Option mem :=
  if boolOfSumbool (range_perm_dec m b lo hi Cur Freeable) then
    some (unchecked_free m b lo hi)
  else
    none

def free_list : mem → List (block × Z × Z) → Option mem
  | m, [] => some m
  | m, (b, lo, hi) :: rest =>
      match free m b lo hi with
      | none => none
      | some m' => free_list m' rest

def getN : Nat → Z → ZMap.t memval → List memval
  | 0, _, _ => []
  | n + 1, p, c => ZMap.get p c :: getN n (zAdd p z1) c

def load (chunk : memory_chunk) (m : mem) (b : block) (ofs : Z) : Option val :=
  if boolOfSumbool (valid_access_dec m chunk b ofs Readable) then
    some (decode_val chunk (getN (size_chunk_nat chunk) ofs (PMap.get b m.mem_contents)))
  else
    none

def loadv (chunk : memory_chunk) (m : mem) (addr : val) : Option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => none

def loadbytes (m : mem) (b : block) (ofs n : Z) : Option (List memval) :=
  if boolOfSumbool (range_perm_dec m b ofs (zAdd ofs n) Cur Readable) then
    some (getN (zToNat n) ofs (PMap.get b m.mem_contents))
  else
    none

def setN : List memval → Z → ZMap.t memval → ZMap.t memval
  | [], _, c => c
  | v :: rest, p, c => setN rest (zAdd p z1) (ZMap.set p v c)

private theorem setNDefault (vl : List memval) (p : Z) (c : ZMap.t memval) :
    (setN vl p c).1 = c.1 := by
  induction vl generalizing p c with
  | nil => rfl
  | cons v rest ih =>
      simpa [setN, ZMap.set, PMap.set] using ih (zAdd p z1) (ZMap.set p v c)

def store (chunk : memory_chunk) (m : mem) (b : block) (ofs : Z) (v : val) : Option mem :=
  if boolOfSumbool (valid_access_dec m chunk b ofs Writable) then
    let contents := setN (encode_val chunk v) ofs (PMap.get b m.mem_contents)
    some
      { mem_contents := PMap.set b contents m.mem_contents
        mem_access := m.mem_access
        nextblock := m.nextblock
        access_max := m.access_max
        nextblock_noaccess := m.nextblock_noaccess
        contents_default := by
          intro b'
          by_cases h : b' = b
          · subst b'
            rw [pmapGetSetSame]
            exact (setNDefault _ _ _).trans (m.contents_default b)
          · rw [pmapGetSetOther _ _ _ _ h]
            exact m.contents_default b' }
  else
    none

def storev (chunk : memory_chunk) (m : mem) (addr v : val) : Option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => none

def storebytes (m : mem) (b : block) (ofs : Z) (bytes : List memval) : Option mem :=
  if boolOfSumbool (range_perm_dec m b ofs (zAdd ofs (zOfNat bytes.length)) Cur Writable) then
    let contents := setN bytes ofs (PMap.get b m.mem_contents)
    some
      { mem_contents := PMap.set b contents m.mem_contents
        mem_access := m.mem_access
        nextblock := m.nextblock
        access_max := m.access_max
        nextblock_noaccess := m.nextblock_noaccess
        contents_default := by
          intro b'
          by_cases h : b' = b
          · subst b'
            rw [pmapGetSetSame]
            exact (setNDefault _ _ _).trans (m.contents_default b)
          · rw [pmapGetSetOther _ _ _ _ h]
            exact m.contents_default b' }
  else
    none

def drop_perm (m : mem) (b : block) (lo hi : Z) (p : permission) : Option mem :=
  match range_perm_dec m b lo hi Cur Freeable with
  | .left hRange =>
    let oldAccess := PMap.get b m.mem_access
    let newAccess : Z → perm_kind → Option permission :=
      fun ofs k =>
        if inRange lo hi ofs then some p else oldAccess ofs k
    some
      { mem_contents := m.mem_contents
        mem_access := PMap.set b newAccess m.mem_access
        nextblock := m.nextblock
        access_max := by
          intro b' ofs
          by_cases h : b' = b
          · subst b'
            rw [pmapGetSetSame]
            simp only [newAccess]
            split
            · exact perm_refl p
            · exact m.access_max b ofs
          · rw [pmapGetSetOther _ _ _ _ h]
            exact m.access_max b' ofs
        nextblock_noaccess := by
          intro b' ofs k hnot
          by_cases h : b' = b
          · subst b'
            rw [pmapGetSetSame]
            simp only [newAccess]
            have oldNone := m.nextblock_noaccess b ofs k hnot
            change oldAccess ofs k = none at oldNone
            split <;> rename_i hIn
            · exfalso
              have hBounds : zLe lo ofs ∧ zLt ofs hi := by
                change intOfZ lo ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi
                simpa [inRange, ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb] using hIn
              have hPerm := hRange ofs hBounds
              unfold perm at hPerm
              change perm_order' (oldAccess ofs Cur) Freeable at hPerm
              have oldCurNone := m.nextblock_noaccess b ofs Cur hnot
              change oldAccess ofs Cur = none at oldCurNone
              rw [oldCurNone] at hPerm
              exact hPerm
            · exact oldNone
          · rw [pmapGetSetOther _ _ _ _ h]
            exact m.nextblock_noaccess b' ofs k hnot
        contents_default := m.contents_default }
  | .right _ => none

def compat_pointer_chunks (chunk1 chunk2 : memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | Mint32, Mint32 | Mint32, Many32 | Many32, Mint32 | Many32, Many32 => True
  | Mint64, Mint64 | Mint64, Many64 | Many64, Mint64 | Many64, Many64 => True
  | _, _ => False

structure mem_inj (f : meminj) (m1 m2 : mem) : Prop where
  mi_perm : ∀ b1 b2 delta ofs k p,
    f b1 = some (b2, delta) →
    perm m1 b1 ofs k p →
    perm m2 b2 (zAdd ofs delta) k p
  mi_align : ∀ b1 b2 delta chunk ofs p,
    f b1 = some (b2, delta) →
    range_perm m1 b1 ofs (zAdd ofs (size_chunk chunk)) Max p →
    zDivide (align_chunk chunk) delta
  mi_memval : ∀ b1 ofs b2 delta,
    f b1 = some (b2, delta) →
    perm m1 b1 ofs Cur Readable →
    memval_inject f
      (ZMap.get ofs (PMap.get b1 m1.mem_contents))
      (ZMap.get (zAdd ofs delta) (PMap.get b2 m2.mem_contents))

export mem_inj (mi_perm mi_align mi_memval)

def meminj_no_overlap (f : meminj) (m : mem) : Prop :=
  ∀ b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
    b1 ≠ b2 →
    f b1 = some (b1', delta1) →
    f b2 = some (b2', delta2) →
    perm m b1 ofs1 Max Memtype.Nonempty →
    perm m b2 ofs2 Max Memtype.Nonempty →
    b1' ≠ b2' ∨ zAdd ofs1 delta1 ≠ zAdd ofs2 delta2

def inj_offset_aligned (delta size : Z) : Prop :=
  ∀ chunk, zLe (size_chunk chunk) size → zDivide (align_chunk chunk) delta

structure extends' (m1 m2 : mem) : Prop where
  mext_next : m1.nextblock = m2.nextblock
  mext_inj : mem_inj inject_id m1 m2
  mext_perm_inv : ∀ b ofs k p,
    perm m2 b ofs k p →
    perm m1 b ofs k p ∨ ¬ perm m1 b ofs Max Memtype.Nonempty

export extends' (mext_next mext_inj mext_perm_inv)

abbrev «extends» := extends'

structure inject' (f : meminj) (m1 m2 : mem) : Prop where
  mi_inj : mem_inj f m1 m2
  mi_freeblocks : ∀ b, ¬ valid_block m1 b → f b = none
  mi_mappedblocks : ∀ b b' delta,
    f b = some (b', delta) → valid_block m2 b'
  mi_no_overlap : meminj_no_overlap f m1
  mi_representable : ∀ b b' delta ofs,
    f b = some (b', delta) →
    (perm m1 b (Ptrofs.unsigned ofs) Max Memtype.Nonempty ∨
      perm m1 b (zSub (Ptrofs.unsigned ofs) z1) Max Memtype.Nonempty) →
    zLe z0 delta ∧
      zLe z0 (zAdd (Ptrofs.unsigned ofs) delta) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) delta) Ptrofs.max_unsigned
  mi_perm_inv : ∀ b1 ofs b2 delta k p,
    f b1 = some (b2, delta) →
    perm m2 b2 (zAdd ofs delta) k p →
    perm m1 b1 ofs k p ∨ ¬ perm m1 b1 ofs Max Memtype.Nonempty

export inject' (mi_inj mi_freeblocks mi_mappedblocks mi_no_overlap mi_representable mi_perm_inv)

abbrev inject := inject'

def flat_inj (thr : block) : meminj :=
  fun b =>
    match plt b thr with
    | .left _ => some (b, z0)
    | .right _ => none

def inject_neutral (thr : block) (m : mem) : Prop :=
  mem_inj (flat_inj thr) m m

structure unchanged_on (P : block → Z → Prop) (m_before m_after : mem) : Prop where
  unchanged_on_nextblock : Ple m_before.nextblock m_after.nextblock
  unchanged_on_perm : ∀ b ofs k p,
    P b ofs → valid_block m_before b →
      (perm m_before b ofs k p ↔ perm m_after b ofs k p)
  unchanged_on_contents : ∀ b ofs,
    P b ofs → perm m_before b ofs Cur Readable →
      ZMap.get ofs (PMap.get b m_after.mem_contents) =
        ZMap.get ofs (PMap.get b m_before.mem_contents)

export unchanged_on (unchanged_on_nextblock unchanged_on_perm unchanged_on_contents)

/-! ## Exact statement descriptors for later proof migration -/

def mkmem_extStatement : Prop :=
  ∀ (cont1 cont2 : PMap.t (ZMap.t memval))
    (acc1 acc2 : PMap.t (Z → perm_kind → Option permission))
    (next1 next2 : block)
    (a1 : ∀ b ofs, perm_order'' ((PMap.get b acc1) ofs Max) ((PMap.get b acc1) ofs Cur))
    (a2 : ∀ b ofs, perm_order'' ((PMap.get b acc2) ofs Max) ((PMap.get b acc2) ofs Cur))
    (b1 : ∀ b ofs k, ¬ Plt b next1 → (PMap.get b acc1) ofs k = none)
    (b2 : ∀ b ofs k, ¬ Plt b next2 → (PMap.get b acc2) ofs k = none)
    (c1 : ∀ b, (PMap.get b cont1).1 = Undef)
    (c2 : ∀ b, (PMap.get b cont2).1 = Undef),
    cont1 = cont2 → acc1 = acc2 → next1 = next2 →
      mem'.mk cont1 acc1 next1 a1 b1 c1 = mem'.mk cont2 acc2 next2 a2 b2 c2

def valid_not_valid_diffStatement : Prop :=
  ∀ m b b', valid_block m b → ¬ valid_block m b' → b ≠ b'

def perm_impliesStatement : Prop :=
  ∀ m b ofs k p1 p2,
    perm m b ofs k p1 → perm_order p1 p2 → perm m b ofs k p2

def perm_cur_maxStatement : Prop :=
  ∀ m b ofs p, perm m b ofs Cur p → perm m b ofs Max p

def perm_curStatement : Prop :=
  ∀ m b ofs k p, perm m b ofs Cur p → perm m b ofs k p

def perm_maxStatement : Prop :=
  ∀ m b ofs k p, perm m b ofs k p → perm m b ofs Max p

def perm_valid_blockStatement : Prop :=
  ∀ m b ofs k p, perm m b ofs k p → valid_block m b

def perm_order_decStatement : Type :=
  ∀ p1 p2, Sumbool (perm_order p1 p2) (¬ perm_order p1 p2)

def perm_order'_decStatement : Type :=
  ∀ op p, Sumbool (perm_order' op p) (¬ perm_order' op p)

def perm_decStatement : Type :=
  ∀ m b ofs k p, Sumbool (perm m b ofs k p) (¬ perm m b ofs k p)

def range_perm_impliesStatement : Prop :=
  ∀ m b lo hi k p1 p2,
    range_perm m b lo hi k p1 → perm_order p1 p2 → range_perm m b lo hi k p2

def range_perm_maxStatement : Prop :=
  ∀ m b lo hi k p,
    range_perm m b lo hi k p → range_perm m b lo hi Max p

def range_perm_decStatement : Type :=
  ∀ m b lo hi k p,
    Sumbool (range_perm m b lo hi k p) (¬ range_perm m b lo hi k p)

def valid_access_impliesStatement : Prop :=
  ∀ m chunk b ofs p1 p2,
    valid_access m chunk b ofs p1 → perm_order p1 p2 → valid_access m chunk b ofs p2

def valid_access_compatStatement : Prop :=
  ∀ m chunk1 chunk2 b ofs p,
    size_chunk chunk1 = size_chunk chunk2 →
    zLe (align_chunk chunk2) (align_chunk chunk1) →
    valid_access m chunk1 b ofs p →
    valid_access m chunk2 b ofs p

def valid_access_decStatement : Type :=
  ∀ m chunk b ofs p,
    Sumbool (valid_access m chunk b ofs p) (¬ valid_access m chunk b ofs p)

def valid_pointer_nonempty_permStatement : Prop :=
  ∀ m b ofs,
    valid_pointer m b ofs = true ↔ perm m b ofs Cur Memtype.Nonempty

def valid_pointer_valid_accessStatement : Prop :=
  ∀ m b ofs,
    valid_pointer m b ofs = true ↔ valid_access m Mint8unsigned b ofs Memtype.Nonempty

def weak_valid_pointer_specStatement : Prop :=
  ∀ m b ofs,
    weak_valid_pointer m b ofs = true ↔
      valid_pointer m b ofs = true ∨ valid_pointer m b (zSub ofs z1) = true

def valid_pointer_impliesStatement : Prop :=
  ∀ m b ofs,
    valid_pointer m b ofs = true → weak_valid_pointer m b ofs = true

def setN_otherStatement : Prop :=
  ∀ vl c p q,
    (∀ r, zLe p r ∧ zLt r (zAdd p (zOfNat vl.length)) → r ≠ q) →
      ZMap.get q (setN vl p c) = ZMap.get q c

def setN_outsideStatement : Prop :=
  ∀ vl c p q,
    zLt q p ∨ zLe (zAdd p (zOfNat vl.length)) q →
      ZMap.get q (setN vl p c) = ZMap.get q c

def getN_setN_sameStatement : Prop :=
  ∀ vl p c, getN vl.length p (setN vl p c) = vl

def getN_extenStatement : Prop :=
  ∀ c1 c2 n p,
    (∀ i, zLe p i ∧ zLt i (zAdd p (zOfNat n)) → ZMap.get i c1 = ZMap.get i c2) →
      getN n p c1 = getN n p c2

def getN_setN_disjointStatement : Prop :=
  ∀ vl q c n p,
    CompCert4Lean.Lib.Intv.disjoint (p, zAdd p (zOfNat n))
      (q, zAdd q (zOfNat vl.length)) →
      getN n p (setN vl q c) = getN n p c

def getN_setN_outsideStatement : Prop :=
  ∀ vl q c n p,
    zLe (zAdd p (zOfNat n)) q ∨ zLe (zAdd q (zOfNat vl.length)) p →
      getN n p (setN vl q c) = getN n p c

def setN_defaultStatement : Prop :=
  ∀ vl q c, (setN vl q c).1 = c.1

def nextblock_emptyStatement : Prop :=
  empty.nextblock = .xH

def valid_access_loadStatement : Prop :=
  ∀ m chunk b ofs,
    valid_access m chunk b ofs Readable → ∃ v, load chunk m b ofs = some v

def load_valid_accessStatement : Prop :=
  ∀ m chunk b ofs v,
    load chunk m b ofs = some v → valid_access m chunk b ofs Readable

def load_resultStatement : Prop :=
  ∀ chunk m b ofs v,
    load chunk m b ofs = some v →
      v = decode_val chunk (getN (size_chunk_nat chunk) ofs (PMap.get b m.mem_contents))

def load_typeStatement : Prop :=
  ∀ m chunk b ofs v,
    load chunk m b ofs = some v → Val.has_type v (type_of_chunk chunk)

def load_xtypeStatement : Prop :=
  ∀ m chunk b ofs v,
    load chunk m b ofs = some v → Val.has_rettype v (xtype_of_chunk chunk)

def load_castStatement : Prop :=
  ∀ m chunk b ofs v,
    load chunk m b ofs = some v →
      match chunk with
      | Mbool => v = Val.norm_bool v
      | Mint8signed => v = Val.sign_ext (zOfNat 8) v
      | Mint8unsigned => v = Val.zero_ext (zOfNat 8) v
      | Mint16signed => v = Val.sign_ext (zOfNat 16) v
      | Mint16unsigned => v = Val.zero_ext (zOfNat 16) v
      | _ => True

def load_bool_int8_unsignedStatement : Prop :=
  ∀ m b ofs,
    load Mbool m b ofs = option_map Val.norm_bool (load Mint8unsigned m b ofs)

def loadbytes_range_permStatement : Prop :=
  ∀ m b ofs len bytes,
    loadbytes m b ofs len = some bytes →
      range_perm m b ofs (zAdd ofs len) Cur Readable

def loadbytes_loadStatement : Prop :=
  ∀ chunk m b ofs bytes,
    loadbytes m b ofs (size_chunk chunk) = some bytes →
    zDivide (align_chunk chunk) ofs →
    load chunk m b ofs = some (decode_val chunk bytes)

def load_loadbytesStatement : Prop :=
  ∀ chunk m b ofs v,
    load chunk m b ofs = some v →
      ∃ bytes, loadbytes m b ofs (size_chunk chunk) = some bytes ∧
        v = decode_val chunk bytes

def getN_lengthStatement : Prop :=
  ∀ c n p, (getN n p c).length = n

def loadbytes_lengthStatement : Prop :=
  ∀ m b ofs n bytes,
    loadbytes m b ofs n = some bytes → bytes.length = zToNat n

def loadbytes_emptyStatement : Prop :=
  ∀ m b ofs n, zLe n z0 → loadbytes m b ofs n = some []

def getN_concatStatement : Prop :=
  ∀ c n1 n2 p,
    getN (n1 + n2) p c = getN n1 p c ++ getN n2 (zAdd p (zOfNat n1)) c

def loadbytes_concatStatement : Prop :=
  ∀ m b ofs n1 n2 bytes1 bytes2,
    loadbytes m b ofs n1 = some bytes1 →
    loadbytes m b (zAdd ofs n1) n2 = some bytes2 →
    zLe z0 n1 → zLe z0 n2 →
    loadbytes m b ofs (zAdd n1 n2) = some (bytes1 ++ bytes2)

def loadbytes_splitStatement : Prop :=
  ∀ m b ofs n1 n2 bytes,
    loadbytes m b ofs (zAdd n1 n2) = some bytes →
    zLe z0 n1 → zLe z0 n2 →
    ∃ bytes1 bytes2,
      loadbytes m b ofs n1 = some bytes1 ∧
      loadbytes m b (zAdd ofs n1) n2 = some bytes2 ∧
      bytes = bytes1 ++ bytes2

def load_int64_splitStatement : Prop :=
  ∀ m b ofs v,
    load Mint64 m b ofs = some v →
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∃ v1 v2,
      load Mint32 m b ofs =
        some (if CompCert4Lean.X86_64.Archi.big_endian then v1 else v2) ∧
      load Mint32 m b (zAdd ofs (zOfNat 4)) =
        some (if CompCert4Lean.X86_64.Archi.big_endian then v2 else v1) ∧
      Val.lessdef v (Val.longofwords v1 v2)

def addressing_int64_splitStatement : Prop :=
  ∀ i : Ptrofs.int,
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    zDivide (zOfNat 8) (Ptrofs.unsigned i) →
    Ptrofs.unsigned (Ptrofs.add i
      (Ptrofs.of_int (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 4)))) =
      zAdd (Ptrofs.unsigned i) (zOfNat 4)

def loadv_int64_splitStatement : Prop :=
  ∀ m a v,
    loadv Mint64 m a = some v →
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∃ v1 v2,
      loadv Mint32 m a =
        some (if CompCert4Lean.X86_64.Archi.big_endian then v1 else v2) ∧
      loadv Mint32 m (Val.add a
        (Vint (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 4)))) =
        some (if CompCert4Lean.X86_64.Archi.big_endian then v2 else v1) ∧
      Val.lessdef v (Val.longofwords v1 v2)

def valid_access_storeStatement :=
  ∀ m1 chunk b ofs v,
    valid_access m1 chunk b ofs Writable →
      Subtype (fun m2 : mem => store chunk m1 b ofs v = some m2)

def store_accessStatement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 → m2.mem_access = m1.mem_access

def store_mem_contentsStatement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
      m2.mem_contents =
        PMap.set b (setN (encode_val chunk v) ofs (PMap.get b m1.mem_contents))
          m1.mem_contents

def perm_store_1Statement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
    ∀ b' ofs' k p, perm m1 b' ofs' k p → perm m2 b' ofs' k p

def perm_store_2Statement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
    ∀ b' ofs' k p, perm m2 b' ofs' k p → perm m1 b' ofs' k p

def nextblock_storeStatement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 → m2.nextblock = m1.nextblock

def store_valid_block_1Statement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
    ∀ b', valid_block m1 b' → valid_block m2 b'

def store_valid_access_1Statement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
    ∀ chunk' b' ofs' p,
      valid_access m1 chunk' b' ofs' p → valid_access m2 chunk' b' ofs' p

def store_valid_access_3Statement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 → valid_access m1 chunk b ofs Writable

def load_store_similarStatement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
    ∀ chunk',
      size_chunk chunk' = size_chunk chunk →
      zLe (align_chunk chunk') (align_chunk chunk) →
      ∃ v', load chunk' m2 b ofs = some v' ∧
        decode_encode_val v chunk chunk' v'

def load_store_similar_2Statement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
    ∀ chunk',
      size_chunk chunk' = size_chunk chunk →
      zLe (align_chunk chunk') (align_chunk chunk) →
      type_of_chunk chunk' = type_of_chunk chunk →
      load chunk' m2 b ofs = some (Val.load_result chunk' v)

def load_store_sameStatement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
      load chunk m2 b ofs = some (Val.load_result chunk v)

def load_store_otherStatement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
    ∀ chunk' b' ofs',
      b' ≠ b ∨
      zLe (zAdd ofs' (size_chunk chunk')) ofs ∨
      zLe (zAdd ofs (size_chunk chunk)) ofs' →
      load chunk' m2 b' ofs' = load chunk' m1 b' ofs'

def loadbytes_store_sameStatement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
      loadbytes m2 b ofs (size_chunk chunk) = some (encode_val chunk v)

def loadbytes_store_otherStatement : Prop :=
  ∀ chunk m1 b ofs v m2,
    store chunk m1 b ofs v = some m2 →
    ∀ b' ofs' n,
      b' ≠ b ∨ zLe n z0 ∨
      zLe (zAdd ofs' n) ofs ∨
      zLe (zAdd ofs (size_chunk chunk)) ofs' →
      loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n

def setN_inStatement : Prop :=
  ∀ vl p q c,
    zLe p q ∧ zLt q (zAdd p (zOfNat vl.length)) →
      ZMap.get q (setN vl p c) ∈ vl

def getN_inStatement : Prop :=
  ∀ c q n p,
    zLe p q ∧ zLt q (zAdd p (zOfNat n)) → ZMap.get q c ∈ getN n p c

def load_store_overlapStatement : Prop :=
  ∀ chunk m1 b ofs v m2 chunk' ofs' v',
    store chunk m1 b ofs v = some m2 →
    load chunk' m2 b ofs' = some v' →
    zLt ofs (zAdd ofs' (size_chunk chunk')) →
    zLt ofs' (zAdd ofs (size_chunk chunk)) →
    ∃ mv1 mvl mv1' mvl',
      shape_encoding chunk v (mv1 :: mvl) ∧
      shape_decoding chunk' (mv1' :: mvl') v' ∧
      ((ofs' = ofs ∧ mv1' = mv1) ∨
       (zLt ofs ofs' ∧ mv1' ∈ mvl) ∨
       (zLt ofs' ofs ∧ mv1 ∈ mvl'))

def compat_pointer_chunks_trueStatement : Prop :=
  ∀ chunk1 chunk2,
    (chunk1 = Mint32 ∨ chunk1 = Many32 ∨ chunk1 = Mint64 ∨ chunk1 = Many64) →
    (chunk2 = Mint32 ∨ chunk2 = Many32 ∨ chunk2 = Mint64 ∨ chunk2 = Many64) →
    quantity_chunk chunk1 = quantity_chunk chunk2 →
    compat_pointer_chunks chunk1 chunk2

def load_pointer_storeStatement : Prop :=
  ∀ chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
    store chunk m1 b ofs v = some m2 →
    load chunk' m2 b' ofs' = some (Vptr v_b v_o) →
    (v = Vptr v_b v_o ∧ compat_pointer_chunks chunk chunk' ∧ b' = b ∧ ofs' = ofs) ∨
    (b' ≠ b ∨
      zLe (zAdd ofs' (size_chunk chunk')) ofs ∨
      zLe (zAdd ofs (size_chunk chunk)) ofs')

def store_similar_chunksStatement : Prop :=
  ∀ chunk1 chunk2 v1 v2 m b ofs,
    encode_val chunk1 v1 = encode_val chunk2 v2 →
    align_chunk chunk1 = align_chunk chunk2 →
    store chunk1 m b ofs v1 = store chunk2 m b ofs v2

def store_bool_unsigned_8Statement : Prop :=
  ∀ m b ofs v, store Mbool m b ofs v = store Mint8unsigned m b ofs v

def store_signed_unsigned_8Statement : Prop :=
  ∀ m b ofs v, store Mint8signed m b ofs v = store Mint8unsigned m b ofs v

def store_signed_unsigned_16Statement : Prop :=
  ∀ m b ofs v, store Mint16signed m b ofs v = store Mint16unsigned m b ofs v

def range_perm_storebytesStatement :=
  ∀ m1 b ofs bytes,
    range_perm m1 b ofs (zAdd ofs (zOfNat bytes.length)) Cur Writable →
      Subtype (fun m2 : mem => storebytes m1 b ofs bytes = some m2)

def storebytes_storeStatement : Prop :=
  ∀ m1 b ofs chunk v m2,
    storebytes m1 b ofs (encode_val chunk v) = some m2 →
    zDivide (align_chunk chunk) ofs →
    store chunk m1 b ofs v = some m2

def store_storebytesStatement : Prop :=
  ∀ m1 b ofs chunk v m2,
    store chunk m1 b ofs v = some m2 →
      storebytes m1 b ofs (encode_val chunk v) = some m2

def storebytes_accessStatement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 → m2.mem_access = m1.mem_access

def storebytes_mem_contentsStatement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 →
      m2.mem_contents =
        PMap.set b (setN bytes ofs (PMap.get b m1.mem_contents)) m1.mem_contents

def perm_storebytes_1Statement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 →
    ∀ b' ofs' k p, perm m1 b' ofs' k p → perm m2 b' ofs' k p

def perm_storebytes_2Statement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 →
    ∀ b' ofs' k p, perm m2 b' ofs' k p → perm m1 b' ofs' k p

def nextblock_storebytesStatement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 → m2.nextblock = m1.nextblock

def storebytes_valid_block_1Statement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 →
    ∀ b', valid_block m1 b' → valid_block m2 b'

def storebytes_range_permStatement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 →
      range_perm m1 b ofs (zAdd ofs (zOfNat bytes.length)) Cur Writable

def loadbytes_storebytes_sameStatement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 →
      loadbytes m2 b ofs (zOfNat bytes.length) = some bytes

def loadbytes_storebytes_disjointStatement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 →
    ∀ b' ofs' len,
      zLe z0 len →
      (b' ≠ b ∨ CompCert4Lean.Lib.Intv.disjoint
        (ofs', zAdd ofs' len) (ofs, zAdd ofs (zOfNat bytes.length))) →
      loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len

def loadbytes_storebytes_otherStatement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 →
    ∀ b' ofs' len,
      zLe z0 len →
      (b' ≠ b ∨ zLe (zAdd ofs' len) ofs ∨
        zLe (zAdd ofs (zOfNat bytes.length)) ofs') →
      loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len

def load_storebytes_otherStatement : Prop :=
  ∀ m1 b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 →
    ∀ chunk b' ofs',
      (b' ≠ b ∨ zLe (zAdd ofs' (size_chunk chunk)) ofs ∨
        zLe (zAdd ofs (zOfNat bytes.length)) ofs') →
      load chunk m2 b' ofs' = load chunk m1 b' ofs'

def setN_concatStatement : Prop :=
  ∀ bytes1 bytes2 ofs c,
    setN (bytes1 ++ bytes2) ofs c =
      setN bytes2 (zAdd ofs (zOfNat bytes1.length)) (setN bytes1 ofs c)

def storebytes_concatStatement : Prop :=
  ∀ m b ofs bytes1 m1 bytes2 m2,
    storebytes m b ofs bytes1 = some m1 →
    storebytes m1 b (zAdd ofs (zOfNat bytes1.length)) bytes2 = some m2 →
    storebytes m b ofs (bytes1 ++ bytes2) = some m2

def storebytes_splitStatement : Prop :=
  ∀ m b ofs bytes1 bytes2 m2,
    storebytes m b ofs (bytes1 ++ bytes2) = some m2 →
    ∃ m1, storebytes m b ofs bytes1 = some m1 ∧
      storebytes m1 b (zAdd ofs (zOfNat bytes1.length)) bytes2 = some m2

def store_int64_splitStatement : Prop :=
  ∀ m b ofs v m',
    store Mint64 m b ofs v = some m' →
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∃ m1,
      store Mint32 m b ofs
        (if CompCert4Lean.X86_64.Archi.big_endian then Val.hiword v else Val.loword v) = some m1 ∧
      store Mint32 m1 b (zAdd ofs (zOfNat 4))
        (if CompCert4Lean.X86_64.Archi.big_endian then Val.loword v else Val.hiword v) = some m'

def storev_int64_splitStatement : Prop :=
  ∀ m a v m',
    storev Mint64 m a v = some m' →
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∃ m1,
      storev Mint32 m a
        (if CompCert4Lean.X86_64.Archi.big_endian then Val.hiword v else Val.loword v) = some m1 ∧
      storev Mint32 m1 (Val.add a
        (Vint (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 4))))
        (if CompCert4Lean.X86_64.Archi.big_endian then Val.loword v else Val.hiword v) = some m'

def nextblock_allocStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) → m2.nextblock = posSucc m1.nextblock

def alloc_resultStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) → b = m1.nextblock

def valid_block_allocStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ b', valid_block m1 b' → valid_block m2 b'

def fresh_block_allocStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) → ¬ valid_block m1 b

def valid_new_blockStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) → valid_block m2 b

def perm_alloc_1Statement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ b' ofs k p, perm m1 b' ofs k p → perm m2 b' ofs k p

def perm_alloc_2Statement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ ofs k, zLe lo ofs ∧ zLt ofs hi → perm m2 b ofs k Freeable

def perm_alloc_invStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ b' ofs k p,
      perm m2 b' ofs k p →
      match eq_block b' b with
      | .left _ => zLe lo ofs ∧ zLt ofs hi
      | .right _ => perm m1 b' ofs k p

def perm_alloc_3Statement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ ofs k p, perm m2 b ofs k p → zLe lo ofs ∧ zLt ofs hi

def perm_alloc_4Statement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ b' ofs k p, perm m2 b' ofs k p → b' ≠ b → perm m1 b' ofs k p

def valid_access_alloc_invStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ chunk b' ofs p,
      valid_access m2 chunk b' ofs p →
      match eq_block b' b with
      | .left _ =>
          zLe lo ofs ∧ zLe (zAdd ofs (size_chunk chunk)) hi ∧
            zDivide (align_chunk chunk) ofs
      | .right _ => valid_access m1 chunk b' ofs p

def load_alloc_unchangedStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ chunk b' ofs,
      valid_block m1 b' → load chunk m2 b' ofs = load chunk m1 b' ofs

def load_alloc_otherStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ chunk b' ofs v,
      load chunk m1 b' ofs = some v → load chunk m2 b' ofs = some v

def load_alloc_sameStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ chunk ofs v, load chunk m2 b ofs = some v → v = Vundef

def load_alloc_same'Statement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ chunk ofs,
      zLe lo ofs → zLe (zAdd ofs (size_chunk chunk)) hi →
      zDivide (align_chunk chunk) ofs →
      load chunk m2 b ofs = some Vundef

def loadbytes_alloc_unchangedStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ b' ofs n,
      valid_block m1 b' → loadbytes m2 b' ofs n = loadbytes m1 b' ofs n

def loadbytes_alloc_sameStatement : Prop :=
  ∀ m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) →
    ∀ n ofs bytes byte,
      loadbytes m2 b ofs n = some bytes → byte ∈ bytes → byte = Undef

def range_perm_freeStatement :=
  ∀ m1 b lo hi,
    range_perm m1 b lo hi Cur Freeable →
      Subtype (fun m2 : mem => free m1 b lo hi = some m2)

def free_range_permStatement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 → range_perm m1 bf lo hi Cur Freeable

def free_resultStatement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 → m2 = unchecked_free m1 bf lo hi

def nextblock_freeStatement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 → m2.nextblock = m1.nextblock

def perm_free_1Statement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 →
    ∀ b ofs k p,
      (b ≠ bf ∨ zLt ofs lo ∨ zLe hi ofs) →
      perm m1 b ofs k p → perm m2 b ofs k p

def perm_free_2Statement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 →
    ∀ ofs k p, zLe lo ofs ∧ zLt ofs hi → ¬ perm m2 bf ofs k p

def perm_free_3Statement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 →
    ∀ b ofs k p, perm m2 b ofs k p → perm m1 b ofs k p

def perm_free_invStatement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 →
    ∀ b ofs k p,
      perm m1 b ofs k p →
      (b = bf ∧ zLe lo ofs ∧ zLt ofs hi) ∨ perm m2 b ofs k p

def valid_access_free_1Statement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 →
    ∀ chunk b ofs p,
      valid_access m1 chunk b ofs p →
      (b ≠ bf ∨ zLe hi lo ∨ zLe (zAdd ofs (size_chunk chunk)) lo ∨ zLe hi ofs) →
      valid_access m2 chunk b ofs p

def valid_access_free_inv_1Statement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 →
    ∀ chunk b ofs p,
      valid_access m2 chunk b ofs p → valid_access m1 chunk b ofs p

def load_freeStatement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 →
    ∀ chunk b ofs,
      (b ≠ bf ∨ zLe hi lo ∨ zLe (zAdd ofs (size_chunk chunk)) lo ∨ zLe hi ofs) →
      load chunk m2 b ofs = load chunk m1 b ofs

def loadbytes_free_2Statement : Prop :=
  ∀ m1 bf lo hi m2,
    free m1 bf lo hi = some m2 →
    ∀ b ofs n bytes,
      loadbytes m2 b ofs n = some bytes → loadbytes m1 b ofs n = some bytes

def range_perm_drop_1Statement : Prop :=
  ∀ m b lo hi p m',
    drop_perm m b lo hi p = some m' → range_perm m b lo hi Cur Freeable

def range_perm_drop_2Statement :=
  ∀ m b lo hi p,
    range_perm m b lo hi Cur Freeable →
      Subtype (fun m' : mem => drop_perm m b lo hi p = some m')

def nextblock_dropStatement : Prop :=
  ∀ m b lo hi p m',
    drop_perm m b lo hi p = some m' → m'.nextblock = m.nextblock

def perm_drop_1Statement : Prop :=
  ∀ m b lo hi p m',
    drop_perm m b lo hi p = some m' →
    ∀ ofs k, zLe lo ofs ∧ zLt ofs hi → perm m' b ofs k p

def perm_drop_2Statement : Prop :=
  ∀ m b lo hi p m',
    drop_perm m b lo hi p = some m' →
    ∀ ofs k p',
      zLe lo ofs ∧ zLt ofs hi → perm m' b ofs k p' → perm_order p p'

def perm_drop_3Statement : Prop :=
  ∀ m b lo hi p m',
    drop_perm m b lo hi p = some m' →
    ∀ b' ofs k p',
      (b' ≠ b ∨ zLt ofs lo ∨ zLe hi ofs) →
      perm m b' ofs k p' → perm m' b' ofs k p'

def perm_drop_4Statement : Prop :=
  ∀ m b lo hi p m',
    drop_perm m b lo hi p = some m' →
    ∀ b' ofs k p', perm m' b' ofs k p' → perm m b' ofs k p'

def valid_access_drop_1Statement : Prop :=
  ∀ m b lo hi p m',
    drop_perm m b lo hi p = some m' →
    ∀ chunk b' ofs p',
      (b' ≠ b ∨ zLe (zAdd ofs (size_chunk chunk)) lo ∨
        zLe hi ofs ∨ perm_order p p') →
      valid_access m chunk b' ofs p' → valid_access m' chunk b' ofs p'

def valid_access_drop_2Statement : Prop :=
  ∀ m b lo hi p m',
    drop_perm m b lo hi p = some m' →
    ∀ chunk b' ofs p',
      valid_access m' chunk b' ofs p' → valid_access m chunk b' ofs p'

def load_dropStatement : Prop :=
  ∀ m b lo hi p m',
    drop_perm m b lo hi p = some m' →
    ∀ chunk b' ofs,
      (b' ≠ b ∨ zLe (zAdd ofs (size_chunk chunk)) lo ∨
        zLe hi ofs ∨ perm_order p Readable) →
      load chunk m' b' ofs = load chunk m b' ofs

def loadbytes_dropStatement : Prop :=
  ∀ m b lo hi p m',
    drop_perm m b lo hi p = some m' →
    ∀ b' ofs n,
      (b' ≠ b ∨ zLe (zAdd ofs n) lo ∨ zLe hi ofs ∨ perm_order p Readable) →
      loadbytes m' b' ofs n = loadbytes m b' ofs n

def perm_injStatement : Prop :=
  ∀ f m1 m2 b1 ofs k p b2 delta,
    mem_inj f m1 m2 →
    perm m1 b1 ofs k p →
    f b1 = some (b2, delta) →
    perm m2 b2 (zAdd ofs delta) k p

def range_perm_injStatement : Prop :=
  ∀ f m1 m2 b1 lo hi k p b2 delta,
    mem_inj f m1 m2 →
    range_perm m1 b1 lo hi k p →
    f b1 = some (b2, delta) →
    range_perm m2 b2 (zAdd lo delta) (zAdd hi delta) k p

def valid_access_injStatement : Prop :=
  ∀ f m1 m2 b1 b2 delta chunk ofs p,
    mem_inj f m1 m2 →
    f b1 = some (b2, delta) →
    valid_access m1 chunk b1 ofs p →
    valid_access m2 chunk b2 (zAdd ofs delta) p

def getN_injStatement : Prop :=
  ∀ f m1 m2 b1 b2 delta,
    mem_inj f m1 m2 →
    f b1 = some (b2, delta) →
    ∀ n ofs,
      range_perm m1 b1 ofs (zAdd ofs (zOfNat n)) Cur Readable →
      CompCert4Lean.Lib.Coqlib.list_forall2 (memval_inject f)
        (getN n ofs (PMap.get b1 m1.mem_contents))
        (getN n (zAdd ofs delta) (PMap.get b2 m2.mem_contents))

def load_injStatement : Prop :=
  ∀ f m1 m2 chunk b1 ofs b2 delta v1,
    mem_inj f m1 m2 →
    load chunk m1 b1 ofs = some v1 →
    f b1 = some (b2, delta) →
    ∃ v2, load chunk m2 b2 (zAdd ofs delta) = some v2 ∧ Val.inject f v1 v2

def loadbytes_injStatement : Prop :=
  ∀ f m1 m2 len b1 ofs b2 delta bytes1,
    mem_inj f m1 m2 →
    loadbytes m1 b1 ofs len = some bytes1 →
    f b1 = some (b2, delta) →
    ∃ bytes2,
      loadbytes m2 b2 (zAdd ofs delta) len = some bytes2 ∧
      CompCert4Lean.Lib.Coqlib.list_forall2 (memval_inject f) bytes1 bytes2

def setN_injStatement : Prop :=
  ∀ (access : Z → Prop) delta f vl1 vl2,
    CompCert4Lean.Lib.Coqlib.list_forall2 (memval_inject f) vl1 vl2 →
    ∀ p c1 c2,
      (∀ q, access q →
        memval_inject f (ZMap.get q c1) (ZMap.get (zAdd q delta) c2)) →
      ∀ q, access q →
        memval_inject f (ZMap.get q (setN vl1 p c1))
          (ZMap.get (zAdd q delta) (setN vl2 (zAdd p delta) c2))

def store_mapped_injStatement : Prop :=
  ∀ f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
    mem_inj f m1 m2 →
    store chunk m1 b1 ofs v1 = some n1 →
    meminj_no_overlap f m1 →
    f b1 = some (b2, delta) →
    Val.inject f v1 v2 →
    ∃ n2,
      store chunk m2 b2 (zAdd ofs delta) v2 = some n2 ∧
      mem_inj f n1 n2

def store_unmapped_injStatement : Prop :=
  ∀ f chunk m1 b1 ofs v1 n1 m2,
    mem_inj f m1 m2 →
    store chunk m1 b1 ofs v1 = some n1 →
    f b1 = none →
    mem_inj f n1 m2

def storebytes_mapped_injStatement : Prop :=
  ∀ f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
    mem_inj f m1 m2 →
    storebytes m1 b1 ofs bytes1 = some n1 →
    meminj_no_overlap f m1 →
    f b1 = some (b2, delta) →
    CompCert4Lean.Lib.Coqlib.list_forall2 (memval_inject f) bytes1 bytes2 →
    ∃ n2,
      storebytes m2 b2 (zAdd ofs delta) bytes2 = some n2 ∧
      mem_inj f n1 n2

def storebytes_empty_injStatement : Prop :=
  ∀ f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
    mem_inj f m1 m2 →
    storebytes m1 b1 ofs1 [] = some m1' →
    storebytes m2 b2 ofs2 [] = some m2' →
    mem_inj f m1' m2'

def alloc_right_injStatement : Prop :=
  ∀ f m1 m2 lo hi b2 m2',
    mem_inj f m1 m2 →
    alloc m2 lo hi = (m2', b2) →
    mem_inj f m1 m2'

def alloc_left_unmapped_injStatement : Prop :=
  ∀ f m1 m2 lo hi m1' b1,
    mem_inj f m1 m2 →
    alloc m1 lo hi = (m1', b1) →
    f b1 = none →
    mem_inj f m1' m2

def alloc_left_mapped_injStatement : Prop :=
  ∀ f m1 m2 lo hi m1' b1 b2 delta,
    mem_inj f m1 m2 →
    alloc m1 lo hi = (m1', b1) →
    valid_block m2 b2 →
    inj_offset_aligned delta (zSub hi lo) →
    (∀ ofs k p, zLe lo ofs ∧ zLt ofs hi →
      perm m2 b2 (zAdd ofs delta) k p) →
    f b1 = some (b2, delta) →
    mem_inj f m1' m2

def free_left_injStatement : Prop :=
  ∀ f m1 m2 b lo hi m1',
    mem_inj f m1 m2 →
    free m1 b lo hi = some m1' →
    mem_inj f m1' m2

def free_right_injStatement : Prop :=
  ∀ f m1 m2 b lo hi m2',
    mem_inj f m1 m2 →
    free m2 b lo hi = some m2' →
    (∀ b' delta ofs k p,
      f b' = some (b, delta) →
      perm m1 b' ofs k p →
      zLe lo (zAdd ofs delta) ∧ zLt (zAdd ofs delta) hi → False) →
    mem_inj f m1 m2'

def drop_mapped_injStatement : Prop :=
  ∀ f m1 m2 b1 b2 delta lo hi p m1',
    mem_inj f m1 m2 →
    drop_perm m1 b1 lo hi p = some m1' →
    meminj_no_overlap f m1 →
    f b1 = some (b2, delta) →
    ∃ m2',
      drop_perm m2 b2 (zAdd lo delta) (zAdd hi delta) p = some m2' ∧
      mem_inj f m1' m2'

def extends_reflStatement : Prop :=
  ∀ m, «extends» m m

def load_extendsStatement : Prop :=
  ∀ chunk m1 m2 b ofs v1,
    «extends» m1 m2 →
    load chunk m1 b ofs = some v1 →
    ∃ v2, load chunk m2 b ofs = some v2 ∧ Val.lessdef v1 v2

def loadv_extendsStatement : Prop :=
  ∀ chunk m1 m2 addr1 addr2 v1,
    «extends» m1 m2 →
    loadv chunk m1 addr1 = some v1 →
    Val.lessdef addr1 addr2 →
    ∃ v2, loadv chunk m2 addr2 = some v2 ∧ Val.lessdef v1 v2

def loadbytes_extendsStatement : Prop :=
  ∀ m1 m2 b ofs len bytes1,
    «extends» m1 m2 →
    loadbytes m1 b ofs len = some bytes1 →
    ∃ bytes2,
      loadbytes m2 b ofs len = some bytes2 ∧
      CompCert4Lean.Lib.Coqlib.list_forall2 memval_lessdef bytes1 bytes2

def store_within_extendsStatement : Prop :=
  ∀ chunk m1 m2 b ofs v1 m1' v2,
    «extends» m1 m2 →
    store chunk m1 b ofs v1 = some m1' →
    Val.lessdef v1 v2 →
    ∃ m2', store chunk m2 b ofs v2 = some m2' ∧ «extends» m1' m2'

def storev_extendsStatement : Prop :=
  ∀ chunk m1 m2 addr1 v1 m1' addr2 v2,
    «extends» m1 m2 →
    storev chunk m1 addr1 v1 = some m1' →
    Val.lessdef addr1 addr2 →
    Val.lessdef v1 v2 →
    ∃ m2', storev chunk m2 addr2 v2 = some m2' ∧ «extends» m1' m2'

def storebytes_within_extendsStatement : Prop :=
  ∀ m1 m2 b ofs bytes1 m1' bytes2,
    «extends» m1 m2 →
    storebytes m1 b ofs bytes1 = some m1' →
    CompCert4Lean.Lib.Coqlib.list_forall2 memval_lessdef bytes1 bytes2 →
    ∃ m2', storebytes m2 b ofs bytes2 = some m2' ∧ «extends» m1' m2'

def alloc_extendsStatement : Prop :=
  ∀ m1 m2 lo1 hi1 b m1' lo2 hi2,
    «extends» m1 m2 →
    alloc m1 lo1 hi1 = (m1', b) →
    zLe lo2 lo1 → zLe hi1 hi2 →
    ∃ m2', alloc m2 lo2 hi2 = (m2', b) ∧ «extends» m1' m2'

def free_left_extendsStatement : Prop :=
  ∀ m1 m2 b lo hi m1',
    «extends» m1 m2 →
    free m1 b lo hi = some m1' →
    «extends» m1' m2

def free_right_extendsStatement : Prop :=
  ∀ m1 m2 b lo hi m2',
    «extends» m1 m2 →
    free m2 b lo hi = some m2' →
    (∀ ofs k p, perm m1 b ofs k p →
      zLe lo ofs ∧ zLt ofs hi → False) →
    «extends» m1 m2'

def free_parallel_extendsStatement : Prop :=
  ∀ m1 m2 b lo hi m1',
    «extends» m1 m2 →
    free m1 b lo hi = some m1' →
    ∃ m2', free m2 b lo hi = some m2' ∧ «extends» m1' m2'

def valid_access_extendsStatement : Prop :=
  ∀ m1 m2 chunk b ofs p,
    «extends» m1 m2 →
    valid_access m1 chunk b ofs p →
    valid_access m2 chunk b ofs p

def valid_pointer_extendsStatement : Prop :=
  ∀ m1 m2 b ofs,
    «extends» m1 m2 →
    valid_pointer m1 b ofs = true →
    valid_pointer m2 b ofs = true

def weak_valid_pointer_extendsStatement : Prop :=
  ∀ m1 m2 b ofs,
    «extends» m1 m2 →
    weak_valid_pointer m1 b ofs = true →
    weak_valid_pointer m2 b ofs = true

def valid_block_inject_1Statement : Prop :=
  ∀ f m1 m2 b1 b2 delta,
    f b1 = some (b2, delta) →
    inject f m1 m2 →
    valid_block m1 b1

def valid_block_inject_2Statement : Prop :=
  ∀ f m1 m2 b1 b2 delta,
    f b1 = some (b2, delta) →
    inject f m1 m2 →
    valid_block m2 b2

def perm_injectStatement : Prop :=
  ∀ f m1 m2 b1 b2 delta ofs k p,
    f b1 = some (b2, delta) →
    inject f m1 m2 →
    perm m1 b1 ofs k p →
    perm m2 b2 (zAdd ofs delta) k p

def range_perm_injectStatement : Prop :=
  ∀ f m1 m2 b1 b2 delta lo hi k p,
    f b1 = some (b2, delta) →
    inject f m1 m2 →
    range_perm m1 b1 lo hi k p →
    range_perm m2 b2 (zAdd lo delta) (zAdd hi delta) k p

def valid_access_injectStatement : Prop :=
  ∀ f m1 m2 chunk b1 ofs b2 delta p,
    f b1 = some (b2, delta) →
    inject f m1 m2 →
    valid_access m1 chunk b1 ofs p →
    valid_access m2 chunk b2 (zAdd ofs delta) p

def valid_pointer_injectStatement : Prop :=
  ∀ f m1 m2 b1 ofs b2 delta,
    f b1 = some (b2, delta) →
    inject f m1 m2 →
    valid_pointer m1 b1 ofs = true →
    valid_pointer m2 b2 (zAdd ofs delta) = true

def weak_valid_pointer_injectStatement : Prop :=
  ∀ f m1 m2 b1 ofs b2 delta,
    f b1 = some (b2, delta) →
    inject f m1 m2 →
    weak_valid_pointer m1 b1 ofs = true →
    weak_valid_pointer m2 b2 (zAdd ofs delta) = true

def address_inject_genStatement : Prop :=
  ∀ f m1 m2 b1 ofs1 b2 delta p,
    inject f m1 m2 →
    (perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ∨
      perm m1 b1 (zSub (Ptrofs.unsigned ofs1) z1) Cur p) →
    f b1 = some (b2, delta) →
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
      zAdd (Ptrofs.unsigned ofs1) delta

def address_injectStatement : Prop :=
  ∀ f m1 m2 b1 ofs1 b2 delta p,
    inject f m1 m2 →
    perm m1 b1 (Ptrofs.unsigned ofs1) Cur p →
    f b1 = some (b2, delta) →
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
      zAdd (Ptrofs.unsigned ofs1) delta

def address_inject'Statement : Prop :=
  ∀ f m1 m2 chunk b1 ofs1 b2 delta,
    inject f m1 m2 →
    valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Memtype.Nonempty →
    f b1 = some (b2, delta) →
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
      zAdd (Ptrofs.unsigned ofs1) delta

def weak_valid_pointer_inject_no_overflowStatement : Prop :=
  ∀ f m1 m2 b ofs b' delta,
    inject f m1 m2 →
    weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true →
    f b = some (b', delta) →
    zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
    zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))
      Ptrofs.max_unsigned

def valid_pointer_inject_valStatement : Prop :=
  ∀ f m1 m2 b ofs b' ofs',
    inject f m1 m2 →
    valid_pointer m1 b (Ptrofs.unsigned ofs) = true →
    Val.inject f (Vptr b ofs) (Vptr b' ofs') →
    valid_pointer m2 b' (Ptrofs.unsigned ofs') = true

def weak_valid_pointer_inject_valStatement : Prop :=
  ∀ f m1 m2 b ofs b' ofs',
    inject f m1 m2 →
    weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true →
    Val.inject f (Vptr b ofs) (Vptr b' ofs') →
    weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true

def different_pointers_injectStatement : Prop :=
  ∀ f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
    inject f m m' →
    b1 ≠ b2 →
    valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
    valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
    f b1 = some (b1', delta1) →
    f b2 = some (b2', delta2) →
    b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))

def disjoint_or_equal_injectStatement : Prop :=
  ∀ f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
    inject f m m' →
    f b1 = some (b1', delta1) →
    f b2 = some (b2', delta2) →
    range_perm m b1 ofs1 (zAdd ofs1 sz) Max Memtype.Nonempty →
    range_perm m b2 ofs2 (zAdd ofs2 sz) Max Memtype.Nonempty →
    zLt z0 sz →
    (b1 ≠ b2 ∨ ofs1 = ofs2 ∨ zLe (zAdd ofs1 sz) ofs2 ∨
      zLe (zAdd ofs2 sz) ofs1) →
    b1' ≠ b2' ∨ zAdd ofs1 delta1 = zAdd ofs2 delta2 ∨
      zLe (zAdd (zAdd ofs1 delta1) sz) (zAdd ofs2 delta2) ∨
      zLe (zAdd (zAdd ofs2 delta2) sz) (zAdd ofs1 delta1)

def aligned_area_injectStatement : Prop :=
  ∀ f m m' b ofs al sz b' delta,
    inject f m m' →
    (al = z1 ∨ al = zOfNat 2 ∨ al = zOfNat 4 ∨ al = zOfNat 8) →
    zLt z0 sz →
    zDivide al sz →
    range_perm m b ofs (zAdd ofs sz) Cur Memtype.Nonempty →
    zDivide al ofs →
    f b = some (b', delta) →
    zDivide al (zAdd ofs delta)

def load_injectStatement : Prop :=
  ∀ f m1 m2 chunk b1 ofs b2 delta v1,
    inject f m1 m2 →
    load chunk m1 b1 ofs = some v1 →
    f b1 = some (b2, delta) →
    ∃ v2, load chunk m2 b2 (zAdd ofs delta) = some v2 ∧ Val.inject f v1 v2

def loadv_injectStatement : Prop :=
  ∀ f m1 m2 chunk a1 a2 v1,
    inject f m1 m2 →
    loadv chunk m1 a1 = some v1 →
    Val.inject f a1 a2 →
    ∃ v2, loadv chunk m2 a2 = some v2 ∧ Val.inject f v1 v2

def loadbytes_injectStatement : Prop :=
  ∀ f m1 m2 b1 ofs len b2 delta bytes1,
    inject f m1 m2 →
    loadbytes m1 b1 ofs len = some bytes1 →
    f b1 = some (b2, delta) →
    ∃ bytes2,
      loadbytes m2 b2 (zAdd ofs delta) len = some bytes2 ∧
      CompCert4Lean.Lib.Coqlib.list_forall2 (memval_inject f) bytes1 bytes2

def store_mapped_injectStatement : Prop :=
  ∀ f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
    inject f m1 m2 →
    store chunk m1 b1 ofs v1 = some n1 →
    f b1 = some (b2, delta) →
    Val.inject f v1 v2 →
    ∃ n2, store chunk m2 b2 (zAdd ofs delta) v2 = some n2 ∧ inject f n1 n2

def store_unmapped_injectStatement : Prop :=
  ∀ f chunk m1 b1 ofs v1 n1 m2,
    inject f m1 m2 →
    store chunk m1 b1 ofs v1 = some n1 →
    f b1 = none →
    inject f n1 m2

def storev_mapped_injectStatement : Prop :=
  ∀ f chunk m1 a1 v1 n1 m2 a2 v2,
    inject f m1 m2 →
    storev chunk m1 a1 v1 = some n1 →
    Val.inject f a1 a2 →
    Val.inject f v1 v2 →
    ∃ n2, storev chunk m2 a2 v2 = some n2 ∧ inject f n1 n2

def storebytes_mapped_injectStatement : Prop :=
  ∀ f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
    inject f m1 m2 →
    storebytes m1 b1 ofs bytes1 = some n1 →
    f b1 = some (b2, delta) →
    CompCert4Lean.Lib.Coqlib.list_forall2 (memval_inject f) bytes1 bytes2 →
    ∃ n2,
      storebytes m2 b2 (zAdd ofs delta) bytes2 = some n2 ∧ inject f n1 n2

def storebytes_empty_injectStatement : Prop :=
  ∀ f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
    inject f m1 m2 →
    storebytes m1 b1 ofs1 [] = some m1' →
    storebytes m2 b2 ofs2 [] = some m2' →
    inject f m1' m2'

def alloc_right_injectStatement : Prop :=
  ∀ f m1 m2 lo hi b2 m2',
    inject f m1 m2 →
    alloc m2 lo hi = (m2', b2) →
    inject f m1 m2'

def alloc_left_unmapped_injectStatement : Prop :=
  ∀ f m1 m2 lo hi m1' b1,
    inject f m1 m2 →
    alloc m1 lo hi = (m1', b1) →
    ∃ f',
      inject f' m1' m2 ∧ inject_incr f f' ∧ f' b1 = none ∧
      ∀ b, b ≠ b1 → f' b = f b

def alloc_left_mapped_injectStatement : Prop :=
  ∀ f m1 m2 lo hi m1' b1 b2 delta,
    inject f m1 m2 →
    alloc m1 lo hi = (m1', b1) →
    valid_block m2 b2 →
    (zLe z0 delta ∧ zLe delta Ptrofs.max_unsigned) →
    (∀ ofs k p, perm m2 b2 ofs k p →
      delta = z0 ∨ (zLe z0 ofs ∧ zLt ofs Ptrofs.max_unsigned)) →
    (∀ ofs k p, zLe lo ofs ∧ zLt ofs hi →
      perm m2 b2 (zAdd ofs delta) k p) →
    inj_offset_aligned delta (zSub hi lo) →
    (∀ b delta' ofs k p,
      f b = some (b2, delta') →
      perm m1 b ofs k p →
      zLe (zAdd lo delta) (zAdd ofs delta') ∧
        zLt (zAdd ofs delta') (zAdd hi delta) → False) →
    ∃ f',
      inject f' m1' m2 ∧ inject_incr f f' ∧ f' b1 = some (b2, delta) ∧
      ∀ b, b ≠ b1 → f' b = f b

def alloc_parallel_injectStatement : Prop :=
  ∀ f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
    inject f m1 m2 →
    alloc m1 lo1 hi1 = (m1', b1) →
    zLe lo2 lo1 → zLe hi1 hi2 →
    ∃ f' m2' b2,
      alloc m2 lo2 hi2 = (m2', b2) ∧
      inject f' m1' m2' ∧ inject_incr f f' ∧ f' b1 = some (b2, z0) ∧
      ∀ b, b ≠ b1 → f' b = f b

def free_left_injectStatement : Prop :=
  ∀ f m1 m2 b lo hi m1',
    inject f m1 m2 →
    free m1 b lo hi = some m1' →
    inject f m1' m2

def free_list_left_injectStatement : Prop :=
  ∀ f m2 l m1 m1',
    inject f m1 m2 →
    free_list m1 l = some m1' →
    inject f m1' m2

def free_right_injectStatement : Prop :=
  ∀ f m1 m2 b lo hi m2',
    inject f m1 m2 →
    free m2 b lo hi = some m2' →
    (∀ b1 delta ofs k p,
      f b1 = some (b, delta) →
      perm m1 b1 ofs k p →
      zLe lo (zAdd ofs delta) ∧ zLt (zAdd ofs delta) hi → False) →
    inject f m1 m2'

def perm_free_listStatement : Prop :=
  ∀ l m m' b ofs k p,
    free_list m l = some m' →
    perm m' b ofs k p →
    perm m b ofs k p ∧
    ∀ lo hi, (b, lo, hi) ∈ l → zLe lo ofs ∧ zLt ofs hi → False

def free_injectStatement : Prop :=
  ∀ f m1 l m1' m2 b lo hi m2',
    inject f m1 m2 →
    free_list m1 l = some m1' →
    free m2 b lo hi = some m2' →
    (∀ b1 delta ofs k p,
      f b1 = some (b, delta) →
      perm m1 b1 ofs k p →
      zLe lo (zAdd ofs delta) ∧ zLt (zAdd ofs delta) hi →
      ∃ lo1 hi1, (b1, lo1, hi1) ∈ l ∧ zLe lo1 ofs ∧ zLt ofs hi1) →
    inject f m1' m2'

def free_parallel_injectStatement : Prop :=
  ∀ f m1 m2 b lo hi m1' b' delta,
    inject f m1 m2 →
    free m1 b lo hi = some m1' →
    f b = some (b', delta) →
    ∃ m2',
      free m2 b' (zAdd lo delta) (zAdd hi delta) = some m2' ∧
      inject f m1' m2'

def flat_inj_no_overlapStatement : Prop :=
  ∀ thr m, meminj_no_overlap (flat_inj thr) m

def neutral_injectStatement : Prop :=
  ∀ m, inject_neutral m.nextblock m → inject (flat_inj m.nextblock) m m

def empty_inject_neutralStatement : Prop :=
  ∀ thr, inject_neutral thr empty

def alloc_inject_neutralStatement : Prop :=
  ∀ thr m lo hi b m',
    alloc m lo hi = (m', b) →
    inject_neutral thr m →
    Plt m.nextblock thr →
    inject_neutral thr m'

def store_inject_neutralStatement : Prop :=
  ∀ chunk m b ofs v m' thr,
    store chunk m b ofs v = some m' →
    inject_neutral thr m →
    Plt b thr →
    Val.inject (flat_inj thr) v v →
    inject_neutral thr m'

def drop_inject_neutralStatement : Prop :=
  ∀ m b lo hi p m' thr,
    drop_perm m b lo hi p = some m' →
    inject_neutral thr m →
    Plt b thr →
    inject_neutral thr m'

def unchanged_on_reflStatement : Prop :=
  ∀ (P : block → Z → Prop) m, unchanged_on P m m

def valid_block_unchanged_onStatement : Prop :=
  ∀ (P : block → Z → Prop) m m' b,
    unchanged_on P m m' →
    valid_block m b →
    valid_block m' b

def perm_unchanged_onStatement : Prop :=
  ∀ (P : block → Z → Prop) m m' b ofs k p,
    unchanged_on P m m' →
    P b ofs →
    perm m b ofs k p →
    perm m' b ofs k p

def perm_unchanged_on_2Statement : Prop :=
  ∀ (P : block → Z → Prop) m m' b ofs k p,
    unchanged_on P m m' →
    P b ofs →
    valid_block m b →
    perm m' b ofs k p →
    perm m b ofs k p

def unchanged_on_transStatement : Prop :=
  ∀ (P : block → Z → Prop) m1 m2 m3,
    unchanged_on P m1 m2 →
    unchanged_on P m2 m3 →
    unchanged_on P m1 m3

def loadbytes_unchanged_on_1Statement : Prop :=
  ∀ (P : block → Z → Prop) m m' b ofs n,
    unchanged_on P m m' →
    valid_block m b →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs n) → P b i) →
    loadbytes m' b ofs n = loadbytes m b ofs n

def loadbytes_unchanged_onStatement : Prop :=
  ∀ (P : block → Z → Prop) m m' b ofs n bytes,
    unchanged_on P m m' →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs n) → P b i) →
    loadbytes m b ofs n = some bytes →
    loadbytes m' b ofs n = some bytes

def load_unchanged_on_1Statement : Prop :=
  ∀ (P : block → Z → Prop) m m' chunk b ofs,
    unchanged_on P m m' →
    valid_block m b →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) → P b i) →
    load chunk m' b ofs = load chunk m b ofs

def load_unchanged_onStatement : Prop :=
  ∀ (P : block → Z → Prop) m m' chunk b ofs v,
    unchanged_on P m m' →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) → P b i) →
    load chunk m b ofs = some v →
    load chunk m' b ofs = some v

def store_unchanged_onStatement : Prop :=
  ∀ (P : block → Z → Prop) chunk m b ofs v m',
    store chunk m b ofs v = some m' →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) → ¬ P b i) →
    unchanged_on P m m'

def storebytes_unchanged_onStatement : Prop :=
  ∀ (P : block → Z → Prop) m b ofs bytes m',
    storebytes m b ofs bytes = some m' →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs (zOfNat bytes.length)) → ¬ P b i) →
    unchanged_on P m m'

def alloc_unchanged_onStatement : Prop :=
  ∀ (P : block → Z → Prop) m lo hi m' b,
    alloc m lo hi = (m', b) →
    unchanged_on P m m'

def free_unchanged_onStatement : Prop :=
  ∀ (P : block → Z → Prop) m b lo hi m',
    free m b lo hi = some m' →
    (∀ i, zLe lo i ∧ zLt i hi → ¬ P b i) →
    unchanged_on P m m'

def drop_perm_unchanged_onStatement : Prop :=
  ∀ (P : block → Z → Prop) m b lo hi p m',
    drop_perm m b lo hi p = some m' →
    (∀ i, zLe lo i ∧ zLt i hi → ¬ P b i) →
    unchanged_on P m m'

def unchanged_on_impliesStatement : Prop :=
  ∀ (P Q : block → Z → Prop) m m',
    unchanged_on P m m' →
    (∀ b ofs, Q b ofs → valid_block m b → P b ofs) →
    unchanged_on Q m m'

end Mem

abbrev mem := Mem.mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps

namespace Mem

theorem mkmem_ext : mkmem_extStatement := by
  intro cont1 cont2 acc1 acc2 next1 next2 a1 a2 b1 b2 c1 c2 hcont hacc hnext
  subst cont2
  subst acc2
  subst next2
  rfl

theorem valid_not_valid_diff : valid_not_valid_diffStatement := by
  intro m b b' hvalid hnot heq
  subst b'
  exact hnot hvalid

theorem perm_implies : perm_impliesStatement := by
  intro m b ofs k p1 p2 hperm horder
  unfold perm perm_order' at hperm ⊢
  cases haccess : (PMap.get b m.mem_access) ofs k with
  | none =>
      exfalso
      simp [haccess] at hperm
  | some p =>
      exact perm_order_trans p p1 p2 (by simpa [haccess] using hperm) horder

private theorem perm_order'_of_perm_order'' (po1 po2 : Option permission) (p : permission) :
    perm_order' po2 p → perm_order'' po1 po2 → perm_order' po1 p := by
  intro h2 h12
  cases po1 <;> cases po2 <;> simp [perm_order', perm_order''] at *
  exact perm_order_trans _ _ _ h12 h2

theorem perm_cur_max : perm_cur_maxStatement := by
  intro m b ofs p hperm
  unfold perm at hperm ⊢
  exact perm_order'_of_perm_order''
    ((PMap.get b m.mem_access) ofs Max)
    ((PMap.get b m.mem_access) ofs Cur)
    p hperm (m.access_max b ofs)

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

namespace Mem

theorem perm_cur : perm_curStatement := by
  intro m b ofs k p hperm
  cases k with
  | Max => exact perm_cur_max m b ofs p hperm
  | Cur => exact hperm

theorem perm_max : perm_maxStatement := by
  intro m b ofs k p hperm
  cases k with
  | Max => exact hperm
  | Cur => exact perm_cur_max m b ofs p hperm

theorem perm_valid_block : perm_valid_blockStatement := by
  intro m b ofs k p hperm
  cases hplt : CompCert4Lean.Lib.Coqlib.plt b m.nextblock with
  | left hvalid => exact hvalid
  | right hnot =>
      unfold perm at hperm
      rw [m.nextblock_noaccess b ofs k hnot] at hperm
      simp [perm_order'] at hperm

theorem range_perm_implies : range_perm_impliesStatement := by
  intro m b lo hi k p1 p2 hperm horder ofs hof
  exact perm_implies m b ofs k p1 p2 (hperm ofs hof) horder

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem range_perm_max : range_perm_maxStatement := by
  intro m b lo hi k p hperm ofs hof
  exact perm_max m b ofs k p (hperm ofs hof)

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype

namespace Mem

theorem valid_access_implies : valid_access_impliesStatement := by
  intro m chunk b ofs p1 p2 hvalid horder
  exact ⟨range_perm_implies m b ofs (zAdd ofs (size_chunk chunk)) Cur p1 p2 hvalid.1 horder,
    hvalid.2⟩

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.Memtype

namespace Mem

theorem valid_pointer_nonempty_perm : valid_pointer_nonempty_permStatement := by
  intro m b ofs
  unfold valid_pointer
  cases h : perm_dec m b ofs Cur Memtype.Nonempty with
  | left hp =>
      simp [boolOfSumbool, h, hp]
  | right hp =>
      simp [boolOfSumbool, h, hp]

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype

namespace Mem

theorem valid_pointer_valid_access : valid_pointer_valid_accessStatement := by
  intro m b ofs
  rw [valid_pointer_nonempty_perm]
  constructor
  · intro hp
    constructor
    · intro ofs' hof
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs' ∧
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs' <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
              (size_chunk CompCert4Lean.Common.AST.Mint8unsigned)) at hof
      simp [size_chunk,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hof
      have heq : ofs' = ofs := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        omega
      subst ofs'
      exact hp
    · exact ⟨ofs, by
        change ofs =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat 1)) *
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs)
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        simpa using (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ ofs).symm
        ⟩
  · rintro ⟨hr, _⟩
    exact hr ofs (by
      constructor
      · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
        omega
      · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
              (size_chunk CompCert4Lean.Common.AST.Mint8unsigned))
        simp [size_chunk,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        omega
      )

theorem weak_valid_pointer_spec : weak_valid_pointer_specStatement := by
  intro m b ofs
  simp [weak_valid_pointer]

theorem valid_pointer_implies : valid_pointer_impliesStatement := by
  intro m b ofs h
  apply (weak_valid_pointer_spec m b ofs).2
  exact Or.inl h

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps

namespace Mem

private theorem pmap_get_set_other_memproof {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) (h : i ≠ j) : PMap.get i (PMap.set j x m) = PMap.get i m := by
  change (match PTree.get i (PTree.set j x m.2) with
    | some y => y
    | none => m.1) =
    (match PTree.get i m.2 with
    | some y => y
    | none => m.1)
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i j with
  | left hij => exact False.elim (h hij)
  | right hne => simp [hpeq]

private theorem zmap_get_set_other_memproof {A : Type} (i j : Z) (x : A)
    (m : ZMap.t A) (h : i ≠ j) : ZMap.get i (ZMap.set j x m) = ZMap.get i m := by
  apply pmap_get_set_other_memproof (ZIndexed.index i) (ZIndexed.index j) x m
  intro hij
  apply h
  exact ZIndexed.index_inj i j hij

private theorem intOfZ_zadd_mem (x y : Z) :
    intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add x y) =
      intOfZ x + intOfZ y := by
  change intOfZ (zOfInt (intOfZ x + intOfZ y)) = intOfZ x + intOfZ y
  rw [intOfZ_zOfInt]

private theorem intOfZ_zofnat_mem (n : Nat) :
    intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) =
      Int.ofNat n := by
  change intOfZ (zOfInt (Int.ofNat n)) = Int.ofNat n
  rw [intOfZ_zOfInt]

theorem setN_other : setN_otherStatement := by
  intro vl
  induction vl with
  | nil =>
      intro c p q h
      rfl
  | cons v rest ih =>
      intro c p q h
      simp only [List.length_cons] at h
      have hTail : ∀ r,
          zLe (zAdd p z1) r ∧
              zLt r (zAdd (zAdd p z1) (zOfNat rest.length)) → r ≠ q := by
        intro r hr
        rcases hr with ⟨hrlo, hrhi⟩
        apply h r
        constructor
        · change intOfZ p ≤ intOfZ r
          change intOfZ (zAdd p z1) ≤ intOfZ r at hrlo
          rw [intOfZ_add_one] at hrlo
          omega
        · change intOfZ r < intOfZ (zAdd p (zOfNat (List.length (v :: rest))))
          change intOfZ r < intOfZ (zAdd (zAdd p z1) (zOfNat rest.length)) at hrhi
          have hnat : Int.ofNat (rest.length + 1) = Int.ofNat rest.length + 1 := by
            simpa using (Int.ofNat_add_ofNat rest.length 1).symm
          rw [show (v :: rest).length = rest.length + 1 by rfl]
          rw [intOfZ_zadd_mem, intOfZ_zofnat_mem, hnat]
          rw [intOfZ_zadd_mem, intOfZ_zadd_mem, intOfZ_zofnat_mem] at hrhi
          have hz1 : intOfZ z1 = (1 : Int) := by rfl
          rw [hz1] at hrhi
          omega
      have hs := ih (ZMap.set p v c) (zAdd p z1) q hTail
      have hneq : q ≠ p := by
        intro heq
        subst q
        have hbad : p ≠ p := h p (by
          constructor
          · change intOfZ p ≤ intOfZ p
            omega
          · change intOfZ p < intOfZ (zAdd p (zOfNat (List.length (v :: rest))))
            rw [intOfZ_zadd_mem, intOfZ_zofnat_mem]
            have hnat : Int.ofNat (rest.length + 1) = Int.ofNat rest.length + 1 := by
              simpa using (Int.ofNat_add_ofNat rest.length 1).symm
            rw [show (v :: rest).length = rest.length + 1 by rfl]
            rw [hnat]
            have hnonneg : (0 : Int) ≤ Int.ofNat rest.length := Int.natCast_nonneg _
            omega)
        exact hbad rfl
      calc
        ZMap.get q (setN (v :: rest) p c) =
            ZMap.get q (setN rest (zAdd p z1) (ZMap.set p v c)) := by rfl
        _ = ZMap.get q (ZMap.set p v c) := hs
        _ = ZMap.get q c := zmap_get_set_other_memproof q p v c hneq

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

namespace Mem

private theorem pmap_get_set_same_memproof {A : Type} (i : positive) (x : A)
    (m : PMap.t A) : PMap.get i (PMap.set i x m) = x := by
  change (match PTree.get i (PTree.set i x m.2) with
    | some y => y
    | none => m.1) = x
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i i with
  | left _ => simp
  | right hne => exact False.elim (hne rfl)

theorem getN_setN_same : getN_setN_sameStatement := by
  intro vl
  induction vl with
  | nil =>
      intro p c
      rfl
  | cons v rest ih =>
      intro p c
      have hneq : ∀ r,
          zLe (zAdd p z1) r ∧
              zLt r (zAdd (zAdd p z1) (zOfNat rest.length)) → r ≠ p := by
        intro r hr
        rcases hr with ⟨hrlo, _⟩
        intro hrp
        subst r
        change intOfZ (zAdd p z1) ≤ intOfZ p at hrlo
        rw [intOfZ_add_one] at hrlo
        omega
      have hhead :
          ZMap.get p (setN rest (zAdd p z1) (ZMap.set p v c)) =
            ZMap.get p (ZMap.set p v c) := by
        apply setN_other
        intro r hr
        exact hneq r hr
      calc
        getN (List.length (v :: rest)) p (setN (v :: rest) p c) =
            ZMap.get p (setN rest (zAdd p z1) (ZMap.set p v c)) ::
              getN rest.length (zAdd p z1)
                (setN rest (zAdd p z1) (ZMap.set p v c)) := by
                rfl
        _ = ZMap.get p (ZMap.set p v c) :: rest := by
          rw [hhead, ih]
        _ = v :: rest := by
          congr 1
          change PMap.get (ZIndexed.index p)
            (PMap.set (ZIndexed.index p) v c) = v
          exact pmap_get_set_same_memproof _ _ _

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

namespace Mem

theorem getN_exten : getN_extenStatement := by
  intro c1 c2 n
  induction n with
  | zero =>
      intro p h
      rfl
  | succ n ih =>
      intro p h
      have hhead : ZMap.get p c1 = ZMap.get p c2 := by
        apply h p
        constructor
        · change intOfZ p ≤ intOfZ p
          omega
        · change intOfZ p < intOfZ (zAdd p (zOfNat (Nat.succ n)))
          have hnat : Int.ofNat (Nat.succ n) = Int.ofNat n + 1 := by
            simpa using (Int.ofNat_add_ofNat n 1).symm
          rw [intOfZ_zadd_mem, intOfZ_zofnat_mem, hnat]
          have hnonneg : (0 : Int) ≤ Int.ofNat n := Int.natCast_nonneg _
          omega
      have htail :
          getN n (zAdd p z1) c1 = getN n (zAdd p z1) c2 := by
        apply ih (p := zAdd p z1)
        intro i hi
        apply h i
        rcases hi with ⟨hi_lo, hi_hi⟩
        constructor
        · change intOfZ p ≤ intOfZ i
          change intOfZ (zAdd p z1) ≤ intOfZ i at hi_lo
          rw [intOfZ_add_one] at hi_lo
          omega
        · change intOfZ i < intOfZ (zAdd p (zOfNat (Nat.succ n)))
          change intOfZ i < intOfZ (zAdd (zAdd p z1) (zOfNat n)) at hi_hi
          have hnat : Int.ofNat (Nat.succ n) = Int.ofNat n + 1 := by
            simpa using (Int.ofNat_add_ofNat n 1).symm
          rw [intOfZ_zadd_mem, intOfZ_zofnat_mem, hnat]
          rw [intOfZ_zadd_mem, intOfZ_zadd_mem, intOfZ_zofnat_mem] at hi_hi
          have hz1 : intOfZ z1 = (1 : Int) := by rfl
          rw [hz1] at hi_hi
          omega
      change ZMap.get p c1 :: getN n (zAdd p z1) c1 =
        ZMap.get p c2 :: getN n (zAdd p z1) c2
      rw [hhead, htail]

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

namespace Mem

theorem getN_setN_disjoint : getN_setN_disjointStatement := by
  intro vl q c n p hdis
  apply getN_exten
  intro i hi
  apply setN_other
  intro r hr
  intro hri
  subst r
  exact hdis i hi hr

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

namespace Mem

theorem getN_setN_outside : getN_setN_outsideStatement := by
  intro vl q c n p h
  apply getN_setN_disjoint vl q c n p
  exact CompCert4Lean.Lib.Intv.disjoint_range _ _ h

theorem setN_default : setN_defaultStatement := by
  intro vl q c
  exact setNDefault vl q c

theorem nextblock_empty : nextblock_emptyStatement := by
  rfl

theorem valid_access_load : valid_access_loadStatement := by
  intro m chunk b ofs hvalid
  refine ⟨CompCert4Lean.Common.Memdata.decode_val chunk
      (getN (CompCert4Lean.Common.Memdata.size_chunk_nat chunk) ofs
        (PMap.get b m.mem_contents)), ?_⟩
  unfold load
  cases hdec : valid_access_dec m chunk b ofs CompCert4Lean.Common.Memtype.Readable with
  | left hproof =>
      simp [boolOfSumbool, hdec]
  | right hnproof =>
      exact False.elim (hnproof hvalid)

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps

namespace Mem

theorem load_valid_access : load_valid_accessStatement := by
  intro m chunk b ofs v hload
  unfold load at hload
  cases hdec : valid_access_dec m chunk b ofs Readable with
  | left hvalid => exact hvalid
  | right hinvalid => simp [boolOfSumbool, hdec] at hload

theorem load_result : load_resultStatement := by
  intro chunk m b ofs v hload
  unfold load at hload
  cases hdec : valid_access_dec m chunk b ofs Readable with
  | left hvalid =>
      simp [boolOfSumbool, hdec] at hload
      exact hload.symm
  | right hinvalid => simp [boolOfSumbool, hdec] at hload

theorem load_type : load_typeStatement := by
  intro m chunk b ofs v hload
  rw [load_result chunk m b ofs v hload]
  exact CompCert4Lean.Common.Memdata.decode_val_type chunk _

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

namespace Mem

theorem loadbytes_range_perm : loadbytes_range_permStatement := by
  intro m b ofs len bytes hload
  unfold loadbytes at hload
  cases hdec : range_perm_dec m b ofs (zAdd ofs len) Cur Readable with
  | left hperm =>
      exact hperm
  | right hnperm =>
      simp [boolOfSumbool, hdec] at hload

theorem loadbytes_load : loadbytes_loadStatement := by
  intro chunk m b ofs bytes hload halign
  unfold loadbytes at hload
  unfold load
  cases hdec : range_perm_dec m b ofs (zAdd ofs (size_chunk chunk)) Cur Readable with
  | right hnperm =>
      simp [boolOfSumbool, hdec] at hload
  | left hperm =>
      have hbytes : bytes = getN (zToNat (size_chunk chunk)) ofs
          (PMap.get b m.mem_contents) := by
        simpa [boolOfSumbool, hdec] using hload.symm
      cases halign' : zdivide_dec (align_chunk chunk) ofs with
      | right hnalign =>
          exact False.elim (hnalign halign)
      | left halign_dec =>
          simp [valid_access_dec, boolOfSumbool, hdec, halign', hbytes,
            size_chunk_nat]

theorem load_bool_int8_unsigned : load_bool_int8_unsignedStatement := by
  intro m b ofs
  unfold load
  change
    (if boolOfSumbool (valid_access_dec m Mbool b ofs Readable) then
        some (decode_val Mbool (getN 1 ofs (PMap.get b m.mem_contents)))
      else none) =
      option_map Val.norm_bool
        (if boolOfSumbool (valid_access_dec m Mint8unsigned b ofs Readable) then
            some (decode_val Mint8unsigned (getN 1 ofs (PMap.get b m.mem_contents)))
          else none)
  have hbool_eq :
      boolOfSumbool (valid_access_dec m Mbool b ofs Readable) =
        boolOfSumbool (valid_access_dec m Mint8unsigned b ofs Readable) := by
    have hs : size_chunk Mbool = size_chunk Mint8unsigned := by rfl
    have ha : align_chunk Mbool = align_chunk Mint8unsigned := by rfl
    have hvalid_bool (chunk : AST.memory_chunk) :
        boolOfSumbool (valid_access_dec m chunk b ofs Readable) =
          (boolOfSumbool
              (range_perm_dec m b ofs (zAdd ofs (size_chunk chunk)) Cur Readable) &&
            boolOfSumbool (zdivide_dec (align_chunk chunk) ofs)) := by
      unfold valid_access_dec
      cases hr : range_perm_dec m b ofs (zAdd ofs (size_chunk chunk)) Cur Readable with
      | right hn => simp [hr, boolOfSumbool]
      | left hp =>
          cases hd : zdivide_dec (align_chunk chunk) ofs with
          | left h => simp [hr, hd, boolOfSumbool]
          | right h => simp [hr, hd, boolOfSumbool]
    have hrange :
        boolOfSumbool
              (range_perm_dec m b ofs (zAdd ofs (size_chunk Mbool)) Cur Readable) =
          boolOfSumbool
              (range_perm_dec m b ofs (zAdd ofs (size_chunk Mint8unsigned)) Cur Readable) := by
      cases hp : range_perm_dec m b ofs (zAdd ofs (size_chunk Mbool)) Cur Readable with
      | left hpp =>
          have hpp' : range_perm m b ofs (zAdd ofs (size_chunk Mint8unsigned)) Cur Readable := by
            simpa [hs] using hpp
          cases hq : range_perm_dec m b ofs (zAdd ofs (size_chunk Mint8unsigned)) Cur Readable with
          | left _ => rfl
          | right hn => exact False.elim (hn hpp')
      | right hnp =>
          have hnp' : ¬ range_perm m b ofs (zAdd ofs (size_chunk Mint8unsigned)) Cur Readable := by
            intro hq
            apply hnp
            simpa [hs] using hq
          cases hq : range_perm_dec m b ofs (zAdd ofs (size_chunk Mint8unsigned)) Cur Readable with
          | left hp => exact False.elim (hnp' hp)
          | right _ => rfl
    have hdivide :
        boolOfSumbool (zdivide_dec (align_chunk Mbool) ofs) =
          boolOfSumbool (zdivide_dec (align_chunk Mint8unsigned) ofs) := by
      cases hp : zdivide_dec (align_chunk Mbool) ofs with
      | left hpp =>
          have hpp' : zDivide (align_chunk Mint8unsigned) ofs := by
            simpa [ha] using hpp
          cases hq : zdivide_dec (align_chunk Mint8unsigned) ofs with
          | left _ => rfl
          | right hn => exact False.elim (hn hpp')
      | right hnp =>
          have hnp' : ¬ zDivide (align_chunk Mint8unsigned) ofs := by
            intro hq
            apply hnp
            simpa [ha] using hq
          cases hq : zdivide_dec (align_chunk Mint8unsigned) ofs with
          | left hp => exact False.elim (hnp' hp)
          | right _ => rfl
    rw [hvalid_bool Mbool, hvalid_bool Mint8unsigned, hrange, hdivide]
  rw [hbool_eq]
  cases hbool : boolOfSumbool (valid_access_dec m Mint8unsigned b ofs Readable) with
  | false =>
      simp [hbool]
      rfl
  | true =>
      have hdecode : decode_val Mbool (getN 1 ofs (PMap.get b m.mem_contents)) =
          Val.norm_bool (decode_val Mint8unsigned
            (getN 1 ofs (PMap.get b m.mem_contents))) := by
        unfold decode_val
        cases hp : proj_bytes (getN 1 ofs (PMap.get b m.mem_contents)) with
        | none => simp [hp, Val.norm_bool]
        | some bl => simp [hp]
      simpa [hbool, option_map, hdecode]

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

namespace Mem

theorem load_loadbytes : load_loadbytesStatement := by
  intro chunk m b ofs v hload
  refine ⟨getN (size_chunk_nat chunk) ofs (PMap.get b m.mem_contents), ?_, ?_⟩
  · have hperm : range_perm m b ofs (zAdd ofs (size_chunk chunk)) Cur Readable :=
      (load_valid_access m chunk b ofs v hload).1
    unfold loadbytes
    cases hdec : range_perm_dec m b ofs (zAdd ofs (size_chunk chunk)) Cur Readable with
    | left _ => simp [boolOfSumbool, hdec, size_chunk_nat]
    | right hnot => exact False.elim (hnot hperm)
  · exact load_result chunk m b ofs v hload

theorem getN_length : getN_lengthStatement := by
  intro c n p
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [getN, ih]

theorem loadbytes_length : loadbytes_lengthStatement := by
  intro m b ofs n bytes hload
  unfold loadbytes at hload
  cases hdec : range_perm_dec m b ofs (zAdd ofs n) Cur Readable with
  | left _ =>
      simp [boolOfSumbool, hdec] at hload
      subst bytes
      exact getN_length (PMap.get b m.mem_contents) (zToNat n) ofs
  | right _ => simp [boolOfSumbool, hdec] at hload

theorem loadbytes_empty : loadbytes_emptyStatement := by
  intro m b ofs n hn
  unfold loadbytes
  have hperm : range_perm m b ofs (zAdd ofs n) Cur Readable := by
    apply range_perm_vacuous
    change intOfZ (zAdd ofs n) ≤ intOfZ ofs
    change intOfZ (zOfInt (intOfZ ofs + intOfZ n)) ≤ intOfZ ofs
    rw [intOfZ_zOfInt]
    change intOfZ n ≤ 0 at hn
    omega
  have hnat : zToNat n = 0 := Z_to_nat_neg n hn
  cases hdec : range_perm_dec m b ofs (zAdd ofs n) Cur Readable with
  | left _ => simp [boolOfSumbool, hdec, hnat, getN]
  | right hnot => exact False.elim (hnot hperm)

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps

namespace Mem

private theorem zadd_succ_nat_memproof (p : Z) (n : Nat) :
    zAdd (zAdd p z1) (zOfNat n) = zAdd p (zOfNat (Nat.succ n)) := by
  apply intOfZ_injective
  simp only [intOfZ_zadd_mem, intOfZ_zofnat_mem]
  have hnat : Int.ofNat (Nat.succ n) = Int.ofNat n + 1 := by
    simpa using (Int.ofNat_add_ofNat n 1).symm
  have hz1 : intOfZ z1 = (1 : Int) := by rfl
  rw [hnat, hz1]
  omega

theorem getN_concat : getN_concatStatement := by
  intro c n1
  induction n1 with
  | zero =>
      intro n2 p
      have hz0 : zAdd p (zOfNat 0) = p := by
        apply intOfZ_injective
        simp only [intOfZ_zadd_mem, intOfZ_zofnat_mem]
        simp
      rw [show 0 + n2 = n2 by omega]
      simp only [getN, List.nil_append]
      rw [hz0]
  | succ n1 ih =>
      intro n2 p
      rw [show n1 + 1 + n2 = (n1 + n2) + 1 by omega]
      simp only [getN, List.cons_append]
      rw [ih]
      rw [zadd_succ_nat_memproof]

end Mem

end CompCert4Lean.Common.Memory
namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps

namespace Mem

private theorem zToNat_add_nonneg_memproof (a b : Z)
    (ha : zLe z0 a) (hb : zLe z0 b) :
    zToNat (zAdd a b) = zToNat a + zToNat b := by
  change Int.toNat (intOfZ (zAdd a b)) =
    Int.toNat (intOfZ a) + Int.toNat (intOfZ b)
  rw [intOfZ_zadd_mem]
  have ha' : 0 ≤ intOfZ a := ha
  have hb' : 0 ≤ intOfZ b := hb
  have hia : Int.ofNat (Int.toNat (intOfZ a)) = intOfZ a :=
    Int.toNat_of_nonneg ha'
  have hib : Int.ofNat (Int.toNat (intOfZ b)) = intOfZ b :=
    Int.toNat_of_nonneg hb'
  have hsum_nonneg : 0 ≤ intOfZ a + intOfZ b := by omega
  exact Int.toNat_add ha' hb'

theorem loadbytes_concat : loadbytes_concatStatement := by
  intro m b ofs n1 n2 bytes1 bytes2 h1 h2 hn1 hn2
  unfold loadbytes at h1 h2 ⊢
  cases hdec1 : range_perm_dec m b ofs (zAdd ofs n1) Cur Readable with
  | right hn => simp [boolOfSumbool, hdec1] at h1
  | left hr1 =>
      cases hdec2 : range_perm_dec m b (zAdd ofs n1)
          (zAdd (zAdd ofs n1) n2) Cur Readable with
      | right hn => simp [boolOfSumbool, hdec2] at h2
      | left hr2 =>
          have hperm : range_perm m b ofs (zAdd ofs (zAdd n1 n2)) Cur Readable := by
            intro ofs0 hof
            by_cases hlt : intOfZ ofs0 < intOfZ (zAdd ofs n1)
            · apply hr1 ofs0
              constructor
              · exact hof.1
              · change intOfZ ofs0 < intOfZ (zAdd ofs n1)
                exact hlt
            · apply hr2 ofs0
              constructor
              · have hmid : intOfZ (zAdd ofs n1) ≤ intOfZ ofs0 := by omega
                change intOfZ (zAdd ofs n1) ≤ intOfZ ofs0
                exact hmid
              · change intOfZ ofs0 < intOfZ (zAdd (zAdd ofs n1) n2)
                change intOfZ ofs ≤ intOfZ ofs0 ∧
                  intOfZ ofs0 < intOfZ (zAdd ofs (zAdd n1 n2)) at hof
                have hsum :
                    intOfZ (zAdd (zAdd ofs n1) n2) =
                      intOfZ (zAdd ofs (zAdd n1 n2)) := by
                  rw [intOfZ_zadd_mem, intOfZ_zadd_mem,
                    intOfZ_zadd_mem, intOfZ_zadd_mem]
                  omega
                rw [hsum]
                exact hof.2
          have hnadd : zToNat (zAdd n1 n2) = zToNat n1 + zToNat n2 :=
            zToNat_add_nonneg_memproof n1 n2 hn1 hn2
          simp [boolOfSumbool, hdec1] at h1
          simp [boolOfSumbool, hdec2] at h2
          cases hdec3 : range_perm_dec m b ofs (zAdd ofs (zAdd n1 n2)) Cur Readable with
          | right hn => exact False.elim (hn hperm)
          | left _ =>
            simp [boolOfSumbool, hdec3]
            rw [hnadd]
            rw [getN_concat]
            have hn1z : zOfNat (zToNat n1) = n1 :=
              (ZArith.Znat.Z2Nat.id n1 hn1)
            rw [hn1z]
            rw [h1, h2]

theorem loadbytes_split : loadbytes_splitStatement := by
  intro m b ofs n1 n2 bytes hload hn1 hn2
  unfold loadbytes at hload ⊢
  cases hdec : range_perm_dec m b ofs (zAdd ofs (zAdd n1 n2)) Cur Readable with
  | right hn => simp [boolOfSumbool, hdec] at hload
  | left hr =>
      have hr1 : range_perm m b ofs (zAdd ofs n1) Cur Readable := by
        intro ofs0 hof
        apply hr ofs0
        constructor
        · exact hof.1
        · change intOfZ ofs0 < intOfZ (zAdd ofs (zAdd n1 n2))
          change intOfZ ofs ≤ intOfZ ofs0 ∧
            intOfZ ofs0 < intOfZ (zAdd ofs n1) at hof
          have hofs :
              intOfZ (zAdd ofs (zAdd n1 n2)) =
                intOfZ ofs + intOfZ n1 + intOfZ n2 := by
            rw [intOfZ_zadd_mem, intOfZ_zadd_mem]
            simp [Int.add_assoc]
          have hn2' : (0 : Int) ≤ intOfZ n2 := hn2
          rw [hofs]
          have hlt1 : intOfZ ofs0 < intOfZ ofs + intOfZ n1 := by
            simpa only [intOfZ_zadd_mem] using hof.2
          omega
      have hr2 : range_perm m b (zAdd ofs n1)
          (zAdd (zAdd ofs n1) n2) Cur Readable := by
        intro ofs0 hof
        apply hr ofs0
        constructor
        · rcases hof with ⟨hoflo, hofhi⟩
          change intOfZ (zAdd ofs n1) ≤ intOfZ ofs0 at hoflo
          change intOfZ ofs ≤ intOfZ ofs0
          have hmid : intOfZ ofs + intOfZ n1 ≤ intOfZ ofs0 := by
            simpa only [intOfZ_zadd_mem] using hoflo
          have hn1' : (0 : Int) ≤ intOfZ n1 := hn1
          omega
        · rcases hof with ⟨hoflo, hofhi⟩
          change intOfZ ofs0 < intOfZ (zAdd ofs (zAdd n1 n2))
          have hupper :
              intOfZ (zAdd (zAdd ofs n1) n2) =
                intOfZ (zAdd ofs (zAdd n1 n2)) := by
            rw [intOfZ_zadd_mem, intOfZ_zadd_mem,
              intOfZ_zadd_mem, intOfZ_zadd_mem]
            simp [Int.add_assoc]
          change intOfZ ofs0 < intOfZ (zAdd (zAdd ofs n1) n2) at hofhi
          rw [← hupper]
          exact hofhi
      have hnadd : zToNat (zAdd n1 n2) = zToNat n1 + zToNat n2 :=
        zToNat_add_nonneg_memproof n1 n2 hn1 hn2
      have hn1z : zOfNat (zToNat n1) = n1 :=
        (ZArith.Znat.Z2Nat.id n1 hn1)
      simp [boolOfSumbool, hdec] at hload
      rw [hnadd, getN_concat, hn1z] at hload
      cases hdec1 : range_perm_dec m b ofs (zAdd ofs n1) Cur Readable with
      | right hn => exact False.elim (hn hr1)
      | left _ =>
          cases hdec2 : range_perm_dec m b (zAdd ofs n1)
              (zAdd (zAdd ofs n1) n2) Cur Readable with
          | right hn => exact False.elim (hn hr2)
          | left _ =>
              refine ⟨getN (zToNat n1) ofs (PMap.get b m.mem_contents),
                getN (zToNat n2) (zAdd ofs n1) (PMap.get b m.mem_contents), ?_, ?_, ?_⟩
              · simp [boolOfSumbool, hdec1]
              · simp [boolOfSumbool, hdec2]
              · exact hload.symm

theorem load_int64_split : load_int64_splitStatement := by
  intro m b ofs v hload hptr
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem addressing_int64_split : addressing_int64_splitStatement := by
  intro i hptr hdiv
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory
namespace Mem
theorem loadv_int64_split : loadv_int64_splitStatement := by
  intro m a v hload hptr
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr
end Mem
end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

def valid_access_store : valid_access_storeStatement := by
  intro m1 chunk b ofs v hvalid
  unfold store
  cases hdec : valid_access_dec m1 chunk b ofs Memtype.Writable with
  | left hproof =>
      simp [boolOfSumbool, hdec]
      exact ⟨_, rfl⟩
  | right hnproof =>
      exact False.elim (hnproof hvalid)

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem store_access : store_accessStatement := by
  intro chunk m1 b ofs v m2 hstore
  unfold store at hstore
  split at hstore
  · cases hstore
    rfl
  · cases hstore

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem store_mem_contents : store_mem_contentsStatement := by
  intro chunk m1 b ofs v m2 hstore
  unfold store at hstore
  split at hstore
  · cases hstore
    rfl
  · cases hstore

theorem perm_store_1 : perm_store_1Statement := by
  intro chunk m1 b ofs v m2 hstore b' ofs' k p hperm
  unfold store at hstore
  split at hstore
  · cases hstore
    exact hperm
  · cases hstore

theorem perm_store_2 : perm_store_2Statement := by
  intro chunk m1 b ofs v m2 hstore b' ofs' k p hperm
  unfold store at hstore
  split at hstore
  · cases hstore
    exact hperm
  · cases hstore

theorem nextblock_store : nextblock_storeStatement := by
  intro chunk m1 b ofs v m2 hstore
  unfold store at hstore
  split at hstore
  · cases hstore
    rfl
  · cases hstore

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem store_valid_block_1 : store_valid_block_1Statement := by
  intro chunk m1 b ofs v m2 hstore b' hvalid
  unfold valid_block at hvalid ⊢
  have hnext : m2.nextblock = m1.nextblock :=
    nextblock_store chunk m1 b ofs v m2 hstore
  rw [hnext]
  exact hvalid

theorem store_valid_access_1 : store_valid_access_1Statement := by
  intro chunk m1 b ofs v m2 hstore chunk' b' ofs' p hvalid
  unfold valid_access at hvalid ⊢
  rcases hvalid with ⟨hrange, halign⟩
  constructor
  · intro ofs0 hof
    exact perm_store_1 chunk m1 b ofs v m2 hstore b' ofs0 Memtype.Cur p
      (hrange ofs0 hof)
  · exact halign

theorem store_valid_access_3 : store_valid_access_3Statement := by
  intro chunk m1 b ofs v m2 hstore
  unfold store at hstore
  cases hdec : valid_access_dec m1 chunk b ofs Memtype.Writable with
  | left hvalid =>
      simp [boolOfSumbool, hdec] at hstore
      exact hvalid
  | right hnot =>
      simp [boolOfSumbool, hdec] at hstore

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps
namespace Mem

theorem loadbytes_store_same : loadbytes_store_sameStatement := by
  intro chunk m1 b ofs v m2 hstore
  have hv : valid_access m2 chunk b ofs Readable := by
    apply store_valid_access_1 chunk m1 b ofs v m2 hstore chunk b ofs Readable
    exact valid_access_implies m1 chunk b ofs Writable Readable
      (store_valid_access_3 chunk m1 b ofs v m2 hstore) perm_W_R
  have hrange : range_perm m2 b ofs (zAdd ofs (size_chunk chunk)) Cur Readable := hv.1
  unfold loadbytes
  cases hdec : range_perm_dec m2 b ofs (zAdd ofs (size_chunk chunk)) Cur Readable with
  | right hn => exact False.elim (hn hrange)
  | left hp =>
      simp [boolOfSumbool, hdec]
      rw [store_mem_contents chunk m1 b ofs v m2 hstore, pmapGetSetSame]
      change getN (size_chunk_nat chunk) ofs
        (setN (encode_val chunk v) ofs (PMap.get b m1.mem_contents)) =
        encode_val chunk v
      rw [← CompCert4Lean.Common.Memdata.encode_val_length]
      rw [getN_setN_same]

end Mem
end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps
namespace Mem

theorem load_store_other : load_store_otherStatement := by
  intro chunk m1 b ofs v m2 hstore chunk' b' ofs' hcond
  have valid_access_2_to_1 : ∀ {ch b0 o p},
      valid_access m2 ch b0 o p → valid_access m1 ch b0 o p := by
    intro ch b0 o p hv
    unfold valid_access at hv ⊢
    constructor
    · intro o0 ho0
      exact perm_store_2 chunk m1 b ofs v m2 hstore b0 o0 Memtype.Cur p
        (hv.1 o0 ho0)
    · exact hv.2
  unfold load
  cases hdec1 : valid_access_dec m1 chunk' b' ofs' Readable with
  | right hn1 =>
      have hn2 : ¬ valid_access m2 chunk' b' ofs' Readable := by
        intro h2
        exact hn1 (valid_access_2_to_1 h2)
      cases hdec2 : valid_access_dec m2 chunk' b' ofs' Readable with
      | left h2 => exact False.elim (hn2 h2)
      | right _ => simp [boolOfSumbool, hdec1, hdec2]
  | left h1 =>
      have h2 : valid_access m2 chunk' b' ofs' Readable :=
        store_valid_access_1 chunk m1 b ofs v m2 hstore chunk' b' ofs' Readable h1
      cases hdec2 : valid_access_dec m2 chunk' b' ofs' Readable with
      | right hn2 => exact False.elim (hn2 h2)
      | left _ =>
          simp only [boolOfSumbool, hdec1, hdec2, ↓reduceIte]
          congr 1
          rw [store_mem_contents chunk m1 b ofs v m2 hstore]
          by_cases hb : b' = b
          · subst b'
            rw [pmapGetSetSame]
            have hget : getN (size_chunk_nat chunk') ofs'
                (setN (encode_val chunk v) ofs (PMap.get b m1.mem_contents)) =
                getN (size_chunk_nat chunk') ofs' (PMap.get b m1.mem_contents) := by
              apply getN_setN_outside (encode_val chunk v) ofs
              have hsize : zOfNat (size_chunk_nat chunk') = size_chunk chunk' := by
                cases chunk' <;> rfl
              have hsize0 : zOfNat (size_chunk_nat chunk) = size_chunk chunk := by
                cases chunk <;> rfl
              rcases hcond with hneq | hleft | hright
              · exact False.elim (hneq rfl)
              · left
                simpa [hsize] using hleft
              · right
                have hlen : (encode_val chunk v).length = size_chunk_nat chunk :=
                  CompCert4Lean.Common.Memdata.encode_val_length chunk v
                simpa [hsize0, hlen] using hright
            rw [hget]
          · rw [pmapGetSetOther _ _ _ _ hb]

end Mem
end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
namespace Mem

theorem loadbytes_store_other : loadbytes_store_otherStatement := by
  intro chunk m1 b ofs v m2 hstore b' ofs' n hcond
  have range_perm_1_to_2 :
      range_perm m1 b' ofs' (zAdd ofs' n) Cur Readable →
        range_perm m2 b' ofs' (zAdd ofs' n) Cur Readable := by
    intro hrange o ho
    exact perm_store_1 chunk m1 b ofs v m2 hstore b' o Cur Readable (hrange o ho)
  have range_perm_2_to_1 :
      range_perm m2 b' ofs' (zAdd ofs' n) Cur Readable →
        range_perm m1 b' ofs' (zAdd ofs' n) Cur Readable := by
    intro hrange o ho
    exact perm_store_2 chunk m1 b ofs v m2 hstore b' o Cur Readable (hrange o ho)
  unfold loadbytes
  cases hdec1 : range_perm_dec m1 b' ofs' (zAdd ofs' n) Cur Readable with
  | right hn1 =>
      have hn2 : ¬ range_perm m2 b' ofs' (zAdd ofs' n) Cur Readable := by
        intro h2
        exact hn1 (range_perm_2_to_1 h2)
      cases hdec2 : range_perm_dec m2 b' ofs' (zAdd ofs' n) Cur Readable with
      | left h2 => exact False.elim (hn2 h2)
      | right _ => simp [boolOfSumbool, hdec1, hdec2]
  | left h1 =>
      have h2 : range_perm m2 b' ofs' (zAdd ofs' n) Cur Readable :=
        range_perm_1_to_2 h1
      cases hdec2 : range_perm_dec m2 b' ofs' (zAdd ofs' n) Cur Readable with
      | right hn2 => exact False.elim (hn2 h2)
      | left _ =>
          simp only [boolOfSumbool, hdec1, hdec2, ↓reduceIte]
          congr 1
          rw [store_mem_contents chunk m1 b ofs v m2 hstore]
          by_cases hb : b' = b
          · subst b'
            rw [pmapGetSetSame]
            by_cases hn : zLe n z0
            · have hnat : zToNat n = 0 := Z_to_nat_neg n hn
              simp [hnat, getN]
            · have hnnonneg : zLe z0 n := by
                change ¬ intOfZ n ≤ intOfZ z0 at hn
                change intOfZ z0 ≤ intOfZ n
                omega
              have hnat : zOfNat (zToNat n) = n :=
                ZArith.Znat.Z2Nat.id n hnnonneg
              have hsize : zOfNat (encode_val chunk v).length = size_chunk chunk := by
                rw [CompCert4Lean.Common.Memdata.encode_val_length]
                cases chunk <;> rfl
              apply getN_setN_outside (encode_val chunk v) ofs
              rcases hcond with hneq | hnonpos | hleft | hright
              · exact False.elim (hneq rfl)
              · exact False.elim (hn hnonpos)
              · left
                simpa only [hnat] using hleft
              · right
                simpa only [hsize] using hright
          · rw [pmapGetSetOther _ _ _ _ hb]

end Mem
end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Lib.Maps
namespace Mem

theorem setN_in : setN_inStatement := by
  intro vl
  induction vl with
  | nil =>
      intro p q c h
      have hfalse : False := by
        have hlo := h.1
        have hlt := h.2
        change intOfZ p ≤ intOfZ q at hlo
        change intOfZ q < intOfZ (zAdd p (zOfNat (List.length ([] : List memval)))) at hlt
        rw [show List.length ([] : List memval) = 0 by rfl]
          at hlt
        rw [intOfZ_zadd_mem, intOfZ_zofnat_mem] at hlt
        have hzero : Int.ofNat 0 = 0 := by rfl
        rw [hzero] at hlt
        omega
      exact hfalse.elim
  | cons v rest ih =>
      intro p q c h
      by_cases hpq : q = p
      · subst q
        have hhead :
            ZMap.get p (setN rest (zAdd p z1) (ZMap.set p v c)) =
              ZMap.get p (ZMap.set p v c) := by
          apply setN_other
          intro r hr
          intro hrp
          subst r
          have hrlo := hr.1
          change intOfZ (zAdd p z1) ≤ intOfZ p at hrlo
          rw [intOfZ_add_one] at hrlo
          omega
        have hset : ZMap.get p (ZMap.set p v c) = v := by
          change PMap.get (ZIndexed.index p)
            (PMap.set (ZIndexed.index p) v c) = v
          exact pmap_get_set_same_memproof _ _ _
        change ZMap.get p (setN rest (zAdd p z1) (ZMap.set p v c)) ∈ v :: rest
        rw [hhead, hset]
        exact List.mem_cons_self
      · right
        apply ih (p := zAdd p z1) (q := q) (c := ZMap.set p v c)
        constructor
        · have hlo := h.1
          have hne : intOfZ q ≠ intOfZ p := by
            intro heq
            apply hpq
            exact intOfZ_injective heq
          change intOfZ (zAdd p z1) ≤ intOfZ q
          change intOfZ p ≤ intOfZ q at hlo
          rw [intOfZ_add_one]
          omega
        · have hhi := h.2
          change intOfZ q <
            intOfZ (zAdd p (zOfNat (List.length (v :: rest)))) at hhi
          change intOfZ q <
            intOfZ (zAdd (zAdd p z1) (zOfNat rest.length))
          have hnat : Int.ofNat (rest.length + 1) = Int.ofNat rest.length + 1 := by
            simpa using (Int.ofNat_add_ofNat rest.length 1).symm
          rw [show (v :: rest).length = rest.length + 1 by rfl]
            at hhi
          rw [intOfZ_zadd_mem, intOfZ_zofnat_mem, hnat] at hhi
          rw [intOfZ_zadd_mem, intOfZ_zadd_mem, intOfZ_zofnat_mem]
          have hz1 : intOfZ z1 = (1 : Int) := by rfl
          rw [hz1]
          omega

end Mem
end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

namespace Mem

theorem getN_in : getN_inStatement := by
  intro c q n
  induction n with
  | zero =>
      intro p h
      rcases h with ⟨hpq, hqp⟩
      change intOfZ p ≤ intOfZ q at hpq
      change intOfZ q < intOfZ (zAdd p (zOfNat 0)) at hqp
      rw [intOfZ_zadd_mem, intOfZ_zofnat_mem] at hqp
      have hqp' : intOfZ q < intOfZ p := by simpa using hqp
      omega
  | succ n ih =>
      intro p h
      simp only [getN, List.mem_cons]
      by_cases hpq : p = q
      · subst q
        exact Or.inl rfl
      · right
        apply ih (p := zAdd p z1)
        rcases h with ⟨hpq', hqend⟩
        constructor
        · change intOfZ (zAdd p z1) ≤ intOfZ q
          change intOfZ p ≤ intOfZ q at hpq'
          have hpqne : intOfZ p ≠ intOfZ q := by
            intro heq
            apply hpq
            exact intOfZ_injective heq
          rw [intOfZ_add_one]
          omega
        · change intOfZ q <
              intOfZ (zAdd (zAdd p z1) (zOfNat n))
          change intOfZ q < intOfZ (zAdd p (zOfNat (Nat.succ n))) at hqend
          have hnat : Int.ofNat (Nat.succ n) = Int.ofNat n + 1 := by
            simpa using (Int.ofNat_add_ofNat n 1).symm
          rw [intOfZ_zadd_mem, intOfZ_zofnat_mem, hnat] at hqend
          rw [intOfZ_zadd_mem, intOfZ_zadd_mem, intOfZ_zofnat_mem]
          have hz1 : intOfZ z1 = (1 : Int) := by rfl
          rw [hz1]
          omega

end Mem

end CompCert4Lean.Common.Memory
namespace CompCert4Lean.Common.Memory
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
namespace Mem

theorem load_store_overlap : load_store_overlapStatement := by
  intro chunk m1 b ofs v m2 chunk' ofs' v' hstore hload hleft hright
  obtain ⟨sz, hsz⟩ := size_chunk_nat_pos chunk
  obtain ⟨sz', hsz'⟩ := size_chunk_nat_pos chunk'
  have hloadres := load_result chunk' m2 b ofs' v' hload
  let c := PMap.get b m1.mem_contents
  let c' := setN (encode_val chunk v) ofs c
  have hloadc : v' = decode_val chunk' (getN (size_chunk_nat chunk') ofs' c') := by
    simpa [c, c', store_mem_contents chunk m1 b ofs v m2 hstore,
      pmapGetSetSame] using hloadres
  cases henc : encode_val chunk v with
  | nil =>
      have hlen := encode_val_length chunk v
      rw [henc, hsz] at hlen
      simp at hlen
  | cons mv1 mvl =>
      have hshapeEnc : shape_encoding chunk v (mv1 :: mvl) := by
        rw [← henc]
        exact encode_val_shape chunk v
      have hlen : (mv1 :: mvl).length = size_chunk_nat chunk := by
        simpa [henc] using (encode_val_length chunk v)
      let mv1' := ZMap.get ofs' c'
      let mvl' := getN sz' (zAdd ofs' z1) c'
      have hloadc' : v' = decode_val chunk' (mv1' :: mvl') := by
        rw [hsz'] at hloadc
        simpa [getN, mv1', mvl'] using hloadc
      have hshapeDec : shape_decoding chunk' (mv1' :: mvl') v' := by
        rw [hloadc']
        exact decode_val_shape chunk' mv1' mvl'
      have hhead : ZMap.get ofs c' = mv1 := by
        dsimp [c']
        rw [henc]
        change ZMap.get ofs (setN mvl (zAdd ofs z1) (ZMap.set ofs mv1 c)) = mv1
        have htail : ZMap.get ofs (setN mvl (zAdd ofs z1) (ZMap.set ofs mv1 c)) =
            ZMap.get ofs (ZMap.set ofs mv1 c) := by
          apply setN_other
          intro r hr
          rcases hr with ⟨hrlo, hrhi⟩
          intro hro
          subst r
          change intOfZ (zAdd ofs z1) ≤ intOfZ ofs at hrlo
          rw [intOfZ_add_one] at hrlo
          omega
        rw [htail]
        change PMap.get (ZIndexed.index ofs) (PMap.set (ZIndexed.index ofs) mv1 c) = mv1
        exact pmap_get_set_same_memproof _ _ _
      refine ⟨mv1, mvl, mv1', mvl', hshapeEnc, hshapeDec, ?_⟩
      by_cases heq : ofs' = ofs
      · left
        subst ofs'
        constructor
        · rfl
        · simpa [mv1'] using hhead
      · have hneInt : intOfZ ofs ≠ intOfZ ofs' := by
          intro he
          apply heq
          exact (intOfZ_injective he).symm
        by_cases hlt : zLt ofs ofs'
        · right
          left
          constructor
          · exact hlt
          · dsimp [mv1', c']
            rw [henc]
            change ZMap.get ofs' (setN mvl (zAdd ofs z1) (ZMap.set ofs mv1 c)) ∈ mvl
            apply setN_in
            constructor
            · change intOfZ (zAdd ofs z1) ≤ intOfZ ofs'
              change intOfZ ofs < intOfZ ofs' at hlt
              rw [intOfZ_add_one]
              omega
            · change intOfZ ofs' < intOfZ (zAdd (zAdd ofs z1) (zOfNat mvl.length))
              have hsize : zOfNat (mv1 :: mvl).length = size_chunk chunk := by
                rw [hlen]
                cases chunk <;> rfl
              change intOfZ ofs' < intOfZ (zAdd ofs (size_chunk chunk)) at hright
              rw [show (mv1 :: mvl).length = mvl.length + 1 by rfl] at hsize
              have hsizeInt : intOfZ (size_chunk chunk) = Int.ofNat mvl.length + 1 := by
                have hh := congrArg intOfZ hsize
                rw [intOfZ_zofnat_mem] at hh
                change Int.ofNat (mvl.length + 1) = intOfZ (size_chunk chunk) at hh
                have hnat : Int.ofNat (mvl.length + 1) = Int.ofNat mvl.length + 1 := by
                  simpa using (Int.ofNat_add_ofNat mvl.length 1).symm
                rw [hnat] at hh
                exact hh.symm
              have hz1 : intOfZ z1 = (1 : Int) := by rfl
              rw [intOfZ_zadd_mem, intOfZ_zadd_mem, intOfZ_zofnat_mem, hz1]
              rw [intOfZ_zadd_mem, hsizeInt] at hright
              omega
        · right
          right
          constructor
          · change intOfZ ofs' < intOfZ ofs
            have hlt' : ¬ intOfZ ofs < intOfZ ofs' := by
              intro h'
              apply hlt
              change intOfZ ofs < intOfZ ofs'
              exact h'
            omega
          · dsimp [mvl']
            rw [← hhead]
            apply getN_in
            constructor
            · change intOfZ (zAdd ofs' z1) ≤ intOfZ ofs
              have hlt' : intOfZ ofs' < intOfZ ofs := by
                have hnot : ¬ intOfZ ofs < intOfZ ofs' := by
                  intro h'
                  apply hlt
                  change intOfZ ofs < intOfZ ofs'
                  exact h'
                omega
              rw [intOfZ_add_one]
              omega
            · change intOfZ ofs < intOfZ (zAdd (zAdd ofs' z1) (zOfNat sz'))
              change intOfZ ofs < intOfZ (zAdd ofs' (size_chunk chunk')) at hleft
              have hsize' : intOfZ (size_chunk chunk') = Int.ofNat sz' + 1 := by
                have hnat : intOfZ (size_chunk chunk') = Int.ofNat (size_chunk_nat chunk') := by
                  cases chunk' <;> rfl
                rw [hnat, hsz']
                simpa using (Int.ofNat_add_ofNat sz' 1).symm
              simp only [intOfZ_zadd_mem, intOfZ_zofnat_mem] at hleft ⊢
              rw [hsize'] at hleft
              have hz1 : intOfZ z1 = (1 : Int) := by rfl
              simp [hz1] at hleft ⊢
              omega

end Mem
end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory
namespace Mem

theorem compat_pointer_chunks_true : compat_pointer_chunks_trueStatement := by
  intro chunk1 chunk2 h1 h2 hq
  rcases h1 with rfl | rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl | rfl <;>
    simp [Memdata.quantity_chunk, compat_pointer_chunks] at hq ⊢

end Mem
end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
namespace Mem

theorem load_pointer_store : load_pointer_storeStatement := by
  intro chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o hstore hload
  by_cases hb : b' = b
  · subst b'
    by_cases hleft : zLe (zAdd ofs' (size_chunk chunk')) ofs
    · exact Or.inr (Or.inr (Or.inl hleft))
    by_cases hright : zLe (zAdd ofs (size_chunk chunk)) ofs'
    · exact Or.inr (Or.inr (Or.inr hright))
    have hlt1 : zLt ofs (zAdd ofs' (size_chunk chunk')) := by
      change intOfZ ofs < intOfZ (zAdd ofs' (size_chunk chunk'))
      change ¬ intOfZ (zAdd ofs' (size_chunk chunk')) ≤ intOfZ ofs at hleft
      omega
    have hlt2 : zLt ofs' (zAdd ofs (size_chunk chunk)) := by
      change intOfZ ofs' < intOfZ (zAdd ofs (size_chunk chunk))
      change ¬ intOfZ (zAdd ofs (size_chunk chunk)) ≤ intOfZ ofs' at hright
      omega
    obtain ⟨mv1, mvl, mv1', mvl', henc, hdec, hcases⟩ :=
      load_store_overlap chunk m1 b ofs v m2 chunk' ofs' (Vptr v_b v_o)
        hstore hload hlt1 hlt2
    have hdec_inv : ∀ (mv : memval) (tail : List memval) (w : val),
        shape_decoding chunk' (mv :: tail) w →
        w = Vptr v_b v_o →
        ∃ vv q i, mv = Fragment vv q i ∧
          (chunk' = Mint32 ∨ chunk' = Many32 ∨ chunk' = Mint64 ∨ chunk' = Many64) ∧
          q = quantity_chunk chunk' ∧
          Nat.succ i = size_quantity_nat q ∧
          Vptr v_b v_o = Val.load_result chunk' vv := by
      intro mv tail w hh hw
      cases hh with
      | fragment vv q i mvl hch hq hi htail =>
          exact ⟨vv, q, i, by simp, hch, hq, hi, hw.symm⟩
      | shape_decoding_b bb mvl vv hv htail =>
          exfalso
          simpa [hw] using hv
      | shape_decoding_u mvl =>
          cases hw
    have hdec_tail : ∀ (mv : memval) (head : memval) (tail : List memval) (w : val),
        shape_decoding chunk' (head :: tail) w →
        w = Vptr v_b v_o →
        mv ∈ tail →
        ∃ vv q j, mv = Fragment vv q j ∧
          Nat.succ j ≠ size_quantity_nat q := by
      intro mv head tail w hh hw hm
      cases hh with
      | fragment vv q i mvl hch hq hi htail =>
          obtain ⟨j, hj, hjne⟩ := htail mv hm
          exact ⟨vv, q, j, hj, hjne⟩
      | shape_decoding_b bb mvl vv hv htail =>
          exact False.elim (by simpa [hw] using hv)
      | shape_decoding_u mvl =>
          cases hw
    cases hcases with
    | inl heq =>
        rcases heq with ⟨heqofs, heqmv⟩
        subst ofs'
        obtain ⟨vv, q, i, hmv, hchunk', hq', hi', hval⟩ :=
          hdec_inv mv1' mvl' (Vptr v_b v_o) hdec rfl
        subst mv1'
        have henc' : v = vv ∧
            (chunk = Mint32 ∨ chunk = Many32 ∨ chunk = Mint64 ∨ chunk = Many64) ∧
            q = quantity_chunk chunk := by
          cases henc with
          | fragment q0 i0 tail0 hch hq0 hi0 htail0 => simp_all
          | bytes b0 tail0 hv htail => simp_all
          | undef tail0 htail => simp_all
        have hvv : vv = Vptr v_b v_o := by
          cases chunk' <;> cases vv <;>
            simp only [Val.load_result, CompCert4Lean.X86_64.Archi.ptr64] at hval
          all_goals try contradiction
          all_goals cases hval; rfl
        have hcomp : compat_pointer_chunks chunk chunk' := by
          exact compat_pointer_chunks_true chunk chunk' henc'.2.1 hchunk'
            (by rw [← henc'.2.2, hq'])
        exact Or.inl ⟨by simpa [hvv] using henc'.1, hcomp, rfl, rfl⟩
    | inr hrest =>
        cases hrest with
        | inl hgt =>
            rcases hgt with ⟨_, hmem⟩
            cases henc with
            | fragment q0 i0 tail0 hch hq0 hi0 htail0 =>
                obtain ⟨j, hj, hjne⟩ := htail0 mv1' hmem
                obtain ⟨vv, q', i', hmv, hch', hq', hi', hval'⟩ :=
                  hdec_inv mv1' mvl' (Vptr v_b v_o) hdec rfl
                rw [hmv] at hj
                have hiTmp := hi'
                have hqTmp := hq'
                cases hj
                exact False.elim (hjne (by simpa [hq0, hqTmp] using hiTmp))
            | bytes b0 tail0 hv htail0 =>
                obtain ⟨b', hb'⟩ := htail0 mv1' hmem
                obtain ⟨vv, q', i', hmv, hch', hq', hi', hval'⟩ :=
                  hdec_inv mv1' mvl' (Vptr v_b v_o) hdec rfl
                rw [hmv] at hb'
                cases hb'
            | undef tail0 htail0 =>
                have hmveq : mv1' = Undef := htail0 mv1' hmem
                obtain ⟨vv, q', i', hmv, hch', hq', hi', hval'⟩ :=
                  hdec_inv mv1' mvl' (Vptr v_b v_o) hdec rfl
                rw [hmv] at hmveq
                cases hmveq
        | inr hlt =>
            rcases hlt with ⟨_, hmem⟩
            obtain ⟨jv, qv, j, hj, hjne⟩ :=
              hdec_tail mv1 mv1' mvl' (Vptr v_b v_o) hdec rfl hmem
            cases henc with
            | fragment q0 i0 tail0 hch hq0 hi0 htail0 =>
                have hi0Tmp := hi0
                cases hj
                exact False.elim (hjne (by simpa [hq0] using hi0Tmp))
            | bytes b0 tail0 hv htail0 =>
                cases hj
            | undef tail0 htail0 =>
                cases hj
  · exact Or.inr (Or.inl hb)

end Mem
end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype

namespace Mem

theorem store_similar_chunks : store_similar_chunksStatement := by
  intro chunk1 chunk2 v1 v2 m b ofs hencode halign
  have hsizeNat : size_chunk_nat chunk1 = size_chunk_nat chunk2 := by
    have hlength := congrArg List.length hencode
    rw [CompCert4Lean.Common.Memdata.encode_val_length chunk1 v1,
      CompCert4Lean.Common.Memdata.encode_val_length chunk2 v2] at hlength
    exact hlength
  have hsize : size_chunk chunk1 = size_chunk chunk2 := by
    rw [size_chunk_conv chunk1, size_chunk_conv chunk2, hsizeNat]
  have hvalid :
      valid_access m chunk1 b ofs Writable ↔
        valid_access m chunk2 b ofs Writable := by
    unfold valid_access
    rw [hsize, halign]
  unfold store
  cases hdec1 : valid_access_dec m chunk1 b ofs Writable with
  | left hv1 =>
      cases hdec2 : valid_access_dec m chunk2 b ofs Writable with
      | left hv2 => simp [boolOfSumbool, hdec1, hdec2, hencode]
      | right hnv2 => exact False.elim (hnv2 (hvalid.mp hv1))
  | right hnv1 =>
      cases hdec2 : valid_access_dec m chunk2 b ofs Writable with
      | left hv2 => exact False.elim (hnv1 (hvalid.mpr hv2))
      | right hnv2 => simp [boolOfSumbool, hdec1, hdec2]

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem store_bool_unsigned_8 : store_bool_unsigned_8Statement := by
  intro m b ofs v
  apply store_similar_chunks
  · cases v <;> rfl
  · rfl

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype

namespace Mem

theorem store_signed_unsigned_8 : store_signed_unsigned_8Statement := by
  intro m b ofs v
  apply store_similar_chunks
  · exact CompCert4Lean.Common.Memdata.encode_val_int8_signed_unsigned v
  · rfl

theorem store_signed_unsigned_16 : store_signed_unsigned_16Statement := by
  intro m b ofs v
  apply store_similar_chunks
  · exact CompCert4Lean.Common.Memdata.encode_val_int16_signed_unsigned v
  · rfl

def range_perm_storebytes : range_perm_storebytesStatement := by
  intro m1 b ofs bytes hperm
  unfold storebytes
  cases hdec : range_perm_dec m1 b ofs (zAdd ofs (zOfNat bytes.length)) Cur Writable with
  | left _ =>
      simp [boolOfSumbool, hdec]
      exact ⟨_, rfl⟩
  | right hn =>
      exact False.elim (hn hperm)

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype

namespace Mem

theorem storebytes_store : storebytes_storeStatement := by
  intro m1 b ofs chunk v m2 hstore halign
  have hlen : zOfNat (encode_val chunk v).length = size_chunk chunk := by
    rw [CompCert4Lean.Common.Memdata.encode_val_length, size_chunk_conv]
  unfold storebytes at hstore
  cases hdec : range_perm_dec m1 b ofs (zAdd ofs (zOfNat (encode_val chunk v).length))
      Cur Writable with
  | right hn =>
      simp [boolOfSumbool, hdec] at hstore
  | left hr =>
      have hr' : range_perm m1 b ofs (zAdd ofs (size_chunk chunk)) Cur Writable := by
        simpa [hlen] using hr
      have hv : valid_access m1 chunk b ofs Writable := ⟨hr', halign⟩
      unfold store
      cases hvalid : valid_access_dec m1 chunk b ofs Writable with
      | right hnvalid => exact False.elim (hnvalid hv)
      | left hp =>
          simp [boolOfSumbool, hvalid, hdec, hlen] at hstore ⊢
          exact hstore

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype

namespace Mem

theorem store_storebytes : store_storebytesStatement := by
  intro m1 b ofs chunk v m2 hstore
  have hlen : zOfNat (encode_val chunk v).length = size_chunk chunk := by
    rw [CompCert4Lean.Common.Memdata.encode_val_length, size_chunk_conv]
  unfold store at hstore
  cases hvalid : valid_access_dec m1 chunk b ofs Writable with
  | right _ => simp [boolOfSumbool, hvalid] at hstore
  | left hv =>
      have hr :
          range_perm m1 b ofs (zAdd ofs (zOfNat (encode_val chunk v).length)) Cur Writable := by
        simpa [hlen] using hv.1
      unfold storebytes
      cases hdec : range_perm_dec m1 b ofs
          (zAdd ofs (zOfNat (encode_val chunk v).length)) Cur Writable with
      | right hn => exact False.elim (hn hr)
      | left _ =>
          simp [boolOfSumbool, hvalid, hdec, hlen] at hstore ⊢
          exact hstore

theorem storebytes_access : storebytes_accessStatement := by
  intro m1 b ofs bytes m2 hstore
  unfold storebytes at hstore
  cases hdec : range_perm_dec m1 b ofs (zAdd ofs (zOfNat bytes.length)) Cur Writable with
  | right _ => simp [boolOfSumbool, hdec] at hstore
  | left _ =>
      simp [boolOfSumbool, hdec] at hstore
      subst m2
      rfl

theorem storebytes_mem_contents : storebytes_mem_contentsStatement := by
  intro m1 b ofs bytes m2 hstore
  unfold storebytes at hstore
  cases hdec : range_perm_dec m1 b ofs (zAdd ofs (zOfNat bytes.length)) Cur Writable with
  | right _ => simp [boolOfSumbool, hdec] at hstore
  | left _ =>
      simp [boolOfSumbool, hdec] at hstore
      subst m2
      rfl

theorem perm_storebytes_1 : perm_storebytes_1Statement := by
  intro m1 b ofs bytes m2 hstore b' ofs' k p hp
  unfold perm at hp ⊢
  rw [storebytes_access m1 b ofs bytes m2 hstore]
  exact hp

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem storebytes_range_perm : storebytes_range_permStatement := by
  intro m1 b ofs bytes m2 hstore
  unfold storebytes at hstore
  cases hdec : range_perm_dec m1 b ofs (zAdd ofs (zOfNat bytes.length))
      CompCert4Lean.Common.Memtype.Cur CompCert4Lean.Common.Memtype.Writable with
  | right _ => simp [boolOfSumbool, hdec] at hstore
  | left hr =>
      simp [boolOfSumbool, hdec] at hstore
      exact hr

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem perm_storebytes_2 : perm_storebytes_2Statement := by
  intro m1 b ofs bytes m2 hstore b' ofs' k p hp
  unfold perm at hp ⊢
  rw [CompCert4Lean.Common.Memory.Mem.storebytes_access m1 b ofs bytes m2 hstore] at hp
  exact hp

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem nextblock_storebytes : nextblock_storebytesStatement := by
  intro m1 b ofs bytes m2 hstore
  unfold storebytes at hstore
  cases hdec : range_perm_dec m1 b ofs (zAdd ofs (zOfNat bytes.length))
      CompCert4Lean.Common.Memtype.Cur CompCert4Lean.Common.Memtype.Writable with
  | right _ => simp [boolOfSumbool, hdec] at hstore
  | left _ =>
      simp [boolOfSumbool, hdec] at hstore
      subst m2
      rfl

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem storebytes_valid_block_1 : storebytes_valid_block_1Statement := by
  intro m1 b ofs bytes m2 hstore b' hb
  unfold valid_block at hb ⊢
  rw [nextblock_storebytes m1 b ofs bytes m2 hstore]
  exact hb

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps

namespace Mem

theorem loadbytes_storebytes_same : loadbytes_storebytes_sameStatement := by
  intro m1 b ofs bytes m2 hstore
  have hperm : range_perm m2 b ofs (zAdd ofs (zOfNat bytes.length)) Cur Readable := by
    intro ofs0 hof
    apply perm_storebytes_1 m1 b ofs bytes m2 hstore b ofs0 Cur Readable
    have hperm1 : range_perm m1 b ofs (zAdd ofs (zOfNat bytes.length)) Cur Writable :=
      storebytes_range_perm m1 b ofs bytes m2 hstore
    have hperm1r : range_perm m1 b ofs (zAdd ofs (zOfNat bytes.length)) Cur Readable :=
      range_perm_implies m1 b ofs (zAdd ofs (zOfNat bytes.length))
        Cur Writable Readable hperm1 perm_W_R
    exact hperm1r ofs0 hof
  unfold loadbytes
  cases hdec : range_perm_dec m2 b ofs (zAdd ofs (zOfNat bytes.length)) Cur Readable with
  | right hn => exact False.elim (hn hperm)
  | left _ =>
      simp [boolOfSumbool, hdec]
      rw [storebytes_mem_contents m1 b ofs bytes m2 hstore, pmapGetSetSame]
      exact getN_setN_same bytes ofs (PMap.get b m1.mem_contents)

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps

namespace Mem

private theorem loadbytes_storebytes_disjoint_aux : loadbytes_storebytes_disjointStatement := by
  intro m1 b ofs bytes m2 hstore b' ofs' len hlen hcond
  have range_perm_1_to_2 :
      range_perm m1 b' ofs' (zAdd ofs' len) Cur Readable ->
        range_perm m2 b' ofs' (zAdd ofs' len) Cur Readable := by
    intro hrange o ho
    exact perm_storebytes_1 m1 b ofs bytes m2 hstore b' o Cur Readable
      (hrange o ho)
  have range_perm_2_to_1 :
      range_perm m2 b' ofs' (zAdd ofs' len) Cur Readable ->
        range_perm m1 b' ofs' (zAdd ofs' len) Cur Readable := by
    intro hrange o ho
    exact perm_storebytes_2 m1 b ofs bytes m2 hstore b' o Cur Readable
      (hrange o ho)
  unfold loadbytes
  cases hdec1 : range_perm_dec m1 b' ofs' (zAdd ofs' len) Cur Readable with
  | right hn1 =>
      have hn2 : ¬ range_perm m2 b' ofs' (zAdd ofs' len) Cur Readable := by
        intro h2
        exact hn1 (range_perm_2_to_1 h2)
      cases hdec2 : range_perm_dec m2 b' ofs' (zAdd ofs' len) Cur Readable with
      | left h2 => exact False.elim (hn2 h2)
      | right _ => simp [boolOfSumbool, hdec1, hdec2]
  | left h1 =>
      have h2 : range_perm m2 b' ofs' (zAdd ofs' len) Cur Readable :=
        range_perm_1_to_2 h1
      cases hdec2 : range_perm_dec m2 b' ofs' (zAdd ofs' len) Cur Readable with
      | right hn2 => exact False.elim (hn2 h2)
      | left _ =>
          simp only [boolOfSumbool, hdec1, hdec2, ↓reduceIte]
          congr 1
          rw [storebytes_mem_contents m1 b ofs bytes m2 hstore]
          by_cases hb : b' = b
          · subst b'
            rw [pmapGetSetSame]
            have hnat : zOfNat (zToNat len) = len :=
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id len hlen
            apply getN_setN_disjoint bytes ofs (PMap.get b m1.mem_contents)
              (zToNat len) ofs'
            rcases hcond with hneq | hdis
            · exact False.elim (hneq rfl)
            · simpa only [hnat] using hdis
          · rw [pmapGetSetOther _ _ _ _ hb]

theorem loadbytes_storebytes_other : loadbytes_storebytes_otherStatement := by
  intro m1 b ofs bytes m2 hstore b' ofs' len hlen hcond
  apply loadbytes_storebytes_disjoint_aux m1 b ofs bytes m2 hstore b' ofs' len hlen
  rcases hcond with hneq | hleft | hright
  · exact Or.inl hneq
  · exact Or.inr (CompCert4Lean.Lib.Intv.disjoint_range _ _ (Or.inl hleft))
  · exact Or.inr (CompCert4Lean.Lib.Intv.disjoint_range _ _ (Or.inr hright))

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps

namespace Mem

theorem load_storebytes_other : load_storebytes_otherStatement := by
  intro m1 b ofs bytes m2 hstore chunk b' ofs' hcond
  have valid_access_1_to_2 : ∀ {ch b0 o p},
      valid_access m1 ch b0 o p → valid_access m2 ch b0 o p := by
    intro ch b0 o p hv
    unfold valid_access at hv ⊢
    constructor
    · intro o0 ho0
      exact perm_storebytes_1 m1 b ofs bytes m2 hstore b0 o0 Memtype.Cur p
        (hv.1 o0 ho0)
    · exact hv.2
  have valid_access_2_to_1 : ∀ {ch b0 o p},
      valid_access m2 ch b0 o p → valid_access m1 ch b0 o p := by
    intro ch b0 o p hv
    unfold valid_access at hv ⊢
    constructor
    · intro o0 ho0
      exact perm_storebytes_2 m1 b ofs bytes m2 hstore b0 o0 Memtype.Cur p
        (hv.1 o0 ho0)
    · exact hv.2
  unfold load
  cases hdec1 : valid_access_dec m1 chunk b' ofs' Readable with
  | right hn1 =>
      have hn2 : ¬ valid_access m2 chunk b' ofs' Readable := by
        intro h2
        exact hn1 (valid_access_2_to_1 h2)
      cases hdec2 : valid_access_dec m2 chunk b' ofs' Readable with
      | left h2 => exact False.elim (hn2 h2)
      | right _ => simp [boolOfSumbool, hdec1, hdec2]
  | left h1 =>
      have h2 : valid_access m2 chunk b' ofs' Readable :=
        valid_access_1_to_2 h1
      cases hdec2 : valid_access_dec m2 chunk b' ofs' Readable with
      | right hn2 => exact False.elim (hn2 h2)
      | left _ =>
          simp only [boolOfSumbool, hdec1, hdec2, ↓reduceIte]
          congr 1
          rw [storebytes_mem_contents m1 b ofs bytes m2 hstore]
          by_cases hb : b' = b
          · subst b'
            rw [pmapGetSetSame]
            have hget : getN (size_chunk_nat chunk) ofs'
                (setN bytes ofs (PMap.get b m1.mem_contents)) =
                getN (size_chunk_nat chunk) ofs' (PMap.get b m1.mem_contents) := by
              apply getN_setN_outside bytes ofs
              have hsize : zOfNat (size_chunk_nat chunk) = size_chunk chunk := by
                cases chunk <;> rfl
              rcases hcond with hneq | hleft | hright
              · exact False.elim (hneq rfl)
              · left
                simpa [hsize] using hleft
              · right
                exact hright
            rw [hget]
          · rw [pmapGetSetOther _ _ _ _ hb]

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Lib.Maps

namespace Mem

private theorem setN_concat_zadd_zero_memproof (ofs : Z) :
    zAdd ofs (zOfNat 0) = ofs := by
  apply intOfZ_injective
  simp only [intOfZ_zadd_mem, intOfZ_zofnat_mem]
  simp

private theorem setN_concat_zadd_succ_memproof (ofs : Z) (n : Nat) :
    zAdd ofs (zOfNat (Nat.succ n)) =
      zAdd (zAdd ofs z1) (zOfNat n) := by
  symm
  apply zadd_succ_nat_memproof

theorem setN_concat : setN_concatStatement := by
  intro bytes1 bytes2 ofs c
  induction bytes1 generalizing ofs c with
  | nil =>
      simp only [List.nil_append, List.length_nil, setN]
      rw [setN_concat_zadd_zero_memproof]
  | cons b rest ih =>
      simp only [List.cons_append, List.length_cons, setN]
      rw [ih]
      rw [setN_concat_zadd_succ_memproof]

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps

namespace Mem

private theorem storebytes_concat_zadd_len (ofs : Z) (bytes1 bytes2 : List memval) :
    zAdd ofs (zOfNat (bytes1 ++ bytes2).length) =
      zAdd (zAdd ofs (zOfNat bytes1.length)) (zOfNat bytes2.length) := by
  apply intOfZ_injective
  rw [intOfZ_zadd_mem, intOfZ_zofnat_mem,
    intOfZ_zadd_mem, intOfZ_zadd_mem, intOfZ_zofnat_mem,
    intOfZ_zofnat_mem]
  simp only [List.length_append]
  have hnat : Int.ofNat (bytes1.length + bytes2.length) =
      Int.ofNat bytes1.length + Int.ofNat bytes2.length :=
    Int.natCast_add bytes1.length bytes2.length
  rw [hnat]
  omega

theorem storebytes_concat : storebytes_concatStatement := by
  intro m b ofs bytes1 m1 bytes2 m2 h1 h2
  have hlen := storebytes_concat_zadd_len ofs bytes1 bytes2
  unfold storebytes at h1 h2 ⊢
  cases hd1 : range_perm_dec m b ofs (zAdd ofs (zOfNat bytes1.length)) Cur Writable with
  | right hn1 => simp [boolOfSumbool, hd1] at h1
  | left hr1 =>
      cases hd2 : range_perm_dec m1 b (zAdd ofs (zOfNat bytes1.length))
          (zAdd (zAdd ofs (zOfNat bytes1.length)) (zOfNat bytes2.length)) Cur Writable with
      | right hn2 => simp [boolOfSumbool, hd2] at h2
      | left hr2 =>
          have hr : range_perm m b ofs
              (zAdd (zAdd ofs (zOfNat bytes1.length)) (zOfNat bytes2.length)) Cur Writable := by
            intro o ho
            change intOfZ ofs ≤ intOfZ o ∧
              intOfZ o < intOfZ (zAdd (zAdd ofs (zOfNat bytes1.length))
                (zOfNat bytes2.length)) at ho
            by_cases hbefore : intOfZ o < intOfZ (zAdd ofs (zOfNat bytes1.length))
            · apply hr1 o
              constructor
              · exact ho.1
              · exact hbefore
            · apply perm_storebytes_2 m b ofs bytes1 m1 h1 b o Cur Writable
                (hr2 o (by
                  constructor
                  · change intOfZ (zAdd ofs (zOfNat bytes1.length)) ≤ intOfZ o
                    exact Int.le_of_not_gt hbefore
                  · exact ho.2))
          cases hd : range_perm_dec m b ofs
              (zAdd ofs (zOfNat (bytes1 ++ bytes2).length)) Cur Writable with
          | right hn =>
              exfalso
              apply hn
              rw [hlen]
              exact hr
          | left hr' =>
              simp [boolOfSumbool, hd1, hd2, hd, hlen] at h1 h2 ⊢
              subst m1
              subst m2
              simp only [pmapGetSetSame]
              apply mkmem_ext
              · have hmap :
                    PMap.set b (setN bytes2 (zAdd ofs (zOfNat bytes1.length))
                      (setN bytes1 ofs (PMap.get b m.mem_contents)))
                      (PMap.set b (setN bytes1 ofs (PMap.get b m.mem_contents)) m.mem_contents) =
                    PMap.set b (setN bytes2 (zAdd ofs (zOfNat bytes1.length))
                      (setN bytes1 ofs (PMap.get b m.mem_contents))) m.mem_contents :=
                  PMap.set2 (A := ZMap.t memval) b
                    (setN bytes1 ofs (PMap.get b m.mem_contents))
                    (setN bytes2 (zAdd ofs (zOfNat bytes1.length))
                      (setN bytes1 ofs (PMap.get b m.mem_contents))) m.mem_contents
                rw [hmap]
                rw [setN_concat]
              · rfl
              · rfl

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps

namespace Mem

theorem storebytes_split : storebytes_splitStatement := by
  intro m b ofs bytes1 bytes2 m2 hstore
  have hlen := storebytes_concat_zadd_len ofs bytes1 bytes2
  have hwhole : range_perm m b ofs
      (zAdd ofs (zOfNat (bytes1 ++ bytes2).length)) Cur Writable :=
    storebytes_range_perm m b ofs (bytes1 ++ bytes2) m2 hstore
  have hfirst : range_perm m b ofs
      (zAdd ofs (zOfNat bytes1.length)) Cur Writable := by
    intro ofs0 hof
    apply hwhole ofs0
    constructor
    · exact hof.1
    · change intOfZ ofs0 < intOfZ (zAdd ofs (zOfNat (bytes1 ++ bytes2).length))
      rw [hlen]
      change intOfZ ofs0 < intOfZ
        (zAdd (zAdd ofs (zOfNat bytes1.length)) (zOfNat bytes2.length))
      rw [intOfZ_zadd_mem, intOfZ_zofnat_mem,
        intOfZ_zadd_mem, intOfZ_zofnat_mem]
      change intOfZ ofs0 < intOfZ ofs + Int.ofNat bytes1.length + Int.ofNat bytes2.length
      change intOfZ ofs ≤ intOfZ ofs0 ∧
        intOfZ ofs0 < intOfZ (zAdd ofs (zOfNat bytes1.length)) at hof
      rw [intOfZ_zadd_mem, intOfZ_zofnat_mem] at hof
      have hnonneg : 0 ≤ Int.ofNat bytes2.length := Int.ofNat_zero_le _
      omega
  obtain ⟨m1, hstore1⟩ := range_perm_storebytes m b ofs bytes1 hfirst
  have hsecond : range_perm m1 b
      (zAdd ofs (zOfNat bytes1.length))
      (zAdd (zAdd ofs (zOfNat bytes1.length)) (zOfNat bytes2.length)) Cur Writable := by
    intro ofs0 hof
    apply perm_storebytes_1 m b ofs bytes1 m1 hstore1 b ofs0 Cur Writable
    apply hwhole ofs0
    constructor
    · change intOfZ ofs ≤ intOfZ ofs0
      have hoflo := hof.1
      change intOfZ (zAdd ofs (zOfNat bytes1.length)) ≤ intOfZ ofs0 at hoflo
      rw [intOfZ_zadd_mem, intOfZ_zofnat_mem] at hoflo
      have hnonneg : 0 ≤ Int.ofNat bytes1.length := Int.ofNat_zero_le _
      omega
    · change intOfZ ofs0 < intOfZ (zAdd ofs (zOfNat (bytes1 ++ bytes2).length))
      rw [hlen]
      change intOfZ ofs0 < intOfZ
        (zAdd (zAdd ofs (zOfNat bytes1.length)) (zOfNat bytes2.length))
      exact hof.2
  obtain ⟨m2', hstore2⟩ := range_perm_storebytes m1
    b (zAdd ofs (zOfNat bytes1.length)) bytes2 hsecond
  have hconcat := storebytes_concat m b ofs bytes1 m1 bytes2 m2' hstore1 hstore2
  have heq : some m2 = some m2' := hstore.symm.trans hconcat
  have hm : m2 = m2' := Option.some.inj heq
  subst m2'
  exact ⟨m1, hstore1, hstore2⟩

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem store_int64_split : store_int64_splitStatement := by
  intro m b ofs v m' hstore hptr
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

namespace Mem

theorem nextblock_alloc : nextblock_allocStatement := by
  intro m1 lo hi m2 b halloc
  simp [alloc] at halloc
  rcases halloc with ⟨rfl, rfl⟩
  rfl

theorem alloc_result : alloc_resultStatement := by
  intro m1 lo hi m2 b halloc
  simp [alloc] at halloc
  rcases halloc with ⟨rfl, rfl⟩
  rfl

theorem valid_block_alloc : valid_block_allocStatement := by
  intro m1 lo hi m2 b halloc b' hb'
  simp [alloc] at halloc
  rcases halloc with ⟨rfl, rfl⟩
  unfold valid_block at hb' ⊢
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat b' <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m1.nextblock at hb'
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat b' <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (posSucc m1.nextblock)
  have hs := pltSucc m1.nextblock
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m1.nextblock <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (posSucc m1.nextblock) at hs
  exact Nat.lt_trans hb' hs

theorem storev_int64_split : storev_int64_splitStatement := by
  intro m a v m' hstore hptr
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

namespace Mem

theorem fresh_block_alloc : fresh_block_allocStatement := by
  intro m1 lo hi m2 b halloc
  simp [alloc] at halloc
  rcases halloc with ⟨rfl, rfl⟩
  unfold valid_block
  intro hvalid
  exact (Plt_strict _ hvalid)

theorem valid_new_block : valid_new_blockStatement := by
  intro m1 lo hi m2 b halloc
  simp [alloc] at halloc
  rcases halloc with ⟨rfl, rfl⟩
  unfold valid_block
  exact pltSucc m1.nextblock

theorem perm_alloc_1 : perm_alloc_1Statement := by
  intro m1 lo hi m2 b halloc b' ofs k p hperm
  simp [alloc] at halloc
  rcases halloc with ⟨rfl, rfl⟩
  unfold perm at hperm ⊢
  by_cases hblock : b' = m1.nextblock
  · subst b'
    rw [pmapGetSetSame]
    by_cases hrange : inRange lo hi ofs
    · simpa [hrange, perm_order'] using (perm_F_any p)
    · simp [hrange]
      have hnone := m1.nextblock_noaccess m1.nextblock ofs k (Plt_strict _)
      rw [hnone] at hperm
      simp [perm_order'] at hperm
  · rw [pmapGetSetOther _ _ _ _ hblock]
    exact hperm

theorem perm_alloc_2 : perm_alloc_2Statement := by
  intro m1 lo hi m2 b halloc ofs k hbounds
  simp [alloc] at halloc
  rcases halloc with ⟨rfl, rfl⟩
  unfold perm
  rw [pmapGetSetSame]
  have hlo : zLeb lo ofs = true := by
    change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ lo ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs then true else false) = true
    have hle := hbounds.1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ lo ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs at hle
    simp [hle]
  have hhi : zLtb ofs hi = true := by
    change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hi then true else false) = true
    have hlt := hbounds.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hi at hlt
    simp [hlt]
  simpa [inRange, hlo, hhi, perm_order'] using (perm_refl Freeable)

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

namespace Mem

private theorem scc083_pmap_get_set_spec {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) :
    PMap.get i (PMap.set j x m) = if h : i = j then x else PMap.get i m := by
  by_cases h : i = j
  · subst j
    simp [pmapGetSetSame]
  · simp [pmapGetSetOther _ _ _ _ h, h]

theorem perm_alloc_inv : perm_alloc_invStatement := by
  intro m1 lo hi m2 b halloc b' ofs k p hperm
  simp [alloc] at halloc
  rcases halloc with ⟨rfl, rfl⟩
  cases heq : eq_block b' m1.nextblock with
  | left hbeq =>
      subst b'
      unfold perm at hperm
      rw [scc083_pmap_get_set_spec] at hperm
      simp at hperm
      unfold perm_order' at hperm
      split at hperm
      · rename_i hIn
        split at hIn
        · rename_i hRange
          simp only [heq]
          change (ZArith.BinInt.Z.leb lo ofs &&
            ZArith.BinInt.Z.ltb ofs hi) = true at hRange
          simp only [Bool.and_eq_true] at hRange
          constructor
          · change intOfZ lo ≤ intOfZ ofs
            simpa [ZArith.BinInt.Z.leb] using hRange.1
          · change intOfZ ofs < intOfZ hi
            simpa [ZArith.BinInt.Z.ltb] using hRange.2
        · simp at hIn
      · simp at hperm
  | right hbneq =>
      unfold perm at hperm
      rw [scc083_pmap_get_set_spec] at hperm
      have hbneq' : b' ≠ m1.nextblock := by
        intro h
        apply hbneq
        exact h
      simp [heq, hbneq, hbneq'] at hperm ⊢
      exact hperm

theorem perm_alloc_3 : perm_alloc_3Statement := by
  intro m1 lo hi m2 b halloc ofs k p hperm
  have hinv := perm_alloc_inv m1 lo hi m2 b halloc b ofs k p hperm
  cases heq : eq_block b b with
  | left _ => simpa [heq] using hinv
  | right hne => exact False.elim (hne rfl)

theorem perm_alloc_4 : perm_alloc_4Statement := by
  intro m1 lo hi m2 b halloc b' ofs k p hperm hne
  have hinv := perm_alloc_inv m1 lo hi m2 b halloc b' ofs k p hperm
  cases heq : eq_block b' b with
  | left hbeq => exact False.elim (hne hbeq)
  | right _ => simpa [heq] using hinv

theorem valid_access_alloc_inv : valid_access_alloc_invStatement := by
  intro m1 lo hi m2 b halloc chunk b' ofs p hvalid
  simp [alloc] at halloc
  rcases halloc with ⟨rfl, rfl⟩
  cases heq : eq_block b' m1.nextblock with
  | left hbeq =>
      subst b'
      have hsize := CompCert4Lean.Common.Memdata.size_chunk_pos chunk
      have hofs_lt : zLt ofs (zAdd ofs (size_chunk chunk)) := by
        change intOfZ ofs < intOfZ (zAdd ofs (size_chunk chunk))
        unfold zAdd ZArith.BinInt.Z.add
        rw [intOfZ_zOfInt]
        change 0 < intOfZ (size_chunk chunk) at hsize
        omega
      have hperm0 : perm (let m' := alloc m1 lo hi |>.1; m')
          m1.nextblock ofs Cur p := by
        exact hvalid.1 ofs ⟨by change intOfZ ofs ≤ intOfZ ofs; omega, hofs_lt⟩
      have hinv0 := perm_alloc_inv m1 lo hi
        (alloc m1 lo hi).1 m1.nextblock rfl m1.nextblock ofs Cur p hperm0
      have hinv0' : zLe lo ofs ∧ zLt ofs hi := by
        simpa [heq] using hinv0
      let ofs1 : Z := zSub (zAdd ofs (size_chunk chunk)) z1
      have hofs1lo : zLe ofs ofs1 := by
        change intOfZ ofs ≤ intOfZ ofs1
        change intOfZ ofs ≤ intOfZ (zSub (zAdd ofs (size_chunk chunk)) z1)
        unfold zSub ZArith.BinInt.Z.sub
        rw [intOfZ_zOfInt]
        unfold zAdd ZArith.BinInt.Z.add
        rw [intOfZ_zOfInt]
        change 0 < intOfZ (size_chunk chunk) at hsize
        have hz1 : intOfZ z1 = (1 : Int) := by rfl
        rw [hz1]
        have hsize1 : (1 : Int) ≤ intOfZ (size_chunk chunk) := by omega
        omega
      have hofs1hi : zLt ofs1 (zAdd ofs (size_chunk chunk)) := by
        change intOfZ ofs1 < intOfZ (zAdd ofs (size_chunk chunk))
        unfold ofs1 zSub ZArith.BinInt.Z.sub
        rw [intOfZ_zOfInt]
        change intOfZ (zAdd ofs (size_chunk chunk)) - 1 <
          intOfZ (zAdd ofs (size_chunk chunk))
        omega
      have hperm1 : perm (let m' := alloc m1 lo hi |>.1; m')
          m1.nextblock ofs1 Cur p := by
        exact hvalid.1 ofs1 ⟨hofs1lo, hofs1hi⟩
      have hinv1 := perm_alloc_inv m1 lo hi
        (alloc m1 lo hi).1 m1.nextblock rfl m1.nextblock ofs1 Cur p hperm1
      have hinv1' : zLe lo ofs1 ∧ zLt ofs1 hi := by
        simpa [heq] using hinv1
      constructor
      · exact hinv0'.1
      constructor
      · change intOfZ (zAdd ofs (size_chunk chunk)) ≤ intOfZ hi
        unfold zAdd ZArith.BinInt.Z.add
        rw [intOfZ_zOfInt]
        have hupper1 := hinv1'.2
        change intOfZ (zSub (zAdd ofs (size_chunk chunk)) z1) < intOfZ hi at hupper1
        unfold zSub ZArith.BinInt.Z.sub at hupper1
        rw [intOfZ_zOfInt] at hupper1
        have hz1 : intOfZ z1 = (1 : Int) := by rfl
        rw [hz1] at hupper1
        unfold zAdd ZArith.BinInt.Z.add at hupper1
        rw [intOfZ_zOfInt] at hupper1
        omega
      · exact hvalid.2
  | right hbneq =>
      have hresult : valid_access m1 chunk b' ofs p := by
        refine ⟨?_, hvalid.2⟩
        intro ofs' hof'
        have hperm := hvalid.1 ofs' hof'
        have hinv := perm_alloc_inv m1 lo hi
          (alloc m1 lo hi).1 m1.nextblock rfl b' ofs' Cur p hperm
        simpa [heq, hbneq] using hinv
      simpa [heq, hbneq] using hresult

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

namespace Mem

theorem load_alloc_unchanged : load_alloc_unchangedStatement := by
  intro m1 lo hi m2 b halloc chunk b' ofs hbvalid
  have hneq : b' ≠ b := by
    intro heq
    subst b'
    have hb : b = m1.nextblock := alloc_result m1 lo hi m2 b halloc
    subst b
    exact Plt_strict _ hbvalid
  cases h1 : valid_access_dec m1 chunk b' ofs Readable with
  | left hv1 =>
      have hv2 : valid_access m2 chunk b' ofs Readable := by
        refine ⟨?_, hv1.2⟩
        intro ofs' hofs'
        exact perm_alloc_1 m1 lo hi m2 b halloc b' ofs' Cur Readable
          (hv1.1 ofs' hofs')
      cases h2 : valid_access_dec m2 chunk b' ofs Readable with
      | left _ =>
          unfold load
          simp [boolOfSumbool, h1, h2]
          have halloc' := halloc
          simp [alloc] at halloc'
          rcases halloc' with ⟨rfl, rfl⟩
          simp [alloc, pmapGetSetOther _ _ _ _ hneq]
      | right hn2 => exact False.elim (hn2 hv2)
  | right hn1 =>
      cases h2 : valid_access_dec m2 chunk b' ofs Readable with
      | left hv2 =>
          have hinv := valid_access_alloc_inv m1 lo hi m2 b halloc
            chunk b' ofs Readable hv2
          cases heq : eq_block b' b with
          | left hbeq => exact False.elim (hneq hbeq)
          | right _ => exact False.elim (hn1 (by simpa [heq] using hinv))
      | right _ =>
          unfold load
          simp [boolOfSumbool, h1, h2]

theorem load_alloc_other : load_alloc_otherStatement := by
  intro m1 lo hi m2 b halloc chunk b' ofs v hload
  have hvalid : valid_access m1 chunk b' ofs Readable :=
    load_valid_access m1 chunk b' ofs v hload
  have hsize := CompCert4Lean.Common.Memdata.size_chunk_pos chunk
  have hofs : zLt ofs (zAdd ofs (size_chunk chunk)) := by
    change intOfZ ofs < intOfZ (zAdd ofs (size_chunk chunk))
    unfold zAdd ZArith.BinInt.Z.add
    rw [intOfZ_zOfInt]
    change 0 < intOfZ (size_chunk chunk) at hsize
    omega
  have hbvalid : valid_block m1 b' :=
    perm_valid_block m1 b' ofs Cur Readable
      (hvalid.1 ofs ⟨by change intOfZ ofs ≤ intOfZ ofs; omega, hofs⟩)
  rw [load_alloc_unchanged m1 lo hi m2 b halloc chunk b' ofs hbvalid]
  exact hload

theorem load_alloc_same : load_alloc_sameStatement := by
  intro m1 lo hi m2 b halloc chunk ofs v hload
  have hres := load_result chunk m2 b ofs v hload
  have halloc' := halloc
  simp [alloc] at halloc'
  rcases halloc' with ⟨rfl, rfl⟩
  rw [hres]
  obtain ⟨n, hn⟩ := CompCert4Lean.Common.Memdata.size_chunk_nat_pos chunk
  simp only [alloc, pmapGetSetSame]
  rw [hn]
  simp only [getN]
  rw [show ZMap.get ofs (ZMap.init Undef) = Undef by rfl]
  exact CompCert4Lean.Common.Memdata.decode_val_undef _ _

theorem load_alloc_same' : load_alloc_same'Statement := by
  intro m1 lo hi m2 b halloc chunk ofs hlo hhi halign
  have hvalidF : valid_access m2 chunk b ofs Freeable := by
    refine ⟨?_, halign⟩
    intro ofs' hofs'
    have hofslo : zLe lo ofs' := by
      change intOfZ lo ≤ intOfZ ofs'
      change intOfZ lo ≤ intOfZ ofs at hlo
      have hofslo' := hofs'.1
      change intOfZ ofs ≤ intOfZ ofs' at hofslo'
      omega
    have hofshi : zLt ofs' hi := by
      change intOfZ ofs' < intOfZ hi
      have hofshi' := hofs'.2
      change intOfZ ofs' < intOfZ (zAdd ofs (size_chunk chunk)) at hofshi'
      change intOfZ (zAdd ofs (size_chunk chunk)) ≤ intOfZ hi at hhi
      unfold zAdd ZArith.BinInt.Z.add at hofshi'
      rw [intOfZ_zOfInt] at hofshi'
      unfold zAdd ZArith.BinInt.Z.add at hhi
      rw [intOfZ_zOfInt] at hhi
      omega
    exact perm_alloc_2 m1 lo hi m2 b halloc ofs' Cur ⟨hofslo, hofshi⟩
  have hvalidR : valid_access m2 chunk b ofs Readable :=
    valid_access_implies m2 chunk b ofs Freeable Readable hvalidF
      (perm_F_any Readable)
  obtain ⟨v, hload⟩ := valid_access_load m2 chunk b ofs hvalidR
  have hv := load_alloc_same m1 lo hi m2 b halloc chunk ofs v hload
  subst v
  exact hload

end Mem

end CompCert4Lean.Common.Memory

namespace CompCert4Lean.Common.Memory

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

namespace Mem

theorem loadbytes_alloc_unchanged : loadbytes_alloc_unchangedStatement := by
  intro m1 lo hi m2 b halloc b' ofs n hbvalid
  have hneq : b' ≠ b := by
    intro heq
    subst b'
    have hb : b = m1.nextblock := by
      have := alloc_result m1 lo hi m2 b halloc
      exact this
    subst b
    exact Plt_strict _ hbvalid
  have h1to2 : ∀ {o},
      perm m1 b' o Cur Readable → perm m2 b' o Cur Readable := by
    intro o hp
    exact perm_alloc_1 m1 lo hi m2 b halloc b' o Cur Readable hp
  have h2to1 : ∀ {o},
      perm m2 b' o Cur Readable → perm m1 b' o Cur Readable := by
    intro o hp
    exact perm_alloc_4 m1 lo hi m2 b halloc b' o Cur Readable hp hneq
  unfold loadbytes
  cases h1 : range_perm_dec m1 b' ofs (zAdd ofs n) Cur Readable with
  | left hv1 =>
      have hv2 : range_perm m2 b' ofs (zAdd ofs n) Cur Readable := by
        intro o ho
        exact h1to2 (hv1 o ho)
      cases h2 : range_perm_dec m2 b' ofs (zAdd ofs n) Cur Readable with
      | left _ =>
          simp [boolOfSumbool, h1, h2]
          have halloc' := halloc
          simp [alloc] at halloc'
          rcases halloc' with ⟨rfl, rfl⟩
          simp [pmapGetSetOther _ _ _ _ hneq]
      | right hn2 => exact False.elim (hn2 hv2)
  | right hn1 =>
      cases h2 : range_perm_dec m2 b' ofs (zAdd ofs n) Cur Readable with
      | left hv2 =>
          apply False.elim
          apply hn1
          intro o ho
          exact h2to1 (hv2 o ho)
      | right _ => simp [boolOfSumbool, h1, h2]

theorem loadbytes_alloc_same : loadbytes_alloc_sameStatement := by
  intro m1 lo hi m2 b halloc n ofs bytes byte hload hmem
  unfold loadbytes at hload
  cases hdec : range_perm_dec m2 b ofs (zAdd ofs n) Cur Readable with
  | right hn => simp [boolOfSumbool, hdec] at hload
  | left _ =>
      have hbytes : bytes = getN (zToNat n) ofs
          (PMap.get b m2.mem_contents) := by
        simpa [boolOfSumbool, hdec] using hload.symm
      subst bytes
      have halloc' := halloc
      simp [alloc] at halloc'
      rcases halloc' with ⟨rfl, rfl⟩
      have hmem' : byte ∈ getN (zToNat n) ofs (ZMap.init Undef) := by
        simpa [alloc, pmapGetSetSame] using hmem
      have hundef : ∀ (k : Nat) (p : Z),
          byte ∈ getN k p (ZMap.init Undef) → byte = Undef := by
        intro k
        induction k with
        | zero => intro p hm; simp [getN] at hm
        | succ k ih =>
            intro p hm
            simp only [getN, List.mem_cons] at hm
            rw [show ZMap.get p (ZMap.init Undef) = Undef by rfl] at hm
            rcases hm with hhead | htail
            · exact hhead
            · exact ih (zAdd p z1) htail
      exact hundef (zToNat n) ofs hmem'

def range_perm_free : range_perm_freeStatement := by
  intro m1 b lo hi hperm
  refine ⟨unchecked_free m1 b lo hi, ?_⟩
  unfold free
  cases hdec : range_perm_dec m1 b lo hi Cur Freeable with
  | left _ => simp [boolOfSumbool, hdec]
  | right hn => exact False.elim (hn hperm)

theorem free_range_perm : free_range_permStatement := by
  intro m1 bf lo hi m2 hfree
  unfold free at hfree
  cases hdec : range_perm_dec m1 bf lo hi Cur Freeable with
  | left hperm => exact hperm
  | right _ => simp [boolOfSumbool, hdec] at hfree

end Mem

end CompCert4Lean.Common.Memory
