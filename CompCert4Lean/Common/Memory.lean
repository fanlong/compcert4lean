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
  if boolOfSumbool (range_perm_dec m b lo hi Cur Freeable) then
    let oldAccess := PMap.get b m.mem_access
    let newAccess : Z → perm_kind → Option permission :=
      fun ofs k =>
        if inRange lo hi ofs then
          match oldAccess ofs k with
          | none => none
          | some _ => some p
        else
          oldAccess ofs k
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
            · have ham := m.access_max b ofs
              change perm_order'' (oldAccess ofs Max) (oldAccess ofs Cur) at ham
              generalize hmax : oldAccess ofs Max = maxPerm
              generalize hcur : oldAccess ofs Cur = curPerm
              cases maxPerm <;> cases curPerm <;>
                simp_all [perm_order'']
              exact perm_refl p
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
            split
            · rw [oldNone]
            · exact oldNone
          · rw [pmapGetSetOther _ _ _ _ h]
            exact m.nextblock_noaccess b' ofs k hnot
        contents_default := m.contents_default }
  else
    none

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
  mext_inj : mem_inj Val.inject_id m1 m2
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

def range_perm_impliesStatement : Prop :=
  ∀ m b lo hi k p1 p2,
    range_perm m b lo hi k p1 → perm_order p1 p2 → range_perm m b lo hi k p2

def range_perm_maxStatement : Prop :=
  ∀ m b lo hi k p,
    range_perm m b lo hi k p → range_perm m b lo hi Max p

def valid_access_impliesStatement : Prop :=
  ∀ m chunk b ofs p1 p2,
    valid_access m chunk b ofs p1 → perm_order p1 p2 → valid_access m chunk b ofs p2

def valid_access_compatStatement : Prop :=
  ∀ m chunk1 chunk2 b ofs p,
    size_chunk chunk1 = size_chunk chunk2 →
    zLe (align_chunk chunk2) (align_chunk chunk1) →
    valid_access m chunk1 b ofs p →
    valid_access m chunk2 b ofs p

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
      inject f' m1' m2 ∧ Val.inject_incr f f' ∧ f' b1 = none ∧
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
      inject f' m1' m2 ∧ Val.inject_incr f f' ∧ f' b1 = some (b2, delta) ∧
      ∀ b, b ≠ b1 → f' b = f b

def alloc_parallel_injectStatement : Prop :=
  ∀ f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
    inject f m1 m2 →
    alloc m1 lo1 hi1 = (m1', b1) →
    zLe lo2 lo1 → zLe hi1 hi2 →
    ∃ f' m2' b2,
      alloc m2 lo2 hi2 = (m2', b2) ∧
      inject f' m1' m2' ∧ Val.inject_incr f f' ∧ f' b1 = some (b2, z0) ∧
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
