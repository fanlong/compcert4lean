import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory

/-!
# Global environments

Definition-bearing translation of CompCert's `common/Globalenvs.v`.  Proofs
assigned to later proof migration are represented by transparent proposition
descriptors.
-/

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev memval := CompCert4Lean.Common.Memdata.memval
private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zMax := ZArith.BinInt.Z.max
private abbrev zToNat := ZArith.BinInt.Z.to_nat
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zDivide := ZArith.BinInt.Z.divide
private abbrev posSucc := PArith.BinPos.Pos.succ

/- `store_zeros` is module-level in the Rocq source. -/
private theorem intOfZ_z1 : intOfZ z1 = 1 := by
  rfl

private theorem intOfZ_sub_one (n : Z) : intOfZ (zSub n z1) = intOfZ n - 1 := by
  unfold zSub ZArith.BinInt.Z.sub
  rw [intOfZ_zOfInt, intOfZ_z1]

private theorem zToNat_sub_one_lt {n : Z} (h : zLt z0 n) :
    zToNat (zSub n z1) < zToNat n := by
  change Int.toNat (intOfZ (zSub n z1)) < Int.toNat (intOfZ n)
  rw [intOfZ_sub_one]
  change 0 < intOfZ n at h
  have hn : 0 ≤ intOfZ n := by omega
  have hn1 : 0 ≤ intOfZ n - 1 := by omega
  have hnat : (Int.toNat (intOfZ n) : Int) = intOfZ n :=
    Int.toNat_of_nonneg hn
  have hnat1 : (Int.toNat (intOfZ n - 1) : Int) = intOfZ n - 1 :=
    Int.toNat_of_nonneg hn1
  omega

def store_zeros (m : mem) (b : block) (p n : Z) : Option mem :=
  match zle n z0 with
  | .left _ => some m
  | .right h =>
      match Mem.store Mint8unsigned m b p Vzero with
      | none => none
      | some m' => store_zeros m' b (zAdd p z1) (zSub n z1)
termination_by zToNat n
decreasing_by exact zToNat_sub_one_lt h

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

private theorem pltTransSucc {a b : positive} (h : Plt a b) : Plt a (posSucc b) :=
  Nat.lt_trans h (pltSucc b)

private def identMem (id : ident) : List ident → Bool
  | [] => false
  | x :: xs =>
      match peq id x with
      | .left _ => true
      | .right _ => identMem id xs

namespace Senv

structure t : Type where
  find_symbol : ident → Option block
  public_symbol : ident → Bool
  invert_symbol : block → Option ident
  block_is_volatile : block → Bool
  {nextblock : block}
  find_symbol_injective :
    ∀ id1 id2 {b}, find_symbol id1 = some b → find_symbol id2 = some b → id1 = id2
  invert_find_symbol :
    ∀ {id} b, invert_symbol b = some id → find_symbol id = some b
  find_invert_symbol :
    ∀ id {b}, find_symbol id = some b → invert_symbol b = some id
  public_symbol_exists :
    ∀ id, public_symbol id = true → ∃ b, find_symbol id = some b
  find_symbol_below :
    ∀ id {b}, find_symbol id = some b → Plt b nextblock
  block_is_volatile_below :
    ∀ b, block_is_volatile b = true → Plt b nextblock

export t (find_symbol public_symbol invert_symbol block_is_volatile nextblock
  find_symbol_injective invert_find_symbol find_invert_symbol public_symbol_exists
  find_symbol_below block_is_volatile_below)

def symbol_address (ge : t) (id : ident) (ofs : ptrofs) : val :=
  match ge.find_symbol id with
  | some b => Vptr b ofs
  | none => Vundef

def equiv (se1 se2 : t) : Prop :=
  (∀ id, se2.find_symbol id = se1.find_symbol id) ∧
  (∀ id, se2.public_symbol id = se1.public_symbol id) ∧
  (∀ b, se2.block_is_volatile b = se1.block_is_volatile b)

end Senv

namespace Genv

structure t (F V : Type) : Type where
  genv_public : List ident
  genv_symb : PTree.t block
  genv_defs : PTree.t (globdef F V)
  {genv_next : block}
  genv_symb_range : ∀ id {b}, PTree.get id genv_symb = some b → Plt b genv_next
  genv_defs_range : ∀ b {g}, PTree.get b genv_defs = some g → Plt b genv_next
  genv_vars_inj : ∀ id1 id2 {b},
    PTree.get id1 genv_symb = some b → PTree.get id2 genv_symb = some b → id1 = id2

export t (genv_public genv_symb genv_defs genv_next genv_symb_range
  genv_defs_range genv_vars_inj)

def find_symbol {F V : Type} (ge : t F V) (id : ident) : Option block :=
  PTree.get id ge.genv_symb

def symbol_address {F V : Type} (ge : t F V) (id : ident) (ofs : ptrofs) : val :=
  match find_symbol ge id with
  | some b => Vptr b ofs
  | none => Vundef

def public_symbol {F V : Type} (ge : t F V) (id : ident) : Bool :=
  match find_symbol ge id with
  | none => false
  | some _ => identMem id ge.genv_public

def find_def {F V : Type} (ge : t F V) (b : block) : Option (globdef F V) :=
  PTree.get b ge.genv_defs

def find_funct_ptr {F V : Type} (ge : t F V) (b : block) : Option F :=
  match find_def ge b with
  | some (.Gfun f) => some f
  | _ => none

def find_funct {F V : Type} (ge : t F V) (v : val) : Option F :=
  match v with
  | Vptr b ofs => if Ptrofs.eq ofs Ptrofs.zero then find_funct_ptr ge b else none
  | _ => none

def invert_symbol {F V : Type} (ge : t F V) (b : block) : Option ident :=
  PTree.fold
    (fun result id b' =>
      match eq_block b b' with
      | .left _ => some id
      | .right _ => result)
    ge.genv_symb none

def find_var_info {F V : Type} (ge : t F V) (b : block) : Option (globvar V) :=
  match find_def ge b with
  | some (.Gvar v) => some v
  | _ => none

def block_is_volatile {F V : Type} (ge : t F V) (b : block) : Bool :=
  match find_var_info ge b with
  | none => false
  | some gv => gv.gvar_volatile

private theorem invertFindSymbolProof {F V : Type} (ge : t F V) :
    ∀ id b, invert_symbol ge b = some id → find_symbol ge id = some b := by
  intro id b hinvert
  have hfold :
      ∀ id',
        PTree.fold
            (fun result id' b' =>
              match eq_block b b' with
              | .left _ => some id'
              | .right _ => result)
            ge.genv_symb (none : Option ident) = some id' →
          PTree.get id' ge.genv_symb = some b := by
    let P : PTree.t block → Option ident → Prop := fun m result =>
      ∀ id', result = some id' → PTree.get id' m = some b
    have hp :
        P ge.genv_symb
          (PTree.fold
            (fun result id' b' =>
              match eq_block b b' with
              | .left _ => some id'
              | .right _ => result)
            ge.genv_symb (none : Option ident)) := by
      apply PTree_Properties.fold_rec_proof
      · intro m m' result hget hP id' hresult
        rw [← hget id']
        exact hP id' hresult
      · intro id' hresult
        cases hresult
      · intro m result k v hk _ hP id' hresult
        cases heq : eq_block b v with
        | left hbv =>
            have hki : (show ident from k) = id' :=
              Option.some.inj (by simpa [heq] using hresult)
            subst id'
            simpa [hbv] using ptreeGetSetSame k v m
        | right hbv =>
            have hresult' : result = some id' := by simpa [heq] using hresult
            have hgetb := hP id' hresult'
            have hik : id' ≠ k := by
              intro hik
              subst id'
              rw [hk] at hgetb
              cases hgetb
            exact (ptreeGetSetOther id' k v m hik).trans hgetb
    exact hp
  exact hfold id hinvert

private theorem findInvertSymbolProof {F V : Type} (ge : t F V) :
    ∀ id b, find_symbol ge id = some b → invert_symbol ge b = some id := by
  intro id b hfind
  have hfind' : PTree.get id ge.genv_symb = some b := hfind
  have hexists :
      ∃ id',
        PTree.fold
            (fun result id' b' =>
              match eq_block b b' with
              | .left _ => some id'
              | .right _ => result)
            ge.genv_symb (none : Option ident) = some id' := by
    let P : PTree.t block → Option ident → Prop := fun m result =>
      PTree.get id m = some b → ∃ id', result = some id'
    have hp :
        P ge.genv_symb
          (PTree.fold
            (fun result id' b' =>
              match eq_block b b' with
              | .left _ => some id'
              | .right _ => result)
            ge.genv_symb (none : Option ident)) := by
      apply PTree_Properties.fold_rec_proof
      · intro m m' result hget hP htarget
        apply hP
        rw [hget id]
        exact htarget
      · intro htarget
        cases htarget
      · intro m result k v hk _ hP htarget
        cases heq : eq_block b v with
        | left _ => exact ⟨k, by simp⟩
        | right hbv =>
            have hik : id ≠ k := by
              intro hik
              subst k
              have hvb : v = b := Option.some.inj ((ptreeGetSetSame id v m).symm.trans htarget)
              exact hbv hvb.symm
            have htarget' : PTree.get id m = some b :=
              (ptreeGetSetOther id k v m hik).symm.trans htarget
            rcases hP htarget' with ⟨id', hresult⟩
            exact ⟨id', by simpa [heq] using hresult⟩
    exact hp hfind'
  rcases hexists with ⟨id', hinvert⟩
  have hback : find_symbol ge id' = some b :=
    invertFindSymbolProof ge id' b (by simpa [invert_symbol] using hinvert)
  have hid : id = id' := ge.genv_vars_inj id id' hfind hback
  simpa [invert_symbol, hid] using hinvert

private theorem blockIsVolatileBelowProof {F V : Type} (ge : t F V) :
    ∀ b, block_is_volatile ge b = true → Plt b ge.genv_next := by
  intro b hvolatile
  unfold block_is_volatile find_var_info find_def at hvolatile
  cases hdef : PTree.get b ge.genv_defs with
  | none => simp [hdef] at hvolatile
  | some gd =>
      cases gd with
      | Gfun f => simp [hdef] at hvolatile
      | Gvar gv => exact ge.genv_defs_range b hdef

def add_global {F V : Type} (ge : t F V) (idg : ident × globdef F V) : t F V :=
  let id := idg.1
  let gd := idg.2
  let next := ge.genv_next
  { genv_public := ge.genv_public
    genv_symb := PTree.set id next ge.genv_symb
    genv_defs := PTree.set next gd ge.genv_defs
    genv_next := posSucc next
    genv_symb_range := by
      intro id' b h
      by_cases heq : id' = id
      · subst id'
        have hs := ptreeGetSetSame (show positive from id) next ge.genv_symb
        have hb : some next = some b := hs.symm.trans h
        cases Option.some.inj hb
        exact pltSucc next
      · have ho := ptreeGetSetOther (show positive from id') (show positive from id)
            next ge.genv_symb heq
        have hold : PTree.get id' ge.genv_symb = some b := ho.symm.trans h
        exact pltTransSucc (ge.genv_symb_range id' hold)
    genv_defs_range := by
      intro b gd' h
      by_cases heq : b = next
      · subst b
        have hs := ptreeGetSetSame (show positive from next) gd ge.genv_defs
        have hgd : some gd = some gd' := hs.symm.trans h
        cases Option.some.inj hgd
        exact pltSucc next
      · have ho := ptreeGetSetOther (show positive from b) (show positive from next)
            gd ge.genv_defs heq
        have hold : PTree.get b ge.genv_defs = some gd' := ho.symm.trans h
        exact pltTransSucc (ge.genv_defs_range b hold)
    genv_vars_inj := by
      intro id1 id2 b h1 h2
      by_cases h1id : id1 = id
      · subst id1
        have hs := ptreeGetSetSame (show positive from id) next ge.genv_symb
        have hb : some next = some b := hs.symm.trans h1
        cases Option.some.inj hb
        by_cases h2id : id2 = id
        · exact h2id.symm
        · have ho := ptreeGetSetOther (show positive from id2) (show positive from id)
              next ge.genv_symb h2id
          have hold : PTree.get id2 ge.genv_symb = some next := ho.symm.trans h2
          have hrange := ge.genv_symb_range id2 hold
          exact False.elim (Nat.lt_irrefl _ hrange)
      · have ho1 := ptreeGetSetOther (show positive from id1) (show positive from id)
            next ge.genv_symb h1id
        have hold1 : PTree.get id1 ge.genv_symb = some b := ho1.symm.trans h1
        by_cases h2id : id2 = id
        · subst id2
          have hs := ptreeGetSetSame (show positive from id) next ge.genv_symb
          have hb : some next = some b := hs.symm.trans h2
          cases Option.some.inj hb
          have hrange := ge.genv_symb_range id1 hold1
          exact False.elim (Nat.lt_irrefl _ hrange)
        · have ho2 := ptreeGetSetOther (show positive from id2) (show positive from id)
              next ge.genv_symb h2id
          have hold2 : PTree.get id2 ge.genv_symb = some b := ho2.symm.trans h2
          exact ge.genv_vars_inj id1 id2 hold1 hold2 }

def add_globals {F V : Type} (ge : t F V)
    (gl : List (ident × globdef F V)) : t F V :=
  gl.foldl add_global ge

def empty_genv (F V : Type) (pub : List ident) : t F V :=
  { genv_public := pub
    genv_symb := PTree.empty block
    genv_defs := PTree.empty (globdef F V)
    genv_next := .xH
    genv_symb_range := by
      intro id b h
      simp [PTree.get, PTree.empty] at h
    genv_defs_range := by
      intro b gd h
      simp [PTree.get, PTree.empty] at h
    genv_vars_inj := by
      intro id1 id2 b h
      simp [PTree.get, PTree.empty] at h }

def globalenv {F V : Type} (p : program F V) : t F V :=
  add_globals (empty_genv F V p.prog_public) p.prog_defs

def advance_next {F V : Type} (gl : List (ident × globdef F V)) (x : positive) : positive :=
  gl.foldl (fun n _ => posSucc n) x

def to_senv {F V : Type} (ge : t F V) : Senv.t :=
  { find_symbol := find_symbol ge
    public_symbol := public_symbol ge
    invert_symbol := invert_symbol ge
    block_is_volatile := block_is_volatile ge
    nextblock := ge.genv_next
    find_symbol_injective := ge.genv_vars_inj
    invert_find_symbol := fun {id} b h => invertFindSymbolProof ge id b h
    find_invert_symbol := fun id {b} h => findInvertSymbolProof ge id b h
    public_symbol_exists := by
      intro id h
      unfold public_symbol at h
      cases hfs : find_symbol ge id with
      | none => simp [hfs] at h
      | some b => exact ⟨b, rfl⟩
    find_symbol_below := by
      intro id b h
      exact ge.genv_symb_range id h
    block_is_volatile_below := blockIsVolatileBelowProof ge }

def store_init_data {F V : Type} (ge : t F V) (m : mem) (b : block)
    (p : Z) (id : init_data) : Option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof symb ofs =>
      match find_symbol ge symb with
      | none => none
      | some b' => Mem.store Mptr m b p (Vptr b' ofs)
  | Init_space _ => some m

def store_init_data_list {F V : Type} (ge : t F V) :
    mem → block → Z → List init_data → Option mem
  | m, _, _, [] => some m
  | m, b, p, id :: rest =>
      match store_init_data ge m b p id with
      | none => none
      | some m' => store_init_data_list ge m' b (zAdd p (init_data_size id)) rest

def perm_globvar {V : Type} (gv : globvar V) : permission :=
  if gv.gvar_volatile then Nonempty
  else if gv.gvar_readonly then Readable
  else Writable

def alloc_global {F V : Type} (ge : t F V) (m : mem)
    (idg : ident × globdef F V) : Option mem :=
  match idg.2 with
  | .Gfun _ =>
      let (m1, b) := Mem.alloc m z0 z1
      Mem.drop_perm m1 b z0 z1 Nonempty
  | .Gvar v =>
      let init := v.gvar_init
      let sz := init_data_list_size init
      let (m1, b) := Mem.alloc m z0 sz
      match store_zeros m1 b z0 sz with
      | none => none
      | some m2 =>
          match store_init_data_list ge m2 b z0 init with
          | none => none
          | some m3 => Mem.drop_perm m3 b z0 sz (perm_globvar v)

def alloc_globals {F V : Type} (ge : t F V) :
    mem → List (ident × globdef F V) → Option mem
  | m, [] => some m
  | m, g :: rest =>
      match alloc_global ge m g with
      | none => none
      | some m' => alloc_globals ge m' rest

def readbytes_as_zero (m : mem) (b : block) (ofs len : Z) : Prop :=
  ∀ p n,
    zLe ofs p → zLe (zAdd p (zOfNat n)) (zAdd ofs len) →
    Mem.loadbytes m b p (zOfNat n) =
      some (List.replicate n (Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)))

def bytes_of_init_data {F V : Type} (ge : t F V) (i : init_data) : List memval :=
  match i with
  | Init_int8 n => inj_bytes (encode_int 1 (Int.unsigned n))
  | Init_int16 n => inj_bytes (encode_int 2 (Int.unsigned n))
  | Init_int32 n => inj_bytes (encode_int 4 (Int.unsigned n))
  | Init_int64 n => inj_bytes (encode_int 8 (Int64.unsigned n))
  | Init_float32 n => inj_bytes (encode_int 4
      (Int.unsigned (CompCert4Lean.Lib.Floats.Float32.to_bits n)))
  | Init_float64 n => inj_bytes (encode_int 8
      (Int64.unsigned (CompCert4Lean.Lib.Floats.Float.to_bits n)))
  | Init_space n =>
      List.replicate (zToNat n) (Byte (CompCert4Lean.Lib.Integers.Byte.repr z0))
  | Init_addrof id ofs =>
      match find_symbol ge id with
      | some b => inj_value (if CompCert4Lean.X86_64.Archi.ptr64 then Q64 else Q32) (Vptr b ofs)
      | none => List.replicate (if CompCert4Lean.X86_64.Archi.ptr64 then 8 else 4) Undef

def bytes_of_init_data_list {F V : Type} (ge : t F V) :
    List init_data → List memval
  | [] => []
  | i :: rest => bytes_of_init_data ge i ++ bytes_of_init_data_list ge rest

def read_as_zero (m : mem) (b : block) (ofs len : Z) : Prop :=
  ∀ chunk p,
    zLe ofs p → zLe (zAdd p (size_chunk chunk)) (zAdd ofs len) →
    zDivide (align_chunk chunk) p →
    Mem.load chunk m b p = some
      (match chunk with
      | Mbool | Mint8unsigned | Mint8signed | Mint16unsigned | Mint16signed | Mint32 =>
          Vint Int.zero
      | Mint64 => Vlong Int64.zero
      | Mfloat32 => Vsingle CompCert4Lean.Lib.Floats.Float32.zero
      | Mfloat64 => Vfloat CompCert4Lean.Lib.Floats.Float.zero
      | Many32 | Many64 => Vundef)

def load_store_init_data {F V : Type} (ge : t F V) (m : mem) (b : block) :
    Z → List init_data → Prop
  | _, [] => True
  | p, Init_int8 n :: rest =>
      Mem.load Mint8unsigned m b p = some (Val.zero_ext (zOfNat 8) (Vint n)) ∧
        load_store_init_data ge m b (zAdd p (zOfNat 1)) rest
  | p, Init_int16 n :: rest =>
      Mem.load Mint16unsigned m b p = some (Val.zero_ext (zOfNat 16) (Vint n)) ∧
        load_store_init_data ge m b (zAdd p (zOfNat 2)) rest
  | p, Init_int32 n :: rest =>
      Mem.load Mint32 m b p = some (Vint n) ∧
        load_store_init_data ge m b (zAdd p (zOfNat 4)) rest
  | p, Init_int64 n :: rest =>
      Mem.load Mint64 m b p = some (Vlong n) ∧
        load_store_init_data ge m b (zAdd p (zOfNat 8)) rest
  | p, Init_float32 n :: rest =>
      Mem.load Mfloat32 m b p = some (Vsingle n) ∧
        load_store_init_data ge m b (zAdd p (zOfNat 4)) rest
  | p, Init_float64 n :: rest =>
      Mem.load Mfloat64 m b p = some (Vfloat n) ∧
        load_store_init_data ge m b (zAdd p (zOfNat 8)) rest
  | p, Init_addrof symb ofs :: rest =>
      (∃ b', find_symbol ge symb = some b' ∧ Mem.load Mptr m b p = some (Vptr b' ofs)) ∧
        load_store_init_data ge m b (zAdd p (size_chunk Mptr)) rest
  | p, Init_space n :: rest =>
      read_as_zero m b p n ∧
        load_store_init_data ge m b (zAdd p (zMax n z0)) rest

def globals_initialized {F V : Type} (ge g : t F V) (m : mem) : Prop :=
  ∀ b gd,
    find_def g b = some gd →
    match gd with
    | .Gfun _ =>
        Mem.perm m b z0 Cur Memtype.Nonempty ∧
          (∀ ofs k p, Mem.perm m b ofs k p → ofs = z0 ∧ p = Memtype.Nonempty)
    | .Gvar v =>
        Mem.range_perm m b z0 (init_data_list_size v.gvar_init) Cur (perm_globvar v) ∧
        (∀ ofs k p, Mem.perm m b ofs k p →
          (zLe z0 ofs ∧ zLt ofs (init_data_list_size v.gvar_init)) ∧
            perm_order (perm_globvar v) p) ∧
        (v.gvar_volatile = false → load_store_init_data ge m b z0 v.gvar_init) ∧
        (v.gvar_volatile = false →
          Mem.loadbytes m b z0 (init_data_list_size v.gvar_init) =
            some (bytes_of_init_data_list ge v.gvar_init))

def init_mem {F V : Type} (p : program F V) : Option mem :=
  alloc_globals (globalenv p) Mem.empty p.prog_defs

def init_data_alignment : init_data → Z
  | Init_int8 _ => zOfNat 1
  | Init_int16 _ => zOfNat 2
  | Init_int32 _ => zOfNat 4
  | Init_int64 _ => zOfNat 8
  | Init_float32 _ => zOfNat 4
  | Init_float64 _ => zOfNat 4
  | Init_addrof _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then zOfNat 8 else zOfNat 4
  | Init_space _ => zOfNat 1

def init_data_list_aligned : Z → List init_data → Prop
  | _, [] => True
  | p, i :: rest =>
      zDivide (init_data_alignment i) p ∧
        init_data_list_aligned (zAdd p (init_data_size i)) rest

structure match_genvs {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (ge1 : t A V) (ge2 : t B W) : Prop where
  Build_match_genvs (ge1 ge2) ::
  mge_next : ge2.genv_next = ge1.genv_next
  mge_symb : ∀ id, PTree.get id ge2.genv_symb = PTree.get id ge1.genv_symb
  mge_defs : ∀ b, option_rel R (PTree.get b ge1.genv_defs) (PTree.get b ge2.genv_defs)

export match_genvs (Build_match_genvs mge_next mge_symb mge_defs)

/-! ## Exact statement descriptors for later proof migration -/

def add_globals_preservesStatement : Prop :=
  ∀ (F V : Type) (P : t F V → Prop) (gl : List (ident × globdef F V)) (ge : t F V),
    (∀ ge id g, P ge → (id, g) ∈ gl → P (add_global ge (id, g))) →
    P ge → P (add_globals ge gl)

def add_globals_ensuresStatement : Prop :=
  ∀ (F V : Type) (P : t F V → Prop) (id : ident) (g : globdef F V)
    (gl : List (ident × globdef F V)) (ge : t F V),
    (∀ ge id g, P ge → (id, g) ∈ gl → P (add_global ge (id, g))) →
    (∀ ge, P (add_global ge (id, g))) →
    (id, g) ∈ gl → P (add_globals ge gl)

def public_symbol_existsStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (id : ident),
    public_symbol ge id = true → ∃ b, find_symbol ge id = some b

def shift_symbol_address_32Statement : Prop :=
  ∀ (F V : Type) (ge : t F V) (id : ident) (ofs : ptrofs) (n : int),
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int n)) =
      Val.add (symbol_address ge id ofs) (Vint n)

def shift_symbol_address_64Statement : Prop :=
  ∀ (F V : Type) (ge : t F V) (id : ident) (ofs : ptrofs) (n : int64),
    CompCert4Lean.X86_64.Archi.ptr64 = true →
    symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int64 n)) =
      Val.addl (symbol_address ge id ofs) (Vlong n)

def find_funct_invStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (v : val) (f : F),
    find_funct ge v = some f → ∃ b, v = Vptr b Ptrofs.zero

def find_funct_find_funct_ptrStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (b : block),
    find_funct ge (Vptr b Ptrofs.zero) = find_funct_ptr ge b

def find_funct_ptr_iffStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (b : block) (f : F),
    find_funct_ptr ge b = some f ↔ find_def ge b = some (Gfun f)

def find_var_info_iffStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (b : block) (v : globvar V),
    find_var_info ge b = some v ↔ find_def ge b = some (Gvar v)

def find_def_symbolStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (id : ident) (g : globdef F V),
    PTree.get id (prog_defmap p) = some g ↔
      ∃ b, find_symbol (globalenv p) id = some b ∧ find_def (globalenv p) b = some g

def find_symbol_existsStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (id : ident) (g : globdef F V),
    (id, g) ∈ p.prog_defs → ∃ b, find_symbol (globalenv p) id = some b

def find_symbol_inversionStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (x : ident) (b : block),
    find_symbol (globalenv p) x = some b → x ∈ prog_defs_names p

def find_def_inversionStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (b : block) (g : globdef F V),
    find_def (globalenv p) b = some g → ∃ id, (id, g) ∈ p.prog_defs

def find_funct_ptr_inversionStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (b : block) (f : F),
    find_funct_ptr (globalenv p) b = some f → ∃ id, (id, Gfun f) ∈ p.prog_defs

def find_funct_inversionStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (v : val) (f : F),
    find_funct (globalenv p) v = some f → ∃ id, (id, Gfun f) ∈ p.prog_defs

def find_funct_ptr_propStatement : Prop :=
  ∀ (F V : Type) (P : F → Prop) (p : program F V) (b : block) (f : F),
    (∀ id f, (id, Gfun f) ∈ p.prog_defs → P f) →
    find_funct_ptr (globalenv p) b = some f → P f

def find_funct_propStatement : Prop :=
  ∀ (F V : Type) (P : F → Prop) (p : program F V) (v : val) (f : F),
    (∀ id f, (id, Gfun f) ∈ p.prog_defs → P f) →
    find_funct (globalenv p) v = some f → P f

def global_addresses_distinctStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (id1 id2 : ident) (b1 b2 : block),
    id1 ≠ id2 → find_symbol ge id1 = some b1 → find_symbol ge id2 = some b2 → b1 ≠ b2

def invert_find_symbolStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (id : ident) (b : block),
    invert_symbol ge b = some id → find_symbol ge id = some b

def find_invert_symbolStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (id : ident) (b : block),
    find_symbol ge id = some b → invert_symbol ge b = some id

def genv_next_add_globalsStatement : Prop :=
  ∀ (F V : Type) (gl : List (ident × globdef F V)) (ge : t F V),
    (add_globals ge gl).genv_next = advance_next gl ge.genv_next

def genv_public_add_globalsStatement : Prop :=
  ∀ (F V : Type) (gl : List (ident × globdef F V)) (ge : t F V),
    (add_globals ge gl).genv_public = ge.genv_public

def globalenv_publicStatement : Prop :=
  ∀ (F V : Type) (p : program F V), (globalenv p).genv_public = p.prog_public

def block_is_volatile_belowStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (b : block),
    block_is_volatile ge b = true → Plt b ge.genv_next

def store_zeros_nextblockStatement : Prop :=
  ∀ (m : mem) (b : block) (p n : Z) (m' : mem),
    store_zeros m b p n = some m' → m'.nextblock = m.nextblock

def store_init_data_list_nextblockStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (idl : List init_data) (b : block)
    (m : mem) (p : Z) (m' : mem),
    store_init_data_list ge m b p idl = some m' → m'.nextblock = m.nextblock

def alloc_global_nextblockStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (g : ident × globdef F V) (m m' : mem),
    alloc_global ge m g = some m' → m'.nextblock = posSucc m.nextblock

def alloc_globals_nextblockStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (gl : List (ident × globdef F V)) (m m' : mem),
    alloc_globals ge m gl = some m' → m'.nextblock = advance_next gl m.nextblock

def store_zeros_permStatement : Prop :=
  ∀ (k : perm_kind) (prm : permission) (b' : block) (q : Z)
    (m : mem) (b : block) (p n : Z) (m' : mem),
    store_zeros m b p n = some m' →
      (Mem.perm m b' q k prm ↔ Mem.perm m' b' q k prm)

def store_init_data_permStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (k : perm_kind) (prm : permission)
    (b' : block) (q : Z) (i : init_data) (b : block) (m : mem) (p : Z) (m' : mem),
    store_init_data ge m b p i = some m' →
      (Mem.perm m b' q k prm ↔ Mem.perm m' b' q k prm)

def store_init_data_list_permStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (k : perm_kind) (prm : permission)
    (b' : block) (q : Z) (idl : List init_data) (b : block)
    (m : mem) (p : Z) (m' : mem),
    store_init_data_list ge m b p idl = some m' →
      (Mem.perm m b' q k prm ↔ Mem.perm m' b' q k prm)

def store_zeros_unchangedStatement : Prop :=
  ∀ (P : block → Z → Prop) (m : mem) (b : block) (p n : Z) (m' : mem),
    store_zeros m b p n = some m' →
    (∀ i, zLe p i ∧ zLt i (zAdd p n) → ¬ P b i) →
    Mem.unchanged_on P m m'

def store_init_data_unchangedStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (P : block → Z → Prop) (b : block)
    (i : init_data) (m : mem) (p : Z) (m' : mem),
    store_init_data ge m b p i = some m' →
    (∀ ofs, zLe p ofs ∧ zLt ofs (zAdd p (init_data_size i)) → ¬ P b ofs) →
    Mem.unchanged_on P m m'

def store_init_data_list_unchangedStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (P : block → Z → Prop) (b : block)
    (il : List init_data) (m : mem) (p : Z) (m' : mem),
    store_init_data_list ge m b p il = some m' →
    (∀ ofs, zLe p ofs → ¬ P b ofs) →
    Mem.unchanged_on P m m'

def store_zeros_loadbytesStatement : Prop :=
  ∀ (m : mem) (b : block) (p n : Z) (m' : mem),
    store_zeros m b p n = some m' → readbytes_as_zero m' b p n

def init_data_size_addrofStatement : Prop :=
  ∀ (id : ident) (ofs : ptrofs), init_data_size (Init_addrof id ofs) = size_chunk Mptr

def store_init_data_loadbytesStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (m : mem) (b : block) (p : Z)
    (i : init_data) (m' : mem),
    store_init_data ge m b p i = some m' →
    readbytes_as_zero m b p (init_data_size i) →
    Mem.loadbytes m' b p (init_data_size i) = some (bytes_of_init_data ge i)

def store_init_data_list_loadbytesStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (b : block) (il : List init_data)
    (m : mem) (p : Z) (m' : mem),
    store_init_data_list ge m b p il = some m' →
    readbytes_as_zero m b p (init_data_list_size il) →
    Mem.loadbytes m' b p (init_data_list_size il) = some (bytes_of_init_data_list ge il)

def read_as_zero_unchangedStatement : Prop :=
  ∀ (P : block → Z → Prop) (m : mem) (b : block) (ofs len : Z) (m' : mem),
    read_as_zero m b ofs len →
    Mem.unchanged_on P m m' →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs len) → P b i) →
    read_as_zero m' b ofs len

def store_zeros_read_as_zeroStatement : Prop :=
  ∀ (m : mem) (b : block) (p n : Z) (m' : mem),
    store_zeros m b p n = some m' → read_as_zero m' b p n

def store_init_data_list_charactStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (b : block) (il : List init_data)
    (m : mem) (p : Z) (m' : mem),
    store_init_data_list ge m b p il = some m' →
    read_as_zero m b p (init_data_list_size il) →
    load_store_init_data ge m' b p il

def alloc_global_unchangedStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (P : block → Z → Prop) (m : mem)
    (id : ident) (g : globdef F V) (m' : mem),
    alloc_global ge m (id, g) = some m' → Mem.unchanged_on P m m'

def load_store_init_data_invariantStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (m m' : mem) (b : block),
    (∀ chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) →
    ∀ il p, load_store_init_data ge m b p il → load_store_init_data ge m' b p il

def alloc_global_initializedStatement : Prop :=
  ∀ (F V : Type) (ge g : t F V) (m : mem) (id : ident)
    (gd : globdef F V) (m' : mem),
    g.genv_next = m.nextblock →
    alloc_global ge m (id, gd) = some m' →
    globals_initialized ge g m →
      globals_initialized ge (add_global g (id, gd)) m' ∧
        (add_global g (id, gd)).genv_next = m'.nextblock

def alloc_globals_initializedStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (gl : List (ident × globdef F V))
    (g : t F V) (m m' : mem),
    alloc_globals ge m gl = some m' →
    g.genv_next = m.nextblock →
    globals_initialized ge g m →
    globals_initialized ge (add_globals g gl) m'

def init_mem_genv_nextStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (m : mem),
    init_mem p = some m → (globalenv p).genv_next = m.nextblock

def find_symbol_not_freshStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (id : ident) (b : block) (m : mem),
    init_mem p = some m → find_symbol (globalenv p) id = some b → Mem.valid_block m b

def find_def_not_freshStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (b : block) (g : globdef F V) (m : mem),
    init_mem p = some m → find_def (globalenv p) b = some g → Mem.valid_block m b

def find_funct_ptr_not_freshStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (b : block) (f : F) (m : mem),
    init_mem p = some m → find_funct_ptr (globalenv p) b = some f → Mem.valid_block m b

def find_var_info_not_freshStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (b : block) (gv : globvar V) (m : mem),
    init_mem p = some m → find_var_info (globalenv p) b = some gv → Mem.valid_block m b

def init_mem_characterization_genStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (m : mem),
    init_mem p = some m → globals_initialized (globalenv p) (globalenv p) m

def init_mem_characterizationStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (b : block) (gv : globvar V) (m : mem),
    find_var_info (globalenv p) b = some gv →
    init_mem p = some m →
    Mem.range_perm m b z0 (init_data_list_size gv.gvar_init) Cur (perm_globvar gv) ∧
    (∀ ofs k prm, Mem.perm m b ofs k prm →
      (zLe z0 ofs ∧ zLt ofs (init_data_list_size gv.gvar_init)) ∧
        perm_order (perm_globvar gv) prm) ∧
    (gv.gvar_volatile = false →
      load_store_init_data (globalenv p) m b z0 gv.gvar_init) ∧
    (gv.gvar_volatile = false →
      Mem.loadbytes m b z0 (init_data_list_size gv.gvar_init) =
        some (bytes_of_init_data_list (globalenv p) gv.gvar_init))

def store_zeros_neutralStatement : Prop :=
  ∀ (thr : block) (m : mem) (b : block) (p n : Z) (m' : mem),
    Mem.inject_neutral thr m → Plt b thr →
    store_zeros m b p n = some m' → Mem.inject_neutral thr m'

def store_init_data_neutralStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (thr : block),
    (∀ id b, find_symbol ge id = some b → Plt b thr) →
    ∀ (m : mem) (b : block) (p : Z) (id : init_data) (m' : mem),
    Mem.inject_neutral thr m → Plt b thr →
    store_init_data ge m b p id = some m' → Mem.inject_neutral thr m'

def store_init_data_list_neutralStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (thr : block),
    (∀ id b, find_symbol ge id = some b → Plt b thr) →
    ∀ (b : block) (idl : List init_data) (m : mem) (p : Z) (m' : mem),
    Mem.inject_neutral thr m → Plt b thr →
    store_init_data_list ge m b p idl = some m' → Mem.inject_neutral thr m'

def alloc_global_neutralStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (thr : block),
    (∀ id b, find_symbol ge id = some b → Plt b thr) →
    ∀ (idg : ident × globdef F V) (m m' : mem),
    alloc_global ge m idg = some m' →
    Mem.inject_neutral thr m → Plt m.nextblock thr → Mem.inject_neutral thr m'

def advance_next_leStatement : Prop :=
  ∀ (F V : Type) (gl : List (ident × globdef F V)) (x : positive),
    Ple x (advance_next gl x)

def alloc_globals_neutralStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (thr : block),
    (∀ id b, find_symbol ge id = some b → Plt b thr) →
    ∀ (gl : List (ident × globdef F V)) (m m' : mem),
    alloc_globals ge m gl = some m' →
    Mem.inject_neutral thr m → Ple m'.nextblock thr → Mem.inject_neutral thr m'

def initmem_injectStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (m : mem),
    init_mem p = some m → Mem.inject (Mem.flat_inj m.nextblock) m m

def store_init_data_alignedStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (m : mem) (b : block) (p : Z)
    (i : init_data) (m' : mem),
    store_init_data ge m b p i = some m' → zDivide (init_data_alignment i) p

def store_init_data_list_alignedStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (b : block) (il : List init_data)
    (m : mem) (p : Z) (m' : mem),
    store_init_data_list ge m b p il = some m' → init_data_list_aligned p il

def store_init_data_list_free_identsStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (b : block) (i : ident) (o : ptrofs)
    (il : List init_data) (m : mem) (p : Z) (m' : mem),
    store_init_data_list ge m b p il = some m' →
    Init_addrof i o ∈ il → ∃ b', find_symbol ge i = some b'

def init_mem_inversionStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (m : mem) (id : ident) (v : globvar V),
    init_mem p = some m → (id, Gvar v) ∈ p.prog_defs →
    init_data_list_aligned z0 v.gvar_init ∧
      ∀ i o, Init_addrof i o ∈ v.gvar_init → ∃ b, find_symbol (globalenv p) i = some b

def store_zeros_existsStatement : Prop :=
  ∀ (m : mem) (b : block) (p n : Z),
    Mem.range_perm m b p (zAdd p n) Cur Writable →
      ∃ m', store_zeros m b p n = some m'

def store_init_data_existsStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (m : mem) (b : block) (p : Z) (i : init_data),
    Mem.range_perm m b p (zAdd p (init_data_size i)) Cur Writable →
    zDivide (init_data_alignment i) p →
    (∀ id ofs, i = Init_addrof id ofs → ∃ b, find_symbol ge id = some b) →
      ∃ m', store_init_data ge m b p i = some m'

def store_init_data_list_existsStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (b : block) (il : List init_data)
    (m : mem) (p : Z),
    Mem.range_perm m b p (zAdd p (init_data_list_size il)) Cur Writable →
    init_data_list_aligned p il →
    (∀ id ofs, Init_addrof id ofs ∈ il → ∃ b, find_symbol ge id = some b) →
      ∃ m', store_init_data_list ge m b p il = some m'

def alloc_global_existsStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (m : mem) (idg : ident × globdef F V),
    (match idg.2 with
    | .Gfun _ => True
    | .Gvar v =>
        init_data_list_aligned z0 v.gvar_init ∧
          ∀ i o, Init_addrof i o ∈ v.gvar_init → ∃ b, find_symbol ge i = some b) →
      ∃ m', alloc_global ge m idg = some m'

def init_mem_existsStatement : Prop :=
  ∀ (F V : Type) (p : program F V),
    (∀ id v, (id, Gvar v) ∈ p.prog_defs →
      init_data_list_aligned z0 v.gvar_init ∧
        ∀ i o, Init_addrof i o ∈ v.gvar_init →
          ∃ b, find_symbol (globalenv p) i = some b) →
      ∃ m, init_mem p = some m

def add_global_matchStatement : Prop :=
  ∀ (A B V W : Type) (R : globdef A V → globdef B W → Prop)
    (ge1 : t A V) (ge2 : t B W) (id : ident)
    (g1 : globdef A V) (g2 : globdef B W),
    match_genvs R ge1 ge2 → R g1 g2 →
      match_genvs R (add_global ge1 (id, g1)) (add_global ge2 (id, g2))

def add_globals_matchStatement : Prop :=
  ∀ (A B V W : Type) (R : globdef A V → globdef B W → Prop)
    (gl1 : List (ident × globdef A V)) (gl2 : List (ident × globdef B W)),
    list_forall2 (fun idg1 idg2 => idg1.1 = idg2.1 ∧ R idg1.2 idg2.2) gl1 gl2 →
    ∀ ge1 ge2, match_genvs R ge1 ge2 →
      match_genvs R (add_globals ge1 gl1) (add_globals ge2 gl2)

def globalenvs_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
      match_genvs (match_globdef match_fundef match_varinfo ctx) (globalenv p) (globalenv tp)

def find_def_match_2Statement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ b, option_rel (match_globdef match_fundef match_varinfo ctx)
      (find_def (globalenv p) b) (find_def (globalenv tp) b)

def find_def_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ b g, find_def (globalenv p) b = some g →
      ∃ tg, find_def (globalenv tp) b = some tg ∧
        match_globdef match_fundef match_varinfo ctx g tg

def find_funct_ptr_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ b f, find_funct_ptr (globalenv p) b = some f →
      ∃ cunit tf, find_funct_ptr (globalenv tp) b = some tf ∧
        match_fundef cunit f tf ∧ linkorder cunit ctx

def find_funct_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ v f, find_funct (globalenv p) v = some f →
      ∃ cunit tf, find_funct (globalenv tp) v = some tf ∧
        match_fundef cunit f tf ∧ linkorder cunit ctx

def find_symbol_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ s : ident, find_symbol (globalenv tp) s = find_symbol (globalenv p) s

def senv_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
      Senv.equiv (to_senv (globalenv p)) (to_senv (globalenv tp))

def store_init_data_list_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ idl m b ofs m',
      store_init_data_list (globalenv p) m b ofs idl = some m' →
      store_init_data_list (globalenv tp) m b ofs idl = some m'

def alloc_globals_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ gl1 gl2,
      list_forall2 (match_ident_globdef match_fundef match_varinfo ctx) gl1 gl2 →
    ∀ m m', alloc_globals (globalenv p) m gl1 = some m' →
      alloc_globals (globalenv tp) m gl2 = some m'

def init_mem_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ m, init_mem p = some m → init_mem tp = some m

def find_funct_ptr_transf_partialStatement : Prop :=
  ∀ (A B V : Type) [Linker A] [Linker V] (transf : A → Res B)
    (p : program A V) (tp : program B V),
    match_program (fun _ f tf => transf f = .OK tf) Eq p tp →
    ∀ b f, find_funct_ptr (globalenv p) b = some f →
      ∃ tf, find_funct_ptr (globalenv tp) b = some tf ∧ transf f = .OK tf

def find_funct_transf_partialStatement : Prop :=
  ∀ (A B V : Type) [Linker A] [Linker V] (transf : A → Res B)
    (p : program A V) (tp : program B V),
    match_program (fun _ f tf => transf f = .OK tf) Eq p tp →
    ∀ v f, find_funct (globalenv p) v = some f →
      ∃ tf, find_funct (globalenv tp) v = some tf ∧ transf f = .OK tf

def find_symbol_transf_partialStatement : Prop :=
  ∀ (A B V : Type) [Linker A] [Linker V] (transf : A → Res B)
    (p : program A V) (tp : program B V),
    match_program (fun _ f tf => transf f = .OK tf) Eq p tp →
    ∀ s : ident, find_symbol (globalenv tp) s = find_symbol (globalenv p) s

def senv_transf_partialStatement : Prop :=
  ∀ (A B V : Type) [Linker A] [Linker V] (transf : A → Res B)
    (p : program A V) (tp : program B V),
    match_program (fun _ f tf => transf f = .OK tf) Eq p tp →
      Senv.equiv (to_senv (globalenv p)) (to_senv (globalenv tp))

def init_mem_transf_partialStatement : Prop :=
  ∀ (A B V : Type) [Linker A] [Linker V] (transf : A → Res B)
    (p : program A V) (tp : program B V),
    match_program (fun _ f tf => transf f = .OK tf) Eq p tp →
    ∀ m, init_mem p = some m → init_mem tp = some m

def find_funct_ptr_transfStatement : Prop :=
  ∀ (A B V : Type) [Linker A] [Linker V] (transf : A → B)
    (p : program A V) (tp : program B V),
    match_program (fun _ f tf => tf = transf f) Eq p tp →
    ∀ b f, find_funct_ptr (globalenv p) b = some f →
      find_funct_ptr (globalenv tp) b = some (transf f)

def find_funct_transfStatement : Prop :=
  ∀ (A B V : Type) [Linker A] [Linker V] (transf : A → B)
    (p : program A V) (tp : program B V),
    match_program (fun _ f tf => tf = transf f) Eq p tp →
    ∀ v f, find_funct (globalenv p) v = some f →
      find_funct (globalenv tp) v = some (transf f)

def find_symbol_transfStatement : Prop :=
  ∀ (A B V : Type) [Linker A] [Linker V] (transf : A → B)
    (p : program A V) (tp : program B V),
    match_program (fun _ f tf => tf = transf f) Eq p tp →
    ∀ s : ident, find_symbol (globalenv tp) s = find_symbol (globalenv p) s

def senv_transfStatement : Prop :=
  ∀ (A B V : Type) [Linker A] [Linker V] (transf : A → B)
    (p : program A V) (tp : program B V),
    match_program (fun _ f tf => tf = transf f) Eq p tp →
      Senv.equiv (to_senv (globalenv p)) (to_senv (globalenv tp))

def init_mem_transfStatement : Prop :=
  ∀ (A B V : Type) [Linker A] [Linker V] (transf : A → B)
    (p : program A V) (tp : program B V),
    match_program (fun _ f tf => tf = transf f) Eq p tp →
    ∀ m, init_mem p = some m → init_mem tp = some m

end Genv

/- Rocq's `Function store_zeros` generates this induction principle.  Selected
   proof declarations consume it, so retain its exact proposition while proof
   construction remains assigned to proof grinding. -/
def store_zeros_indStatement : Prop :=
  ∀ (P : mem → block → Z → Z → Option mem → Prop),
    (∀ (m : mem) (b : block) (p n : Z)
      (x : ZArith.BinInt.Z.le n z0),
      zle n z0 = .left x →
      P m b p n (some m)) →
    (∀ (m : mem) (b : block) (p n : Z)
      (x : ZArith.BinInt.Z.gt n z0),
      zle n z0 = .right x →
      ∀ m' : mem,
        Mem.store Mint8unsigned m b p Vzero = some m' →
        P m' b (zAdd p z1) (ZArith.BinInt.Z.sub n z1)
          (store_zeros m' b (zAdd p z1) (ZArith.BinInt.Z.sub n z1)) →
        P m b p n
          (store_zeros m' b (zAdd p z1) (ZArith.BinInt.Z.sub n z1))) →
    (∀ (m : mem) (b : block) (p n : Z)
      (x : ZArith.BinInt.Z.gt n z0),
      zle n z0 = .right x →
      Mem.store Mint8unsigned m b p Vzero = none →
      P m b p n none) →
    ∀ (m : mem) (b : block) (p n : Z),
      P m b p n (store_zeros m b p n)

end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

theorem store_zeros_ind : store_zeros_indStatement := by
  intro P hzero hstore hnone
  have hind : ∀ k, ∀ m b p n,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat n = k →
        P m b p n (store_zeros m b p n) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
        intro m b p n hk
        unfold store_zeros
        split
        · rename_i x hx
          exact hzero m b p n x hx
        · rename_i x hx
          split
          · rename_i hmem
            exact hnone m b p n x hx hmem
          · rename_i m' hmem
            apply hstore m b p n x hx m' hmem
            apply ih (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub n
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
                  .xH)))
            · simpa [hk] using zToNat_sub_one_lt x
            · rfl
  intro m b p n
  exact hind (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat n)
    m b p n rfl

namespace Genv

theorem add_globals_preserves : add_globals_preservesStatement := by
  intro F V P gl
  induction gl with
  | nil =>
      intro ge _ hP
      exact hP
  | cons idg gl ih =>
      intro ge hstep hP
      rcases idg with ⟨id, g⟩
      have hstep' : ∀ ge' id' g', P ge' → (id', g') ∈ gl →
          P (add_global ge' (id', g')) := by
        intro ge' id' g' hP' hin'
        exact hstep ge' id' g' hP' (by simp [hin'])
      apply ih (ge := add_global ge (id, g)) hstep'
      exact hstep ge id g hP (by simp)

theorem add_globals_ensures : add_globals_ensuresStatement := by
  intro F V P id g gl
  induction gl with
  | nil =>
      intro ge hstep hensures hin
      cases hin
  | cons idg gl ih =>
      intro ge hstep hensures hin
      rcases idg with ⟨id', g'⟩
      simp only [List.mem_cons] at hin
      rcases hin with heq | hin
      · cases heq
        change P (add_globals (add_global ge (id, g)) gl)
        have hstep' : ∀ ge' id'' g'', P ge' → (id'', g'') ∈ gl →
            P (add_global ge' (id'', g'')) := by
          intro ge' id'' g'' hP' hin'
          exact hstep ge' id'' g'' hP' (by simp [hin'])
        exact add_globals_preserves F V P gl (add_global ge (id, g)) hstep'
          (hensures ge)
      · have hstep' : ∀ ge' id'' g'', P ge' → (id'', g'') ∈ gl →
            P (add_global ge' (id'', g'')) := by
          intro ge' id'' g'' hP' hin'
          exact hstep ge' id'' g'' hP' (by simp [hin'])
        exact ih (ge := add_global ge (id', g')) hstep' hensures hin

theorem public_symbol_exists : public_symbol_existsStatement := by
  intro F V ge id hpub
  unfold public_symbol at hpub
  cases hfind : find_symbol ge id with
  | none => simp [hfind] at hpub
  | some b => exact ⟨b, rfl⟩

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem shift_symbol_address_32 : shift_symbol_address_32Statement := by
  intro F V ge id ofs n hptr
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

theorem shift_symbol_address_64 : shift_symbol_address_64Statement := by
  intro F V ge id ofs n hptr
  unfold symbol_address
  cases hfind : find_symbol ge id with
  | none => rfl
  | some b =>
      simp [hfind, CompCert4Lean.Common.Values.Val.addl,
        CompCert4Lean.X86_64.Archi.ptr64]

theorem find_funct_inv : find_funct_invStatement := by
  intro F V ge v f h
  cases v with
  | Vundef => simp [find_funct] at h
  | Vint n => simp [find_funct] at h
  | Vfloat n => simp [find_funct] at h
  | Vlong n => simp [find_funct] at h
  | Vsingle n => simp [find_funct] at h
  | Vptr b ofs =>
      unfold find_funct at h
      by_cases hof : ofs = CompCert4Lean.Lib.Integers.Ptrofs.zero
      · simp [hof] at h
        exact ⟨b, by simp [hof]⟩
      · have heqfalse : CompCert4Lean.Lib.Integers.Ptrofs.eq ofs
            CompCert4Lean.Lib.Integers.Ptrofs.zero = false := by
          change decide (ofs.intval =
            (CompCert4Lean.Lib.Integers.Ptrofs.zero).intval) = false
          have hneval : ofs.intval ≠
              (CompCert4Lean.Lib.Integers.Ptrofs.zero).intval := by
            intro hv
            apply hof
            exact CompCert4Lean.Lib.Integers.WordCore.ext hv
          simp [hneval]
        change (if CompCert4Lean.Lib.Integers.Ptrofs.eq ofs
            CompCert4Lean.Lib.Integers.Ptrofs.zero = true then
              find_funct_ptr ge b else none) = some f at h
        rw [heqfalse] at h
        simp at h

theorem find_funct_find_funct_ptr : find_funct_find_funct_ptrStatement := by
  intro F V ge b
  have heq : CompCert4Lean.Lib.Integers.Ptrofs.eq
      CompCert4Lean.Lib.Integers.Ptrofs.zero
      CompCert4Lean.Lib.Integers.Ptrofs.zero = true := by
    simp [CompCert4Lean.Lib.Integers.Ptrofs.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq]
  simp [find_funct, find_funct_ptr, heq]

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_funct_ptr_iff : find_funct_ptr_iffStatement := by
  intro F V ge b f
  unfold find_funct_ptr
  cases h : find_def ge b with
  | none => simp [h]
  | some gd =>
      cases gd with
      | Gfun f' => simp [h]
      | Gvar v => simp [h]

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_var_info_iff : find_var_info_iffStatement := by
  intro F V ge b v
  unfold find_var_info
  cases h : find_def ge b with
  | none => simp [h]
  | some gd =>
      cases gd with
      | Gfun f => simp [h]
      | Gvar v' => simp [h]

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

theorem find_def_symbol : find_def_symbolStatement := by
  intro F V p id g
  have hfold : ∀ (l : List (ident × globdef F V))
      (dm : PTree.t (globdef F V)) (ge : t F V),
      (∀ (id : ident) (g : globdef F V), PTree.get (show positive from id) dm = some g ↔
        ∃ b, find_symbol ge id = some b ∧ find_def ge b = some g) →
      ∀ (id : ident) (g : globdef F V), PTree.get (show positive from id)
        (l.foldl (fun m idg => PTree.set (show positive from idg.1) idg.2 m) dm) = some g ↔
        ∃ b, find_symbol (l.foldl Genv.add_global ge) id = some b ∧
          find_def (l.foldl Genv.add_global ge) b = some g := by
    intro l
    induction l with
    | nil =>
        intro dm ge hinv id g
        simpa only [List.foldl] using hinv id g
    | cons idg l ih =>
        rcases idg with ⟨k, v⟩
        intro dm ge hinv id g
        apply ih (PTree.set (show positive from k) v dm) (Genv.add_global ge (k, v))
        intro x g'
        by_cases hx : x = k
        · subst x
          constructor
          · intro hget
            have hset : PTree.get (show positive from k)
                (PTree.set (show positive from k) v dm) = some v :=
              PTree.gss (show positive from k) v dm
            have hvalue : v = g' := Option.some.inj (hset.symm.trans hget)
            subst g'
            refine ⟨ge.genv_next, ?_, ?_⟩
            · change PTree.get (show positive from k)
                (PTree.set (show positive from k) ge.genv_next ge.genv_symb) =
                some ge.genv_next
              exact PTree.gss (show positive from k) ge.genv_next ge.genv_symb
            · change PTree.get (show positive from ge.genv_next)
                (PTree.set (show positive from ge.genv_next) v ge.genv_defs) =
                some v
              exact PTree.gss (show positive from ge.genv_next) v ge.genv_defs
          · rintro ⟨b, hsymbol, hdef⟩
            have hs : some ge.genv_next = some b := by
              change PTree.get (show positive from k)
                  (PTree.set (show positive from k) ge.genv_next ge.genv_symb) = some b at hsymbol
              exact (PTree.gss (show positive from k) ge.genv_next ge.genv_symb).symm.trans hsymbol
            have hblock : b = ge.genv_next := (Option.some.inj hs).symm
            subst b
            have hvalue : v = g' := by
              have hd : some v = some g' := by
                change PTree.get (show positive from ge.genv_next)
                    (PTree.set (show positive from ge.genv_next) v ge.genv_defs) = some g' at hdef
                exact (PTree.gss (show positive from ge.genv_next) v ge.genv_defs).symm.trans hdef
              exact Option.some.inj hd
            subst g'
            exact PTree.gss (show positive from k) v dm
        · have hxp : (show positive from x) ≠ (show positive from k) := by
            intro h
            exact hx h
          constructor
          · intro hget
            have hset : PTree.get (show positive from x)
                (PTree.set (show positive from k) v dm) = PTree.get (show positive from x) dm :=
              PTree.gso v dm hxp
            have hold : PTree.get (show positive from x) dm = some g' := hset.symm.trans hget
            rcases (hinv x g').mp hold with ⟨b, hsymbol, hdef⟩
            refine ⟨b, ?_, ?_⟩
            · change PTree.get (show positive from x)
                (PTree.set (show positive from k) ge.genv_next ge.genv_symb) = some b
              have hset' : PTree.get (show positive from x)
                  (PTree.set (show positive from k) ge.genv_next ge.genv_symb) =
                  PTree.get (show positive from x) ge.genv_symb :=
                PTree.gso ge.genv_next ge.genv_symb hxp
              exact hset'.trans hsymbol
            · have hbne : b ≠ ge.genv_next := by
                intro heq
                subst b
                exact (Nat.lt_irrefl _ (ge.genv_symb_range x hsymbol))
              change PTree.get (show positive from b)
                  (PTree.set (show positive from ge.genv_next) v ge.genv_defs) = some g'
              have hset' : PTree.get (show positive from b)
                  (PTree.set (show positive from ge.genv_next) v ge.genv_defs) =
                  PTree.get (show positive from b) ge.genv_defs :=
                PTree.gso v ge.genv_defs hbne
              exact hset'.trans hdef
          · rintro ⟨b, hsymbol, hdef⟩
            have hold_symbol : PTree.get (show positive from x) ge.genv_symb = some b := by
              change PTree.get (show positive from x)
                  (PTree.set (show positive from k) ge.genv_next ge.genv_symb) = some b at hsymbol
              have hset' : PTree.get (show positive from x)
                  (PTree.set (show positive from k) ge.genv_next ge.genv_symb) =
                  PTree.get (show positive from x) ge.genv_symb :=
                PTree.gso ge.genv_next ge.genv_symb hxp
              exact hset'.symm.trans hsymbol
            have hbne : b ≠ ge.genv_next := by
              intro heq
              subst b
              exact (Nat.lt_irrefl _ (ge.genv_symb_range x hold_symbol))
            have hold_def : PTree.get (show positive from b) ge.genv_defs = some g' := by
              change PTree.get (show positive from b)
                  (PTree.set (show positive from ge.genv_next) v ge.genv_defs) = some g' at hdef
              have hset' : PTree.get (show positive from b)
                  (PTree.set (show positive from ge.genv_next) v ge.genv_defs) =
                  PTree.get (show positive from b) ge.genv_defs :=
                PTree.gso v ge.genv_defs hbne
              exact hset'.symm.trans hdef
            have hold := (hinv x g').mpr ⟨b, hold_symbol, hold_def⟩
            change PTree.get (show positive from x)
              (PTree.set (show positive from k) v dm) = some g'
            have hset : PTree.get (show positive from x)
                (PTree.set (show positive from k) v dm) = PTree.get (show positive from x) dm :=
              PTree.gso v dm hxp
            exact hset.trans hold
  have hbase : ∀ (x : ident) (g' : globdef F V),
      PTree.get (show positive from x) (PTree.empty (globdef F V)) = some g' ↔
        ∃ b, find_symbol (Genv.empty_genv F V p.prog_public) x = some b ∧
          find_def (Genv.empty_genv F V p.prog_public) b = some g' := by
    intro x g'
    constructor
    · intro hget
      simp [PTree.get, PTree.empty] at hget
    · rintro ⟨b, hsymbol, hdef⟩
      have hfalse : False := by
        change PTree.get (show positive from x)
            (PTree.empty block) = some b at hsymbol
        simp [PTree.get, PTree.empty] at hsymbol
      exact hfalse.elim
  have h := hfold p.prog_defs (PTree.empty (globdef F V))
      (Genv.empty_genv F V p.prog_public) hbase id g
  constructor
  · intro hget
    have hget' : PTree.get (show positive from id)
        (p.prog_defs.foldl
          (fun m idg => PTree.set (show positive from idg.1) idg.2 m)
          (PTree.empty (globdef F V))) = some g := by
      change PTree.get (show positive from id)
        (p.prog_defs.foldl
          (fun m idg => PTree.set (show positive from idg.1) idg.2 m)
          (PTree.empty (globdef F V))) = some g at hget
      exact hget
    have h' := h.mp hget'
    change ∃ b, find_symbol (p.prog_defs.foldl Genv.add_global
      (Genv.empty_genv F V p.prog_public)) id = some b ∧
      find_def (p.prog_defs.foldl Genv.add_global
      (Genv.empty_genv F V p.prog_public)) b = some g at h'
    exact h'
  · intro hex
    have hex' : ∃ b, find_symbol
        (p.prog_defs.foldl Genv.add_global (Genv.empty_genv F V p.prog_public)) id = some b ∧
        find_def (p.prog_defs.foldl Genv.add_global (Genv.empty_genv F V p.prog_public)) b = some g := by
      change ∃ b, find_symbol (p.prog_defs.foldl Genv.add_global
        (Genv.empty_genv F V p.prog_public)) id = some b ∧
        find_def (p.prog_defs.foldl Genv.add_global
        (Genv.empty_genv F V p.prog_public)) b = some g at hex
      exact hex
    have h' := h.mpr hex'
    change PTree.get (show positive from id)
      (p.prog_defs.foldl
        (fun m idg => PTree.set (show positive from idg.1) idg.2 m)
        (PTree.empty (globdef F V))) = some g at h'
    exact h'

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps

theorem find_symbol_inversion : find_symbol_inversionStatement := by
  intro F V p x b hfind
  unfold globalenv at hfind
  let P : t F V → Prop := fun ge =>
    find_symbol ge x = some b → x ∈ CompCert4Lean.Common.AST.prog_defs_names p
  have hpres : ∀ (ge : t F V) (id : CompCert4Lean.Common.AST.ident)
      (g : CompCert4Lean.Common.AST.globdef F V),
      P ge → (id, g) ∈ p.prog_defs → P (add_global ge (id, g)) := by
    intro ge id g hP hin
    change find_symbol (add_global ge (id, g)) x = some b →
      x ∈ CompCert4Lean.Common.AST.prog_defs_names p
    intro hnew
    unfold P at hP
    unfold find_symbol at hnew
    change PTree.get x
      (PTree.set id ge.genv_next ge.genv_symb) = some b at hnew
    by_cases heq : x = id
    · subst x
      have hmem : id ∈ CompCert4Lean.Common.AST.prog_defs_names p := by
        change id ∈ p.prog_defs.map Prod.fst
        exact _root_.List.mem_map.mpr ⟨(id, g), hin, rfl⟩
      exact hmem
    · have hgetold : PTree.get x ge.genv_symb = some b := by
        exact (PTree.gso ge.genv_next ge.genv_symb heq).symm.trans hnew
      exact hP hgetold
  have hbase : P (empty_genv F V p.prog_public) := by
    change find_symbol (empty_genv F V p.prog_public) x = some b →
      x ∈ CompCert4Lean.Common.AST.prog_defs_names p
    intro hbase
    unfold find_symbol at hbase
    change none = some b at hbase
    cases hbase
  have h := add_globals_preserves F V P p.prog_defs
      (empty_genv F V p.prog_public) hpres hbase
  exact h hfind

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem find_def_inversion : find_def_inversionStatement := by
  intro F V p b g hfind
  unfold globalenv at hfind
  let P : t F V → Prop := fun ge =>
    find_def ge b = some g → ∃ id, (id, g) ∈ p.prog_defs
  have hpres : ∀ (ge : t F V) (id : ident) (gd : globdef F V),
      P ge → (id, gd) ∈ p.prog_defs → P (add_global ge (id, gd)) := by
    intro ge id gd hP hmem hnew
    change find_def ge b = some g → ∃ id, (id, g) ∈ p.prog_defs at hP
    change PTree.get (show positive from b)
      (PTree.set (show positive from ge.genv_next) gd ge.genv_defs) = some g at hnew
    by_cases hnext : b = ge.genv_next
    · subst b
      have hs := ptreeGetSetSame (show positive from ge.genv_next) gd ge.genv_defs
      have hgd : gd = g := Option.some.inj (hs.symm.trans hnew)
      subst gd
      exact ⟨id, hmem⟩
    · have ho := ptreeGetSetOther (show positive from b)
          (show positive from ge.genv_next) gd ge.genv_defs hnext
      have hold : PTree.get (show positive from b) ge.genv_defs = some g :=
        ho.symm.trans hnew
      exact hP hold
  have hbase : P (empty_genv F V p.prog_public) := by
    unfold P find_def empty_genv
    intro h
    simp [PTree.get, PTree.empty] at h
  have hall := add_globals_preserves F V P p.prog_defs
      (empty_genv F V p.prog_public) hpres hbase
  exact hall hfind

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

open CompCert4Lean.Common.AST

theorem find_funct_ptr_inversion : find_funct_ptr_inversionStatement := by
  intro F V p b f hfind
  apply find_def_inversion (p := p) (b := b) (g := Gfun f)
  exact (find_funct_ptr_iff (F := F) (V := V) (ge := globalenv p) (b := b) (f := f)).mp hfind

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_funct_inversion : find_funct_inversionStatement := by
  intro F V p v f hfind
  rcases find_funct_inv (F := F) (V := V) (ge := globalenv p) (v := v) (f := f) hfind with
    ⟨b, hv⟩
  subst v
  have hptr : find_funct_ptr (globalenv p) b = some f := by
    exact (find_funct_find_funct_ptr (F := F) (V := V) (ge := globalenv p) (b := b)).symm.trans hfind
  apply find_funct_ptr_inversion (F := F) (V := V) (p := p) (b := b) (f := f)
  exact hptr

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_funct_ptr_prop : find_funct_ptr_propStatement := by
  intro F V P p b f hP hfind
  rcases find_funct_ptr_inversion (F := F) (V := V) (p := p) (b := b) (f := f) hfind with
    ⟨id, hmem⟩
  exact hP id f hmem

theorem find_funct_prop : find_funct_propStatement := by
  intro F V P p v f hP hfind
  rcases find_funct_inversion (F := F) (V := V) (p := p) (v := v) (f := f) hfind with
    ⟨id, hmem⟩
  exact hP id f hmem

theorem global_addresses_distinct : global_addresses_distinctStatement := by
  intro F V ge id1 id2 b1 b2 hids h1 h2 hbeq
  apply hids
  subst b2
  exact ge.genv_vars_inj id1 id2 h1 h2

theorem invert_find_symbol : invert_find_symbolStatement := by
  intro F V ge id b hinvert
  exact invertFindSymbolProof ge id b hinvert

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_invert_symbol : find_invert_symbolStatement := by
  intro F V ge id b hfind
  exact findInvertSymbolProof ge id b hfind

theorem genv_next_add_globals : genv_next_add_globalsStatement := by
  intro F V gl ge
  induction gl generalizing ge with
  | nil => rfl
  | cons x gl ih =>
      change (add_globals (add_global ge x) gl).genv_next =
        advance_next gl (add_global ge x).genv_next
      exact ih (ge := add_global ge x)

theorem genv_public_add_globals : genv_public_add_globalsStatement := by
  intro F V gl ge
  induction gl generalizing ge with
  | nil => rfl
  | cons x gl ih =>
      change (add_globals (add_global ge x) gl).genv_public =
        (add_global ge x).genv_public
      exact ih (ge := add_global ge x)

theorem globalenv_public : globalenv_publicStatement := by
  intro F V p
  unfold globalenv
  exact genv_public_add_globals F V p.prog_defs (empty_genv F V p.prog_public)

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem mem_store_nextblock {chunk : memory_chunk}
    (m : mem) (b : block) (ofs : Z) (v : val) (m' : mem)
    (h : Mem.store chunk m b ofs v = some m') : m'.nextblock = m.nextblock := by
  unfold Mem.store at h
  split at h
  · cases h
    rfl
  · cases h

private theorem mem_alloc_nextblock (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (h : Mem.alloc m lo hi = (m', b)) : m'.nextblock = posSucc m.nextblock := by
  unfold Mem.alloc at h
  cases h
  rfl

private theorem mem_drop_nextblock (m : mem) (b : block) (lo hi : Z) (p : permission)
    (m' : mem) (h : Mem.drop_perm m b lo hi p = some m') : m'.nextblock = m.nextblock := by
  unfold Mem.drop_perm at h
  split at h
  · cases h
    rfl
  · cases h

private theorem store_init_data_nextblock {F V : Type} (ge : Genv.t F V)
    (m : mem) (b : block) (p : Z) (i : init_data) (m' : mem)
    (h : Genv.store_init_data ge m b p i = some m') : m'.nextblock = m.nextblock := by
  cases i with
  | Init_int8 n =>
      change Mem.store Mint8unsigned m b p (Vint n) = some m' at h
      exact mem_store_nextblock (m := m) (b := b) (ofs := p) (v := Vint n) (m' := m') h
  | Init_int16 n =>
      change Mem.store Mint16unsigned m b p (Vint n) = some m' at h
      exact mem_store_nextblock (m := m) (b := b) (ofs := p) (v := Vint n) (m' := m') h
  | Init_int32 n =>
      change Mem.store Mint32 m b p (Vint n) = some m' at h
      exact mem_store_nextblock (m := m) (b := b) (ofs := p) (v := Vint n) (m' := m') h
  | Init_int64 n =>
      change Mem.store Mint64 m b p (Vlong n) = some m' at h
      exact mem_store_nextblock (m := m) (b := b) (ofs := p) (v := Vlong n) (m' := m') h
  | Init_float32 n =>
      change Mem.store Mfloat32 m b p (Vsingle n) = some m' at h
      exact mem_store_nextblock (m := m) (b := b) (ofs := p) (v := Vsingle n) (m' := m') h
  | Init_float64 n =>
      change Mem.store Mfloat64 m b p (Vfloat n) = some m' at h
      exact mem_store_nextblock (m := m) (b := b) (ofs := p) (v := Vfloat n) (m' := m') h
  | Init_addrof id ofs =>
      change (match Genv.find_symbol ge id with
        | none => none
        | some b' => Mem.store Mptr m b p (Vptr b' ofs)) = some m' at h
      cases hfind : Genv.find_symbol ge id with
      | none => simp [hfind] at h
      | some b' =>
          simp [hfind] at h
          exact mem_store_nextblock (m := m) (b := b) (ofs := p)
            (v := Vptr b' ofs) (m' := m') h
  | Init_space n =>
      change some m = some m' at h
      cases h
      rfl

namespace Genv

theorem block_is_volatile_below : block_is_volatile_belowStatement := by
  intro F V ge b h
  exact blockIsVolatileBelowProof ge b h

theorem store_zeros_nextblock : store_zeros_nextblockStatement := by
  intro m b p n m' h
  let P : mem → block → Z → Z → Option mem → Prop := fun m0 _ _ _ result =>
    match result with
    | some m1 => m1.nextblock = m0.nextblock
    | none => True
  have hP : ∀ m0 b0 p0 n0, P m0 b0 p0 n0 (store_zeros m0 b0 p0 n0) := by
    apply store_zeros_ind (P := P)
    · intro m0 b0 p0 n0 x hx
      rfl
    · intro m0 b0 p0 n0 x hx m1 hstore hrec
      cases hresult : store_zeros m1 b0 (zAdd p0 z1) (ZArith.BinInt.Z.sub n0 z1) with
      | none => trivial
      | some m2 =>
          rw [hresult] at hrec
          change m2.nextblock = m0.nextblock
          exact hrec.trans (mem_store_nextblock (m := m0) (b := b0) (ofs := p0)
            (v := Vzero) (m' := m1) hstore)
    · intro m0 b0 p0 n0 x hx hnone
      trivial
  have hs := hP m b p n
  rw [h] at hs
  exact hs

theorem store_init_data_list_nextblock : store_init_data_list_nextblockStatement := by
  intro F V ge idl
  induction idl with
  | nil =>
      intro b m p m' h
      change some m = some m' at h
      cases h
      rfl
  | cons i rest ih =>
      intro b m p m' h
      change (match store_init_data ge m b p i with
        | none => none
        | some m1 => store_init_data_list ge m1 b (zAdd p (init_data_size i)) rest) = some m' at h
      cases hstore : store_init_data ge m b p i with
      | none => simp [hstore] at h
      | some m1 =>
          have hlist : store_init_data_list ge m1 b (zAdd p (init_data_size i)) rest = some m' := by
            simpa [hstore] using h
          have hnext := ih (b := b) (m := m1) (p := zAdd p (init_data_size i))
            (m' := m') hlist
          exact hnext.trans (store_init_data_nextblock ge m b p i m1 hstore)

theorem alloc_global_nextblock : alloc_global_nextblockStatement := by
  intro F V ge g m m' h
  rcases g with ⟨id, gd⟩
  cases gd with
  | Gfun f =>
      unfold alloc_global at h
      cases halloc : Mem.alloc m z0 z1 with
      | mk m1 b =>
          have hdrop : Mem.drop_perm m1 b z0 z1 Nonempty = some m' := by
            simpa [halloc] using h
          exact (mem_drop_nextblock (m := m1) (b := b) (lo := z0)
            (hi := z1) (p := Nonempty) (m' := m') hdrop).trans
            (mem_alloc_nextblock (m := m) (lo := z0) (hi := z1)
              (m' := m1) (b := b) halloc)
  | Gvar v =>
      let init := v.gvar_init
      let sz := init_data_list_size init
      unfold alloc_global at h
      dsimp [init, sz] at h
      cases halloc : Mem.alloc m z0 (init_data_list_size v.gvar_init) with
      | mk m1 b =>
          cases hzeros : store_zeros m1 b z0 (init_data_list_size v.gvar_init) with
          | none => simp [halloc, hzeros] at h
          | some m2 =>
              cases hlist : store_init_data_list ge m2 b z0 v.gvar_init with
              | none => simp [halloc, hzeros, hlist] at h
              | some m3 =>
                  have hdrop : Mem.drop_perm m3 b z0
                      (init_data_list_size v.gvar_init) (perm_globvar v) = some m' := by
                    simpa [halloc, hzeros, hlist] using h
                  have hdropnext := mem_drop_nextblock (m := m3) (b := b)
                    (lo := z0) (hi := init_data_list_size v.gvar_init)
                    (p := perm_globvar v) (m' := m') hdrop
                  have hlistnext := store_init_data_list_nextblock F V ge
                    v.gvar_init b m2 z0 m3 hlist
                  have hzerosnext := store_zeros_nextblock m1 b z0
                    (init_data_list_size v.gvar_init) m2 hzeros
                  have hallocnext := mem_alloc_nextblock (m := m)
                    (lo := z0) (hi := init_data_list_size v.gvar_init)
                    (m' := m1) (b := b) halloc
                  exact hdropnext.trans (hlistnext.trans (hzerosnext.trans hallocnext))

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

namespace Genv

theorem alloc_globals_nextblock : alloc_globals_nextblockStatement := by
  intro F V ge gl
  induction gl with
  | nil =>
      intro m m' h
      change some m = some m' at h
      cases h
      rfl
  | cons g rest ih =>
      intro m m' h
      change (match alloc_global ge m g with
        | none => none
        | some m1 => alloc_globals ge m1 rest) = some m' at h
      cases halloc : alloc_global ge m g with
      | none => simp [halloc] at h
      | some m1 =>
          have hrest : alloc_globals ge m1 rest = some m' := by
            simpa [halloc] using h
          have hnext := ih (m := m1) (m' := m') hrest
          have hallocnext := Genv.alloc_global_nextblock F V ge g m m1 halloc
          calc
            m'.nextblock = advance_next rest m1.nextblock := hnext
            _ = advance_next rest (posSucc m.nextblock) := by rw [hallocnext]
            _ = advance_next (g :: rest) m.nextblock := by rfl

private theorem mem_store_perm (chunk : memory_chunk) (m : mem) (b : block)
    (ofs : Z) (v : val) (m' : mem)
    (h : Mem.store chunk m b ofs v = some m') :
    ∀ (k : perm_kind) (prm : permission) (b' : block) (q : Z),
      Mem.perm m b' q k prm ↔ Mem.perm m' b' q k prm := by
  unfold Mem.store at h
  split at h
  · cases h
    intro k prm b' q
    rfl
  · cases h

theorem store_zeros_perm : store_zeros_permStatement := by
  let P : mem → block → Z → Z → Option mem → Prop := fun m0 _ _ _ result =>
    match result with
    | some m1 =>
        ∀ (k : perm_kind) (prm : permission) (b' : block) (q : Z),
          Mem.perm m0 b' q k prm ↔ Mem.perm m1 b' q k prm
    | none => True
  have hP : ∀ m0 b0 p0 n0, P m0 b0 p0 n0 (store_zeros m0 b0 p0 n0) := by
    apply store_zeros_ind (P := P)
    · intro m0 b0 p0 n0 x hx
      intro k prm b' q
      rfl
    · intro m0 b0 p0 n0 x hx m1 hstore hrec
      cases hresult : store_zeros m1 b0 (zAdd p0 z1) (ZArith.BinInt.Z.sub n0 z1) with
      | none => trivial
      | some m2 =>
          rw [hresult] at hrec
          change ∀ (k : perm_kind) (prm : permission) (b' : block) (q : Z),
            Mem.perm m0 b' q k prm ↔ Mem.perm m2 b' q k prm
          intro k prm b' q
          exact (mem_store_perm Mint8unsigned m0 b0 p0 Vzero m1 hstore k prm b' q).trans
            (hrec k prm b' q)
    · intro m0 b0 p0 n0 x hx hnone
      trivial
  intro k prm b' q m b p n m' h
  have hs := hP m b p n
  rw [h] at hs
  simpa [P] using hs k prm b' q

theorem store_init_data_perm : store_init_data_permStatement := by
  intro F V ge k prm b' q i b m p m' h
  cases i with
  | Init_int8 n =>
      change Mem.store Mint8unsigned m b p (Vint n) = some m' at h
      exact mem_store_perm Mint8unsigned m b p (Vint n) m' h k prm b' q
  | Init_int16 n =>
      change Mem.store Mint16unsigned m b p (Vint n) = some m' at h
      exact mem_store_perm Mint16unsigned m b p (Vint n) m' h k prm b' q
  | Init_int32 n =>
      change Mem.store Mint32 m b p (Vint n) = some m' at h
      exact mem_store_perm Mint32 m b p (Vint n) m' h k prm b' q
  | Init_int64 n =>
      change Mem.store Mint64 m b p (Vlong n) = some m' at h
      exact mem_store_perm Mint64 m b p (Vlong n) m' h k prm b' q
  | Init_float32 n =>
      change Mem.store Mfloat32 m b p (Vsingle n) = some m' at h
      exact mem_store_perm Mfloat32 m b p (Vsingle n) m' h k prm b' q
  | Init_float64 n =>
      change Mem.store Mfloat64 m b p (Vfloat n) = some m' at h
      exact mem_store_perm Mfloat64 m b p (Vfloat n) m' h k prm b' q
  | Init_addrof id ofs =>
      change (match find_symbol ge id with
        | none => none
        | some b'' => Mem.store Mptr m b p (Vptr b'' ofs)) = some m' at h
      cases hfind : find_symbol ge id with
      | none => simp [hfind] at h
      | some b'' =>
          simp [hfind] at h
          exact mem_store_perm Mptr m b p (Vptr b'' ofs) m' h k prm b' q
  | Init_space n =>
      change some m = some m' at h
      cases h
      rfl

theorem store_init_data_list_perm : store_init_data_list_permStatement := by
  intro F V ge k prm b' q idl
  induction idl with
  | nil =>
      intro b m p m' h
      change some m = some m' at h
      cases h
      rfl
  | cons i rest ih =>
      intro b m p m' h
      change (match store_init_data ge m b p i with
        | none => none
        | some m1 => store_init_data_list ge m1 b (zAdd p (init_data_size i)) rest) = some m' at h
      cases hstore : store_init_data ge m b p i with
      | none => simp [hstore] at h
      | some m1 =>
          have hlist : store_init_data_list ge m1 b (zAdd p (init_data_size i)) rest = some m' := by
            simpa [hstore] using h
          have hhead := store_init_data_perm F V ge k prm b' q i b m p m1 hstore
          have htail := ih (b := b) (m := m1) (p := zAdd p (init_data_size i))
            (m' := m') hlist
          exact hhead.trans htail

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

namespace Genv

private theorem pg_unchanged_on_refl (P : block → Z → Prop) (m : mem) :
    Mem.unchanged_on P m m := by
  exact {
    unchanged_on_nextblock := Ple_refl _
    unchanged_on_perm := by
      intro b ofs k prm hP hvalid
      rfl
    unchanged_on_contents := by
      intro b ofs hP hread
      rfl }

private theorem pg_unchanged_on_trans (P : block → Z → Prop)
    (m1 m2 m3 : mem) (h12 : Mem.unchanged_on P m1 m2)
    (h23 : Mem.unchanged_on P m2 m3) : Mem.unchanged_on P m1 m3 := by
  exact {
    unchanged_on_nextblock :=
      Ple_trans _ _ _ h12.unchanged_on_nextblock h23.unchanged_on_nextblock
    unchanged_on_perm := by
      intro b ofs k prm hP hvalid
      have hvalid2 : Mem.valid_block m2 b :=
        Plt_Ple_trans _ _ _ hvalid h12.unchanged_on_nextblock
      exact (h12.unchanged_on_perm b ofs k prm hP hvalid).trans
        (h23.unchanged_on_perm b ofs k prm hP hvalid2)
    unchanged_on_contents := by
      intro b ofs hP hread
      have hread2 : Mem.perm m2 b ofs Cur Readable :=
        (h12.unchanged_on_perm b ofs Cur Readable hP
          (Mem.perm_valid_block m1 b ofs Cur Readable hread)).mp hread
      exact (h23.unchanged_on_contents b ofs hP hread2).trans
        (h12.unchanged_on_contents b ofs hP hread) }

private theorem pg_pmap_get_set_same {A : Type} (i : positive) (x : A)
    (m : PMap.t A) : PMap.get i (PMap.set i x m) = x := by
  change (match PTree.get i (PTree.set i x m.2) with
    | some y => y
    | none => m.1) = x
  rw [PTree.gsspec_proof]
  cases h : peq i i with
  | left _ => simp [h]
  | right hn => exact False.elim (hn rfl)

private theorem pg_pmap_get_set_other {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) (hij : i ≠ j) :
    PMap.get i (PMap.set j x m) = PMap.get i m := by
  change (match PTree.get i (PTree.set j x m.2) with
    | some y => y
    | none => m.1) =
    (match PTree.get i m.2 with
    | some y => y
    | none => m.1)
  rw [PTree.gsspec_proof]
  cases h : peq i j with
  | left heq => exact False.elim (hij heq)
  | right _ => simp [h]

private theorem pg_store_unchanged_on (P : block → Z → Prop)
    (chunk : memory_chunk) (m : mem) (b : block) (ofs : Z) (v : val)
    (m' : mem) (hstore : Mem.store chunk m b ofs v = some m')
    (houtside : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) → ¬ P b i) :
    Mem.unchanged_on P m m' := by
  unfold Mem.store at hstore
  split at hstore
  · cases hstore
    let contents := Mem.setN (encode_val chunk v) ofs (PMap.get b m.mem_contents)
    exact {
      unchanged_on_nextblock := Ple_refl _
      unchanged_on_perm := by
        intro b' ofs' k prm hP hvalid'
        rfl
      unchanged_on_contents := by
        intro b' ofs' hP hread
        by_cases hbb : b' = b
        · subst b'
          change ZMap.get ofs'
            (PMap.get b (PMap.set b contents m.mem_contents)) =
            ZMap.get ofs' (PMap.get b m.mem_contents)
          have hbget : PMap.get b (PMap.set b contents m.mem_contents) = contents :=
            pg_pmap_get_set_same b contents m.mem_contents
          rw [hbget]
          apply Mem.setN_other
          intro i hi heq
          subst i
          apply houtside ofs'
          · have hi' := hi
            rw [encode_val_length chunk v] at hi'
            cases chunk <;> simpa [size_chunk, size_chunk_nat] using hi'
          · exact hP
        · rw [pg_pmap_get_set_other _ _ _ _ hbb] }
  · cases hstore

theorem store_zeros_unchanged : store_zeros_unchangedStatement := by
  intro P
  let Q : mem → block → Z → Z → Option mem → Prop :=
    fun m0 b0 p0 n0 result =>
      match result with
      | some m1 =>
          (∀ houtside : ∀ i, zLe p0 i ∧ zLt i (zAdd p0 n0) → ¬ P b0 i,
            Mem.unchanged_on P m0 m1)
      | none => True
  have hQ : ∀ m0 b0 p0 n0, Q m0 b0 p0 n0 (store_zeros m0 b0 p0 n0) := by
    apply store_zeros_ind (P := Q)
    · intro m0 b0 p0 n0 x hx
      intro houtside
      exact pg_unchanged_on_refl P m0
    · intro m0 b0 p0 n0 x hx m1 hstore hrec
      cases hresult : store_zeros m1 b0 (zAdd p0 z1) (zSub n0 z1) with
      | none => trivial
      | some m2 =>
          rw [hresult] at hrec
          intro houtside
          apply pg_unchanged_on_trans P m0 m1 m2
          · apply pg_store_unchanged_on P Mint8unsigned m0 b0 p0 Vzero m1 hstore
            intro i hi
            apply houtside i
            change intOfZ p0 ≤ intOfZ i ∧ intOfZ i < intOfZ (zAdd p0 n0)
            change intOfZ p0 ≤ intOfZ i ∧
              intOfZ i < intOfZ (zAdd p0 (size_chunk Mint8unsigned)) at hi
            change 0 < intOfZ n0 at x
            have hsize : size_chunk Mint8unsigned = z1 := rfl
            rw [hsize] at hi
            simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hi ⊢
            have hone : intOfZ z1 = 1 := rfl
            rw [hone] at hi
            omega
          · apply hrec
            intro i hi
            apply houtside i
            change intOfZ p0 ≤ intOfZ i ∧ intOfZ i < intOfZ (zAdd p0 n0)
            change intOfZ (zAdd p0 z1) ≤ intOfZ i ∧
              intOfZ i < intOfZ (zAdd (zAdd p0 z1) (zSub n0 z1)) at hi
            simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
              intOfZ_zOfInt] at hi ⊢
            have hone : intOfZ z1 = 1 := rfl
            rw [hone] at hi
            omega
    · intro m0 b0 p0 n0 x hx hnone
      trivial
  intro m b p n m' hstore houtside
  have h := hQ m b p n
  rw [hstore] at h
  exact h houtside

theorem store_init_data_unchanged : store_init_data_unchangedStatement := by
  intro F V ge P b i m p m' hstore houtside
  cases i with
  | Init_int8 n =>
      exact pg_store_unchanged_on P Mint8unsigned m b p (Vint n) m' hstore
        (by simpa [init_data_size, size_chunk] using houtside)
  | Init_int16 n =>
      exact pg_store_unchanged_on P Mint16unsigned m b p (Vint n) m' hstore
        (by simpa [init_data_size, size_chunk] using houtside)
  | Init_int32 n =>
      exact pg_store_unchanged_on P Mint32 m b p (Vint n) m' hstore
        (by simpa [init_data_size, size_chunk] using houtside)
  | Init_int64 n =>
      exact pg_store_unchanged_on P Mint64 m b p (Vlong n) m' hstore
        (by simpa [init_data_size, size_chunk] using houtside)
  | Init_float32 n =>
      exact pg_store_unchanged_on P Mfloat32 m b p (Vsingle n) m' hstore
        (by simpa [init_data_size, size_chunk] using houtside)
  | Init_float64 n =>
      exact pg_store_unchanged_on P Mfloat64 m b p (Vfloat n) m' hstore
        (by simpa [init_data_size, size_chunk] using houtside)
  | Init_space n =>
      change some m = some m' at hstore
      cases hstore
      exact pg_unchanged_on_refl P m
  | Init_addrof id ofs =>
      change (match find_symbol ge id with
        | none => none
        | some b' => Mem.store Mptr m b p (Vptr b' ofs)) = some m' at hstore
      cases hfind : find_symbol ge id with
      | none => simp [hfind] at hstore
      | some b' =>
          simp [hfind] at hstore
          exact pg_store_unchanged_on P Mptr m b p (Vptr b' ofs) m' hstore
            (by
              intro i hi
              apply houtside i
              rcases hi with ⟨hlo, hhi⟩
              have hsize : init_data_size (Init_addrof id ofs) = size_chunk Mptr := by
                rfl
              exact ⟨hlo, by simpa [hsize] using hhi⟩)

theorem store_init_data_list_unchanged : store_init_data_list_unchangedStatement := by
  intro F V ge P b il
  induction il with
  | nil =>
      intro m p m' hstore houtside
      change some m = some m' at hstore
      cases hstore
      exact pg_unchanged_on_refl P m
  | cons i rest ih =>
      intro m p m' hstore houtside
      change (match store_init_data ge m b p i with
        | none => none
        | some m1 => store_init_data_list ge m1 b (zAdd p (init_data_size i)) rest) =
          some m' at hstore
      cases hhead : store_init_data ge m b p i with
      | none => simp [hhead] at hstore
      | some m1 =>
          have htail : store_init_data_list ge m1 b (zAdd p (init_data_size i)) rest =
              some m' := by
            simpa [hhead] using hstore
          apply pg_unchanged_on_trans P m m1 m'
          · apply store_init_data_unchanged F V ge P b i m p m1 hhead
            intro ofs hi
            exact houtside ofs hi.1
          · apply ih m1 (zAdd p (init_data_size i)) m' htail
            intro ofs hlo
            apply houtside ofs
            change intOfZ p ≤ intOfZ ofs
            change intOfZ (zAdd p (init_data_size i)) ≤ intOfZ ofs at hlo
            have hnonneg := init_data_size_pos i
            change 0 ≤ intOfZ (init_data_size i) at hnonneg
            simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hlo
            omega

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

namespace Genv

theorem init_data_size_addrof : init_data_size_addrofStatement := by
  intro id ofs
  rfl

private theorem pg_intOfZ_zadd (x y : Z) :
    intOfZ (zAdd x y) = intOfZ x + intOfZ y := by
  change intOfZ (zOfInt (intOfZ x + intOfZ y)) = intOfZ x + intOfZ y
  rw [intOfZ_zOfInt]

private theorem pg_zadd_lt (x y : Z) (hy : zLt z0 y) : zLt x (zAdd x y) := by
  change intOfZ x < intOfZ (zAdd x y)
  rw [pg_intOfZ_zadd]
  change 0 < intOfZ y at hy
  omega

private theorem pg_zle_trans {x y z : Z} (hxy : zLe x y) (hyz : zLe y z) :
    zLe x z := by
  change intOfZ x ≤ intOfZ y at hxy
  change intOfZ y ≤ intOfZ z at hyz
  change intOfZ x ≤ intOfZ z
  omega

private theorem pg_zlt_zle {x y z : Z} (hxy : zLt x y) (hyz : zLe y z) :
    zLt x z := by
  change intOfZ x < intOfZ y at hxy
  change intOfZ y ≤ intOfZ z at hyz
  change intOfZ x < intOfZ z
  omega

private theorem pg_load_unchanged_on
    (P : block → Z → Prop) (m m' : mem) (chunk : memory_chunk)
    (b : block) (p : Z) (v : val)
    (hunch : Mem.unchanged_on P m m')
    (hP : ∀ i, zLe p i ∧ zLt i (zAdd p (size_chunk chunk)) → P b i)
    (hload : Mem.load chunk m b p = some v) :
    Mem.load chunk m' b p = some v := by
  have hvacc := Mem.load_valid_access m chunk b p v hload
  have hpvalid := hvacc.1 p ⟨by
    change intOfZ p ≤ intOfZ p
    omega, pg_zadd_lt p (size_chunk chunk) (Memdata.size_chunk_pos chunk)⟩
  have hvb := Mem.perm_valid_block m b p Cur Readable hpvalid
  have hrange : Mem.range_perm m' b p (zAdd p (size_chunk chunk)) Cur Readable := by
    intro q hq
    apply (hunch.unchanged_on_perm b q Cur Readable (hP q hq) hvb).mp
    exact hvacc.1 q hq
  have hvalid' : Mem.valid_access m' chunk b p Readable := ⟨hrange, hvacc.2⟩
  have hgetN :
      Mem.getN (size_chunk_nat chunk) p (PMap.get b m'.mem_contents) =
        Mem.getN (size_chunk_nat chunk) p (PMap.get b m.mem_contents) := by
    apply Mem.getN_exten
    intro q hq
    apply hunch.unchanged_on_contents b q
    · apply hP q
      constructor
      · exact hq.1
      · have hsize := Memdata.size_chunk_conv chunk
        simpa [hsize] using hq.2
    · apply hvacc.1 q
      constructor
      · exact hq.1
      · have hsize := Memdata.size_chunk_conv chunk
        simpa [hsize] using hq.2
  rcases Mem.valid_access_load m' chunk b p hvalid' with ⟨v', hload'⟩
  have hres' := Mem.load_result chunk m' b p v' hload'
  have hres := Mem.load_result chunk m b p v hload
  have heq : v' = v := by
    calc
      v' = decode_val chunk
          (Mem.getN (size_chunk_nat chunk) p (PMap.get b m'.mem_contents)) := hres'
      _ = decode_val chunk
          (Mem.getN (size_chunk_nat chunk) p (PMap.get b m.mem_contents)) := by rw [hgetN]
      _ = v := hres.symm
  simpa [heq] using hload'

theorem read_as_zero_unchanged : read_as_zero_unchangedStatement := by
  intro P m b ofs len m' hzero hunch hP chunk p hlo hhi halign
  apply pg_load_unchanged_on P m m' chunk b p _ hunch
  · intro i hi
    apply hP i
    exact ⟨pg_zle_trans hlo hi.1, pg_zlt_zle hi.2 hhi⟩
  · exact hzero chunk p hlo hhi halign

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers
namespace Genv

private theorem pg_alloc_unchanged_on (P : positive → Z → Prop)
    (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (h : Mem.alloc m lo hi = (m', b)) : Mem.unchanged_on P m m' := by
  unfold Mem.alloc at h
  cases h
  constructor
  · exact Ple_succ _
  · intro b' ofs k p hP hvalid
    have hne : b' ≠ m.nextblock := Plt_ne _ _ hvalid
    unfold Mem.perm
    rw [pg_pmap_get_set_other _ _ _ _ hne]
  · intro b' ofs hP hread
    have hne : b' ≠ m.nextblock :=
      Plt_ne _ _ (Mem.perm_valid_block m b' ofs Cur Readable hread)
    rw [pg_pmap_get_set_other _ _ _ _ hne]

private theorem pg_alloc_fresh (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (h : Mem.alloc m lo hi = (m', b)) : b = m.nextblock := by
  unfold Mem.alloc at h
  cases h
  rfl

private theorem pg_drop_perm_unchanged_on (P : positive → Z → Prop)
    (m : mem) (b : positive) (lo hi : Z) (p : permission) (m' : mem)
    (h : Mem.drop_perm m b lo hi p = some m')
    (houtside : ∀ i, zLe lo i ∧ zLt i hi → ¬ P b i) :
    Mem.unchanged_on P m m' := by
  unfold Mem.drop_perm at h
  cases hRange : Mem.range_perm_dec m b lo hi Cur Freeable with
  | right hnone => simp [hRange] at h
  | left hvalidRange =>
      simp [hRange] at h
      cases h
      constructor
      · exact Ple_refl _
      · intro b' ofs k prm hP hvalid
        unfold Mem.perm
        by_cases hne : b' = b
        · subst b'
          rw [pg_pmap_get_set_same]
          change Mem.perm_order' ((PMap.get b m.mem_access) ofs k) prm ↔
            Mem.perm_order' (if (ZArith.BinInt.Z.leb lo ofs &&
              ZArith.BinInt.Z.ltb ofs hi) = true then some p
              else (PMap.get b m.mem_access) ofs k) prm
          by_cases hIn : (ZArith.BinInt.Z.leb lo ofs &&
              ZArith.BinInt.Z.ltb ofs hi) = true
          · have hBounds : zLe lo ofs ∧ zLt ofs hi := by
              change intOfZ lo ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi
              simpa [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb] using hIn
            exact False.elim (houtside ofs hBounds hP)
          · simp [hIn]
        · change Mem.perm_order' ((PMap.get b' m.mem_access) ofs k) prm ↔
            Mem.perm_order' ((PMap.get b' (PMap.set b _ m.mem_access)) ofs k) prm
          rw [pg_pmap_get_set_other _ _ _ _ hne]
      · intro b' ofs hP hread
        by_cases hne : b' = b
        · rfl
        · rfl

private theorem pg_unchanged_on_trans_pos (P : positive → Z → Prop)
    (m1 m2 m3 : mem) (h12 : Mem.unchanged_on P m1 m2)
    (h23 : Mem.unchanged_on P m2 m3) : Mem.unchanged_on P m1 m3 := by
  exact {
    unchanged_on_nextblock :=
      Ple_trans _ _ _ h12.unchanged_on_nextblock h23.unchanged_on_nextblock
    unchanged_on_perm := by
      intro b ofs k prm hP hvalid
      have hvalid2 : Mem.valid_block m2 b :=
        Plt_Ple_trans _ _ _ hvalid h12.unchanged_on_nextblock
      exact (h12.unchanged_on_perm b ofs k prm hP hvalid).trans
        (h23.unchanged_on_perm b ofs k prm hP hvalid2)
    unchanged_on_contents := by
      intro b ofs hP hread
      have hread2 : Mem.perm m2 b ofs Cur Readable :=
        (h12.unchanged_on_perm b ofs Cur Readable hP
          (Mem.perm_valid_block m1 b ofs Cur Readable hread)).mp hread
      exact (h23.unchanged_on_contents b ofs hP hread2).trans
        (h12.unchanged_on_contents b ofs hP hread) }

theorem alloc_global_unchanged : alloc_global_unchangedStatement := by
  intro F V ge P m id g m' h
  cases g with
  | Gfun f =>
      unfold alloc_global at h
      cases halloc : Mem.alloc m z0 z1 with
      | mk m1 b =>
          have hdrop : Mem.drop_perm m1 b z0 z1 Nonempty = some m' := by
            simpa [halloc] using h
          have hb : b = m.nextblock := pg_alloc_fresh m z0 z1 m1 b halloc
          let Q : positive → Z → Prop := fun b' _ => b' ≠ b
          have ha := pg_alloc_unchanged_on Q m z0 z1 m1 b halloc
          have hd := pg_drop_perm_unchanged_on Q m1 b z0 z1 Nonempty m' hdrop (by
            intro ofs _ hQ
            exact hQ rfl)
          have hq := pg_unchanged_on_trans_pos Q m m1 m' ha hd
          exact {
            unchanged_on_nextblock := hq.unchanged_on_nextblock
            unchanged_on_perm := by
              intro b' ofs k prm hP hvalid
              have hQ : Q b' ofs := by
                dsimp [Q]
                intro heq
                apply (Plt_strict b')
                change Plt b' m.nextblock at hvalid
                rw [← hb, ← heq] at hvalid
                exact hvalid
              exact hq.unchanged_on_perm b' ofs k prm hQ hvalid
            unchanged_on_contents := by
              intro b' ofs hP hread
              have hQ : Q b' ofs := by
                dsimp [Q]
                intro heq
                apply (Plt_strict b')
                have hvb := Mem.perm_valid_block m b' ofs Cur Readable hread
                change Plt b' m.nextblock at hvb
                rw [← hb, ← heq] at hvb
                exact hvb
              exact hq.unchanged_on_contents b' ofs hQ hread }
  | Gvar v =>
      let init := v.gvar_init
      let sz := init_data_list_size init
      unfold alloc_global at h
      dsimp [init, sz] at h
      cases halloc : Mem.alloc m z0 (init_data_list_size v.gvar_init) with
      | mk m1 b =>
          cases hzeros : store_zeros m1 b z0 (init_data_list_size v.gvar_init) with
          | none => simp [halloc, hzeros] at h
          | some m2 =>
              cases hlist : store_init_data_list ge m2 b z0 v.gvar_init with
              | none => simp [halloc, hzeros, hlist] at h
              | some m3 =>
                  have hdrop : Mem.drop_perm m3 b z0
                      (init_data_list_size v.gvar_init) (perm_globvar v) = some m' := by
                    simpa [halloc, hzeros, hlist] using h
                  have hb : b = m.nextblock := pg_alloc_fresh m z0
                    (init_data_list_size v.gvar_init) m1 b halloc
                  let Q : positive → Z → Prop := fun b' _ => b' ≠ b
                  have ha := pg_alloc_unchanged_on Q m z0
                    (init_data_list_size v.gvar_init) m1 b halloc
                  have hz := store_zeros_unchanged (P := Q) m1 b z0
                    (init_data_list_size v.gvar_init) m2 hzeros (by
                      intro ofs _ hQ
                      exact hQ rfl)
                  have hl := store_init_data_list_unchanged F V ge (P := Q)
                    b v.gvar_init m2 z0 m3 hlist (by
                      intro ofs _ hQ
                      exact hQ rfl)
                  have hd := pg_drop_perm_unchanged_on Q m3 b z0
                    (init_data_list_size v.gvar_init) (perm_globvar v) m' hdrop (by
                      intro ofs _ hQ
                      exact hQ rfl)
                  have hq12 := pg_unchanged_on_trans_pos Q m m1 m2
                    ha hz
                  have hq123 := pg_unchanged_on_trans_pos Q m m2 m3
                    hq12 hl
                  have hq := pg_unchanged_on_trans_pos Q m m3 m' hq123 hd
                  exact {
                    unchanged_on_nextblock := hq.unchanged_on_nextblock
                    unchanged_on_perm := by
                      intro b' ofs k prm hP hvalid
                      have hQ : Q b' ofs := by
                        dsimp [Q]
                        intro heq
                        apply (Plt_strict b')
                        change Plt b' m.nextblock at hvalid
                        rw [← hb, ← heq] at hvalid
                        exact hvalid
                      exact hq.unchanged_on_perm b' ofs k prm hQ hvalid
                    unchanged_on_contents := by
                      intro b' ofs hP hread
                      have hQ : Q b' ofs := by
                        dsimp [Q]
                        intro heq
                        apply (Plt_strict b')
                        have hvb := Mem.perm_valid_block m b' ofs Cur Readable hread
                        change Plt b' m.nextblock at hvb
                        rw [← hb, ← heq] at hvb
                        exact hvb
                      exact hq.unchanged_on_contents b' ofs hQ hread }

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

namespace Genv

theorem load_store_init_data_invariant : load_store_init_data_invariantStatement := by
  intro F V ge m m' b hload il p h
  induction il generalizing p with
  | nil => trivial
  | cons i rest ih =>
      cases i with
      | Init_int8 n =>
          rcases h with ⟨hhead, htail⟩
          constructor
          · rw [hload Mint8unsigned p]
            exact hhead
          · exact ih (zAdd p (zOfNat 1)) htail
      | Init_int16 n =>
          rcases h with ⟨hhead, htail⟩
          constructor
          · rw [hload Mint16unsigned p]
            exact hhead
          · exact ih (zAdd p (zOfNat 2)) htail
      | Init_int32 n =>
          rcases h with ⟨hhead, htail⟩
          constructor
          · rw [hload Mint32 p]
            exact hhead
          · exact ih (zAdd p (zOfNat 4)) htail
      | Init_int64 n =>
          rcases h with ⟨hhead, htail⟩
          constructor
          · rw [hload Mint64 p]
            exact hhead
          · exact ih (zAdd p (zOfNat 8)) htail
      | Init_float32 n =>
          rcases h with ⟨hhead, htail⟩
          constructor
          · rw [hload Mfloat32 p]
            exact hhead
          · exact ih (zAdd p (zOfNat 4)) htail
      | Init_float64 n =>
          rcases h with ⟨hhead, htail⟩
          constructor
          · rw [hload Mfloat64 p]
            exact hhead
          · exact ih (zAdd p (zOfNat 8)) htail
      | Init_addrof symb ofs =>
          rcases h with ⟨⟨b', hsymb, hhead⟩, htail⟩
          constructor
          · exact ⟨b', hsymb, by rw [hload Mptr p]; exact hhead⟩
          · exact ih (zAdd p (size_chunk Mptr)) htail
      | Init_space n =>
          rcases h with ⟨hzero, htail⟩
          constructor
          · intro chunk q hlo hhi halign
            rw [hload chunk q]
            exact hzero chunk q hlo hhi halign
          · exact ih (zAdd p (zMax n z0)) htail

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers
namespace Genv

theorem init_mem_genv_next : init_mem_genv_nextStatement := by
  intro F V p m hmem
  unfold init_mem at hmem
  have hnext := alloc_globals_nextblock (F := F) (V := V)
    (ge := globalenv p) (gl := p.prog_defs) (m := Mem.empty) (m' := m) hmem
  have hglobal := genv_next_add_globals (F := F) (V := V)
    (gl := p.prog_defs) (ge := empty_genv F V p.prog_public)
  unfold globalenv
  exact hglobal.trans hnext.symm

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib

theorem find_symbol_not_fresh : find_symbol_not_freshStatement := by
  intro F V p id b m hmem hfind
  change Plt b m.nextblock
  rw [← init_mem_genv_next (F := F) (V := V) (p := p) (m := m) hmem]
  unfold find_symbol at hfind
  exact (globalenv p).genv_symb_range id hfind

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib

theorem find_def_not_fresh : find_def_not_freshStatement := by
  intro F V p b g m hmem hfind
  change Plt b m.nextblock
  rw [← init_mem_genv_next (F := F) (V := V) (p := p) (m := m) hmem]
  unfold find_def at hfind
  exact (globalenv p).genv_defs_range b hfind

theorem find_funct_ptr_not_fresh : find_funct_ptr_not_freshStatement := by
  intro F V p b f m hmem hfind
  rw [find_funct_ptr_iff] at hfind
  exact find_def_not_fresh F V p b (Gfun f) m hmem hfind

theorem find_var_info_not_fresh : find_var_info_not_freshStatement := by
  intro F V p b gv m hmem hfind
  rw [find_var_info_iff] at hfind
  exact find_def_not_fresh F V p b (Gvar gv) m hmem hfind

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

namespace Genv

private theorem pg_neutral_zmap_get_set_same {A : Type} (i : Z) (x : A)
    (m : ZMap.t A) : ZMap.get i (ZMap.set i x m) = x := by
  change PMap.get (ZIndexed.index i) (PMap.set (ZIndexed.index i) x m) = x
  exact pg_pmap_get_set_same _ _ _

private theorem pg_neutral_zmap_get_set_other {A : Type} (i j : Z) (x : A)
    (m : ZMap.t A) (h : i ≠ j) :
    ZMap.get i (ZMap.set j x m) = ZMap.get i m := by
  change PMap.get (ZIndexed.index i) (PMap.set (ZIndexed.index j) x m) =
    PMap.get (ZIndexed.index i) m
  apply pg_pmap_get_set_other
  intro hij
  apply h
  exact ZIndexed.index_inj i j hij

private theorem pg_neutral_zadd_succ (p delta : Z) :
    ZArith.BinInt.Z.add (ZArith.BinInt.Z.add p delta) (.Zpos .xH) =
      ZArith.BinInt.Z.add (ZArith.BinInt.Z.add p (.Zpos .xH)) delta := by
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  omega

private theorem pg_neutral_zadd_zero (p : Z) :
    ZArith.BinInt.Z.add p .Z0 = p := by
  exact ZArith.BinInt.Z.add_0_r p

private theorem pg_neutral_setN_inj
    (access : Z → Prop) (delta : Z) (f : Val.meminj)
    {vl1 vl2 : List memval}
    (hvl : list_forall2 (memval_inject f) vl1 vl2) :
    ∀ p c1 c2,
      (∀ q, access q →
        memval_inject f (ZMap.get q c1)
          (ZMap.get (ZArith.BinInt.Z.add q delta) c2)) →
      ∀ q, access q →
        memval_inject f (ZMap.get q (Mem.setN vl1 p c1))
          (ZMap.get (ZArith.BinInt.Z.add q delta)
            (Mem.setN vl2 (ZArith.BinInt.Z.add p delta) c2)) := by
  induction hvl with
  | nil =>
      intro p c1 c2 hbase q hq
      exact hbase q hq
  | cons v1 v2 hv htail ih =>
      intro p c1 c2 hbase q hq
      simp only [Mem.setN]
      change memval_inject f
        (ZMap.get q
          (Mem.setN _ (ZArith.BinInt.Z.add p (.Zpos .xH))
            (ZMap.set p v1 c1)))
        (ZMap.get (ZArith.BinInt.Z.add q delta)
          (Mem.setN _
            (ZArith.BinInt.Z.add
              (ZArith.BinInt.Z.add p delta) (.Zpos .xH))
            (ZMap.set (ZArith.BinInt.Z.add p delta) v2 c2)))
      rw [pg_neutral_zadd_succ]
      apply ih (ZArith.BinInt.Z.add p (.Zpos .xH))
        (ZMap.set p v1 c1)
        (ZMap.set (ZArith.BinInt.Z.add p delta) v2 c2)
      intro r hr
      by_cases heq : r = p
      · subst r
        rw [pg_neutral_zmap_get_set_same, pg_neutral_zmap_get_set_same]
        exact hv
      · rw [pg_neutral_zmap_get_set_other _ _ _ _ heq]
        rw [pg_neutral_zmap_get_set_other]
        · exact hbase r hr
        · intro hadd
          apply heq
          apply intOfZ_injective
          have hadd' := congrArg intOfZ hadd
          simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at hadd'
          omega
      exact hq

private theorem pg_store_inject_neutral
    (chunk : memory_chunk) (m : Mem.mem) (b : positive) (ofs : Z)
    (v : val) (m' : Mem.mem) (thr : positive)
    (hstore : Mem.store chunk m b ofs v = some m')
    (hneutral : Mem.inject_neutral thr m) (hb : Plt b thr)
    (hv : Val.inject (Mem.flat_inj thr) v v) :
    Mem.inject_neutral thr m' := by
  unfold Mem.store at hstore
  split at hstore
  · cases hstore
    exact {
      mi_perm := by
        intro b1 b2 delta q k prm hmap hperm
        exact hneutral.mi_perm b1 b2 delta q k prm hmap hperm
      mi_align := by
        intro b1 b2 delta chunk' q prm hmap hperm
        exact hneutral.mi_align b1 b2 delta chunk' q prm hmap hperm
      mi_memval := by
        intro b1 q b2 delta hmap hread
        change Mem.perm m b1 q Cur Readable at hread
        have hflat : Mem.flat_inj thr b1 = some (b1, .Z0) := by
          cases hplt : plt b1 thr with
          | left _ =>
              unfold Mem.flat_inj
              simp [hplt]
          | right hn =>
              unfold Mem.flat_inj at hmap
              simp [hplt] at hmap
        have hpairs : (b1, .Z0) = (b2, delta) := Option.some.inj (hflat.symm.trans hmap)
        cases hpairs
        change memval_inject (Mem.flat_inj thr)
          (ZMap.get q
            (PMap.get b1
              (PMap.set b (Mem.setN (encode_val chunk v) ofs
                (PMap.get b m.mem_contents)) m.mem_contents)))
          (ZMap.get (ZArith.BinInt.Z.add q .Z0)
            (PMap.get b1
              (PMap.set b (Mem.setN (encode_val chunk v) ofs
                (PMap.get b m.mem_contents)) m.mem_contents)))
        rw [ZArith.BinInt.Z.add_0_r]
        by_cases hbb : b1 = b
        · subst b1
          rw [pg_pmap_get_set_same]
          have henc := encode_val_inject (Mem.flat_inj thr) v v chunk hv
          have hbase : ∀ r, Mem.perm m b r Cur Readable →
              memval_inject (Mem.flat_inj thr)
                (ZMap.get r (PMap.get b m.mem_contents))
                (ZMap.get (ZArith.BinInt.Z.add r .Z0)
                  (PMap.get b m.mem_contents)) := by
            intro r hr
            exact hneutral.mi_memval b r b .Z0 (by
              unfold Mem.flat_inj
              cases hplt : plt b thr with
              | left _ => rfl
              | right hn => exact False.elim (hn hb)) hr
          have hset := pg_neutral_setN_inj
            (access := fun r => Mem.perm m b r Cur Readable)
            (delta := .Z0) (f := Mem.flat_inj thr) henc ofs
            (PMap.get b m.mem_contents) (PMap.get b m.mem_contents)
            hbase q hread
          change memval_inject (Mem.flat_inj thr)
            (ZMap.get q
              (Mem.setN (encode_val chunk v) ofs (PMap.get b m.mem_contents)))
            (ZMap.get (ZArith.BinInt.Z.add q .Z0)
              (Mem.setN (encode_val chunk v)
                (ZArith.BinInt.Z.add ofs .Z0) (PMap.get b m.mem_contents))) at hset
          rw [pg_neutral_zadd_zero, pg_neutral_zadd_zero] at hset
          exact hset
        · rw [pg_pmap_get_set_other _ _ _ _ hbb]
          have hold := hneutral.mi_memval b1 q b1 .Z0 hflat hread
          change memval_inject (Mem.flat_inj thr)
            (ZMap.get q (PMap.get b1 m.mem_contents))
            (ZMap.get (ZArith.BinInt.Z.add q .Z0)
              (PMap.get b1 m.mem_contents)) at hold
          rw [pg_neutral_zadd_zero] at hold
          exact hold }
  · cases hstore

theorem store_zeros_neutral : store_zeros_neutralStatement := by
  let P : Mem.mem → positive → Z → Z → Option Mem.mem → Prop :=
    fun m b _ _ result =>
      match result with
      | some m' => ∀ thr, Mem.inject_neutral thr m →
          Plt b thr → Mem.inject_neutral thr m'
      | none => True
  have hP : ∀ m b p n, P m b p n (store_zeros m b p n) := by
    apply store_zeros_ind (P := P)
    · intro m b p n x hx
      intro thr hneutral hb
      exact hneutral
    · intro m b p n x hx m1 hstore hrec
      cases hresult : store_zeros m1 b
          (ZArith.BinInt.Z.add p (.Zpos .xH))
          (ZArith.BinInt.Z.sub n (.Zpos .xH)) with
      | none => trivial
      | some m2 =>
          rw [hresult] at hrec
          intro thr hneutral hb
          apply hrec thr
          · exact pg_store_inject_neutral Mint8unsigned m b p Vzero m1 thr
              hstore hneutral hb (Val.inject.inject_int _)
          · exact hb
    · intro m b p n x hx hnone
      trivial
  intro thr m b p n m' hneutral hb hstore
  have hs := hP m b p n
  rw [hstore] at hs
  exact hs thr hneutral hb

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta
namespace Genv

private def pg_memdataPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Common") "Memdata"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem pg_store_init_data_ptrofs_add_zero (ofs : ptrofs) :
    Ptrofs.add ofs (Ptrofs.repr (.Z0 : Z)) = ofs := by
  run_tac
    let lctx ← getLCtx
    let ofsF := (lctx.findFromUserName? `ofs).get!
    let e ← mkAppM
      (pg_memdataPrivateName "CompCert4Lean.Common.Memdata.memdata_ptrofs_add_zero")
      #[mkFVar ofsF.fvarId]
    closeMainGoal Name.anonymous e

theorem store_init_data_neutral : store_init_data_neutralStatement := by
  intro F V ge thr hsym m b p id m' hneutral hb hstore
  cases id with
  | Init_int8 n =>
      exact pg_store_inject_neutral Mint8unsigned m b p (Vint n) m' thr
        hstore hneutral hb (Val.inject.inject_int n)
  | Init_int16 n =>
      exact pg_store_inject_neutral Mint16unsigned m b p (Vint n) m' thr
        hstore hneutral hb (Val.inject.inject_int n)
  | Init_int32 n =>
      exact pg_store_inject_neutral Mint32 m b p (Vint n) m' thr
        hstore hneutral hb (Val.inject.inject_int n)
  | Init_int64 n =>
      exact pg_store_inject_neutral Mint64 m b p (Vlong n) m' thr
        hstore hneutral hb (Val.inject.inject_long n)
  | Init_float32 n =>
      exact pg_store_inject_neutral Mfloat32 m b p (Vsingle n) m' thr
        hstore hneutral hb (Val.inject.inject_single n)
  | Init_float64 n =>
      exact pg_store_inject_neutral Mfloat64 m b p (Vfloat n) m' thr
        hstore hneutral hb (Val.inject.inject_float n)
  | Init_addrof symb ofs =>
      simp only [store_init_data] at hstore
      cases hfind : find_symbol ge symb with
      | none => simp [hfind] at hstore
      | some b' =>
          rw [hfind] at hstore
          have hb' : Plt b' thr := hsym symb b' hfind
          have hmap : Mem.flat_inj thr b' = some (b', .Z0) := by
            unfold Mem.flat_inj
            cases hplt : plt b' thr with
            | left _ => rfl
            | right hn => exact False.elim (hn hb')
          apply pg_store_inject_neutral Mptr m b p (Vptr b' ofs) m' thr
            hstore hneutral hb
          exact Val.inject.inject_ptr b' ofs b' ofs .Z0 hmap
            (pg_store_init_data_ptrofs_add_zero ofs).symm
  | Init_space n =>
      simp only [store_init_data] at hstore
      cases hstore
      exact hneutral

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers
namespace Genv

theorem store_init_data_list_neutral : store_init_data_list_neutralStatement := by
  intro F V ge thr hsym b idl
  induction idl with
  | nil =>
      intro m p m' hneutral hb hstore
      change some m = some m' at hstore
      cases hstore
      exact hneutral
  | cons id rest ih =>
      intro m p m' hneutral hb hstore
      change (match store_init_data ge m b p id with
        | none => none
        | some m1 =>
            store_init_data_list ge m1 b (zAdd p (init_data_size id)) rest) = some m' at hstore
      cases hstep : store_init_data ge m b p id with
      | none => simp [hstep] at hstore
      | some m1 =>
          have htail :
              store_init_data_list ge m1 b (zAdd p (init_data_size id)) rest = some m' := by
            simpa [hstep] using hstore
          have hfirst : Mem.inject_neutral thr m1 :=
            store_init_data_neutral F V ge thr hsym m b p id m1 hneutral hb hstep
          exact ih m1 (zAdd p (init_data_size id)) m' hfirst hb htail

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers
namespace Genv

theorem advance_next_le : advance_next_leStatement := by
  intro F V gl x
  induction gl generalizing x with
  | nil => exact Ple_refl x
  | cons g rest ih =>
      change Ple x (advance_next rest (posSucc x))
      exact Ple_trans x (posSucc x) (advance_next rest (posSucc x))
        (Ple_succ x) (ih (posSucc x))

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers
namespace Genv

private theorem pg_alloc_inject_neutral
    (thr : positive) (m : mem) (lo hi : Z) (m' : mem) (b : positive)
    (halloc : Mem.alloc m lo hi = (m', b))
    (hneutral : Mem.inject_neutral thr m) (hnext : Plt m.nextblock thr) :
    Mem.inject_neutral thr m' := by
  unfold Mem.alloc at halloc
  dsimp at halloc
  cases halloc
  constructor
  · intro b1 b2 delta ofs k p hmap hperm
    have hmap_orig := hmap
    unfold Mem.flat_inj at hmap
    cases hplt : plt b1 thr with
    | right hn => simp [hplt] at hmap
    | left hb1 =>
        simp [hplt] at hmap
        rcases hmap with ⟨hb2, hdelta⟩
        subst b2
        by_cases hfresh : b1 = m.nextblock
        · subst b1
          change Mem.perm _ _ (ZArith.BinInt.Z.add ofs delta) k p
          have hadd : ZArith.BinInt.Z.add ofs delta = ofs := by
            rw [← hdelta]
            exact pg_neutral_zadd_zero ofs
          rw [hadd]
          exact hperm
        · unfold Mem.perm
          rw [pg_pmap_get_set_other _ _ _ _ hfresh]
          have hperm' : Mem.perm m b1 ofs k p := by
            unfold Mem.perm at hperm
            rw [pg_pmap_get_set_other _ _ _ _ hfresh] at hperm
            exact hperm
          have hself : Mem.flat_inj thr b1 = some (b1, delta) := by
            exact hmap_orig
          change Mem.perm _ b1 (ZArith.BinInt.Z.add ofs delta) k p
          exact hneutral.mi_perm b1 b1 delta ofs k p hself hperm'
  · intro b1 b2 delta chunk ofs p hmap hrange
    have hmap_orig := hmap
    unfold Mem.flat_inj at hmap
    cases hplt : plt b1 thr with
    | right hn => simp [hplt] at hmap
    | left hb1 =>
        simp [hplt] at hmap
        rcases hmap with ⟨hb2, hdelta⟩
        subst b2
        have hself : Mem.flat_inj thr b1 = some (b1, delta) := by
          exact hmap_orig
        rw [← hdelta]
        exact ZArith.BinInt.Z.divide_0_r _
  · intro b1 ofs b2 delta hmap hread
    have hmap_orig := hmap
    unfold Mem.flat_inj at hmap
    cases hplt : plt b1 thr with
    | right hn => simp [hplt] at hmap
    | left hb1 =>
        simp [hplt] at hmap
        rcases hmap with ⟨hb2, hdelta⟩
        subst b2
        by_cases hfresh : b1 = m.nextblock
        · subst b1
          rw [pg_pmap_get_set_same]
          simp only [ZMap.get, ZMap.init, PMap.gi]
          exact memval_inject.undef _ _
        · rw [pg_pmap_get_set_other _ _ _ _ hfresh]
          have hread' : Mem.perm m b1 ofs Cur Readable := by
            unfold Mem.perm at hread
            rw [pg_pmap_get_set_other _ _ _ _ hfresh] at hread
            exact hread
          have hself : Mem.flat_inj thr b1 = some (b1, delta) := by
            exact hmap_orig
          change memval_inject _ _
            (ZMap.get (ZArith.BinInt.Z.add ofs delta) (PMap.get b1 m.mem_contents))
          exact hneutral.mi_memval b1 ofs b1 delta hself hread'

private theorem pg_drop_inject_neutral
    (thr : positive) (m : mem) (b) (lo hi : Z) (p : permission)
    (m' : mem) (hdrop : Mem.drop_perm m b lo hi p = some m')
    (hneutral : Mem.inject_neutral thr m) (hb : Plt b thr) :
    Mem.inject_neutral thr m' := by
  unfold Mem.drop_perm at hdrop
  cases hr : Mem.range_perm_dec m b lo hi Cur Freeable with
  | right hn => simp [hr] at hdrop
  | left hRange =>
      simp [hr] at hdrop
      cases hdrop
      constructor
      · intro b1 b2 delta ofs k p' hmap hperm
        have hmap_orig := hmap
        unfold Mem.flat_inj at hmap
        cases hplt : plt b1 thr with
        | right hn => simp [hplt] at hmap
        | left hb1 =>
            simp [hplt] at hmap
            rcases hmap with ⟨hb2, hdelta⟩
            subst b2
            change Mem.perm _ _ (ZArith.BinInt.Z.add ofs delta) k p'
            have hadd : ZArith.BinInt.Z.add ofs delta = ofs := by
              rw [← hdelta]
              exact pg_neutral_zadd_zero ofs
            rw [hadd]
            exact hperm
      · intro b1 b2 delta chunk ofs p' hmap hrange
        have hmap_orig := hmap
        unfold Mem.flat_inj at hmap
        cases hplt : plt b1 thr with
        | right hn => simp [hplt] at hmap
        | left hb1 =>
            simp [hplt] at hmap
            rcases hmap with ⟨hb2, hdelta⟩
            subst b2
            rw [← hdelta]
            exact ZArith.BinInt.Z.divide_0_r _
      · intro b1 ofs b2 delta hmap hread
        have hmap_orig := hmap
        unfold Mem.flat_inj at hmap
        cases hplt : plt b1 thr with
        | right hn => simp [hplt] at hmap
        | left hb1 =>
            simp [hplt] at hmap
            rcases hmap with ⟨hb2, hdelta⟩
            subst b2
            by_cases htarget : b1 = b
            · subst b1
              unfold Mem.perm at hread
              rw [pg_pmap_get_set_same] at hread
              split at hread <;> rename_i hIn
              · have hIn' : (ZArith.BinInt.Z.leb lo ofs &&
                    ZArith.BinInt.Z.ltb ofs hi) = true := by
                  exact hIn
                have hBounds : zLe lo ofs ∧ zLt ofs hi := by
                  change intOfZ lo ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi
                  simpa [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb] using hIn'
                have hfree := hRange ofs hBounds
                have hread' : Mem.perm m b ofs Cur Readable :=
                  Mem.perm_implies m b ofs Cur Freeable Readable hfree
                    (CompCert4Lean.Common.Memtype.perm_order.perm_F_any _)
                have hself : Mem.flat_inj thr b = some (b, delta) := by
                  exact hmap_orig
                exact hneutral.mi_memval b ofs b delta hself hread'
              · have hread' : Mem.perm m b ofs Cur Readable := by
                  exact hread
                have hself : Mem.flat_inj thr b = some (b, delta) := by
                  exact hmap_orig
                exact hneutral.mi_memval b ofs b delta hself hread'
            · have hread' : Mem.perm m b1 ofs Cur Readable := by
                unfold Mem.perm at hread
                rw [pg_pmap_get_set_other _ _ _ _ htarget] at hread
                exact hread
              have hself : Mem.flat_inj thr b1 = some (b1, delta) := by
                exact hmap_orig
              exact hneutral.mi_memval b1 ofs b1 delta hself hread'

private theorem pg_alloc_global_neutral
    (F V : Type) (ge : t F V) (thr : block)
    (hsym : ∀ id b, find_symbol ge id = some b → Plt b thr)
    (idg : ident × globdef F V) (m m' : mem)
    (hallocGlobal : alloc_global ge m idg = some m')
    (hneutral : Mem.inject_neutral thr m) (hnext : Plt m.nextblock thr) :
    Mem.inject_neutral thr m' := by
  rcases idg with ⟨id, gd⟩
  cases gd with
  | Gfun f =>
      unfold alloc_global at hallocGlobal
      cases halloc : Mem.alloc m z0 z1 with
      | mk m1 b =>
          have hdrop : Mem.drop_perm m1 b z0 z1 Nonempty = some m' := by
            simpa [halloc] using hallocGlobal
          have hb : b = m.nextblock := by
            unfold Mem.alloc at halloc
            exact (congrArg Prod.snd halloc).symm
          have hbthr : Plt b thr := by simpa [hb] using hnext
          have hallocNeutral : Mem.inject_neutral thr m1 :=
            pg_alloc_inject_neutral thr m z0 z1 m1 b halloc hneutral hnext
          exact pg_drop_inject_neutral thr m1 b z0 z1 Nonempty m' hdrop
            hallocNeutral hbthr
  | Gvar v =>
      unfold alloc_global at hallocGlobal
      cases halloc : Mem.alloc m z0 (init_data_list_size v.gvar_init) with
      | mk m1 b =>
          cases hzeros : store_zeros m1 b z0
              (init_data_list_size v.gvar_init) with
          | none => simp [halloc, hzeros] at hallocGlobal
          | some m2 =>
              cases hlist : store_init_data_list ge m2 b z0 v.gvar_init with
              | none => simp [halloc, hzeros, hlist] at hallocGlobal
              | some m3 =>
                  have hdrop : Mem.drop_perm m3 b z0
                      (init_data_list_size v.gvar_init) (perm_globvar v) = some m' := by
                    simpa [halloc, hzeros, hlist] using hallocGlobal
                  have hb : b = m.nextblock := by
                    unfold Mem.alloc at halloc
                    exact (congrArg Prod.snd halloc).symm
                  have hbthr : Plt b thr := by simpa [hb] using hnext
                  have hallocNeutral : Mem.inject_neutral thr m1 :=
                    pg_alloc_inject_neutral thr m z0
                      (init_data_list_size v.gvar_init) m1 b halloc hneutral hnext
                  have hzerosNeutral : Mem.inject_neutral thr m2 :=
                    store_zeros_neutral thr m1 b z0
                      (init_data_list_size v.gvar_init) m2 hallocNeutral hbthr hzeros
                  have hlistNeutral : Mem.inject_neutral thr m3 :=
                    store_init_data_list_neutral F V ge thr hsym b v.gvar_init
                      m2 z0 m3 hzerosNeutral hbthr hlist
                  exact pg_drop_inject_neutral thr m3 b z0
                    (init_data_list_size v.gvar_init) (perm_globvar v) m' hdrop
                    hlistNeutral hbthr

theorem alloc_globals_neutral : alloc_globals_neutralStatement := by
  intro F V ge thr hsym gl
  induction gl with
  | nil =>
      intro m m' hallocs hneutral hbound
      change some m = some m' at hallocs
      cases hallocs
      exact hneutral
  | cons g rest ih =>
      intro m m' hallocs hneutral hbound
      change (match alloc_global ge m g with
        | none => none
        | some m1 => alloc_globals ge m1 rest) = some m' at hallocs
      cases halloc : alloc_global ge m g with
      | none => simp [halloc] at hallocs
      | some m1 =>
          have hrest : alloc_globals ge m1 rest = some m' := by
            simpa [halloc] using hallocs
          have hrestNext := alloc_globals_nextblock F V ge rest m1 m' hrest
          have hglobalNext := alloc_global_nextblock F V ge g m m1 halloc
          have hsuccFinal : Ple (posSucc m.nextblock) m'.nextblock := by
            rw [hrestNext, hglobalNext]
            exact advance_next_le F V rest (posSucc m.nextblock)
          have hsuccBound : Ple (posSucc m.nextblock) thr :=
            Ple_trans (posSucc m.nextblock) m'.nextblock thr hsuccFinal hbound
          have hnext : Plt m.nextblock thr :=
            Plt_Ple_trans m.nextblock (posSucc m.nextblock) thr
              (Plt_succ m.nextblock) hsuccBound
          have hfirst : Mem.inject_neutral thr m1 :=
            pg_alloc_global_neutral F V ge thr hsym g m m1 halloc hneutral hnext
          exact ih m1 m' hrest hfirst hbound

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

namespace Genv

private theorem pg_initmem_flat_inj_some
    (thr b b' : positive) (delta : Z)
    (hmap : Mem.flat_inj thr b = some (b', delta)) :
    b = b' ∧ (.Z0 : Z) = delta ∧ Plt b thr := by
  unfold Mem.flat_inj at hmap
  cases hplt : plt b thr with
  | left hb =>
      rw [hplt] at hmap
      have hpairs : (b, (.Z0 : Z)) = (b', delta) := Option.some.inj hmap
      exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs, hb⟩
  | right hn => simp [hplt] at hmap

private theorem pg_initmem_zadd_zero (a : Z) :
    ZArith.BinInt.Z.add a (.Z0 : Z) = a := by
  exact ZArith.BinInt.Z.add_0_r a

private theorem pg_initmem_ptrofs_unsigned_range (ofs : Ptrofs.int) :
    ZArith.BinInt.Z.le (.Z0 : Z) (Ptrofs.unsigned ofs) ∧
      ZArith.BinInt.Z.le (Ptrofs.unsigned ofs) Ptrofs.max_unsigned := by
  constructor
  · have h := ofs.intrange.1
    change (-1 : Int) < intOfZ ofs.intval at h
    change (0 : Int) ≤ intOfZ ofs.intval
    omega
  · have h := ofs.intrange.2
    change intOfZ ofs.intval < intOfZ Ptrofs.modulus at h
    change intOfZ ofs.intval ≤
      intOfZ (ZArith.BinInt.Z.sub Ptrofs.modulus (.Zpos .xH))
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change intOfZ ofs.intval ≤ intOfZ Ptrofs.modulus - 1
    omega

private theorem pg_initmem_empty_inject_neutral (thr : positive) :
    Mem.inject_neutral thr Mem.empty := by
  refine { mi_perm := ?_, mi_align := ?_, mi_memval := ?_ }
  · intro b b' delta ofs k p hmap hperm
    rcases pg_initmem_flat_inj_some thr b b' delta hmap with ⟨rfl, rfl, _⟩
    change Mem.perm Mem.empty b
      (ZArith.BinInt.Z.add ofs (.Z0 : Z)) k p
    rw [pg_initmem_zadd_zero]
    exact hperm
  · intro b b' delta chunk ofs p hmap _
    rcases pg_initmem_flat_inj_some thr b b' delta hmap with ⟨rfl, rfl, _⟩
    exact ZArith.BinInt.Z.divide_0_r _
  · intro b ofs b' delta hmap hperm
    rcases pg_initmem_flat_inj_some thr b b' delta hmap with ⟨rfl, rfl, _⟩
    unfold Mem.perm Mem.empty Mem.perm_order' at hperm
    simp [PMap.get, PMap.init, PTree.get, PTree.empty] at hperm

private theorem pg_initmem_neutral_inject (m : Mem.mem)
    (hneutral : Mem.inject_neutral m.nextblock m) :
    Mem.inject (Mem.flat_inj m.nextblock) m m := by
  refine {
    mi_inj := hneutral
    mi_freeblocks := ?_
    mi_mappedblocks := ?_
    mi_no_overlap := ?_
    mi_representable := ?_
    mi_perm_inv := ?_ }
  · intro b hinvalid
    unfold Mem.flat_inj
    cases hplt : plt b m.nextblock with
    | left hb => exact False.elim (hinvalid hb)
    | right _ => rfl
  · intro b b' delta hmap
    rcases pg_initmem_flat_inj_some m.nextblock b b' delta hmap with
      ⟨rfl, rfl, hb⟩
    exact hb
  · intro b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne hmap1 hmap2 _ _
    rcases pg_initmem_flat_inj_some m.nextblock b1 b1' delta1 hmap1 with
      ⟨rfl, rfl, _⟩
    rcases pg_initmem_flat_inj_some m.nextblock b2 b2' delta2 hmap2 with
      ⟨rfl, rfl, _⟩
    exact Or.inl hne
  · intro b b' delta ofs hmap _
    rcases pg_initmem_flat_inj_some m.nextblock b b' delta hmap with
      ⟨rfl, rfl, _⟩
    have hzero : ZArith.BinInt.Z.le (.Z0 : Z) .Z0 := by
      change (0 : Int) ≤ 0
      omega
    change ZArith.BinInt.Z.le (.Z0 : Z) .Z0 ∧
      ZArith.BinInt.Z.le (.Z0 : Z)
        (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) (.Z0 : Z)) ∧
      ZArith.BinInt.Z.le
        (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) (.Z0 : Z))
        Ptrofs.max_unsigned
    rw [pg_initmem_zadd_zero]
    exact And.intro hzero (pg_initmem_ptrofs_unsigned_range ofs)
  · intro b ofs b' delta k p hmap hperm
    rcases pg_initmem_flat_inj_some m.nextblock b b' delta hmap with
      ⟨rfl, rfl, _⟩
    left
    change Mem.perm m b ofs k p
    change Mem.perm m b (ZArith.BinInt.Z.add ofs (.Z0 : Z)) k p at hperm
    rw [pg_initmem_zadd_zero] at hperm
    exact hperm

theorem initmem_inject : initmem_injectStatement := by
  intro F V p m hmem
  unfold init_mem at hmem
  apply pg_initmem_neutral_inject m
  exact alloc_globals_neutral F V (globalenv p) m.nextblock
    (fun id b hfind => find_symbol_not_fresh F V p id b m hmem hfind)
    p.prog_defs Mem.empty m hmem (pg_initmem_empty_inject_neutral m.nextblock)
    (Ple_refl m.nextblock)

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

namespace Genv

theorem store_init_data_aligned : store_init_data_alignedStatement := by
  intro F V ge m b p i m' hstore
  have dfl : ∀ chunk v,
      Mem.store chunk m b p v = some m' →
      align_chunk chunk = init_data_alignment i →
      zDivide (init_data_alignment i) p := by
    intro chunk v h hEq
    have hvalid : Mem.valid_access m chunk b p Writable :=
      Mem.store_valid_access_3 chunk m b p v m' h
    unfold Mem.valid_access at hvalid
    simpa [hEq] using hvalid.2
  cases i with
  | Init_int8 n =>
      change Mem.store Mint8unsigned m b p (Vint n) = some m' at hstore
      exact dfl Mint8unsigned (Vint n) hstore rfl
  | Init_int16 n =>
      change Mem.store Mint16unsigned m b p (Vint n) = some m' at hstore
      exact dfl Mint16unsigned (Vint n) hstore rfl
  | Init_int32 n =>
      change Mem.store Mint32 m b p (Vint n) = some m' at hstore
      exact dfl Mint32 (Vint n) hstore rfl
  | Init_int64 n =>
      change Mem.store Mint64 m b p (Vlong n) = some m' at hstore
      exact dfl Mint64 (Vlong n) hstore rfl
  | Init_float32 n =>
      change Mem.store Mfloat32 m b p (Vsingle n) = some m' at hstore
      exact dfl Mfloat32 (Vsingle n) hstore rfl
  | Init_float64 n =>
      change Mem.store Mfloat64 m b p (Vfloat n) = some m' at hstore
      exact dfl Mfloat64 (Vfloat n) hstore rfl
  | Init_addrof id ofs =>
      change (match find_symbol ge id with
        | none => none
        | some b' => Mem.store Mptr m b p (Vptr b' ofs)) = some m' at hstore
      cases hfind : find_symbol ge id with
      | none => simp [hfind] at hstore
      | some b' =>
          simp [hfind] at hstore
          apply dfl Mptr (Vptr b' ofs) hstore
          unfold init_data_alignment
          exact align_chunk_Mptr
  | Init_space n =>
      change some m = some m' at hstore
      cases hstore
      exact ZArith.BinInt.Z.divide_1_l p

theorem store_init_data_list_aligned : store_init_data_list_alignedStatement := by
  intro F V ge b il
  induction il with
  | nil =>
      intro m p m' hstore
      trivial
  | cons i rest ih =>
      intro m p m' hstore
      change (match store_init_data ge m b p i with
        | none => none
        | some m1 => store_init_data_list ge m1 b (zAdd p (init_data_size i)) rest) = some m' at hstore
      cases hstep : store_init_data ge m b p i with
      | none => simp [hstep] at hstore
      | some m1 =>
          have htail :
              store_init_data_list ge m1 b (zAdd p (init_data_size i)) rest = some m' := by
            simpa [hstep] using hstore
          exact ⟨store_init_data_aligned F V ge m b p i m1 hstep,
            ih m1 (zAdd p (init_data_size i)) m' htail⟩

theorem store_init_data_list_free_idents : store_init_data_list_free_identsStatement := by
  intro F V ge b i o il
  induction il with
  | nil =>
      intro m p m' hstore hin
      cases hin
  | cons i1 rest ih =>
      intro m p m' hstore hin
      change (match store_init_data ge m b p i1 with
        | none => none
        | some m1 => store_init_data_list ge m1 b (zAdd p (init_data_size i1)) rest) = some m' at hstore
      cases hstep : store_init_data ge m b p i1 with
      | none => simp [hstep] at hstore
      | some m1 =>
          have hrest :
              store_init_data_list ge m1 b (zAdd p (init_data_size i1)) rest = some m' := by
            simpa [hstep] using hstore
          rcases List.mem_cons.mp hin with hhead | hmem
          · cases hhead
            change store_init_data ge m b p (Init_addrof i o) = some m1 at hstep
            simp only [store_init_data] at hstep
            cases hfind : find_symbol ge i with
            | none => simp [hfind] at hstep
            | some b' => exact ⟨b', rfl⟩
          · exact ih m1 (zAdd p (init_data_size i1)) m' hrest hmem

theorem init_mem_inversion : init_mem_inversionStatement := by
  intro F V p m id v hmem hin
  have aux : ∀ (defs : List (ident × globdef F V)) (m m' : mem)
      (id : ident) (v : globvar V),
      alloc_globals (globalenv p) m defs = some m' →
      (id, Gvar v) ∈ defs →
      init_data_list_aligned z0 v.gvar_init ∧
        ∀ i o, Init_addrof i o ∈ v.gvar_init →
          ∃ b, find_symbol (globalenv p) i = some b := by
    intro defs
    induction defs with
    | nil =>
        intro m m' id v halloc hmem
        cases hmem
    | cons idg defs ih =>
        intro m m' id v halloc hmem
        change (match alloc_global (globalenv p) m idg with
          | none => none
          | some m1 => alloc_globals (globalenv p) m1 defs) = some m' at halloc
        cases hstep : alloc_global (globalenv p) m idg with
        | none => simp [hstep] at halloc
        | some m1 =>
            have htail : alloc_globals (globalenv p) m1 defs = some m' := by
              simpa [hstep] using halloc
            rcases List.mem_cons.mp hmem with hhead | hrest
            · subst idg
              unfold alloc_global at hstep
              dsimp at hstep
              cases halloc' : Mem.alloc m z0 (init_data_list_size v.gvar_init) with
              | mk m0 b =>
                  cases hzeros : store_zeros m0 b z0
                      (init_data_list_size v.gvar_init) with
                  | none => simp [halloc', hzeros] at hstep
                  | some m2 =>
                      cases hlist : store_init_data_list (globalenv p) m2 b z0
                          v.gvar_init with
                      | none => simp [halloc', hzeros, hlist] at hstep
                      | some m3 =>
                          exact ⟨
                            store_init_data_list_aligned F V (globalenv p) b
                              v.gvar_init m2 z0 m3 hlist,
                            fun i o hin =>
                              store_init_data_list_free_idents F V
                                (globalenv p) b i o v.gvar_init m2 z0 m3 hlist hin⟩
            · exact ih m1 m' id v htail hrest
  exact aux p.prog_defs Mem.empty m id v hmem hin

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

namespace Genv

theorem store_zeros_exists : store_zeros_existsStatement := by
  intro m b p n hrange
  let P : mem → block → Z → Z → Option mem → Prop :=
    fun m b p n r =>
      Mem.range_perm m b p (zAdd p n) Cur Writable → ∃ m', r = some m'
  have hP : ∀ (m : mem) (b : block) (p n : Z),
      P m b p n (store_zeros m b p n) := by
    apply store_zeros_ind (P := P)
    · intro m b p n x hx hrange
      exact ⟨m, rfl⟩
    · intro m b p n x hx m' hstore hrec hrange
      have hv : Mem.valid_access m Mint8unsigned b p Writable := by
        constructor
        · intro ofs hofs
          rcases hofs with ⟨hofslo, hofshi⟩
          apply hrange ofs
          constructor
          · exact hofslo
          · change intOfZ ofs < intOfZ (zAdd p n)
            change intOfZ ofs < intOfZ (zAdd p (zOfNat 1)) at hofshi
            change intOfZ n > 0 at x
            simp [zAdd, ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
              intOfZ_zOfInt] at hofshi ⊢
            omega
        · change zDivide (zOfNat 1) p
          refine ⟨p, ?_⟩
          apply intOfZ_injective
          simp [ZArith.BinInt.Z.mul, ZArith.BinInt.Z.of_nat,
            intOfZ_zOfInt]
      rcases Mem.valid_access_store m Mint8unsigned b p Vzero hv with ⟨m1, hm1⟩
      have hm1eq : m1 = m' := Option.some.inj (hm1.symm.trans hstore)
      subst m1
      have hrange' : Mem.range_perm m' b (zAdd p (zOfNat 1))
          (zAdd (zAdd p (zOfNat 1)) (ZArith.BinInt.Z.sub n (zOfNat 1)))
          Cur Writable := by
        intro ofs hofs
        apply Mem.perm_store_1 Mint8unsigned m b p Vzero m' hstore b ofs Cur Writable
        apply hrange
        rcases hofs with ⟨hofslo, hofshi⟩
        constructor
        · change intOfZ p ≤ intOfZ ofs
          change intOfZ (zAdd p (zOfNat 1)) ≤ intOfZ ofs at hofslo
          simp [zAdd, ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
            intOfZ_zOfInt] at hofslo ⊢
          omega
        · change intOfZ ofs < intOfZ (zAdd p n)
          change intOfZ ofs < intOfZ
            (zAdd (zAdd p (zOfNat 1)) (ZArith.BinInt.Z.sub n (zOfNat 1))) at hofshi
          change intOfZ n > 0 at x
          simp [zAdd, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
            ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hofshi ⊢
          omega
      rcases hrec hrange' with ⟨m2, hm2⟩
      exact ⟨m2, hm2⟩
    · intro m b p n x hx hnone hrange
      have hv : Mem.valid_access m Mint8unsigned b p Writable := by
        constructor
        · intro ofs hofs
          rcases hofs with ⟨hofslo, hofshi⟩
          apply hrange ofs
          constructor
          · exact hofslo
          · change intOfZ ofs < intOfZ (zAdd p n)
            change intOfZ ofs < intOfZ (zAdd p (zOfNat 1)) at hofshi
            change intOfZ n > 0 at x
            simp [zAdd, ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
              intOfZ_zOfInt] at hofshi ⊢
            omega
        · change zDivide (zOfNat 1) p
          refine ⟨p, ?_⟩
          apply intOfZ_injective
          simp [ZArith.BinInt.Z.mul, ZArith.BinInt.Z.of_nat,
            intOfZ_zOfInt]
      rcases Mem.valid_access_store m Mint8unsigned b p Vzero hv with ⟨m', hm'⟩
      rw [hm'] at hnone
      cases hnone
  exact hP m b p n hrange

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

namespace Genv

private theorem pg_mem_store_exists
    (chunk : memory_chunk) (m : mem) (b : block) (p : Z) (v : val)
    (hrange : Mem.range_perm m b p (zAdd p (size_chunk chunk)) Cur Writable)
    (halign : zDivide (align_chunk chunk) p) :
    ∃ m', Mem.store chunk m b p v = some m' := by
  rcases Mem.valid_access_store m chunk b p v ⟨hrange, halign⟩ with ⟨m', hm'⟩
  exact ⟨m', hm'⟩

theorem store_init_data_exists : store_init_data_existsStatement := by
  intro F V ge m b p i hrange halign hfind
  cases i with
  | Init_int8 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (pg_mem_store_exists Mint8unsigned m b p (Vint n)
          (by simpa [init_data_size, size_chunk, Mptr] using hrange)
          (by simpa [init_data_alignment, align_chunk, Mptr] using halign))
  | Init_int16 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (pg_mem_store_exists Mint16unsigned m b p (Vint n)
          (by simpa [init_data_size, size_chunk] using hrange)
          (by simpa [init_data_alignment, align_chunk] using halign))
  | Init_int32 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (pg_mem_store_exists Mint32 m b p (Vint n)
          (by simpa [init_data_size, size_chunk] using hrange)
          (by simpa [init_data_alignment, align_chunk] using halign))
  | Init_int64 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (pg_mem_store_exists Mint64 m b p (Vlong n)
          (by simpa [init_data_size, size_chunk] using hrange)
          (by simpa [init_data_alignment, align_chunk] using halign))
  | Init_float32 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (pg_mem_store_exists Mfloat32 m b p (Vsingle n)
          (by simpa [init_data_size, size_chunk] using hrange)
          (by simpa [init_data_alignment, align_chunk] using halign))
  | Init_float64 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (pg_mem_store_exists Mfloat64 m b p (Vfloat n)
          (by simpa [init_data_size, size_chunk] using hrange)
          (by simpa [init_data_alignment, align_chunk] using halign))
  | Init_addrof id ofs =>
      rcases hfind id ofs rfl with ⟨b', hb'⟩
      have hrange' := hrange
      have hsize : init_data_size (Init_addrof id ofs) = size_chunk Mptr := by
        rfl
      rw [hsize] at hrange'
      have halign' := halign
      simp [init_data_alignment] at halign'
      rw [← align_chunk_Mptr] at halign'
      simpa [store_init_data, hb'] using
        (pg_mem_store_exists Mptr m b p (Vptr b' ofs) hrange' halign')
  | Init_space n =>
      exact ⟨m, rfl⟩

private theorem pg_store_init_data_perm
    (F V : Type) (ge : t F V) (m m' : mem) (b : block) (p : Z)
    (i : init_data) (hm : store_init_data ge m b p i = some m') :
    ∀ b' ofs k prm, Mem.perm m b' ofs k prm → Mem.perm m' b' ofs k prm := by
  intro b' ofs k prm hperm
  cases i with
  | Init_int8 n =>
      exact Mem.perm_store_1 Mint8unsigned m b p (Vint n) m'
        (by simpa [store_init_data] using hm) b' ofs k prm hperm
  | Init_int16 n =>
      exact Mem.perm_store_1 Mint16unsigned m b p (Vint n) m'
        (by simpa [store_init_data] using hm) b' ofs k prm hperm
  | Init_int32 n =>
      exact Mem.perm_store_1 Mint32 m b p (Vint n) m'
        (by simpa [store_init_data] using hm) b' ofs k prm hperm
  | Init_int64 n =>
      exact Mem.perm_store_1 Mint64 m b p (Vlong n) m'
        (by simpa [store_init_data] using hm) b' ofs k prm hperm
  | Init_float32 n =>
      exact Mem.perm_store_1 Mfloat32 m b p (Vsingle n) m'
        (by simpa [store_init_data] using hm) b' ofs k prm hperm
  | Init_float64 n =>
      exact Mem.perm_store_1 Mfloat64 m b p (Vfloat n) m'
        (by simpa [store_init_data] using hm) b' ofs k prm hperm
  | Init_addrof id ofs0 =>
      cases hsym : find_symbol ge id with
      | none => simp [store_init_data, hsym] at hm
      | some b0 =>
          exact Mem.perm_store_1 Mptr m b p (Vptr b0 ofs0) m'
            (by simpa [store_init_data, hsym] using hm) b' ofs k prm hperm
  | Init_space n =>
      have hm' : m' = m := by simpa [store_init_data] using hm.symm
      subst m'
      exact hperm

theorem store_init_data_list_exists : store_init_data_list_existsStatement := by
  intro F V ge b il
  induction il with
  | nil =>
      intro m p hrange halign hfind
      exact ⟨m, rfl⟩
  | cons i rest ih =>
      intro m p hrange halign hfind
      rcases halign with ⟨hhead, htail⟩
      have hrange_i : Mem.range_perm m b p
          (zAdd p (init_data_size i)) Cur Writable := by
        intro ofs hofs
        rcases hofs with ⟨hofslo, hofshi⟩
        apply hrange ofs
        constructor
        · exact hofslo
        · change intOfZ ofs < intOfZ (zAdd p (init_data_list_size (i :: rest)))
          change intOfZ ofs < intOfZ (zAdd p (init_data_size i)) at hofshi
          simp [init_data_list_size, zAdd, ZArith.BinInt.Z.add,
            intOfZ_zOfInt] at hofshi ⊢
          have hnonneg := init_data_list_size_pos rest
          change 0 ≤ intOfZ (init_data_list_size rest) at hnonneg
          omega
      have hfind_i : ∀ id ofs, i = Init_addrof id ofs →
          ∃ b, find_symbol ge id = some b := by
        intro id ofs hi
        apply hfind id ofs
        simp [hi]
      rcases store_init_data_exists F V ge m b p i hrange_i hhead hfind_i with
        ⟨m1, hm1⟩
      have hrange_tail : Mem.range_perm m1 b
          (zAdd p (init_data_size i))
          (zAdd (zAdd p (init_data_size i)) (init_data_list_size rest))
          Cur Writable := by
        intro ofs hofs
        rcases hofs with ⟨hofslo, hofshi⟩
        apply pg_store_init_data_perm F V ge m m1 b p i hm1 b ofs Cur Writable
        apply hrange ofs
        constructor
        · change intOfZ p ≤ intOfZ ofs
          change intOfZ (zAdd p (init_data_size i)) ≤ intOfZ ofs at hofslo
          simp [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hofslo ⊢
          have hi := init_data_size_pos i
          change 0 ≤ intOfZ (init_data_size i) at hi
          omega
        · have hadd : zAdd p (init_data_list_size (i :: rest)) =
              zAdd (zAdd p (init_data_size i)) (init_data_list_size rest) := by
              apply intOfZ_injective
              simp [init_data_list_size, zAdd, ZArith.BinInt.Z.add,
                intOfZ_zOfInt]
              omega
          rw [hadd]
          exact hofshi
      have hfind_tail : ∀ id ofs, Init_addrof id ofs ∈ rest →
          ∃ b, find_symbol ge id = some b := by
        intro id ofs hmem
        apply hfind id ofs
        simp [hmem]
      rcases ih m1 (zAdd p (init_data_size i)) hrange_tail htail hfind_tail with
        ⟨m2, hm2⟩
      refine ⟨m2, ?_⟩
      simp [store_init_data_list, hm1, hm2]

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

namespace Genv

private theorem pg_drop_perm_exists (m : mem) (b : block) (lo hi : Z)
    (p : permission) (hrange : Mem.range_perm m b lo hi Cur Freeable) :
    ∃ m', Mem.drop_perm m b lo hi p = some m' := by
  unfold Mem.drop_perm
  cases hdec : Mem.range_perm_dec m b lo hi Cur Freeable with
  | left hproof =>
      simp [hdec]
  | right hnot =>
      exact False.elim (hnot hrange)

private theorem pg_alloc_range_perm (m : mem) (lo hi : Z) :
    let r := Mem.alloc m lo hi
    Mem.range_perm r.1 r.2 lo hi Cur Freeable := by
  unfold Mem.alloc
  dsimp
  intro ofs hofs
  unfold Mem.perm
  rw [PMap.gss]
  have hle : ZArith.BinInt.Z.leb lo ofs = true := by
    have hh := hofs.1
    change intOfZ lo ≤ intOfZ ofs at hh
    simpa [ZArith.BinInt.Z.leb] using hh
  have hlt : ZArith.BinInt.Z.ltb ofs hi = true := by
    have hh := hofs.2
    change intOfZ ofs < intOfZ hi at hh
    simpa [ZArith.BinInt.Z.ltb] using hh
  change Mem.perm_order'
    (if (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true
      then some Freeable else none) Freeable
  simpa [hle, hlt, Mem.perm_order'] using (perm_refl Freeable)

theorem alloc_global_exists : alloc_global_existsStatement := by
  intro F V ge m idg hvalid
  rcases idg with ⟨id, gd⟩
  cases gd with
  | Gfun f =>
      unfold alloc_global
      cases halloc : Mem.alloc m z0 z1 with
      | mk m1 b =>
          have hrange : Mem.range_perm m1 b z0 z1 Cur Freeable := by
            simpa [halloc] using (pg_alloc_range_perm m z0 z1)
          rcases pg_drop_perm_exists m1 b z0 z1 Nonempty hrange with
            ⟨m2, hdrop⟩
          exact ⟨m2, by simp [halloc, hdrop]⟩
  | Gvar v =>
      rcases hvalid with ⟨halign, hfind⟩
      let sz := init_data_list_size v.gvar_init
      unfold alloc_global
      cases halloc : Mem.alloc m z0 sz with
      | mk m1 b =>
          have hrange1f : Mem.range_perm m1 b z0 sz Cur Freeable := by
            simpa [halloc] using (pg_alloc_range_perm m z0 sz)
          have hrange1 : Mem.range_perm m1 b z0 sz Cur Writable :=
            Mem.range_perm_implies m1 b z0 sz Cur Freeable Writable
              hrange1f (perm_F_any Writable)
          have hzadd : zAdd z0 sz = sz := by
            apply intOfZ_injective
            simp [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
            change intOfZ z0 + intOfZ sz = intOfZ sz
            have hz0 : intOfZ z0 = 0 := by rfl
            rw [hz0]
            omega
          have hrange1' : Mem.range_perm m1 b z0 (zAdd z0 sz) Cur Writable := by
            simpa [hzadd] using hrange1
          rcases store_zeros_exists m1 b z0 sz hrange1' with ⟨m2, hzeros⟩
          have hrange2f : Mem.range_perm m2 b z0 sz Cur Freeable := by
            intro ofs hofs
            exact (store_zeros_perm Cur Freeable b ofs m1 b z0 sz m2 hzeros).mp
              (hrange1f ofs hofs)
          have hrange2 : Mem.range_perm m2 b z0 sz Cur Writable :=
            Mem.range_perm_implies m2 b z0 sz Cur Freeable Writable
              hrange2f (perm_F_any Writable)
          have hsize : init_data_list_size v.gvar_init = sz := by rfl
          rcases store_init_data_list_exists F V ge b v.gvar_init m2 z0
              (by simpa [hsize, hzadd] using hrange2) halign hfind with ⟨m3, hlist⟩
          have hrange3f : Mem.range_perm m3 b z0 sz Cur Freeable := by
            intro ofs hofs
            exact (store_init_data_list_perm F V ge Cur Freeable b ofs
              v.gvar_init b m2 z0 m3 hlist).mp (hrange2f ofs hofs)
          rcases pg_drop_perm_exists m3 b z0 sz (perm_globvar v) hrange3f with
            ⟨m4, hdrop⟩
          exact ⟨m4, by simp [halloc, hzeros, hlist, hdrop, sz]⟩

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

namespace Genv

private theorem pg_alloc_globals_exists
    (F V : Type) (ge : t F V)
    (gl : List (ident × globdef F V)) (m : mem)
    (hvars : ∀ id v, (id, Gvar v) ∈ gl →
      init_data_list_aligned z0 v.gvar_init ∧
        ∀ i o, Init_addrof i o ∈ v.gvar_init →
          ∃ b, find_symbol ge i = some b) :
    ∃ m', alloc_globals ge m gl = some m' := by
  induction gl generalizing m with
  | nil =>
      exact ⟨m, rfl⟩
  | cons g rest ih =>
      rcases g with ⟨id, gd⟩
      have hvars_rest : ∀ id' v, (id', Gvar v) ∈ rest →
          init_data_list_aligned z0 v.gvar_init ∧
            ∀ i o, Init_addrof i o ∈ v.gvar_init →
              ∃ b, find_symbol ge i = some b := by
        intro id' v hmem
        apply hvars id' v
        exact List.mem_cons_of_mem (id, gd) hmem
      have htail : ∀ m1, ∃ m', alloc_globals ge m1 rest = some m' :=
        fun m1 => ih m1 hvars_rest
      cases gd with
      | Gfun f =>
          rcases alloc_global_exists F V ge m (id, Gfun f) trivial with
            ⟨m1, halloc⟩
          rcases htail m1 with ⟨m2, hrest⟩
          exact ⟨m2, by simp [alloc_globals, halloc, hrest]⟩
      | Gvar v =>
          have hv := hvars id v (by simp)
          rcases alloc_global_exists F V ge m (id, Gvar v) hv with
            ⟨m1, halloc⟩
          rcases htail m1 with ⟨m2, hrest⟩
          exact ⟨m2, by simp [alloc_globals, halloc, hrest]⟩

theorem init_mem_exists : init_mem_existsStatement := by
  intro F V p hvars
  unfold init_mem
  exact pg_alloc_globals_exists F V (globalenv p) p.prog_defs Mem.empty hvars

theorem add_global_match : add_global_matchStatement := by
  intro A B V W R ge1 ge2 id g1 g2 h hr
  change positive at id
  constructor
  · simp only [add_global]
    change PArith.BinPos.Pos.succ ge2.genv_next =
      PArith.BinPos.Pos.succ ge1.genv_next
    exact congrArg _ h.mge_next
  · intro id'
    simp only [add_global]
    change PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb)
    have hx2 := @PTree.gsspec_proof _ id' id ge2.genv_next ge2.genv_symb
    have hx1 := @PTree.gsspec_proof _ id' id ge1.genv_next ge1.genv_symb
    cases heq : peq id' id with
    | left hij =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            some ge2.genv_next := by
          simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            some ge1.genv_next := by
          simpa [heq] using hx1
        rw [hx2', hx1', h.mge_next]
    | right hne =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            PTree.get id' ge2.genv_symb := by
          simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            PTree.get id' ge1.genv_symb := by
          simpa [heq] using hx1
        rw [hx2', hx1', h.mge_symb]
  · intro b
    simp only [add_global]
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have hx1 := @PTree.gsspec_proof _ b ge1.genv_next g1 ge1.genv_defs
    have hx2 := @PTree.gsspec_proof _ b ge2.genv_next g2 ge2.genv_defs
    cases heq : peq b ge1.genv_next with
    | left hb =>
        have heq' : b = ge2.genv_next := hb.trans h.mge_next.symm
        cases hpeq2 : peq b ge2.genv_next with
        | left hb2 =>
            have hx1' : PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs) =
                some g1 := by
              simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                some g2 := by
              simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact option_rel.some g1 g2 hr
        | right hb2 => exact False.elim (hb2 heq')
    | right hb =>
        have hb2 : b ≠ ge2.genv_next := by
          intro hbeq
          apply hb
          exact hbeq.trans h.mge_next
        cases hpeq2 : peq b ge2.genv_next with
        | left hb2' => exact False.elim (hb (hb2'.trans h.mge_next))
        | right hb2' =>
            have hx1' : PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs) =
                PTree.get b ge1.genv_defs := by
              simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                PTree.get b ge2.genv_defs := by
              simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact h.mge_defs b

theorem add_globals_match : add_globals_matchStatement := by
  intro A B V W R gl1 gl2 hlist ge1 ge2 hge
  induction hlist generalizing ge1 ge2 with
  | nil => exact hge
  | cons hd1 hd2 hhd htl ih =>
      rcases hhd with ⟨hid, hrel⟩
      cases hd1 with
      | mk id1 gd1 =>
          cases hd2 with
          | mk id2 gd2 =>
              simp only [add_globals, List.foldl]
              change id1 = id2 at hid
              subst id2
              exact ih
                (add_global ge1 (id1, gd1))
                (add_global ge2 (id1, gd2))
                (add_global_match A B V W R ge1 ge2 id1 gd1 gd2 hge hrel)

theorem globalenvs_match : globalenvs_matchStatement := by
  intro C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch
  have hempty : match_genvs
      (match_globdef match_fundef match_varinfo ctx)
      (empty_genv F1 V1 p.prog_public) (empty_genv F2 V2 tp.prog_public) := by
    constructor
    · rfl
    · intro id
      rfl
    · intro b
      exact option_rel.none _
  exact add_globals_match F1 F2 V1 V2
    (match_globdef match_fundef match_varinfo ctx)
    p.prog_defs tp.prog_defs hmatch.1
    (empty_genv F1 V1 p.prog_public) (empty_genv F2 V2 tp.prog_public) hempty

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_def_match_2 : find_def_match_2Statement := by
  intro C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch b
  exact (@globalenvs_match C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch).mge_defs b

open CompCert4Lean.Common.AST

theorem find_def_match : find_def_matchStatement := by
  intro C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch b g hfind
  have hrel := @find_def_match_2 C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch b
  rw [hfind] at hrel
  cases hdef : find_def (globalenv tp) b with
  | none =>
      rw [hdef] at hrel
      cases hrel
  | some tg =>
      rw [hdef] at hrel
      cases hrel with
      | some _ _ htg => exact ⟨tg, rfl, htg⟩

theorem find_funct_ptr_match : find_funct_ptr_matchStatement := by
  intro C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch b f hfind
  have hdef : find_def (globalenv p) b = some (Gfun f) :=
    (find_funct_ptr_iff (F := F1) (V := V1) (ge := globalenv p) (b := b) (f := f)).mp hfind
  rcases @find_def_match C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch b (Gfun f) hdef with
    ⟨tg, htdef, htg⟩
  cases htg with
  | match_globdef_fun ctx' _ f2 horder hfun =>
      exact ⟨ctx', f2,
        (find_funct_ptr_iff (F := F2) (V := V2) (ge := globalenv tp) (b := b) (f := f2)).mpr htdef,
        hfun, horder⟩

theorem find_funct_match : find_funct_matchStatement := by
  intro C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch v f hfind
  rcases find_funct_inv (F := F1) (V := V1) (ge := globalenv p) (v := v) (f := f) hfind with
    ⟨b, hv⟩
  subst v
  have hptr : find_funct_ptr (globalenv p) b = some f :=
    (find_funct_find_funct_ptr (F := F1) (V := V1) (ge := globalenv p) (b := b)).symm.trans hfind
  exact @find_funct_ptr_match C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch b f hptr

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_symbol_match : find_symbol_matchStatement := by
  intro C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch s
  exact (@globalenvs_match C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch).mge_symb s

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem senv_match : senv_matchStatement := by
  intro C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch
  unfold Senv.equiv
  constructor
  · intro id
    exact @find_symbol_match C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch id
  constructor
  · intro id
    change public_symbol (globalenv tp) id = public_symbol (globalenv p) id
    unfold public_symbol
    rw [@find_symbol_match C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch id]
    rw [globalenv_public, globalenv_public, hmatch.2.2]
  · intro b
    change block_is_volatile (globalenv tp) b = block_is_volatile (globalenv p) b
    have hge := @globalenvs_match C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch
    unfold block_is_volatile find_var_info find_def
    have hdefs := hge.mge_defs b
    cases hsrc : CompCert4Lean.Lib.Maps.PTree.get b (globalenv p).genv_defs with
    | none =>
        cases htgt : CompCert4Lean.Lib.Maps.PTree.get b (globalenv tp).genv_defs with
        | none => rfl
        | some gd2 =>
            simp [hsrc, htgt] at hdefs
            cases hdefs
    | some gd1 =>
        cases htgt : CompCert4Lean.Lib.Maps.PTree.get b (globalenv tp).genv_defs with
        | none =>
            simp [hsrc, htgt] at hdefs
            cases hdefs
        | some gd2 =>
            simp [hsrc, htgt] at hdefs
            cases hdefs with
            | some _ _ hrel =>
                cases hrel with
                | match_globdef_fun => rfl
                | match_globdef_var _ _ hvar =>
                    cases hvar
                    rfl

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking

private theorem pg_store_init_data_match
    {C F1 V1 F2 V2 : Type} [Linker C]
    (match_fundef : C → F1 → F2 → Prop)
    (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2)
    (hmatch : match_program_gen match_fundef match_varinfo ctx p tp) :
    ∀ (i : init_data) (m : mem) (b : block) (ofs : Z) (m' : mem),
      store_init_data (globalenv p) m b ofs i = some m' →
      store_init_data (globalenv tp) m b ofs i = some m' := by
  intro i m b ofs m' h
  cases i with
  | Init_int8 n => exact h
  | Init_int16 n => exact h
  | Init_int32 n => exact h
  | Init_int64 n => exact h
  | Init_float32 n => exact h
  | Init_float64 n => exact h
  | Init_space n => exact h
  | Init_addrof id offset =>
      change (match find_symbol (globalenv p) id with
        | none => none
        | some b' => Mem.store Mptr m b ofs (Vptr b' offset)) = some m' at h
      change (match find_symbol (globalenv tp) id with
        | none => none
        | some b' => Mem.store Mptr m b ofs (Vptr b' offset)) = some m'
      have hsym := @find_symbol_match C F1 V1 F2 V2 _ match_fundef match_varinfo
        ctx p tp hmatch id
      rw [hsym]
      exact h

private theorem pg_store_init_data_list_match
    {C F1 V1 F2 V2 : Type} [Linker C]
    (match_fundef : C → F1 → F2 → Prop)
    (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2)
    (hmatch : match_program_gen match_fundef match_varinfo ctx p tp) :
    ∀ (idl : List init_data) (m : mem) (b : block) (ofs : Z) (m' : mem),
      store_init_data_list (globalenv p) m b ofs idl = some m' →
      store_init_data_list (globalenv tp) m b ofs idl = some m' := by
  intro idl
  induction idl with
  | nil =>
      intro m b ofs m' h
      exact h
  | cons i rest ih =>
      intro m b ofs m' h
      change (match store_init_data (globalenv p) m b ofs i with
        | none => none
        | some m1 =>
            store_init_data_list (globalenv p) m1 b
              (zAdd ofs (init_data_size i)) rest) = some m' at h
      cases hstep : store_init_data (globalenv p) m b ofs i with
      | none => simp [hstep] at h
      | some m1 =>
          have htail : store_init_data_list (globalenv p) m1 b
              (zAdd ofs (init_data_size i)) rest = some m' := by
            simpa [hstep] using h
          have hfirst := pg_store_init_data_match match_fundef match_varinfo ctx p tp
            hmatch i m b ofs m1 hstep
          change (match store_init_data (globalenv tp) m b ofs i with
            | none => none
            | some m1 =>
                store_init_data_list (globalenv tp) m1 b
                  (zAdd ofs (init_data_size i)) rest) = some m'
          rw [hfirst]
          exact ih m1 b (zAdd ofs (init_data_size i)) m' htail

theorem alloc_globals_match : alloc_globals_matchStatement := by
  intro C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch
  intro gl1 gl2 hgl
  induction hgl with
  | nil =>
      intro m m' h
      exact h
  | @cons hd1 tl1 hd2 tl2 hhd htl ih =>
      intro m m' h
      rcases hd1 with ⟨id1, gd1⟩
      rcases hd2 with ⟨id2, gd2⟩
      rcases hhd with ⟨hid, hgd⟩
      change id1 = id2 at hid
      subst id2
      change (match alloc_global (globalenv p) m (id1, gd1) with
        | none => none
        | some m1 => alloc_globals (globalenv p) m1 tl1) = some m' at h
      cases halloc : alloc_global (globalenv p) m (id1, gd1) with
      | none => simp [halloc] at h
      | some m1 =>
          have htail : alloc_globals (globalenv p) m1 tl1 = some m' := by
            simpa [halloc] using h
          have halloc' : alloc_global (globalenv tp) m (id1, gd2) = some m1 := by
            cases gd1 with
            | Gfun f1 =>
                cases gd2 with
                | Gfun f2 =>
                    simpa [alloc_global] using halloc
                | Gvar v2 => cases hgd
            | Gvar v1 =>
                cases gd2 with
                | Gfun f2 => cases hgd
                | Gvar v2 =>
                    cases hgd with
                    | match_globdef_var _ _ hvar =>
                        cases hvar with
                        | match_globvar_intro info1 info2 init readonly volatile hinfo =>
                            unfold alloc_global at halloc ⊢
                            cases hmem : Mem.alloc m z0 (init_data_list_size init) with
                            | mk m2 b =>
                                cases hzeros : store_zeros m2 b z0
                                    (init_data_list_size init) with
                                | none => simp [hmem, hzeros] at halloc
                                | some m3 =>
                                    cases hlist : store_init_data_list (globalenv p) m3 b z0
                                        init with
                                    | none => simp [hmem, hzeros, hlist] at halloc
                                    | some m4 =>
                                        have hstored : store_init_data_list (globalenv tp) m3 b z0
                                            init = some m4 :=
                                          pg_store_init_data_list_match match_fundef match_varinfo
                                            ctx p tp hmatch init m3 b z0 m4 hlist
                                        simpa [perm_globvar, hmem, hzeros, hlist, hstored] using halloc
          change (match alloc_global (globalenv tp) m (id1, gd2) with
            | none => none
            | some m1 => alloc_globals (globalenv tp) m1 tl2) = some m'
          rw [halloc']
          exact ih m1 m' htail

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem init_mem_match : init_mem_matchStatement := by
  intro C F1 V1 F2 V2 _ match_fundef match_varinfo ctx p tp hmatch
  intro m hmem
  unfold init_mem at hmem ⊢
  exact alloc_globals_match C F1 V1 F2 V2 match_fundef match_varinfo ctx p tp
    hmatch p.prog_defs tp.prog_defs hmatch.1 CompCert4Lean.Common.Memory.Mem.empty m hmem

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_funct_ptr_transf_partial : find_funct_ptr_transf_partialStatement := by
  intro A B V _ _ transf p tp hmatch b f hfind
  rcases @find_funct_ptr_match (CompCert4Lean.Common.AST.program A V) A V B V _
      (fun _ f tf => transf f = .OK tf) Eq p p tp hmatch b f hfind with
    ⟨_, tf, htf, htransf, _⟩
  exact ⟨tf, htf, htransf⟩

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_funct_transf_partial : find_funct_transf_partialStatement := by
  intro A B V _ _ transf p tp hmatch v f hfind
  rcases @find_funct_match (CompCert4Lean.Common.AST.program A V) A V B V _
      (fun _ f tf => transf f = .OK tf) Eq p p tp hmatch v f hfind with
    ⟨_, tf, htf, htransf, _⟩
  exact ⟨tf, htf, htransf⟩

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_symbol_transf_partial : find_symbol_transf_partialStatement := by
  intro A B V _ _ transf p tp hmatch s
  exact @find_symbol_match (CompCert4Lean.Common.AST.program A V) A V B V _
      (fun _ f tf => transf f = .OK tf) Eq p p tp hmatch s

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem senv_transf_partial : senv_transf_partialStatement := by
  intro A B V _ _ transf p tp hmatch
  exact @senv_match (CompCert4Lean.Common.AST.program A V) A V B V _
      (fun _ f tf => transf f = .OK tf) Eq p p tp hmatch

theorem init_mem_transf_partial : init_mem_transf_partialStatement := by
  intro A B V _ _ transf p tp hmatch
  exact @init_mem_match (CompCert4Lean.Common.AST.program A V) A V B V _
      (fun _ f tf => transf f = .OK tf) Eq p p tp hmatch

theorem find_funct_ptr_transf : find_funct_ptr_transfStatement := by
  intro A B V _ _ transf p tp hmatch b f hfind
  rcases @find_funct_ptr_match (CompCert4Lean.Common.AST.program A V) A V B V _
      (fun _ f tf => tf = transf f) Eq p p tp hmatch b f hfind with
    ⟨_, tf, htf, htransf, _⟩
  simpa [htransf] using htf

theorem find_funct_transf : find_funct_transfStatement := by
  intro A B V _ _ transf p tp hmatch v f hfind
  rcases @find_funct_match (CompCert4Lean.Common.AST.program A V) A V B V _
      (fun _ f tf => tf = transf f) Eq p p tp hmatch v f hfind with
    ⟨_, tf, htf, htransf, _⟩
  simpa [htransf] using htf

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_symbol_transf : find_symbol_transfStatement := by
  intro A B V _ _ transf p tp hmatch s
  exact @find_symbol_match (CompCert4Lean.Common.AST.program A V) A V B V _
      (fun _ f tf => tf = transf f) Eq p p tp hmatch s

theorem senv_transf : senv_transfStatement := by
  intro A B V _ _ transf p tp hmatch
  exact @senv_match (CompCert4Lean.Common.AST.program A V) A V B V _
      (fun _ f tf => tf = transf f) Eq p p tp hmatch

theorem init_mem_transf : init_mem_transfStatement := by
  intro A B V _ _ transf p tp hmatch
  exact @init_mem_match (CompCert4Lean.Common.AST.program A V) A V B V _
      (fun _ f tf => tf = transf f) Eq p p tp hmatch

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

theorem find_symbol_exists : find_symbol_existsStatement := by
  intro F V p id g hin
  unfold globalenv
  apply add_globals_ensures F V
    (fun ge => ∃ b, find_symbol ge id = some b)
    id g p.prog_defs (empty_genv F V p.prog_public)
  · intro ge id' g' hP hmem
    rcases hP with ⟨b, hb⟩
    by_cases heq : id = id'
    · subst id'
      refine ⟨ge.genv_next, ?_⟩
      change CompCert4Lean.Lib.Maps.PTree.get id
        (CompCert4Lean.Lib.Maps.PTree.set id ge.genv_next ge.genv_symb) =
          some ge.genv_next
      exact CompCert4Lean.Lib.Maps.PTree.gss _ _ _
    · refine ⟨b, ?_⟩
      change CompCert4Lean.Lib.Maps.PTree.get id
        (CompCert4Lean.Lib.Maps.PTree.set id' ge.genv_next ge.genv_symb) = some b
      rw [CompCert4Lean.Lib.Maps.PTree.gso ge.genv_next ge.genv_symb heq]
      exact hb
  · intro ge
    refine ⟨ge.genv_next, ?_⟩
    change CompCert4Lean.Lib.Maps.PTree.get id
      (CompCert4Lean.Lib.Maps.PTree.set id ge.genv_next ge.genv_symb) =
        some ge.genv_next
    exact CompCert4Lean.Lib.Maps.PTree.gss _ _ _
  · exact hin

end Genv
end CompCert4Lean.Common.Globalenvs
namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

namespace Genv

private theorem pg_store_zeros_loadbytes_unchanged
    (P : block → Z → Prop) (m m' : mem) (b : block) (ofs n : Z)
    (bytes : List memval) (hunch : Mem.unchanged_on P m m')
    (hn : zLe z0 n)
    (hP : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs n) → P b i)
    (hload : Mem.loadbytes m b ofs n = some bytes) :
    Mem.loadbytes m' b ofs n = some bytes := by
  unfold Mem.loadbytes at hload ⊢
  cases hdec : Mem.range_perm_dec m b ofs (zAdd ofs n) Cur Readable with
  | right hnot =>
      rw [hdec] at hload
      change none = some bytes at hload
      cases hload
  | left hrange =>
      have hrange' : Mem.range_perm m' b ofs (zAdd ofs n) Cur Readable := by
        intro i hi
        have hperm := hrange i hi
        exact (hunch.unchanged_on_perm b i Cur Readable (hP i hi)
          (Mem.perm_valid_block m b i Cur Readable hperm)).mp hperm
      cases hdec' : Mem.range_perm_dec m' b ofs (zAdd ofs n) Cur Readable with
      | right hnot => exact False.elim (hnot hrange')
      | left _ =>
          rw [hdec] at hload
          change some (Mem.getN (ZArith.BinInt.Z.to_nat n) ofs
            (PMap.get b m.mem_contents)) = some bytes at hload
          change some (Mem.getN (ZArith.BinInt.Z.to_nat n) ofs
            (PMap.get b m'.mem_contents)) = some bytes
          simp only [Option.some.injEq] at hload ⊢
          rw [← hload]
          apply Mem.getN_exten
          intro i hi
          have hnid : zOfNat (ZArith.BinInt.Z.to_nat n) = n :=
            ZArith.Znat.Z2Nat.id n hn
          have hi' : zLe ofs i ∧ zLt i (zAdd ofs n) := by
            simpa [hnid] using hi
          exact hunch.unchanged_on_contents b i (hP i hi') (hrange i hi')

private abbrev pg_z1 : Z := .Zpos .xH

private theorem pg_z1_int : intOfZ pg_z1 = 1 := rfl

private theorem pg_zOfNat_nonneg (n : Nat) :
    ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.of_nat n) := by
  change (0 : Int) ≤ intOfZ (ZArith.BinInt.Z.of_nat n)
  simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  change (0 : Int) ≤ Int.ofNat n
  exact Int.ofNat_zero_le n

theorem store_zeros_loadbytes : store_zeros_loadbytesStatement := by
  intro m b p n m' hzeros
  let P : mem → block → Z → Z → Option mem → Prop :=
    fun m0 b0 p0 n0 result =>
      ∀ m1, result = some m1 → readbytes_as_zero m1 b0 p0 n0
  have hP : ∀ m0 b0 p0 n0, P m0 b0 p0 n0 (store_zeros m0 b0 p0 n0) := by
    apply store_zeros_ind (P := P)
    · intro m0 b0 p0 n0 hn hbranch m1 hm1 q len hlo hhi
      cases Option.some.inj hm1
      have hlen : len = 0 := by
        change intOfZ n0 ≤ 0 at hn
        change intOfZ p0 ≤ intOfZ q at hlo
        change intOfZ (zAdd q (zOfNat len)) ≤ intOfZ (zAdd p0 n0) at hhi
        simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
          intOfZ_zOfInt] at hhi
        omega
      subst len
      simpa using (Mem.loadbytes_empty m0 b0 q (zOfNat 0) (by
        change intOfZ (zOfNat 0) ≤ 0
        simp [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]))
    · intro m0 b0 p0 n0 hn hbranch m1 hstore hrec
      cases hresult : store_zeros m1 b0 (zAdd p0 pg_z1)
          (ZArith.BinInt.Z.sub n0 pg_z1) with
      | none =>
          intro m2 hm2
          cases hm2
      | some m2 =>
          rw [hresult] at hrec
          intro m2' hm2'
          cases Option.some.inj hm2'
          intro q len hlo hhi
          by_cases hqp : q = p0
          · subst q
            cases len with
            | zero =>
                simpa using (Mem.loadbytes_empty m2 b0 p0 (zOfNat 0) (by
                  change intOfZ (zOfNat 0) ≤ 0
                  simp [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]))
            | succ len =>
                let Q : block → Z → Prop := fun b' i => b' = b0 ∧ i = p0
                have hunch : Mem.unchanged_on Q m1 m2 := by
                  apply Genv.store_zeros_unchanged Q m1 b0 (zAdd p0 pg_z1)
                    (ZArith.BinInt.Z.sub n0 pg_z1) m2 hresult
                  intro i hi hQi
                  rcases hQi with ⟨_, hiEq⟩
                  subst i
                  have hlo' := hi.1
                  change intOfZ (zAdd p0 pg_z1) ≤ intOfZ p0 at hlo'
                  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at hlo'
                  rw [pg_z1_int] at hlo'
                  omega
                have hbyte :
                    Mem.loadbytes m1 b0 p0 pg_z1 =
                      some [Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)] := by
                  have hs := Mem.loadbytes_store_same Mint8unsigned m0 b0 p0 Vzero m1 hstore
                  have henc : encode_val Mint8unsigned Vzero =
                      [Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)] := by
                    rfl
                  have hsize : size_chunk Mint8unsigned = pg_z1 := rfl
                  rw [← hsize]
                  exact hs.trans (congrArg some henc)
                have hbyte' :
                    Mem.loadbytes m2 b0 p0 pg_z1 =
                      some [Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)] := by
                  apply pg_store_zeros_loadbytes_unchanged Q m1 m2 b0 p0 pg_z1 _ hunch
                  · change (0 : Int) ≤ 1
                    omega
                  · intro i hi
                    constructor
                    · rfl
                    · change intOfZ p0 ≤ intOfZ i ∧
                        intOfZ i < intOfZ (zAdd p0 pg_z1) at hi
                      change i = p0
                      apply intOfZ_injective
                      simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at hi
                      rw [pg_z1_int] at hi
                      omega
                  · exact hbyte
                have htail : Mem.loadbytes m2 (b0) (zAdd p0 pg_z1) (zOfNat len) =
                    some (List.replicate len
                      (Byte (CompCert4Lean.Lib.Integers.Byte.repr z0))) := by
                  apply hrec m2 rfl (zAdd p0 pg_z1) len
                  · change intOfZ (zAdd p0 pg_z1) ≤ intOfZ (zAdd p0 pg_z1)
                    omega
                  · change intOfZ
                        (zAdd (zAdd p0 pg_z1) (zOfNat len)) ≤
                      intOfZ (zAdd (zAdd p0 pg_z1)
                        (ZArith.BinInt.Z.sub n0 pg_z1))
                    change intOfZ (zAdd p0 (zOfNat (Nat.succ len))) ≤
                      intOfZ (zAdd p0 n0) at hhi
                    simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
                      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hhi ⊢
                    rw [pg_z1_int]
                    omega
                have hcat := Mem.loadbytes_concat m2 b0 p0 pg_z1 (zOfNat len)
                  [Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)]
                  (List.replicate len
                    (Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)))
                  hbyte' htail
                  (by change (0 : Int) ≤ 1; omega)
                  (pg_zOfNat_nonneg len)
                have hsizes : zAdd pg_z1 (zOfNat len) = zOfNat (Nat.succ len) := by
                  apply intOfZ_injective
                  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
                    intOfZ_zOfInt]
                  rw [pg_z1_int]
                  calc
                    1 + Int.ofNat len = Int.ofNat len + 1 := Int.add_comm _ _
                    _ = Int.ofNat len.succ := (Int.natCast_succ len).symm
                simpa [hsizes, List.replicate_succ] using hcat
          · apply hrec m2 rfl q len
            · change intOfZ (zAdd p0 pg_z1) ≤ intOfZ q
              change intOfZ p0 ≤ intOfZ q at hlo
              have hne : intOfZ q ≠ intOfZ p0 := by
                intro heq
                exact hqp (intOfZ_injective heq)
              simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
              rw [pg_z1_int]
              omega
            · change intOfZ (zAdd q (zOfNat len)) ≤
                intOfZ (zAdd (zAdd p0 pg_z1)
                  (ZArith.BinInt.Z.sub n0 pg_z1))
              change intOfZ (zAdd q (zOfNat len)) ≤ intOfZ (zAdd p0 n0) at hhi
              simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
                intOfZ_zOfInt] at hhi ⊢
              rw [pg_z1_int] at ⊢
              omega
    · intro m0 b0 p0 n0 hn hbranch hnone m1 hm1
      cases hm1
  exact hP m b p n m' hzeros

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

namespace Genv

private theorem pg_init_zOfNat_nonneg (n : Nat) :
    ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.of_nat n) := by
  change (0 : Int) ≤ intOfZ (ZArith.BinInt.Z.of_nat n)
  simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  change (0 : Int) ≤ Int.ofNat n
  exact Int.ofNat_zero_le n

private theorem pg_init_ofNat_toNat_max (z : Z) :
    ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat z) =
      ZArith.BinInt.Z.max z Z0 := by
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.to_nat,
    intOfZ_zOfInt]
  unfold ZArith.BinInt.Z.max
  split <;> rename_i h
  · have hz : intOfZ z ≤ 0 := by
      change intOfZ z ≤ 0 at h
      exact h
    rw [Int.toNat_of_nonpos hz]
    rfl
  · have hz : 0 ≤ intOfZ z := by
      change ¬ intOfZ z ≤ 0 at h
      omega
    exact Int.toNat_of_nonneg hz

theorem store_init_data_loadbytes : store_init_data_loadbytesStatement := by
  intro F V ge m b p i m' hstore hzero
  cases i with
  | Init_int8 n =>
      exact Mem.loadbytes_store_same Mint8unsigned m b p (Vint n) m' hstore
  | Init_int16 n =>
      exact Mem.loadbytes_store_same Mint16unsigned m b p (Vint n) m' hstore
  | Init_int32 n =>
      exact Mem.loadbytes_store_same Mint32 m b p (Vint n) m' hstore
  | Init_int64 n =>
      exact Mem.loadbytes_store_same Mint64 m b p (Vlong n) m' hstore
  | Init_float32 n =>
      exact Mem.loadbytes_store_same Mfloat32 m b p (Vsingle n) m' hstore
  | Init_float64 n =>
      exact Mem.loadbytes_store_same Mfloat64 m b p (Vfloat n) m' hstore
  | Init_space n =>
      change some m = some m' at hstore
      cases hstore
      have heq := pg_init_ofNat_toNat_max n
      have hz := hzero p (ZArith.BinInt.Z.to_nat n)
        (by change intOfZ p ≤ intOfZ p; omega)
        (by
          change intOfZ (zAdd p
              (ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat n))) ≤
            intOfZ (zAdd p (ZArith.BinInt.Z.max n Z0))
          rw [heq]
          omega)
      change Mem.loadbytes m b p
          (ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat n)) =
        some (List.replicate (ZArith.BinInt.Z.to_nat n)
          (Byte (CompCert4Lean.Lib.Integers.Byte.repr Z0))) at hz
      rw [heq] at hz
      simpa [init_data_size, bytes_of_init_data] using hz
  | Init_addrof id ofs =>
      cases hfind : find_symbol ge id with
      | none => simp [store_init_data, hfind] at hstore
      | some b' =>
          have hs := Mem.loadbytes_store_same Mptr m b p (Vptr b' ofs) m'
            (by simpa [store_init_data, hfind] using hstore)
          have hsize : init_data_size (Init_addrof id ofs) = size_chunk Mptr := rfl
          rw [hsize, hs]
          congr 1
          simp [bytes_of_init_data, hfind, Mptr, encode_val,
            CompCert4Lean.X86_64.Archi.ptr64]

end Genv
end CompCert4Lean.Common.Globalenvs
namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

namespace Genv

private theorem pg_list_loadbytes_unchanged
    (P : block → Z → Prop) (m m' : mem) (b : block) (ofs n : Z)
    (bytes : List memval) (hunch : Mem.unchanged_on P m m')
    (hn : zLe z0 n)
    (hP : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs n) → P b i)
    (hload : Mem.loadbytes m b ofs n = some bytes) :
    Mem.loadbytes m' b ofs n = some bytes := by
  unfold Mem.loadbytes at hload ⊢
  cases hdec : Mem.range_perm_dec m b ofs (zAdd ofs n) Cur Readable with
  | right hnot =>
      rw [hdec] at hload
      change none = some bytes at hload
      cases hload
  | left hrange =>
      have hrange' : Mem.range_perm m' b ofs (zAdd ofs n) Cur Readable := by
        intro i hi
        have hperm := hrange i hi
        exact (hunch.unchanged_on_perm b i Cur Readable (hP i hi)
          (Mem.perm_valid_block m b i Cur Readable hperm)).mp hperm
      cases hdec' : Mem.range_perm_dec m' b ofs (zAdd ofs n) Cur Readable with
      | right hnot => exact False.elim (hnot hrange')
      | left _ =>
          rw [hdec] at hload
          change some (Mem.getN (ZArith.BinInt.Z.to_nat n) ofs
            (PMap.get b m.mem_contents)) = some bytes at hload
          change some (Mem.getN (ZArith.BinInt.Z.to_nat n) ofs
            (PMap.get b m'.mem_contents)) = some bytes
          simp only [Option.some.injEq] at hload ⊢
          rw [← hload]
          apply Mem.getN_exten
          intro i hi
          have hnid : zOfNat (ZArith.BinInt.Z.to_nat n) = n :=
            ZArith.Znat.Z2Nat.id n hn
          have hi' : zLe ofs i ∧ zLt i (zAdd ofs n) := by
            simpa [hnid] using hi
          exact hunch.unchanged_on_contents b i (hP i hi') (hrange i hi')

private theorem pg_list_store_init_data_loadbytes_one
    (F V : Type) (ge : Genv.t F V) (m : mem) (b : block) (p : Z)
    (i : init_data) (m' : mem)
    (hstore : store_init_data ge m b p i = some m')
    (hzero : readbytes_as_zero m b p (init_data_size i)) :
    Mem.loadbytes m' b p (init_data_size i) = some (bytes_of_init_data ge i) := by
  cases i with
  | Init_int8 n =>
      exact Mem.loadbytes_store_same Mint8unsigned m b p (Vint n) m' hstore
  | Init_int16 n =>
      exact Mem.loadbytes_store_same Mint16unsigned m b p (Vint n) m' hstore
  | Init_int32 n =>
      exact Mem.loadbytes_store_same Mint32 m b p (Vint n) m' hstore
  | Init_int64 n =>
      exact Mem.loadbytes_store_same Mint64 m b p (Vlong n) m' hstore
  | Init_float32 n =>
      exact Mem.loadbytes_store_same Mfloat32 m b p (Vsingle n) m' hstore
  | Init_float64 n =>
      exact Mem.loadbytes_store_same Mfloat64 m b p (Vfloat n) m' hstore
  | Init_space n =>
      change some m = some m' at hstore
      cases hstore
      have heq := pg_init_ofNat_toNat_max n
      have hz := hzero p (ZArith.BinInt.Z.to_nat n)
        (by change intOfZ p ≤ intOfZ p; omega)
        (by
          change intOfZ (zAdd p
              (ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat n))) ≤
            intOfZ (zAdd p (ZArith.BinInt.Z.max n Z0))
          rw [heq]
          omega)
      change Mem.loadbytes m b p
          (ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat n)) =
        some (List.replicate (ZArith.BinInt.Z.to_nat n)
          (Byte (CompCert4Lean.Lib.Integers.Byte.repr Z0))) at hz
      rw [heq] at hz
      simpa [init_data_size, bytes_of_init_data] using hz
  | Init_addrof id ofs =>
      cases hfind : Genv.find_symbol ge id with
      | none => simp [store_init_data, hfind] at hstore
      | some b' =>
          have hs := Mem.loadbytes_store_same Mptr m b p (Vptr b' ofs) m' (by
            simpa [store_init_data, hfind] using hstore)
          have hsize : init_data_size (Init_addrof id ofs) = size_chunk Mptr := rfl
          rw [hsize, hs]
          congr 1
          simp [bytes_of_init_data, hfind, Mptr, encode_val,
            CompCert4Lean.X86_64.Archi.ptr64]

private theorem pg_list_store_init_data_loadbytes
    (F V : Type) (ge : Genv.t F V) (b : block) (il : List init_data)
    (m : mem) (p : Z) (m' : mem)
    (hstore : store_init_data_list ge m b p il = some m')
    (hzero : readbytes_as_zero m b p (init_data_list_size il)) :
    Mem.loadbytes m' b p (init_data_list_size il) =
      some (bytes_of_init_data_list ge il) := by
  induction il generalizing m p with
  | nil =>
      change some m = some m' at hstore
      cases hstore
      simpa [init_data_list_size, bytes_of_init_data_list] using
        (Mem.loadbytes_empty m' b p Z0 (by change (0 : Int) ≤ 0; omega))
  | cons i rest ih =>
      change (match store_init_data ge m b p i with
        | none => none
        | some m1 => store_init_data_list ge m1 b
          (zAdd p (init_data_size i)) rest) = some m' at hstore
      cases hhead : store_init_data ge m b p i with
      | none => simp [hhead] at hstore
      | some m1 =>
          have htail : store_init_data_list ge m1 b
              (zAdd p (init_data_size i)) rest = some m' := by
            simpa [hhead] using hstore
          let Phead : block → Z → Prop := fun _ ofs =>
            zLt ofs (zAdd p (init_data_size i))
          have hunchtail : Mem.unchanged_on Phead m1 m' := by
            apply Genv.store_init_data_list_unchanged F V ge Phead b rest m1
              (zAdd p (init_data_size i)) m' htail
            intro ofs hlo hp
            change intOfZ (zAdd p (init_data_size i)) ≤ intOfZ ofs at hlo
            change intOfZ ofs < intOfZ (zAdd p (init_data_size i)) at hp
            omega
          have hzerohead : readbytes_as_zero m b p (init_data_size i) := by
            intro q len hlo hhi
            apply hzero q len hlo
            change intOfZ (zAdd q (zOfNat len)) ≤
              intOfZ (zAdd p (init_data_list_size (i :: rest)))
            change intOfZ (zAdd q (zOfNat len)) ≤
              intOfZ (zAdd p (init_data_size i)) at hhi
            simp only [init_data_list_size, ZArith.BinInt.Z.add,
              intOfZ_zOfInt] at hhi ⊢
            have hrestnonneg := init_data_list_size_pos rest
            change (0 : Int) ≤ intOfZ (init_data_list_size rest) at hrestnonneg
            omega
          have hloadhead1 := pg_list_store_init_data_loadbytes_one F V ge m b p i m1
            hhead hzerohead
          have hloadhead : Mem.loadbytes m' b p (init_data_size i) =
              some (bytes_of_init_data ge i) := by
            apply pg_list_loadbytes_unchanged Phead m1 m' b p
              (init_data_size i) _ hunchtail (init_data_size_pos i)
            · intro ofs hi
              exact hi.2
            · exact hloadhead1
          let Ptail : block → Z → Prop := fun _ ofs =>
            zLe (zAdd p (init_data_size i)) ofs
          have hunchhead : Mem.unchanged_on Ptail m m1 := by
            apply Genv.store_init_data_unchanged F V ge Ptail b i m p m1 hhead
            intro ofs hi hp
            have hupper := hi.2
            change intOfZ ofs < intOfZ (zAdd p (init_data_size i)) at hupper
            change intOfZ (zAdd p (init_data_size i)) ≤ intOfZ ofs at hp
            omega
          have hzerotail : readbytes_as_zero m1 b
              (zAdd p (init_data_size i)) (init_data_list_size rest) := by
            intro q len hlo hhi
            apply pg_list_loadbytes_unchanged Ptail m m1 b q (zOfNat len) _
              hunchhead (pg_init_zOfNat_nonneg len)
            · intro ofs hi
              change intOfZ (zAdd p (init_data_size i)) ≤ intOfZ ofs
              change intOfZ (zAdd p (init_data_size i)) ≤ intOfZ q at hlo
              have hilower := hi.1
              change intOfZ q ≤ intOfZ ofs at hilower
              omega
            · apply hzero q len
              · change intOfZ p ≤ intOfZ q
                change intOfZ (zAdd p (init_data_size i)) ≤ intOfZ q at hlo
                simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at hlo
                have hinonneg := init_data_size_pos i
                change (0 : Int) ≤ intOfZ (init_data_size i) at hinonneg
                omega
              · change intOfZ (zAdd q (zOfNat len)) ≤
                  intOfZ (zAdd p (init_data_list_size (i :: rest)))
                change intOfZ (zAdd q (zOfNat len)) ≤
                  intOfZ (zAdd (zAdd p (init_data_size i))
                    (init_data_list_size rest)) at hhi
                simp only [init_data_list_size, ZArith.BinInt.Z.add,
                  intOfZ_zOfInt] at hhi ⊢
                omega
          have hloadtail := ih m1 (zAdd p (init_data_size i)) htail hzerotail
          have hcat := Mem.loadbytes_concat m' b p (init_data_size i)
            (init_data_list_size rest) (bytes_of_init_data ge i)
            (bytes_of_init_data_list ge rest) hloadhead hloadtail
            (init_data_size_pos i) (init_data_list_size_pos rest)
          simpa [init_data_list_size, bytes_of_init_data_list] using hcat

theorem store_init_data_list_loadbytes : store_init_data_list_loadbytesStatement := by
  exact pg_list_store_init_data_loadbytes

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory

namespace Genv

theorem store_zeros_read_as_zero : store_zeros_read_as_zeroStatement := by
  intro m b p n m' hstore chunk q hlo hhi halign
  have hbytes := store_zeros_loadbytes m b p n m' hstore q
    (size_chunk_nat chunk) hlo (by simpa only [← size_chunk_conv chunk] using hhi)
  have hload := Mem.loadbytes_load chunk m' b q _
    (by simpa only [← size_chunk_conv chunk] using hbytes) halign
  rw [hload]
  cases chunk <;> rfl

end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers

namespace Genv

private theorem pg_charact_repr_pos (bits : Nat) (p : positive) :
    intOfZ (WordCore.unsigned (WordCore.repr bits (Zpos p))) =
      (posToNat p % (2 ^ bits) : Nat) := by
  change intOfZ (ZArith.BinInt.Z.of_nat _) = _
  rw [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  apply congrArg Int.ofNat
  change _ % (2 ^ bits) = posToNat p % (2 ^ bits)
  congr 1
  induction p with
  | xH => rfl
  | xI p ih => change 2 * _ + 1 = 2 * _ + 1; rw [ih]
  | xO p ih => change 2 * _ = 2 * _; rw [ih]

private theorem pg_charact_repr_nonneg (bits : Nat) (z : Z)
    (hz : 0 ≤ intOfZ z) :
    intOfZ (WordCore.unsigned (WordCore.repr bits z)) =
      intOfZ z % (2 : Int) ^ bits := by
  cases z with
  | Z0 => change (0 : Int) = 0 % (2 : Int) ^ bits; simp
  | Zpos p =>
      rw [pg_charact_repr_pos]
      simp only [intOfZ, Int.natCast_emod, Int.natCast_pow]
      rfl
  | Zneg p =>
      have hp := posToNat_positive p
      change 0 ≤ -(Int.ofNat (posToNat p)) at hz
      simp only [Int.ofNat_eq_natCast] at hz
      omega

private theorem pg_charact_div256 (z : Z) :
    intOfZ (ZArith.BinInt.Z.div z (zOfNat 256)) = intOfZ z / 256 := by
  unfold ZArith.BinInt.Z.div
  rw [intOfZ_zOfInt]
  rfl

private theorem pg_charact_bytes_step (n : Nat) (z : Z) (hz : 0 ≤ intOfZ z) :
    intOfZ (int_of_bytes (bytes_of_int (n + 1) z)) =
      intOfZ z % 256 +
        intOfZ (int_of_bytes (bytes_of_int n
          (ZArith.BinInt.Z.div z (zOfNat 256)))) * 256 := by
  simp only [bytes_of_int, int_of_bytes, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  change intOfZ (Byte.unsigned (Byte.repr z)) +
    intOfZ (int_of_bytes (bytes_of_int n (ZArith.BinInt.Z.div z (zOfNat 256)))) * 256 = _
  rw [show intOfZ (Byte.unsigned (Byte.repr z)) = intOfZ z % 256 from
    pg_charact_repr_nonneg 8 z hz]

private theorem pg_charact_bytes_bounded (n : Nat) (z : Z)
    (hz : 0 ≤ intOfZ z) (hbound : intOfZ z < (256 : Int) ^ n) :
    intOfZ (int_of_bytes (bytes_of_int n z)) = intOfZ z := by
  induction n generalizing z with
  | zero =>
      change (0 : Int) = intOfZ z
      simp only [Int.pow_zero] at hbound
      omega
  | succ n ih =>
      rw [pg_charact_bytes_step n z hz]
      rw [ih]
      · rw [pg_charact_div256]
        exact Int.emod_add_ediv_mul _ _
      · rw [pg_charact_div256]
        omega
      · rw [pg_charact_div256]
        rw [Int.pow_succ] at hbound
        omega

private theorem pg_charact_proj_bytes (bl : List byte) :
    proj_bytes (inj_bytes bl) = some bl := by
  induction bl with
  | nil => rfl
  | cons b bl ih =>
      change (match proj_bytes (inj_bytes bl) with
        | none => none | some l => some (b :: l)) = some (b :: bl)
      rw [ih]

private theorem pg_charact_word_nonneg {bits : Nat} (w : WordCore.Word bits) :
    0 ≤ intOfZ (WordCore.unsigned w) := by
  have h := w.intrange.1
  change (-1 : Int) < intOfZ (WordCore.unsigned w) at h
  omega

private theorem pg_charact_decode_word (bits n : Nat) (w : WordCore.Word bits)
    (hbound : intOfZ (WordCore.unsigned w) < (256 : Int) ^ n)
    (hbound' : intOfZ (WordCore.unsigned w) < (2 : Int) ^ bits) :
    WordCore.repr bits (decode_int (encode_int n (WordCore.unsigned w))) = w := by
  have hn := pg_charact_word_nonneg w
  have hdec : decode_int (encode_int n (WordCore.unsigned w)) = WordCore.unsigned w := by
    apply intOfZ_injective
    exact pg_charact_bytes_bounded n _ hn hbound
  rw [hdec]
  apply WordCore.ext
  apply intOfZ_injective
  change intOfZ (WordCore.unsigned (WordCore.repr bits (WordCore.unsigned w))) = _
  rw [pg_charact_repr_nonneg bits _ hn]
  exact Int.emod_eq_of_lt hn hbound'

private theorem pg_charact_decode_int32 (w : int) :
    CompCert4Lean.Lib.Integers.Int.repr (decode_int (encode_int 4 (Int.unsigned w))) = w := by
  apply pg_charact_decode_word 32 4 w
  all_goals exact w.intrange.2

private theorem pg_charact_decode_int64 (w : int64) :
    Int64.repr (decode_int (encode_int 8 (Int64.unsigned w))) = w := by
  apply pg_charact_decode_word 64 8 w
  all_goals exact w.intrange.2

private theorem pg_charact_decode_byte (z : Z) (hz : 0 ≤ intOfZ z) :
    intOfZ (decode_int (encode_int 1 z)) = intOfZ z % 256 := by
  change intOfZ (int_of_bytes (bytes_of_int (0 + 1) z)) = _
  rw [pg_charact_bytes_step 0 z hz]
  change intOfZ z % 256 + 0 * 256 = _
  omega

private theorem pg_charact_decode_short (z : Z) (hz : 0 ≤ intOfZ z) :
    intOfZ (decode_int (encode_int 2 z)) = intOfZ z % 65536 := by
  change intOfZ (int_of_bytes (bytes_of_int (1 + 1) z)) = _
  rw [pg_charact_bytes_step 1 z hz]
  have hd : 0 ≤ intOfZ (ZArith.BinInt.Z.div z (zOfNat 256)) := by
    rw [pg_charact_div256]
    omega
  rw [pg_charact_bytes_step 0 _ hd, pg_charact_div256]
  change intOfZ z % 256 + (intOfZ z / 256 % 256 + 0 * 256) * 256 = _
  omega

private theorem pg_charact_zero_ext8 (w : int) :
    Int.zero_ext (zOfNat 8) (CompCert4Lean.Lib.Integers.Int.repr (decode_int (encode_int 1 (Int.unsigned w)))) =
      Int.zero_ext (zOfNat 8) w := by
  have hn := pg_charact_word_nonneg w
  have hd := pg_charact_decode_byte (Int.unsigned w) hn
  have hdn : 0 ≤ intOfZ (decode_int (encode_int 1 (Int.unsigned w))) := by
    rw [hd]
    omega
  apply WordCore.ext
  change Int.unsigned (Int.zero_ext (zOfNat 8) _) = Int.unsigned (Int.zero_ext (zOfNat 8) w)
  rw [Int.zero_ext_mod_proof_api _ _ (by change (0 : Int) ≤ 8 ∧ (8 : Int) < 32; omega),
    Int.zero_ext_mod_proof_api _ _ (by change (0 : Int) ≤ 8 ∧ (8 : Int) < 32; omega)]
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.modulo, intOfZ_zOfInt]
  change intOfZ (Int.unsigned (CompCert4Lean.Lib.Integers.Int.repr (decode_int (encode_int 1 (Int.unsigned w))))) % 256 =
    intOfZ (Int.unsigned w) % 256
  change intOfZ (WordCore.unsigned (WordCore.repr 32 _)) % _ = _
  rw [pg_charact_repr_nonneg 32 _ hdn, hd]
  omega

private theorem pg_charact_zero_ext16 (w : int) :
    Int.zero_ext (zOfNat 16) (CompCert4Lean.Lib.Integers.Int.repr (decode_int (encode_int 2 (Int.unsigned w)))) =
      Int.zero_ext (zOfNat 16) w := by
  have hn := pg_charact_word_nonneg w
  have hd := pg_charact_decode_short (Int.unsigned w) hn
  have hdn : 0 ≤ intOfZ (decode_int (encode_int 2 (Int.unsigned w))) := by
    rw [hd]
    omega
  apply WordCore.ext
  change Int.unsigned (Int.zero_ext (zOfNat 16) _) = Int.unsigned (Int.zero_ext (zOfNat 16) w)
  rw [Int.zero_ext_mod_proof_api _ _ (by change (0 : Int) ≤ 16 ∧ (16 : Int) < 32; omega),
    Int.zero_ext_mod_proof_api _ _ (by change (0 : Int) ≤ 16 ∧ (16 : Int) < 32; omega)]
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.modulo, intOfZ_zOfInt]
  change intOfZ (Int.unsigned (CompCert4Lean.Lib.Integers.Int.repr (decode_int (encode_int 2 (Int.unsigned w))))) % 65536 =
    intOfZ (Int.unsigned w) % 65536
  change intOfZ (WordCore.unsigned (WordCore.repr 32 _)) % _ = _
  rw [pg_charact_repr_nonneg 32 _ hdn, hd]
  omega

private theorem pg_charact_decode_int8_val (w : int) :
    decode_val Mint8unsigned (encode_val Mint8unsigned (Vint w)) =
      Val.zero_ext (zOfNat 8) (Vint w) := by
  simp only [encode_val, decode_val, pg_charact_proj_bytes]
  exact congrArg Vint (pg_charact_zero_ext8 w)

private theorem pg_charact_decode_int16_val (w : int) :
    decode_val Mint16unsigned (encode_val Mint16unsigned (Vint w)) =
      Val.zero_ext (zOfNat 16) (Vint w) := by
  simp only [encode_val, decode_val, pg_charact_proj_bytes]
  exact congrArg Vint (pg_charact_zero_ext16 w)

private theorem pg_charact_decode_int32_val (w : int) :
    decode_val Mint32 (encode_val Mint32 (Vint w)) = Vint w := by
  simp only [encode_val, decode_val, pg_charact_proj_bytes]
  exact congrArg Vint (pg_charact_decode_int32 w)

private theorem pg_charact_decode_int64_val (w : int64) :
    decode_val Mint64 (encode_val Mint64 (Vlong w)) = Vlong w := by
  simp only [encode_val, decode_val, pg_charact_proj_bytes]
  exact congrArg Vlong (pg_charact_decode_int64 w)

private theorem pg_charact_decode_float32_val (w : CompCert4Lean.Lib.Floats.float32) :
    decode_val Mfloat32 (encode_val Mfloat32 (Vsingle w)) = Vsingle w := by
  simp only [encode_val, decode_val, pg_charact_proj_bytes]
  change Vsingle (CompCert4Lean.Lib.Floats.Float32.of_bits (CompCert4Lean.Lib.Integers.Int.repr
    (decode_int (encode_int 4 (Int.unsigned (CompCert4Lean.Lib.Floats.Float32.to_bits w)))))) = _
  rw [pg_charact_decode_int32, CompCert4Lean.Lib.Floats.Float32.of_to_bits]

private theorem pg_charact_decode_float64_val (w : CompCert4Lean.Lib.Floats.float) :
    decode_val Mfloat64 (encode_val Mfloat64 (Vfloat w)) = Vfloat w := by
  simp only [encode_val, decode_val, pg_charact_proj_bytes]
  change Vfloat (CompCert4Lean.Lib.Floats.Float.of_bits (Int64.repr
    (decode_int (encode_int 8 (Int64.unsigned (CompCert4Lean.Lib.Floats.Float.to_bits w)))))) = _
  rw [pg_charact_decode_int64, CompCert4Lean.Lib.Floats.Float.of_to_bits]

private theorem pg_charact_decode_ptr_val (b : block) (ofs : ptrofs) :
    decode_val Mptr (encode_val Mptr (Vptr b ofs)) = Vptr b ofs := by
  simp [Mptr, CompCert4Lean.X86_64.Archi.ptr64, encode_val, decode_val,
    inj_value, inj_value_rec, size_quantity_nat, proj_bytes, proj_value,
    check_value, Val.eq, quantity_eq, Val.load_result]
  rfl

private theorem pg_charact_head_load {F V : Type} (ge : t F V)
    (chunk : memory_chunk) (v result : val) (m m1 m' : mem)
    (b : block) (p : Z) (il : List init_data)
    (hstore : Mem.store chunk m b p v = some m1)
    (htail : store_init_data_list ge m1 b (zAdd p (size_chunk chunk)) il = some m')
    (hdecode : decode_val chunk (encode_val chunk v) = result) :
    Mem.load chunk m' b p = some result := by
  have hbytes := Mem.loadbytes_store_same chunk m b p v m1 hstore
  have halign := (Mem.store_valid_access_3 chunk m b p v m1 hstore).2
  have hload := Mem.loadbytes_load chunk m1 b p _ hbytes halign
  rw [hdecode] at hload
  let P : block → Z → Prop := fun _ q => zLt q (zAdd p (size_chunk chunk))
  apply pg_load_unchanged_on P m1 m' chunk b p result
  · apply store_init_data_list_unchanged F V ge P b il m1
      (zAdd p (size_chunk chunk)) m' htail
    intro q hlo hP
    change intOfZ (zAdd p (size_chunk chunk)) ≤ intOfZ q at hlo
    change intOfZ q < intOfZ (zAdd p (size_chunk chunk)) at hP
    omega
  · intro q hq
    exact hq.2
  · exact hload

theorem store_init_data_list_charact : store_init_data_list_charactStatement := by
  intro F V ge b il
  induction il with
  | nil => intro m p m' hstore hzero; trivial
  | cons i rest ih =>
      intro m p m' hstore hzero
      cases hhead : store_init_data ge m b p i with
      | none => simp [store_init_data_list, hhead] at hstore
      | some m1 =>
          have htail : store_init_data_list ge m1 b
              (zAdd p (init_data_size i)) rest = some m' := by
            simpa only [store_init_data_list, hhead] using hstore
          let Ptail : block → Z → Prop := fun _ q =>
            zLe (zAdd p (init_data_size i)) q
          have hzero_before : read_as_zero m b (zAdd p (init_data_size i))
              (init_data_list_size rest) := by
            intro chunk q hlo hhi halign
            apply hzero chunk q _ _ halign
            · change intOfZ p ≤ intOfZ q
              change intOfZ (zAdd p (init_data_size i)) ≤ intOfZ q at hlo
              have hnonneg := init_data_size_pos i
              change (0 : Int) ≤ intOfZ (init_data_size i) at hnonneg
              simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at hlo
              omega
            · change intOfZ (zAdd q (size_chunk chunk)) ≤
                intOfZ (zAdd p (init_data_list_size (i :: rest)))
              change intOfZ (zAdd q (size_chunk chunk)) ≤
                intOfZ (zAdd (zAdd p (init_data_size i)) (init_data_list_size rest)) at hhi
              simp only [init_data_list_size, ZArith.BinInt.Z.add,
                intOfZ_zOfInt] at hhi ⊢
              omega
          have hunch_head : Mem.unchanged_on Ptail m m1 := by
            apply store_init_data_unchanged F V ge Ptail b i m p m1 hhead
            intro q hq hP
            have hupper := hq.2
            change intOfZ q < intOfZ (zAdd p (init_data_size i)) at hupper
            change intOfZ (zAdd p (init_data_size i)) ≤ intOfZ q at hP
            omega
          have hzero_tail : read_as_zero m1 b (zAdd p (init_data_size i))
              (init_data_list_size rest) := by
            apply read_as_zero_unchanged Ptail m b (zAdd p (init_data_size i))
              (init_data_list_size rest) m1 hzero_before hunch_head
            intro q hq
            exact hq.1
          have hresult := ih m1 (zAdd p (init_data_size i)) m' htail hzero_tail
          cases i with
          | Init_int8 n =>
              exact ⟨pg_charact_head_load ge Mint8unsigned (Vint n) _ m m1 m' b p rest
                hhead htail (pg_charact_decode_int8_val n), hresult⟩
          | Init_int16 n =>
              exact ⟨pg_charact_head_load ge Mint16unsigned (Vint n) _ m m1 m' b p rest
                hhead htail (pg_charact_decode_int16_val n), hresult⟩
          | Init_int32 n =>
              exact ⟨pg_charact_head_load ge Mint32 (Vint n) _ m m1 m' b p rest
                hhead htail (pg_charact_decode_int32_val n), hresult⟩
          | Init_int64 n =>
              exact ⟨pg_charact_head_load ge Mint64 (Vlong n) _ m m1 m' b p rest
                hhead htail (pg_charact_decode_int64_val n), hresult⟩
          | Init_float32 n =>
              exact ⟨pg_charact_head_load ge Mfloat32 (Vsingle n) _ m m1 m' b p rest
                hhead htail (pg_charact_decode_float32_val n), hresult⟩
          | Init_float64 n =>
              exact ⟨pg_charact_head_load ge Mfloat64 (Vfloat n) _ m m1 m' b p rest
                hhead htail (pg_charact_decode_float64_val n), hresult⟩
          | Init_addrof symb ofs =>
              cases hsym : find_symbol ge symb with
              | none => simp [store_init_data, hsym] at hhead
              | some b' =>
                  have hs : Mem.store Mptr m b p (Vptr b' ofs) = some m1 := by
                    simpa [store_init_data, hsym] using hhead
                  exact ⟨⟨b', hsym, pg_charact_head_load ge Mptr (Vptr b' ofs) _
                    m m1 m' b p rest hs htail (pg_charact_decode_ptr_val b' ofs)⟩, hresult⟩
          | Init_space n =>
              have hm : m = m1 := Option.some.inj hhead
              subst m1
              refine ⟨?_, hresult⟩
              have hn : intOfZ n ≤ intOfZ (init_data_size (Init_space n)) := by
                change intOfZ n ≤ intOfZ (zMax n z0)
                unfold zMax ZArith.BinInt.Z.max
                split <;> rename_i h
                · change intOfZ n ≤ 0 at h
                  exact h
                · omega
              let Phead : block → Z → Prop := fun _ q =>
                zLt q (zAdd p (init_data_size (Init_space n)))
              apply read_as_zero_unchanged Phead m b p n m'
              · intro chunk q hlo hhi halign
                apply hzero chunk q hlo _ halign
                have hnonneg := init_data_list_size_pos rest
                change (0 : Int) ≤ intOfZ (init_data_list_size rest) at hnonneg
                change intOfZ (zAdd q (size_chunk chunk)) ≤
                  intOfZ (zAdd p (init_data_list_size (Init_space n :: rest)))
                change intOfZ (zAdd q (size_chunk chunk)) ≤ intOfZ (zAdd p n) at hhi
                simp only [init_data_list_size, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hhi ⊢
                omega
              · apply store_init_data_list_unchanged F V ge Phead b rest m
                  (zAdd p (init_data_size (Init_space n))) m' htail
                intro q hlo hP
                change intOfZ (zAdd p (init_data_size (Init_space n))) ≤ intOfZ q at hlo
                change intOfZ q < intOfZ (zAdd p (init_data_size (Init_space n))) at hP
                omega
              · intro q hq
                have hupper := hq.2
                change intOfZ q < intOfZ (zAdd p n) at hupper
                change intOfZ q < intOfZ (zAdd p (init_data_size (Init_space n)))
                simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at hupper ⊢
                omega

end Genv
end CompCert4Lean.Common.Globalenvs


namespace CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers
namespace Genv

private theorem pg_alloc_nonempty_order_eq (p : permission)
    (h : perm_order Memtype.Nonempty p) : p = Memtype.Nonempty := by
  cases h <;> rfl

private theorem pg_load_store_invariant
    (F V : Type) (ge : t F V) (m m' : mem) (b : block)
    (hunch : Mem.unchanged_on (fun _ _ => True) m m')
    (_hvalid : Mem.valid_block m b) :
    ∀ il p, load_store_init_data ge m b p il →
      load_store_init_data ge m' b p il := by
  intro il
  induction il with
  | nil => intro p h; trivial
  | cons i rest ih =>
      intro p h
      cases i with
      | Init_int8 n =>
          rcases h with ⟨hh, ht⟩
          constructor
          · exact pg_load_unchanged_on (fun _ _ => True) m m' Mint8unsigned b p _ hunch
              (by intro _ _; trivial) hh
          · exact ih (zAdd p (zOfNat 1)) ht
      | Init_int16 n =>
          rcases h with ⟨hh, ht⟩
          constructor
          · exact pg_load_unchanged_on (fun _ _ => True) m m' Mint16unsigned b p _ hunch
              (by intro _ _; trivial) hh
          · exact ih (zAdd p (zOfNat 2)) ht
      | Init_int32 n =>
          rcases h with ⟨hh, ht⟩
          constructor
          · exact pg_load_unchanged_on (fun _ _ => True) m m' Mint32 b p _ hunch
              (by intro _ _; trivial) hh
          · exact ih (zAdd p (zOfNat 4)) ht
      | Init_int64 n =>
          rcases h with ⟨hh, ht⟩
          constructor
          · exact pg_load_unchanged_on (fun _ _ => True) m m' Mint64 b p _ hunch
              (by intro _ _; trivial) hh
          · exact ih (zAdd p (zOfNat 8)) ht
      | Init_float32 n =>
          rcases h with ⟨hh, ht⟩
          constructor
          · exact pg_load_unchanged_on (fun _ _ => True) m m' Mfloat32 b p _ hunch
              (by intro _ _; trivial) hh
          · exact ih (zAdd p (zOfNat 4)) ht
      | Init_float64 n =>
          rcases h with ⟨hh, ht⟩
          constructor
          · exact pg_load_unchanged_on (fun _ _ => True) m m' Mfloat64 b p _ hunch
              (by intro _ _; trivial) hh
          · exact ih (zAdd p (zOfNat 8)) ht
      | Init_addrof symb ofs =>
          rcases h with ⟨⟨b', hs, hh⟩, ht⟩
          constructor
          · exact ⟨b', hs, pg_load_unchanged_on (fun _ _ => True) m m' Mptr b p _ hunch
              (by intro _ _; trivial) hh⟩
          · exact ih (zAdd p (size_chunk Mptr)) ht
      | Init_space n =>
          rcases h with ⟨hz, ht⟩
          constructor
          · intro chunk q hlo hhi halign
            exact pg_load_unchanged_on (fun _ _ => True) m m' chunk b q _ hunch
              (by intro _ _; trivial) (hz chunk q hlo hhi halign)
          · exact ih (zAdd p (zMax n z0)) ht


theorem alloc_global_initialized
    (F V : Type) (ge g : t F V) (m : mem) (id : ident)
    (gd : globdef F V) (m' : mem)
    (hnext : g.genv_next = m.nextblock)
    (halloc : alloc_global ge m (id, gd) = some m')
    (hglobals : globals_initialized ge g m) :
    globals_initialized ge (add_global g (id, gd)) m' ∧
      (add_global g (id, gd)).genv_next = m'.nextblock := by
  have hnextalloc := alloc_global_nextblock F V ge (id, gd) m m' halloc
  constructor
  · intro b gd' hfind
    unfold find_def at hfind
    change PTree.get b (PTree.set g.genv_next gd g.genv_defs) = some gd' at hfind
    rw [PTree.gsspec_proof (show positive from b)
      (show positive from g.genv_next) gd g.genv_defs] at hfind
    cases heq : peq (show positive from b) (show positive from g.genv_next) with
    | left hbeq =>
        rw [heq] at hfind
        cases Option.some.inj hfind
        have hb : b = g.genv_next := hbeq
        cases hb
        cases gd with
        | Gfun f =>
            unfold alloc_global at halloc
            cases ha : Mem.alloc m z0 z1 with
            | mk m1 bnew =>
                have hdrop : Mem.drop_perm m1 bnew z0 z1 Memtype.Nonempty = some m' := by
                  simpa [ha] using halloc
                have hbnew := Mem.alloc_result m z0 z1 m1 bnew ha
                have hgb : g.genv_next = bnew := hnext.trans hbnew.symm
                rw [hgb]
                constructor
                · exact Mem.perm_drop_1 m1 bnew z0 z1 Nonempty m' hdrop z0 Cur
                    (by constructor <;> change (0:Int) ≤ 0 <;> omega)
                · intro ofs k prm hp
                  have hp1 := Mem.perm_drop_4 m1 bnew z0 z1 Nonempty m' hdrop
                    bnew ofs k prm hp
                  have hbounds := Mem.perm_alloc_3 m z0 z1 m1 bnew ha ofs k prm hp1
                  have hord := Mem.perm_drop_2 m1 bnew z0 z1 Nonempty m' hdrop
                    ofs k prm hbounds hp
                  constructor
                  · apply intOfZ_injective
                    have hlo := hbounds.1
                    have hhi := hbounds.2
                    change (0 : Int) ≤ intOfZ ofs at hlo
                    change intOfZ ofs < 1 at hhi
                    change intOfZ ofs = 0
                    omega
                  · exact pg_alloc_nonempty_order_eq prm hord
        | Gvar v =>
            unfold alloc_global at halloc
            cases ha : Mem.alloc m z0 (init_data_list_size v.gvar_init) with
            | mk m1 bnew =>
                cases hz : store_zeros m1 bnew z0
                    (init_data_list_size v.gvar_init) with
                | none => simp [ha, hz] at halloc
                | some m2 =>
                    cases hl : store_init_data_list ge m2 bnew z0 v.gvar_init with
                    | none => simp [ha, hz, hl] at halloc
                    | some m3 =>
                        have hdrop : Mem.drop_perm m3 bnew z0
                            (init_data_list_size v.gvar_init) (perm_globvar v) = some m' := by
                          simpa [ha, hz, hl] using halloc
                        have hbnew := Mem.alloc_result m z0
                          (init_data_list_size v.gvar_init) m1 bnew ha
                        have hgb : g.genv_next = bnew := hnext.trans hbnew.symm
                        rw [hgb]
                        constructor
                        · intro ofs hofs
                          exact Mem.perm_drop_1 m3 bnew z0
                            (init_data_list_size v.gvar_init) (perm_globvar v) m' hdrop ofs Cur hofs
                        constructor
                        · intro ofs k prm hp
                          have hp3 := Mem.perm_drop_4 m3 bnew z0
                            (init_data_list_size v.gvar_init) (perm_globvar v) m' hdrop
                            bnew ofs k prm hp
                          have hp2 := (store_init_data_list_perm F V ge k prm
                            bnew ofs v.gvar_init bnew m2 z0 m3 hl).mpr hp3
                          have hp1 := (store_zeros_perm k prm bnew ofs m1 bnew z0
                            (init_data_list_size v.gvar_init) m2 hz).mpr hp2
                          have hbounds := Mem.perm_alloc_3 m z0
                            (init_data_list_size v.gvar_init) m1 bnew ha ofs k prm hp1
                          exact ⟨hbounds, Mem.perm_drop_2 m3 bnew z0
                            (init_data_list_size v.gvar_init) (perm_globvar v) m' hdrop
                            ofs k prm hbounds hp⟩
                        constructor
                        · intro hnonvol
                          have hchar := store_init_data_list_charact F V ge bnew
                            v.gvar_init m2 z0 m3 hl
                            (store_zeros_read_as_zero m1 bnew z0
                              (init_data_list_size v.gvar_init) m2 hz)
                          apply load_store_init_data_invariant F V ge m3 m' bnew
                            (fun chunk ofs => by
                              exact Mem.load_drop m3 bnew z0
                                (init_data_list_size v.gvar_init) (perm_globvar v) m' hdrop
                                chunk bnew ofs
                                (Or.inr (Or.inr (Or.inr (by
                                  unfold perm_globvar
                                  rw [hnonvol]
                                  cases v.gvar_readonly <;> constructor)))))
                            v.gvar_init z0 hchar
                        · intro hnonvol
                          have hload := store_init_data_list_loadbytes F V ge bnew
                            v.gvar_init m2 z0 m3 hl
                            (store_zeros_loadbytes m1 bnew z0
                              (init_data_list_size v.gvar_init) m2 hz)
                          have hread : perm_order (perm_globvar v) Readable := by
                            unfold perm_globvar
                            rw [hnonvol]
                            cases v.gvar_readonly <;> constructor
                          exact Mem.loadbytes_drop m3 bnew z0
                            (init_data_list_size v.gvar_init) (perm_globvar v) m' hdrop
                            bnew z0 (init_data_list_size v.gvar_init)
                            (Or.inr (Or.inr (Or.inr hread))) |>.trans hload
    | right hbne =>
        rw [heq] at hfind
        have hold : find_def g b = some gd' := hfind
        have hvalid : Mem.valid_block m b := by
          change Plt b m.nextblock
          rw [← hnext]
          exact g.genv_defs_range b hold
        have hunch := alloc_global_unchanged F V ge
          (fun _ _ => True) m id gd m' halloc
        have holdprops := hglobals b gd' hold
        cases gd' with
        | Gfun f =>
            constructor
            · exact (hunch.unchanged_on_perm b z0 Cur Memtype.Nonempty trivial hvalid).mp
                holdprops.1
            · intro ofs k prm hp
              apply holdprops.2 ofs k prm
              exact (hunch.unchanged_on_perm b ofs k prm trivial hvalid).mpr hp
        | Gvar v =>
            constructor
            · intro ofs hi
              exact (hunch.unchanged_on_perm b ofs Cur (perm_globvar v)
                trivial hvalid).mp (holdprops.1 ofs hi)
            constructor
            · intro ofs k prm hp
              apply holdprops.2.1 ofs k prm
              exact (hunch.unchanged_on_perm b ofs k prm trivial hvalid).mpr hp
            constructor
            · intro hnonvol
              exact pg_load_store_invariant F V ge m m' b hunch hvalid
                v.gvar_init z0 (holdprops.2.2.1 hnonvol)
            · intro hnonvol
              exact pg_store_zeros_loadbytes_unchanged (fun _ _ => True) m m' b z0
                (init_data_list_size v.gvar_init) _ hunch
                (init_data_list_size_pos v.gvar_init)
                (by intro _ _; trivial)
                (holdprops.2.2.2 hnonvol)
  · change PArith.BinPos.Pos.succ g.genv_next = m'.nextblock
    rw [hnext]
    exact hnextalloc.symm


end Genv
end CompCert4Lean.Common.Globalenvs

namespace CompCert4Lean.Common.Globalenvs
namespace Genv

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

theorem alloc_globals_initialized : alloc_globals_initializedStatement := by
  intro F V ge gl g m m' halloc hnext hglobals
  induction gl generalizing g m with
  | nil =>
      change some m = some m' at halloc
      cases halloc
      exact hglobals
  | cons idg rest ih =>
      rcases idg with ⟨id, gd⟩
      change (match alloc_global ge m (id, gd) with
        | none => none
        | some m1 => alloc_globals ge m1 rest) = some m' at halloc
      cases hstep : alloc_global ge m (id, gd) with
      | none => simp [hstep] at halloc
      | some m1 =>
          have hrest : alloc_globals ge m1 rest = some m' := by
            simpa [hstep] using halloc
          have hone := alloc_global_initialized F V ge g m id gd m1 hnext hstep hglobals
          rcases hone with ⟨hglobals', hnext'⟩
          exact ih (g := add_global g (id, gd)) (m := m1)
            hrest hnext' hglobals'

end Genv
end CompCert4Lean.Common.Globalenvs
