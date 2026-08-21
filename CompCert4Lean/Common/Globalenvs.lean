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
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zMax := ZArith.BinInt.Z.max
private abbrev zToNat := ZArith.BinInt.Z.to_nat
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zDivide := ZArith.BinInt.Z.divide
private abbrev posSucc := PArith.BinPos.Pos.succ

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
  nextblock : block
  find_symbol_injective :
    ∀ id1 id2 b, find_symbol id1 = some b → find_symbol id2 = some b → id1 = id2
  public_symbol_exists :
    ∀ id, public_symbol id = true → ∃ b, find_symbol id = some b
  find_symbol_below :
    ∀ id b, find_symbol id = some b → Plt b nextblock

export t (find_symbol public_symbol invert_symbol block_is_volatile nextblock
  find_symbol_injective public_symbol_exists find_symbol_below)

def invert_find_symbol (ge : t) : Prop :=
  ∀ id b, ge.invert_symbol b = some id → ge.find_symbol id = some b

def find_invert_symbol (ge : t) : Prop :=
  ∀ id b, ge.find_symbol id = some b → ge.invert_symbol b = some id

def block_is_volatile_below (ge : t) : Prop :=
  ∀ b, ge.block_is_volatile b = true → Plt b ge.nextblock

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
  genv_next : block
  genv_symb_range : ∀ id b, PTree.get id genv_symb = some b → Plt b genv_next
  genv_defs_range : ∀ b g, PTree.get b genv_defs = some g → Plt b genv_next
  genv_vars_inj : ∀ id1 id2 b,
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
        exact pltTransSucc (ge.genv_symb_range id' b hold)
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
        exact pltTransSucc (ge.genv_defs_range b gd' hold)
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
          have hrange := ge.genv_symb_range id2 next hold
          exact False.elim (Nat.lt_irrefl _ hrange)
      · have ho1 := ptreeGetSetOther (show positive from id1) (show positive from id)
            next ge.genv_symb h1id
        have hold1 : PTree.get id1 ge.genv_symb = some b := ho1.symm.trans h1
        by_cases h2id : id2 = id
        · subst id2
          have hs := ptreeGetSetSame (show positive from id) next ge.genv_symb
          have hb : some next = some b := hs.symm.trans h2
          cases Option.some.inj hb
          have hrange := ge.genv_symb_range id1 next hold1
          exact False.elim (Nat.lt_irrefl _ hrange)
        · have ho2 := ptreeGetSetOther (show positive from id2) (show positive from id)
              next ge.genv_symb h2id
          have hold2 : PTree.get id2 ge.genv_symb = some b := ho2.symm.trans h2
          exact ge.genv_vars_inj id1 id2 b hold1 hold2 }

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
    public_symbol_exists := by
      intro id h
      unfold public_symbol at h
      cases hfs : find_symbol ge id with
      | none => simp [hfs] at h
      | some b => exact ⟨b, rfl⟩
    find_symbol_below := by
      intro id b h
      exact ge.genv_symb_range id b h }

private def storeZerosNat : Nat → mem → block → Z → Option mem
  | 0, m, _, _ => some m
  | n + 1, m, b, p =>
      match Mem.store Mint8unsigned m b p Vzero with
      | none => none
      | some m' => storeZerosNat n m' b (zAdd p z1)

def store_zeros (m : mem) (b : block) (p n : Z) : Option mem :=
  storeZerosNat (zToNat n) m b p

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
  mge_next : ge2.genv_next = ge1.genv_next
  mge_symb : ∀ id, PTree.get id ge2.genv_symb = PTree.get id ge1.genv_symb
  mge_defs : ∀ b, option_rel R (PTree.get b ge1.genv_defs) (PTree.get b ge2.genv_defs)

export match_genvs (mge_next mge_symb mge_defs)

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
  ∀ (F V : Type) (ge : t F V) (thr : block) (m : mem) (b : block)
    (p : Z) (id : init_data) (m' : mem),
    Mem.inject_neutral thr m → Plt b thr →
    store_init_data ge m b p id = some m' → Mem.inject_neutral thr m'

def store_init_data_list_neutralStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (thr : block) (b : block)
    (idl : List init_data) (m : mem) (p : Z) (m' : mem),
    Mem.inject_neutral thr m → Plt b thr →
    store_init_data_list ge m b p idl = some m' → Mem.inject_neutral thr m'

def alloc_global_neutralStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (thr : block) (idg : ident × globdef F V)
    (m m' : mem),
    alloc_global ge m idg = some m' →
    Mem.inject_neutral thr m → Plt m.nextblock thr → Mem.inject_neutral thr m'

def advance_next_leStatement : Prop :=
  ∀ (F V : Type) (gl : List (ident × globdef F V)) (x : positive),
    Ple x (advance_next gl x)

def alloc_globals_neutralStatement : Prop :=
  ∀ (F V : Type) (ge : t F V) (thr : block)
    (gl : List (ident × globdef F V)) (m m' : mem),
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
  ∀ (C F1 V1 F2 V2 : Type) [Linker C] [Linker F1] [Linker V1]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
      match_genvs (match_globdef match_fundef match_varinfo ctx) (globalenv p) (globalenv tp)

def find_def_match_2Statement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C] [Linker F1] [Linker V1]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ b, option_rel (match_globdef match_fundef match_varinfo ctx)
      (find_def (globalenv p) b) (find_def (globalenv tp) b)

def find_def_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C] [Linker F1] [Linker V1]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ b g, find_def (globalenv p) b = some g →
      ∃ tg, find_def (globalenv tp) b = some tg ∧
        match_globdef match_fundef match_varinfo ctx g tg

def find_funct_ptr_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C] [Linker F1] [Linker V1]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ b f, find_funct_ptr (globalenv p) b = some f →
      ∃ cunit tf, find_funct_ptr (globalenv tp) b = some tf ∧
        match_fundef cunit f tf ∧ linkorder cunit ctx

def find_funct_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C] [Linker F1] [Linker V1]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ v f, find_funct (globalenv p) v = some f →
      ∃ cunit tf, find_funct (globalenv tp) v = some tf ∧
        match_fundef cunit f tf ∧ linkorder cunit ctx

def find_symbol_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C] [Linker F1] [Linker V1]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ s : ident, find_symbol (globalenv tp) s = find_symbol (globalenv p) s

def senv_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C] [Linker F1] [Linker V1]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
      Senv.equiv (to_senv (globalenv p)) (to_senv (globalenv tp))

def store_init_data_list_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C] [Linker F1] [Linker V1]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ idl m b ofs m',
      store_init_data_list (globalenv p) m b ofs idl = some m' →
      store_init_data_list (globalenv tp) m b ofs idl = some m'

def alloc_globals_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C] [Linker F1] [Linker V1]
    (match_fundef : C → F1 → F2 → Prop) (match_varinfo : V1 → V2 → Prop)
    (ctx : C) (p : program F1 V1) (tp : program F2 V2),
    match_program_gen match_fundef match_varinfo ctx p tp →
    ∀ gl1 gl2,
      list_forall2 (match_ident_globdef match_fundef match_varinfo ctx) gl1 gl2 →
    ∀ m m', alloc_globals (globalenv p) m gl1 = some m' →
      alloc_globals (globalenv tp) m gl2 = some m'

def init_mem_matchStatement : Prop :=
  ∀ (C F1 V1 F2 V2 : Type) [Linker C] [Linker F1] [Linker V1]
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

/- `store_zeros` is module-level in the Rocq source.  Keep the implementation in
   `Genv`, where the translated consumers live, and expose the exact source path. -/
abbrev store_zeros := Genv.store_zeros

end CompCert4Lean.Common.Globalenvs
