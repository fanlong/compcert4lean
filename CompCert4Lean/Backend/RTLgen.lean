import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.AST
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Backend.CminorSel
import CompCert4Lean.Backend.RTL
import CompCert4Lean.X86.Op

/-!
# Translation from CminorSel to RTL

Definition-bearing translation of CompCert's `backend/RTLgen.v`.  The branch
orientation heuristic is the accepted pure, bounded translation of
`RTLgenaux.ml`.  Proofs assigned to later proof migration are represented by
exact transparent proposition descriptors.
-/

namespace CompCert4Lean.Backend.RTLgen

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Support
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.RTL
open CompCert4Lean.X86.Op

/-! ## Translation environments and state -/

structure mapping : Type where
  map_vars : PTree.t reg
  map_letvars : List reg

export mapping (map_vars map_letvars)

structure state : Type where
  st_nextreg : positive
  st_nextnode : positive
  st_code : code
  st_wf : ∀ pc : positive, Plt pc st_nextnode ∨ PTree.get pc st_code = none

export state (st_nextreg st_nextnode st_code st_wf)

inductive state_incr : state → state → Prop where
  | state_incr_intro (s1 s2 : state)
      (nextnode : Ple s1.st_nextnode s2.st_nextnode)
      (nextreg : Ple s1.st_nextreg s2.st_nextreg)
      (code : ∀ pc, PTree.get pc s1.st_code = none ∨
        PTree.get pc s2.st_code = PTree.get pc s1.st_code) :
      state_incr s1 s2

export state_incr (state_incr_intro)

def state_incr_reflStatement : Prop :=
  ∀ s, state_incr s s

def state_incr_transStatement : Prop :=
  ∀ s1 s2 s3, state_incr s1 s2 → state_incr s2 s3 → state_incr s1 s3

private theorem stateIncrRefl (s : state) : state_incr s s := by
  constructor
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · intro pc
    exact Or.inr rfl

private theorem stateIncrTrans {s1 s2 s3 : state}
    (h12 : state_incr s1 s2) (h23 : state_incr s2 s3) : state_incr s1 s3 := by
  cases h12 with
  | state_incr_intro hn12 hr12 hc12 =>
    cases h23 with
    | state_incr_intro hn23 hr23 hc23 =>
      constructor
      · exact Nat.le_trans hn12 hn23
      · exact Nat.le_trans hr12 hr23
      · intro pc
        rcases hc12 pc with hnone | heq12
        · exact Or.inl hnone
        · rcases hc23 pc with hnone | heq23
          · exact Or.inl (by simpa [heq12] using hnone)
          · exact Or.inr (by simpa [heq12] using heq23)

private theorem posToNatSucc (p : positive) :
    PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p) =
      PArith.BinPos.Pos.to_nat p + 1 := by
  induction p with
  | xH => rfl
  | xI p ih =>
      change 2 * PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p) =
        (2 * PArith.BinPos.Pos.to_nat p + 1) + 1
      rw [ih]
      omega
  | xO p ih => rfl

private theorem pltSucc (p : positive) : Plt p (PArith.BinPos.Pos.succ p) := by
  change PArith.BinPos.Pos.to_nat p <
    PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p)
  rw [posToNatSucc]
  omega

private theorem pltTransSucc {p q : positive} (h : Plt p q) :
    Plt p (PArith.BinPos.Pos.succ q) := by
  change PArith.BinPos.Pos.to_nat p < PArith.BinPos.Pos.to_nat q at h
  change PArith.BinPos.Pos.to_nat p <
    PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ q)
  rw [posToNatSucc]
  omega

private theorem pltNe {p q : positive} (h : Plt p q) : p ≠ q := by
  intro heq
  subst q
  exact Nat.lt_irrefl _ h

private theorem ptreeGetEmpty {A : Type} (p : positive) :
    PTree.get p (PTree.empty A) = none := by
  rfl

private theorem ptreeGetSet0Eq {A : Type} (p : positive) (x : A) :
    PTree.get' p (PTree.set0 p x) = some x := by
  induction p with
  | xH => rfl
  | xI p ih => exact ih
  | xO p ih => exact ih

private theorem ptreeGetSetPrimeEq {A : Type} (p : positive) (x : A)
    (m : PTree.tree' A) : PTree.get' p (PTree.set' p x m) = some x := by
  induction p generalizing m with
  | xH => cases m <;> rfl
  | xI p ih => cases m <;> simp only [PTree.set', PTree.get'] <;>
      first | exact ih _ | exact ptreeGetSet0Eq p x
  | xO p ih => cases m <;> simp only [PTree.set', PTree.get'] <;>
      first | exact ih _ | exact ptreeGetSet0Eq p x

private theorem ptreeGetSetEq {A : Type} (p : positive) (x : A)
    (m : PTree.t A) : PTree.get p (PTree.set p x m) = some x := by
  cases m with
  | Empty => exact ptreeGetSet0Eq p x
  | Nodes m => exact ptreeGetSetPrimeEq p x m

private theorem ptreeGetSet0Ne {A : Type} (p q : positive) (x : A)
    (h : p ≠ q) : PTree.get' p (PTree.set0 q x) = none := by
  induction p generalizing q with
  | xH => cases q with
    | xH => contradiction
    | xI _ => rfl
    | xO _ => rfl
  | xI p ih => cases q with
    | xH => rfl
    | xI q =>
        apply ih q
        intro hpq
        apply h
        cases hpq
        rfl
    | xO _ => rfl
  | xO p ih => cases q with
    | xH => rfl
    | xI _ => rfl
    | xO q =>
        apply ih q
        intro hpq
        apply h
        cases hpq
        rfl

private theorem ptreeGetSetPrimeNe {A : Type} (p q : positive) (x : A)
    (m : PTree.tree' A) (h : p ≠ q) :
    PTree.get' p (PTree.set' q x m) = PTree.get' p m := by
  induction p generalizing q m with
  | xH => cases q with
    | xH => contradiction
    | xI q => cases m <;> rfl
    | xO q => cases m <;> rfl
  | xI p ih => cases q with
    | xH => cases m <;> rfl
    | xI q =>
        have hpq : p ≠ q := by
          intro e; apply h; cases e; rfl
        cases m <;> simp only [PTree.set', PTree.get'] <;>
          first | exact ih q _ hpq | exact ptreeGetSet0Ne p q x hpq
    | xO q => cases m <;> rfl
  | xO p ih => cases q with
    | xH => cases m <;> rfl
    | xI q => cases m <;> rfl
    | xO q =>
        have hpq : p ≠ q := by
          intro e; apply h; cases e; rfl
        cases m <;> simp only [PTree.set', PTree.get'] <;>
          first | exact ih q _ hpq | exact ptreeGetSet0Ne p q x hpq

private theorem ptreeGetSetNe {A : Type} (p q : positive) (x : A)
    (m : PTree.t A) (h : p ≠ q) :
    PTree.get p (PTree.set q x m) = PTree.get p m := by
  cases m with
  | Empty => exact ptreeGetSet0Ne p q x h
  | Nodes m => exact ptreeGetSetPrimeNe p q x m h

/-! ## State and error monad -/

inductive res (A : Type) (s : state) : Type where
  | Error (msg : CompCert4Lean.Common.Errors.errmsg)
  | OK (value : A) (s' : state) (incr : state_incr s s')

export res (Error OK)

def mon (A : Type) : Type := ∀ s : state, res A s

def ret {A : Type} (x : A) : mon A :=
  fun s => .OK x s (stateIncrRefl s)

def bind {A B : Type} (f : mon A) (g : A → mon B) : mon B :=
  fun s =>
    match f s with
    | .Error msg => .Error msg
    | .OK a s' h =>
        match g a s' with
        | .Error msg => .Error msg
        | .OK b s'' h' => .OK b s'' (stateIncrTrans h h')

def bind2 {A B C : Type} (f : mon (A × B)) (g : A → B → mon C) : mon C :=
  bind f (fun xy => g xy.1 xy.2)

private instance : Monad mon where
  pure := @ret
  bind := @bind

def error {A : Type} (msg : CompCert4Lean.Common.Errors.errmsg) : mon A :=
  fun _ => .Error msg

def handle_error {A : Type} (f g : mon A) : mon A :=
  fun s =>
    match f s with
    | .OK a s' h => .OK a s' h
    | .Error _ => g s

/-! ## Error-message constants -/

private def byteString : List UInt8 →
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
  | [] => .EmptyString
  | b :: bs => .String b (byteString bs)

private def textUpdateInstr := byteString
  [82, 84, 76, 103, 101, 110, 46, 117, 112, 100, 97, 116, 101, 95, 105, 110, 115, 116, 114]
private def textUnboundVariable := byteString
  [82, 84, 76, 103, 101, 110, 58, 32, 117, 110, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32]
private def textUnboundLetVariable := byteString
  [82, 84, 76, 103, 101, 110, 58, 32, 117, 110, 98, 111, 117, 110, 100, 32, 108, 101, 116, 32, 118, 97, 114, 105, 97, 98, 108, 101]
private def textBadBuiltinRes := byteString
  [82, 84, 76, 103, 101, 110, 58, 32, 98, 97, 100, 32, 98, 117, 105, 108, 116, 105, 110, 95, 114, 101, 115]
private def textTranslExprlist := byteString
  [82, 84, 76, 103, 101, 110, 46, 116, 114, 97, 110, 115, 108, 95, 101, 120, 112, 114, 108, 105, 115, 116]
private def textWrongExit := byteString
  [82, 84, 76, 103, 101, 110, 58, 32, 119, 114, 111, 110, 103, 32, 101, 120, 105, 116]
private def textReturnMismatch := byteString
  [82, 84, 76, 103, 101, 110, 58, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 111, 110, 32, 114, 101, 116, 117, 114, 110]
private def textUnboundLabel := byteString
  [82, 84, 76, 103, 101, 110, 58, 32, 117, 110, 98, 111, 117, 110, 100, 32, 108, 97, 98, 101, 108]
private def textMultiplyDefinedLabel := byteString
  [77, 117, 108, 116, 105, 112, 108, 121, 45, 100, 101, 102, 105, 110, 101, 100, 32, 108, 97, 98, 101, 108, 32]
private def textUndefinedDefinedLabel := byteString
  [85, 110, 100, 101, 102, 105, 110, 101, 100, 32, 100, 101, 102, 105, 110, 101, 100, 32, 108, 97, 98, 101, 108, 32]

/-! ## State operations -/

def init_state_wfStatement : Prop :=
  ∀ pc, Plt pc (.xH : positive) ∨
    PTree.get pc (PTree.empty instruction) = none

private theorem initStateWf (pc : positive) :
    Plt pc (.xH : positive) ∨ PTree.get pc (PTree.empty instruction) = none :=
  Or.inr (ptreeGetEmpty pc)

def init_state : state :=
  { st_nextreg := .xH
    st_nextnode := .xH
    st_code := PTree.empty instruction
    st_wf := initStateWf }

def add_instr_wfStatement : Prop :=
  ∀ (s : state) (i : instruction) (pc : positive),
    let n := s.st_nextnode
    Plt pc (PArith.BinPos.Pos.succ n) ∨ PTree.get pc (PTree.set n i s.st_code) = none

private theorem addInstrWf (s : state) (i : instruction) (pc : positive) :
    Plt pc (PArith.BinPos.Pos.succ s.st_nextnode) ∨
      PTree.get pc (PTree.set s.st_nextnode i s.st_code) = none := by
  by_cases hpc : pc = s.st_nextnode
  · subst pc
    exact Or.inl (pltSucc _)
  · rw [ptreeGetSetNe pc s.st_nextnode i s.st_code hpc]
    rcases s.st_wf pc with hlt | hnone
    · exact Or.inl (pltTransSucc hlt)
    · exact Or.inr hnone

private def addInstrState (s : state) (i : instruction) : state :=
  { st_nextreg := s.st_nextreg
    st_nextnode := PArith.BinPos.Pos.succ s.st_nextnode
    st_code := PTree.set s.st_nextnode i s.st_code
    st_wf := addInstrWf s i }

def add_instr_incrStatement : Prop :=
  ∀ s i,
    let n := s.st_nextnode
    state_incr s
      { st_nextreg := s.st_nextreg
        st_nextnode := PArith.BinPos.Pos.succ n
        st_code := PTree.set n i s.st_code
        st_wf := addInstrWf s i }

private theorem addInstrIncr (s : state) (i : instruction) :
    state_incr s (addInstrState s i) := by
  constructor
  · change PArith.BinPos.Pos.to_nat s.st_nextnode ≤
      PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ s.st_nextnode)
    rw [posToNatSucc]
    omega
  · exact Nat.le_refl _
  · intro pc
    rcases s.st_wf pc with hlt | hnone
    · exact Or.inr (ptreeGetSetNe pc s.st_nextnode i s.st_code (pltNe hlt))
    · exact Or.inl hnone

def add_instr (i : instruction) : mon node :=
  fun s => .OK s.st_nextnode (addInstrState s i) (addInstrIncr s i)

def reserve_instr_wfStatement : Prop :=
  ∀ (s : state) pc, Plt pc (PArith.BinPos.Pos.succ s.st_nextnode) ∨
    PTree.get pc s.st_code = none

private theorem reserveInstrWf (s : state) (pc : positive) :
    Plt pc (PArith.BinPos.Pos.succ s.st_nextnode) ∨ PTree.get pc s.st_code = none := by
  rcases s.st_wf pc with hlt | hnone
  · exact Or.inl (pltTransSucc hlt)
  · exact Or.inr hnone

private def reserveInstrState (s : state) : state :=
  { st_nextreg := s.st_nextreg
    st_nextnode := PArith.BinPos.Pos.succ s.st_nextnode
    st_code := s.st_code
    st_wf := reserveInstrWf s }

def reserve_instr_incrStatement : Prop :=
  ∀ s,
    let n := s.st_nextnode
    state_incr s
      { st_nextreg := s.st_nextreg
        st_nextnode := PArith.BinPos.Pos.succ n
        st_code := s.st_code
        st_wf := reserveInstrWf s }

private theorem reserveInstrIncr (s : state) : state_incr s (reserveInstrState s) := by
  constructor
  · change PArith.BinPos.Pos.to_nat s.st_nextnode ≤
      PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ s.st_nextnode)
    rw [posToNatSucc]
    omega
  · exact Nat.le_refl _
  · intro pc
    exact Or.inr rfl

def reserve_instr : mon node :=
  fun s => .OK s.st_nextnode (reserveInstrState s) (reserveInstrIncr s)

def update_instr_wfStatement : Prop :=
  ∀ (s : state) n i, Plt n s.st_nextnode → ∀ pc,
    Plt pc s.st_nextnode ∨ PTree.get pc (PTree.set n i s.st_code) = none

private theorem updateInstrWf (s : state) (n : node) (i : instruction)
    (hlt : Plt n s.st_nextnode) (pc : positive) :
    Plt pc s.st_nextnode ∨ PTree.get pc (PTree.set n i s.st_code) = none := by
  by_cases hpc : pc = n
  · subst pc
    exact Or.inl hlt
  · rw [ptreeGetSetNe pc n i s.st_code hpc]
    exact s.st_wf pc

private def updateInstrState (s : state) (n : node) (i : instruction)
    (hlt : Plt n s.st_nextnode) : state :=
  { st_nextreg := s.st_nextreg
    st_nextnode := s.st_nextnode
    st_code := PTree.set n i s.st_code
    st_wf := updateInstrWf s n i hlt }

def update_instr_incrStatement : Prop :=
  ∀ s n i (hlt : Plt n s.st_nextnode), PTree.get n s.st_code = none →
    state_incr s
      { st_nextreg := s.st_nextreg
        st_nextnode := s.st_nextnode
        st_code := PTree.set n i s.st_code
        st_wf := updateInstrWf s n i hlt }

private theorem updateInstrIncr (s : state) (n : node) (i : instruction)
    (hlt : Plt n s.st_nextnode) (hempty : PTree.get n s.st_code = none) :
    state_incr s (updateInstrState s n i hlt) := by
  constructor
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · intro pc
    by_cases hpc : pc = n
    · subst pc
      exact Or.inl hempty
    · exact Or.inr (ptreeGetSetNe pc n i s.st_code hpc)

def check_empty_node (s : state) (n : node) :
    Sumbool (PTree.get n s.st_code = none) True :=
  match h : PTree.get n s.st_code with
  | none => .left (by simpa using h)
  | some _ => .right trivial

def update_instr (n : node) (i : instruction) : mon Unit :=
  fun s =>
    match plt n s.st_nextnode, check_empty_node s n with
    | .left hlt, .left hempty =>
        .OK () (updateInstrState s n i hlt) (updateInstrIncr s n i hlt hempty)
    | _, _ => .Error (CompCert4Lean.Common.Errors.msg textUpdateInstr)

private def newRegState (s : state) : state :=
  { st_nextreg := PArith.BinPos.Pos.succ s.st_nextreg
    st_nextnode := s.st_nextnode
    st_code := s.st_code
    st_wf := s.st_wf }

def new_reg_incrStatement : Prop :=
  ∀ s,
    state_incr s
      { st_nextreg := PArith.BinPos.Pos.succ s.st_nextreg
        st_nextnode := s.st_nextnode
        st_code := s.st_code
        st_wf := s.st_wf }

private theorem newRegIncr (s : state) : state_incr s (newRegState s) := by
  constructor
  · exact Nat.le_refl _
  · change PArith.BinPos.Pos.to_nat s.st_nextreg ≤
      PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ s.st_nextreg)
    rw [posToNatSucc]
    omega
  · intro pc
    exact Or.inr rfl

def new_reg : mon reg :=
  fun s => .OK s.st_nextreg (newRegState s) (newRegIncr s)

/-! ## Mapping operations -/

def init_mapping : mapping :=
  { map_vars := PTree.empty reg, map_letvars := [] }

def add_var (map : mapping) (name : ident) : mon (reg × mapping) := do
  let r ← new_reg
  ret (r, { map_vars := PTree.set name r map.map_vars
            map_letvars := map.map_letvars })

def add_vars (map : mapping) : List ident → mon (List reg × mapping)
  | [] => ret ([], map)
  | n1 :: nl => do
      let (rl, map1) ← add_vars map nl
      let (r1, map2) ← add_var map1 n1
      ret (r1 :: rl, map2)

def find_var (map : mapping) (name : ident) : mon reg :=
  match PTree.get name map.map_vars with
  | none => error (CompCert4Lean.Common.Errors.MSG textUnboundVariable ::
      CompCert4Lean.Common.Errors.CTX name :: [])
  | some r => ret r

def add_letvar (map : mapping) (r : reg) : mapping :=
  { map_vars := map.map_vars, map_letvars := r :: map.map_letvars }

def find_letvar (map : mapping) (idx : Nat) : mon reg :=
  match map.map_letvars[idx]? with
  | none => error (CompCert4Lean.Common.Errors.msg textUnboundLetVariable)
  | some r => ret r

def alloc_reg (map : mapping) (a : expr) : mon reg :=
  match a with
  | .Evar id => find_var map id
  | .Eletvar n => find_letvar map n
  | _ => new_reg

def alloc_regs (map : mapping) : exprlist → mon (List reg)
  | .Enil => ret []
  | .Econs a bl => do
      let r ← alloc_reg map a
      let rl ← alloc_regs map bl
      ret (r :: rl)

def alloc_optreg (map : mapping) : Option ident → mon reg
  | some id => find_var map id
  | none => new_reg

/-! ## RTL generation -/

def add_move (rs rd : reg) (nd : node) : mon node :=
  if rs = rd then ret nd else add_instr (Iop Omove [rs] rd nd)

def exprlist_of_expr_list (l : List expr) : exprlist :=
  l.foldr Econs Enil

def convert_builtin_arg {A : Type} : builtin_arg expr → List A → builtin_arg A × List A
  | .BA _, r :: rs => (.BA r, rs)
  | .BA _, [] => (.BA_int Int.zero, [])
  | .BA_int n, rl => (.BA_int n, rl)
  | .BA_long n, rl => (.BA_long n, rl)
  | .BA_float n, rl => (.BA_float n, rl)
  | .BA_single n, rl => (.BA_single n, rl)
  | .BA_loadstack chunk ofs, rl => (.BA_loadstack chunk ofs, rl)
  | .BA_addrstack ofs, rl => (.BA_addrstack ofs, rl)
  | .BA_loadglobal chunk id ofs, rl => (.BA_loadglobal chunk id ofs, rl)
  | .BA_addrglobal id ofs, rl => (.BA_addrglobal id ofs, rl)
  | .BA_splitlong hi lo, rl =>
      let (hi', rl1) := convert_builtin_arg hi rl
      let (lo', rl2) := convert_builtin_arg lo rl1
      (.BA_splitlong hi' lo', rl2)
  | .BA_addptr a1 a2, rl =>
      let (a1', rl1) := convert_builtin_arg a1 rl
      let (a2', rl2) := convert_builtin_arg a2 rl1
      (.BA_addptr a1' a2', rl2)

def convert_builtin_args {A : Type} : List (builtin_arg expr) → List A → List (builtin_arg A)
  | [], _ => []
  | a :: al, rl =>
      let (a', rl') := convert_builtin_arg a rl
      a' :: convert_builtin_args al rl'

def convert_builtin_res (map : mapping) (ty : xtype) :
    builtin_res ident → mon (builtin_res reg)
  | .BR id => do
      let r ← find_var map id
      ret (.BR r)
  | .BR_none =>
      if ty = Xvoid then ret .BR_none else do
        let r ← new_reg
        ret (.BR r)
  | .BR_splitlong _ _ =>
      error (CompCert4Lean.Common.Errors.msg textBadBuiltinRes)

mutual
  def transl_expr (map : mapping) (a : expr) (rd : reg) (nd : node) : mon node :=
    match a with
    | .Evar v => do
        let r ← find_var map v
        add_move r rd nd
    | .Eop op al => do
        let rl ← alloc_regs map al
        let no ← add_instr (Iop op rl rd nd)
        transl_exprlist map al rl no
    | .Eload chunk addr al => do
        let rl ← alloc_regs map al
        let no ← add_instr (Iload chunk addr rl rd nd)
        transl_exprlist map al rl no
    | .Econdition a b c => do
        let nfalse ← transl_expr map c rd nd
        let ntrue ← transl_expr map b rd nd
        transl_condexpr map a ntrue nfalse
    | .Elet b c => do
        let r ← new_reg
        let nc ← transl_expr (add_letvar map r) c rd nd
        transl_expr map b r nc
    | .Eletvar n => do
        let r ← find_letvar map n
        add_move r rd nd
    | .Ebuiltin ef al => do
        let rl ← alloc_regs map al
        let no ← add_instr (Ibuiltin ef (rl.map BA) (BR rd) nd)
        transl_exprlist map al rl no
    | .Eexternal id sg al => do
        let rl ← alloc_regs map al
        let no ← add_instr (Icall sg (.inr id) rl rd nd)
        transl_exprlist map al rl no

  def transl_exprlist (map : mapping) (al : exprlist) (rl : List reg)
      (nd : node) : mon node :=
    match al, rl with
    | .Enil, [] => ret nd
    | .Econs b bs, r :: rs => do
        let no ← transl_exprlist map bs rs nd
        transl_expr map b r no
    | _, _ => error (CompCert4Lean.Common.Errors.msg textTranslExprlist)

  def transl_condexpr (map : mapping) (a : condexpr) (ntrue nfalse : node) : mon node :=
    match a with
    | .CEcond c al => do
        let rl ← alloc_regs map al
        let nt ← add_instr (Icond c rl ntrue nfalse)
        transl_exprlist map al rl nt
    | .CEcondition a b c => do
        let nc ← transl_condexpr map c ntrue nfalse
        let nb ← transl_condexpr map b ntrue nfalse
        transl_condexpr map a nb nc
    | .CElet b c => do
        let r ← new_reg
        let nc ← transl_condexpr (add_letvar map r) c ntrue nfalse
        transl_expr map b r nc
end

def transl_exit (nexits : List node) (n : Nat) : mon node :=
  match nexits[n]? with
  | none => error (CompCert4Lean.Common.Errors.msg textWrongExit)
  | some ne => ret ne

def transl_jumptable (nexits : List node) : List Nat → mon (List node)
  | [] => ret []
  | t1 :: tl => do
      let n1 ← transl_exit nexits t1
      let nl ← transl_jumptable nexits tl
      ret (n1 :: nl)

def transl_exitexpr (map : mapping) (a : exitexpr) (nexits : List node) : mon node :=
  match a with
  | .XEexit n => transl_exit nexits n
  | .XEjumptable a tbl => do
      let r ← alloc_reg map a
      let tbl' ← transl_jumptable nexits tbl
      let n1 ← add_instr (Ijumptable r tbl')
      transl_expr map a r n1
  | .XEcondition a b c => do
      let nc ← transl_exitexpr map c nexits
      let nb ← transl_exitexpr map b nexits
      transl_condexpr map a nb nc
  | .XElet a b => do
      let r ← new_reg
      let n1 ← transl_exitexpr (add_letvar map r) b nexits
      transl_expr map a r n1

/-! ## Pure bounded branch-orientation heuristic -/

private def cap (n : Nat) : Nat := min n 100
private def cadd (a b : Nat) : Nat := cap (a + b)
private def cmul (a b : Nat) : Nat := cap (a * b)

mutual
  private def sizeExpr : expr → Nat
    | .Evar _ => 0
    | .Eop _ args => cadd 1 (sizeExprs args)
    | .Eload _ _ args => cadd 1 (sizeExprs args)
    | .Econdition ce e1 e2 => cadd 1 (cadd (sizeCondexpr ce) (max (sizeExpr e1) (sizeExpr e2)))
    | .Elet e1 e2 => cadd (sizeExpr e1) (sizeExpr e2)
    | .Eletvar _ => 0
    | .Ebuiltin _ el => cadd 2 (sizeExprs el)
    | .Eexternal _ _ el => cadd 5 (sizeExprs el)

  private def sizeExprs : exprlist → Nat
    | .Enil => 0
    | .Econs e el => cadd (sizeExpr e) (sizeExprs el)

  private def sizeCondexpr : condexpr → Nat
    | .CEcond _ args => sizeExprs args
    | .CEcondition c1 c2 c3 =>
        cadd 1 (cadd (sizeCondexpr c1) (cadd (sizeCondexpr c2) (sizeCondexpr c3)))
    | .CElet a c => cadd (sizeExpr a) (sizeCondexpr c)
end

private def lengthExprs : exprlist → Nat
  | .Enil => 0
  | .Econs _ el => cadd 1 (lengthExprs el)

private def sizeEos : Sum expr ident → Nat
  | .inl e => sizeExpr e
  | .inr _ => 0

private def sizeBuiltinArgs (args : List (builtin_arg expr)) : Nat :=
  (params_of_builtin_args args).foldr (fun e n => cadd (sizeExpr e) n) 0

private def sizeExitexpr : exitexpr → Nat
  | .XEexit _ => 0
  | .XEjumptable arg _ => cadd 2 (sizeExpr arg)
  | .XEcondition c e1 e2 => cadd 1 (cadd (sizeCondexpr c) (cadd (sizeExitexpr e1) (sizeExitexpr e2)))
  | .XElet a e => cadd (sizeExpr a) (sizeExitexpr e)

private def sizeStmt : Nat → stmt → Nat
  | _, .Sskip => 0
  | _, .Sassign _ a => sizeExpr a
  | _, .Sstore _ _ args src => cadd 1 (cadd (sizeExprs args) (sizeExpr src))
  | _, .Scall _ _ eos args => cadd 3 (cadd (sizeEos eos) (cadd (sizeExprs args) (lengthExprs args)))
  | _, .Stailcall _ eos args => cadd 3 (cadd (sizeEos eos) (cadd (sizeExprs args) (lengthExprs args)))
  | _, .Sbuiltin _ (.EF_annot _ _ _) _ => 0
  | _, .Sbuiltin _ (.EF_debug _ _ _) _ => 0
  | _, .Sbuiltin _ _ args => cadd 1 (sizeBuiltinArgs args)
  | depth, .Sseq s1 s2 => cadd (sizeStmt depth s1) (sizeStmt depth s2)
  | 0, .Sifthenelse _ _ _ => 100
  | depth + 1, .Sifthenelse ce s1 s2 =>
      cadd (sizeCondexpr ce) (max (sizeStmt depth s1) (sizeStmt depth s2))
  | depth, .Sloop s => cadd 1 (cmul 4 (sizeStmt depth s))
  | depth, .Sblock s => sizeStmt depth s
  | _, .Sexit _ => 1
  | _, .Sswitch xe => sizeExitexpr xe
  | _, .Sreturn none => 2
  | _, .Sreturn (some arg) => cadd 2 (sizeExpr arg)
  | depth, .Slabel _ s => sizeStmt depth s
  | _, .Sgoto _ => 1

def more_likely (_c : condexpr) (ifso ifnot : stmt) : Bool :=
  decide (sizeStmt 4 ifso > sizeStmt 4 ifnot)

def labelmap : Type := PTree.t node

def transl_stmt (map : mapping) (s : stmt) (nd : node) (nexits : List node)
    (ngoto : labelmap) (nret : node) (rret : Option reg) : mon node :=
  match s with
  | .Sskip => ret nd
  | .Sassign v b => do
      let r ← find_var map v
      transl_expr map b r nd
  | .Sstore chunk addr al b => do
      let rl ← alloc_regs map al
      let r ← alloc_reg map b
      let no ← add_instr (Istore chunk addr rl r nd)
      let ns ← transl_expr map b r no
      transl_exprlist map al rl ns
  | .Scall optid sig (.inl b) cl => do
      let rf ← alloc_reg map b
      let rargs ← alloc_regs map cl
      let r ← alloc_optreg map optid
      let n1 ← add_instr (Icall sig (.inl rf) rargs r nd)
      let n2 ← transl_exprlist map cl rargs n1
      transl_expr map b rf n2
  | .Scall optid sig (.inr id) cl => do
      let rargs ← alloc_regs map cl
      let r ← alloc_optreg map optid
      let n1 ← add_instr (Icall sig (.inr id) rargs r nd)
      transl_exprlist map cl rargs n1
  | .Stailcall sig (.inl b) cl => do
      let rf ← alloc_reg map b
      let rargs ← alloc_regs map cl
      let n1 ← add_instr (Itailcall sig (.inl rf) rargs)
      let n2 ← transl_exprlist map cl rargs n1
      transl_expr map b rf n2
  | .Stailcall sig (.inr id) cl => do
      let rargs ← alloc_regs map cl
      let n1 ← add_instr (Itailcall sig (.inr id) rargs)
      transl_exprlist map cl rargs n1
  | .Sbuiltin result ef args => do
      let al := exprlist_of_expr_list (params_of_builtin_args args)
      let rargs ← alloc_regs map al
      let args' := convert_builtin_args args rargs
      let result' ← convert_builtin_res map (ef_sig ef).sig_res result
      let n1 ← add_instr (Ibuiltin ef args' result' nd)
      transl_exprlist map al rargs n1
  | .Sseq s1 s2 => do
      let ns ← transl_stmt map s2 nd nexits ngoto nret rret
      transl_stmt map s1 ns nexits ngoto nret rret
  | .Sifthenelse c strue sfalse =>
      if more_likely c strue sfalse then do
        let nfalse ← transl_stmt map sfalse nd nexits ngoto nret rret
        let ntrue ← transl_stmt map strue nd nexits ngoto nret rret
        transl_condexpr map c ntrue nfalse
      else do
        let ntrue ← transl_stmt map strue nd nexits ngoto nret rret
        let nfalse ← transl_stmt map sfalse nd nexits ngoto nret rret
        transl_condexpr map c ntrue nfalse
  | .Sloop body => do
      let n1 ← reserve_instr
      let n2 ← transl_stmt map body n1 nexits ngoto nret rret
      let _ ← update_instr n1 (Inop n2)
      add_instr (Inop n2)
  | .Sblock body => transl_stmt map body nd (nd :: nexits) ngoto nret rret
  | .Sexit n => transl_exit nexits n
  | .Sswitch a => transl_exitexpr map a nexits
  | .Sreturn opta =>
      match opta, rret with
      | none, _ => ret nret
      | some a, some r => transl_expr map a r nret
      | _, _ => error (CompCert4Lean.Common.Errors.msg textReturnMismatch)
  | .Slabel lbl body => do
      let ns ← transl_stmt map body nd nexits ngoto nret rret
      match PTree.get lbl ngoto with
      | none => error (CompCert4Lean.Common.Errors.msg textUnboundLabel)
      | some n => do
          let _ ← handle_error (update_instr n (Inop ns))
            (error (CompCert4Lean.Common.Errors.MSG textMultiplyDefinedLabel ::
              CompCert4Lean.Common.Errors.CTX lbl :: []))
          ret ns
  | .Sgoto lbl =>
      match PTree.get lbl ngoto with
      | none => error (CompCert4Lean.Common.Errors.MSG textUndefinedDefinedLabel ::
          CompCert4Lean.Common.Errors.CTX lbl :: [])
      | some n => ret n
termination_by s

def alloc_label (lbl : ident) (map : labelmap) : mon labelmap := do
  let n ← reserve_instr
  ret (PTree.set lbl n map)

def reserve_labels (s : stmt) (lm : labelmap) : mon labelmap :=
  match s with
  | .Sseq s1 s2 | .Sifthenelse _ s1 s2 => do
      let lm' ← reserve_labels s2 lm
      reserve_labels s1 lm'
  | .Sloop s1 | .Sblock s1 => reserve_labels s1 lm
  | .Slabel lbl s1 => do
      let lm' ← reserve_labels s1 lm
      alloc_label lbl lm'
  | _ => ret lm
termination_by s

def ret_reg (sig : signature) (rd : reg) : Option reg :=
  if sig.sig_res = Xvoid then none else some rd

def transl_fun (f : CminorSel.function) : mon (node × List reg) := do
  let ngoto ← reserve_labels f.fn_body (PTree.empty node)
  let (rparams, map1) ← add_vars init_mapping f.fn_params
  let (_, map2) ← add_vars map1 f.fn_vars
  let rret ← new_reg
  let orret := ret_reg f.fn_sig rret
  let nret ← add_instr (Ireturn orret)
  let nentry ← transl_stmt map2 f.fn_body nret [] ngoto nret orret
  ret (nentry, rparams)

def transl_function (f : CminorSel.function) :
    CompCert4Lean.Common.Errors.res RTL.function :=
  match transl_fun f init_state with
  | .Error msg => .Error msg
  | .OK (nentry, rparams) s _ =>
      .OK
        { fn_sig := f.fn_sig
          fn_params := rparams
          fn_stacksize := f.fn_stackspace
          fn_code := s.st_code
          fn_entrypoint := nentry }

def transl_fundef : CminorSel.fundef → CompCert4Lean.Common.Errors.res RTL.fundef :=
  transf_partial_fundef transl_function

def transl_program (p : CminorSel.program) : CompCert4Lean.Common.Errors.res RTL.program :=
  transform_partial_program transl_fundef p

end CompCert4Lean.Backend.RTLgen

namespace CompCert4Lean.Backend.RTLgen

theorem state_incr_refl : state_incr_reflStatement := by
  exact fun s => stateIncrRefl s

theorem state_incr_trans : state_incr_transStatement := by
  exact fun s1 s2 s3 h12 h23 => stateIncrTrans h12 h23

theorem init_state_wf : init_state_wfStatement := by
  exact fun pc => initStateWf pc

theorem add_instr_wf : add_instr_wfStatement := by
  intro s i pc
  exact addInstrWf s i pc

end CompCert4Lean.Backend.RTLgen

namespace CompCert4Lean.Backend.RTLgen

theorem add_instr_incr : add_instr_incrStatement := by
  intro s i
  exact addInstrIncr s i

theorem reserve_instr_wf : reserve_instr_wfStatement := by
  intro s pc
  exact reserveInstrWf s pc

theorem reserve_instr_incr : reserve_instr_incrStatement := by
  intro s
  exact reserveInstrIncr s

theorem update_instr_wf : update_instr_wfStatement := by
  intro s n i hlt pc
  exact updateInstrWf s n i hlt pc

end CompCert4Lean.Backend.RTLgen

namespace CompCert4Lean.Backend.RTLgen

theorem update_instr_incr : update_instr_incrStatement := by
  intro s n i hlt hempty
  exact updateInstrIncr s n i hlt hempty

theorem new_reg_incr : new_reg_incrStatement := by
  intro s
  exact newRegIncr s

end CompCert4Lean.Backend.RTLgen
