import CompCert4Lean.Backend.RTL
import CompCert4Lean.Common.Errors
import CompCert4Lean.Lib.Wfsimpl

/-!
# RTL function inlining

Definition-bearing translation of CompCert's `backend/Inlining.v`.  The
extracted inlining heuristic is represented as a pure analysis over explicit
immutable frontend facts, following the accepted explicit-compiler-services
boundary.  The two proof declarations assigned to later proof migration are
recorded as exact proposition descriptors.
-/

namespace CompCert4Lean.Backend.Inlining

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private abbrev zZero : Z := Z0
private abbrev zOne : Z := Zpos xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zMax := ZArith.BinInt.Z.max
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

/-! ## Environment of inlinable functions -/

def funenv : Type := PTree.t function

private def treeCount' {A : Type} : PTree.tree' A → Nat
  | .Node001 r => treeCount' r
  | .Node010 _ => 1
  | .Node011 _ r => 1 + treeCount' r
  | .Node100 l => treeCount' l
  | .Node101 l r => treeCount' l + treeCount' r
  | .Node110 l _ => treeCount' l + 1
  | .Node111 l _ r => treeCount' l + 1 + treeCount' r

private def treeCount {A : Type} : PTree.tree A → Nat
  | .Empty => 0
  | .Nodes tree => treeCount' tree

private theorem xelementsLength {A : Type} (tree : PTree.tree' A)
    (index : positive) (suffix : List (positive × A)) :
    (PTree.xelements' tree index suffix).length = treeCount' tree + suffix.length := by
  induction tree generalizing index suffix <;>
    simp_all [PTree.xelements', treeCount', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem cardinalEqTreeCount {A : Type} (tree : PTree.tree A) :
    PTree_Properties.cardinal tree = treeCount tree := by
  cases tree with
  | Empty => rfl
  | Nodes tree =>
      simpa [PTree_Properties.cardinal, PTree.elements, PTree.xelements, treeCount]
        using xelementsLength tree xH []

def size_fenv (fenv : funenv) : Nat := PTree_Properties.cardinal fenv

private theorem treeCountRemLt {A : Type} (p : positive) (tree : PTree.tree' A)
    (value : A) (h : PTree.get' p tree = some value) :
    treeCount (PTree.remove' p tree) < treeCount' tree := by
  induction p generalizing tree with
  | xH =>
      cases tree <;>
        simp_all [PTree.get', PTree.remove', treeCount, treeCount']
  | xI p ih =>
      cases tree <;> simp_all [PTree.get', PTree.remove', treeCount, treeCount']
      all_goals
        have decrease := ih _ h
        cases hrem : PTree.remove' p _ <;>
          simp [hrem, treeCount'] at decrease ⊢ <;> omega
  | xO p ih =>
      cases tree <;> simp_all [PTree.get', PTree.remove', treeCount, treeCount']
      all_goals
        have decrease := ih _ h
        cases hrem : PTree.remove' p _ <;>
          simp [hrem, treeCount'] at decrease ⊢ <;> omega

private theorem sizeFenvRemoveLt (fenv : funenv) (id : ident) (f : function)
    (h : PTree.get id fenv = some f) :
    size_fenv (PTree.remove id fenv) < size_fenv fenv := by
  rw [show size_fenv (PTree.remove id fenv) = treeCount (PTree.remove id fenv) by
        exact cardinalEqTreeCount _]
  rw [show size_fenv fenv = treeCount fenv by exact cardinalEqTreeCount _]
  cases fenv with
  | Empty => simp [PTree.get] at h
  | Nodes tree =>
      exact treeCountRemLt id tree f (by simpa [PTree.get] using h)

/-! ## Explicit inlining analysis and policy -/

inductive InlineStatus : Type where
  | inline
  | noinline
  | noSpecifier
deriving DecidableEq

structure InliningConfig : Type where
  enabled : Bool
  functionsCalledOnce : Bool
  inlineStatus : ident → InlineStatus
  isStatic : ident → Bool

private inductive CallMultiplicity : Type where
  | zero
  | one
  | many
deriving DecidableEq

private structure InliningInfoRepr : Type where
  calls : PTree.t CallMultiplicity
  addrTaken : PTree.t Unit

def inlining_info : Type := InliningInfoRepr

private def emptyInliningInfo : inlining_info :=
  { calls := PTree.empty CallMultiplicity
    addrTaken := PTree.empty Unit }

private def callMultiplicity (id : ident) (info : inlining_info) : CallMultiplicity :=
  match PTree.get id info.calls with
  | none => .zero
  | some count => count

private def incrementMultiplicity : CallMultiplicity → CallMultiplicity
  | .zero => .one
  | .one | .many => .many

private def called (id : ident) (info : inlining_info) : inlining_info :=
  { info with
    calls := PTree.set id (incrementMultiplicity (callMultiplicity id info)) info.calls }

private def addressTaken (id : ident) (info : inlining_info) : Bool :=
  match PTree.get id info.addrTaken with
  | none => false
  | some _ => true

private def usedIds (info : inlining_info) (ids : List ident) : inlining_info :=
  ids.foldl (fun acc id => { acc with addrTaken := PTree.set id () acc.addrTaken }) info

private def usedInGlobvar (info : inlining_info) (gv : globvar Unit) : inlining_info :=
  gv.gvar_init.foldl
    (fun acc init =>
      match init with
      | .Init_addrof id _ => usedIds acc [id]
      | _ => acc)
    info

private def analyzeInstruction (info : inlining_info) (_pc : node)
    (instr : instruction) : inlining_info :=
  match instr with
  | .Iop op _ _ _ => usedIds info (globals_operation op)
  | .Iload _ addr _ _ _ => usedIds info (globals_addressing addr)
  | .Istore _ addr _ _ _ => usedIds info (globals_addressing addr)
  | .Ibuiltin _ args _ _ => usedIds info (globals_of_builtin_args args)
  | .Icall _ (.inr id) _ _ _ => called id info
  | .Itailcall _ (.inr id) _ => called id info
  | _ => info

private def analyzeFunction (info : inlining_info) (f : function) : inlining_info :=
  PTree.fold analyzeInstruction f.fn_code info

def inlining_analysis (cfg : InliningConfig) (p : program) : inlining_info :=
  if cfg.enabled && cfg.functionsCalledOnce then
    p.prog_defs.foldl
      (fun info idg =>
        match idg.2 with
        | .Gfun (.Internal f) => analyzeFunction info f
        | .Gvar gv => usedInGlobvar info gv
        | _ => info)
      emptyInliningInfo
  else
    emptyInliningInfo

private def leafInstruction (leaf : Bool) (_pc : node) (instr : instruction) : Bool :=
  match instr with
  | .Icall _ _ _ _ _ | .Itailcall _ _ _ => false
  | _ => leaf

private def instructionCost (cost : Nat) (_pc : node) (instr : instruction) : Nat :=
  match instr with
  | .Inop _ | .Ibuiltin (.EF_debug ..) _ _ _ => cost
  | _ => cost + 1

private def codeCost (f : function) : Nat :=
  PTree.fold instructionCost f.fn_code 0

private def smallLeafFunction (f : function) : Bool :=
  decide (codeCost f ≤ 160) && PTree.fold leafInstruction f.fn_code true

private def multiCallCandidate (f : function) : Bool :=
  smallLeafFunction f || decide (treeCount f.fn_code ≤ 8)

def should_inline (cfg : InliningConfig) (info : inlining_info)
    (id : ident) (f : function) : Bool :=
  if !cfg.enabled then
    false
  else
    match cfg.inlineStatus id with
    | .inline => true
    | .noinline => false
    | .noSpecifier =>
        cfg.functionsCalledOnce &&
          !addressTaken id info &&
          ((cfg.isStatic id && (callMultiplicity id info != .many || multiCallCandidate f)) ||
            (!cfg.isStatic id && callMultiplicity id info == .one &&
              ((decide (treeCount f.fn_code ≤ 16) && PTree.fold leafInstruction f.fn_code true) ||
                decide (treeCount f.fn_code ≤ 12))))

def add_globdef (cfg : InliningConfig) (info : inlining_info)
    (fenv : funenv) (idg : ident × globdef fundef Unit) : funenv :=
  match idg with
  | (id, .Gfun (.Internal f)) =>
      if should_inline cfg info id f then PTree.set id f fenv else PTree.remove id fenv
  | (id, _) => PTree.remove id fenv

def funenv_program (cfg : InliningConfig) (p : program) : funenv :=
  let info := inlining_analysis cfg p
  p.prog_defs.foldl (add_globdef cfg info) (PTree.empty function)

/-! ## State monad -/

structure state : Type where
  st_nextreg : positive
  st_nextnode : positive
  st_code : code
  st_stksize : Z

export state (st_nextreg st_nextnode st_code st_stksize)

inductive sincr (s1 s2 : state) : Prop where
  | intro
      (nextreg : Ple s1.st_nextreg s2.st_nextreg)
      (nextnode : Ple s1.st_nextnode s2.st_nextnode)
      (stksize : zLe s1.st_stksize s2.st_stksize)

def sincr_reflStatement : Prop :=
  ∀ s : state, sincr s s

def sincr_transStatement : Prop :=
  ∀ s1 s2 s3 : state, sincr s1 s2 → sincr s2 s3 → sincr s1 s3

private def sincrRefl (s : state) : sincr s s :=
  .intro (Nat.le_refl _) (Nat.le_refl _) (Int.le_refl _)

private def sincrCompose {s1 s2 s3 : state}
    (h12 : sincr s1 s2) (h23 : sincr s2 s3) : sincr s1 s3 :=
  match h12, h23 with
  | .intro nr12 nn12 ss12, .intro nr23 nn23 ss23 =>
      .intro (Nat.le_trans nr12 nr23) (Nat.le_trans nn12 nn23)
        (Int.le_trans ss12 ss23)

inductive res {A : Type} {s : state} : Type where
  | R (x : A) (s' : state) (incr : sincr s s')

export res (R)

def mon (A : Type) : Type := ∀ s : state, res (A := A) (s := s)

def ret {A : Type} (x : A) : mon A :=
  fun s => R x s (sincrRefl s)

def bind {A B : Type} (x : mon A) (f : A → mon B) : mon B :=
  fun s1 =>
    match x s1 with
    | R vx s2 h12 =>
        match f vx s2 with
        | R vy s3 h23 => R vy s3 (sincrCompose h12 h23)

def initstate : state :=
  { st_nextreg := xH
    st_nextnode := xH
    st_code := PTree.empty instruction
    st_stksize := zZero }

private theorem posToNatSucc (p : positive) :
    posToNat (PArith.BinPos.Pos.succ p) = posToNat p + 1 := by
  induction p with
  | xH => simp [PArith.BinPos.Pos.succ, posToNat]
  | xI p ih => simp [PArith.BinPos.Pos.succ, posToNat, ih]; omega
  | xO p => simp [PArith.BinPos.Pos.succ, posToNat]

private theorem pleSucc (p : positive) : Ple p (PArith.BinPos.Pos.succ p) := by
  change posToNat p ≤ posToNat (PArith.BinPos.Pos.succ p)
  rw [posToNatSucc]
  omega

private theorem pleAdd (p q : positive) : Ple p (PArith.BinPos.Pos.add p q) := by
  change posToNat p ≤ posToNat (posOfNat (posToNat p + posToNat q))
  rw [posToNat_posOfNat]
  · omega
  · exact Nat.add_pos_left (posToNat_positive p) _

private theorem zLeMaxLeft (x y : Z) : zLe x (zMax x y) := by
  change intOfZ x ≤ intOfZ (ZArith.BinInt.Z.max x y)
  by_cases h : intOfZ x ≤ intOfZ y
  · simp [ZArith.BinInt.Z.max, h]
  · simp [ZArith.BinInt.Z.max, h]

/-! Exact proposition companions for the eight proof constants generated by
Rocq's `Program Definition` commands in `backend/Inlining.v`.  The executable
definitions below retain their proof-erased behavior; these source-named
descriptors keep the generated proof surface explicit for proof grinding. -/

def set_instr_obligation_1Statement : Prop :=
  ∀ (pc : node) (instr : instruction) (s : state),
    sincr s
      { st_nextreg := s.st_nextreg
        st_nextnode := s.st_nextnode
        st_code := PTree.set pc instr s.st_code
        st_stksize := s.st_stksize }

def add_instr_obligation_1Statement : Prop :=
  ∀ (instr : instruction) (s : state),
    let pc := s.st_nextnode
    sincr s
      { st_nextreg := s.st_nextreg
        st_nextnode := PArith.BinPos.Pos.succ pc
        st_code := PTree.set pc instr s.st_code
        st_stksize := s.st_stksize }

def reserve_nodes_obligation_1Statement : Prop :=
  ∀ (numnodes : positive) (s : state),
    sincr s
      { st_nextreg := s.st_nextreg
        st_nextnode := PArith.BinPos.Pos.add s.st_nextnode numnodes
        st_code := s.st_code
        st_stksize := s.st_stksize }

def reserve_regs_obligation_1Statement : Prop :=
  ∀ (numregs : positive) (s : state),
    sincr s
      { st_nextreg := PArith.BinPos.Pos.add s.st_nextreg numregs
        st_nextnode := s.st_nextnode
        st_code := s.st_code
        st_stksize := s.st_stksize }

def request_stack_obligation_1Statement : Prop :=
  ∀ (size : Z) (s : state),
    sincr s
      { st_nextreg := s.st_nextreg
        st_nextnode := s.st_nextnode
        st_code := s.st_code
        st_stksize := zMax s.st_stksize size }

def ptree_mfold_obligation_1Statement : Prop :=
  ∀ (A : Type) (f : positive → A → mon Unit) (tree : PTree.t A) (s : state),
    sincr s
      (PTree.fold
        (fun s1 key value =>
          match f key value s1 with
          | R _ s2 _ => s2)
        tree s)

def can_inline_obligation_1Statement : Prop :=
  ∀ id : ident, (Sum.inr id : reg ⊕ ident) = Sum.inr id

def can_inline_obligation_2Statement : Prop :=
  ∀ (fenv : funenv) (id : ident),
    let filtered := PTree.get id fenv
    ∀ (f : function), some f = filtered → PTree.get id fenv = some f

def set_instr (pc : node) (instr : instruction) : mon Unit :=
  fun s =>
    R ()
      { st_nextreg := s.st_nextreg
        st_nextnode := s.st_nextnode
        st_code := PTree.set pc instr s.st_code
        st_stksize := s.st_stksize }
      (.intro (Nat.le_refl _) (Nat.le_refl _) (Int.le_refl _))

def add_instr (instr : instruction) : mon node :=
  fun s =>
    let pc := s.st_nextnode
    R pc
      { st_nextreg := s.st_nextreg
        st_nextnode := PArith.BinPos.Pos.succ pc
        st_code := PTree.set pc instr s.st_code
        st_stksize := s.st_stksize }
      (.intro (Nat.le_refl _) (pleSucc pc) (Int.le_refl _))

def reserve_nodes (numnodes : positive) : mon positive :=
  fun s =>
    R s.st_nextnode
      { st_nextreg := s.st_nextreg
        st_nextnode := PArith.BinPos.Pos.add s.st_nextnode numnodes
        st_code := s.st_code
        st_stksize := s.st_stksize }
      (.intro (Nat.le_refl _) (pleAdd s.st_nextnode numnodes) (Int.le_refl _))

def reserve_regs (numregs : positive) : mon positive :=
  fun s =>
    R s.st_nextreg
      { st_nextreg := PArith.BinPos.Pos.add s.st_nextreg numregs
        st_nextnode := s.st_nextnode
        st_code := s.st_code
        st_stksize := s.st_stksize }
      (.intro (pleAdd s.st_nextreg numregs) (Nat.le_refl _) (Int.le_refl _))

def request_stack (size : Z) : mon Unit :=
  fun s =>
    R ()
      { st_nextreg := s.st_nextreg
        st_nextnode := s.st_nextnode
        st_code := s.st_code
        st_stksize := zMax s.st_stksize size }
      (.intro (Nat.le_refl _) (Nat.le_refl _) (zLeMaxLeft s.st_stksize size))

def ptree_mfold {A : Type} (f : positive → A → mon Unit)
    (tree : PTree.t A) : mon Unit :=
  fun s =>
    PTree.fold
      (fun result key value =>
        match result with
        | R _ s1 h1 =>
            match f key value s1 with
            | R _ s2 h2 => R () s2 (sincrCompose h1 h2))
      tree
      (R () s (sincrRefl s))

/-! ## Inlining contexts -/

structure context : Type where
  dpc : positive
  dreg : positive
  dstk : Z
  mreg : positive
  mstk : Z
  retinfo : Option (node × reg)

export context (dpc dreg dstk mreg mstk retinfo)

def shiftpos (p amount : positive) : positive :=
  PArith.BinPos.Pos.pred (PArith.BinPos.Pos.add p amount)

def spc (ctx : context) (pc : node) : node := shiftpos pc ctx.dpc

def sreg (ctx : context) (r : reg) : reg := shiftpos r ctx.dreg

def sregs (ctx : context) (regs : List reg) : List reg := regs.map (sreg ctx)

def sros (ctx : context) : Sum reg ident → Sum reg ident
  | .inl r => .inl (sreg ctx r)
  | .inr id => .inr id

def sop (ctx : context) (op : operation) : operation :=
  shift_stack_operation ctx.dstk op

def saddr (ctx : context) (addr : addressing) : addressing :=
  shift_stack_addressing ctx.dstk addr

def sbuiltinarg (ctx : context) : builtin_arg reg → builtin_arg reg
  | .BA x => .BA (sreg ctx x)
  | .BA_loadstack chunk ofs =>
      .BA_loadstack chunk (Ptrofs.add ofs (Ptrofs.repr ctx.dstk))
  | .BA_addrstack ofs => .BA_addrstack (Ptrofs.add ofs (Ptrofs.repr ctx.dstk))
  | .BA_splitlong hi lo => .BA_splitlong (sbuiltinarg ctx hi) (sbuiltinarg ctx lo)
  | .BA_addptr a1 a2 => .BA_addptr (sbuiltinarg ctx a1) (sbuiltinarg ctx a2)
  | .BA_int n => .BA_int n
  | .BA_long n => .BA_long n
  | .BA_float n => .BA_float n
  | .BA_single n => .BA_single n
  | .BA_loadglobal chunk id ofs => .BA_loadglobal chunk id ofs
  | .BA_addrglobal id ofs => .BA_addrglobal id ofs

def sbuiltinres (ctx : context) : builtin_res reg → builtin_res reg
  | .BR x => .BR (sreg ctx x)
  | _ => .BR_none

def initcontext (dpc dreg nreg : positive) (size : Z) : context :=
  { dpc := dpc
    dreg := dreg
    dstk := zZero
    mreg := nreg
    mstk := zMax size zZero
    retinfo := none }

def min_alignment (size : Z) : Z :=
  match zle size (zOfNat 1) with
  | .left _ => zOfNat 1
  | .right _ =>
      match zle size (zOfNat 2) with
      | .left _ => zOfNat 2
      | .right _ =>
          match zle size (zOfNat 4) with
          | .left _ => zOfNat 4
          | .right _ => zOfNat 8

def callcontext (ctx : context) (dpc dreg nreg : positive) (size : Z)
    (retpc : node) (retreg : reg) : context :=
  { dpc := dpc
    dreg := dreg
    dstk := align (zAdd ctx.dstk ctx.mstk) (min_alignment size)
    mreg := nreg
    mstk := zMax size zZero
    retinfo := some (spc ctx retpc, sreg ctx retreg) }

def tailcontext (ctx : context) (dpc dreg nreg : positive) (size : Z) : context :=
  { dpc := dpc
    dreg := dreg
    dstk := align ctx.dstk (min_alignment size)
    mreg := nreg
    mstk := zMax size zZero
    retinfo := ctx.retinfo }

/-! ## Recursive CFG expansion -/

def add_moves : List reg → List reg → node → mon node
  | src :: srcs, dst :: dsts, succ =>
      bind (add_instr (.Iop .Omove [src] dst succ))
        (fun next => add_moves srcs dsts next)
  | _, _, succ => ret succ

inductive inline_decision (fenv : funenv) (ros : Sum reg ident) : Type where
  | Cannot_inline
  | Can_inline (id : ident) (f : function)
      (target : ros = .inr id) (lookup : PTree.get id fenv = some f)

export inline_decision (Cannot_inline Can_inline)

def can_inline (fenv : funenv) (ros : Sum reg ident) : inline_decision fenv ros :=
  match ros with
  | .inl _ => .Cannot_inline
  | .inr id =>
      match h : PTree.get id fenv with
      | none => .Cannot_inline
      | some f => .Can_inline id f rfl h

def inline_function (fenv : funenv)
    (rec : ∀ fenv', size_fenv fenv' < size_fenv fenv → context → function → mon Unit)
    (ctx : context) (id : ident) (f : function) (lookup : PTree.get id fenv = some f)
    (args : List reg) (retpc : node) (retreg : reg) : mon node :=
  let npc := max_pc_function f
  let nreg := max_reg_function f
  bind (reserve_nodes npc) (fun dpc =>
    bind (reserve_regs nreg) (fun dreg =>
      let ctx' := callcontext ctx dpc dreg nreg f.fn_stacksize retpc retreg
      bind (rec (PTree.remove id fenv) (sizeFenvRemoveLt fenv id f lookup) ctx' f) (fun _ =>
        add_moves (sregs ctx args) (sregs ctx' f.fn_params) (spc ctx' f.fn_entrypoint))))

def inline_tail_function (fenv : funenv)
    (rec : ∀ fenv', size_fenv fenv' < size_fenv fenv → context → function → mon Unit)
    (ctx : context) (id : ident) (f : function) (lookup : PTree.get id fenv = some f)
    (args : List reg) : mon node :=
  let npc := max_pc_function f
  let nreg := max_reg_function f
  bind (reserve_nodes npc) (fun dpc =>
    bind (reserve_regs nreg) (fun dreg =>
      let ctx' := tailcontext ctx dpc dreg nreg f.fn_stacksize
      bind (rec (PTree.remove id fenv) (sizeFenvRemoveLt fenv id f lookup) ctx' f) (fun _ =>
        add_moves (sregs ctx args) (sregs ctx' f.fn_params) (spc ctx' f.fn_entrypoint))))

def inline_return (ctx : context) (result : Option reg) (returnInfo : node × reg) :
    instruction :=
  match returnInfo, result with
  | (retpc, retreg), some r => .Iop .Omove [sreg ctx r] retreg retpc
  | (retpc, _), none => .Inop retpc

def expand_instr (fenv : funenv)
    (rec : ∀ fenv', size_fenv fenv' < size_fenv fenv → context → function → mon Unit)
    (ctx : context) (pc : node) (instr : instruction) : mon Unit :=
  match instr with
  | .Inop succ =>
      set_instr (spc ctx pc) (.Inop (spc ctx succ))
  | .Iop op args result succ =>
      set_instr (spc ctx pc)
        (.Iop (sop ctx op) (sregs ctx args) (sreg ctx result) (spc ctx succ))
  | .Iload chunk addr args dst succ =>
      set_instr (spc ctx pc)
        (.Iload chunk (saddr ctx addr) (sregs ctx args) (sreg ctx dst) (spc ctx succ))
  | .Istore chunk addr args src succ =>
      set_instr (spc ctx pc)
        (.Istore chunk (saddr ctx addr) (sregs ctx args) (sreg ctx src) (spc ctx succ))
  | .Icall sig ros args result succ =>
      match can_inline fenv ros with
      | .Cannot_inline =>
          set_instr (spc ctx pc)
            (.Icall sig (sros ctx ros) (sregs ctx args) (sreg ctx result) (spc ctx succ))
      | .Can_inline id f _ lookup =>
          bind (inline_function fenv rec ctx id f lookup args succ result) (fun next =>
            set_instr (spc ctx pc) (.Inop next))
  | .Itailcall sig ros args =>
      match can_inline fenv ros with
      | .Cannot_inline =>
          match ctx.retinfo with
          | none =>
              set_instr (spc ctx pc) (.Itailcall sig (sros ctx ros) (sregs ctx args))
          | some (rpc, rreg) =>
              set_instr (spc ctx pc) (.Icall sig (sros ctx ros) (sregs ctx args) rreg rpc)
      | .Can_inline id f _ lookup =>
          bind (inline_tail_function fenv rec ctx id f lookup args) (fun next =>
            set_instr (spc ctx pc) (.Inop next))
  | .Ibuiltin ef args result succ =>
      set_instr (spc ctx pc)
        (.Ibuiltin ef (args.map (sbuiltinarg ctx)) (sbuiltinres ctx result) (spc ctx succ))
  | .Icond cond args ifso ifnot =>
      set_instr (spc ctx pc)
        (.Icond cond (sregs ctx args) (spc ctx ifso) (spc ctx ifnot))
  | .Ijumptable arg table =>
      set_instr (spc ctx pc) (.Ijumptable (sreg ctx arg) (table.map (spc ctx)))
  | .Ireturn result =>
      match ctx.retinfo with
      | none => set_instr (spc ctx pc) (.Ireturn (result.map (sreg ctx)))
      | some returnInfo => set_instr (spc ctx pc) (inline_return ctx result returnInfo)

def expand_cfg_rec (fenv : funenv)
    (rec : ∀ fenv', size_fenv fenv' < size_fenv fenv → context → function → mon Unit)
    (ctx : context) (f : function) : mon Unit :=
  bind (request_stack (zAdd ctx.dstk ctx.mstk)) (fun _ =>
    ptree_mfold (expand_instr fenv rec ctx) f.fn_code)

def expand_cfg (fenv : funenv) (ctx : context) (f : function) : mon Unit :=
  CompCert4Lean.Lib.Wfsimpl.Fixm size_fenv expand_cfg_rec fenv ctx f

def expand_function (fenv : funenv) (f : function) : mon context :=
  let npc := max_pc_function f
  let nreg := max_reg_function f
  bind (reserve_nodes npc) (fun dpc =>
    bind (reserve_regs nreg) (fun dreg =>
      let ctx := initcontext dpc dreg nreg f.fn_stacksize
      bind (expand_cfg fenv ctx f) (fun _ => ret ctx)))

/-! ## Inlining in functions and whole programs -/

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private def rocqStringOfBytes : List UInt8 → RocqString
  | [] => .EmptyString
  | byte :: rest => .String byte (rocqStringOfBytes rest)

private def stackTooBigText : RocqString :=
  rocqStringOfBytes
    [73, 110, 108, 105, 110, 105, 110, 103, 58, 32, 115, 116, 97, 99, 107, 32,
      116, 111, 111, 32, 98, 105, 103]

def transf_function (fenv : funenv) (f : function) :
    CompCert4Lean.Common.Errors.res function :=
  match expand_function fenv f initstate with
  | R ctx s _ =>
      match zlt s.st_stksize Ptrofs.max_unsigned with
      | .left _ =>
          .OK
            { fn_sig := f.fn_sig
              fn_params := sregs ctx f.fn_params
              fn_stacksize := s.st_stksize
              fn_code := s.st_code
              fn_entrypoint := spc ctx f.fn_entrypoint }
      | .right _ => .Error (msg stackTooBigText)

def transf_fundef (fenv : funenv) (fd : fundef) :
    CompCert4Lean.Common.Errors.res fundef :=
  CompCert4Lean.Common.AST.transf_partial_fundef (transf_function fenv) fd

def transf_program (cfg : InliningConfig) (p : program) :
    CompCert4Lean.Common.Errors.res program :=
  let fenv := funenv_program cfg p
  CompCert4Lean.Common.AST.transform_partial_program (transf_fundef fenv) p

end CompCert4Lean.Backend.Inlining

namespace CompCert4Lean.Backend.Inlining

theorem sincr_refl : sincr_reflStatement := by
  intro s
  exact sincrRefl s

theorem sincr_trans : sincr_transStatement := by
  intro s1 s2 s3 h12 h23
  exact sincrCompose h12 h23

theorem set_instr_obligation_1 : set_instr_obligation_1Statement := by
  intro pc instr s
  exact .intro (Nat.le_refl _) (Nat.le_refl _) (Int.le_refl _)

theorem add_instr_obligation_1 : add_instr_obligation_1Statement := by
  intro instr s
  exact .intro (Nat.le_refl _) (pleSucc s.st_nextnode) (Int.le_refl _)

end CompCert4Lean.Backend.Inlining

namespace CompCert4Lean.Backend.Inlining

theorem reserve_nodes_obligation_1 : reserve_nodes_obligation_1Statement := by
  intro numnodes s
  exact .intro (Nat.le_refl _) (pleAdd s.st_nextnode numnodes) (Int.le_refl _)

theorem reserve_regs_obligation_1 : reserve_regs_obligation_1Statement := by
  intro numregs s
  exact .intro (pleAdd s.st_nextreg numregs) (Nat.le_refl _) (Int.le_refl _)

theorem request_stack_obligation_1 : request_stack_obligation_1Statement := by
  intro size s
  exact .intro (Nat.le_refl _) (Nat.le_refl _) (zLeMaxLeft s.st_stksize size)

theorem ptree_mfold_obligation_1 : ptree_mfold_obligation_1Statement := by
  intro A f tree s
  apply CompCert4Lean.Lib.Maps.PTree_Properties.fold_rec_proof
    (V := A) (A := state)
    (f := fun s1 key value =>
      match f key value s1 with
      | R _ s2 _ => s2)
    (P := fun _ s' => sincr s s') (init := s) (mFinal := tree)
  · intro m m' a hext hP
    exact hP
  · exact sincrRefl s
  · intro m a k v hnone hfinal hP
    cases hfv : f k v a with
    | R _ s2 hstep =>
        exact sincrCompose hP hstep

end CompCert4Lean.Backend.Inlining

namespace CompCert4Lean.Backend.Inlining

theorem can_inline_obligation_1 : can_inline_obligation_1Statement := by
  intro id
  rfl

theorem can_inline_obligation_2 : can_inline_obligation_2Statement := by
  intro fenv id filtered f h
  exact h.symm

end CompCert4Lean.Backend.Inlining
