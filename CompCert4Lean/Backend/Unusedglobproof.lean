import CompCert4Lean.Backend.Unusedglob

/-!
# Correctness interface for elimination of unreferenced globals

Definition-bearing translation of CompCert's `backend/Unusedglobproof.v`.
Proofs assigned to the later proof-migration phase are represented by exact
proposition descriptors.  The external-call environment is threaded
explicitly through the statements that use RTL transitions or semantics.
-/

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev z0 : Z := .Z0
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

/-! ## Relational specification of the transformation -/

structure match_prog_1 (u : IS.t) (p tp : program) : Prop where
  match_prog_main : tp.prog_main = p.prog_main
  match_prog_public : tp.prog_public = p.prog_public
  match_prog_def :
    ∀ id, PTree.get id (prog_defmap tp) =
      if IS.mem id u then PTree.get id (prog_defmap p) else none
  match_prog_unique : list_norepet (prog_defs_names tp)

export match_prog_1
  (match_prog_main match_prog_public match_prog_def match_prog_unique)

def ref_function (f : function) (id : ident) : Prop :=
  ∃ pc i, PTree.get pc f.fn_code = some i ∧ id ∈ ref_instruction i

def ref_fundef (fd : fundef) (id : ident) : Prop :=
  match fd with
  | .Internal f => ref_function f id
  | .External _ => False

def ref_init (il : List init_data) (id : ident) : Prop :=
  ∃ ofs, Init_addrof id ofs ∈ il

def ref_def (gd : globdef fundef Unit) (id : ident) : Prop :=
  match gd with
  | .Gfun fd => ref_fundef fd id
  | .Gvar gv => ref_init gv.gvar_init id

structure valid_used_set (p : program) (u : IS.t) : Prop where
  used_closed : ∀ id gd id',
    IS.In id u → PTree.get id (prog_defmap p) = some gd → ref_def gd id' →
      IS.In id' u
  used_main : IS.In p.prog_main u
  used_public : ∀ id, id ∈ p.prog_public → IS.In id u
  used_defined : ∀ id,
    IS.In id u → id ∈ prog_defs_names p ∨ id = p.prog_main

export valid_used_set (used_closed used_main used_public used_defined)

def match_prog (p tp : program) : Prop :=
  ∃ u : IS.t, valid_used_set p u ∧ match_prog_1 u p tp

/-! ## Properties of the static analysis -/

structure workset_incl (w1 w2 : workset) : Prop where
  seen_subset : IS.Subset w1.w_seen w2.w_seen
  todo_subset : ∀ ⦃id⦄, id ∈ w1.w_todo → id ∈ w2.w_todo
  seen_tracked : ∀ id,
    IS.In id w2.w_seen → IS.In id w1.w_seen ∨ id ∈ w2.w_todo

def seen_workset_inclStatement : Prop :=
  ∀ (w1 w2 : workset) (id : IS.elt),
    workset_incl w1 w2 → IS.In id w1.w_seen → IS.In id w2.w_seen

def workset_incl_reflStatement : Prop :=
  ∀ w : workset, workset_incl w w

def workset_incl_transStatement : Prop :=
  ∀ w1 w2 w3 : workset,
    workset_incl w1 w2 → workset_incl w2 w3 → workset_incl w1 w3

def add_workset_inclStatement : Prop :=
  ∀ (id : ident) (w : workset), workset_incl w (add_workset id w)

def addlist_workset_inclStatement : Prop :=
  ∀ (l : List ident) (w : workset), workset_incl w (addlist_workset l w)

def add_ref_function_inclStatement : Prop :=
  ∀ (f : function) (w : workset), workset_incl w (add_ref_function f w)

def add_ref_globvar_inclStatement : Prop :=
  ∀ (gv : globvar Unit) (w : workset), workset_incl w (add_ref_globvar gv w)

def add_ref_definition_inclStatement : Prop :=
  ∀ (pm : prog_map) (id : ident) (w : workset),
    workset_incl w (add_ref_definition pm id w)

def initial_workset_inclStatement : Prop :=
  ∀ p : program,
    workset_incl { w_seen := IS.empty, w_todo := [] } (initial_workset p)

def seen_add_worksetStatement : Prop :=
  ∀ (id : IS.elt) (w : workset), IS.In id (add_workset id w).w_seen

def seen_addlist_worksetStatement : Prop :=
  ∀ (id : IS.elt) (l : List IS.elt) (w : workset),
    id ∈ l → IS.In id (addlist_workset l w).w_seen

def seen_add_ref_functionStatement : Prop :=
  ∀ (id : ident) (f : function) (w : workset),
    ref_function f id → IS.In id (add_ref_function f w).w_seen

def seen_add_ref_definitionStatement : Prop :=
  ∀ (pm : prog_map) (id : ident) (gd : globdef fundef Unit)
    (id' : ident) (w : workset),
    PTree.get id pm = some gd → ref_def gd id' →
      IS.In id' (add_ref_definition pm id w).w_seen

def seen_main_initial_worksetStatement : Prop :=
  ∀ p : program, IS.In p.prog_main (initial_workset p).w_seen

def seen_public_initial_worksetStatement : Prop :=
  ∀ (p : program) (id : ident),
    id ∈ p.prog_public → IS.In id (initial_workset p).w_seen

def workset_invariant (p : program) (w : workset) : Prop :=
  ∀ id gd id',
    IS.In id w.w_seen → ¬ id ∈ w.w_todo →
      PTree.get id (prog_defmap p) = some gd → ref_def gd id' →
        IS.In id' w.w_seen

def used_set_closed (p : program) (u : IS.t) : Prop :=
  ∀ id gd id',
    IS.In id u → PTree.get id (prog_defmap p) = some gd → ref_def gd id' →
      IS.In id' u

def iter_step_invariantStatement : Prop :=
  ∀ (p : program) (w : workset),
    workset_invariant p w →
      match iter_step (prog_defmap p) w with
      | .inl u => used_set_closed p u
      | .inr w' => workset_invariant p w'

def used_globals_soundStatement : Prop :=
  ∀ (p : program) (u : IS.t),
    used_globals p (prog_defmap p) = some u → used_set_closed p u

def used_globals_inclStatement : Prop :=
  ∀ (p : program) (u : IS.t),
    used_globals p (prog_defmap p) = some u →
      IS.Subset (initial_workset p).w_seen u

def used_globals_validStatement : Prop :=
  ∀ (p : program) (u : IS.t),
    used_globals p (prog_defmap p) = some u →
      IS.for_all (global_defined p (prog_defmap p)) u = true →
        valid_used_set p u

/-! ## Filtering global definitions -/

def filter_globdefs_accuStatement : Prop :=
  ∀ (defs accu1 accu2 : List (ident × globdef fundef Unit)) (u : IS.t),
    filter_globdefs u (accu1 ++ accu2) defs =
      filter_globdefs u accu1 defs ++ accu2

def filter_globdefs_nilStatement : Prop :=
  ∀ (u : IS.t) (accu defs : List (ident × globdef fundef Unit)),
    filter_globdefs u accu defs = filter_globdefs u [] defs ++ accu

def filter_globdefs_map_1Statement : Prop :=
  ∀ (id : IS.elt) (l : List (ident × globdef fundef Unit))
    (u : IS.t) (m1 : prog_map),
    IS.mem id u = false → PTree.get id m1 = none →
      PTree.get id
        (List.foldl
          (fun m idg => PTree.set idg.1 idg.2 m)
          m1 (filter_globdefs u [] l)) = none

def filter_globdefs_map_2Statement : Prop :=
  ∀ (id : IS.elt) (l : List (ident × globdef fundef Unit))
    (u : IS.t) (m1 m2 : prog_map),
    IS.mem id u = true → PTree.get id m1 = PTree.get id m2 →
      PTree.get id
        (List.foldl
          (fun m idg => PTree.set idg.1 idg.2 m)
          m1 (filter_globdefs u [] l)) =
      PTree.get id
        (List.foldl
          (fun m idg => PTree.set idg.1 idg.2 m)
          m2 l.reverse)

def filter_globdefs_mapStatement : Prop :=
  ∀ (id : ident) (u : IS.t) (defs : List (ident × globdef fundef Unit)),
    PTree.get id (PTree_Properties.of_list (filter_globdefs u [] defs.reverse)) =
      if IS.mem id u then PTree.get id (PTree_Properties.of_list defs) else none

def filter_globdefs_domainStatement : Prop :=
  ∀ (id : ident) (l : List (ident × globdef fundef Unit)) (u : IS.t),
    id ∈ (filter_globdefs u [] l).map Prod.fst →
      IS.In id u ∧ id ∈ l.map Prod.fst

def filter_globdefs_unique_namesStatement : Prop :=
  ∀ (l : List (ident × globdef fundef Unit)) (u : IS.t),
    list_norepet ((filter_globdefs u [] l).map Prod.fst)

def transf_program_matchStatement : Prop :=
  ∀ p tp : program, transform_program p = .OK tp → match_prog p tp

/-! ## Used globals and global-memory injections -/

def kept (used : IS.t) (id : ident) : Prop :=
  IS.In id used

def kept_closedStatement : Prop :=
  ∀ (p : program) (used : IS.t),
    valid_used_set p used →
      ∀ (id : ident) (gd : globdef fundef Unit) (id' : ident),
        kept used id → PTree.get id (prog_defmap p) = some gd →
          ref_def gd id' → kept used id'

def kept_mainStatement : Prop :=
  ∀ (p : program) (used : IS.t),
    valid_used_set p used → kept used p.prog_main

def kept_publicStatement : Prop :=
  ∀ (p : program) (used : IS.t),
    valid_used_set p used →
      ∀ id, id ∈ p.prog_public → kept used id

def transform_find_symbol_1Statement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    match_prog_1 used p tp →
      ∀ (id : ident) (b : block),
        Genv.find_symbol (Genv.globalenv p) id = some b → kept used id →
          ∃ b', Genv.find_symbol (Genv.globalenv tp) id = some b'

def transform_find_symbol_2Statement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    match_prog_1 used p tp →
      ∀ (id : ident) (b : block),
        Genv.find_symbol (Genv.globalenv tp) id = some b →
          kept used id ∧ ∃ b', Genv.find_symbol (Genv.globalenv p) id = some b'

structure meminj_preserves_globals
    (p tp : program) (used : IS.t) (f : Val.meminj) : Prop where
  symbols_inject_1 : ∀ id b b' delta,
    f b = some (b', delta) →
      Genv.find_symbol (Genv.globalenv p) id = some b →
        delta = z0 ∧ Genv.find_symbol (Genv.globalenv tp) id = some b'
  symbols_inject_2 : ∀ id b,
    kept used id → Genv.find_symbol (Genv.globalenv p) id = some b →
      ∃ b', Genv.find_symbol (Genv.globalenv tp) id = some b' ∧
        f b = some (b', z0)
  symbols_inject_3 : ∀ id b',
    Genv.find_symbol (Genv.globalenv tp) id = some b' →
      ∃ b, Genv.find_symbol (Genv.globalenv p) id = some b ∧
        f b = some (b', z0)
  defs_inject : ∀ b b' delta gd,
    f b = some (b', delta) → Genv.find_def (Genv.globalenv p) b = some gd →
      Genv.find_def (Genv.globalenv tp) b' = some gd ∧ delta = z0 ∧
        ∀ id, ref_def gd id → kept used id
  defs_rev_inject : ∀ b b' delta gd,
    f b = some (b', delta) → Genv.find_def (Genv.globalenv tp) b' = some gd →
      Genv.find_def (Genv.globalenv p) b = some gd ∧ delta = z0

export meminj_preserves_globals
  (symbols_inject_1 symbols_inject_2 symbols_inject_3 defs_inject
    defs_rev_inject)

def init_meminj (p tp : program) : Val.meminj :=
  fun b =>
    match Genv.invert_symbol (Genv.globalenv p) b with
    | some id =>
        match Genv.find_symbol (Genv.globalenv tp) id with
        | some b' => some (b', z0)
        | none => none
    | none => none

def init_meminj_eqStatement : Prop :=
  ∀ (p tp : program) (id : ident) (b b' : block),
    Genv.find_symbol (Genv.globalenv p) id = some b →
      Genv.find_symbol (Genv.globalenv tp) id = some b' →
        init_meminj p tp b = some (b', z0)

def init_meminj_invertStatement : Prop :=
  ∀ (p tp : program) (b b' : block) (delta : Z),
    init_meminj p tp b = some (b', delta) →
      delta = z0 ∧
        ∃ id, Genv.find_symbol (Genv.globalenv p) id = some b ∧
          Genv.find_symbol (Genv.globalenv tp) id = some b'

def init_meminj_preserves_globalsStatement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      meminj_preserves_globals p tp used (init_meminj p tp)

def globals_symbols_injectStatement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ j : Val.meminj,
        meminj_preserves_globals p tp used j →
          symbols_inject j
            (Genv.to_senv (Genv.globalenv p))
            (Genv.to_senv (Genv.globalenv tp))

def symbol_address_injectStatement : Prop :=
  ∀ (p tp : program) (used : IS.t) (j : Val.meminj)
    (id : ident) (ofs : ptrofs),
    meminj_preserves_globals p tp used j → kept used id →
      Val.inject j
        (Genv.symbol_address (Genv.globalenv p) id ofs)
        (Genv.symbol_address (Genv.globalenv tp) id ofs)

/-! ## Semantic state relations -/

def regset_inject (f : Val.meminj) (rs rs' : regset) : Prop :=
  ∀ r, Val.inject f (Regmap.get r rs) (Regmap.get r rs')

def regs_injectStatement : Prop :=
  ∀ (f : Val.meminj) (rs rs' : regset),
    regset_inject f rs rs' →
      ∀ l : List reg,
        Val.inject_list f
          (l.map (fun r => Regmap.get r rs))
          (l.map (fun r => Regmap.get r rs'))

def set_reg_injectStatement : Prop :=
  ∀ (f : Val.meminj) (rs rs' : regset) (r : reg) (v v' : val),
    regset_inject f rs rs' → Val.inject f v v' →
      regset_inject f (Regmap.set r v rs) (Regmap.set r v' rs')

def set_res_injectStatement : Prop :=
  ∀ (f : Val.meminj) (rs rs' : regset) (res : builtin_res reg) (v v' : val),
    regset_inject f rs rs' → Val.inject f v v' →
      regset_inject f (regmap_setres res v rs) (regmap_setres res v' rs')

def regset_inject_incrStatement : Prop :=
  ∀ (f f' : Val.meminj) (rs rs' : regset),
    regset_inject f rs rs' → Val.inject_incr f f' → regset_inject f' rs rs'

def regset_undef_injectStatement : Prop :=
  ∀ f : Val.meminj,
    regset_inject f (Regmap.init Vundef) (Regmap.init Vundef)

def init_regs_injectStatement : Prop :=
  ∀ (f : Val.meminj) (args args' : List val),
    Val.inject_list f args args' →
      ∀ params : List reg,
        regset_inject f (init_regs args params) (init_regs args' params)

inductive match_stacks (p tp : program) (used : IS.t) (j : Val.meminj) :
    List stackframe → List stackframe → block → block → Prop where
  | base (bound tbound : block)
      (globals : meminj_preserves_globals p tp used j)
      (source_bound : Ple (Genv.globalenv p).genv_next bound)
      (target_bound : Ple (Genv.globalenv tp).genv_next tbound) :
      match_stacks p tp used j [] [] bound tbound
  | frame (res : reg) (f : function) (sp : block) (pc : node)
      (rs : regset) (s : List stackframe) (tsp : block) (trs : regset)
      (ts : List stackframe) (bound tbound : block)
      (stacks : match_stacks p tp used j s ts sp tsp)
      (refs_kept : ∀ id, ref_function f id → kept used id)
      (sp_inject : j sp = some (tsp, z0))
      (regs : regset_inject j rs trs)
      (below : Plt sp bound)
      (target_below : Plt tsp tbound) :
      match_stacks p tp used j
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: s)
        (Stackframe res f (Vptr tsp Ptrofs.zero) pc trs :: ts)
        bound tbound

def match_stacks_preserves_globalsStatement : Prop :=
  ∀ (p tp : program) (used : IS.t) (j : Val.meminj)
    (s ts : List stackframe) (bound tbound : block),
    match_stacks p tp used j s ts bound tbound →
      meminj_preserves_globals p tp used j

def match_stacks_incrStatement : Prop :=
  ∀ (p tp : program) (used : IS.t) (j j' : Val.meminj),
    Val.inject_incr j j' →
      ∀ (s ts : List stackframe) (bound tbound : block),
        match_stacks p tp used j s ts bound tbound →
          (∀ (b1 b2 : block) (delta : Z),
            j b1 = none → j' b1 = some (b2, delta) →
              Ple bound b1 ∧ Ple tbound b2) →
            match_stacks p tp used j' s ts bound tbound

def match_stacks_boundStatement : Prop :=
  ∀ (p tp : program) (used : IS.t) (j : Val.meminj)
    (s ts : List stackframe) (bound tbound bound' tbound' : block),
    match_stacks p tp used j s ts bound tbound →
      Ple bound bound' → Ple tbound tbound' →
        match_stacks p tp used j s ts bound' tbound'

inductive match_states (p tp : program) (used : IS.t) : state → state → Prop where
  | match_states_regular (s : List stackframe) (f : function) (sp : block)
      (pc : node) (rs : regset) (m : mem) (ts : List stackframe)
      (tsp : block) (trs : regset) (tm : mem) (j : Val.meminj)
      (stacks : match_stacks p tp used j s ts sp tsp)
      (refs_kept : ∀ id, ref_function f id → kept used id)
      (sp_inject : j sp = some (tsp, z0))
      (regs : regset_inject j rs trs)
      (memory : Mem.inject j m tm) :
      match_states p tp used
        (State s f (Vptr sp Ptrofs.zero) pc rs m)
        (State ts f (Vptr tsp Ptrofs.zero) pc trs tm)
  | call (s : List stackframe) (fd : fundef) (args : List val) (m : mem)
      (ts : List stackframe) (targs : List val) (tm : mem) (j : Val.meminj)
      (stacks : match_stacks p tp used j s ts m.nextblock tm.nextblock)
      (refs_kept : ∀ id, ref_fundef fd id → kept used id)
      (args_inject : Val.inject_list j args targs)
      (memory : Mem.inject j m tm) :
      match_states p tp used
        (Callstate s fd args m) (Callstate ts fd targs tm)
  | match_states_return (s : List stackframe) (res : val) (m : mem)
      (ts : List stackframe) (tres : val) (tm : mem) (j : Val.meminj)
      (stacks : match_stacks p tp used j s ts m.nextblock tm.nextblock)
      (res_inject : Val.inject j res tres)
      (memory : Mem.inject j m tm) :
      match_states p tp used
        (Returnstate s res m) (Returnstate ts tres tm)

export match_states (match_states_regular match_states_return)

def external_call_injectStatement : Prop :=
  ∀ (xi : ExternalCalls) (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ (ef : external_function) (vargs : List val) (m1 : mem)
        (t : trace) (vres : val) (m2 : mem) (f : Val.meminj)
        (m1' : mem) (vargs' : List val),
        meminj_preserves_globals p tp used f →
          external_call xi ef (Genv.to_senv (Genv.globalenv p))
            vargs m1 t vres m2 →
          Mem.inject f m1 m1' → Val.inject_list f vargs vargs' →
            ∃ f' vres' m2',
              external_call xi ef (Genv.to_senv (Genv.globalenv tp))
                vargs' m1' t vres' m2' ∧
              Val.inject f' vres vres' ∧
              Mem.inject f' m2 m2' ∧
              Mem.unchanged_on (loc_unmapped f) m1 m2 ∧
              Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' ∧
              Val.inject_incr f f' ∧
              inject_separated f f' m1 m1'

def find_function_injectStatement : Prop :=
  ∀ (p tp : program) (used : IS.t) (j : Val.meminj)
    (ros : Sum reg ident) (rs : regset) (fd : fundef) (trs : regset),
    meminj_preserves_globals p tp used j →
      find_function (Genv.globalenv p) ros rs = some fd →
      (match ros with
       | .inl _ => regset_inject j rs trs
       | .inr id => kept used id) →
      find_function (Genv.globalenv tp) ros trs = some fd ∧
        ∀ id, ref_fundef fd id → kept used id

def eval_builtin_arg_injectStatement : Prop :=
  ∀ (p tp : program) (used : IS.t) (rs : regset) (sp : block)
    (m : mem) (j : Val.meminj) (rs' : regset) (sp' : block) (m' : mem)
    (a : builtin_arg reg) (v : val),
    eval_builtin_arg (Genv.to_senv (Genv.globalenv p))
      (fun r => Regmap.get r rs) (Vptr sp Ptrofs.zero) m a v →
    j sp = some (sp', z0) →
    meminj_preserves_globals p tp used j →
    regset_inject j rs rs' → Mem.inject j m m' →
    (∀ id, id ∈ globals_of_builtin_arg a → kept used id) →
      ∃ v',
        eval_builtin_arg (Genv.to_senv (Genv.globalenv tp))
          (fun r => Regmap.get r rs') (Vptr sp' Ptrofs.zero) m' a v' ∧
        Val.inject j v v'

def eval_builtin_args_injectStatement : Prop :=
  ∀ (p tp : program) (used : IS.t) (rs : regset) (sp : block)
    (m : mem) (j : Val.meminj) (rs' : regset) (sp' : block) (m' : mem)
    (al : List (builtin_arg reg)) (vl : List val),
    eval_builtin_args (Genv.to_senv (Genv.globalenv p))
      (fun r => Regmap.get r rs) (Vptr sp Ptrofs.zero) m al vl →
    j sp = some (sp', z0) →
    meminj_preserves_globals p tp used j →
    regset_inject j rs rs' → Mem.inject j m m' →
    (∀ id, id ∈ globals_of_builtin_args al → kept used id) →
      ∃ vl',
        eval_builtin_args (Genv.to_senv (Genv.globalenv tp))
          (fun r => Regmap.get r rs') (Vptr sp' Ptrofs.zero) m' al vl' ∧
        Val.inject_list j vl vl'

def step_simulationStatement : Prop :=
  ∀ (xi : ExternalCalls) (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ (S1 : state) (t : trace) (S2 : state),
        step xi (Genv.globalenv p) S1 t S2 →
          ∀ S1', match_states p tp used S1 S1' →
            ∃ S2', step xi (Genv.globalenv tp) S1' t S2' ∧
              match_states p tp used S2 S2'

/-! ## Initial memories and whole-program simulation -/

def init_meminj_invert_strongStatement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ (b b' : block) (delta : Z),
        init_meminj p tp b = some (b', delta) →
          delta = z0 ∧
            ∃ id gd,
              Genv.find_symbol (Genv.globalenv p) id = some b ∧
              Genv.find_symbol (Genv.globalenv tp) id = some b' ∧
              Genv.find_def (Genv.globalenv p) b = some gd ∧
              Genv.find_def (Genv.globalenv tp) b' = some gd ∧
              ∀ i, ref_def gd i → kept used i

def bytes_of_init_injectStatement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ il : List init_data,
        (∀ id, ref_init il id → kept used id) →
          list_forall2 (memval_inject (init_meminj p tp))
            (Genv.bytes_of_init_data_list (Genv.globalenv p) il)
            (Genv.bytes_of_init_data_list (Genv.globalenv tp) il)

def Mem_getN_forall2Statement : Prop :=
  ∀ (P : memval → memval → Prop) (c1 c2 : ZMap.t memval)
    (i : Z) (n : Nat) (p : Z),
    list_forall2 P (Mem.getN n p c1) (Mem.getN n p c2) →
      zLe p i → zLt i (zAdd p (zOfNat n)) →
        P (ZMap.get i c1) (ZMap.get i c2)

def init_mem_inj_1Statement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ m tm : mem,
        Genv.init_mem p = some m → Genv.init_mem tp = some tm →
          Mem.mem_inj (init_meminj p tp) m tm

def init_mem_inj_2Statement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ m tm : mem,
        Genv.init_mem p = some m → Genv.init_mem tp = some tm →
          Mem.inject (init_meminj p tp) m tm

def init_mem_existsStatement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ m : mem, Genv.init_mem p = some m →
        ∃ tm, Genv.init_mem tp = some tm

def init_mem_injectStatement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ m : mem, Genv.init_mem p = some m →
        ∃ f tm,
          Genv.init_mem tp = some tm ∧ Mem.inject f m tm ∧
            meminj_preserves_globals p tp used f

def transf_initial_statesStatement : Prop :=
  ∀ (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ S1 : state, initial_state p S1 →
        ∃ S2, initial_state tp S2 ∧ match_states p tp used S1 S2

def transf_final_statesStatement : Prop :=
  ∀ (p tp : program) (used : IS.t) (S1 S2 : state) (r : int),
    match_states p tp used S1 S2 → final_state S1 r → final_state S2 r

def transf_program_correct_1Statement : Prop :=
  ∀ (xi : ExternalCalls) (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      forward_simulation (semantics xi p) (semantics xi tp)

def transf_program_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (p tp : program),
    match_prog p tp → forward_simulation (semantics xi p) (semantics xi tp)

end CompCert4Lean.Backend.Unusedglobproof
