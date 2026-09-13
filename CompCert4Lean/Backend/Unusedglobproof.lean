import CompCert4Lean.Backend.Unusedglob
import CompCert4Lean.Common.Linking

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
open CompCert4Lean.Common.Linking
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
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

/-! ## Selected generated finite-set facts surface -/

namespace ISF

/-- The selected `FSetFacts.Facts(IS)` application over the canonical set provider. -/
def ISF := CompCert4Lean.Backend.Unusedglob.IS.MF

abbrev F := ISF
abbrev elt := CompCert4Lean.Backend.Unusedglob.IS.elt
abbrev t := CompCert4Lean.Backend.Unusedglob.IS.t
abbrev In := CompCert4Lean.Backend.Unusedglob.IS.In
abbrev eqb := CompCert4Lean.Lib.FSetFacts.WFacts_fun.eqb ISF
abbrev mem := CompCert4Lean.Backend.Unusedglob.IS.mem
abbrev remove := CompCert4Lean.Backend.Unusedglob.IS.remove
abbrev for_all := CompCert4Lean.Backend.Unusedglob.IS.for_all

abbrev for_all_iff :=
  CompCert4Lean.Lib.FSetFacts.WFacts_fun.for_all_iff ISF
abbrev remove_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_b ISF
abbrev remove_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_iff ISF

end ISF

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

/-! ## Linking-compatible transformation obligation -/

/- The source theorem is retained as an exact proposition descriptor. Its
   linker arguments are the canonical RTL program linkers used by
   `CompCert4Lean.Common.Linking.TransfLink`; the proof remains deferred to
   the later proof-migration phase. -/
def link_match_programStatement : Prop :=
  ∀ (p1 p2 tp1 tp2 p : RTL.program),
    @link RTL.program
      (@Linker_prog RTL.fundef Unit (@Linker_fundef RTL.function) Linker_unit)
      p1 p2 = some p →
    match_prog p1 tp1 →
    match_prog p2 tp2 →
    ∃ tp : RTL.program,
      @link RTL.program
        (@Linker_prog RTL.fundef Unit (@Linker_fundef RTL.function) Linker_unit)
        tp1 tp2 = some tp ∧
      match_prog p tp

/- The source `TransfSelectionLink` instance contributes precisely this
   canonical `TransfLink match_prog` proposition. It is exposed as a
   source-named descriptor for the certificate-gated adapter below. -/
def TransfSelectionLinkStatement : Prop :=
  @TransfLink RTL.program RTL.program
    (@Linker_prog RTL.fundef Unit (@Linker_fundef RTL.function) Linker_unit)
    (@Linker_prog RTL.fundef Unit (@Linker_fundef RTL.function) Linker_unit)
    match_prog

/- The source global instance is restored through a mandatory companion
   certificate.  Its proof term remains assigned to the later proof-grinding
   phase, while the adapter preserves the exact canonical RTL `TransfLink`
   surface without introducing a default inhabitant. -/
class TransfSelectionLink_Certificate : Prop where
  link : TransfSelectionLinkStatement

instance TransfSelectionLink [certificate : TransfSelectionLink_Certificate] :
    @TransfLink RTL.program RTL.program
      (@Linker_prog RTL.fundef Unit (@Linker_fundef RTL.function) Linker_unit)
      (@Linker_prog RTL.fundef Unit (@Linker_fundef RTL.function) Linker_unit)
      match_prog := certificate.link

/-! ## Properties of the static analysis -/

inductive workset_incl (w1 w2 : workset) : Prop where
  | workset_incl_intro
      (SEEN : IS.Subset w1.w_seen w2.w_seen)
      (TODO : ∀ (id : ident), id ∈ w1.w_todo → id ∈ w2.w_todo)
      (TRACK : ∀ id,
        IS.In id w2.w_seen → IS.In id w1.w_seen ∨ id ∈ w2.w_todo) :
      workset_incl w1 w2

export workset_incl (workset_incl_intro)

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
    regset_inject f rs rs' → inject_incr f f' → regset_inject f' rs rs'

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
  | match_stacks_nil (bound tbound : block)
      (globals : meminj_preserves_globals p tp used j)
      (source_bound : Ple (Genv.globalenv p).genv_next bound)
      (target_bound : Ple (Genv.globalenv tp).genv_next tbound) :
      match_stacks p tp used j [] [] bound tbound
  | match_stacks_cons (res : reg) (f : function) (sp : block) (pc : node)
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

export match_stacks (match_stacks_nil match_stacks_cons)

def match_stacks_preserves_globalsStatement : Prop :=
  ∀ (p tp : program) (used : IS.t) (j : Val.meminj)
    (s ts : List stackframe) (bound tbound : block),
    match_stacks p tp used j s ts bound tbound →
      meminj_preserves_globals p tp used j

def match_stacks_incrStatement : Prop :=
  ∀ (p tp : program) (used : IS.t) (j j' : Val.meminj),
    inject_incr j j' →
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
  | match_states_call (s : List stackframe) (fd : fundef) (args : List val) (m : mem)
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

export match_states (match_states_regular match_states_call match_states_return)

def external_call_injectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ (ef : external_function) (vargs : List val) (m1 : mem)
        (t : trace) (vres : val) (m2 : mem) (f : Val.meminj)
        (m1' : mem) (vargs' : List val),
        meminj_preserves_globals p tp used f →
          external_call
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            xi ef (Genv.to_senv (Genv.globalenv p))
            vargs m1 t vres m2 →
          Mem.inject f m1 m1' → Val.inject_list f vargs vargs' →
            ∃ f' vres' m2',
              external_call
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate)
                xi ef (Genv.to_senv (Genv.globalenv tp))
                vargs' m1' t vres' m2' ∧
              Val.inject f' vres vres' ∧
              Mem.inject f' m2 m2' ∧
              Mem.unchanged_on (loc_unmapped f) m1 m2 ∧
              Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' ∧
              inject_incr f f' ∧
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

def step_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      ∀ (S1 : state) (t : trace) (S2 : state),
        step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi (Genv.globalenv p) S1 t S2 →
          ∀ S1', match_states p tp used S1 S1' →
            ∃ S2', step
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              xi (Genv.globalenv tp) S1' t S2' ∧
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

def transf_program_correct_1Statement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p tp : program) (used : IS.t),
    valid_used_set p used → match_prog_1 used p tp →
      forward_simulation
        (semantics
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi p)
        (semantics
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi tp)

def transf_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p tp : program),
    match_prog p tp →
      forward_simulation
        (semantics
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi p)
        (semantics
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi tp)

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

namespace ISF

theorem for_all_iff_proof : ISF.for_all_iff := by
  intro s f hf
  constructor
  · exact ISF.source.1.for_all_1 s f hf
  · exact ISF.source.1.for_all_2 s f hf

theorem remove_iff_proof : ISF.remove_iff := by
  intro s x y
  constructor
  · intro hy
    have hys : ISF.M.In y s := ISF.source.1.remove_3 s x y hy
    constructor
    · exact hys
    · intro hxy
      exact ISF.source.1.remove_1 s x y hxy hy
  · intro h
    exact ISF.source.1.remove_2 s x y h.2 h.1

theorem remove_b_proof : ISF.remove_b := by
  intro s x y
  by_cases hxy : ISF.E.eq x y
  · have heqb : ISF.eqb x y = true := by
      cases h : ISF.E.eq_dec x y with
      | left h' => simp [ISF.eqb, CompCert4Lean.Lib.FSetFacts.WFacts_fun.eqb, h]
      | right h' => exact False.elim (h' hxy)
    have hleft : ISF.M.mem y (ISF.M.remove x s) = false := by
      cases hm : ISF.M.mem y (ISF.M.remove x s) with
      | false => rfl
      | true => exact False.elim (ISF.source.1.remove_1 s x y hxy
          (ISF.source.1.mem_2 (ISF.M.remove x s) y hm))
    simpa [heqb] using hleft
  · by_cases hm : ISF.M.mem y s = true
    · have hy : ISF.M.In y s := ISF.source.1.mem_2 s y hm
      have hremove : ISF.M.In y (ISF.M.remove x s) :=
        ISF.source.1.remove_2 s x y hxy hy
      have hleft : ISF.M.mem y (ISF.M.remove x s) = true :=
        ISF.source.1.mem_1 (ISF.M.remove x s) y hremove
      have heqb : ISF.eqb x y = false := by
        cases h : ISF.E.eq_dec x y with
        | left h' => exact False.elim (hxy h')
        | right h' => simp [ISF.eqb, CompCert4Lean.Lib.FSetFacts.WFacts_fun.eqb, h]
      simpa [hm, heqb] using hleft
    · have hleft : ISF.M.mem y (ISF.M.remove x s) = false := by
        cases hmr : ISF.M.mem y (ISF.M.remove x s) with
        | false => rfl
        | true =>
            have hys : ISF.M.In y s := ISF.source.1.remove_3 s x y
              (ISF.source.1.mem_2 (ISF.M.remove x s) y hmr)
            exact False.elim (hm (ISF.source.1.mem_1 s y hys))
      have heqb : ISF.eqb x y = false := by
        cases h : ISF.E.eq_dec x y with
        | left h' => exact False.elim (hxy h')
        | right h' => simp [ISF.eqb, CompCert4Lean.Lib.FSetFacts.WFacts_fun.eqb, h]
      simpa [hm, heqb] using hleft

end ISF

theorem seen_workset_incl : seen_workset_inclStatement := by
  intro w1 w2 id hwi hid
  cases hwi with
  | workset_incl_intro seen _ _ => exact seen id hid

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

theorem workset_incl_refl : workset_incl_reflStatement := by
  intro w
  apply workset_incl_intro
  · intro id h
    exact h
  · intro id h
    exact h
  · intro id h
    exact Or.inl h

theorem workset_incl_trans : workset_incl_transStatement := by
  intro w1 w2 w3 h12 h23
  cases h12 with
  | workset_incl_intro seen12 todo12 track12 =>
    cases h23 with
    | workset_incl_intro seen23 todo23 track23 =>
      apply workset_incl_intro
      · intro id h
        exact seen23 id (seen12 id h)
      · intro id h
        exact todo23 id (todo12 id h)
      · intro id h
        rcases track23 id h with h2 | htodo2
        · rcases track12 id h2 with h1 | htodo1
          · exact Or.inl h1
          · exact Or.inr (todo23 id htodo1)
        · exact Or.inr htodo2

theorem add_workset_incl : add_workset_inclStatement := by
  intro id w
  unfold CompCert4Lean.Backend.Unusedglob.add_workset
  split
  · apply workset_incl_intro
    · intro x h
      exact h
    · intro x h
      exact h
    · intro x h
      exact Or.inl h
  · apply workset_incl_intro
    · intro x h
      exact CompCert4Lean.Lib.FSetAVLplus.Make.add_2 w.w_seen id x h
    · intro x h
      exact List.Mem.tail id h
    · intro x h
      by_cases heq : CompCert4Lean.Backend.Unusedglob.IS.X'.eq id x
      · exact Or.inr (heq ▸ List.Mem.head w.w_todo)
      · exact Or.inl
          (CompCert4Lean.Lib.FSetAVLplus.Make.add_3 w.w_seen id x heq h)

theorem addlist_workset_incl : addlist_workset_inclStatement := by
  intro l w
  induction l generalizing w with
  | nil =>
      exact workset_incl_refl w
  | cons id rest ih =>
      exact workset_incl_trans w
        (CompCert4Lean.Backend.Unusedglob.add_workset id w)
        (CompCert4Lean.Backend.Unusedglob.addlist_workset rest
          (CompCert4Lean.Backend.Unusedglob.add_workset id w))
        (add_workset_incl id w)
        (ih (CompCert4Lean.Backend.Unusedglob.add_workset id w))

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

theorem add_ref_function_incl : add_ref_function_inclStatement := by
  intro f w
  unfold CompCert4Lean.Backend.Unusedglob.add_ref_function
  apply CompCert4Lean.Lib.Maps.PTree_Properties.fold_rec_proof
    (P := fun _ a => workset_incl w a)
  · intro m m' a _ h
    exact h
  · exact workset_incl_refl w
  · intro m a k i _ _ h
    exact workset_incl_trans w a
      (CompCert4Lean.Backend.Unusedglob.add_ref_instruction a k i)
      h (addlist_workset_incl
        (CompCert4Lean.Backend.Unusedglob.ref_instruction i) a)

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

theorem add_ref_globvar_incl : add_ref_globvar_inclStatement := by
  intro gv w
  unfold CompCert4Lean.Backend.Unusedglob.add_ref_globvar
  revert w
  induction gv.gvar_init with
  | nil =>
      intro w
      exact workset_incl_refl w
  | cons i il ih =>
      intro w
      simp only [List.foldl]
      apply workset_incl_trans w
        (CompCert4Lean.Backend.Unusedglob.add_ref_init_data w i)
        (List.foldl CompCert4Lean.Backend.Unusedglob.add_ref_init_data
          (CompCert4Lean.Backend.Unusedglob.add_ref_init_data w i) il)
      · unfold CompCert4Lean.Backend.Unusedglob.add_ref_init_data
        cases i with
        | Init_addrof id ofs => exact add_workset_incl id w
        | Init_int8 value => exact workset_incl_refl w
        | Init_int16 value => exact workset_incl_refl w
        | Init_int32 value => exact workset_incl_refl w
        | Init_int64 value => exact workset_incl_refl w
        | Init_float32 value => exact workset_incl_refl w
        | Init_float64 value => exact workset_incl_refl w
        | Init_space size => exact workset_incl_refl w
      · exact ih (CompCert4Lean.Backend.Unusedglob.add_ref_init_data w i)

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

theorem add_ref_definition_incl : add_ref_definition_inclStatement := by
  intro pm id w
  unfold CompCert4Lean.Backend.Unusedglob.add_ref_definition
  cases h : CompCert4Lean.Lib.Maps.PTree.get id pm with
  | none => exact workset_incl_refl w
  | some gd =>
      cases gd with
      | Gfun fd =>
          cases fd with
          | Internal f => exact add_ref_function_incl f w
          | External ef => exact workset_incl_refl w
      | Gvar gv => exact add_ref_globvar_incl gv w

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

theorem initial_workset_incl : initial_workset_inclStatement := by
  intro p
  unfold CompCert4Lean.Backend.Unusedglob.initial_workset
  have hfold : ∀ l w, l.foldl
      (fun w id => CompCert4Lean.Backend.Unusedglob.add_workset id w) w =
      CompCert4Lean.Backend.Unusedglob.addlist_workset l w := by
    intro l
    induction l with
    | nil => intro w; rfl
    | cons id rest ih =>
        intro w
        simp [List.foldl, CompCert4Lean.Backend.Unusedglob.addlist_workset, ih]
  rw [hfold]
  apply workset_incl_trans _ _ _
  · exact addlist_workset_incl p.prog_public _
  · exact add_workset_incl p.prog_main _

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

theorem seen_add_workset : seen_add_worksetStatement := by
  intro id w
  unfold CompCert4Lean.Backend.Unusedglob.add_workset
  split
  · exact CompCert4Lean.Backend.Unusedglob.IS.mem_2_proof _ _ ‹_›
  · exact CompCert4Lean.Backend.Unusedglob.IS.add_1_proof _ _ _ rfl

theorem seen_addlist_workset : seen_addlist_worksetStatement := by
  intro id l w hid
  induction l generalizing w with
  | nil => cases hid
  | cons x xs ih =>
      simp only [List.mem_cons] at hid
      simp only [CompCert4Lean.Backend.Unusedglob.addlist_workset]
      rcases hid with rfl | hid
      · exact seen_workset_incl _ _ id
          (addlist_workset_incl xs (CompCert4Lean.Backend.Unusedglob.add_workset id w))
          (seen_add_workset id w)
      · exact ih (CompCert4Lean.Backend.Unusedglob.add_workset x w) hid

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

theorem seen_add_ref_function : seen_add_ref_functionStatement := by
  intro id f w href
  unfold ref_function at href
  unfold CompCert4Lean.Backend.Unusedglob.add_ref_function
  let P : CompCert4Lean.Lib.Maps.PTree.t CompCert4Lean.Backend.RTL.instruction →
      CompCert4Lean.Backend.Unusedglob.workset → Prop := fun m a =>
    ∀ id, (∃ pc i, CompCert4Lean.Lib.Maps.PTree.get pc m = some i ∧
      id ∈ CompCert4Lean.Backend.Unusedglob.ref_instruction i) →
      CompCert4Lean.Backend.Unusedglob.IS.In id a.w_seen
  have hfold : P f.fn_code
      (CompCert4Lean.Lib.Maps.PTree.fold
        CompCert4Lean.Backend.Unusedglob.add_ref_instruction f.fn_code w) := by
    apply CompCert4Lean.Lib.Maps.PTree_Properties.fold_rec_proof
      (P := P)
    · intro m m' a hext hP id h
      rcases h with ⟨pc, i, hget, hrefi⟩
      apply hP id
      exact ⟨pc, i, by rw [hext pc]; exact hget, hrefi⟩
    · intro id h
      rcases h with ⟨pc, i, hget, hrefi⟩
      simp [CompCert4Lean.Lib.Maps.PTree.empty,
        CompCert4Lean.Lib.Maps.PTree.get] at hget
    · intro m a k i hnone hfinal hP id h
      rcases h with ⟨pc, j, hget, hrefj⟩
      rw [CompCert4Lean.Lib.Maps.PTree.getSet_equation] at hget
      split at hget
      · rename_i hpk
        subst pc
        cases hget
        unfold CompCert4Lean.Backend.Unusedglob.add_ref_instruction
        exact seen_addlist_workset id
          (CompCert4Lean.Backend.Unusedglob.ref_instruction i)
          a hrefj
      · unfold CompCert4Lean.Backend.Unusedglob.add_ref_instruction
        apply seen_workset_incl _ _ id
          (addlist_workset_incl
            (CompCert4Lean.Backend.Unusedglob.ref_instruction i) a)
        exact hP id ⟨pc, j, hget, hrefj⟩
  exact hfold id href

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

theorem seen_add_ref_definition : seen_add_ref_definitionStatement := by
  intro pm id gd id' w hget href
  unfold CompCert4Lean.Backend.Unusedglob.add_ref_definition
  rw [hget]
  cases gd with
  | Gfun fd =>
      cases fd with
      | Internal f => exact seen_add_ref_function id' f w href
      | External ef => cases href
  | Gvar gv =>
      rcases href with ⟨ofs, hmem⟩
      unfold CompCert4Lean.Backend.Unusedglob.add_ref_globvar
      have hfold : ∀ (l : List CompCert4Lean.Common.AST.init_data)
          (w : CompCert4Lean.Backend.Unusedglob.workset),
          CompCert4Lean.Backend.Unusedglob.IS.In id' w.w_seen ∨
            CompCert4Lean.Common.AST.init_data.Init_addrof id' ofs ∈ l →
          CompCert4Lean.Backend.Unusedglob.IS.In id' (List.foldl
            CompCert4Lean.Backend.Unusedglob.add_ref_init_data w l).w_seen := by
        intro l
        induction l with
        | nil =>
            intro w h
            cases h with
            | inl hw => exact hw
            | inr hm => cases hm
        | cons i rest ih =>
            intro w h
            simp only [List.foldl]
            rcases h with hw | hm
            · apply ih (CompCert4Lean.Backend.Unusedglob.add_ref_init_data w i)
              left
              unfold CompCert4Lean.Backend.Unusedglob.add_ref_init_data
              cases i with
              | Init_addrof id0 ofs0 =>
                  exact seen_workset_incl _ _ id'
                    (add_workset_incl id0 w) hw
              | Init_int8 value => exact hw
              | Init_int16 value => exact hw
              | Init_int32 value => exact hw
              | Init_int64 value => exact hw
              | Init_float32 value => exact hw
              | Init_float64 value => exact hw
              | Init_space size => exact hw
            · simp only [List.mem_cons] at hm
              rcases hm with rfl | hm
              · apply ih (CompCert4Lean.Backend.Unusedglob.add_ref_init_data w
                  (CompCert4Lean.Common.AST.init_data.Init_addrof id' ofs))
                left
                unfold CompCert4Lean.Backend.Unusedglob.add_ref_init_data
                exact seen_add_workset id' w
              · exact ih (CompCert4Lean.Backend.Unusedglob.add_ref_init_data w i)
                  (Or.inr hm)
      exact hfold gv.gvar_init w (Or.inr hmem)

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST

theorem seen_main_initial_workset : seen_main_initial_worksetStatement := by
  intro p
  unfold CompCert4Lean.Backend.Unusedglob.initial_workset
  exact seen_add_workset p.prog_main
    (p.prog_public.foldl
      (fun w id => CompCert4Lean.Backend.Unusedglob.add_workset id w)
      { w_seen := CompCert4Lean.Backend.Unusedglob.IS.empty, w_todo := [] })

theorem seen_public_initial_workset : seen_public_initial_worksetStatement := by
  intro p id hid
  unfold CompCert4Lean.Backend.Unusedglob.initial_workset
  apply seen_workset_incl _ _ id
    (add_workset_incl p.prog_main _)
  have hEq : ∀ (l : List ident) (w : workset),
      l.foldl (fun w id => CompCert4Lean.Backend.Unusedglob.add_workset id w) w =
        CompCert4Lean.Backend.Unusedglob.addlist_workset l w := by
    intro l
    induction l with
    | nil => intro w; rfl
    | cons x xs ih =>
        intro w
        simp only [List.foldl,
          CompCert4Lean.Backend.Unusedglob.addlist_workset]
        exact ih (CompCert4Lean.Backend.Unusedglob.add_workset x w)
  have hfold : ∀ (l : List ident) (w : workset),
      id ∈ l → IS.In id
        (l.foldl (fun w id => CompCert4Lean.Backend.Unusedglob.add_workset id w) w).w_seen := by
    intro l
    induction l with
    | nil => intro w h; cases h
    | cons x xs ih =>
        intro w h
        simp only [List.mem_cons] at h
        simp only [List.foldl]
        rcases h with rfl | h
        · rw [hEq]
          exact seen_workset_incl _ _ id
            (addlist_workset_incl xs
              (CompCert4Lean.Backend.Unusedglob.add_workset id w))
            (seen_add_workset id w)
        · exact ih (CompCert4Lean.Backend.Unusedglob.add_workset x w) h
  exact hfold p.prog_public
    { w_seen := CompCert4Lean.Backend.Unusedglob.IS.empty, w_todo := [] } hid

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST

theorem used_globals_incl : used_globals_inclStatement := by
  intro p u h
  unfold CompCert4Lean.Backend.Unusedglob.used_globals at h
  have hprop := CompCert4Lean.Lib.Iteration.PrimIter.iterate_prop
    workset IS.t
    (CompCert4Lean.Backend.Unusedglob.iter_step
      (CompCert4Lean.Common.AST.prog_defmap p))
    (fun w => IS.Subset (initial_workset p).w_seen w.w_seen)
    (fun u => IS.Subset (initial_workset p).w_seen u)
    (by
      intro w hw
      cases hstep : CompCert4Lean.Backend.Unusedglob.iter_step
          (CompCert4Lean.Common.AST.prog_defmap p) w with
      | inl u =>
          simp only
          unfold CompCert4Lean.Backend.Unusedglob.iter_step at hstep
          cases htodo : w.w_todo with
          | nil =>
              simp [htodo] at hstep
              cases hstep
              exact hw
          | cons id rem =>
              simp [htodo] at hstep
      | inr w' =>
          simp only
          unfold CompCert4Lean.Backend.Unusedglob.iter_step at hstep
          cases htodo : w.w_todo with
          | nil =>
              simp [htodo] at hstep
          | cons id rem =>
              simp only [htodo] at hstep
              injection hstep with hw'
              subst w'
              intro x hx
              exact seen_workset_incl
                { w_seen := w.w_seen, w_todo := rem }
                (CompCert4Lean.Backend.Unusedglob.add_ref_definition
                  (CompCert4Lean.Common.AST.prog_defmap p) id
                  { w_seen := w.w_seen, w_todo := rem })
                x
                (add_ref_definition_incl
                  (CompCert4Lean.Common.AST.prog_defmap p) id
                  { w_seen := w.w_seen, w_todo := rem })
                (hw x hx))
  unfold CompCert4Lean.Lib.Iteration.PrimIter.iterate_propStatement at hprop
  exact hprop (initial_workset p) u h (by
    intro id hid
    exact hid)

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Unusedglob

theorem filter_globdefs_accu : filter_globdefs_accuStatement := by
  intro defs
  induction defs with
  | nil =>
      intro accu1 accu2 u
      rfl
  | cons idg rest ih =>
      intro accu1 accu2 u
      cases idg with
      | mk id gd =>
          unfold CompCert4Lean.Backend.Unusedglob.filter_globdefs
          split
          · simpa [List.cons_append] using
              ih ((id, gd) :: accu1) accu2
                (CompCert4Lean.Backend.Unusedglob.IS.remove id u)
          · simpa [List.cons_append] using ih accu1 accu2 u

theorem filter_globdefs_nil : filter_globdefs_nilStatement := by
  intro u accu defs
  simpa using (filter_globdefs_accu defs [] accu u)

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST

theorem used_globals_valid : used_globals_validStatement := by
  intro p u h hdef
  have hsound : used_set_closed p u := by
    unfold CompCert4Lean.Backend.Unusedglob.used_globals at h
    have hprop := CompCert4Lean.Lib.Iteration.PrimIter.iterate_prop
      workset IS.t
      (CompCert4Lean.Backend.Unusedglob.iter_step
        (CompCert4Lean.Common.AST.prog_defmap p))
      (fun w => workset_invariant p w)
      (fun u => used_set_closed p u)
      (by
        intro w hw
        cases hstep : CompCert4Lean.Backend.Unusedglob.iter_step
            (CompCert4Lean.Common.AST.prog_defmap p) w with
        | inl u' =>
            simp only
            unfold CompCert4Lean.Backend.Unusedglob.iter_step at hstep
            cases htodo : w.w_todo with
            | nil =>
                simp [htodo] at hstep
                cases hstep
                unfold used_set_closed
                intro id gd id' hseen hget href
                apply hw id gd id' hseen
                · rw [htodo]
                  exact List.not_mem_nil
                · exact hget
                · exact href
            | cons id rem =>
                simp [htodo] at hstep
        | inr w' =>
            simp only
            unfold CompCert4Lean.Backend.Unusedglob.iter_step at hstep
            cases htodo : w.w_todo with
            | nil =>
                simp [htodo] at hstep
            | cons id rem =>
                simp only [htodo] at hstep
                injection hstep with hw'
                subst w'
                unfold workset_invariant at hw ⊢
                intro id0 gd id' hseen hnot_todo hget href
                have hwi := add_ref_definition_incl
                  (CompCert4Lean.Common.AST.prog_defmap p) id
                  { w_seen := w.w_seen, w_todo := rem }
                cases hwi with
                | workset_incl_intro seen todo track =>
                    by_cases heq : id = id0
                    · subst id0
                      exact seen_add_ref_definition
                        (CompCert4Lean.Common.AST.prog_defmap p) id gd id'
                        { w_seen := w.w_seen, w_todo := rem } hget href
                    · have htrack := track id0 hseen
                      rcases htrack with hbase | hnew
                      · have hnot_rem : ¬ id0 ∈ rem := by
                          intro hrem
                          exact hnot_todo (todo id0 hrem)
                        have hnot_orig : ¬ id0 ∈ w.w_todo := by
                          intro horig
                          have horig'' : id0 ∈ id :: rem := by
                            simpa [htodo] using horig
                          have horig' : id0 = id ∨ id0 ∈ rem :=
                            List.mem_cons.mp horig''
                          rcases horig' with horig | horig
                          · exact heq horig.symm
                          · exact hnot_rem horig
                        have hout := hw id0 gd id' hbase hnot_orig hget href
                        exact seen_workset_incl
                          { w_seen := w.w_seen, w_todo := rem }
                          (CompCert4Lean.Backend.Unusedglob.add_ref_definition
                            (CompCert4Lean.Common.AST.prog_defmap p) id
                            { w_seen := w.w_seen, w_todo := rem })
                          id' (workset_incl_intro seen todo track) hout
                      · exact False.elim (hnot_todo hnew))
    unfold CompCert4Lean.Lib.Iteration.PrimIter.iterate_propStatement at hprop
    exact hprop (initial_workset p) u h (by
      unfold workset_invariant
      intro id gd id' hseen hnot_todo hget href
      have hwi := initial_workset_incl p
      cases hwi with
      | workset_incl_intro seen todo track =>
          rcases track id hseen with hempty | htodo
          · exact False.elim
              (CompCert4Lean.Backend.Unusedglob.IS.empty_1_proof id hempty)
          · exact False.elim (hnot_todo htodo))
  have hincl := used_globals_incl p u h
  constructor
  · exact hsound
  · exact hincl p.prog_main (seen_main_initial_workset p)
  · intro id hid
    exact hincl id (seen_public_initial_workset p id hid)
  · intro id hid
    have hall := (ISF.for_all_iff_proof u (global_defined p
      (CompCert4Lean.Common.AST.prog_defmap p)) (by
        intro x y hxy
        change x = y at hxy
        subst y
        rfl))
    have hpred := hall.mpr hdef
    have hdefined := hpred id hid
    unfold CompCert4Lean.Backend.Unusedglob.global_defined at hdefined
    cases hget : CompCert4Lean.Lib.Maps.PTree.get id
        (CompCert4Lean.Common.AST.prog_defmap p) with
    | none =>
        simp [hget] at hdefined
        cases hEq : CompCert4Lean.Common.AST.ident_eq id p.prog_main with
        | left heq =>
            simp [hEq] at hdefined
            exact Or.inr heq
        | right hne =>
            simp [hEq] at hdefined
    | some gd =>
        left
        have hmem := CompCert4Lean.Common.AST.in_prog_defmap
          (CompCert4Lean.Backend.RTL.fundef) Unit p id gd hget
        exact List.mem_map.mpr ⟨(id, gd), hmem, rfl⟩

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Unusedglob

theorem filter_globdefs_map_1 : filter_globdefs_map_1Statement := by
  intro id l u m1
  unfold CompCert4Lean.Backend.Unusedglob.prog_map at m1
  unfold CompCert4Lean.Lib.Maps.PTree.t at m1
  induction l generalizing u m1 with
  | nil =>
      intro hmem hget
      simpa [CompCert4Lean.Backend.Unusedglob.filter_globdefs,
        List.foldl] using hget
  | cons idg l ih =>
      intro hmem hget
      rcases idg with ⟨id1, gd1⟩
      unfold CompCert4Lean.Backend.Unusedglob.filter_globdefs
      split
      · rename_i hbranch
        have hne : id ≠ id1 := by
          intro heq
          subst id1
          simp [hmem] at hbranch
        rw [filter_globdefs_nil]
        change CompCert4Lean.Lib.Maps.PTree.get id
          (List.foldl
            (fun (m : CompCert4Lean.Lib.Maps.PTree.tree
                (CompCert4Lean.Common.AST.globdef CompCert4Lean.Backend.RTL.fundef Unit))
                (idg : CompCert4Lean.Common.AST.ident ×
                  CompCert4Lean.Common.AST.globdef CompCert4Lean.Backend.RTL.fundef Unit) =>
              CompCert4Lean.Lib.Maps.PTree.set
                (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from idg.1)
                idg.2 m)
            m1
            (filter_globdefs (IS.remove (show IS.elt from id1) u) [] l ++ [(id1, gd1)])) = none
        rw [List.foldl_append]
        simp only [List.foldl]
        have hmem' : IS.mem id (IS.remove (show IS.elt from id1) u) = false := by
          change CompCert4Lean.Backend.Unusedglobproof.ISF.ISF.M.mem id
            (CompCert4Lean.Backend.Unusedglobproof.ISF.ISF.M.remove
              (show CompCert4Lean.Backend.Unusedglobproof.ISF.ISF.elt from id1) u) = false
          have hremove := ISF.remove_b_proof (s := u)
            (x := (show ISF.elt from id1)) (y := id)
          have hmem0 : CompCert4Lean.Backend.Unusedglobproof.ISF.ISF.M.mem id u = false := by
            exact hmem
          rw [hremove]
          simp [hmem0]
        have hrest := ih (IS.remove (show IS.elt from id1) u) m1 hmem' hget
        have hset := CompCert4Lean.Lib.Maps.PTree.getSet_equation
          (A := CompCert4Lean.Common.AST.globdef CompCert4Lean.Backend.RTL.fundef Unit)
          (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
          (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id1)
          gd1
          (List.foldl
            (fun (m : CompCert4Lean.Lib.Maps.PTree.tree
                (CompCert4Lean.Common.AST.globdef CompCert4Lean.Backend.RTL.fundef Unit))
                (idg : CompCert4Lean.Common.AST.ident ×
                  CompCert4Lean.Common.AST.globdef CompCert4Lean.Backend.RTL.fundef Unit) =>
              CompCert4Lean.Lib.Maps.PTree.set
                (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from idg.1)
                idg.2 m)
            m1 (filter_globdefs (IS.remove (show IS.elt from id1) u) [] l))
        rw [hset]
        split
        · rename_i heq
          exact False.elim (hne heq)
        · exact hrest
      · exact ih u m1 hmem hget

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Unusedglob

theorem filter_globdefs_map_2 : filter_globdefs_map_2Statement := by
  intro id l u m1 m2
  unfold CompCert4Lean.Backend.Unusedglob.prog_map at m1 m2
  unfold CompCert4Lean.Lib.Maps.PTree.t at m1 m2
  induction l generalizing u m1 m2 with
  | nil =>
      intro hmem hget
      simpa [CompCert4Lean.Backend.Unusedglob.filter_globdefs,
        List.foldl] using hget
  | cons idg l ih =>
      intro hmem hget
      rcases idg with ⟨id1, gd1⟩
      unfold CompCert4Lean.Backend.Unusedglob.filter_globdefs
      split
      · rename_i hbranch
        rw [filter_globdefs_nil]
        simp only [List.reverse_cons]
        change CompCert4Lean.Lib.Maps.PTree.get id
          (List.foldl
            (fun (m : CompCert4Lean.Lib.Maps.PTree.tree
                (CompCert4Lean.Common.AST.globdef CompCert4Lean.Backend.RTL.fundef Unit))
                (idg : CompCert4Lean.Common.AST.ident ×
                  CompCert4Lean.Common.AST.globdef CompCert4Lean.Backend.RTL.fundef Unit) =>
              CompCert4Lean.Lib.Maps.PTree.set
                (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from idg.1)
                idg.2 m)
            m1
            (filter_globdefs (IS.remove (show IS.elt from id1) u) [] l ++ [(id1, gd1)])) =
          CompCert4Lean.Lib.Maps.PTree.get
            (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
            (List.foldl
              (fun (m : CompCert4Lean.Lib.Maps.PTree.tree
                  (CompCert4Lean.Common.AST.globdef CompCert4Lean.Backend.RTL.fundef Unit))
                  (idg : CompCert4Lean.Common.AST.ident ×
                    CompCert4Lean.Common.AST.globdef CompCert4Lean.Backend.RTL.fundef Unit) =>
                CompCert4Lean.Lib.Maps.PTree.set
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from idg.1)
                  idg.2 m)
              m2 (List.reverse l ++ [(id1, gd1)]))
        rw [List.foldl_append]
        rw [List.foldl_append]
        simp only [List.foldl]
        change CompCert4Lean.Lib.Maps.PTree.get
            (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
            (CompCert4Lean.Lib.Maps.PTree.set
              (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id1)
              gd1 _) =
          CompCert4Lean.Lib.Maps.PTree.get
            (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
            (CompCert4Lean.Lib.Maps.PTree.set
              (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id1)
              gd1 _)
        rw [CompCert4Lean.Lib.Maps.PTree.getSet_equation,
          CompCert4Lean.Lib.Maps.PTree.getSet_equation]
        split
        · rfl
        · rename_i hne
          apply ih (IS.remove (show IS.elt from id1) u) m1 m2
          · change CompCert4Lean.Backend.Unusedglobproof.ISF.ISF.M.mem id
              (CompCert4Lean.Backend.Unusedglobproof.ISF.ISF.M.remove
                (show CompCert4Lean.Backend.Unusedglobproof.ISF.ISF.elt from id1) u) = true
            have hremove := ISF.remove_b_proof (s := u)
              (x := (show ISF.elt from id1)) (y := id)
            rw [hremove]
            have heq_false : ISF.eqb (show ISF.elt from id1) id = false := by
              cases h : ISF.ISF.E.eq_dec (show ISF.elt from id1) id with
              | left h' => exact False.elim (hne h'.symm)
              | right h' =>
                  simp [ISF.eqb, CompCert4Lean.Lib.FSetFacts.WFacts_fun.eqb, h]
            have hmem0 : ISF.ISF.M.mem id u = true := by
              exact hmem
            simp [hmem0, heq_false]
          · exact hget
      · rename_i hbranch
        have hne : id ≠ id1 := by
          intro heq
          subst id1
          simp [hmem] at hbranch
        simp only [List.reverse_cons]
        rw [List.foldl_append]
        simp only [List.foldl]
        rw [CompCert4Lean.Lib.Maps.PTree.gso _ _ hne]
        exact ih u m1 m2 hmem hget

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Unusedglob

theorem filter_globdefs_map : filter_globdefs_mapStatement := by
  intro id u defs
  unfold CompCert4Lean.Lib.Maps.PTree_Properties.of_list
  cases hmem : IS.mem id u with
  | true =>
      simp only [if_true]
      have h := filter_globdefs_map_2 id defs.reverse u
        (CompCert4Lean.Lib.Maps.PTree.empty _)
        (CompCert4Lean.Lib.Maps.PTree.empty _)
        hmem rfl
      rw [List.reverse_reverse] at h
      exact h
  | false =>
      apply filter_globdefs_map_1 id defs.reverse u
        (CompCert4Lean.Lib.Maps.PTree.empty _)
      · exact hmem
      · exact CompCert4Lean.Lib.Maps.PTree.gempty _ _

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib

private theorem list_norepet_append_singleton {A : Type} (l : List A) (a : A)
    (hnr : CompCert4Lean.Lib.Coqlib.list_norepet l)
    (hnot : ¬ a ∈ l) :
    CompCert4Lean.Lib.Coqlib.list_norepet (l ++ [a]) := by
  induction l with
  | nil =>
      exact CompCert4Lean.Lib.Coqlib.list_norepet.cons a (by simp)
        (CompCert4Lean.Lib.Coqlib.list_norepet.nil _)
  | cons hd tl ih =>
      cases hnr with
      | cons _ hhd htl =>
          simpa only [List.cons_append] using
            (CompCert4Lean.Lib.Coqlib.list_norepet.cons hd (by
              intro hmem
              apply hhd
              rcases List.mem_append.mp hmem with hmem | hmem
              · exact hmem
              · have heq : hd = a := List.mem_singleton.mp hmem
                exact False.elim (hnot (by simp [heq])))
              (ih htl (by
                intro hmem
                exact hnot (by simp [hmem]))))

private theorem filter_globdefs_domain_local :
    ∀ (id : CompCert4Lean.Common.AST.ident)
      (l : List (CompCert4Lean.Common.AST.ident ×
        CompCert4Lean.Common.AST.globdef CompCert4Lean.Backend.RTL.fundef Unit))
      (u : IS.t),
      id ∈ (filter_globdefs u [] l).map Prod.fst →
        IS.In id u ∧ id ∈ l.map Prod.fst := by
  intro id l
  induction l generalizing id with
  | nil =>
      intro u h
      exfalso
      simpa [CompCert4Lean.Backend.Unusedglob.filter_globdefs] using h
  | cons idg l ih =>
      rcases idg with ⟨id1, gd1⟩
      intro u h
      unfold CompCert4Lean.Backend.Unusedglob.filter_globdefs at h
      split at h
      · rename_i hmem
        rw [filter_globdefs_nil, List.map_append] at h
        rcases (List.mem_append.mp h) with htail | hhead
        · have hdom := ih id
            (CompCert4Lean.Backend.Unusedglob.IS.remove id1 u) htail
          have hremove := (ISF.remove_iff_proof u id1 id).mp hdom.1
          exact ⟨hremove.1, by simp [hdom.2]⟩
        · have heq : id = id1 := List.mem_singleton.mp hhead
          subst id
          exact ⟨CompCert4Lean.Backend.Unusedglob.IS.mem_2_proof u id1 hmem, by simp⟩
      · have hdom := ih id u h
        exact ⟨hdom.1, by simp [hdom.2]⟩

theorem filter_globdefs_unique_names : filter_globdefs_unique_namesStatement := by
  intro l u
  induction l generalizing u with
  | nil =>
      exact CompCert4Lean.Lib.Coqlib.list_norepet.nil _
  | cons idg l ih =>
      rcases idg with ⟨id1, gd1⟩
      unfold CompCert4Lean.Backend.Unusedglob.filter_globdefs
      split
      · rename_i hmem
        rw [filter_globdefs_nil]
        simp only [List.map_append, List.map_cons, List.map_nil]
        apply list_norepet_append_singleton
        · exact ih (CompCert4Lean.Backend.Unusedglob.IS.remove id1 u)
        · intro hmem'
          have hdom := filter_globdefs_domain_local id1 l
            (CompCert4Lean.Backend.Unusedglob.IS.remove id1 u) hmem'
          have hremove := (ISF.remove_iff_proof u id1 id1).mp hdom.1
          exact hremove.2 rfl
      · exact ih u

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST

theorem transf_program_match : transf_program_matchStatement := by
  intro p tp htrans
  unfold CompCert4Lean.Backend.Unusedglob.transform_program at htrans
  cases hused : CompCert4Lean.Backend.Unusedglob.used_globals p
      (CompCert4Lean.Common.AST.prog_defmap p) with
  | none => simp [hused] at htrans
  | some used =>
      cases hdef : CompCert4Lean.Backend.Unusedglob.IS.for_all
          (CompCert4Lean.Backend.Unusedglob.global_defined p
            (CompCert4Lean.Common.AST.prog_defmap p)) used with
      | false => simp [hused, hdef] at htrans
      | true =>
          simp [hused, hdef] at htrans
          cases htrans
          refine ⟨used, ?_, ?_⟩
          · apply used_globals_valid p used
            · exact hused
            · exact hdef
          · constructor
            · rfl
            · rfl
            · intro id
              exact filter_globdefs_map id used p.prog_defs
            · exact filter_globdefs_unique_names p.prog_defs.reverse used

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

theorem kept_closed : kept_closedStatement := by
  intro p used hvalid id gd id' hkept hget href
  unfold kept at hkept ⊢
  exact hvalid.used_closed id gd id' hkept hget href

theorem kept_main : kept_mainStatement := by
  intro p used hvalid
  unfold kept
  exact hvalid.used_main

end CompCert4Lean.Backend.Unusedglobproof
