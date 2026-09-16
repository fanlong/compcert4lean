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

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Maps

theorem kept_public : kept_publicStatement := by
  intro p used hvalid id hid
  exact hvalid.used_public id hid

theorem transform_find_symbol_1 : transform_find_symbol_1Statement := by
  intro p tp used hmatch id b hfind hkept
  have hdom : id ∈ prog_defs_names p :=
    Genv.find_symbol_inversion (F := RTL.fundef) (V := Unit)
      (p := p) (x := id) (b := b) hfind
  rcases prog_defmap_dom (F := RTL.fundef) (V := Unit) p id hdom with
    ⟨gd, hget⟩
  have hget' : PTree.get id (prog_defmap tp) = some gd := by
    rw [match_prog_def hmatch id]
    have hmem : IS.mem id used = true :=
      CompCert4Lean.Backend.Unusedglob.IS.mem_1_proof used id hkept
    simp [hmem, hget]
  rcases (Genv.find_def_symbol (F := RTL.fundef) (V := Unit)
      (p := tp) (id := id) (g := gd)).mp hget' with ⟨b', hsym, _⟩
  exact ⟨b', hsym⟩

theorem transform_find_symbol_2 : transform_find_symbol_2Statement := by
  intro p tp used hmatch id b hfind
  have hdom : id ∈ prog_defs_names tp :=
    Genv.find_symbol_inversion (F := RTL.fundef) (V := Unit)
      (p := tp) (x := id) (b := b) hfind
  rcases prog_defmap_dom (F := RTL.fundef) (V := Unit) tp id hdom with
    ⟨gd, hget_tp⟩
  have hrel := match_prog_def hmatch id
  rw [hget_tp] at hrel
  cases hmem : IS.mem id used with
  | false => simp [hmem] at hrel
  | true =>
      have hget_p : PTree.get id (prog_defmap p) = some gd := by
        simpa [hmem] using hrel.symm
      have hkept : kept used id :=
        CompCert4Lean.Backend.Unusedglob.IS.mem_2_proof used id hmem
      rcases (Genv.find_def_symbol (F := RTL.fundef) (V := Unit)
          (p := p) (id := id) (g := gd)).mp hget_p with ⟨b', hsym, _⟩
      exact ⟨hkept, ⟨b', hsym⟩⟩

theorem init_meminj_eq : init_meminj_eqStatement := by
  intro p tp id b b' hfind hfind'
  unfold init_meminj
  rw [Genv.find_invert_symbol (F := RTL.fundef) (V := Unit)
      (ge := Genv.globalenv p) (id := id) (b := b) hfind]
  simp [hfind']

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Maps

theorem init_meminj_invert : init_meminj_invertStatement := by
  intro p tp b b' delta h
  unfold init_meminj at h
  cases hinv : Genv.invert_symbol (Genv.globalenv p) b with
  | none => simp [hinv] at h
  | some id =>
      cases hfind : Genv.find_symbol (Genv.globalenv tp) id with
      | none => simp [hinv, hfind] at h
      | some b'' =>
          have hpair : (b'', z0) = (b', delta) := by
            exact Option.some.inj (by simpa [hinv, hfind] using h)
          cases hpair
          refine ⟨rfl, id, ?_, hfind⟩
          exact Genv.invert_find_symbol (F := RTL.fundef) (V := Unit)
            (ge := Genv.globalenv p) (id := id) (b := b) hinv

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Globalenvs

open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps

theorem init_meminj_preserves_globals : init_meminj_preserves_globalsStatement := by
  intro p tp used hvalid hmatch
  constructor
  · intro id b b' delta hmap hfind
    have hinv := init_meminj_invert p tp b b' delta hmap
    rcases hinv with ⟨hdelta, id1, hfind1, hfind2⟩
    have hid : id1 = id :=
      (Genv.globalenv p).genv_vars_inj id1 id hfind1 hfind
    subst id1
    exact ⟨hdelta, hfind2⟩
  · intro id b hkept hfind
    rcases transform_find_symbol_1 p tp used hmatch id b hfind hkept with
      ⟨b', hfind'⟩
    exact ⟨b', hfind', init_meminj_eq p tp id b b' hfind hfind'⟩
  · intro id b' hfind'
    rcases transform_find_symbol_2 p tp used hmatch id b' hfind' with
      ⟨hkept, b, hfind⟩
    exact ⟨b, hfind, init_meminj_eq p tp id b b' hfind hfind'⟩
  · intro b b' delta gd hmap hdef
    have hinv := init_meminj_invert p tp b b' delta hmap
    rcases hinv with ⟨hdelta, id, hfind, hfind'⟩
    have hkept : kept used id :=
      (transform_find_symbol_2 p tp used hmatch id b' hfind').1
    have hget : PTree.get id (prog_defmap p) = some gd :=
      (Genv.find_def_symbol (F := RTL.fundef) (V := Unit)
        (p := p) (id := id) (g := gd)).2 ⟨b, hfind, hdef⟩
    have hmem : IS.mem id used = true :=
      CompCert4Lean.Backend.Unusedglob.IS.mem_1_proof used id hkept
    have hget' : PTree.get id (prog_defmap tp) = some gd := by
      rw [match_prog_def hmatch id]
      simp [hmem, hget]
    rcases (Genv.find_def_symbol (F := RTL.fundef) (V := Unit)
      (p := tp) (id := id) (g := gd)).mp hget' with ⟨b1, hfind1, hdef1⟩
    have hb : b' = b1 := Option.some.inj (hfind'.symm.trans hfind1)
    subst b1
    exact ⟨hdef1, hdelta, by
      intro id' href
      exact kept_closed p used hvalid id gd id' hkept hget
        href⟩
  · intro b b' delta gd hmap hdef'
    have hinv := init_meminj_invert p tp b b' delta hmap
    rcases hinv with ⟨hdelta, id, hfind, hfind'⟩
    have hget' : PTree.get id (prog_defmap tp) = some gd :=
      (Genv.find_def_symbol (F := RTL.fundef) (V := Unit)
        (p := tp) (id := id) (g := gd)).2 ⟨b', hfind', hdef'⟩
    rw [match_prog_def hmatch id] at hget'
    cases hmem : IS.mem id used with
    | false => simp [hmem] at hget'
    | true =>
        have hget : PTree.get id (prog_defmap p) = some gd := by
          simpa [hmem] using hget'
        rcases (Genv.find_def_symbol (F := RTL.fundef) (V := Unit)
          (p := p) (id := id) (g := gd)).mp hget with ⟨b1, hfind1, hdef1⟩
        have hb : b = b1 := Option.some.inj (hfind.symm.trans hfind1)
        subst b1
        exact ⟨hdef1, hdelta⟩

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps
open Lean Elab Tactic Meta

private def unusedglobPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem unusedglob_wordcore_add_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.add x y).val =
      (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (unusedglobPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem unusedglob_wordcore_zero_val (bits : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.zero bits).val = 0 := by
  unfold CompCert4Lean.Lib.Integers.WordCore.zero
  run_tac
    let lctx ← getLCtx
    let bF := (lctx.findFromUserName? `bits).get!
    let e ← mkAppM
      (unusedglobPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")
      #[mkFVar bF.fvarId,
        mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0]
    closeMainGoal Name.anonymous e

private theorem unusedglob_wordcore_val_lt
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    x.val < 2 ^ bits := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (unusedglobPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e

private theorem unusedglob_ptrofs_add_zero_repr
    (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add ofs
      (CompCert4Lean.Lib.Integers.Ptrofs.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0)) = ofs := by
  change CompCert4Lean.Lib.Integers.WordCore.add ofs
    (CompCert4Lean.Lib.Integers.WordCore.zero
      CompCert4Lean.Lib.Integers.Ptrofs.wordsize) = ofs
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [unusedglob_wordcore_add_val, unusedglob_wordcore_zero_val, Nat.add_zero]
  exact Nat.mod_eq_of_lt (unusedglob_wordcore_val_lt ofs)

theorem symbol_address_inject : symbol_address_injectStatement := by
  intro p tp used j id ofs hj hkept
  change Val.inject j
    (Genv.symbol_address (Genv.globalenv p) id ofs)
    (Genv.symbol_address (Genv.globalenv tp) id ofs)
  unfold Genv.symbol_address
  cases hfind : Genv.find_symbol (Genv.globalenv p) id with
  | none =>
      simp only [hfind]
      exact Val.val_inject_undef j _
  | some b =>
      rcases hj.symbols_inject_2 id b hkept hfind with
        ⟨b', hfind', hmap⟩
      simp only [hfind, hfind']
      refine Val.inject_ptr j b ofs b' ofs z0 hmap ?_
      exact (unusedglob_ptrofs_add_zero_repr ofs).symm

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

private theorem unusedglob_set_reg_inject_aux :
    ∀ (f : Val.meminj) (rs rs' : CompCert4Lean.Backend.RTL.regset)
      (r : reg) (v v' : val),
      regset_inject f rs rs' → Val.inject f v v' →
        regset_inject f (Regmap.set r v rs) (Regmap.set r v' rs') := by
  intro f rs rs' r v v' h hv r0
  rw [@Regmap.gsspec_proof val r0 r v rs,
      @Regmap.gsspec_proof val r0 r v' rs']
  cases peq r0 r with
  | left heq =>
      subst r0
      simp
      exact hv
  | right hne =>
      simp [hne]
      exact h r0

theorem set_res_inject : set_res_injectStatement := by
  intro f rs rs' res v v' h hv
  cases res with
  | BR r => exact unusedglob_set_reg_inject_aux f rs rs' r v v' h hv
  | _ => exact h

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values

private theorem unusedglob_val_inject_incr
    (f f' : Val.meminj) (v v' : val)
    (hinc : inject_incr f f') (hval : Val.inject f v v') :
    Val.inject f' v v' := by
  cases hval with
  | inject_int i => exact Val.inject.inject_int i
  | inject_long i => exact Val.inject.inject_long i
  | inject_float f => exact Val.inject.inject_float f
  | inject_single f => exact Val.inject.inject_single f
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      exact Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta
        (hinc b1 b2 delta hmap) hofs
  | val_inject_undef v' => exact Val.inject.val_inject_undef v'

theorem regset_inject_incr : regset_inject_incrStatement := by
  intro f f' rs rs' hreg hinc r
  exact unusedglob_val_inject_incr f f' _ _ hinc (hreg r)

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem regset_undef_inject : regset_undef_injectStatement := by
  intro f r
  change Val.inject f (Regmap.get r (Regmap.init Vundef))
    (Regmap.get r (Regmap.init Vundef))
  rw [Regmap.gi_proof]
  exact Val.val_inject_undef f Vundef

theorem init_regs_inject : init_regs_injectStatement := by
  intro f args args' hargs params
  induction hargs generalizing params with
  | inject_list_nil =>
      cases params with
      | nil =>
          intro r
          change Val.inject f (Regmap.get r (Regmap.init Vundef))
            (Regmap.get r (Regmap.init Vundef))
          rw [Regmap.gi_proof]
          exact Val.val_inject_undef f Vundef
      | cons r rs =>
          intro r0
          change Val.inject f (Regmap.get r0 (Regmap.init Vundef))
            (Regmap.get r0 (Regmap.init Vundef))
          rw [Regmap.gi_proof]
          exact Val.val_inject_undef f Vundef
  | inject_list_cons v v' vs vs' hv hvs ih =>
      cases params with
      | nil =>
          intro r
          change Val.inject f (Regmap.get r (Regmap.init Vundef))
            (Regmap.get r (Regmap.init Vundef))
          rw [Regmap.gi_proof]
          exact Val.val_inject_undef f Vundef
      | cons r rs =>
          intro r0
          change Val.inject f
            (Regmap.get r0 (Regmap.set r v (RTL.init_regs vs rs)))
            (Regmap.get r0 (Regmap.set r v' (RTL.init_regs vs' rs)))
          rw [@Regmap.gsspec_proof val r0 r v (RTL.init_regs vs rs),
            @Regmap.gsspec_proof val r0 r v' (RTL.init_regs vs' rs)]
          cases peq r0 r with
          | left heq =>
              subst r0
              simp
              exact hv
          | right hne =>
              simp [hne]
              exact ih rs r0

theorem match_stacks_preserves_globals : match_stacks_preserves_globalsStatement := by
  intro p tp used j s ts bound tbound h
  induction h with
  | match_stacks_nil bound tbound globals source_bound target_bound =>
      exact globals
  | match_stacks_cons res f sp pc rs s tsp trs ts bound tbound stacks refs_kept
      sp_inject regs below target_below ih =>
      exact ih

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem match_stacks_incr : match_stacks_incrStatement := by
  intro p tp used j j' hinc s ts bound tbound hstacks
  induction hstacks with
  | match_stacks_nil bound tbound globals source_bound target_bound =>
      intro hnew
      have same_source : ∀ (b b' : block) (delta : Z),
          Plt b (Genv.globalenv p).genv_next →
          j' b = some (b', delta) →
          j b = some (b', delta) := by
        intro b b' delta hb hmap
        cases hj : j b with
        | none =>
            have hbounds := hnew b b' delta hj hmap
            have hbad : Plt b b :=
              Plt_Ple_trans b (Genv.globalenv p).genv_next b hb
                (Ple_trans _ _ _ source_bound hbounds.1)
            exact (Plt_strict b hbad).elim
        | some pair =>
            rcases pair with ⟨b1, delta1⟩
            have heq : (b1, delta1) = (b', delta) :=
              Option.some.inj ((hinc b b1 delta1 hj).symm.trans hmap)
            cases heq
            rfl
      have same_target : ∀ (b b' : block) (delta : Z),
          Plt b' (Genv.globalenv tp).genv_next →
          j' b = some (b', delta) →
          j b = some (b', delta) := by
        intro b b' delta hb hmap
        cases hj : j b with
        | none =>
            have hbounds := hnew b b' delta hj hmap
            have hbad : Plt b' b' :=
              Plt_Ple_trans b' (Genv.globalenv tp).genv_next b' hb
                (Ple_trans _ _ _ target_bound hbounds.2)
            exact (Plt_strict b' hbad).elim
        | some pair =>
            rcases pair with ⟨b1, delta1⟩
            have heq : (b1, delta1) = (b', delta) :=
              Option.some.inj ((hinc b b1 delta1 hj).symm.trans hmap)
            cases heq
            rfl
      refine match_stacks_nil bound tbound ?_ source_bound target_bound
      refine {
        symbols_inject_1 := ?_,
        symbols_inject_2 := ?_,
        symbols_inject_3 := ?_,
        defs_inject := ?_,
        defs_rev_inject := ?_ }
      · intro id b b' delta hmap hfind
        exact globals.symbols_inject_1 id b b' delta
          (same_source b b' delta ((Genv.globalenv p).genv_symb_range id hfind) hmap)
          hfind
      · intro id b hkept hfind
        rcases globals.symbols_inject_2 id b hkept hfind with
          ⟨b', hfind', hmap⟩
        exact ⟨b', hfind', hinc b b' z0 hmap⟩
      · intro id b' hfind
        rcases globals.symbols_inject_3 id b' hfind with
          ⟨b, hfind', hmap⟩
        exact ⟨b, hfind', hinc b b' z0 hmap⟩
      · intro b b' delta gd hmap hdef
        exact globals.defs_inject b b' delta gd
          (same_source b b' delta ((Genv.globalenv p).genv_defs_range b hdef) hmap)
          hdef
      · intro b b' delta gd hmap hdef
        exact globals.defs_rev_inject b b' delta gd
          (same_target b b' delta ((Genv.globalenv tp).genv_defs_range b' hdef) hmap)
          hdef
  | match_stacks_cons res f sp pc rs s tsp trs ts bound tbound stacks refs_kept
      sp_inject regs below target_below ih =>
      intro hnew
      refine match_stacks_cons res f sp pc rs s tsp trs ts bound tbound
        (ih ?_) refs_kept (hinc sp tsp z0 sp_inject)
        (regset_inject_incr j j' rs trs regs hinc) below target_below
      intro b1 b2 delta hmap hmap'
      have hbounds := hnew b1 b2 delta hmap hmap'
      exact ⟨Ple_trans sp bound b1 (Plt_Ple sp bound below) hbounds.1,
        Ple_trans tsp tbound b2 (Plt_Ple tsp tbound target_below) hbounds.2⟩

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Lib.Coqlib

theorem match_stacks_bound : match_stacks_boundStatement := by
  intro p tp used j s ts bound tbound bound' tbound' hstacks hbound htbound
  induction hstacks with
  | match_stacks_nil bound0 tbound0 globals source_bound target_bound =>
      exact match_stacks_nil bound' tbound' globals
        (Ple_trans _ _ _ source_bound hbound)
        (Ple_trans _ _ _ target_bound htbound)
  | match_stacks_cons res f sp pc rs s tsp trs ts bound0 tbound0 stacks refs_kept
      sp_inject regs below target_below ih =>
      exact match_stacks_cons res f sp pc rs s tsp trs ts bound' tbound'
        stacks
          refs_kept sp_inject regs
        (Plt_Ple_trans _ _ _ below hbound)
        (Plt_Ple_trans _ _ _ target_below htbound)

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values

theorem find_function_inject : find_function_injectStatement := by
  intro p tp used j ros rs fd trs hglobals hfind hcond
  cases ros with
  | inl r =>
      simp only [CompCert4Lean.Backend.RTL.find_function, Sum.rec] at hfind ⊢
      have hinv := Genv.find_funct_inv (F := fundef) (V := Unit)
        (ge := Genv.globalenv p) (v := Regmap.get r rs) (f := fd) hfind
      rcases hinv with ⟨b, hv⟩
      have hfind_v : Genv.find_funct (Genv.globalenv p)
          (Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero) = some fd := by
        simpa [hv] using hfind
      have hptr : Genv.find_funct_ptr (Genv.globalenv p) b = some fd :=
        (Genv.find_funct_find_funct_ptr (F := fundef) (V := Unit)
          (ge := Genv.globalenv p) (b := b)).symm.trans hfind_v
      have hval := hcond r
      generalize hsrc : Regmap.get r rs = sv at hval
      generalize htgt : Regmap.get r trs = tv at hval ⊢
      have hsv : sv = Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero :=
        hsrc.symm.trans hv
      rw [hsv] at hval
      cases hval with
      | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
          have hdef : Genv.find_def (Genv.globalenv p) b = some (.Gfun fd) :=
            (Genv.find_funct_ptr_iff (F := fundef) (V := Unit)
              (ge := Genv.globalenv p) (b := b) (f := fd)).mp hptr
          have hdefs := hglobals.defs_inject b b2 delta (.Gfun fd) hmap hdef
          rcases hdefs with ⟨hfind_def, hdelta, hrefs⟩
          have hptr_t : Genv.find_funct_ptr (Genv.globalenv tp) b2 = some fd :=
            (Genv.find_funct_ptr_iff (F := fundef) (V := Unit)
              (ge := Genv.globalenv tp) (b := b2) (f := fd)).mpr hfind_def
          have hfind_t : Genv.find_funct (Genv.globalenv tp)
              (Vptr b2 CompCert4Lean.Lib.Integers.Ptrofs.zero) = some fd := by
            exact (Genv.find_funct_find_funct_ptr (F := fundef) (V := Unit)
              (ge := Genv.globalenv tp) (b := b2)).trans hptr_t
          have hofs0 : ofs2 = CompCert4Lean.Lib.Integers.Ptrofs.zero := by
            rw [hdelta] at hofs
            rw [hofs]
            exact unusedglob_ptrofs_add_zero_repr _
          exact ⟨by simpa [hofs0] using hfind_t, hrefs⟩
  | inr id =>
      simp only [CompCert4Lean.Backend.RTL.find_function, Sum.rec] at hfind ⊢
      cases hs : Genv.find_symbol (Genv.globalenv p) id with
      | none => simp [hs] at hfind
      | some b =>
          have hptr : Genv.find_funct_ptr (Genv.globalenv p) b = some fd := by
            simpa [hs] using hfind
          rcases hglobals.symbols_inject_2 id b hcond hs with
            ⟨b', hsym', hmap⟩
          have hdef : Genv.find_def (Genv.globalenv p) b = some (.Gfun fd) :=
            (Genv.find_funct_ptr_iff (F := fundef) (V := Unit)
              (ge := Genv.globalenv p) (b := b) (f := fd)).mp hptr
          have hdefs := hglobals.defs_inject b b' z0 (.Gfun fd) hmap hdef
          rcases hdefs with ⟨hfind_def, hdelta, hrefs⟩
          have hptr_t : Genv.find_funct_ptr (Genv.globalenv tp) b' = some fd :=
            (Genv.find_funct_ptr_iff (F := fundef) (V := Unit)
              (ge := Genv.globalenv tp) (b := b') (f := fd)).mpr hfind_def
          exact ⟨by simpa [hs, hsym'] using hptr_t, hrefs⟩

end CompCert4Lean.Backend.Unusedglobproof
namespace CompCert4Lean.Backend.Unusedglobproof
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private abbrev evalInjectZ1 : Z := .Zpos .xH
private abbrev evalInjectZAdd := ZArith.BinInt.Z.add
private abbrev evalInjectZOfNat := ZArith.BinInt.Z.of_nat

private theorem evalInjectZAddInt (x y : Z) :
    intOfZ (evalInjectZAdd x y) = intOfZ x + intOfZ y := by
  change intOfZ (zOfInt (intOfZ x + intOfZ y)) = _
  rw [intOfZ_zOfInt]

private theorem evalInjectZOfNatInt (n : Nat) :
    intOfZ (evalInjectZOfNat n) = (n : Int) := by
  change intOfZ (zOfInt (Int.ofNat n)) = _
  rw [intOfZ_zOfInt]
  rfl
private theorem evalInjectZAddZero (x : Z) : evalInjectZAdd x .Z0 = x := by
  apply intOfZ_injective
  rw [evalInjectZAddInt]
  have hz : intOfZ (.Z0 : Z) = 0 := by rfl
  rw [hz, Int.add_zero]
private theorem evalInjectSizeChunk (chunk : memory_chunk) :
    size_chunk chunk = evalInjectZOfNat (size_chunk_nat chunk) := by
  cases chunk <;> rfl

private theorem evalInjectGetN
    (f : Val.meminj) (m1 m2 : mem) (b1 b2 : block) (delta : Z)
    (hinj : Mem.inject f m1 m2) (hmap : f b1 = some (b2, delta)) :
    ∀ n ofs,
      Mem.range_perm m1 b1 ofs (evalInjectZAdd ofs (evalInjectZOfNat n)) Cur Readable →
      list_forall2 (memval_inject f)
        (Mem.getN n ofs (PMap.get b1 m1.mem_contents))
        (Mem.getN n (evalInjectZAdd ofs delta) (PMap.get b2 m2.mem_contents)) := by
  intro n
  induction n with
  | zero => intro ofs h; constructor
  | succ n ih =>
      intro ofs hperm
      apply list_forall2.cons
      · apply hinj.mi_inj.mi_memval b1 ofs b2 delta hmap
        apply hperm
        constructor
        · change intOfZ ofs ≤ intOfZ ofs
          omega
        · change intOfZ ofs < intOfZ (evalInjectZAdd ofs (evalInjectZOfNat (Nat.succ n)))
          rw [evalInjectZAddInt, evalInjectZOfNatInt]
          omega
      · change list_forall2 (memval_inject f)
          (Mem.getN n (evalInjectZAdd ofs evalInjectZ1) (PMap.get b1 m1.mem_contents))
          (Mem.getN n (evalInjectZAdd (evalInjectZAdd ofs delta) evalInjectZ1)
            (PMap.get b2 m2.mem_contents))
        have hadd : evalInjectZAdd (evalInjectZAdd ofs delta) evalInjectZ1 =
            evalInjectZAdd (evalInjectZAdd ofs evalInjectZ1) delta := by
          apply intOfZ_injective
          rw [evalInjectZAddInt, evalInjectZAddInt, evalInjectZAddInt, evalInjectZAddInt]
          have hone : intOfZ evalInjectZ1 = 1 := by decide
          rw [hone]
          omega
        rw [hadd]
        apply ih (evalInjectZAdd ofs evalInjectZ1)
        intro q hq
        rcases hq with ⟨hqlo, hqhi⟩
        apply hperm
        constructor
        · change intOfZ ofs ≤ intOfZ q
          change intOfZ (evalInjectZAdd ofs evalInjectZ1) ≤ intOfZ q at hqlo
          rw [evalInjectZAddInt] at hqlo
          have hone : intOfZ evalInjectZ1 = 1 := by decide
          rw [hone] at hqlo
          omega
        · change intOfZ q < intOfZ (evalInjectZAdd ofs (evalInjectZOfNat (Nat.succ n)))
          change intOfZ q <
            intOfZ (evalInjectZAdd (evalInjectZAdd ofs evalInjectZ1) (evalInjectZOfNat n)) at hqhi
          rw [evalInjectZAddInt, evalInjectZAddInt, evalInjectZOfNatInt] at hqhi
          rw [evalInjectZAddInt, evalInjectZOfNatInt]
          have hone : intOfZ evalInjectZ1 = 1 := by decide
          rw [hone] at hqhi
          omega

private theorem evalInjectLoadZero
    (f : Val.meminj) (m1 m2 : mem) (chunk : memory_chunk)
    (b1 b2 : block) (ofs : Z) (v1 : val) :
    Mem.inject f m1 m2 →
    Mem.load chunk m1 b1 ofs = some v1 →
    f b1 = some (b2, .Z0) →
    ∃ v2, Mem.load chunk m2 b2 ofs = some v2 ∧ Val.inject f v1 v2 := by
  intro hinj hload hmap
  have hacc := Mem.load_valid_access m1 chunk b1 ofs v1 hload
  have hget : list_forall2 (memval_inject f)
      (Mem.getN (size_chunk_nat chunk) ofs (PMap.get b1 m1.mem_contents))
      (Mem.getN (size_chunk_nat chunk) ofs (PMap.get b2 m2.mem_contents)) := by
    have h := evalInjectGetN f m1 m2 b1 b2 .Z0 hinj hmap
      (size_chunk_nat chunk) ofs (by
        rw [← evalInjectSizeChunk]
        exact hacc.1)
    rw [evalInjectZAddZero] at h
    exact h
  have hacc2 : Mem.valid_access m2 chunk b2 ofs Readable := by
    constructor
    · intro q hq
      have hp := hinj.mi_inj.mi_perm b1 b2 .Z0 q Cur Readable hmap
        (hacc.1 q hq)
      simpa only [evalInjectZAddZero] using hp
    · exact hacc.2
  have hload1 : decode_val chunk
      (Mem.getN (size_chunk_nat chunk) ofs (PMap.get b1 m1.mem_contents)) = v1 :=
    (Mem.load_result chunk m1 b1 ofs v1 hload).symm
  let v2 := decode_val chunk
    (Mem.getN (size_chunk_nat chunk) ofs (PMap.get b2 m2.mem_contents))
  refine ⟨v2, ?_, ?_⟩
  · unfold Mem.load
    cases hdec : Mem.valid_access_dec m2 chunk b2 ofs Readable with
    | left _ =>
        change (if true then some v2 else none) = some v2
        simp [v2]
    | right hn => exact False.elim (hn hacc2)
  · subst v1
    exact decode_val_inject f _ _ chunk hget

private theorem evalInjectPtrofsAddZero (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add ofs
      (CompCert4Lean.Lib.Integers.Ptrofs.repr (.Z0)) = ofs := by
  exact unusedglob_ptrofs_add_zero_repr ofs

private theorem evalInjectOffsetPtr (f : Val.meminj) (v v' : val) (ofs : Ptrofs.int) :
    Val.inject f v v' → Val.inject f (Val.offset_ptr v ofs) (Val.offset_ptr v' ofs) := by
  intro h
  cases h with
  | inject_int i => exact Val.val_inject_undef f _
  | inject_long i => exact Val.val_inject_undef f _
  | inject_float x => exact Val.val_inject_undef f _
  | inject_single x => exact Val.val_inject_undef f _
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      simp [Val.offset_ptr]
      apply Val.inject_ptr f b1 _ b2 _ delta hmap
      subst ofs2
      simp only [Ptrofs.add_commut_proof_api, Ptrofs.add_assoc_proof_api]
  | val_inject_undef v => exact Val.val_inject_undef f _

private theorem evalInjectLongofwords (f : Val.meminj) (v1 v1' v2 v2' : val) :
    Val.inject f v1 v1' → Val.inject f v2 v2' →
      Val.inject f (Val.longofwords v1 v2) (Val.longofwords v1' v2') := by
  intro h1 h2
  cases h1 <;> cases h2 <;> simp [Val.longofwords] <;> constructor

private theorem evalInjectAdd (f : Val.meminj) (v1 v1' v2 v2' : val) :
    Val.inject f v1 v1' → Val.inject f v2 v2' →
      Val.inject f (Val.add v1 v2) (Val.add v1' v2') := by
  intro h1 h2
  cases h1 <;> cases h2 <;>
    simp [Val.add, CompCert4Lean.X86_64.Archi.ptr64] <;>
    constructor <;> try assumption
  all_goals
    subst_vars
    rw [Ptrofs.add_assoc_proof_api, Ptrofs.add_commut_proof_api]

theorem eval_builtin_arg_inject : eval_builtin_arg_injectStatement := by
  intro p tp used rs sp m j rs' sp' m' a v hEval hsp hglobals hregs hmem hkeep
  induction hEval with
  | eval_BA x =>
      refine ⟨Regmap.get x rs', eval_BA x, hregs x⟩
  | eval_BA_int n => exact ⟨Vint n, eval_BA_int n, Val.inject_int j n⟩
  | eval_BA_long n => exact ⟨Vlong n, eval_BA_long n, Val.inject_long j n⟩
  | eval_BA_float n => exact ⟨Vfloat n, eval_BA_float n, Val.inject_float j n⟩
  | eval_BA_single n => exact ⟨Vsingle n, eval_BA_single n, Val.inject_single j n⟩
  | eval_BA_loadstack chunk ofs v load =>
      simp [Mem.loadv, Val.offset_ptr] at load
      rcases evalInjectLoadZero j m m' chunk sp sp'
          (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs)) v hmem load hsp with
        ⟨v', hload', hinj'⟩
      refine ⟨v', ?_, hinj'⟩
      apply eval_BA_loadstack
      simpa [Mem.loadv, Val.offset_ptr] using hload'
  | eval_BA_addrstack ofs =>
      have hbase : Val.inject j (Vptr sp Ptrofs.zero) (Vptr sp' Ptrofs.zero) :=
        Val.inject_ptr j sp Ptrofs.zero sp' Ptrofs.zero .Z0 hsp
          ((evalInjectPtrofsAddZero Ptrofs.zero).symm)
      refine ⟨Val.offset_ptr (Vptr sp' Ptrofs.zero) ofs, eval_BA_addrstack ofs, ?_⟩
      exact evalInjectOffsetPtr j _ _ ofs hbase
  | eval_BA_loadglobal chunk id ofs v load =>
      have hkid : kept used id := hkeep id (by simp [globals_of_builtin_arg])
      change Mem.loadv chunk m (Genv.symbol_address (Genv.globalenv p) id ofs) = some v at load
      unfold Genv.symbol_address at load
      cases hfind : Genv.find_symbol (Genv.globalenv p) id with
      | none => simp [hfind, Mem.loadv] at load
      | some b =>
          rcases hglobals.symbols_inject_2 id b hkid hfind with ⟨b', hfind', hmap⟩
          simp only [hfind] at load
          simp [Mem.loadv] at load
          rcases evalInjectLoadZero j m m' chunk b b' (Ptrofs.unsigned ofs) v
              hmem load hmap with ⟨v', hload', hinj'⟩
          refine ⟨v', ?_, hinj'⟩
          apply eval_BA_loadglobal
          change Mem.loadv chunk m' (Genv.symbol_address (Genv.globalenv tp) id ofs) = some v'
          unfold Genv.symbol_address
          simp [hfind', Mem.loadv, hload']
  | eval_BA_addrglobal id ofs =>
      have hkid : kept used id := hkeep id (by simp [globals_of_builtin_arg])
      refine ⟨Genv.symbol_address (Genv.globalenv tp) id ofs, ?_, ?_⟩
      · change eval_builtin_arg (Genv.to_senv (Genv.globalenv tp))
          (fun r => Regmap.get r rs') (Vptr sp' Ptrofs.zero) m'
          (BA_addrglobal id ofs) (Senv.symbol_address (Genv.to_senv (Genv.globalenv tp)) id ofs)
        exact eval_BA_addrglobal id ofs
      · exact symbol_address_inject p tp used j id ofs hglobals hkid
  | eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      rcases ihhi (by
        intro id hid
        apply hkeep id
        simp [globals_of_builtin_arg, hid]) with ⟨vhi', hhi', hinjhi⟩
      rcases ihlo (by
        intro id hid
        apply hkeep id
        simp [globals_of_builtin_arg, hid]) with ⟨vlo', hlo', hinjlo⟩
      refine ⟨Val.longofwords vhi' vlo', eval_BA_splitlong hi lo vhi' vlo' hhi' hlo', ?_⟩
      exact evalInjectLongofwords j vhi vhi' vlo vlo' hinjhi hinjlo
  | eval_BA_addptr a1 a2 v1 v2 h1 h2 ih1 ih2 =>
      rcases ih1 (by
        intro id hid
        apply hkeep id
        simp [globals_of_builtin_arg, hid]) with ⟨v1', h1', hinj1⟩
      rcases ih2 (by
        intro id hid
        apply hkeep id
        simp [globals_of_builtin_arg, hid]) with ⟨v2', h2', hinj2⟩
      refine ⟨if CompCert4Lean.X86_64.Archi.ptr64 then Val.addl v1' v2' else Val.add v1' v2',
        eval_BA_addptr a1 a2 v1' v2' h1' h2', ?_⟩
      cases hp : CompCert4Lean.X86_64.Archi.ptr64
      · simp [hp]
        exact evalInjectAdd j v1 v1' v2 v2' hinj1 hinj2
      · simp [hp]
        exact Val.addl_inject j v1 v1' v2 v2' hinj1 hinj2
end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem eval_builtin_args_inject : eval_builtin_args_injectStatement := by
  intro p tp used rs sp m j rs' sp' m' al vl hEval hsp hglobals hregs hmem hkeep
  unfold eval_builtin_args at hEval ⊢
  induction hEval with
  | nil =>
      exact ⟨[], list_forall2_nil _, Val.inject_list_nil j⟩
  | @cons a al v vl ha htail ih =>
      have hkeep_a : ∀ id, id ∈ globals_of_builtin_arg a → kept used id := by
        intro id hid
        apply hkeep id
        change id ∈ globals_of_builtin_arg a ++ globals_of_builtin_args al
        exact List.mem_append.mpr (Or.inl hid)
      obtain ⟨v', ha', hinj⟩ :=
        eval_builtin_arg_inject p tp used rs sp m j rs' sp' m' a v ha hsp
          hglobals hregs hmem hkeep_a
      have hkeep_tail : ∀ id, id ∈ globals_of_builtin_args al → kept used id := by
        intro id hid
        apply hkeep id
        change id ∈ globals_of_builtin_arg a ++ globals_of_builtin_args al
        exact List.mem_append.mpr (Or.inr hid)
      obtain ⟨vl', htail', hinjtail⟩ := ih hkeep_tail
      exact ⟨v' :: vl', list_forall2.cons _ _ ha' htail',
        Val.inject_list_cons j v v' vl vl' hinj hinjtail⟩

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Maps

theorem init_meminj_invert_strong : init_meminj_invert_strongStatement := by
  intro p tp used hvalid hmatch b b' delta hmap
  rcases init_meminj_invert p tp b b' delta hmap with
    ⟨hdelta, id, hfind, hfind'⟩
  have hdom : id ∈ prog_defs_names p :=
    Genv.find_symbol_inversion (F := RTL.fundef) (V := Unit)
      (p := p) (x := id) (b := b) hfind
  rcases prog_defmap_dom (F := RTL.fundef) (V := Unit) p id hdom with
    ⟨gd, hget⟩
  rcases (Genv.find_def_symbol (F := RTL.fundef) (V := Unit)
      (p := p) (id := id) (g := gd)).mp hget with
    ⟨b'', hfind'', hdef⟩
  have hb : b = b'' := Option.some.inj (hfind.symm.trans hfind'')
  subst b''
  rcases (init_meminj_preserves_globals p tp used hvalid hmatch).defs_inject
      b b' delta gd hmap hdef with ⟨hdef', _, hrefs⟩
  exact ⟨hdelta, id, gd, hfind, hfind', hdef, hdef', hrefs⟩

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

private theorem unusedglob_replicate_byte_inject
    (f : Val.meminj) (n : Nat) (b : CompCert4Lean.Lib.Integers.byte) :
    list_forall2 (memval_inject f)
      (List.replicate n (Byte b)) (List.replicate n (Byte b)) := by
  induction n with
  | zero => constructor
  | succ n ih =>
      simp only [List.replicate_succ]
      exact list_forall2.cons _ _ (memval_inject.byte f b) ih

theorem bytes_of_init_inject : bytes_of_init_injectStatement := by
  intro p tp used hvalid hmatch il hkeep
  have hglobals := init_meminj_preserves_globals p tp used hvalid hmatch
  induction il with
  | nil => constructor
  | cons i il ih =>
      unfold Genv.bytes_of_init_data_list
      apply list_forall2_app
      · cases i with
        | Init_int8 n => exact inj_bytes_inject _ _
        | Init_int16 n => exact inj_bytes_inject _ _
        | Init_int32 n => exact inj_bytes_inject _ _
        | Init_int64 n => exact inj_bytes_inject _ _
        | Init_float32 n => exact inj_bytes_inject _ _
        | Init_float64 n => exact inj_bytes_inject _ _
        | Init_space n =>
            exact unusedglob_replicate_byte_inject _ _ _
        | Init_addrof id ofs =>
            have hkid : kept used id := by
              apply hkeep id
              exact ⟨ofs, by simp⟩
            unfold Genv.bytes_of_init_data
            cases hfind : Genv.find_symbol (Genv.globalenv p) id with
            | none =>
                cases hfind' : Genv.find_symbol (Genv.globalenv tp) id with
                | none =>
                    simp [Genv.bytes_of_init_data, hfind, hfind']
                    exact repeat_Undef_inject_self _ _
                | some b' =>
                    rcases hglobals.symbols_inject_3 id b' hfind' with
                      ⟨b, hfindb, _⟩
                    simp [hfind] at hfindb
            | some b =>
                rcases hglobals.symbols_inject_2 id b hkid hfind with
                  ⟨b', hfind', hmap⟩
                simp [Genv.bytes_of_init_data, hfind, hfind']
                apply inj_value_inject
                apply Val.inject_ptr (init_meminj p tp) b ofs b' ofs z0 hmap
                exact (unusedglob_ptrofs_add_zero_repr ofs).symm
      · apply ih
        intro id hid
        apply hkeep id
        rcases hid with ⟨ofs, hmem⟩
        exact ⟨ofs, by simp [hmem]⟩

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Mem_getN_forall2 : Mem_getN_forall2Statement := by
  intro P c1 c2 i n p hlist hpi hupper
  induction n generalizing p with
  | zero =>
      exfalso
      change intOfZ i < intOfZ (zAdd p (zOfNat 0)) at hupper
      change intOfZ p ≤ intOfZ i at hpi
      simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
        intOfZ_zOfInt] at hupper
      omega
  | succ n ih =>
      simp only [CompCert4Lean.Common.Memory.Mem.getN] at hlist
      cases hlist with
      | cons _ _ hhead htail =>
          by_cases heq : i = p
          · subst i
            exact hhead
          · apply ih (p := ZArith.BinInt.Z.add p (ZArith.BinInt.Z.of_nat 1)) htail
            · change intOfZ (ZArith.BinInt.Z.add p (ZArith.BinInt.Z.of_nat 1)) ≤ intOfZ i
              change intOfZ p ≤ intOfZ i at hpi
              have hne' : intOfZ i ≠ intOfZ p := by
                intro h
                exact heq (intOfZ_injective h)
              simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
                intOfZ_zOfInt]
              omega
            · change intOfZ i < intOfZ (zAdd
                (ZArith.BinInt.Z.add p (ZArith.BinInt.Z.of_nat 1)) (zOfNat n))
              change intOfZ i < intOfZ (zAdd p (zOfNat (Nat.succ n))) at hupper
              simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
                intOfZ_zOfInt] at hupper ⊢
              omega

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Globalenvs.Genv
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata

private theorem ug_drop_perm_exists (m : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (lo hi : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (p : CompCert4Lean.Common.Memtype.permission)
    (h : Mem.range_perm m b lo hi Cur Freeable) :
    ∃ m', Mem.drop_perm m b lo hi p = some m' := by
  unfold Mem.drop_perm
  cases hdec : Mem.range_perm_dec m b lo hi Cur Freeable with
  | left hproof =>
      simp [hdec]
  | right hnot =>
      exact False.elim (hnot h)

private theorem ug_store_zeros_exists
    (m : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (p n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (h : Mem.range_perm m b p
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p n)
      Cur Writable) :
    ∃ m', store_zeros m b p n = some m' := by
  let P : CompCert4Lean.Common.Memory.mem →
      CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Option CompCert4Lean.Common.Memory.mem → Prop :=
    fun m b p n r =>
      Mem.range_perm m b p
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p n)
        Cur Writable → ∃ m', r = some m'
  have hP : ∀ (m : CompCert4Lean.Common.Memory.mem)
      (b : CompCert4Lean.Common.Values.block)
      (p n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z),
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
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p n)
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1)) at hofshi
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n > 0 at x
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hofshi ⊢
            omega
        · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.divide
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1) p
          refine ⟨p, ?_⟩
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rcases Mem.valid_access_store m Mint8unsigned b p Vzero hv with ⟨m1, hm1⟩
      have hm1eq : m1 = m' := Option.some.inj (hm1.symm.trans hstore)
      subst m1
      have hrange' : Mem.range_perm m' b
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1))
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1))
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub n
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1)))
          Cur Writable := by
        intro ofs hofs
        apply Mem.perm_store_1 Mint8unsigned m b p Vzero m' hstore b ofs Cur Writable
        apply hrange
        rcases hofs with ⟨hofslo, hofshi⟩
        constructor
        · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ p ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1)) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs at hofslo
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hofslo ⊢
          omega
        · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p n)
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1))
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub n
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1))) at hofshi
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n > 0 at x
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hofshi ⊢
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
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p n)
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1)) at hofshi
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n > 0 at x
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hofshi ⊢
            omega
        · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.divide
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1) p
          refine ⟨p, ?_⟩
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rcases Mem.valid_access_store m Mint8unsigned b p Vzero hv with ⟨m', hm'⟩
      rw [hm'] at hnone
      cases hnone
  exact hP m b p n h

private theorem ug_mem_store_exists
    (chunk : memory_chunk) (m : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (v : val)
    (hrange : Mem.range_perm m b p
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
        (CompCert4Lean.Common.Memdata.size_chunk chunk)) Cur Writable)
    (halign : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.divide
      (CompCert4Lean.Common.Memdata.align_chunk chunk) p) :
    ∃ m', Mem.store chunk m b p v = some m' := by
  rcases Mem.valid_access_store m chunk b p v ⟨hrange, halign⟩ with ⟨m', hm'⟩
  exact ⟨m', hm'⟩

private theorem ug_store_init_data_exists
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (m : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (i : init_data)
    (hrange : Mem.range_perm m b p
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
        (init_data_size i)) Cur Writable)
    (halign : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.divide
      (init_data_alignment i) p)
    (hfind : ∀ id ofs, i = Init_addrof id ofs →
      ∃ b, Genv.find_symbol ge id = some b) :
    ∃ m', store_init_data ge m b p i = some m' := by
  cases i with
  | Init_int8 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (ug_mem_store_exists Mint8unsigned m b p (Vint n)
          (by simpa [init_data_size, size_chunk, Mptr] using hrange)
          (by simpa [init_data_alignment, align_chunk, Mptr] using halign))
  | Init_int16 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (ug_mem_store_exists Mint16unsigned m b p (Vint n)
          (by simpa [init_data_size, size_chunk] using hrange)
          (by simpa [init_data_alignment, align_chunk] using halign))
  | Init_int32 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (ug_mem_store_exists Mint32 m b p (Vint n)
          (by simpa [init_data_size, size_chunk] using hrange)
          (by simpa [init_data_alignment, align_chunk] using halign))
  | Init_int64 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (ug_mem_store_exists Mint64 m b p (Vlong n)
          (by simpa [init_data_size, size_chunk] using hrange)
          (by simpa [init_data_alignment, align_chunk] using halign))
  | Init_float32 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (ug_mem_store_exists Mfloat32 m b p (Vsingle n)
          (by simpa [init_data_size, size_chunk] using hrange)
          (by simpa [init_data_alignment, align_chunk] using halign))
  | Init_float64 n =>
      simpa [store_init_data, init_data_size, init_data_alignment] using
        (ug_mem_store_exists Mfloat64 m b p (Vfloat n)
          (by simpa [init_data_size, size_chunk] using hrange)
          (by simpa [init_data_alignment, align_chunk] using halign))
  | Init_addrof id ofs =>
      rcases hfind id ofs rfl with ⟨b', hb'⟩
      have hrange' := hrange
      rw [Genv.init_data_size_addrof] at hrange'
      have halign' := halign
      simp [init_data_alignment] at halign'
      rw [← CompCert4Lean.Common.Memdata.align_chunk_Mptr] at halign'
      simpa [store_init_data, hb'] using
        (ug_mem_store_exists Mptr m b p (Vptr b' ofs) hrange' halign')
  | Init_space n =>
      exact ⟨m, by rfl⟩

private theorem ug_store_init_data_perm
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (m m' : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
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
      cases hsym : Genv.find_symbol ge id with
      | none => simp [store_init_data, hsym] at hm
      | some b0 =>
          exact Mem.perm_store_1 Mptr m b p (Vptr b0 ofs0) m'
            (by simpa [store_init_data, hsym] using hm) b' ofs k prm hperm
  | Init_space n =>
      have hm' : m' = m := by simpa [store_init_data] using hm.symm
      subst m'
      exact hperm

private theorem ug_store_init_data_list_exists
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (b : CompCert4Lean.Common.Values.block) (il : List init_data)
    (m : CompCert4Lean.Common.Memory.mem)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hrange : Mem.range_perm m b p
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
        (init_data_list_size il)) Cur Writable)
    (halign : init_data_list_aligned p il)
    (hfind : ∀ id ofs, Init_addrof id ofs ∈ il →
      ∃ b, Genv.find_symbol ge id = some b) :
    ∃ m', store_init_data_list ge m b p il = some m' := by
  induction il generalizing m p with
  | nil =>
      exact ⟨m, rfl⟩
  | cons i rest ih =>
      rcases halign with ⟨hhead, htail⟩
      have hrange_i : Mem.range_perm m b p
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
            (init_data_size i)) Cur Writable := by
        intro ofs hofs
        rcases hofs with ⟨hofslo, hofshi⟩
        apply hrange ofs
        constructor
        · exact hofslo
        · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                (init_data_list_size (i :: rest)))
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                (init_data_size i)) at hofshi
          simp [init_data_list_size,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hofshi ⊢
          have hnonneg := init_data_list_size_pos rest
          change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (init_data_list_size rest) at hnonneg
          omega
      have hfind_i : ∀ id ofs, i = Init_addrof id ofs →
          ∃ b, Genv.find_symbol ge id = some b := by
        intro id ofs hi
        apply hfind id ofs
        simp [hi]
      rcases ug_store_init_data_exists F V ge m b p i hrange_i hhead hfind_i with
        ⟨m1, hm1⟩
      have hrange_tail : Mem.range_perm m1 b
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
            (init_data_size i))
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
              (init_data_size i)) (init_data_list_size rest)) Cur Writable := by
        intro ofs hofs
        rcases hofs with ⟨hofslo, hofshi⟩
        apply ug_store_init_data_perm F V ge m m1 b p i hm1 b ofs Cur Writable
        apply hrange ofs
        constructor
        · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ p ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                  (init_data_size i)) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs at hofslo
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hofslo ⊢
          have hi := init_data_size_pos i
          change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (init_data_size i) at hi
          omega
        · have hadd :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                  (init_data_list_size (i :: rest)) =
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                    (init_data_size i)) (init_data_list_size rest) := by
              apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
              simp [init_data_list_size,
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
              omega
          rw [hadd]
          exact hofshi
      have hfind_tail : ∀ id ofs, Init_addrof id ofs ∈ rest →
          ∃ b, Genv.find_symbol ge id = some b := by
        intro id ofs hmem
        apply hfind id ofs
        simp [hmem]
      rcases ih m1
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
            (init_data_size i)) hrange_tail htail hfind_tail with ⟨m2, hm2⟩
      refine ⟨m2, ?_⟩
      simp [store_init_data_list, hm1, hm2]

private theorem ug_alloc_range_perm
    (m : CompCert4Lean.Common.Memory.mem)
    (lo hi : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    let r := Mem.alloc m lo hi
    Mem.range_perm r.1 r.2 lo hi Cur Freeable := by
  unfold Mem.alloc
  dsimp
  intro ofs hofs
  unfold Mem.perm
  rw [CompCert4Lean.Lib.Maps.PMap.gss]
  have hle :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb lo ofs = true := by
    have hh := hofs.1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ lo ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs at hh
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb] using hh
  have hlt :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.ltb ofs hi = true := by
    have hh := hofs.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hi at hh
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.ltb] using hh
  change Mem.perm_order'
    (if (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb lo ofs &&
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.ltb ofs hi) = true
        then some Freeable else none) Freeable
  simpa [hle, hlt, Mem.perm_order'] using (perm_refl Freeable)

private theorem ug_alloc_range_perm_writable
    (m : CompCert4Lean.Common.Memory.mem)
    (lo hi : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    let r := Mem.alloc m lo hi
    Mem.range_perm r.1 r.2 lo hi Cur Writable := by
  unfold Mem.alloc
  dsimp
  intro ofs hofs
  unfold Mem.perm
  rw [CompCert4Lean.Lib.Maps.PMap.gss]
  have hle :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb lo ofs = true := by
    have hh := hofs.1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ lo ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs at hh
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb] using hh
  have hlt :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.ltb ofs hi = true := by
    have hh := hofs.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hi at hh
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.ltb] using hh
  change Mem.perm_order'
    (if (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb lo ofs &&
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.ltb ofs hi) = true
        then some Freeable else none) Writable
  simpa [hle, hlt, Mem.perm_order'] using (perm_F_any Writable)

private theorem ug_store_zeros_perm
    (m m' : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (p n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hs : store_zeros m b p n = some m') :
    ∀ b' ofs k prm, Mem.perm m b' ofs k prm → Mem.perm m' b' ofs k prm := by
  let P : CompCert4Lean.Common.Memory.mem →
      CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Option CompCert4Lean.Common.Memory.mem → Prop :=
    fun m b p n r =>
      ∀ m', r = some m' →
        ∀ b' ofs k prm, Mem.perm m b' ofs k prm → Mem.perm m' b' ofs k prm
  have hP : ∀ (m : CompCert4Lean.Common.Memory.mem)
      (b : CompCert4Lean.Common.Values.block)
      (p n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z),
      P m b p n (store_zeros m b p n) := by
    apply store_zeros_ind (P := P)
    · intro m b p n x hx m' hm' b' ofs k prm hperm
      cases Option.some.inj hm'
      exact hperm
    · intro m b p n x hx m1 hstore hrec m' hm' b' ofs k prm hperm
      apply hrec m' hm' b' ofs k prm
      exact Mem.perm_store_1 Mint8unsigned m b p Vzero m1 hstore
        b' ofs k prm hperm
    · intro m b p n x hx hnone m' hm' b' ofs k prm hperm
      cases hm'
  exact hP m b p n m' hs

private theorem ug_store_init_data_list_perm
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (m m' : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (il : List init_data)
    (hm : store_init_data_list ge m b p il = some m') :
    ∀ b' ofs k prm, Mem.perm m b' ofs k prm → Mem.perm m' b' ofs k prm := by
  cases il with
  | nil =>
      have hm' : m' = m := by simpa [store_init_data_list] using hm.symm
      subst m'
      intro b' ofs k prm hperm
      exact hperm
  | cons i rest =>
      simp only [store_init_data_list] at hm
      cases hstep : store_init_data ge m b p i with
      | none => simp [hstep] at hm
      | some m1 =>
          have hm1 : store_init_data ge m b p i = some m1 := hstep
          have htail : store_init_data_list ge m1 b
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                (init_data_size i)) rest = some m' := by
            simpa [hstep] using hm
          intro b' ofs k prm hperm
          have hperm1 := ug_store_init_data_perm F V ge m m1 b p i hm1
            b' ofs k prm hperm
          exact ug_store_init_data_list_perm F V ge m1 m' b
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
              (init_data_size i)) rest htail b' ofs k prm hperm1

private theorem ug_perm_freeable_to_writable
    (m : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (ofs : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (k : perm_kind) (h : Mem.perm m b ofs k Freeable) :
    Mem.perm m b ofs k Writable := by
  unfold Mem.perm at h ⊢
  cases hq : (CompCert4Lean.Lib.Maps.PMap.get b m.mem_access) ofs k with
  | none => simp [Mem.perm_order', hq] at h
  | some q =>
      simp [Mem.perm_order', hq] at h ⊢
      cases h with
      | perm_refl _ => exact perm_F_any _
      | perm_F_any _ => exact perm_F_any _

private theorem ug_alloc_global_exists
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (m : CompCert4Lean.Common.Memory.mem)
    (idg : ident × globdef F V)
    (h : match idg.2 with
      | .Gfun _ => True
      | .Gvar v =>
          init_data_list_aligned z0 v.gvar_init ∧
            ∀ i o, Init_addrof i o ∈ v.gvar_init →
              ∃ b, Genv.find_symbol ge i = some b) :
    ∃ m', alloc_global ge m idg = some m' := by
  rcases idg with ⟨id, gd⟩
  cases gd with
  | Gfun f =>
      cases ha : Mem.alloc m z0
          (.Zpos .xH) with
      | mk m1 b =>
          have hr : Mem.range_perm m1 b z0
              (.Zpos .xH)
              Cur Freeable := by
            simpa [ha] using (ug_alloc_range_perm m z0
              (.Zpos .xH))
          rcases ug_drop_perm_exists m1 b z0
              (.Zpos .xH)
              Nonempty hr with ⟨m2, hm2⟩
          refine ⟨m2, ?_⟩
          simp [alloc_global, ha, hm2]
  | Gvar v =>
      rcases h with ⟨halign, hfind⟩
      let sz := init_data_list_size v.gvar_init
      cases ha : Mem.alloc m z0 sz with
      | mk m1 b =>
          have hr0 : Mem.range_perm m1 b z0
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add z0 sz)
              Cur Freeable := by
            have hr := ug_alloc_range_perm m z0 sz
            rw [ha] at hr
            dsimp at hr
            have hz :
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add z0 sz = sz := by
              apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 +
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ sz)) =
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ sz
              rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
              have hz0 :
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 = 0 := by
                rfl
              rw [hz0]
              simp
            simpa [hz] using hr
          have hr0w : Mem.range_perm m1 b z0
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add z0 sz)
              Cur Writable := by
            intro ofs hofs
            apply ug_perm_freeable_to_writable m1 b ofs Cur
            exact hr0 ofs hofs
          rcases ug_store_zeros_exists m1 b z0 sz hr0w with ⟨m2, hm2⟩
          have hr2 : Mem.range_perm m2 b z0
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add z0 sz)
              Cur Freeable := by
            intro ofs hofs
            apply ug_store_zeros_perm m1 m2 b z0 sz hm2 b ofs Cur Freeable
            exact hr0 ofs hofs
          have hr2w : Mem.range_perm m2 b z0
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add z0 sz)
              Cur Writable := by
            intro ofs hofs
            apply ug_perm_freeable_to_writable m2 b ofs Cur
            exact hr2 ofs hofs
          have hfind' : ∀ i o, Init_addrof i o ∈ v.gvar_init →
              ∃ b, Genv.find_symbol ge i = some b := hfind
          have hr2' : Mem.range_perm m2 b z0
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add z0
                (init_data_list_size v.gvar_init)) Cur Writable := by
            simpa [sz] using hr2w
          rcases ug_store_init_data_list_exists F V ge b v.gvar_init m2 z0
              hr2' halign hfind' with ⟨m3, hm3⟩
          have hr3 : Mem.range_perm m3 b z0
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add z0 sz)
              Cur Freeable := by
            intro ofs hofs
            apply ug_store_init_data_list_perm F V ge m2 m3 b z0
              v.gvar_init hm3 b ofs Cur Freeable
            exact hr2 ofs hofs
          have hz :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add z0 sz = sz := by
            apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 +
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ sz)) =
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ sz
            rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            have hz0 :
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0 = 0 := by
              rfl
            rw [hz0]
            simp
          have hr3s : Mem.range_perm m3 b z0 sz Cur Freeable := by
            simpa [hz] using hr3
          rcases ug_drop_perm_exists m3 b z0 sz (perm_globvar v) hr3s with
            ⟨m4, hm4⟩
          refine ⟨m4, ?_⟩
          simp [alloc_global, ha, hm2, hm3, hm4, sz]

private theorem ug_mem_store_valid_access
    (chunk : CompCert4Lean.Common.AST.memory_chunk)
    (m : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (v : CompCert4Lean.Common.Values.val)
    (m' : CompCert4Lean.Common.Memory.mem)
    (h : CompCert4Lean.Common.Memory.Mem.store chunk m b p v = some m') :
    CompCert4Lean.Common.Memory.Mem.valid_access m chunk b p Writable := by
  unfold CompCert4Lean.Common.Memory.Mem.store at h
  cases hdec : CompCert4Lean.Common.Memory.Mem.valid_access_dec m chunk b p Writable with
  | left hproof => exact hproof
  | right hnot =>
      simp [hdec] at h
      have hb := h.1
      change false = true at hb
      cases hb

private theorem ug_store_init_data_aligned
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (m m' : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (i : init_data)
    (h : store_init_data ge m b p i = some m') :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.divide
      (init_data_alignment i) p := by
  cases i with
  | Init_int8 n =>
      have hv := ug_mem_store_valid_access Mint8unsigned m b p (Vint n) m'
        (by simpa [store_init_data] using h)
      simpa [init_data_alignment, align_chunk, Mptr] using hv.2
  | Init_int16 n =>
      have hv := ug_mem_store_valid_access Mint16unsigned m b p (Vint n) m'
        (by simpa [store_init_data] using h)
      simpa [init_data_alignment, align_chunk, Mptr] using hv.2
  | Init_int32 n =>
      have hv := ug_mem_store_valid_access Mint32 m b p (Vint n) m'
        (by simpa [store_init_data] using h)
      simpa [init_data_alignment, align_chunk, Mptr] using hv.2
  | Init_int64 n =>
      have hv := ug_mem_store_valid_access Mint64 m b p (Vlong n) m'
        (by simpa [store_init_data] using h)
      simpa [init_data_alignment, align_chunk, Mptr] using hv.2
  | Init_float32 n =>
      have hv := ug_mem_store_valid_access Mfloat32 m b p (Vsingle n) m'
        (by simpa [store_init_data] using h)
      simpa [init_data_alignment, align_chunk, Mptr] using hv.2
  | Init_float64 n =>
      have hv := ug_mem_store_valid_access Mfloat64 m b p (Vfloat n) m'
        (by simpa [store_init_data] using h)
      simpa [init_data_alignment, align_chunk, Mptr] using hv.2
  | Init_addrof id ofs =>
      cases hsym : Genv.find_symbol ge id with
      | none => simp [store_init_data, hsym] at h
      | some b' =>
          have hv := ug_mem_store_valid_access Mptr m b p (Vptr b' ofs) m'
            (by simpa [store_init_data, hsym] using h)
          have ha := hv.2
          rw [CompCert4Lean.Common.Memdata.align_chunk_Mptr] at ha
          simpa [init_data_alignment] using ha
  | Init_space n =>
      simp [init_data_alignment]
      refine ⟨p, ?_⟩
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

end CompCert4Lean.Backend.Unusedglobproof


namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Globalenvs.Genv
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata

private theorem ug_store_init_data_props
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (m m' : CompCert4Lean.Common.Memory.mem)
    (b : CompCert4Lean.Common.Values.block)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (i : init_data)
    (h : store_init_data ge m b p i = some m') :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.divide
        (init_data_alignment i) p ∧
      ∀ id ofs, i = Init_addrof id ofs →
        ∃ b, Genv.find_symbol ge id = some b := by
  constructor
  · exact ug_store_init_data_aligned F V ge m m' b p i h
  · intro id ofs hi
    cases i with
    | Init_int8 n => cases hi
    | Init_int16 n => cases hi
    | Init_int32 n => cases hi
    | Init_int64 n => cases hi
    | Init_float32 n => cases hi
    | Init_float64 n => cases hi
    | Init_space n => cases hi
    | Init_addrof id0 ofs0 =>
        cases hi
        cases hs : Genv.find_symbol ge id with
        | none => simp [store_init_data, hs] at h
        | some b => exact ⟨b, rfl⟩

private theorem ug_store_init_data_list_props
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (b : CompCert4Lean.Common.Values.block) (il : List init_data)
    (m m' : CompCert4Lean.Common.Memory.mem)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (h : store_init_data_list ge m b p il = some m') :
    init_data_list_aligned p il ∧
      ∀ id ofs, Init_addrof id ofs ∈ il →
        ∃ b, Genv.find_symbol ge id = some b := by
  induction il generalizing m p with
  | nil =>
      constructor
      · trivial
      · intro id ofs hmem
        cases hmem
  | cons i rest ih =>
      simp only [store_init_data_list] at h
      cases hs : store_init_data ge m b p i with
      | none => simp [hs] at h
      | some m1 =>
          have htail :
              store_init_data_list ge m1 b
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                  (init_data_size i)) rest = some m' := by
            simpa [hs] using h
          have hi := ug_store_init_data_props F V ge m m1 b p i hs
          have ht := ih m1
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
              (init_data_size i)) htail
          constructor
          · exact ⟨hi.1, ht.1⟩
          · intro id ofs hmem
            rcases List.mem_cons.mp hmem with hhead | hrest
            · have hi' := hi.2 id ofs
                (by simpa using hhead.symm)
              exact hi'
            · exact ht.2 id ofs hrest

private theorem ug_alloc_global_props
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (m m' : CompCert4Lean.Common.Memory.mem)
    (id : CompCert4Lean.Common.AST.ident)
    (v : globvar V)
    (h : alloc_global ge m (id, Gvar v) = some m') :
    init_data_list_aligned z0 v.gvar_init ∧
      ∀ i o, Init_addrof i o ∈ v.gvar_init →
        ∃ b, Genv.find_symbol ge i = some b := by
  simp only [alloc_global, Prod.snd] at h
  split at h
  · cases h
  · split at h
    · cases h
    · apply ug_store_init_data_list_props F V ge
      assumption

private theorem ug_alloc_globals_props
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (gl : List (CompCert4Lean.Common.AST.ident × globdef F V))
    (m m' : CompCert4Lean.Common.Memory.mem)
    (h : alloc_globals ge m gl = some m') :
    ∀ id v, (id, Gvar v) ∈ gl →
      init_data_list_aligned z0 v.gvar_init ∧
        ∀ i o, Init_addrof i o ∈ v.gvar_init →
          ∃ b, Genv.find_symbol ge i = some b := by
  induction gl generalizing m m' with
  | nil =>
      intro id v hmem
      cases hmem
  | cons g rest ih =>
      rcases g with ⟨id0, gd⟩
      simp only [alloc_globals] at h
      cases ha : alloc_global ge m (id0, gd) with
      | none => simp [ha] at h
      | some m1 =>
          have htail : alloc_globals ge m1 rest = some m' := by
            simpa [ha] using h
          intro id v hmem
          rcases List.mem_cons.mp hmem with hhead | hrest
          · cases gd with
            | Gfun f => cases hhead
            | Gvar v0 =>
                injection hhead with hid hv
                subst id0
                cases hv
                exact ug_alloc_global_props F V ge m m1 id v ha
          · exact ih m1 m' htail id v hrest

private theorem ug_init_mem_props
    (F V : Type) (p : CompCert4Lean.Common.AST.program F V)
    (m : CompCert4Lean.Common.Memory.mem)
    (h : Genv.init_mem p = some m) :
    ∀ id v, (id, Gvar v) ∈ p.prog_defs →
      init_data_list_aligned z0 v.gvar_init ∧
        ∀ i o, Init_addrof i o ∈ v.gvar_init →
          ∃ b, Genv.find_symbol (Genv.globalenv p) i = some b := by
  unfold Genv.init_mem at h
  exact ug_alloc_globals_props F V (Genv.globalenv p) p.prog_defs Mem.empty m h

private theorem ug_alloc_globals_exists
    (F V : Type) (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (gl : List (CompCert4Lean.Common.AST.ident × globdef F V))
    (m : CompCert4Lean.Common.Memory.mem)
    (hvars : ∀ id v, (id, Gvar v) ∈ gl →
      init_data_list_aligned z0 v.gvar_init ∧
        ∀ i o, Init_addrof i o ∈ v.gvar_init →
          ∃ b, Genv.find_symbol ge i = some b) :
    ∃ m', alloc_globals ge m gl = some m' := by
  induction gl generalizing m with
  | nil =>
      exact ⟨m, rfl⟩
  | cons g rest ih =>
      rcases g with ⟨id, gd⟩
      have hvars_rest : ∀ id' v, (id', Gvar v) ∈ rest →
          init_data_list_aligned z0 v.gvar_init ∧
            ∀ i o, Init_addrof i o ∈ v.gvar_init →
              ∃ b, Genv.find_symbol ge i = some b := by
        intro id' v hmem
        apply hvars id' v
        exact List.mem_cons_of_mem (id, gd) hmem
      have htail : ∀ m1, ∃ m', alloc_globals ge m1 rest = some m' :=
        fun m1 => ih m1 hvars_rest
      cases gd with
      | Gfun f =>
          rcases ug_alloc_global_exists F V ge m (id, Gfun f) trivial with
            ⟨m1, halloc⟩
          rcases htail m1 with ⟨m2, hrest⟩
          exact ⟨m2, by simp [alloc_globals, halloc, hrest]⟩
      | Gvar v =>
          have hv := hvars id v (by simp)
          rcases ug_alloc_global_exists F V ge m (id, Gvar v) hv with
            ⟨m1, halloc⟩
          rcases htail m1 with ⟨m2, hrest⟩
          exact ⟨m2, by simp [alloc_globals, halloc, hrest]⟩

private theorem ug_init_mem_exists
    (F V : Type) (p : CompCert4Lean.Common.AST.program F V)
    (hvars : ∀ id v, (id, Gvar v) ∈ p.prog_defs →
      init_data_list_aligned z0 v.gvar_init ∧
        ∀ i o, Init_addrof i o ∈ v.gvar_init →
          ∃ b, Genv.find_symbol (Genv.globalenv p) i = some b) :
    ∃ m, Genv.init_mem p = some m := by
  unfold Genv.init_mem
  exact ug_alloc_globals_exists F V (Genv.globalenv p) p.prog_defs Mem.empty hvars

end CompCert4Lean.Backend.Unusedglobproof


namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Unusedglob
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Globalenvs.Genv
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

theorem init_mem_exists : init_mem_existsStatement := by
  intro p tp used hvalid hmatch m hmem
  have hsource_props := ug_init_mem_props _ _ p m hmem
  have htarget_props :
      ∀ id v, (id, Gvar v) ∈ tp.prog_defs →
        init_data_list_aligned z0 v.gvar_init ∧
          ∀ i o, Init_addrof i o ∈ v.gvar_init →
            ∃ b, Genv.find_symbol (Genv.globalenv tp) i = some b := by
    intro id v hmemtp
    have hmaptp : PTree.get id (prog_defmap tp) = some (Gvar v) :=
      prog_defmap_norepet (F := RTL.fundef) (V := Unit) tp id (Gvar v)
        (match_prog_unique hmatch) hmemtp
    rw [match_prog_def hmatch id] at hmaptp
    cases hused : IS.mem id used with
    | false =>
        simp [hused] at hmaptp
    | true =>
        have hmap : PTree.get id (prog_defmap p) = some (Gvar v) := by
          simpa [hused] using hmaptp
        have hmem_p : (id, Gvar v) ∈ p.prog_defs :=
          in_prog_defmap (F := RTL.fundef) (V := Unit) p id (Gvar v) hmap
        have hprops := hsource_props id v hmem_p
        refine ⟨hprops.1, ?_⟩
        intro i o hinit
        rcases hprops.2 i o hinit with ⟨b, hfind⟩
        have hkept_i : kept used i := by
          apply kept_closed p used hvalid id (Gvar v)
          · exact CompCert4Lean.Backend.Unusedglob.IS.mem_2_proof used id hused
          · exact hmap
          · exact ⟨o, hinit⟩
        rcases transform_find_symbol_1 p tp used hmatch i b hfind hkept_i with
          ⟨b', hfind'⟩
        exact ⟨b', hfind'⟩
  exact ug_init_mem_exists _ _ tp htarget_props

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.RTL

theorem transf_final_states : transf_final_statesStatement := by
  intro p tp used S1 S2 r hmatch hfinal
  cases hfinal
  cases hmatch with
  | match_states_return s res m ts tres tm j stacks res_inj hmem =>
      cases stacks
      cases res_inj
      constructor

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Globalenvs.Genv
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps


private theorem ug_init_pmap_gss {A : Type} (b : block) (x : A) (m : PMap.t A) :
    PMap.get b (PMap.set b x m) = x := by
  exact PMap.gss b x m

private theorem ug_init_pmap_gso {A : Type} (b b' : block) (x : A) (m : PMap.t A)
    (h : b' ≠ b) : PMap.get b' (PMap.set b x m) = PMap.get b' m := by
  exact PMap.gso x m h

private theorem ug_init_loadbytes_unchanged
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

private theorem ug_init_alloc_result
    (m m' : mem) (lo hi : Z) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) :
    b = m.nextblock := by
  unfold Mem.alloc at halloc
  cases halloc
  rfl

private theorem ug_init_alloc_perm_bound
    (m m' : mem) (lo hi : Z) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b))
    (ofs : Z) (k : perm_kind) (prm : permission)
    (hperm : Mem.perm m' b ofs k prm) :
    zLe lo ofs ∧ zLt ofs hi := by
  unfold Mem.alloc at halloc
  cases halloc
  unfold Mem.perm at hperm
  rw [PMap.gss] at hperm
  change Mem.perm_order'
    (if (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true
      then some Freeable else none) prm at hperm
  cases hle : ZArith.BinInt.Z.leb lo ofs with
  | false => simp [Mem.perm_order', hle] at hperm
  | true =>
      cases hlt : ZArith.BinInt.Z.ltb ofs hi with
      | false => simp [Mem.perm_order', hlt] at hperm
      | true =>
          constructor
          · change intOfZ lo ≤ intOfZ ofs
            simpa [ZArith.BinInt.Z.leb] using hle
          · change intOfZ ofs < intOfZ hi
            simpa [ZArith.BinInt.Z.ltb] using hlt

private theorem ug_init_drop_perm_range
    (m m' : mem) (b : block) (lo hi : Z) (prm : permission)
    (hdrop : Mem.drop_perm m b lo hi prm = some m') :
    Mem.range_perm m' b lo hi Cur prm := by
  unfold Mem.drop_perm at hdrop
  cases hdec : Mem.range_perm_dec m b lo hi Cur Freeable with
  | right _ => simp [hdec] at hdrop
  | left _ =>
      simp [hdec] at hdrop
      cases hdrop
      intro ofs hofs
      unfold Mem.perm
      change Mem.perm_order'
        (PMap.get b (PMap.set b _ m.mem_access) ofs Cur) prm
      rw [ug_init_pmap_gss]
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
          then some prm else (PMap.get b m.mem_access) ofs Cur) prm
      simpa [hle, hlt, Mem.perm_order'] using (perm_refl prm)

private theorem ug_init_drop_perm_order
    (m m' : mem) (b : block) (lo hi : Z) (prm : permission)
    (hdrop : Mem.drop_perm m b lo hi prm = some m')
    (ofs : Z) (k : perm_kind) (prm' : permission)
    (hofs : zLe lo ofs ∧ zLt ofs hi)
    (hperm : Mem.perm m' b ofs k prm') :
    perm_order prm prm' := by
  unfold Mem.drop_perm at hdrop
  cases hdec : Mem.range_perm_dec m b lo hi Cur Freeable with
  | right _ => simp [hdec] at hdrop
  | left _ =>
      simp [hdec] at hdrop
      cases hdrop
      unfold Mem.perm at hperm
      change Mem.perm_order'
        (PMap.get b (PMap.set b _ m.mem_access) ofs k) prm' at hperm
      rw [ug_init_pmap_gss] at hperm
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
          then some prm else (PMap.get b m.mem_access) ofs k) prm' at hperm
      simpa [hle, hlt, Mem.perm_order'] using hperm

private theorem ug_init_drop_perm_inv
    (m m' : mem) (b : block) (lo hi : Z) (prm : permission)
    (hdrop : Mem.drop_perm m b lo hi prm = some m')
    (b' : block) (ofs : Z) (k : perm_kind) (prm' : permission)
    (hperm : Mem.perm m' b' ofs k prm') :
    Mem.perm m b' ofs k prm' := by
  unfold Mem.drop_perm at hdrop
  cases hdec : Mem.range_perm_dec m b lo hi Cur Freeable with
  | right _ => simp [hdec] at hdrop
  | left hrange =>
      simp [hdec] at hdrop
      cases hdrop
      by_cases hbb : b' = b
      · subst b'
        by_cases hin : zLe lo ofs ∧ zLt ofs hi
        · have hfreeCur := hrange ofs hin
          have hfree : Mem.perm m b ofs k Freeable := by
            cases k with
            | Cur => exact hfreeCur
            | Max => exact Mem.perm_cur_max m b ofs Freeable hfreeCur
          exact Mem.perm_implies m b ofs k Freeable prm' hfree (perm_F_any prm')
        · unfold Mem.perm at hperm ⊢
          change Mem.perm_order'
            (PMap.get b (PMap.set b _ m.mem_access) ofs k) prm' at hperm
          rw [ug_init_pmap_gss] at hperm
          change Mem.perm_order'
            (if (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true
              then some prm else (PMap.get b m.mem_access) ofs k) prm' at hperm
          have hbool :
              (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = false := by
            cases hle : ZArith.BinInt.Z.leb lo ofs with
            | false => simp [hle]
            | true =>
                cases hlt : ZArith.BinInt.Z.ltb ofs hi with
                | false => simp [hlt]
                | true =>
                    exfalso
                    apply hin
                    constructor
                    · change intOfZ lo ≤ intOfZ ofs
                      simpa [ZArith.BinInt.Z.leb] using hle
                    · change intOfZ ofs < intOfZ hi
                      simpa [ZArith.BinInt.Z.ltb] using hlt
          simpa [hbool] using hperm
      · unfold Mem.perm at hperm ⊢
        change Mem.perm_order'
          (PMap.get b' (PMap.set b _ m.mem_access) ofs k) prm' at hperm
        rw [ug_init_pmap_gso _ _ _ _ hbb] at hperm
        exact hperm

private theorem ug_init_drop_loadbytes
    (m m' : mem) (b : block) (lo hi : Z) (prm : permission)
    (hdrop : Mem.drop_perm m b lo hi prm = some m')
    (ofs n : Z) (bytes : List memval)
    (hread : perm_order prm Readable)
    (hload : Mem.loadbytes m b ofs n = some bytes)
    (hrange : ∀ i, zLe ofs i ∧ zLt i (zAdd ofs n) →
      zLe lo i ∧ zLt i hi) :
    Mem.loadbytes m' b ofs n = some bytes := by
  have hcontents : m'.mem_contents = m.mem_contents := by
    unfold Mem.drop_perm at hdrop
    cases hdec : Mem.range_perm_dec m b lo hi Cur Freeable with
    | right _ => simp [hdec] at hdrop
    | left _ =>
        simp [hdec] at hdrop
        cases hdrop
        rfl
  unfold Mem.loadbytes at hload ⊢
  cases hold : Mem.range_perm_dec m b ofs (zAdd ofs n) Cur Readable with
  | right _ =>
      rw [hold] at hload
      change none = some bytes at hload
      cases hload
  | left _ =>
      have hnewrange : Mem.range_perm m' b ofs (zAdd ofs n) Cur Readable := by
        intro i hi'
        exact Mem.perm_implies m' b i Cur prm Readable
          (ug_init_drop_perm_range m m' b lo hi prm hdrop i (hrange i hi')) hread
      cases hnew : Mem.range_perm_dec m' b ofs (zAdd ofs n) Cur Readable with
      | right hnot => exact False.elim (hnot hnewrange)
      | left _ =>
          rw [hold] at hload
          change some (Mem.getN (ZArith.BinInt.Z.to_nat n) ofs
            (PMap.get b m.mem_contents)) = some bytes at hload
          change some (Mem.getN (ZArith.BinInt.Z.to_nat n) ofs
            (PMap.get b m'.mem_contents)) = some bytes
          rw [hcontents]
          exact hload

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Globalenvs.Genv
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev ug_init_z1 : Z := .Zpos .xH

private theorem ug_init_z1_int : intOfZ ug_init_z1 = 1 := rfl

private theorem ug_init_zOfNat_nonneg (n : Nat) :
    ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.of_nat n) := by
  change (0 : Int) ≤ intOfZ (ZArith.BinInt.Z.of_nat n)
  simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  change (0 : Int) ≤ Int.ofNat n
  exact Int.ofNat_zero_le n

private theorem ug_init_store_zeros_loadbytes
    (m : mem) (b : block) (p n : Z) (m' : mem)
    (hzeros : store_zeros m b p n = some m') :
    readbytes_as_zero m' b p n := by
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
      cases hresult : store_zeros m1 b0 (zAdd p0 ug_init_z1)
          (ZArith.BinInt.Z.sub n0 ug_init_z1) with
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
                  apply Genv.store_zeros_unchanged Q m1 b0 (zAdd p0 ug_init_z1)
                    (ZArith.BinInt.Z.sub n0 ug_init_z1) m2 hresult
                  intro i hi hQi
                  rcases hQi with ⟨_, hiEq⟩
                  subst i
                  have hlo' := hi.1
                  change intOfZ (zAdd p0 ug_init_z1) ≤ intOfZ p0 at hlo'
                  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at hlo'
                  rw [ug_init_z1_int] at hlo'
                  omega
                have hbyte :
                    Mem.loadbytes m1 b0 p0 ug_init_z1 =
                      some [Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)] := by
                  have hs := Mem.loadbytes_store_same Mint8unsigned m0 b0 p0 Vzero m1 hstore
                  have henc : encode_val Mint8unsigned Vzero =
                      [Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)] := by
                    rfl
                  have hsize : size_chunk Mint8unsigned = ug_init_z1 := rfl
                  rw [← hsize]
                  exact hs.trans (congrArg some henc)
                have hbyte' :
                    Mem.loadbytes m2 b0 p0 ug_init_z1 =
                      some [Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)] := by
                  apply ug_init_loadbytes_unchanged Q m1 m2 b0 p0 ug_init_z1 _ hunch
                  · change (0 : Int) ≤ 1
                    omega
                  · intro i hi
                    constructor
                    · rfl
                    · change intOfZ p0 ≤ intOfZ i ∧
                        intOfZ i < intOfZ (zAdd p0 ug_init_z1) at hi
                      change i = p0
                      apply intOfZ_injective
                      simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at hi
                      rw [ug_init_z1_int] at hi
                      omega
                  · exact hbyte
                have htail : Mem.loadbytes m2 b0 (zAdd p0 ug_init_z1) (zOfNat len) =
                    some (List.replicate len
                      (Byte (CompCert4Lean.Lib.Integers.Byte.repr z0))) := by
                  apply hrec m2 rfl (zAdd p0 ug_init_z1) len
                  · change intOfZ (zAdd p0 ug_init_z1) ≤ intOfZ (zAdd p0 ug_init_z1)
                    omega
                  · change intOfZ
                        (zAdd (zAdd p0 ug_init_z1) (zOfNat len)) ≤
                      intOfZ (zAdd (zAdd p0 ug_init_z1)
                        (ZArith.BinInt.Z.sub n0 ug_init_z1))
                    change intOfZ (zAdd p0 (zOfNat (Nat.succ len))) ≤
                      intOfZ (zAdd p0 n0) at hhi
                    simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
                      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hhi ⊢
                    rw [ug_init_z1_int]
                    omega
                have hcat := Mem.loadbytes_concat m2 b0 p0 ug_init_z1 (zOfNat len)
                  [Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)]
                  (List.replicate len
                    (Byte (CompCert4Lean.Lib.Integers.Byte.repr z0)))
                  hbyte' htail
                  (by change (0 : Int) ≤ 1; omega)
                  (ug_init_zOfNat_nonneg len)
                have hsizes : zAdd ug_init_z1 (zOfNat len) = zOfNat (Nat.succ len) := by
                  apply intOfZ_injective
                  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
                    intOfZ_zOfInt]
                  rw [ug_init_z1_int]
                  calc
                    1 + Int.ofNat len = Int.ofNat len + 1 := Int.add_comm _ _
                    _ = Int.ofNat len.succ := (Int.natCast_succ len).symm
                simpa [hsizes, List.replicate_succ] using hcat
          · apply hrec m2 rfl q len
            · change intOfZ (zAdd p0 ug_init_z1) ≤ intOfZ q
              change intOfZ p0 ≤ intOfZ q at hlo
              have hne : intOfZ q ≠ intOfZ p0 := by
                intro heq
                exact hqp (intOfZ_injective heq)
              simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
              rw [ug_init_z1_int]
              omega
            · change intOfZ (zAdd q (zOfNat len)) ≤
                intOfZ (zAdd (zAdd p0 ug_init_z1)
                  (ZArith.BinInt.Z.sub n0 ug_init_z1))
              change intOfZ (zAdd q (zOfNat len)) ≤ intOfZ (zAdd p0 n0) at hhi
              simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
                intOfZ_zOfInt] at hhi ⊢
              rw [ug_init_z1_int] at ⊢
              omega
    · intro m0 b0 p0 n0 hn hbranch hnone m1 hm1
      cases hm1
  exact hP m b p n m' hzeros

private theorem ug_init_ofNat_toNat_max (z : Z) :
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

private theorem ug_init_store_init_data_loadbytes
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
      have heq := ug_init_ofNat_toNat_max n
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

private theorem ug_init_store_init_data_list_loadbytes
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
          have hloadhead1 := ug_init_store_init_data_loadbytes F V ge m b p i m1
            hhead hzerohead
          have hloadhead : Mem.loadbytes m' b p (init_data_size i) =
              some (bytes_of_init_data ge i) := by
            apply ug_init_loadbytes_unchanged Phead m1 m' b p
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
            apply ug_init_loadbytes_unchanged Ptail m m1 b q (zOfNat len) _
              hunchhead (ug_init_zOfNat_nonneg len)
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

private def ug_init_globals {F V : Type} (ge g : Genv.t F V) (m : mem) : Prop :=
  ∀ b gd, Genv.find_def g b = some gd →
    match gd with
    | Gfun _ =>
        Mem.perm m b Z0 Cur CompCert4Lean.Common.Memtype.Nonempty ∧
          ∀ ofs k prm, Mem.perm m b ofs k prm →
            ofs = Z0 ∧ prm = CompCert4Lean.Common.Memtype.Nonempty
    | Gvar v =>
        Mem.range_perm m b Z0 (init_data_list_size v.gvar_init) Cur
            (perm_globvar v) ∧
          (∀ ofs k prm, Mem.perm m b ofs k prm →
            (ZArith.BinInt.Z.le Z0 ofs ∧
              ZArith.BinInt.Z.lt ofs (init_data_list_size v.gvar_init)) ∧
            perm_order (perm_globvar v) prm) ∧
          (v.gvar_volatile = false →
            Mem.loadbytes m b Z0 (init_data_list_size v.gvar_init) =
              some (bytes_of_init_data_list ge v.gvar_init))

private theorem ug_init_nonempty_order_eq (p : permission)
    (h : perm_order CompCert4Lean.Common.Memtype.Nonempty p) :
    p = CompCert4Lean.Common.Memtype.Nonempty := by
  cases h <;> rfl

private theorem ug_init_alloc_global
    (F V : Type) (ge g : Genv.t F V) (m : mem) (id : ident)
    (gd : globdef F V) (m' : mem)
    (hnext : g.genv_next = m.nextblock)
    (halloc : alloc_global ge m (id, gd) = some m')
    (hglobals : ug_init_globals ge g m) :
    ug_init_globals ge (Genv.add_global g (id, gd)) m' ∧
      (Genv.add_global g (id, gd)).genv_next = m'.nextblock := by
  have hnextalloc := Genv.alloc_global_nextblock F V ge (id, gd) m m' halloc
  constructor
  · intro b gd' hfind
    unfold Genv.find_def at hfind
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
            cases ha : Mem.alloc m Z0 ug_init_z1 with
            | mk m1 bnew =>
                have hdrop : Mem.drop_perm m1 bnew Z0 ug_init_z1
                    CompCert4Lean.Common.Memtype.Nonempty =
                    some m' := by
                  simpa [ha] using halloc
                have hbnew := ug_init_alloc_result m m1 Z0 ug_init_z1 bnew ha
                have hgb : g.genv_next = bnew := hnext.trans hbnew.symm
                rw [hgb]
                constructor
                · exact ug_init_drop_perm_range m1 m' bnew Z0 ug_init_z1
                    CompCert4Lean.Common.Memtype.Nonempty hdrop Z0 (by
                      constructor
                      · change (0 : Int) ≤ 0
                        omega
                      · change (0 : Int) < 1
                        omega)
                · intro ofs k prm hp
                  have hp1 := ug_init_drop_perm_inv m1 m' bnew Z0 ug_init_z1
                    CompCert4Lean.Common.Memtype.Nonempty hdrop bnew ofs k prm hp
                  have hbounds := ug_init_alloc_perm_bound m m1 Z0 ug_init_z1
                    bnew ha ofs k prm hp1
                  have hord := ug_init_drop_perm_order m1 m' bnew Z0 ug_init_z1
                    CompCert4Lean.Common.Memtype.Nonempty hdrop ofs k prm hbounds hp
                  constructor
                  · apply intOfZ_injective
                    have hlo := hbounds.1
                    have hhi := hbounds.2
                    change (0 : Int) ≤ intOfZ ofs at hlo
                    change intOfZ ofs < 1 at hhi
                    change intOfZ ofs = 0
                    omega
                  · exact ug_init_nonempty_order_eq prm hord
        | Gvar v =>
            unfold alloc_global at halloc
            cases ha : Mem.alloc m Z0 (init_data_list_size v.gvar_init) with
            | mk m1 bnew =>
                cases hz : store_zeros m1 bnew Z0
                    (init_data_list_size v.gvar_init) with
                | none => simp [ha, hz] at halloc
                | some m2 =>
                    cases hl : store_init_data_list ge m2 bnew Z0 v.gvar_init with
                    | none => simp [ha, hz, hl] at halloc
                    | some m3 =>
                        have hdrop : Mem.drop_perm m3 bnew Z0
                            (init_data_list_size v.gvar_init) (perm_globvar v) =
                            some m' := by
                          simpa [ha, hz, hl] using halloc
                        have hbnew := ug_init_alloc_result m m1 Z0
                          (init_data_list_size v.gvar_init) bnew ha
                        have hgb : g.genv_next = bnew := hnext.trans hbnew.symm
                        rw [hgb]
                        constructor
                        · exact ug_init_drop_perm_range m3 m' bnew Z0
                            (init_data_list_size v.gvar_init) (perm_globvar v) hdrop
                        constructor
                        · intro ofs k prm hp
                          have hp3 := ug_init_drop_perm_inv m3 m' bnew Z0
                            (init_data_list_size v.gvar_init) (perm_globvar v)
                            hdrop bnew ofs k prm hp
                          have hp2 := (Genv.store_init_data_list_perm F V ge k prm
                            bnew ofs v.gvar_init bnew m2 Z0 m3 hl).mpr hp3
                          have hp1 := (Genv.store_zeros_perm k prm bnew ofs m1 bnew Z0
                            (init_data_list_size v.gvar_init) m2 hz).mpr hp2
                          have hbounds := ug_init_alloc_perm_bound m m1 Z0
                            (init_data_list_size v.gvar_init) bnew ha ofs k prm hp1
                          exact ⟨hbounds, ug_init_drop_perm_order m3 m' bnew Z0
                            (init_data_list_size v.gvar_init) (perm_globvar v)
                            hdrop ofs k prm hbounds hp⟩
                        · intro hnonvol
                          have hzero := ug_init_store_zeros_loadbytes m1 bnew Z0
                            (init_data_list_size v.gvar_init) m2 hz
                          have hload3 := ug_init_store_init_data_list_loadbytes F V
                            ge bnew v.gvar_init m2 Z0 m3 hl hzero
                          have hread : perm_order (perm_globvar v) Readable := by
                            unfold perm_globvar
                            rw [hnonvol]
                            cases v.gvar_readonly <;> constructor
                          apply ug_init_drop_loadbytes m3 m' bnew Z0
                            (init_data_list_size v.gvar_init) (perm_globvar v) hdrop
                            Z0 (init_data_list_size v.gvar_init) _ hread hload3
                          intro ofs hi
                          constructor
                          · exact hi.1
                          · have hhi := hi.2
                            change intOfZ ofs < intOfZ
                              (zAdd Z0 (init_data_list_size v.gvar_init)) at hhi
                            change intOfZ ofs < intOfZ
                              (init_data_list_size v.gvar_init)
                            simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at hhi
                            have hz0 : intOfZ Z0 = 0 := rfl
                            rw [hz0] at hhi
                            simpa using hhi
    | right hbne =>
        rw [heq] at hfind
        have hold : Genv.find_def g b = some gd' := hfind
        have hvalid : Mem.valid_block m b := by
          change Plt b m.nextblock
          rw [← hnext]
          exact g.genv_defs_range b hold
        have hunch := Genv.alloc_global_unchanged F V ge
          (fun _ _ => True) m id gd m' halloc
        have holdprops := hglobals b gd' hold
        cases gd' with
        | Gfun f =>
            constructor
            · exact (hunch.unchanged_on_perm b Z0 Cur
                CompCert4Lean.Common.Memtype.Nonempty trivial hvalid).mp
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
            · intro hnonvol
              apply ug_init_loadbytes_unchanged (fun _ _ => True) m m' b Z0
                (init_data_list_size v.gvar_init) _ hunch
                (init_data_list_size_pos v.gvar_init)
              · intro _ _
                trivial
              · exact holdprops.2.2 hnonvol
  · change PArith.BinPos.Pos.succ g.genv_next = m'.nextblock
    rw [hnext]
    exact hnextalloc.symm

private theorem ug_init_alloc_globals
    (F V : Type) (ge : Genv.t F V) (gl : List (ident × globdef F V))
    (g : Genv.t F V) (m m' : mem)
    (halloc : alloc_globals ge m gl = some m')
    (hnext : g.genv_next = m.nextblock)
    (hglobals : ug_init_globals ge g m) :
    ug_init_globals ge (Genv.add_globals g gl) m' := by
  induction gl generalizing g m with
  | nil =>
      change some m = some m' at halloc
      cases halloc
      exact hglobals
  | cons idgd rest ih =>
      rcases idgd with ⟨id, gd⟩
      change (match alloc_global ge m (id, gd) with
        | none => none
        | some m1 => alloc_globals ge m1 rest) = some m' at halloc
      cases hhead : alloc_global ge m (id, gd) with
      | none => simp [hhead] at halloc
      | some m1 =>
          have htail : alloc_globals ge m1 rest = some m' := by
            simpa [hhead] using halloc
          have hstep := ug_init_alloc_global F V ge g m id gd m1
            hnext hhead hglobals
          change ug_init_globals ge
            (Genv.add_globals (Genv.add_global g (id, gd)) rest) m'
          exact ih (Genv.add_global g (id, gd)) m1 htail hstep.2 hstep.1

private theorem ug_init_mem_characterization
    (F V : Type) (p : program F V) (m : mem)
    (hmem : Genv.init_mem p = some m) :
    ug_init_globals (Genv.globalenv p) (Genv.globalenv p) m := by
  unfold Genv.init_mem at hmem
  change ug_init_globals (Genv.globalenv p)
    (Genv.add_globals (Genv.empty_genv F V p.prog_public) p.prog_defs) m
  apply ug_init_alloc_globals F V (Genv.globalenv p) p.prog_defs
    (Genv.empty_genv F V p.prog_public) Mem.empty m hmem
  · rfl
  · intro b gd hfind
    unfold Genv.find_def Genv.empty_genv at hfind
    simp [PTree.get, PTree.empty] at hfind

private theorem ug_init_zadd_zero (z : Z) :
    ZArith.BinInt.Z.add z Z0 = z := by
  unfold ZArith.BinInt.Z.add
  have hz0 : intOfZ Z0 = 0 := rfl
  rw [hz0, Int.add_zero]
  exact zOfInt_intOfZ z

private theorem ug_init_zero_zadd (z : Z) :
    ZArith.BinInt.Z.add Z0 z = z := by
  unfold ZArith.BinInt.Z.add
  have hz0 : intOfZ Z0 = 0 := rfl
  rw [hz0, Int.zero_add]
  exact zOfInt_intOfZ z

private theorem ug_init_nonvolatile_of_readable {V : Type} (v : globvar V)
    (h : perm_order (perm_globvar v) Readable) :
    v.gvar_volatile = false := by
  cases hv : v.gvar_volatile with
  | false => rfl
  | true =>
      unfold perm_globvar at h
      rw [hv] at h
      cases h

private theorem ug_init_mem_inj_1
    (p tp : CompCert4Lean.Backend.RTL.program)
    (used : CompCert4Lean.Backend.Unusedglob.IS.t)
    (hvalid : valid_used_set p used) (hmatch : match_prog_1 used p tp)
    (m tm : mem) (hmem : Genv.init_mem p = some m)
    (htmem : Genv.init_mem tp = some tm) :
    Mem.mem_inj (init_meminj p tp) m tm := by
  have hsource := ug_init_mem_characterization _ _ p m hmem
  have htarget := ug_init_mem_characterization _ _ tp tm htmem
  constructor
  · intro b b' delta ofs k prm hmap hp
    rcases init_meminj_invert_strong p tp used hvalid hmatch b b' delta hmap with
      ⟨hdelta, id, gd, hfind, hfind', hdef, hdef', hrefs⟩
    subst delta
    have hs := hsource b gd hdef
    have ht := htarget b' gd hdef'
    cases gd with
    | Gfun f =>
        rcases hs.2 ofs k prm hp with ⟨hofs, hprm⟩
        subst ofs
        subst prm
        change Mem.perm tm b' (ZArith.BinInt.Z.add Z0 Z0) k
          CompCert4Lean.Common.Memtype.Nonempty
        rw [ug_init_zadd_zero]
        exact Mem.perm_cur tm b' Z0 k CompCert4Lean.Common.Memtype.Nonempty ht.1
    | Gvar v =>
        have hsbound := hs.2.1 ofs k prm hp
        have htcur := ht.1 ofs hsbound.1
        have htprm := Mem.perm_implies tm b' ofs Cur (perm_globvar v) prm
          htcur hsbound.2
        change Mem.perm tm b' (ZArith.BinInt.Z.add ofs Z0) k prm
        rw [ug_init_zadd_zero]
        exact Mem.perm_cur tm b' ofs k prm htprm
  · intro b b' delta chunk ofs prm hmap hrange
    rcases init_meminj_invert p tp b b' delta hmap with
      ⟨hdelta, id, hfind, hfind'⟩
    subst delta
    exact ZArith.BinInt.Z.divide_0_r (align_chunk chunk)
  · intro b ofs b' delta hmap hread
    rcases init_meminj_invert_strong p tp used hvalid hmatch b b' delta hmap with
      ⟨hdelta, id, gd, hfind, hfind', hdef, hdef', hrefs⟩
    subst delta
    have hs := hsource b gd hdef
    have ht := htarget b' gd hdef'
    cases gd with
    | Gfun f =>
        have hbad := (hs.2 ofs Cur Readable hread).2
        cases hbad
    | Gvar v =>
        have hsbound := hs.2.1 ofs Cur Readable hread
        have hnonvol := ug_init_nonvolatile_of_readable v hsbound.2
        have hloads := hs.2.2 hnonvol
        have hloadt := ht.2.2 hnonvol
        let sz := init_data_list_size v.gvar_init
        have hgets : Mem.getN (ZArith.BinInt.Z.to_nat sz) Z0
              (PMap.get b m.mem_contents) =
            bytes_of_init_data_list (Genv.globalenv p) v.gvar_init := by
          unfold Mem.loadbytes at hloads
          split at hloads
          · exact Option.some.inj hloads
          · cases hloads
        have hgett : Mem.getN (ZArith.BinInt.Z.to_nat sz) Z0
              (PMap.get b' tm.mem_contents) =
            bytes_of_init_data_list (Genv.globalenv tp) v.gvar_init := by
          unfold Mem.loadbytes at hloadt
          split at hloadt
          · exact Option.some.inj hloadt
          · cases hloadt
        have hbytes := bytes_of_init_inject p tp used hvalid hmatch v.gvar_init (by
          intro rid href
          exact hrefs rid href)
        have hgetrel : list_forall2 (memval_inject (init_meminj p tp))
            (Mem.getN (ZArith.BinInt.Z.to_nat sz) Z0
              (PMap.get b m.mem_contents))
            (Mem.getN (ZArith.BinInt.Z.to_nat sz) Z0
              (PMap.get b' tm.mem_contents)) := by
          rw [hgets, hgett]
          exact hbytes
        have hupper : ZArith.BinInt.Z.lt ofs
            (zAdd Z0 (zOfNat (ZArith.BinInt.Z.to_nat sz))) := by
          have hsizeid := ZArith.Znat.Z2Nat.id sz (init_data_list_size_pos v.gvar_init)
          change ZArith.BinInt.Z.lt ofs
            (ZArith.BinInt.Z.add Z0
              (ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat sz)))
          rw [hsizeid, ug_init_zero_zadd]
          exact hsbound.1.2
        have hmv := Mem_getN_forall2 (memval_inject (init_meminj p tp))
          (PMap.get b m.mem_contents) (PMap.get b' tm.mem_contents)
          ofs (ZArith.BinInt.Z.to_nat sz) Z0 hgetrel hsbound.1.1 hupper
        change memval_inject (init_meminj p tp)
          (ZMap.get ofs (PMap.get b m.mem_contents))
          (ZMap.get (ZArith.BinInt.Z.add ofs Z0) (PMap.get b' tm.mem_contents))
        rw [ug_init_zadd_zero]
        exact hmv

private theorem ug_init_ptrofs_unsigned_range_2
    (ofs : CompCert4Lean.Lib.Integers.ptrofs) :
    ZArith.BinInt.Z.le Z0 (Ptrofs.unsigned ofs) ∧
      ZArith.BinInt.Z.le (Ptrofs.unsigned ofs) Ptrofs.max_unsigned := by
  constructor
  · have hlo := ofs.intrange.1
    change (-1 : Int) < intOfZ ofs.intval at hlo
    change (0 : Int) ≤ intOfZ (Ptrofs.unsigned ofs)
    unfold Ptrofs.unsigned WordCore.unsigned
    omega
  · have hhi := ofs.intrange.2
    change intOfZ ofs.intval < intOfZ Ptrofs.modulus at hhi
    change intOfZ (Ptrofs.unsigned ofs) ≤ intOfZ Ptrofs.max_unsigned
    unfold Ptrofs.unsigned WordCore.unsigned Ptrofs.max_unsigned
    change intOfZ ofs.intval ≤
      intOfZ (ZArith.BinInt.Z.sub Ptrofs.modulus (Zpos xH))
    unfold ZArith.BinInt.Z.sub
    rw [intOfZ_zOfInt]
    have hone : intOfZ (Zpos xH) = 1 := rfl
    rw [hone]
    omega

private theorem ug_init_mem_inj_2
    (p tp : CompCert4Lean.Backend.RTL.program)
    (used : CompCert4Lean.Backend.Unusedglob.IS.t)
    (hvalid : valid_used_set p used) (hmatch : match_prog_1 used p tp)
    (m tm : mem) (hmem : Genv.init_mem p = some m)
    (htmem : Genv.init_mem tp = some tm) :
    Mem.inject (init_meminj p tp) m tm := by
  have hsource := ug_init_mem_characterization _ _ p m hmem
  have htarget := ug_init_mem_characterization _ _ tp tm htmem
  constructor
  · exact ug_init_mem_inj_1 p tp used hvalid hmatch m tm hmem htmem
  · intro b hnot
    cases hmap : init_meminj p tp b with
    | none => rfl
    | some bd =>
        rcases bd with ⟨b', delta⟩
        exfalso
        apply hnot
        rcases init_meminj_invert p tp b b' delta hmap with
          ⟨hdelta, id, hfind, hfind'⟩
        exact Genv.find_symbol_not_fresh _ _ p id b m hmem hfind
  · intro b b' delta hmap
    rcases init_meminj_invert p tp b b' delta hmap with
      ⟨hdelta, id, hfind, hfind'⟩
    exact Genv.find_symbol_not_fresh _ _ tp id b' tm htmem hfind'
  · intro b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hb hmap1 hmap2 hp1 hp2
    rcases init_meminj_invert p tp b1 b1' delta1 hmap1 with
      ⟨hdelta1, id1, hfind1, hfind1'⟩
    rcases init_meminj_invert p tp b2 b2' delta2 hmap2 with
      ⟨hdelta2, id2, hfind2, hfind2'⟩
    by_cases hids : id1 = id2
    · subst id2
      have hblocks : b1 = b2 := Option.some.inj (hfind1.symm.trans hfind2)
      exact False.elim (hb hblocks)
    · left
      exact Genv.global_addresses_distinct _ _ (Genv.globalenv tp)
        id1 id2 b1' b2' hids hfind1' hfind2'
  · intro b b' delta ofs hmap hperm
    rcases init_meminj_invert p tp b b' delta hmap with
      ⟨hdelta, id, hfind, hfind'⟩
    subst delta
    have hrange := ug_init_ptrofs_unsigned_range_2 ofs
    constructor
    · change (0 : Int) ≤ 0
      omega
    constructor
    · change ZArith.BinInt.Z.le Z0
        (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) Z0)
      rw [ug_init_zadd_zero]
      exact hrange.1
    · change ZArith.BinInt.Z.le
        (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) Z0) Ptrofs.max_unsigned
      rw [ug_init_zadd_zero]
      exact hrange.2
  · intro b ofs b' delta k prm hmap hp
    rcases init_meminj_invert_strong p tp used hvalid hmatch b b' delta hmap with
      ⟨hdelta, id, gd, hfind, hfind', hdef, hdef', hrefs⟩
    subst delta
    have hs := hsource b gd hdef
    have ht := htarget b' gd hdef'
    have hp' : Mem.perm tm b' ofs k prm := by
      change Mem.perm tm b' (ZArith.BinInt.Z.add ofs Z0) k prm at hp
      rw [ug_init_zadd_zero] at hp
      exact hp
    left
    cases gd with
    | Gfun f =>
        rcases ht.2 ofs k prm hp' with ⟨hofs, hprm⟩
        subst ofs
        subst prm
        exact Mem.perm_cur m b Z0 k CompCert4Lean.Common.Memtype.Nonempty hs.1
    | Gvar v =>
        have htbound := ht.2.1 ofs k prm hp'
        have hscur := hs.1 ofs htbound.1
        have hsprm := Mem.perm_implies m b ofs Cur (perm_globvar v) prm
          hscur htbound.2
        exact Mem.perm_cur m b ofs k prm hsprm

theorem init_mem_inject : init_mem_injectStatement := by
  intro p tp used hvalid hmatch m hmem
  rcases init_mem_exists p tp used hvalid hmatch m hmem with ⟨tm, htmem⟩
  refine ⟨init_meminj p tp, tm, htmem, ?_, ?_⟩
  · exact ug_init_mem_inj_2 p tp used hvalid hmatch m tm hmem htmem
  · exact init_meminj_preserves_globals p tp used hvalid hmatch

end CompCert4Lean.Backend.Unusedglobproof

namespace CompCert4Lean.Backend.Unusedglobproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values

theorem transf_initial_states : transf_initial_statesStatement := by
  intro p tp used hvalid hmatch S1 hinit
  cases hinit with
  | intro b f m0 hmem hsymb hfun hsig =>
      rcases init_mem_inject p tp used hvalid hmatch m0 hmem with
        ⟨j, tm, htmem, hmeminj, hglobals⟩
      have hmain : kept used p.prog_main := kept_main p used hvalid
      rcases hglobals.symbols_inject_2 p.prog_main b hmain hsymb with
        ⟨b', hsymb', hmap⟩
      have hdef : Genv.find_def (Genv.globalenv p) b = some (.Gfun f) :=
        (Genv.find_funct_ptr_iff (F := fundef) (V := Unit)
          (ge := Genv.globalenv p) (b := b) (f := f)).mp hfun
      rcases hglobals.defs_inject b b' z0 (.Gfun f) hmap hdef with
        ⟨hdef', _, hrefs⟩
      have hfun' : Genv.find_funct_ptr (Genv.globalenv tp) b' = some f :=
        (Genv.find_funct_ptr_iff (F := fundef) (V := Unit)
          (ge := Genv.globalenv tp) (b := b') (f := f)).mpr hdef'
      refine ⟨Callstate [] f [] tm, ?_, ?_⟩
      · apply initial_state.intro b' f tm
        · exact htmem
        · change Genv.find_symbol (Genv.globalenv tp) tp.prog_main = some b'
          rw [match_prog_main hmatch]
          exact hsymb'
        · exact hfun'
        · exact hsig
      · apply match_states_call [] f [] m0 [] [] tm j
        · apply match_stacks_nil m0.nextblock tm.nextblock hglobals
          · rw [← Genv.init_mem_genv_next (F := fundef) (V := Unit)
              (p := p) (m := m0) hmem]
            exact CompCert4Lean.Lib.Coqlib.Ple_refl _
          · rw [← Genv.init_mem_genv_next (F := fundef) (V := Unit)
              (p := tp) (m := tm) htmem]
            exact CompCert4Lean.Lib.Coqlib.Ple_refl _
        · exact hrefs
        · exact Val.inject_list_nil j
        · exact hmeminj

end CompCert4Lean.Backend.Unusedglobproof
