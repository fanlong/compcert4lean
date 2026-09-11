import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Debugvar
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep

/-!
# Correctness surface for debug-variable live-range analysis

Definition-bearing translation of CompCert's `backend/Debugvarproof.v`.
Proof obligations assigned to the later proof-migration phase are represented
by exact transparent proposition descriptors.
-/

namespace CompCert4Lean.Backend.Debugvarproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Debugvar
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Machregs

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig

/-! ## Relational characterization of the transformation -/

def match_prog (cfg : CompilerConfig) (p tp : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun _ f tf => CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf)
    (fun x y : Unit => x = y) p tp

def transf_program_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program),
    CompCert4Lean.Backend.Debugvar.transf_program cfg p = .OK tp →
      match_prog cfg p tp

inductive match_code : code → code → Prop where
  | nil : match_code [] []
  | cons (i : instruction) (before after : Option avail) (c c' : code) :
      match_code c c' →
      match_code (i :: c) (i :: add_delta_ranges before after c')

def diff_sameStatement : Prop :=
  ∀ s : avail, diff s s = []

def delta_state_sameStatement : Prop :=
  ∀ s : Option avail, delta_state s s = ([], [])

def transf_code_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (lm : labelmap) (c : code) (before : Option avail),
    match_code c (transf_code cfg lm before c)

inductive match_function : function → function → Prop where
  | intro (f : function) (c : code) :
      match_code f.fn_code c →
      match_function f
        { fn_sig := f.fn_sig
          fn_stacksize := f.fn_stacksize
          fn_code := c }

def transf_function_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (tf : function),
    CompCert4Lean.Backend.Debugvar.transf_function cfg f = .OK tf →
      match_function f tf

def find_label_add_delta_rangesStatement : Prop :=
  ∀ (lbl : label) (c : code) (before after : Option avail),
    find_label lbl (add_delta_ranges before after c) = find_label lbl c

def find_label_match_recStatement : Prop :=
  ∀ (lbl : label) (c' c tc : code),
    match_code c tc →
    find_label lbl c = some c' →
      ∃ (before after : Option avail) (tc' : code),
        find_label lbl tc = some (add_delta_ranges before after tc') ∧
          match_code c' tc'

def find_label_matchStatement : Prop :=
  ∀ (f tf : function) (lbl : label) (c : code),
    match_function f tf →
    find_label lbl f.fn_code = some c →
      ∃ (before after : Option avail) (tc : code),
        find_label lbl tf.fn_code = some (add_delta_ranges before after tc) ∧
          match_code c tc

/-! ## Preserved global-environment observations -/

def symbols_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ s : ident,
        Genv.find_symbol (Genv.globalenv tprog) s =
          Genv.find_symbol (Genv.globalenv prog) s

def senv_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      Senv.equiv
        (Genv.to_senv (Genv.globalenv prog))
        (Genv.to_senv (Genv.globalenv tprog))

def functions_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ (v : val) (f : fundef),
        Genv.find_funct (Genv.globalenv prog) v = some f →
          ∃ tf,
            Genv.find_funct (Genv.globalenv tprog) v = some tf ∧
              CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf

def function_ptr_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ (b : block) (f : fundef),
        Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
          ∃ tf,
            Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
              CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf

def sig_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f tf : fundef),
    CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf →
      funsig tf = funsig f

def find_function_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ (ros : Sum mreg ident) (ls : locset) (f : fundef),
        find_function (Genv.globalenv prog) ros ls = some f →
          ∃ tf,
            find_function (Genv.globalenv tprog) ros ls = some tf ∧
              CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf

/-! ## Evaluation and state matching -/

def can_eval_safe_argStatement : Prop :=
  ∀ (tprog : program),
    ∀ (rs : locset) (sp : val) (m : mem) (a : builtin_arg loc),
      safe_builtin_arg a →
        ∃ v,
          eval_builtin_arg (Genv.to_senv (Genv.globalenv tprog)) rs sp m a v

def eval_add_delta_rangesStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (tprog : program),
    ∀ (s : List stackframe) (f : function) (sp : val) (c : code)
      (rs : locset) (m : mem) (before after : Option avail),
      star
        (fun ge => Linear.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg xi ge)
        (Genv.globalenv tprog)
        (State s f sp (add_delta_ranges before after c) rs m)
        E0 (State s f sp c rs m)

inductive match_stackframes : stackframe → stackframe → Prop where
  | intro (f : function) (sp : val) (rs : locset) (c : code)
      (tf : function) (tc : code) (before after : Option avail) :
      match_function f tf →
      match_code c tc →
      match_stackframes
        (Stackframe f sp rs c)
        (Stackframe tf sp rs (add_delta_ranges before after tc))

inductive match_states (cfg : CompilerConfig) : state → state → Prop where
  | instr (s : List stackframe) (f : function) (sp : val) (c : code)
      (rs : locset) (m : mem) (tf : function) (ts : List stackframe)
      (tc : code) :
      list_forall2 match_stackframes s ts →
      match_function f tf →
      match_code c tc →
      match_states cfg (State s f sp c rs m) (State ts tf sp tc rs m)
  | call (s : List stackframe) (f : fundef) (rs : locset) (m : mem)
      (tf : fundef) (ts : List stackframe) :
      list_forall2 match_stackframes s ts →
      CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf →
      match_states cfg (Callstate s f rs m) (Callstate ts tf rs m)
  | return (s : List stackframe) (rs : locset) (m : mem)
      (ts : List stackframe) :
      list_forall2 match_stackframes s ts →
      match_states cfg (Returnstate s rs m) (Returnstate ts rs m)

def parent_locset_matchStatement : Prop :=
  ∀ (s ts : List stackframe),
    list_forall2 match_stackframes s ts →
      parent_locset ts = parent_locset s

def transf_step_correctStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ (s1 : state) (t : trace) (s2 : state),
        Linear.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg xi (Genv.globalenv prog) s1 t s2 →
          ∀ ts1, match_states cfg s1 ts1 →
            ∃ ts2,
              plus
                (fun ge => Linear.step
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate) cfg xi ge)
                (Genv.globalenv tprog) ts1 t ts2 ∧
                match_states cfg s2 ts2

def transf_initial_statesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ st1, initial_state prog st1 →
        ∃ st2, initial_state tprog st2 ∧ match_states cfg st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (st1 st2 : state) (r : int),
    match_states cfg st1 st2 → final_state st1 r → final_state st2 r

def transf_program_correctStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog cfg prog tprog →
      forward_simulation
        (Linear.semantics
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg xi prog)
        (Linear.semantics
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg xi tprog)

end CompCert4Lean.Backend.Debugvarproof

namespace CompCert4Lean.Backend.Debugvarproof

open CompCert4Lean.Backend.Debugvar
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem transf_program_match : transf_program_matchStatement := by
  letI : Linker (CompCert4Lean.Backend.Linear.fundef) := by
    change Linker (CompCert4Lean.Common.AST.fundef CompCert4Lean.Backend.Linear.function)
    exact Linker_fundef CompCert4Lean.Backend.Linear.function
  letI : Linker (CompCert4Lean.Backend.Linear.program) := by
    change Linker (CompCert4Lean.Common.AST.program
      (CompCert4Lean.Common.AST.fundef CompCert4Lean.Backend.Linear.function) Unit)
    exact @Linker_prog
      (CompCert4Lean.Common.AST.fundef CompCert4Lean.Backend.Linear.function) Unit
      (Linker_fundef CompCert4Lean.Backend.Linear.function) Linker_unit
  intro cfg p tp h
  unfold match_prog
  unfold CompCert4Lean.Backend.Debugvar.transf_program at h
  unfold CompCert4Lean.Common.AST.transform_partial_program at h
  unfold CompCert4Lean.Common.AST.transform_partial_program2 at h
  have hlist : ∀ (defs : List (ident × globdef CompCert4Lean.Backend.Linear.fundef Unit))
      (tdefs : List (ident × globdef CompCert4Lean.Backend.Linear.fundef Unit)),
      CompCert4Lean.Common.AST.transf_globdefs
        (fun _ f => CompCert4Lean.Backend.Debugvar.transf_fundef cfg f)
        (fun _ v => .OK v) defs = .OK tdefs →
      CompCert4Lean.Lib.Coqlib.list_forall2
        (match_ident_globdef
          (fun _ f tf => CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf)
          (fun x y : Unit => x = y) p) defs tdefs := by
    intro defs
    induction defs with
    | nil =>
        intro tdefs hdefs
        cases tdefs with
        | nil => exact list_forall2.nil _
        | cons hd tl => simp [CompCert4Lean.Common.AST.transf_globdefs] at hdefs
    | cons hd tl ih =>
        cases hd with
        | mk id gd =>
            cases gd with
            | Gfun f =>
                intro tdefs hdefs
                cases htf : CompCert4Lean.Backend.Debugvar.transf_fundef cfg f with
                | Error msg => simp [CompCert4Lean.Common.AST.transf_globdefs, htf] at hdefs
                | OK tf =>
                    cases htail : CompCert4Lean.Common.AST.transf_globdefs
                        (fun _ f => CompCert4Lean.Backend.Debugvar.transf_fundef cfg f)
                        (fun _ v => .OK v) tl with
                    | Error msg => simp [CompCert4Lean.Common.AST.transf_globdefs, htf, htail] at hdefs
                    | OK ttail =>
                        cases tdefs with
                        | nil => simp [CompCert4Lean.Common.AST.transf_globdefs, htf, htail] at hdefs
                        | cons thd ttail' =>
                            simp only [CompCert4Lean.Common.AST.transf_globdefs, htf, htail] at hdefs
                            cases hdefs
                            apply list_forall2.cons
                            · constructor
                              · rfl
                              · apply match_globdef.match_globdef_fun (ctx' := p)
                                · exact linkorder_refl _
                                · exact htf
                            · apply ih
                              exact htail
            | Gvar v =>
                intro tdefs hdefs
                cases htail : CompCert4Lean.Common.AST.transf_globdefs
                    (fun _ f => CompCert4Lean.Backend.Debugvar.transf_fundef cfg f)
                    (fun _ v => .OK v) tl with
                | Error msg =>
                    simp [CompCert4Lean.Common.AST.transf_globdefs,
                      CompCert4Lean.Common.AST.transf_globvar, htail] at hdefs
                | OK ttail =>
                    cases tdefs with
                    | nil => simp [CompCert4Lean.Common.AST.transf_globdefs,
                          CompCert4Lean.Common.AST.transf_globvar, htail] at hdefs
                    | cons thd ttail' =>
                        simp only [CompCert4Lean.Common.AST.transf_globdefs,
                          CompCert4Lean.Common.AST.transf_globvar, htail] at hdefs
                        cases hdefs
                        apply list_forall2.cons
                        · constructor
                          · rfl
                          · apply match_globdef.match_globdef_var
                            exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                        · apply ih
                          exact htail
  cases hdefs : CompCert4Lean.Common.AST.transf_globdefs
      (fun _ f => CompCert4Lean.Backend.Debugvar.transf_fundef cfg f)
          (fun _ v => CompCert4Lean.Common.Errors.OK v) p.prog_defs with
  | Error msg =>
      rw [hdefs] at h
      cases h
  | OK defs =>
      rw [hdefs] at h
      cases h
      exact ⟨hlist p.prog_defs defs hdefs, rfl, rfl⟩

end CompCert4Lean.Backend.Debugvarproof

namespace CompCert4Lean.Backend.Debugvarproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Debugvar
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST

theorem diff_same : diff_sameStatement := by
  intro s
  induction s with
  | nil => exact CompCert4Lean.Backend.Debugvar.diff.eq_1 []
  | cons p s ih =>
      cases p with
      | mk v i =>
          rw [CompCert4Lean.Backend.Debugvar.diff.eq_3]
          have hcmp : CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.compare v v =
              CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.comparison.Eq := by
            change (if _ < _ then _ else if _ = _ then _ else _) = _
            simp
          rw [hcmp]
          cases hinfo : CompCert4Lean.Backend.Debugvar.eq_debuginfo i i with
          | left h => exact ih
          | right h => exact False.elim (h rfl)

theorem delta_state_same : delta_state_sameStatement := by
  intro s
  cases s with
  | none => rfl
  | some s =>
      change (CompCert4Lean.Backend.Debugvar.diff s s,
        CompCert4Lean.Backend.Debugvar.diff s s) = ([], [])
      exact Prod.ext (diff_same s) (diff_same s)

end CompCert4Lean.Backend.Debugvarproof

namespace CompCert4Lean.Backend.Debugvarproof

open CompCert4Lean.Backend.Debugvar
open CompCert4Lean.Backend.Linear

theorem transf_code_match : transf_code_matchStatement := by
  intro cfg lm c
  refine List.brecOn
    (motive := fun c => ∀ before : Option avail,
      match_code c (transf_code cfg lm before c)) c ?_
  intro c rec
  cases c with
  | nil =>
      intro before
      exact match_code.nil
  | cons i rest =>
      intro before
      have generic : match_code (i :: rest)
            (i :: add_delta_ranges before
              (skip_debug_setvar cfg lm (transfer cfg lm before i).snd rest)
              (transf_code cfg lm
                (skip_debug_setvar cfg lm (transfer cfg lm before i).snd rest) rest)) := by
        apply match_code.cons
        exact rec.1 _
      cases i with
      | Lgoto lbl1 =>
          cases rest with
          | nil => exact generic
          | cons j r =>
              cases j with
              | Llabel lbl2 =>
                  let after := get_label lbl2 lm
                  change match_code (Lgoto lbl1 :: Llabel lbl2 :: r)
                    (Lgoto lbl1 :: Llabel lbl2 ::
                      add_delta_ranges before after
                        (transf_code cfg lm after r))
                  have hs : add_delta_ranges before before
                      (Llabel lbl2 :: add_delta_ranges before after
                        (transf_code cfg lm after r)) =
                      (Llabel lbl2 :: add_delta_ranges before after
                        (transf_code cfg lm after r)) := by
                    unfold add_delta_ranges
                    rw [delta_state_same before]
                    rfl
                  rw [← hs]
                  apply match_code.cons
                  apply match_code.cons
                  exact rec.2.1 after
              | _ => exact generic
      | _ => exact generic

end CompCert4Lean.Backend.Debugvarproof

namespace CompCert4Lean.Backend.Debugvarproof

open CompCert4Lean.Backend.Debugvar
open CompCert4Lean.Backend.Linear

theorem transf_function_match : transf_function_matchStatement := by
  intro cfg f tf h
  unfold CompCert4Lean.Backend.Debugvar.transf_function at h
  cases hfun : CompCert4Lean.Backend.Debugvar.ana_function cfg f with
  | none =>
      simp [hfun] at h
  | some lm =>
      simp [hfun] at h
      cases h
      apply match_function.intro
      exact transf_code_match cfg lm f.fn_code (some top)

end CompCert4Lean.Backend.Debugvarproof

namespace CompCert4Lean.Backend.Debugvarproof

open CompCert4Lean.Backend.Debugvar
open CompCert4Lean.Backend.Linear

theorem find_label_add_delta_ranges : find_label_add_delta_rangesStatement := by
  intro lbl c before after
  unfold add_delta_ranges
  cases hdelta : delta_state before after with
  | mk killed born =>
      have hstart : ∀ (vi : CompCert4Lean.Common.AST.ident × debuginfo) (c : code),
          find_label lbl (add_start_range vi c) = find_label lbl c := by
        intro vi c
        simp [add_start_range, find_label, is_label]
      have hend : ∀ (vi : CompCert4Lean.Common.AST.ident × debuginfo) (c : code),
          find_label lbl (add_end_range vi c) = find_label lbl c := by
        intro vi c
        simp [add_end_range, find_label, is_label]
      have hstarts : ∀ (xs : List (CompCert4Lean.Common.AST.ident × debuginfo)) (c : code),
          find_label lbl (xs.foldr add_start_range c) = find_label lbl c := by
        intro xs
        induction xs with
        | nil => intro c; rfl
        | cons x xs ih =>
            intro c
            rw [List.foldr_cons, hstart, ih]
      have hends : ∀ (xs : List (CompCert4Lean.Common.AST.ident × debuginfo)) (c : code),
          find_label lbl (xs.foldr add_end_range c) = find_label lbl c := by
        intro xs
        induction xs with
        | nil => intro c; rfl
        | cons x xs ih =>
            intro c
            rw [List.foldr_cons, hend, ih]
      rw [hends killed, hstarts born]

theorem find_label_match_rec : find_label_match_recStatement := by
  intro lbl c' c tc hmatch hfind
  induction hmatch with
  | nil =>
      simp [find_label] at hfind
  | @cons i before after c tc htail ih =>
      simp only [find_label] at hfind
      by_cases hil : is_label lbl i
      · simp [hil] at hfind
        subst c'
        refine ⟨before, after, tc, ?_, htail⟩
        simp [find_label, hil]
      · simp [hil] at hfind
        rcases ih hfind with ⟨before', after', tc', hfind', hmatch'⟩
        refine ⟨before', after', tc', ?_, hmatch'⟩
        have hadd : find_label lbl (add_delta_ranges before after tc) =
            find_label lbl tc := find_label_add_delta_ranges lbl tc before after
        change find_label lbl (i :: add_delta_ranges before after tc) = _
        simp only [find_label, hil]
        rw [hadd]
        exact hfind'

theorem find_label_match : find_label_matchStatement := by
  intro f tf lbl c hmatch hfind
  cases hmatch with
  | intro tc hcode =>
      exact find_label_match_rec lbl c f.fn_code tc hcode hfind

end CompCert4Lean.Backend.Debugvarproof

namespace CompCert4Lean.Backend.Debugvarproof

open CompCert4Lean.Backend.Debugvar
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

private theorem debugvar_symbol_add_global
    (ge1 ge2 : Genv.t CompCert4Lean.Backend.Linear.fundef Unit) (id : ident)
    (hm : ∀ id', CompCert4Lean.Lib.Maps.PTree.get id' ge2.genv_symb =
      CompCert4Lean.Lib.Maps.PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', CompCert4Lean.Lib.Maps.PTree.get id'
      (CompCert4Lean.Lib.Maps.PTree.set id ge2.genv_next ge2.genv_symb) =
      CompCert4Lean.Lib.Maps.PTree.get id'
      (CompCert4Lean.Lib.Maps.PTree.set id ge1.genv_next ge1.genv_symb) := by
  intro id'
  have h2 := @CompCert4Lean.Lib.Maps.PTree.getSet_equation _ id' id
      ge2.genv_next ge2.genv_symb
  have h1 := @CompCert4Lean.Lib.Maps.PTree.getSet_equation _ id' id
      ge1.genv_next ge1.genv_symb
  by_cases h : id' = id
  · rw [h2, h1]
    simp only [dif_pos h]
    exact congrArg some hn
  · rw [h2, h1]
    simp only [dif_neg h]
    exact hm id'

private theorem debugvar_symbol_add_globals
    (xs ys : List (ident × globdef CompCert4Lean.Backend.Linear.fundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1) xs ys)
    (ge1 ge2 : Genv.t CompCert4Lean.Backend.Linear.fundef Unit)
    (hm : ∀ id', CompCert4Lean.Lib.Maps.PTree.get id' ge2.genv_symb =
      CompCert4Lean.Lib.Maps.PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', CompCert4Lean.Lib.Maps.PTree.get id'
      (Genv.add_globals ge2 ys).genv_symb =
      CompCert4Lean.Lib.Maps.PTree.get id'
      (Genv.add_globals ge1 xs).genv_symb := by
  induction hxy generalizing ge1 ge2 with
  | nil =>
      intro id'
      simpa [Genv.add_globals] using hm id'
  | @cons a xs b ys hab htail ih =>
      rcases a with ⟨aid, ag⟩
      rcases b with ⟨bid, bg⟩
      change aid = bid at hab
      subst bid
      simp only [Genv.add_globals, List.foldl_cons]
      apply ih
      · intro id'
        exact debugvar_symbol_add_global ge1 ge2 aid hm hn id'
      · exact congrArg PArith.BinPos.Pos.succ hn

theorem symbols_preserved : symbols_preservedStatement := by
  intro cfg prog tprog hm id
  letI : Linker CompCert4Lean.Backend.Linear.fundef :=
    Linker_fundef CompCert4Lean.Backend.Linear.function
  letI : Linker (CompCert4Lean.Common.AST.program
      CompCert4Lean.Backend.Linear.fundef Unit) :=
    Linker_prog CompCert4Lean.Backend.Linear.fundef Unit
  unfold match_prog match_program match_program_gen at hm
  have hlist_of : ∀ (xs ys : List (ident × globdef
      CompCert4Lean.Backend.Linear.fundef Unit)),
      list_forall2 (@match_ident_globdef
        (CompCert4Lean.Common.AST.program CompCert4Lean.Backend.Linear.fundef Unit)
        CompCert4Lean.Backend.Linear.fundef Unit
        CompCert4Lean.Backend.Linear.fundef Unit
        (Linker_prog CompCert4Lean.Backend.Linear.fundef Unit)
        (fun _ f tf => CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf)
        (fun x y : Unit => x = y) prog) xs ys →
      list_forall2 (fun a b => a.1 = b.1) xs ys := by
    intro xs ys h
    induction h with
    | nil => exact list_forall2.nil _
    | @cons a xs b ys hab htail ih =>
        apply list_forall2.cons
        · exact hab.1
        · exact ih
  have hlist := hlist_of prog.prog_defs tprog.prog_defs hm.1
  have hempty : ∀ id',
      CompCert4Lean.Lib.Maps.PTree.get id'
        (Genv.empty_genv CompCert4Lean.Backend.Linear.fundef Unit tprog.prog_public).genv_symb =
      CompCert4Lean.Lib.Maps.PTree.get id'
        (Genv.empty_genv CompCert4Lean.Backend.Linear.fundef Unit prog.prog_public).genv_symb := by
    intro id'
    rfl
  have hnext :
      (Genv.empty_genv CompCert4Lean.Backend.Linear.fundef Unit tprog.prog_public).genv_next =
      (Genv.empty_genv CompCert4Lean.Backend.Linear.fundef Unit prog.prog_public).genv_next := rfl
  have hsymb := debugvar_symbol_add_globals prog.prog_defs tprog.prog_defs
    hlist (Genv.empty_genv CompCert4Lean.Backend.Linear.fundef Unit prog.prog_public)
    (Genv.empty_genv CompCert4Lean.Backend.Linear.fundef Unit tprog.prog_public) hempty hnext id
  simpa [Genv.find_symbol, Genv.globalenv] using hsymb

end CompCert4Lean.Backend.Debugvarproof

namespace CompCert4Lean.Backend.Debugvarproof

open CompCert4Lean.Backend.Debugvar
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

private theorem debugvar_match_genvs_add_global
    (R : globdef fundef Unit → globdef fundef Unit → Prop)
    (ge1 ge2 : Genv.t fundef Unit) (id : ident)
    (g1 g2 : globdef fundef Unit)
    (hm : Genv.match_genvs R ge1 ge2) (hrel : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · exact debugvar_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (CompCert4Lean.Lib.Maps.PTree.get b
        (CompCert4Lean.Lib.Maps.PTree.set ge1.genv_next g1 ge1.genv_defs))
      (CompCert4Lean.Lib.Maps.PTree.get b
        (CompCert4Lean.Lib.Maps.PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @CompCert4Lean.Lib.Maps.PTree.getSet_equation _ b
      ge1.genv_next g1 ge1.genv_defs
    have h2 := @CompCert4Lean.Lib.Maps.PTree.getSet_equation _ b
      ge2.genv_next g2 ge2.genv_defs
    by_cases h : b = ge1.genv_next
    · have h' : b = ge2.genv_next := h.trans hm.mge_next.symm
      rw [h1, h2]
      simp only [dif_pos h, dif_pos h']
      exact option_rel.some g1 g2 hrel
    · have h' : b ≠ ge2.genv_next := by
        intro hb
        apply h
        exact hb.trans hm.mge_next
      rw [h1, h2]
      simp only [dif_neg h, dif_neg h']
      exact hm.mge_defs b

private theorem debugvar_match_genvs_add_globals
    (R : globdef fundef Unit → globdef fundef Unit → Prop)
    (xs ys : List (ident × globdef fundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 ge2 : Genv.t fundef Unit) (hm : Genv.match_genvs R ge1 ge2) :
    Genv.match_genvs R (Genv.add_globals ge1 xs) (Genv.add_globals ge2 ys) := by
  induction hxy generalizing ge1 ge2 with
  | nil => simpa [Genv.add_globals] using hm
  | @cons a xs b ys hab htail ih =>
      rcases a with ⟨aid, ag⟩
      rcases b with ⟨bid, bg⟩
      rcases hab with ⟨habid, habg⟩
      change aid = bid at habid
      subst bid
      simp only [Genv.add_globals, List.foldl_cons]
      apply ih
      simpa using (debugvar_match_genvs_add_global R ge1 ge2 aid ag bg hm habg)

private theorem debugvar_add_globals_public
    (ge : Genv.t fundef Unit) (gl : List (ident × globdef fundef Unit)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons idg gl ih =>
      simp only [Genv.add_globals, List.foldl_cons]
      simpa [Genv.add_globals, Genv.add_global] using ih (Genv.add_global ge idg)

private theorem debugvar_globalenvs_match
    (cfg : CompilerConfig)
    (prog tprog : CompCert4Lean.Common.AST.program fundef Unit)
    (hm : match_prog cfg prog tprog) :
    Genv.match_genvs
      (@match_globdef (CompCert4Lean.Common.AST.program fundef Unit)
        fundef Unit fundef Unit
        (@Linker_prog fundef Unit (Linker_fundef function) Linker_unit)
        (fun (_ : CompCert4Lean.Common.AST.program fundef Unit) f tf =>
          CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf)
        (fun _ _ : Unit => True) prog)
      (Genv.globalenv prog) (Genv.globalenv tprog) := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker (CompCert4Lean.Common.AST.program fundef Unit) :=
    Linker_prog fundef Unit
  unfold match_prog match_program match_program_gen at hm
  let R : globdef fundef Unit → globdef fundef Unit → Prop :=
    match_globdef
      (fun (_ : CompCert4Lean.Common.AST.program fundef Unit) f tf =>
        CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf)
      (fun _ _ : Unit => True) prog
  have hempty : Genv.match_genvs R
      (Genv.empty_genv fundef Unit prog.prog_public)
      (Genv.empty_genv fundef Unit tprog.prog_public) := by
    constructor
    · rfl
    · intro id'
      rfl
    · intro b
      exact option_rel.none R
  have hlist_of : ∀ (xs ys : List (ident × globdef fundef Unit)),
      list_forall2 (match_ident_globdef
        (fun (_ : CompCert4Lean.Common.AST.program fundef Unit) f tf =>
          CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf)
        (fun x y : Unit => x = y) prog) xs ys →
      list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys := by
    intro xs ys h
    induction h with
    | nil => exact list_forall2.nil _
    | @cons a xs b ys hab htail ih =>
        apply list_forall2.cons
        · constructor
          · exact hab.1
          · simpa [R] using hab.2
        · exact ih
  have hlist := hlist_of prog.prog_defs tprog.prog_defs hm.1
  exact debugvar_match_genvs_add_globals R prog.prog_defs tprog.prog_defs
    hlist _ _ hempty

theorem function_ptr_translated : function_ptr_translatedStatement := by
  intro cfg prog tprog hm b f hfind
  have hg := debugvar_globalenvs_match cfg prog tprog hm
  unfold Genv.find_funct_ptr Genv.find_def at hfind ⊢
  cases h1 : CompCert4Lean.Lib.Maps.PTree.get b (Genv.globalenv prog).genv_defs with
  | none => simp [h1] at hfind
  | some gd1 =>
      cases gd1 with
      | Gfun f1 =>
          have hf : f1 = f := by simpa [h1] using hfind
          subst f1
          cases h2 : CompCert4Lean.Lib.Maps.PTree.get b (Genv.globalenv tprog).genv_defs with
          | none =>
              have hd := hg.mge_defs b
              simp [h1, h2] at hd
              cases hd
          | some gd2 =>
              cases gd2 with
              | Gfun f2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel =>
                      cases hrel with
                      | match_globdef_fun ctx' f1 f2 horder htrans =>
                          simpa using htrans
              | Gvar v2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel => cases hrel
      | Gvar v1 => simp [h1] at hfind

theorem functions_translated : functions_translatedStatement := by
  intro cfg prog tprog hm v f hfind
  unfold Genv.find_funct at hfind ⊢
  cases v with
  | Vundef => simp at hfind
  | Vint n => simp at hfind
  | Vlong n => simp at hfind
  | Vfloat n => simp at hfind
  | Vsingle n => simp at hfind
  | Vptr b ofs =>
      cases hzero : CompCert4Lean.Lib.Integers.Ptrofs.eq ofs
          CompCert4Lean.Lib.Integers.Ptrofs.zero with
      | false => simp [hzero] at hfind
      | true =>
          simp [hzero] at hfind ⊢
          exact function_ptr_translated cfg prog tprog hm b f hfind

theorem senv_preserved : senv_preservedStatement := by
  intro cfg prog tprog hm
  unfold Senv.equiv
  constructor
  · intro id
    exact symbols_preserved cfg prog tprog hm id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv tprog) id =
      Genv.public_symbol (Genv.globalenv prog) id
    have ht : (Genv.globalenv tprog).genv_public = tprog.prog_public := by
      unfold Genv.globalenv
      exact debugvar_add_globals_public _ _
    have hp : (Genv.globalenv prog).genv_public = prog.prog_public := by
      unfold Genv.globalenv
      exact debugvar_add_globals_public _ _
    unfold Genv.public_symbol
    rw [symbols_preserved cfg prog tprog hm id]
    unfold match_prog match_program match_program_gen at hm
    rw [ht, hp, hm.2.2]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv tprog) b =
      Genv.block_is_volatile (Genv.globalenv prog) b
    have hg := debugvar_globalenvs_match cfg prog tprog hm
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    cases h1 : CompCert4Lean.Lib.Maps.PTree.get b (Genv.globalenv prog).genv_defs with
    | none =>
        cases h2 : CompCert4Lean.Lib.Maps.PTree.get b (Genv.globalenv tprog).genv_defs with
        | none => rfl
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
    | some gd1 =>
        cases h2 : CompCert4Lean.Lib.Maps.PTree.get b (Genv.globalenv tprog).genv_defs with
        | none =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd with
            | some x y hrel =>
                cases hrel with
                | match_globdef_fun ctx' f1 f2 horder htrans => rfl
                | match_globdef_var v1 v2 hvar =>
                    cases hvar
                    rfl

theorem sig_preserved : sig_preservedStatement := by
  intro cfg f tf h
  unfold CompCert4Lean.Backend.Debugvar.transf_fundef
    CompCert4Lean.Common.AST.transf_partial_fundef at h
  cases f with
  | Internal f =>
      cases hfun : CompCert4Lean.Backend.Debugvar.transf_function cfg f with
      | Error msg => simp [hfun] at h
      | OK tf' =>
          simp [hfun] at h
          cases h
          cases hAna : CompCert4Lean.Backend.Debugvar.ana_function cfg f with
          | none => simp [CompCert4Lean.Backend.Debugvar.transf_function, hAna] at hfun
          | some lm =>
              simp [CompCert4Lean.Backend.Debugvar.transf_function, hAna] at hfun
              cases hfun
              rfl
  | External ef =>
      cases h
      rfl

end CompCert4Lean.Backend.Debugvarproof

namespace CompCert4Lean.Backend.Debugvarproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Debugvar
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.Smallstep

theorem find_function_translated : find_function_translatedStatement := by
  intro cfg prog tprog hm ros ls f hfind
  unfold CompCert4Lean.Backend.Linear.find_function at hfind ⊢
  cases ros with
  | inl r =>
      exact functions_translated cfg prog tprog hm
        (ls (CompCert4Lean.Backend.Locations.R r)) f hfind
  | inr symb =>
      change
        (match Genv.find_symbol (Genv.globalenv prog) symb with
        | none => none
        | some b => Genv.find_funct_ptr (Genv.globalenv prog) b) = some f at hfind
      simp only [Sum.rec] at ⊢
      cases hs : Genv.find_symbol (Genv.globalenv prog) symb with
      | none => simp [hs] at hfind
      | some b =>
          have hs' := symbols_preserved cfg prog tprog hm symb
          rw [hs', hs]
          exact function_ptr_translated cfg prog tprog hm b f
            (by simpa [hs] using hfind)

theorem parent_locset_match : parent_locset_matchStatement := by
  intro s ts hmatch
  cases hmatch with
  | nil => rfl
  | cons a b hframe htail =>
      cases hframe
      rfl

theorem can_eval_safe_arg : can_eval_safe_argStatement := by
  intro tprog rs sp m a hsafe
  induction a with
  | BA x =>
      exact ⟨rs x, eval_BA x⟩
  | BA_int n =>
      exact ⟨Vint n, eval_BA_int n⟩
  | BA_long n =>
      exact ⟨Vlong n, eval_BA_long n⟩
  | BA_float n =>
      exact ⟨Vfloat n, eval_BA_float n⟩
  | BA_single n =>
      exact ⟨Vsingle n, eval_BA_single n⟩
  | BA_loadstack chunk ofs =>
      exact False.elim hsafe
  | BA_addrstack ofs =>
      exact False.elim hsafe
  | BA_loadglobal chunk id ofs =>
      exact False.elim hsafe
  | BA_addrglobal id ofs =>
      exact False.elim hsafe
  | BA_splitlong hi lo ihi ilo =>
      rcases hsafe with ⟨hhi, hlo⟩
      rcases ihi hhi with ⟨vhi, ehi⟩
      rcases ilo hlo with ⟨vlo, elo⟩
      exact ⟨Val.longofwords vhi vlo, eval_BA_splitlong hi lo vhi vlo ehi elo⟩
  | BA_addptr a1 a2 =>
      exact False.elim hsafe

end CompCert4Lean.Backend.Debugvarproof
