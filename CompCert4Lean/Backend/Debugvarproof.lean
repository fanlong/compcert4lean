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
