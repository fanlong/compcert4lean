import CompCert4Lean.Backend.PairScheduling
import CompCert4Lean.Backend.LoopUnrollproof

namespace CompCert4Lean.Backend.PairSchedulingproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.PairScheduling
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
open CompCert4Lean.X86.Op

private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

variable (policy : Policy)

def match_prog (source target : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun _ source target => target = PairScheduling.transf_fundef policy source) Eq
    source target

theorem transf_program_match (source : program) :
    match_prog policy source (PairScheduling.transf_program policy source) :=
  @match_transform_program fundef fundef Unit
    (Linker_fundef function) Linker_unit (PairScheduling.transf_fundef policy) source

theorem sig_preserved (source : fundef) :
    funsig (PairScheduling.transf_fundef policy source) = funsig source := by
  cases source <;> rfl

theorem params_preserved (source : function) :
    (PairScheduling.transf_function policy source).fn_params = source.fn_params := rfl

theorem stacksize_preserved (source : function) :
    (PairScheduling.transf_function policy source).fn_stacksize = source.fn_stacksize := rfl

theorem entrypoint_preserved (source : function) :
    (PairScheduling.transf_function policy source).fn_entrypoint =
      normal_pc source.fn_entrypoint := rfl

theorem selected_hint (hints : PTree.t Unit) (source : function) (pc : node)
    (pair : Pair source pc) (selected : pair_at hints source pc = some pair) :
    PTree.get pc hints = some () := by
  cases hint_at : PTree.get pc hints with
  | none => simp [pair_at, hint_at] at selected
  | some hint =>
      cases hint
      simp only [hint_at]

theorem extra_code_at (hints : PTree.t Unit) (source : function) (pc : node)
    (pair : Pair source pc) (selected : pair_at hints source pc = some pair)
    (render : (pc : node) → Pair source pc → instruction) :
    PTree.get pc (extra_code hints source render) = some (render pc pair) := by
  unfold extra_code
  rw [PTree.gmap_filter1 _ _ pc, PTree.gmap _ pc hints,
    selected_hint hints source pc pair selected]
  simp [selected]

theorem regular_code_at (source : function) (pc : node) (instr : instruction)
    (code_at : PTree.get pc source.fn_code = some instr) :
    PTree.get (normal_pc pc) (PairScheduling.transf_function policy source).fn_code =
      some (regular_instruction (policy source) source pc instr) := by
  change positive at pc
  exact (PTree.gNode_proof (.xO pc) _ _ _).trans
    ((PTree.gmap (regular_instruction (policy source) source) pc source.fn_code).trans
      (congrArg (Option.map (regular_instruction (policy source) source pc)) code_at))

theorem first_code_at (source : function) (pc : node) (pair : Pair source pc)
    (selected : pair_at (policy source) source pc = some pair) :
    PTree.get (first_pc pc) (PairScheduling.transf_function policy source).fn_code =
      some (first_instruction pc pair) := by
  change positive at pc
  exact (PTree.gNode_proof (.xI (.xO pc)) _ _ _).trans
    ((PTree.gNode_proof (.xO pc) _ _ _).trans
      (extra_code_at (policy source) source pc pair selected first_instruction))

theorem second_code_at (source : function) (pc : node) (pair : Pair source pc)
    (selected : pair_at (policy source) source pc = some pair) :
    PTree.get (second_pc pc) (PairScheduling.transf_function policy source).fn_code =
      some (second_instruction pc pair) := by
  change positive at pc
  exact (PTree.gNode_proof (.xI (.xI pc)) _ _ _).trans
    ((PTree.gNode_proof (.xI pc) _ _ _).trans
      (extra_code_at (policy source) source pc pair selected second_instruction))

theorem arguments_preserved (arguments : List reg) (result : reg) (value : val)
    (registers : regset) (absent : result ∉ arguments) :
    arguments.map (fun register => Regmap.get register (Regmap.set result value registers)) =
      arguments.map (fun register => Regmap.get register registers) := by
  apply List.map_congr_left
  intro register member
  apply PMap.gso
  intro same
  exact absent (same ▸ member)

theorem register_sets_commute (first second : reg) (first_value second_value : val)
    (registers : regset) (different : first ≠ second) :
    Regmap.set first first_value (Regmap.set second second_value registers) =
      Regmap.set second second_value (Regmap.set first first_value registers) := by
  change positive at first second
  change val × PTree.t val at registers
  rcases registers with ⟨fallback, tree⟩
  change PTree.tree val at tree
  change (fallback, PTree.set first first_value (PTree.set second second_value tree)) =
    (fallback, PTree.set second second_value (PTree.set first first_value tree))
  congr 1
  apply PTree.extensionality
  intro register
  by_cases first_eq : register = first
  · subst register
    rw [PTree.gss, PTree.gso _ _ different, PTree.gss]
  · by_cases second_eq : register = second
    · subst register
      rw [PTree.gso _ _ (Ne.symm different), PTree.gss, PTree.gss]
    · rw [PTree.gso _ _ first_eq, PTree.gso _ _ second_eq,
        PTree.gso _ _ second_eq, PTree.gso _ _ first_eq]

inductive match_frames : stackframe → stackframe → Prop where
  | intro (result : reg) (source : function) (sp : val) (pc : node)
      (registers : regset) :
      match_frames
        (Stackframe result source sp pc registers)
        (Stackframe result (PairScheduling.transf_function policy source) sp
          (normal_pc pc) registers)

variable
  [binary64_certificate : BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate : BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

inductive match_states (environment : genv) : state → state → Prop where
  | regular (stack : List stackframe) (source : function) (sp : val) (pc : node)
      (registers : regset) (memory : mem) (target_stack : List stackframe)
      (stacks : list_forall2 (match_frames policy) stack target_stack) :
      match_states environment
        (State stack source sp pc registers memory)
        (State target_stack (PairScheduling.transf_function policy source) sp
          (normal_pc pc) registers memory)
  | pending (stack : List stackframe) (source : function) (sp : val) (pc : node)
      (registers : regset) (memory : mem) (target_stack : List stackframe)
      (pair : Pair source pc) (value : val)
      (selected : pair_at (policy source) source pc = some pair)
      (evaluated : eval_operation environment sp pair.first_operation
        (pair.first_arguments.map (fun register => Regmap.get register registers)) memory = some value)
      (stacks : list_forall2 (match_frames policy) stack target_stack) :
      match_states environment
        (State stack source sp pair.middle (Regmap.set pair.first_result value registers) memory)
        (State target_stack (PairScheduling.transf_function policy source) sp
          (first_pc pc) registers memory)
  | call (stack : List stackframe) (source : fundef) (args : List val) (memory : mem)
      (target_stack : List stackframe)
      (stacks : list_forall2 (match_frames policy) stack target_stack) :
      match_states environment
        (Callstate stack source args memory)
        (Callstate target_stack (PairScheduling.transf_fundef policy source) args memory)
  | result (stack : List stackframe) (value : val) (memory : mem)
      (target_stack : List stackframe)
      (stacks : list_forall2 (match_frames policy) stack target_stack) :
      match_states environment (Returnstate stack value memory)
        (Returnstate target_stack value memory)

theorem find_function_translated (source target : program)
    (programs : match_prog policy source target) (callee : Sum reg ident)
    (registers : regset) (definition : fundef)
    (found : find_function (Genv.globalenv source) callee registers = some definition) :
    find_function (Genv.globalenv target) callee registers =
      some (PairScheduling.transf_fundef policy definition) := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  cases callee with
  | inl register =>
      exact Genv.find_funct_transf fundef fundef Unit _ source target programs _ _ found
  | inr symbol =>
      simp only [find_function] at found ⊢
      rw [Genv.find_symbol_transf fundef fundef Unit _ source target programs]
      cases lookup : Genv.find_symbol (Genv.globalenv source) symbol with
      | none => simp [lookup] at found
      | some address =>
          simp only [lookup] at found ⊢
          exact Genv.find_funct_ptr_transf fundef fundef Unit _ source target programs _ _ found

theorem operation_step_inv (providers : ExternalCalls) (environment : genv)
    (stack : List stackframe) (source : function) (sp : val) (pc : node)
    (registers : regset) (memory : mem) (operation : operation) (arguments : List reg)
    (result : reg) (successor : node) (events : trace) (after : state)
    (code_at : PTree.get pc source.fn_code = some (.Iop operation arguments result successor))
    (transition : step providers environment
      (State stack source sp pc registers memory) events after) :
    ∃ value, events = E0 ∧
      after = State stack source sp successor (Regmap.set result value registers) memory ∧
      eval_operation environment sp operation
        (arguments.map (fun register => Regmap.get register registers)) memory = some value := by
  cases transition with
  | exec_Iop _ _ _ _ _ _ actual_operation actual_arguments actual_result actual_successor
      value actual_at evaluated =>
      have shape := Option.some.inj (code_at.symm.trans actual_at)
      rcases instruction.Iop.inj shape with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨value, rfl, rfl, evaluated⟩
  | _ => simp_all

set_option maxHeartbeats 800000 in
theorem step_simulation (providers : ExternalCalls) (source target : program)
    (programs : match_prog policy source target)
    (before : state) (events : trace) (after : state)
    (transition : step providers (Genv.globalenv source) before events after)
    (target_before : state)
    (states : match_states policy (Genv.globalenv source) before target_before) :
    ∃ target_after,
      plus (step providers) (Genv.globalenv target) target_before events target_after ∧
      match_states policy (Genv.globalenv source) after target_after := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  have symbols := Genv.find_symbol_transf fundef fundef Unit _ source target programs
  have environments := Genv.senv_transf fundef fundef Unit _ source target programs
  cases states with
  | regular stack func sp pc registers memory target_stack stacks =>
      cases transition with
      | exec_Inop _ _ _ _ _ _ successor code_at =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor
            registers memory target_stack stacks⟩
          apply plus_one _ _ _ _ _ _ _
          apply step.exec_Inop
          simpa [regular_instruction, pair_at, code_at, LoopUnroll.map_instruction] using
            regular_code_at policy func pc _ code_at
      | exec_Iop _ _ _ _ _ _ operation args result successor value code_at evaluated =>
          cases selected : pair_at (policy func) func pc with
          | none =>
              refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor
                (Regmap.set result value registers) memory target_stack stacks⟩
              apply plus_one _ _ _ _ _ _ _
              apply step.exec_Iop (op := operation) (args := args)
              · simpa [regular_instruction, selected, LoopUnroll.map_instruction] using
                  regular_code_at policy func pc _ code_at
              · rw [eval_operation_preserved _ _ _ _ _ _ symbols]
                exact evaluated
          | some pair =>
              have shape := Option.some.inj (code_at.symm.trans pair.first_at)
              rcases instruction.Iop.inj shape with ⟨rfl, rfl, rfl, rfl⟩
              refine ⟨_, ?_, match_states.pending (policy := policy) stack func sp pc registers memory
                target_stack pair value selected evaluated stacks⟩
              apply plus_one _ _ _ _ _ _ _
              apply step.exec_Inop
              simpa [regular_instruction, selected] using regular_code_at policy func pc _ pair.first_at
      | exec_Iload _ _ _ _ _ _ chunk addressing args result successor address value code_at evaluated loaded =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor
            (Regmap.set result value registers) memory target_stack stacks⟩
          apply plus_one _ _ _ _ _ _ _
          apply step.exec_Iload (chunk := chunk) (addr := addressing) (args := args) (a := address)
          · simpa [regular_instruction, pair_at, code_at, LoopUnroll.map_instruction] using
              regular_code_at policy func pc _ code_at
          · rw [eval_addressing_preserved _ _ _ _ _ _ symbols]
            exact evaluated
          · exact loaded
      | exec_Istore _ _ _ _ _ _ chunk addressing args value successor address new_memory code_at evaluated stored =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor
            registers new_memory target_stack stacks⟩
          apply plus_one _ _ _ _ _ _ _
          apply step.exec_Istore (chunk := chunk) (addr := addressing) (args := args)
            (src := value) (a := address)
          · simpa [regular_instruction, pair_at, code_at, LoopUnroll.map_instruction] using
              regular_code_at policy func pc _ code_at
          · rw [eval_addressing_preserved _ _ _ _ _ _ symbols]
            exact evaluated
          · exact stored
      | exec_Icall _ _ _ _ _ _ signature callee args result successor definition code_at found signature_eq =>
          refine ⟨_, ?_, match_states.call (policy := policy) _ definition _ memory _
            (list_forall2.cons _ _ (match_frames.intro (policy := policy) result func sp successor registers) stacks)⟩
          apply plus_one _ _ _ _ _ _ _
          apply step.exec_Icall (sig := signature) (ros := callee)
          · simpa [regular_instruction, pair_at, code_at, LoopUnroll.map_instruction] using
              regular_code_at policy func pc _ code_at
          · exact find_function_translated policy source target programs callee registers definition found
          · rw [sig_preserved]
            exact signature_eq
      | exec_Itailcall _ _ _ _ _ _ signature callee args definition new_memory code_at found signature_eq freed =>
          refine ⟨_, ?_, match_states.call (policy := policy) stack definition _ new_memory target_stack stacks⟩
          apply plus_one _ _ _ _ _ _ _
          apply step.exec_Itailcall (sig := signature) (ros := callee)
          · simpa [regular_instruction, pair_at, code_at, LoopUnroll.map_instruction] using
              regular_code_at policy func pc _ code_at
          · exact find_function_translated policy source target programs callee registers definition found
          · rw [sig_preserved]
            exact signature_eq
          · simpa only [stacksize_preserved] using freed
      | exec_Ibuiltin _ _ _ _ _ _ external args result successor values trace value new_memory code_at evaluated called =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor
            (regmap_setres result value registers) new_memory target_stack stacks⟩
          apply plus_one _ _ _ _ _ _ _
          apply step.exec_Ibuiltin (ef := external) (args := args) (vargs := values)
          · simpa [regular_instruction, pair_at, code_at, LoopUnroll.map_instruction] using
              regular_code_at policy func pc _ code_at
          · exact eval_builtin_args_preserved _ _ _ _ _ _ _ _ _ _ symbols _ _ evaluated
          · exact external_call_symbols_preserved_proof providers external _ _ _ _ _ _ _
              environments called
      | exec_Icond _ _ _ _ _ _ condition args ifso ifnot decision successor code_at evaluated selected =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor
            registers memory target_stack stacks⟩
          apply plus_one _ _ _ _ _ _ _
          apply step.exec_Icond (cond := condition) (args := args)
            (ifso := normal_pc ifso) (ifnot := normal_pc ifnot) (b := decision)
          · simpa [regular_instruction, pair_at, code_at, LoopUnroll.map_instruction] using
              regular_code_at policy func pc _ code_at
          · exact evaluated
          · rw [selected]
            cases decision <;> rfl
      | exec_Ijumptable _ _ _ _ _ _ arg targets index successor code_at evaluated selected =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor
            registers memory target_stack stacks⟩
          apply plus_one _ _ _ _ _ _ _
          apply step.exec_Ijumptable (arg := arg) (tbl := targets.map normal_pc) (n := index)
          · simpa [regular_instruction, pair_at, code_at, LoopUnroll.map_instruction] using
              regular_code_at policy func pc _ code_at
          · exact evaluated
          · rw [list_nth_z_map, selected]
            rfl
      | exec_Ireturn _ _ _ _ _ _ result new_memory code_at freed =>
          refine ⟨_, ?_, match_states.result (policy := policy) stack _ new_memory target_stack stacks⟩
          apply plus_one _ _ _ _ _ _ _
          apply step.exec_Ireturn
          · simpa [regular_instruction, pair_at, code_at, LoopUnroll.map_instruction] using
              regular_code_at policy func pc _ code_at
          · simpa only [stacksize_preserved] using freed
  | pending stack func sp pc registers memory target_stack pair first_value selected first_evaluated stacks =>
      obtain ⟨second_value, rfl, rfl, second_evaluated⟩ := operation_step_inv providers
        (Genv.globalenv source) stack func sp pair.middle
        (Regmap.set pair.first_result first_value registers) memory
        pair.second_operation pair.second_arguments pair.second_result pair.successor
        events after pair.second_at transition
      rw [arguments_preserved pair.second_arguments pair.first_result first_value registers
        pair.second_preserved] at second_evaluated
      have second_target : eval_operation (Genv.globalenv target) sp pair.second_operation
          (pair.second_arguments.map (fun register => Regmap.get register registers)) memory =
            some second_value := by
        rw [eval_operation_preserved _ _ _ _ _ _ symbols]
        exact second_evaluated
      have first_target : eval_operation (Genv.globalenv target) sp pair.first_operation
          (pair.first_arguments.map (fun register =>
            Regmap.get register (Regmap.set pair.second_result second_value registers))) memory =
            some first_value := by
        rw [arguments_preserved pair.first_arguments pair.second_result second_value registers
          pair.first_preserved, eval_operation_preserved _ _ _ _ _ _ symbols]
        exact first_evaluated
      have first_step := step.exec_Iop (xi := providers) (ge := Genv.globalenv target)
        target_stack (PairScheduling.transf_function policy func) sp (first_pc pc)
        registers memory pair.second_operation pair.second_arguments pair.second_result
        (second_pc pc) second_value (first_code_at policy func pc pair selected) second_target
      have second_step := step.exec_Iop (xi := providers) (ge := Genv.globalenv target)
        target_stack (PairScheduling.transf_function policy func) sp (second_pc pc)
        (Regmap.set pair.second_result second_value registers) memory
        pair.first_operation pair.first_arguments pair.first_result (normal_pc pair.successor)
        first_value (second_code_at policy func pc pair selected) first_target
      refine ⟨_, plus_two _ _ _ _ _ _ _ _ _ _ first_step second_step rfl, ?_⟩
      rw [register_sets_commute pair.first_result pair.second_result first_value second_value
        registers pair.distinct]
      exact match_states.regular (policy := policy) stack func sp pair.successor
        (Regmap.set pair.second_result second_value (Regmap.set pair.first_result first_value registers))
        memory target_stack stacks
  | call stack func args memory target_stack stacks =>
      cases transition with
      | exec_function_internal _ func _ _ new_memory frame typed allocated =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func (Vptr frame Ptrofs.zero)
            func.fn_entrypoint (init_regs args func.fn_params) new_memory target_stack stacks⟩
          apply plus_one _ _ _ _ _ _ _
          have signature_eq := sig_preserved policy (.Internal func)
          change (PairScheduling.transf_function policy func).fn_sig = func.fn_sig at signature_eq
          have translated := step.exec_function_internal (xi := providers)
            (ge := Genv.globalenv target) target_stack
            (PairScheduling.transf_function policy func) args memory new_memory frame
            (by simpa only [signature_eq] using typed)
            (by simpa only [stacksize_preserved] using allocated)
          simpa only [entrypoint_preserved, params_preserved, PairScheduling.transf_fundef,
            Common.AST.transf_fundef] using translated
      | exec_function_external _ external _ result trace _ new_memory called =>
          refine ⟨_, ?_, match_states.result (policy := policy) stack result new_memory target_stack stacks⟩
          apply plus_one _ _ _ _ _ _ _
          apply step.exec_function_external
          exact external_call_symbols_preserved_proof providers external _ _ _ _ _ _ _
            environments called
  | result stack value memory target_stack stacks =>
      cases transition with
      | exec_return result func sp pc registers rest _ _ =>
          cases stacks with
          | cons source_frame target_frame frames remaining =>
              cases frames with
              | intro =>
                  refine ⟨_, ?_, match_states.regular (policy := policy) rest func sp pc
                    (Regmap.set result value registers) memory _ remaining⟩
                  apply plus_one _ _ _ _ _ _ _
                  exact step.exec_return _ _ _ _ _ _ _ _

theorem transf_initial_states (source target : program)
    (programs : match_prog policy source target) (initial : state)
    (started : initial_state source initial) :
    ∃ target_initial, initial_state target target_initial ∧
      match_states policy (Genv.globalenv source) initial target_initial := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  cases started with
  | intro address definition memory initialized symbol found signature_eq =>
      refine ⟨Callstate [] (PairScheduling.transf_fundef policy definition) [] memory, ?_,
        match_states.call (policy := policy) [] definition [] memory [] (list_forall2.nil _)⟩
      apply initial_state.intro address (PairScheduling.transf_fundef policy definition) memory
      · exact Genv.init_mem_transf fundef fundef Unit _ source target programs _ initialized
      · rw [programs.2.1, Genv.find_symbol_transf fundef fundef Unit _ source target programs]
        exact symbol
      · exact Genv.find_funct_ptr_transf fundef fundef Unit _ source target programs _ _ found
      · rw [sig_preserved]
        exact signature_eq

theorem transf_final_states (environment : genv) (source target : state) (result : int)
    (states : match_states policy environment source target) (finished : final_state source result) :
    final_state target result := by
  cases finished
  cases states with
  | result _ _ _ target_stack stacks =>
      cases stacks
      exact final_state.intro _ _

theorem transf_program_correct (providers : ExternalCalls) (source target : program)
    (programs : match_prog policy source target) :
    forward_simulation (semantics providers source) (semantics providers target) := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  exact forward_simulation_plus _ _
    (Genv.senv_transf fundef fundef Unit _ source target programs).2.1
    (match_states policy (Genv.globalenv source)) (transf_initial_states policy source target programs)
    (transf_final_states policy (Genv.globalenv source))
    (step_simulation policy providers source target programs)

end CompCert4Lean.Backend.PairSchedulingproof
