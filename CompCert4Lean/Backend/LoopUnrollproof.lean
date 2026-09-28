import CompCert4Lean.Backend.LoopUnroll

namespace CompCert4Lean.Backend.LoopUnrollproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LoopUnroll
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
    (fun _ source target => target = LoopUnroll.transf_fundef policy source) Eq
    source target

theorem transf_program_match (source : program) :
    match_prog policy source (LoopUnroll.transf_program policy source) :=
  @match_transform_program fundef fundef Unit
    (Linker_fundef function) Linker_unit (LoopUnroll.transf_fundef policy) source

theorem sig_preserved (source : fundef) :
    funsig (LoopUnroll.transf_fundef policy source) = funsig source := by
  cases source with
  | Internal source =>
      simp only [LoopUnroll.transf_fundef, Common.AST.transf_fundef, funsig,
        LoopUnroll.transf_function]
      cases policy source <;> rfl
  | External external => rfl

theorem params_preserved (source : function) :
    (LoopUnroll.transf_function policy source).fn_params = source.fn_params := by
  simp only [LoopUnroll.transf_function]
  cases policy source <;> rfl

theorem stacksize_preserved (source : function) :
    (LoopUnroll.transf_function policy source).fn_stacksize = source.fn_stacksize := by
  simp only [LoopUnroll.transf_function]
  cases policy source <;> rfl

theorem entrypoint_preserved (source : function) :
    (LoopUnroll.transf_function policy source).fn_entrypoint =
      transf_pc policy source initial_copy source.fn_entrypoint := by
  simp only [LoopUnroll.transf_function, transf_pc]
  cases policy source <;> rfl

theorem map_instruction_id (instr : instruction) : map_instruction id instr = instr := by
  cases instr <;> simp [map_instruction]

theorem extra_code_at (route : Route) (source : code) (pc : node) (instr : instruction)
    (code_at : PTree.get pc source = some instr) (copied : route.extra pc = true) :
    PTree.get pc (extra_code route source) = some instr := by
  unfold extra_code
  rw [PTree.gmap_filter1 _ _ pc, PTree.gmap _ pc source, code_at]
  simp [copied]

theorem normalize_copy_valid (route : Route) (copy : Phase) (pc : node) :
    route.extra pc = true ∨ (normalize_copy route copy pc).2.2 = false := by
  cases copied : route.extra pc with
  | false => exact Or.inr (by simp [normalize_copy, copied])
  | true => exact Or.inl rfl

theorem copy_code_at (route : Route) (source : code) (copy : Phase)
    (pc : node) (instr : instruction) (code_at : PTree.get pc source = some instr)
    (valid : route.extra pc = true ∨ copy.2.2 = false) :
    PTree.get (copy_pc copy pc) (copy_code route source) =
      some (transf_instruction route copy pc instr) := by
  change positive at pc
  rcases copy with ⟨first, second, third⟩
  cases first <;> cases second <;> cases third
  · exact (PTree.gNode_proof (.xO (.xO (.xO pc))) _ _ _).trans
      ((PTree.gNode_proof (.xO (.xO pc)) _ _ _).trans
        ((PTree.gNode_proof (.xO pc) _ _ _).trans
          ((PTree.gmap (transf_instruction route (false, false, false)) pc source).trans
            (congrArg (Option.map (transf_instruction route (false, false, false) pc)) code_at))))
  · have copied := extra_code_at route source pc instr code_at (valid.resolve_right (by decide))
    exact (PTree.gNode_proof (.xO (.xO (.xI pc))) _ _ _).trans
      ((PTree.gNode_proof (.xO (.xI pc)) _ _ _).trans
        ((PTree.gNode_proof (.xI pc) _ _ _).trans
          ((PTree.gmap (transf_instruction route (false, false, true)) pc (extra_code route source)).trans
            (congrArg (Option.map (transf_instruction route (false, false, true) pc)) copied))))
  · exact (PTree.gNode_proof (.xO (.xI (.xO pc))) _ _ _).trans
      ((PTree.gNode_proof (.xI (.xO pc)) _ _ _).trans
        ((PTree.gNode_proof (.xO pc) _ _ _).trans
          ((PTree.gmap (transf_instruction route (false, true, false)) pc source).trans
            (congrArg (Option.map (transf_instruction route (false, true, false) pc)) code_at))))
  · have copied := extra_code_at route source pc instr code_at (valid.resolve_right (by decide))
    exact (PTree.gNode_proof (.xO (.xI (.xI pc))) _ _ _).trans
      ((PTree.gNode_proof (.xI (.xI pc)) _ _ _).trans
        ((PTree.gNode_proof (.xI pc) _ _ _).trans
          ((PTree.gmap (transf_instruction route (false, true, true)) pc (extra_code route source)).trans
            (congrArg (Option.map (transf_instruction route (false, true, true) pc)) copied))))
  · exact (PTree.gNode_proof (.xI (.xO (.xO pc))) _ _ _).trans
      ((PTree.gNode_proof (.xO (.xO pc)) _ _ _).trans
        ((PTree.gNode_proof (.xO pc) _ _ _).trans
          ((PTree.gmap (transf_instruction route (true, false, false)) pc source).trans
            (congrArg (Option.map (transf_instruction route (true, false, false) pc)) code_at))))
  · have copied := extra_code_at route source pc instr code_at (valid.resolve_right (by decide))
    exact (PTree.gNode_proof (.xI (.xO (.xI pc))) _ _ _).trans
      ((PTree.gNode_proof (.xO (.xI pc)) _ _ _).trans
        ((PTree.gNode_proof (.xI pc) _ _ _).trans
          ((PTree.gmap (transf_instruction route (true, false, true)) pc (extra_code route source)).trans
            (congrArg (Option.map (transf_instruction route (true, false, true) pc)) copied))))
  · exact (PTree.gNode_proof (.xI (.xI (.xO pc))) _ _ _).trans
      ((PTree.gNode_proof (.xI (.xO pc)) _ _ _).trans
        ((PTree.gNode_proof (.xO pc) _ _ _).trans
          ((PTree.gmap (transf_instruction route (true, true, false)) pc source).trans
            (congrArg (Option.map (transf_instruction route (true, true, false) pc)) code_at))))
  · have copied := extra_code_at route source pc instr code_at (valid.resolve_right (by decide))
    exact (PTree.gNode_proof (.xI (.xI (.xI pc))) _ _ _).trans
      ((PTree.gNode_proof (.xI (.xI pc)) _ _ _).trans
        ((PTree.gNode_proof (.xI pc) _ _ _).trans
          ((PTree.gmap (transf_instruction route (true, true, true)) pc (extra_code route source)).trans
            (congrArg (Option.map (transf_instruction route (true, true, true) pc)) copied))))

theorem transf_function_at (source : function) (copy : Phase) (pc : node)
    (instr : instruction) (code_at : PTree.get pc source.fn_code = some instr) :
    PTree.get (transf_pc policy source copy pc)
        (LoopUnroll.transf_function policy source).fn_code =
      some (map_instruction
        (fun successor => transf_pc policy source
          (next_copy policy source copy pc successor) successor) instr) := by
  change positive at pc
  cases selected : policy source with
  | none =>
      have identity : map_instruction (fun successor : node => successor) instr = instr :=
        map_instruction_id instr
      simpa [LoopUnroll.transf_function, transf_pc, next_copy, selected,
        identity] using code_at
  | some route =>
      simp only [LoopUnroll.transf_function, transf_pc, next_copy, selected]
      exact copy_code_at route source.fn_code (normalize_copy route copy pc) pc instr code_at
        (normalize_copy_valid route copy pc)

inductive match_frames : stackframe → stackframe → Prop where
  | intro (result : reg) (source : function) (sp : val) (pc : node)
      (registers : regset) (copy : Phase) :
      match_frames
        (Stackframe result source sp pc registers)
        (Stackframe result (LoopUnroll.transf_function policy source) sp
          (transf_pc policy source copy pc) registers)

inductive match_states : state → state → Prop where
  | regular (stack : List stackframe) (source : function) (sp : val) (pc : node)
      (registers : regset) (memory : mem) (target_stack : List stackframe) (copy : Phase)
      (stacks : list_forall2 (match_frames policy) stack target_stack) :
      match_states
        (State stack source sp pc registers memory)
        (State target_stack (LoopUnroll.transf_function policy source) sp
          (transf_pc policy source copy pc) registers memory)
  | call (stack : List stackframe) (source : fundef) (args : List val) (memory : mem)
      (target_stack : List stackframe)
      (stacks : list_forall2 (match_frames policy) stack target_stack) :
      match_states
        (Callstate stack source args memory)
        (Callstate target_stack (LoopUnroll.transf_fundef policy source) args memory)
  | result (stack : List stackframe) (value : val) (memory : mem)
      (target_stack : List stackframe)
      (stacks : list_forall2 (match_frames policy) stack target_stack) :
      match_states (Returnstate stack value memory) (Returnstate target_stack value memory)

theorem find_function_translated (source target : program)
    (programs : match_prog policy source target) (callee : Sum reg ident)
    (registers : regset) (definition : fundef)
    (found : find_function (Genv.globalenv source) callee registers = some definition) :
    find_function (Genv.globalenv target) callee registers =
      some (LoopUnroll.transf_fundef policy definition) := by
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

set_option maxHeartbeats 800000 in
theorem step_simulation
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (providers : ExternalCalls) (source target : program)
    (programs : match_prog policy source target)
    (before : state) (events : trace) (after : state)
    (transition : step providers (Genv.globalenv source) before events after)
    (target_before : state) (states : match_states policy before target_before) :
    ∃ target_after,
      step providers (Genv.globalenv target) target_before events target_after ∧
      match_states policy after target_after := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  have symbols := Genv.find_symbol_transf fundef fundef Unit _ source target programs
  have environments := Genv.senv_transf fundef fundef Unit _ source target programs
  cases transition with
  | exec_Inop stack func sp pc registers memory successor code_at =>
      cases states with
      | regular _ _ _ _ _ _ target_stack copy stacks =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor registers memory
            target_stack (next_copy policy func copy pc successor) stacks⟩
          exact step.exec_Inop _ _ _ _ _ _ _ (transf_function_at policy func copy pc _ code_at)
  | exec_Iop stack func sp pc registers memory operation args result successor value code_at evaluated =>
      cases states with
      | regular _ _ _ _ _ _ target_stack copy stacks =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor
            (Regmap.set result value registers) memory target_stack
            (next_copy policy func copy pc successor) stacks⟩
          apply step.exec_Iop (op := operation) (args := args)
          · exact transf_function_at policy func copy pc _ code_at
          · rw [eval_operation_preserved _ _ _ _ _ _ symbols]
            exact evaluated
  | exec_Iload stack func sp pc registers memory chunk addressing args result successor address value code_at evaluated loaded =>
      cases states with
      | regular _ _ _ _ _ _ target_stack copy stacks =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor
            (Regmap.set result value registers) memory target_stack
            (next_copy policy func copy pc successor) stacks⟩
          apply step.exec_Iload (chunk := chunk) (addr := addressing) (args := args) (a := address)
          · exact transf_function_at policy func copy pc _ code_at
          · rw [eval_addressing_preserved _ _ _ _ _ _ symbols]
            exact evaluated
          · exact loaded
  | exec_Istore stack func sp pc registers memory chunk addressing args value successor address new_memory code_at evaluated stored =>
      cases states with
      | regular _ _ _ _ _ _ target_stack copy stacks =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor registers new_memory
            target_stack (next_copy policy func copy pc successor) stacks⟩
          apply step.exec_Istore (chunk := chunk) (addr := addressing) (args := args)
            (src := value) (a := address)
          · exact transf_function_at policy func copy pc _ code_at
          · rw [eval_addressing_preserved _ _ _ _ _ _ symbols]
            exact evaluated
          · exact stored
  | exec_Icall stack func sp pc registers memory signature callee args result successor definition code_at found signature_eq =>
      cases states with
      | regular _ _ _ _ _ _ target_stack copy stacks =>
          refine ⟨_, ?_, match_states.call (policy := policy) _ definition _ memory _
            (list_forall2.cons _ _ (match_frames.intro (policy := policy) result func sp successor registers
              (next_copy policy func copy pc successor)) stacks)⟩
          apply step.exec_Icall (sig := signature) (ros := callee)
          · exact transf_function_at policy func copy pc _ code_at
          · exact find_function_translated policy source target programs callee registers definition found
          · rw [sig_preserved]
            exact signature_eq
  | exec_Itailcall stack func frame pc registers memory signature callee args definition new_memory code_at found signature_eq freed =>
      cases states with
      | regular _ _ _ _ _ _ target_stack copy stacks =>
          refine ⟨_, ?_, match_states.call (policy := policy) stack definition _ new_memory target_stack stacks⟩
          apply step.exec_Itailcall (sig := signature) (ros := callee)
          · exact transf_function_at policy func copy pc _ code_at
          · exact find_function_translated policy source target programs callee registers definition found
          · rw [sig_preserved]
            exact signature_eq
          · simpa only [stacksize_preserved] using freed
  | exec_Ibuiltin stack func sp pc registers memory external args result successor values trace value new_memory code_at evaluated called =>
      cases states with
      | regular _ _ _ _ _ _ target_stack copy stacks =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor
            (regmap_setres result value registers) new_memory target_stack
            (next_copy policy func copy pc successor) stacks⟩
          apply step.exec_Ibuiltin (ef := external) (args := args) (vargs := values)
          · exact transf_function_at policy func copy pc _ code_at
          · exact eval_builtin_args_preserved _ _ _ _ _ _ _ _ _ _ symbols _ _ evaluated
          · exact external_call_symbols_preserved_proof providers external _ _ _ _ _ _ _
              environments called
  | exec_Icond stack func sp pc registers memory condition args ifso ifnot decision successor code_at evaluated selected =>
      cases states with
      | regular _ _ _ _ _ _ target_stack copy stacks =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor registers memory
            target_stack (next_copy policy func copy pc successor) stacks⟩
          apply step.exec_Icond (cond := condition) (args := args)
            (ifso := transf_pc policy func (next_copy policy func copy pc ifso) ifso)
            (ifnot := transf_pc policy func (next_copy policy func copy pc ifnot) ifnot)
            (b := decision)
          · exact transf_function_at policy func copy pc _ code_at
          · exact evaluated
          · rw [selected]
            cases decision <;> rfl
  | exec_Ijumptable stack func sp pc registers memory arg targets index successor code_at evaluated selected =>
      cases states with
      | regular _ _ _ _ _ _ target_stack copy stacks =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp successor registers memory
            target_stack (next_copy policy func copy pc successor) stacks⟩
          apply step.exec_Ijumptable (arg := arg)
            (tbl := targets.map (fun target => transf_pc policy func
              (next_copy policy func copy pc target) target)) (n := index)
          · exact transf_function_at policy func copy pc _ code_at
          · exact evaluated
          · rw [list_nth_z_map, selected]
            rfl
  | exec_Ireturn stack func frame pc registers memory result new_memory code_at freed =>
      cases states with
      | regular _ _ _ _ _ _ target_stack copy stacks =>
          refine ⟨_, ?_, match_states.result (policy := policy) stack _ new_memory target_stack stacks⟩
          apply step.exec_Ireturn
          · exact transf_function_at policy func copy pc _ code_at
          · simpa only [stacksize_preserved] using freed
  | exec_function_internal stack func args memory new_memory frame typed allocated =>
      cases states with
      | call _ _ _ _ target_stack stacks =>
          refine ⟨_, ?_, match_states.regular (policy := policy) stack func (Vptr frame Ptrofs.zero)
            func.fn_entrypoint (init_regs args func.fn_params) new_memory target_stack initial_copy stacks⟩
          have signature_eq := sig_preserved policy (.Internal func)
          change (LoopUnroll.transf_function policy func).fn_sig = func.fn_sig at signature_eq
          have transition := step.exec_function_internal (xi := providers)
            (ge := Genv.globalenv target) target_stack
            (LoopUnroll.transf_function policy func) args memory new_memory frame
            (by simpa only [signature_eq] using typed)
            (by simpa only [stacksize_preserved] using allocated)
          simpa only [entrypoint_preserved, params_preserved, LoopUnroll.transf_fundef,
            Common.AST.transf_fundef] using transition
  | exec_function_external stack external args result trace memory new_memory called =>
      cases states with
      | call _ _ _ _ target_stack stacks =>
          refine ⟨_, ?_, match_states.result (policy := policy) stack result new_memory target_stack stacks⟩
          apply step.exec_function_external
          exact external_call_symbols_preserved_proof providers external _ _ _ _ _ _ _
            environments called
  | exec_return result func sp pc registers stack value memory =>
      cases states with
      | result _ _ _ target_stack stacks =>
          cases stacks with
          | cons source_frame target_frame frames rest =>
              cases frames with
              | intro _ _ _ _ _ copy =>
                  refine ⟨_, ?_, match_states.regular (policy := policy) stack func sp pc
                    (Regmap.set result value registers) memory _ copy rest⟩
                  exact step.exec_return _ _ _ _ _ _ _ _

theorem transf_initial_states (source target : program)
    (programs : match_prog policy source target) (initial : state)
    (started : initial_state source initial) :
    ∃ target_initial, initial_state target target_initial ∧
      match_states policy initial target_initial := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  cases started with
  | intro address definition memory initialized symbol found signature_eq =>
      refine ⟨Callstate [] (LoopUnroll.transf_fundef policy definition) [] memory, ?_,
        match_states.call (policy := policy) [] definition [] memory [] (list_forall2.nil _)⟩
      apply initial_state.intro address (LoopUnroll.transf_fundef policy definition) memory
      · exact Genv.init_mem_transf fundef fundef Unit _ source target programs _ initialized
      · rw [programs.2.1, Genv.find_symbol_transf fundef fundef Unit _ source target programs]
        exact symbol
      · exact Genv.find_funct_ptr_transf fundef fundef Unit _ source target programs _ _ found
      · rw [sig_preserved]
        exact signature_eq

theorem transf_final_states (source target : state) (result : int)
    (states : match_states policy source target) (finished : final_state source result) :
    final_state target result := by
  cases finished
  cases states with
  | result _ _ _ target_stack stacks =>
      cases stacks
      exact final_state.intro _ _

theorem transf_program_correct
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (providers : ExternalCalls) (source target : program)
    (programs : match_prog policy source target) :
    forward_simulation (semantics providers source) (semantics providers target) := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  exact forward_simulation_step _ _
    (Genv.senv_transf fundef fundef Unit _ source target programs).2.1
    (match_states policy) (transf_initial_states policy source target programs)
    (transf_final_states policy) (step_simulation policy providers source target programs)

end CompCert4Lean.Backend.LoopUnrollproof
