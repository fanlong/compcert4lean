import CompCert4Lean.Backend.LoopUnroll
import CompCert4Lean.Backend.Liveness

namespace CompCert4Lean.Backend.PairScheduling

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

abbrev Policy := function → PTree.t Unit

inductive Action where
  | operation (operator : operation) (arguments : List reg) (result : reg)
  | load (chunk : memory_chunk) (mode : addressing) (arguments : List reg) (result : reg)

def Action.arguments : Action → List reg
  | .operation _ arguments _ | .load _ _ arguments _ => arguments

def Action.result : Action → reg
  | .operation _ _ result | .load _ _ _ result => result

def Action.instruction (action : Action) (successor : node) : instruction :=
  match action with
  | .operation operator arguments result => .Iop operator arguments result successor
  | .load chunk mode arguments result => .Iload chunk mode arguments result successor

structure ActionAt (source : function) (pc : node) where
  action : Action
  successor : node
  code_at : PTree.get pc source.fn_code = some (action.instruction successor)

def action_at (source : function) (pc : node) : Option (ActionAt source pc) :=
  match code_at : PTree.get pc source.fn_code with
  | some (.Iop operator arguments result successor) =>
      some { action := .operation operator arguments result
             successor := successor
             code_at := code_at }
  | some (.Iload chunk mode arguments result successor) =>
      some { action := .load chunk mode arguments result
             successor := successor
             code_at := code_at }
  | _ => none

structure Pair (source : function) (pc : node) where
  first : Action
  middle : node
  second : Action
  successor : node
  first_at : PTree.get pc source.fn_code =
    some (first.instruction middle)
  second_at : PTree.get middle source.fn_code =
    some (second.instruction successor)
  first_preserved : second.result ∉ first.arguments
  second_preserved : first.result ∉ second.arguments
  distinct : first.result ≠ second.result

def pair_at (hints : PTree.t Unit) (source : function) (pc : node) : Option (Pair source pc) :=
  if (PTree.get pc hints).isSome then
    match action_at source pc with
    | some first =>
        match action_at source first.successor with
        | some second =>
            if independent : second.action.result ∉ first.action.arguments ∧
                first.action.result ∉ second.action.arguments ∧
                first.action.result ≠ second.action.result then
              some {
                first := first.action
                middle := first.successor
                second := second.action
                successor := second.successor
                first_at := first.code_at
                second_at := second.code_at
                first_preserved := independent.1
                second_preserved := independent.2.1
                distinct := independent.2.2 }
            else none
        | _ => none
    | _ => none
  else none

def normal_pc (pc : node) : node := .xO pc
def first_pc (pc : node) : node := .xI (.xO pc)
def second_pc (pc : node) : node := .xI (.xI pc)

def mapped_pc (hints : PTree.t Unit) (pc : node) : node :=
  match hints with
  | .Empty => pc
  | .Nodes _ => normal_pc pc

def regular_instruction (hints : PTree.t Unit) (source : function)
    (pc : node) (instr : instruction) : instruction :=
  match pair_at hints source pc with
  | none => LoopUnroll.map_instruction (mapped_pc hints) instr
  | some _ => .Inop (first_pc pc)

def first_instruction {source : function} (pc : node) (pair : Pair source pc) : instruction :=
  pair.second.instruction (second_pc pc)

def second_instruction (hints : PTree.t Unit) {source : function}
    (pc : node) (pair : Pair source pc) : instruction :=
  pair.first.instruction (mapped_pc hints pair.successor)

def extra_code (hints : PTree.t Unit) (source : function)
    (render : (pc : node) → Pair source pc → instruction) : code :=
  PTree.map_filter1 (fun entry : node × Unit =>
    (pair_at hints source entry.1).map (render entry.1))
    (PTree.map (fun pc hint => (pc, hint)) hints)

def transf_function (policy : Policy) (source : function) : function :=
  let hints := policy source
  match hints with
  | .Empty => source
  | .Nodes _ =>
      { source with
        fn_code := PTree.Node
          (PTree.map (regular_instruction hints source) source.fn_code) none
          (PTree.Node (extra_code hints source first_instruction) none
            (extra_code hints source (second_instruction hints)))
        fn_entrypoint := mapped_pc hints source.fn_entrypoint }

def transf_fundef (policy : Policy) (source : fundef) : fundef :=
  CompCert4Lean.Common.AST.transf_fundef (transf_function policy) source

def transf_program (policy : Policy) (source : program) : program :=
  CompCert4Lean.Common.AST.transform_program (transf_fundef policy) source

def short_lived (live : Regset.t) (arguments : List reg) : Nat :=
  arguments.eraseDups.countP fun register => !(Regset.mem register live)

private def instruction_registers : instruction → Option (List reg × reg × node)
  | .Iop _ arguments result successor
  | .Iload _ _ arguments result successor => some (arguments, result, successor)
  | _ => none

def pressure_policy (source : function) : PTree.t Unit :=
  let nodes := PTree.elements source.fn_code
  if nodes.length > 512 then PTree.empty Unit else
  let candidates := nodes.filterMap fun (pc, instr) =>
    match instruction_registers instr with
    | some (first_arguments, first_result, middle) =>
        match (PTree.get middle source.fn_code).bind instruction_registers with
        | some (second_arguments, second_result, _) =>
            if second_result ∉ first_arguments ∧ first_result ∉ second_arguments ∧
                first_result ≠ second_result then
              some (pc, middle, first_arguments, second_arguments)
            else none
        | _ => none
    | _ => none
  if candidates.isEmpty then PTree.empty Unit else
  match Liveness.analyze source with
  | none => PTree.empty Unit
  | some live =>
      candidates.foldl (fun hints (pc, middle, first_arguments, second_arguments) =>
        let after := PMap.get middle live
        if short_lived after first_arguments < short_lived after second_arguments then
          PTree.set pc () hints
        else hints) (PTree.empty Unit)

end CompCert4Lean.Backend.PairScheduling
