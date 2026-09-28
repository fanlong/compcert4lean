import CompCert4Lean.Backend.LoopUnroll
import CompCert4Lean.Backend.Liveness

namespace CompCert4Lean.Backend.PairScheduling

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

abbrev Policy := function → PTree.t Unit

structure Pair (source : function) (pc : node) where
  first_operation : operation
  first_arguments : List reg
  first_result : reg
  middle : node
  second_operation : operation
  second_arguments : List reg
  second_result : reg
  successor : node
  first_at : PTree.get pc source.fn_code =
    some (.Iop first_operation first_arguments first_result middle)
  second_at : PTree.get middle source.fn_code =
    some (.Iop second_operation second_arguments second_result successor)
  first_preserved : second_result ∉ first_arguments
  second_preserved : first_result ∉ second_arguments
  distinct : first_result ≠ second_result

def pair_at (hints : PTree.t Unit) (source : function) (pc : node) : Option (Pair source pc) :=
  if (PTree.get pc hints).isSome then
    match first_at : PTree.get pc source.fn_code with
    | some (.Iop first_operation first_arguments first_result middle) =>
        match second_at : PTree.get middle source.fn_code with
        | some (.Iop second_operation second_arguments second_result successor) =>
            if independent : second_result ∉ first_arguments ∧
                first_result ∉ second_arguments ∧ first_result ≠ second_result then
              some {
                first_operation := first_operation
                first_arguments := first_arguments
                first_result := first_result
                middle := middle
                second_operation := second_operation
                second_arguments := second_arguments
                second_result := second_result
                successor := successor
                first_at := first_at
                second_at := second_at
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

def regular_instruction (hints : PTree.t Unit) (source : function)
    (pc : node) (instr : instruction) : instruction :=
  match pair_at hints source pc with
  | none => LoopUnroll.map_instruction normal_pc instr
  | some _ => .Inop (first_pc pc)

def first_instruction {source : function} (pc : node) (pair : Pair source pc) : instruction :=
  .Iop pair.second_operation pair.second_arguments pair.second_result (second_pc pc)

def second_instruction {source : function} (pc : node) (pair : Pair source pc) : instruction :=
  .Iop pair.first_operation pair.first_arguments pair.first_result (normal_pc pair.successor)

def extra_code (hints : PTree.t Unit) (source : function)
    (render : (pc : node) → Pair source pc → instruction) : code :=
  PTree.map_filter1 (fun entry : node × Unit =>
    (pair_at hints source entry.1).map (render entry.1))
    (PTree.map (fun pc hint => (pc, hint)) hints)

def transf_function (policy : Policy) (source : function) : function :=
  let hints := policy source
  { source with
    fn_code := PTree.Node
      (PTree.map (regular_instruction hints source) source.fn_code) none
      (PTree.Node (extra_code hints source first_instruction) none
        (extra_code hints source second_instruction))
    fn_entrypoint := normal_pc source.fn_entrypoint }

def transf_fundef (policy : Policy) (source : fundef) : fundef :=
  CompCert4Lean.Common.AST.transf_fundef (transf_function policy) source

def transf_program (policy : Policy) (source : program) : program :=
  CompCert4Lean.Common.AST.transform_program (transf_fundef policy) source

def short_lived (live : Regset.t) (arguments : List reg) : Nat :=
  arguments.eraseDups.countP fun register => !(Regset.mem register live)

def pressure_policy (source : function) : PTree.t Unit :=
  let nodes := PTree.elements source.fn_code
  if nodes.length > 256 then PTree.empty Unit else
  let candidates := nodes.filterMap fun (pc, instr) =>
    match instr with
    | .Iop _ first_arguments first_result middle =>
        match PTree.get middle source.fn_code with
        | some (.Iop _ second_arguments second_result _) =>
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
