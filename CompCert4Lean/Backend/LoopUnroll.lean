import CompCert4Lean.Backend.RTL

namespace CompCert4Lean.Backend.LoopUnroll

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Lib.Maps

abbrev Phase := Bool × Bool
abbrev Route := Phase → node → node → Phase
abbrev Policy := function → Option Route

def initial_copy : Phase := (false, false)

def advance_copy (copy : Phase) : Phase :=
  (!copy.1, if copy.1 then !copy.2 else copy.2)

def copy_pc : Phase → node → node
  | (false, false), pc => .xO (.xO pc)
  | (false, true), pc => .xO (.xI pc)
  | (true, false), pc => .xI (.xO pc)
  | (true, true), pc => .xI (.xI pc)

def transf_pc (policy : Policy) (source : function) (copy : Phase) (pc : node) : node :=
  match policy source with
  | none => pc
  | some _ => copy_pc copy pc

def next_copy (policy : Policy) (source : function) (copy : Phase)
    (pc successor : node) : Phase :=
  match policy source with
  | none => initial_copy
  | some route => route copy pc successor

def map_instruction (successor : node → node) : instruction → instruction
  | .Inop target => .Inop (successor target)
  | .Iop operation args result target => .Iop operation args result (successor target)
  | .Iload chunk addressing args result target =>
      .Iload chunk addressing args result (successor target)
  | .Istore chunk addressing args source target =>
      .Istore chunk addressing args source (successor target)
  | .Icall signature callee args result target =>
      .Icall signature callee args result (successor target)
  | .Itailcall signature callee args => .Itailcall signature callee args
  | .Ibuiltin external args result target => .Ibuiltin external args result (successor target)
  | .Icond condition args ifso ifnot => .Icond condition args (successor ifso) (successor ifnot)
  | .Ijumptable arg targets => .Ijumptable arg (targets.map successor)
  | .Ireturn result => .Ireturn result

def transf_instruction (route : Route) (copy : Phase) (pc : node) : instruction → instruction :=
  map_instruction (fun successor => copy_pc (route copy pc successor) successor)

def transf_function (policy : Policy) (source : function) : function :=
  match policy source with
  | none => source
  | some route =>
      { source with
        fn_code := PTree.Node
          (PTree.Node
            (PTree.map (transf_instruction route (false, false)) source.fn_code) none
            (PTree.map (transf_instruction route (false, true)) source.fn_code)) none
          (PTree.Node
            (PTree.map (transf_instruction route (true, false)) source.fn_code) none
            (PTree.map (transf_instruction route (true, true)) source.fn_code))
        fn_entrypoint := copy_pc initial_copy source.fn_entrypoint }

def transf_fundef (policy : Policy) (source : fundef) : fundef :=
  CompCert4Lean.Common.AST.transf_fundef (transf_function policy) source

def transf_program (policy : Policy) (source : program) : program :=
  CompCert4Lean.Common.AST.transform_program (transf_fundef policy) source

structure Loop where
  header : node
  first : Nat
  last : Nat

def Loop.contains (loop : Loop) (pc : node) : Bool :=
  loop.first <= posToNat pc && posToNat pc <= loop.last

def Loop.overlaps (left right : Loop) : Bool :=
  left.first <= right.last && right.first <= left.last

def loop_instruction : instruction → Bool
  | .Icall .. | .Itailcall .. | .Ibuiltin .. | .Ijumptable .. => false
  | _ => true

def loop_candidates (nodes : List (node × instruction)) : List Loop :=
  let candidates := nodes.flatMap fun (pc, instr) =>
    (successors_instr instr).filterMap fun successor =>
      let first := posToNat pc
      let last := posToNat successor
      if first < last && last - first < 48 then
        some { header := successor, first, last }
      else none
  let candidates := candidates.mergeSort fun left right =>
    left.last - left.first <= right.last - right.first
  candidates.foldl (fun selected candidate =>
    if selected.length >= 8 || selected.any (Loop.overlaps candidate) then selected
    else if nodes.all (fun (pc, instr) =>
        !candidate.contains pc || loop_instruction instr) then
      candidate :: selected
    else selected) []

def acyclic_paths (source : function) : Option Route :=
  let nodes := PTree.elements source.fn_code
  if nodes.length > 128 then none else
  let acyclic := nodes.all fun (pc, instr) =>
    (successors_instr instr).all (fun successor => posToNat successor < posToNat pc)
  if !acyclic then none else
  let branches := nodes.filterMap fun (pc, instr) =>
    match instr with
    | .Icond _ _ ifso ifnot =>
        if posToNat ifso == posToNat ifnot then none else some (pc, ifso)
    | _ => none
  if branches.isEmpty || branches.length > 2 then none else
  let first := branches.head?
  let second := (branches.drop 1).head?
  some (fun copy pc successor =>
    let update := fun branch bit =>
      match branch with
      | some (branch_pc, ifso) =>
          if posToNat pc == posToNat branch_pc then posToNat successor == posToNat ifso else bit
      | none => bit
    (update first copy.1, update second copy.2))

def small_loops (source : function) : Option Route :=
  let nodes := PTree.elements source.fn_code
  if nodes.length > 256 then none else
  let loops := loop_candidates nodes
  if loops.isEmpty then none else
  let membership := nodes.foldl (fun membership (pc, _) =>
    match loops.find? (fun loop => loop.contains pc) with
    | none => membership
    | some loop => PTree.set pc loop.header membership) (PTree.empty node)
  some (fun copy pc successor =>
    match PTree.get pc membership, PTree.get successor membership with
    | some header, some next_header =>
        if posToNat header == posToNat next_header then
          if posToNat successor == posToNat header then advance_copy copy else copy
        else initial_copy
    | _, _ => initial_copy)

end CompCert4Lean.Backend.LoopUnroll
