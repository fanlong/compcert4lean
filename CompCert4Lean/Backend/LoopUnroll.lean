import CompCert4Lean.Backend.RTL

namespace CompCert4Lean.Backend.LoopUnroll

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Lib.Maps

abbrev Phase := Bool × Bool × Bool
structure Route where
  extra : node → Bool
  advance : Phase → node → node → Phase

abbrev Policy := function → Option Route

def initial_copy : Phase := (false, false, false)

def advance_copy (copy : Phase) : Phase :=
  (!copy.1, if copy.1 then !copy.2.1 else copy.2.1,
    if copy.1 && copy.2.1 then !copy.2.2 else copy.2.2)

def advance_four (copy : Phase) : Phase :=
  (!copy.1, if copy.1 then !copy.2.1 else copy.2.1, false)

def copy_pc : Phase → node → node
  | (false, false, false), pc => .xO (.xO (.xO pc))
  | (false, false, true), pc => .xO (.xO (.xI pc))
  | (false, true, false), pc => .xO (.xI (.xO pc))
  | (false, true, true), pc => .xO (.xI (.xI pc))
  | (true, false, false), pc => .xI (.xO (.xO pc))
  | (true, false, true), pc => .xI (.xO (.xI pc))
  | (true, true, false), pc => .xI (.xI (.xO pc))
  | (true, true, true), pc => .xI (.xI (.xI pc))

def normalize_copy (route : Route) (copy : Phase) (pc : node) : Phase :=
  (copy.1, copy.2.1, copy.2.2 && route.extra pc)

def routed_pc (route : Route) (copy : Phase) (pc : node) : node :=
  copy_pc (normalize_copy route copy pc) pc

def transf_pc (policy : Policy) (source : function) (copy : Phase) (pc : node) : node :=
  match policy source with
  | none => pc
  | some route => routed_pc route copy pc

def next_copy (policy : Policy) (source : function) (copy : Phase)
    (pc successor : node) : Phase :=
  match policy source with
  | none => initial_copy
  | some route => route.advance (normalize_copy route copy pc) pc successor

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
  map_instruction (fun successor => routed_pc route (route.advance copy pc successor) successor)

def extra_code (route : Route) (source : code) : code :=
  PTree.map_filter1
    (fun entry : node × instruction => if route.extra entry.1 then some entry.2 else none)
    (PTree.map (fun pc instr => (pc, instr)) source)

def copy_code (route : Route) (source : code) : code :=
  let selected := extra_code route source
  let pair := fun first second => PTree.Node
    (PTree.map (transf_instruction route (first, second, false)) source) none
    (PTree.map (transf_instruction route (first, second, true)) selected)
  PTree.Node
    (PTree.Node (pair false false) none (pair false true)) none
    (PTree.Node (pair true false) none (pair true true))

def transf_function (policy : Policy) (source : function) : function :=
  match policy source with
  | none => source
  | some route =>
      { source with
        fn_code := copy_code route source.fn_code
        fn_entrypoint := routed_pc route initial_copy source.fn_entrypoint }

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
  some {
    extra := fun _ => false
    advance := fun copy pc successor =>
      let update := fun branch bit =>
        match branch with
        | some (branch_pc, ifso) =>
            if posToNat pc == posToNat branch_pc then posToNat successor == posToNat ifso else bit
        | none => bit
      (update first copy.1, update second copy.2.1, false) }

def division_loop (nodes : List (node × instruction)) (loop : Loop) : Bool :=
  let body := nodes.filter (fun entry => loop.contains entry.1)
  nodes.length ≤ 96 && body.length ≤ 32 &&
    body.countP (fun entry => match entry.2 with | .Istore .. => true | _ => false) ≤ 1 &&
    body.countP (fun entry => match entry.2 with | .Icond .. => true | _ => false) ≤ 2 &&
    body.any (fun entry => match entry.2 with
      | .Iop operation _ _ _ =>
          match operation with
          | .Odiv | .Odivu | .Odivl | .Odivlu | .Odivf | .Odivfs => true
          | _ => false
      | _ => false)

def small_loops (source : function) : Option Route :=
  let nodes := PTree.elements source.fn_code
  if nodes.length > 256 then none else
  let loops := loop_candidates nodes
  if loops.isEmpty then none else
  let expanded := (loops.filter (division_loop nodes)).take 1
  let membership := nodes.foldl (fun membership (pc, _) =>
    match loops.find? (fun loop => loop.contains pc) with
    | none => membership
    | some loop => PTree.set pc loop.header membership) (PTree.empty node)
  some {
    extra := fun pc => expanded.any (fun loop => loop.contains pc)
    advance := fun copy pc successor =>
      match PTree.get pc membership, PTree.get successor membership with
      | some header, some next_header =>
          if posToNat header == posToNat next_header then
            if posToNat successor == posToNat header then
              if expanded.any (fun loop => posToNat loop.header == posToNat header) then advance_copy copy
              else advance_four copy
            else copy
          else initial_copy
      | _, _ => initial_copy }

end CompCert4Lean.Backend.LoopUnroll
