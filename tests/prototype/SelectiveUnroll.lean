import CompCert4Lean.Backend.LoopUnrollproof

open CompCert4Lean CompCert4Lean.Backend
open Foundation.Numbers.Rocq.Coq Common.AST Lib.Maps Lib.Integers LoopUnroll

def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def sourceFunction (length : Nat) (division : Bool) : RTL.function :=
  let body := (List.range length).foldl (fun code index =>
    let label := index + 2
    let instr := if label == 2 then
      RTL.instruction.Icond (.Ccompimm .Cgt Int.zero) [posOfNat 1]
        (posOfNat (length + 1)) (posOfNat 1)
      else if label == 3 then
        .Iop (if division then .Odivf else .Oaddf) [posOfNat 2, posOfNat 3]
          (posOfNat 2) (posOfNat 2)
      else .Inop (posOfNat (label - 1))
    PTree.set (posOfNat label) instr code)
    (PTree.set (posOfNat 1) (.Ireturn (some (posOfNat 1))) (PTree.empty RTL.instruction))
  { fn_sig := { sig_args := [.Xint, .Xfloat, .Xfloat], sig_res := .Xint, sig_cc := cc_default }
    fn_params := [posOfNat 1, posOfNat 2, posOfNat 3]
    fn_stacksize := Z0
    fn_code := body
    fn_entrypoint := posOfNat (length + 1) }

def cycle (route : Route) (header : RTL.node) : Nat → Phase
  | 0 => initial_copy
  | steps + 1 => route.advance (cycle route header steps) (posOfNat 2) header

def tests : Except String Unit := do
  for division in [false, true] do
    for length in [8, 16, 24, 32, 33, 40] do
      let source := sourceFunction length division
      let some route := small_loops source | throw "bounded loop was not selected"
      let header := posOfNat (length + 1)
      let copies := if division && length ≤ 32 then 8 else 4
      for steps in [:copies] do
        require (decide (cycle route header steps = initial_copy) == (steps == 0))
          "loop returned to its first copy prematurely"
      require (decide (cycle route header copies = initial_copy))
        "loop exceeded its selected copy count"
      require (decide (route.advance (cycle route header 1) (posOfNat 4) (posOfNat 3) =
          cycle route header 1)) "ordinary loop edge changed the copy"
      require (decide (route.advance (cycle route header 1) (posOfNat 2) (posOfNat 1) =
          initial_copy)) "loop exit retained a duplicated continuation"
      let transformed := transf_function small_loops source
      let extra := if copies == 8 then 4 * length else 0
      require ((PTree.elements transformed.fn_code).length == 4 * (length + 1) + extra)
        "sparse expansion copied instructions outside the chosen loop"
      require (PTree.get (copy_pc (true, true, true) (posOfNat 1)) transformed.fn_code).isNone
        "unused extra exit copy was generated"
      require (PTree.get (routed_pc route (true, true, true) (posOfNat 1)) transformed.fn_code).isSome
        "normalized exit does not have a target instruction"

def main : IO UInt32 := do
  match tests with
  | .ok () => IO.println "selective sparse eight-copy routing: PASS"; return 0
  | .error message => IO.eprintln message; return 1

#print axioms CompCert4Lean.Backend.LoopUnrollproof.transf_program_correct
