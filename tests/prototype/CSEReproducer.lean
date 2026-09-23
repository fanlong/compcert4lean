import CompCert4Lean.Prototype.Services

open CompCert4Lean Backend Common.AST Foundation.Numbers.Rocq.Coq Lib.Maps

def chain (count : Nat) : RTL.function :=
  { fn_sig := { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }
    fn_params := [], fn_stacksize := zOfInt 0, fn_entrypoint := posOfNat 1
    fn_code := (List.range count).foldl (fun code index =>
      PTree.set (posOfNat (index + 1))
        (if index + 1 == count then .Ireturn none else .Inop (posOfNat (index + 2))) code)
      (PTree.empty _) }

example (entry : positive) (code : RTL.code) :
    Kildall.BBlock_solver.basic_block_map entry code RTL.successors_instr =
      Kildall.BBlock_solver.is_basic_block_head entry (Kildall.make_predecessors code RTL.successors_instr) := rfl

def timed (name : String) (count : Nat) (action : Unit → Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  let result ← IO.mkRef (action ())
  let elapsed := (← IO.monoNanosNow) - start
  let result ← result.get
  IO.println (Lean.Json.mkObj [("operation", .str name), ("nodes", Lean.toJson count),
    ("nanoseconds", Lean.toJson elapsed), ("result", Lean.toJson result)]).compress
  return result

def main : IO UInt32 := do
  for count in [1000, 2000, 4000] do
    let function := chain count
    match RTLtyping.type_function Prototype.optimizedCfg function with
    | .Error _ => throw (IO.userError "ill-typed reproducer")
    | .OK _ => pure ()
    let original ← timed "core-basic-block-list" count (fun _ =>
      (Kildall.BBlock_solver.basic_block_list
        (Kildall.BBlock_solver.basic_block_map function.fn_entrypoint function.fn_code RTL.successors_instr)
        function.fn_code).length)
    let control ← timed "precomputed-predecessors-control" count (fun _ =>
      let predecessors := Kildall.make_predecessors function.fn_code RTL.successors_instr
      (Kildall.BBlock_solver.basic_block_list
        (Kildall.BBlock_solver.is_basic_block_head function.fn_entrypoint predecessors) function.fn_code).length)
    unless original == 1 && control == original do throw (IO.userError "block head discrepancy")
    let program : RTL.program :=
      { prog_defs := [(posOfNat 1, .Gfun (.Internal function))]
        prog_public := [posOfNat 1], prog_main := posOfNat 1 }
    let result ← timed "core-CSE-transf-program" count (fun _ =>
      match CSE.transf_program Prototype.optimizedCfg program with
      | .OK output => output.prog_defs.length
      | .Error _ => 0)
    unless result == 1 do throw (IO.userError "core CSE rejected well-typed chain")
  return 0
