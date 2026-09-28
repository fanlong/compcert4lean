import CompCert4Lean.Backend.PairSchedulingproof

namespace PairSchedulingTests

open CompCert4Lean CompCert4Lean.Backend
open Foundation.Numbers.Rocq.Coq Common.AST Lib.Maps Lib.Integers PairScheduling

def source : RTL.function :=
  { fn_sig := { sig_args := [.Xint, .Xint, .Xint], sig_res := .Xint, sig_cc := cc_default }
    fn_params := [posOfNat 1, posOfNat 2, posOfNat 3]
    fn_stacksize := Z0
    fn_code :=
      PTree.set (posOfNat 1) (.Ireturn (some (posOfNat 6))) <|
      PTree.set (posOfNat 2) (.Iop .Oxor [posOfNat 3, posOfNat 5] (posOfNat 6) (posOfNat 1)) <|
      PTree.set (posOfNat 3) (.Iop .Omul [posOfNat 1, posOfNat 2] (posOfNat 5) (posOfNat 2)) <|
      PTree.set (posOfNat 4) (.Iop (.Ointconst (Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 7))) [] (posOfNat 3) (posOfNat 3)) <|
      PTree.set (posOfNat 5) (.Icond (.Ccompimm .Ceq Lib.Integers.Int.zero) [posOfNat 3] (posOfNat 4) (posOfNat 3)) <|
      PTree.empty RTL.instruction
    fn_entrypoint := posOfNat 5 }

def hints : PTree.t Unit := PTree.set (posOfNat 4) () (PTree.empty Unit)

def unknown_hint : PTree.t Unit := PTree.set (posOfNat 77) () hints

def read_dependency : RTL.function :=
  { source with
    fn_code := PTree.set (posOfNat 3)
      (.Iop .Omul [posOfNat 3, posOfNat 2] (posOfNat 5) (posOfNat 2)) source.fn_code }

def write_dependency : RTL.function :=
  { source with
    fn_code := PTree.set (posOfNat 4)
      (.Iop .Oneg [posOfNat 5] (posOfNat 3) (posOfNat 3)) source.fn_code }

def same_destination : RTL.function :=
  { source with
    fn_code := PTree.set (posOfNat 3)
      (.Iop .Omul [posOfNat 1, posOfNat 2] (posOfNat 3) (posOfNat 2)) source.fn_code }

def memory_read : RTL.function :=
  { source with
    fn_code := PTree.set (posOfNat 3)
      (.Iload .Mint32 (.Aindexed Z0) [posOfNat 1] (posOfNat 5) (posOfNat 2)) source.fn_code }

example : (pair_at hints source (posOfNat 4)).isSome = true := by decide
example : (pair_at (PTree.empty Unit) source (posOfNat 4)).isNone = true := by decide
example : (pair_at hints read_dependency (posOfNat 4)).isNone = true := by decide
example : (pair_at hints write_dependency (posOfNat 4)).isNone = true := by decide
example : (pair_at hints same_destination (posOfNat 4)).isNone = true := by decide
example : (pair_at hints memory_read (posOfNat 4)).isNone = true := by decide
#eval show IO Unit from do
  unless (pair_at (pressure_policy source) source (posOfNat 4)).isSome do
    throw (IO.userError "pressure policy did not select the independent pair")
example : PTree.get (first_pc (posOfNat 77))
    (transf_function (fun _ => unknown_hint) source).fn_code = none := by decide
example : (PTree.elements (transf_function (fun _ => unknown_hint) source).fn_code).length = 7 := by decide

example : PTree.get (normal_pc (posOfNat 4)) (transf_function (fun _ => hints) source).fn_code =
    some (.Inop (first_pc (posOfNat 4))) := by rfl
example : PTree.get (first_pc (posOfNat 4)) (transf_function (fun _ => hints) source).fn_code =
    some (.Iop .Omul [posOfNat 1, posOfNat 2] (posOfNat 5) (second_pc (posOfNat 4))) := by rfl
example : PTree.get (second_pc (posOfNat 4)) (transf_function (fun _ => hints) source).fn_code =
    some (.Iop (.Ointconst (Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 7))) [] (posOfNat 3) (normal_pc (posOfNat 2))) := by rfl
example : PTree.get (normal_pc (posOfNat 3)) (transf_function (fun _ => hints) source).fn_code =
    some (.Iop .Omul [posOfNat 1, posOfNat 2] (posOfNat 5) (normal_pc (posOfNat 2))) := by rfl

#print axioms PairSchedulingproof.transf_program_correct

end PairSchedulingTests
