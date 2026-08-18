import CompCert4Lean.Backend.RTL
import CompCert4Lean.Lib.Postorder

/-!
# Postorder renumbering of RTL control-flow graphs

Definition-bearing translation of CompCert's `backend/Renumber.v`.
-/

namespace CompCert4Lean.Backend.Renumber

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps

def renum_pc (pnum : PTree.t positive) (pc : node) : node :=
  match PTree.get pc pnum with
  | some pc' => pc'
  | none => .xH

def renum_instr (pnum : PTree.t positive) : instruction → instruction
  | Inop s => Inop (renum_pc pnum s)
  | Iop op args res s => Iop op args res (renum_pc pnum s)
  | Iload chunk addr args res s => Iload chunk addr args res (renum_pc pnum s)
  | Istore chunk addr args src s => Istore chunk addr args src (renum_pc pnum s)
  | Icall sg ros args res s => Icall sg ros args res (renum_pc pnum s)
  | i@(Itailcall _ _ _) => i
  | Ibuiltin ef args res s => Ibuiltin ef args res (renum_pc pnum s)
  | Icond cond args s1 s2 =>
      Icond cond args (renum_pc pnum s1) (renum_pc pnum s2)
  | Ijumptable arg tbl => Ijumptable arg (tbl.map (renum_pc pnum))
  | i@(Ireturn _) => i

def renum_node (pnum : PTree.t positive) (c' : code)
    (pc : node) (i : instruction) : code :=
  match PTree.get pc pnum with
  | none => c'
  | some pc' => PTree.set pc' (renum_instr pnum i) c'

def renum_cfg (pnum : PTree.t positive) (c : code) : code :=
  PTree.fold (renum_node pnum) c (PTree.empty instruction)

def transf_function (f : function) : function :=
  let pnum :=
    CompCert4Lean.Lib.Postorder.postorder (successors_map f) f.fn_entrypoint
  { fn_sig := f.fn_sig
    fn_params := f.fn_params
    fn_stacksize := f.fn_stacksize
    fn_code := renum_cfg pnum f.fn_code
    fn_entrypoint := renum_pc pnum f.fn_entrypoint }

def transf_fundef (fd : fundef) : fundef :=
  CompCert4Lean.Common.AST.transf_fundef transf_function fd

def transf_program (p : program) : program :=
  CompCert4Lean.Common.AST.transform_program transf_fundef p

end CompCert4Lean.Backend.Renumber
