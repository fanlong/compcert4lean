import CompCert4Lean.Config
import CompCert4Lean.Driver.Compopts
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Backend.ValueAnalysis
import CompCert4Lean.Backend.ValueDomain
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps
import CompCert4Lean.X86.ConstpropOp
import CompCert4Lean.X86.Machregs
import CompCert4Lean.X86.ValueAOp

/-!
# Constant propagation

Definition-bearing translation of CompCert's `backend/Constprop.v`.
-/

namespace CompCert4Lean.Backend.Constprop

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.ConstpropOp
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev reg := CompCert4Lean.Backend.Registers.reg
private abbrev node := CompCert4Lean.Backend.RTL.node
private abbrev function := CompCert4Lean.Backend.RTL.function
private abbrev instruction := CompCert4Lean.Backend.RTL.instruction
private abbrev fundef := CompCert4Lean.Backend.RTL.fundef
private abbrev program := CompCert4Lean.Backend.RTL.program
private abbrev aenv := CompCert4Lean.Backend.ValueDomain.aenv
private abbrev aval := CompCert4Lean.Backend.ValueDomain.aval
private abbrev romem := CompCert4Lean.Backend.ValueDomain.romem
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

def transf_ros (ae : aenv) (ros : Sum reg ident) : Sum reg ident :=
  match ros with
  | .inl r =>
      match areg ae r with
      | Ptr (Gl symb ofs) =>
          if Ptrofs.eq ofs Ptrofs.zero then .inr symb else ros
      | _ => ros
  | .inr _ => ros

def successor_rec (cfg : CompilerConfig) (n : Nat) (f : function)
    (ae : aenv) (pc : node) : node :=
  match n with
  | 0 => pc
  | n' + 1 =>
      match PTree.get pc f.fn_code with
      | some (Inop s) => successor_rec cfg n' f ae s
      | some (Icond cond args s1 s2) =>
          match resolve_branch
              (CompCert4Lean.X86.ValueAOp.eval_static_condition cfg cond
                (aregs ae args)) with
          | some b => successor_rec cfg n' f ae (if b then s1 else s2)
          | none => pc
      | _ => pc

def num_iter : Nat := 10

def successor (cfg : CompilerConfig) (f : function) (ae : aenv) (pc : node) : node :=
  successor_rec cfg num_iter f ae pc

def builtin_arg_reduction (cfg : CompilerConfig) (ae : aenv) :
    builtin_arg reg → builtin_arg reg
  | .BA r =>
      match areg ae r with
      | I n => .BA_int n
      | L n => .BA_long n
      | F n => if CompCert4Lean.Driver.Compopts.generate_float_constants cfg
        then .BA_float n else .BA r
      | FS n => if CompCert4Lean.Driver.Compopts.generate_float_constants cfg
        then .BA_single n else .BA r
      | _ => .BA r
  | .BA_splitlong hi lo =>
      match builtin_arg_reduction cfg ae hi, builtin_arg_reduction cfg ae lo with
      | .BA_int nhi, .BA_int nlo =>
          .BA_long (CompCert4Lean.Lib.Integers.Int64.ofwords nhi nlo)
      | hi', lo' => .BA_splitlong hi' lo'
  | .BA_addptr a1 a2 =>
      .BA_addptr (builtin_arg_reduction cfg ae a1) (builtin_arg_reduction cfg ae a2)
  | a => a

def builtin_arg_strength_reduction
    (cfg : CompilerConfig) (ae : aenv) (a : builtin_arg reg)
    (c : builtin_arg_constraint) : builtin_arg reg :=
  let a' := builtin_arg_reduction cfg ae a
  if builtin_arg_ok a' c then a' else a

def builtin_args_strength_reduction
    (cfg : CompilerConfig) (ae : aenv) :
      List (builtin_arg reg) → List builtin_arg_constraint →
      List (builtin_arg reg)
  | [], _ => []
  | a :: al, cl =>
      builtin_arg_strength_reduction cfg ae a (cl.headD OK_default) ::
        builtin_args_strength_reduction cfg ae al cl.tail

def debug_strength_reduction (cfg : CompilerConfig) (ae : aenv) :
    List (builtin_arg reg) → List (builtin_arg reg)
  | [] => []
  | a :: al =>
      let a' := builtin_arg_reduction cfg ae a
      let al' := a :: debug_strength_reduction cfg ae al
      match a, a' with
      | .BA _, .BA_int _ => a' :: al'
      | .BA _, .BA_long _ => a' :: al'
      | .BA _, .BA_float _ => a' :: al'
      | .BA _, .BA_single _ => a' :: al'
      | _, _ => al'

def builtin_strength_reduction
    (cfg : CompilerConfig) (ae : aenv) (ef : external_function)
    (al : List (builtin_arg reg)) :
      List (builtin_arg reg) :=
  match ef with
  | .EF_debug _ _ _ => debug_strength_reduction cfg ae al
  | _ => builtin_args_strength_reduction cfg ae al (builtin_constraints ef)

def transf_instr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (f : function)
    (an : PMap.t VA.t) (rm : romem)
    (pc : node) (instr : instruction) : instruction :=
  match PMap.get pc an with
  | .Bot => instr
  | .State ae am =>
      match instr with
      | Iop op args res s =>
          let aargs := aregs ae args
          let a := CompCert4Lean.X86.ValueAOp.eval_static_operation
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) cfg op aargs
          let s' := successor cfg f (AE.set res a ae) s
          match const_for_result cfg cfg.relocation a with
          | some cop => Iop cop [] res s'
          | none =>
              let (op', args') := op_strength_reduction cfg op args aargs
              Iop op' args' res s'
      | Iload chunk addr args dst s =>
          let aargs := aregs ae args
          let a := loadv cfg chunk rm am
            (CompCert4Lean.X86.ValueAOp.eval_static_addressing addr aargs)
          match const_for_result cfg cfg.relocation a with
          | some cop => Iop cop [] dst s
          | none =>
              let (addr', args') := addr_strength_reduction addr args aargs
              Iload chunk addr' args' dst s
      | Istore chunk addr args src s =>
          let aargs := aregs ae args
          let (addr', args') := addr_strength_reduction addr args aargs
          Istore chunk addr' args' src s
      | Icall sig ros args res s =>
          Icall sig (transf_ros ae ros) args res s
      | Itailcall sig ros args =>
          Itailcall sig (transf_ros ae ros) args
      | Ibuiltin ef args res s =>
          let dfl := Ibuiltin ef (builtin_strength_reduction cfg ae ef args) res s
          match ef, res with
          | .EF_builtin name sg, .BR rd =>
              match lookup_builtin_function name sg with
              | some bf =>
                  match eval_static_builtin_function
                      (binary64_certificate := binary64_certificate)
                      (binary32_certificate := binary32_certificate)
                      cfg ae am rm bf args with
                  | some a =>
                      match const_for_result cfg cfg.relocation a with
                      | some cop => Iop cop [] rd s
                      | none => dfl
                  | none => dfl
              | none => dfl
          | _, _ => dfl
      | Icond cond args s1 s2 =>
          let aargs := aregs ae args
          match resolve_branch
              (CompCert4Lean.X86.ValueAOp.eval_static_condition cfg cond aargs) with
          | some b => if b then Inop s1 else Inop s2
          | none =>
              let (cond', args') := cond_strength_reduction cond args aargs
              Icond cond' args' s1 s2
      | Ijumptable arg tbl =>
          match areg ae arg with
          | I n =>
              match list_nth_z tbl (CompCert4Lean.Lib.Integers.Int.unsigned n) with
              | some s => Inop s
              | none => instr
          | _ => instr
      | _ => instr

def transf_function
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (rm : romem) (f : function) : function :=
  let an := CompCert4Lean.Backend.ValueAnalysis.analyze
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) cfg rm f
  { fn_sig := f.fn_sig
    fn_params := f.fn_params
    fn_stacksize := f.fn_stacksize
    fn_code := PTree.map
      (transf_instr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg f an rm)
      f.fn_code
    fn_entrypoint := f.fn_entrypoint }

def transf_fundef
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (rm : romem) (fd : fundef) : fundef :=
  CompCert4Lean.Common.AST.transf_fundef
    (transf_function
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg rm) fd

def transf_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (p : program) : program :=
  let rm := CompCert4Lean.Backend.ValueAnalysis.romem_for cfg p
  CompCert4Lean.Common.AST.transform_program
    (transf_fundef
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg rm) p

end CompCert4Lean.Backend.Constprop
