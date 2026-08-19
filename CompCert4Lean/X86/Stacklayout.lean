import CompCert4Lean.Config
import CompCert4Lean.Foundation.RocqStdlib
import CompCert4Lean.Backend.Bounds
import CompCert4Lean.Common.Memdata
import CompCert4Lean.Common.Separation
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.X86_64.Archi

/-! Definition translation of `x86/Stacklayout.v`. -/

namespace CompCert4Lean.X86.Stacklayout

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Separation
open CompCert4Lean.Lib.Coqlib

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev mem := CompCert4Lean.Common.Memory.mem

private abbrev z0 : Z := .Z0
private abbrev z4 : Z := ZArith.BinInt.Z.of_nat 4
private abbrev z8 : Z := ZArith.BinInt.Z.of_nat 8
private abbrev z32 : Z := ZArith.BinInt.Z.of_nat 32
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zDivide := ZArith.BinInt.Z.divide

/-! ## Activation-record layout definitions -/

def fe_ofs_arg (cfg : CompilerConfig) : Z :=
  if CompCert4Lean.X86_64.Archi.win64 cfg then z32 else z0

def make_env (cfg : CompilerConfig) (b : bounds cfg) : frame_env :=
  let w := if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4
  let olink := align (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing)) w
  let ocs := zAdd olink w
  let ol := align (size_callee_save_area cfg b ocs) z8
  let ostkdata := align (zAdd ol (zMul z4 b.bound_local)) z8
  let oretaddr := align (zAdd ostkdata b.bound_stack_data) w
  let sz := zAdd oretaddr w
  { fe_size := sz
    fe_ofs_link := olink
    fe_ofs_retaddr := oretaddr
    fe_ofs_local := ol
    fe_ofs_callee_save := ocs
    fe_stack_data := ostkdata
    fe_used_callee_save := b.used_callee_save }

/-! ## Statement descriptors for later proof migration -/

def frame_env_separatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (b : bounds cfg) (sp : block) (m : mem) (P : massert),
    let fe := make_env cfg b
    (sepconj
      (range sp z0 (fe_stack_data fe))
      (sepconj
        (range sp (zAdd (fe_stack_data fe) b.bound_stack_data) (fe_size fe))
        P)).m_pred m →
    (sepconj
      (range sp (fe_ofs_local fe)
        (zAdd (fe_ofs_local fe) (zMul z4 b.bound_local)))
      (sepconj
        (range sp (fe_ofs_arg cfg)
          (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing)))
        (sepconj
          (range sp (fe_ofs_link fe)
            (zAdd (fe_ofs_link fe) (size_chunk Mptr)))
          (sepconj
            (range sp (fe_ofs_retaddr fe)
              (zAdd (fe_ofs_retaddr fe) (size_chunk Mptr)))
            (sepconj
              (range sp (fe_ofs_callee_save fe)
                (size_callee_save_area cfg b (fe_ofs_callee_save fe)))
              P))))).m_pred m

def frame_env_rangeStatement : Prop :=
  ∀ (cfg : CompilerConfig) (b : bounds cfg),
    let fe := make_env cfg b
    zLe z0 (fe_stack_data fe) ∧
      zLe (zAdd (fe_stack_data fe) b.bound_stack_data) (fe_size fe)

def frame_env_alignedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (b : bounds cfg),
    let fe := make_env cfg b
    zDivide z8 (fe_ofs_arg cfg) ∧
      zDivide z8 (fe_ofs_local fe) ∧
      zDivide z8 (fe_stack_data fe) ∧
      zDivide (align_chunk Mptr) (fe_ofs_link fe) ∧
      zDivide (align_chunk Mptr) (fe_ofs_retaddr fe)

end CompCert4Lean.X86.Stacklayout
