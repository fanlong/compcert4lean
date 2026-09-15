import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.CSE
import CompCert4Lean.Backend.CSEdomain
import CompCert4Lean.Backend.Kildall
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Backend.ValueAnalysis
import CompCert4Lean.Backend.ValueDomain
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Memdata
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps
import CompCert4Lean.X86.Op

/-!
# Correctness surface for common-subexpression elimination

Executable definitions mirror the source proof module. Proof-bearing source
declarations are retained as transparent statement descriptors for a later
proof-migration phase.
-/

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Backend.CSE
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Backend.Kildall
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev reg := CompCert4Lean.Backend.Registers.reg
private abbrev node := CompCert4Lean.Backend.RTL.node
private abbrev function := CompCert4Lean.Backend.RTL.function
private abbrev instruction := CompCert4Lean.Backend.RTL.instruction
private abbrev program := CompCert4Lean.Backend.RTL.program
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev regset := CompCert4Lean.Backend.RTL.regset
private abbrev state := CompCert4Lean.Backend.RTL.state
private abbrev stackframe := CompCert4Lean.Backend.RTL.stackframe
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev memval := CompCert4Lean.Common.Memdata.memval
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev z0 : Z := .Z0
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zToNat := ZArith.BinInt.Z.to_nat
private abbrev zDivide := ZArith.BinInt.Z.divide

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

def match_prog (cfg : CompilerConfig) (prog tprog : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun p f tf =>
      CSE.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap p) (romem_for cfg p) f = OK tf)
    (fun x y : Unit => x = y) prog tprog

def valu_agree (valu1 valu2 : valuation) (upto : valnum) : Prop :=
  ∀ v, Plt v upto → valu2 v = valu1 v

def transf_function' (f : function) (cu : program)
    (approxs : PMap.t numbering) : function :=
  { fn_sig := f.fn_sig
    fn_params := f.fn_params
    fn_stacksize := f.fn_stacksize
    fn_code := transf_code (prog_defmap cu) approxs f.fn_code
    fn_entrypoint := f.fn_entrypoint }

def regs_lessdef (rs1 rs2 : regset) : Prop :=
  ∀ r, Val.lessdef (Regmap.get r rs1) (Regmap.get r rs2)

def analyze (cfg : CompilerConfig) (cu : program) (f : function) :=
  CSE.analyze
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    cfg f (prog_defmap cu)
    (vanalyze
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg (romem_for cfg cu) f)

inductive match_stackframes
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (prog : program) :
    List stackframe → List stackframe → Prop where
  | nil : match_stackframes
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog [] []
  | match_stackframes_cons (res : reg) (sp : val) (pc : node) (rs : regset)
      (f : function) (s : List stackframe) (rs' : regset) (s' : List stackframe)
      (cu : program) (approx : PMap.t numbering)
      (link : linkorder cu prog)
      (analyze : CSEproof.analyze
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg cu f = some approx)
      (sat : ∀ v m, ∃ valu,
        numbering_holds
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          valu (Genv.globalenv prog) sp
          (Regmap.set res v rs) m (PMap.get pc approx))
      (rld : regs_lessdef rs rs')
      (stacks : match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog s s') :
      match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog
        (Stackframe res f sp pc rs :: s)
        (Stackframe res (transf_function' f cu approx) sp pc rs' :: s')

inductive match_states
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (prog : program) :
    state → state → Prop where
  | intro (s : List stackframe) (sp : val) (pc : node) (rs : regset) (m : mem)
      (s' : List stackframe) (rs' : regset) (m' : mem) (f : function)
      (cu : program) (approx : PMap.t numbering)
      (link : linkorder cu prog)
      (analyze : CSEproof.analyze
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg cu f = some approx)
      (sat : ∃ valu,
        numbering_holds
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          valu (Genv.globalenv prog) sp rs m
          (PMap.get pc approx))
      (rld : regs_lessdef rs rs')
      (mext : Mem.extends m m')
      (stacks : match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog s s') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg prog (State s f sp pc rs m)
        (State s' (transf_function' f cu approx) sp pc rs' m')
  | call (s : List stackframe) (f tf : fundef) (args : List val) (m : mem)
      (s' : List stackframe) (args' : List val) (m' : mem) (cu : program)
      (link : linkorder cu prog)
      (stacks : match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog s s')
      (tfd : CSE.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu) (romem_for cfg cu) f = OK tf)
      (args_lessdef : Val.lessdef_list args args')
      (mext : Mem.extends m m') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg prog (Callstate s f args m) (Callstate s' tf args' m')
  | return (s s' : List stackframe) (v v' : val) (m m' : mem)
      (stacks : match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog s s')
      (res : Val.lessdef v v')
      (mext : Mem.extends m m') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg prog (Returnstate s v m) (Returnstate s' v' m')

def eventually (prog : program)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls) (n : Nat) (s : state)
    (P : state → Prop) : Prop :=
  CompCert4Lean.Common.Smallstep.eventually
    (fun ge => RTL.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge)
    RTL.final_state (Genv.globalenv prog) n s P

export match_stackframes (match_stackframes_cons)

/-! Exact statement descriptors for the later proof-migration phase. -/

variable (cfg : CompilerConfig)

def transf_program_matchStatement : Prop :=
  ∀ (prog tprog : program),
    CSE.transf_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog = OK tprog →
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog

def wf_equation_incrStatement : Prop :=
  ∀ (next1 next2 : valnum) (e : equation),
    wf_equation next1 e → Ple next1 next2 → wf_equation next2 e

def valu_agree_reflStatement : Prop :=
  ∀ (valu : valuation) (upto : valnum), valu_agree valu valu upto

def valnums_val_extenStatement : Prop :=
  ∀ (valu1 : valuation) (upto : valnum) (valu2 : valuation)
    (hagree : valu_agree valu1 valu2 upto) (vl : List valnum),
    (∀ v, v ∈ vl → Plt v upto) →
      List.map valu2 vl = List.map valu1 vl

def builtin_arg_val_extenStatement : Prop :=
  ∀ (valu1 : valuation) (upto : valnum) (valu2 : valuation)
    (hagree : valu_agree valu1 valu2 upto) (ge : genv) (sp : val) (m : mem)
    (a : builtin_arg valnum) (v : val),
    eval_builtin_arg (Genv.to_senv ge) valu1 sp m a v →
    (∀ vn, vn ∈ params_of_builtin_arg a → Plt vn upto) →
    eval_builtin_arg (Genv.to_senv ge) valu2 sp m a v

def builtin_args_val_extenStatement : Prop :=
  ∀ (valu1 : valuation) (upto : valnum) (valu2 : valuation)
    (hagree : valu_agree valu1 valu2 upto) (ge : genv) (sp : val) (m : mem)
    (al : List (builtin_arg valnum)) (vl : List val),
    eval_builtin_args (Genv.to_senv ge) valu1 sp m al vl →
    (∀ vn, vn ∈ params_of_builtin_args al → Plt vn upto) →
    eval_builtin_args (Genv.to_senv ge) valu2 sp m al vl

def rhs_eval_to_extenStatement : Prop :=
  ∀ (valu1 : valuation) (upto : valnum) (valu2 : valuation)
    (hagree : valu_agree valu1 valu2 upto) (ge : genv) (sp : val) (m : mem)
    (r : rhs) (v : val),
    rhs_eval_to
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu1 ge sp m r v →
    (∀ vn, vn ∈ valnums_rhs r → Plt vn upto) →
    rhs_eval_to
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu2 ge sp m r v

def rhs_valid_extenStatement : Prop :=
  ∀ (valu1 : valuation) (upto : valnum) (valu2 : valuation)
    (hagree : valu_agree valu1 valu2 upto) (ge : genv) (sp : val) (r : rhs),
    rhs_valid valu1 ge sp r →
    (∀ vn, vn ∈ valnums_rhs r → Plt vn upto) →
    rhs_valid valu2 ge sp r

def equation_holds_extenStatement : Prop :=
  ∀ (valu1 : valuation) (upto : valnum) (valu2 : valuation)
    (hagree : valu_agree valu1 valu2 upto) (ge : genv) (sp : val) (m : mem)
    (e : equation),
    equation_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu1 ge sp m e →
    wf_equation upto e →
    equation_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu2 ge sp m e

def valnum_reg_holdsStatement : Prop :=
  ∀ (valu1 : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering) (r : reg) (n' : numbering) (v : valnum),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu1 ge sp rs m n →
    valnum_reg n r = (n', v) →
    ∃ valu2,
      numbering_holds
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) valu2 ge sp rs m n' ∧
      Regmap.get r rs = valu2 v ∧
      valu_agree valu1 valu2 n.num_next ∧
      Plt v n'.num_next ∧
      Ple n.num_next n'.num_next

def valnum_regs_holdsStatement : Prop :=
  ∀ (rl : List reg) (valu1 : valuation) (ge : genv) (sp : val) (rs : regset)
    (m : mem) (n n' : numbering) (vl : List valnum),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu1 ge sp rs m n →
    valnum_regs n rl = (n', vl) →
    ∃ valu2,
      numbering_holds
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) valu2 ge sp rs m n' ∧
      List.map (fun r => Regmap.get r rs) rl = List.map valu2 vl ∧
      valu_agree valu1 valu2 n.num_next ∧
      (∀ v, v ∈ vl → Plt v n'.num_next) ∧
      Ple n.num_next n'.num_next

def valnum_builtin_arg_holdsStatement : Prop :=
  ∀ (ge : genv) (sp : val) (rs : regset) (m : mem)
    (a : builtin_arg reg) (v : val),
    eval_builtin_arg (Genv.to_senv ge) (fun r => Regmap.get r rs) sp m a v →
    ∀ (valu1 : valuation) (n n' : numbering) (a' : builtin_arg valnum),
      numbering_holds
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) valu1 ge sp rs m n →
      valnum_builtin_arg n a = (n', a') →
      ∃ valu2,
        numbering_holds
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) valu2 ge sp rs m n' ∧
        eval_builtin_arg (Genv.to_senv ge) valu2 sp m a' v ∧
        valu_agree valu1 valu2 n.num_next ∧
        (∀ vn, vn ∈ params_of_builtin_arg a' → Plt vn n'.num_next) ∧
        Ple n.num_next n'.num_next

def valnum_builtin_args_holdsStatement : Prop :=
  ∀ (ge : genv) (sp : val) (rs : regset) (m : mem)
    (al : List (builtin_arg reg)) (vl : List val),
    eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs) sp m al vl →
    ∀ (valu1 : valuation) (n n' : numbering) (al' : List (builtin_arg valnum)),
      numbering_holds
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) valu1 ge sp rs m n →
      valnum_builtin_args n al = (n', al') →
      ∃ valu2,
        numbering_holds
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) valu2 ge sp rs m n' ∧
        eval_builtin_args (Genv.to_senv ge) valu2 sp m al' vl ∧
        valu_agree valu1 valu2 n.num_next ∧
        (∀ vn, vn ∈ params_of_builtin_args al' → Plt vn n'.num_next) ∧
        Ple n.num_next n'.num_next

def eval_builtin_args_trivialStatement : Prop :=
  ∀ (ge : genv) (sp : val) (rs : regset) (m : mem) (rl : List reg),
    eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs) sp m
      (rl.map (fun r => BA r)) (rl.map (fun r => Regmap.get r rs))

def find_valnum_rhs_charactStatement : Prop :=
  ∀ (rh : rhs) (v : valnum) (eqs : List equation),
    find_valnum_rhs rh eqs = some v →
    ∃ rh', Eq v true rh' ∈ eqs ∧ rhs_compat rh rh'

def find_valnum_rhs'_charactStatement : Prop :=
  ∀ (rh : rhs) (v : valnum) (eqs : List equation),
    find_valnum_rhs' rh eqs = some v →
    ∃ strict rh', Eq v strict rh' ∈ eqs ∧ rhs_compat rh rh'

def find_valnum_num_charactStatement : Prop :=
  ∀ (v : valnum) (r : rhs) (eqs : List equation),
    find_valnum_num v eqs = some r → Eq v true r ∈ eqs

def reg_valnum_soundStatement : Prop :=
  ∀ (n : numbering) (v : valnum) (r : reg) (valu : valuation) (ge : genv)
    (sp : val) (rs : regset) (m : mem),
    reg_valnum n v = some r →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    Regmap.get r rs = valu v

def regs_valnums_soundStatement : Prop :=
  ∀ (n : numbering) (valu : valuation) (ge : genv) (sp : val) (rs : regset)
    (m : mem) (vl : List valnum) (rl : List reg),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    regs_valnums n vl = some rl →
    List.map (fun r => Regmap.get r rs) rl = List.map valu vl

def find_rhs_soundStatement : Prop :=
  ∀ (n : numbering) (rh : rhs) (r : reg) (valu : valuation) (ge : genv)
    (sp : val) (rs : regset) (m : mem),
    find_rhs n rh = some r →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    ∃ v, rhs_eval_to
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp m rh v ∧
      Val.lessdef v (Regmap.get r rs)

def forget_reg_charactStatement : Prop :=
  ∀ (n : numbering) (rd r : reg) (v : valnum),
    wf_numbering n →
    r ∈ PMap.get v (forget_reg n rd) →
    r ≠ rd ∧ r ∈ PMap.get v n.num_val

def update_reg_charactStatement : Prop :=
  ∀ (n : numbering) (rd : reg) (vd : valnum) (r : reg) (v : valnum),
    wf_numbering n →
    r ∈ PMap.get v (update_reg n rd vd) →
    PTree.get r (PTree.set rd vd n.num_reg) = some v

def rhs_eval_to_injStatement : Prop :=
  ∀ (valu : valuation) (ge : genv) (sp : val) (m : mem) (rh : rhs)
    (v1 v2 : val),
    rhs_eval_to
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp m rh v1 →
    rhs_eval_to
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp m rh v2 →
    v1 = v2

def add_rhs_holdsStatement : Prop :=
  ∀ (valu1 : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering) (rd : reg) (rh : rhs) (rs' : regset),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu1 ge sp rs m n →
    rhs_valid valu1 ge sp rh →
    rhs_eval_to
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu1 ge sp m rh (Regmap.get rd rs') →
    wf_rhs n.num_next rh →
    (∀ r, r ≠ rd → Regmap.get r rs' = Regmap.get r rs) →
    ∃ valu2, numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu2 ge sp rs' m (add_rhs n rd rh)

def add_op_holdsStatement : Prop :=
  ∀ (valu1 : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering) (op : operation) (args : List reg) (v : val) (dst : reg),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu1 ge sp rs m n →
    eval_operation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge sp op (args.map (fun r => Regmap.get r rs)) m = some v →
    ∃ valu2,
      numbering_holds
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu2 ge sp (Regmap.set dst v rs) m
        (add_op n dst op args)

def add_load_holdsStatement : Prop :=
  ∀ (valu1 : valuation) (ge : genv) (sp : block) (rs : regset) (m : mem)
    (n : numbering) (addr : addressing) (args : List reg) (ap : aptr)
    (b : block) (ofs : ptrofs) (chunk : memory_chunk) (v : val) (dst : reg)
    (bc : block_classification),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu1 ge (Vptr sp Ptrofs.zero) rs m n →
    eval_addressing ge (Vptr sp Ptrofs.zero) addr
      (args.map (fun r => Regmap.get r rs)) = some (Vptr b ofs) →
    Mem.loadv chunk m (Vptr b ofs) = some v →
    pmatch bc b ofs ap → genv_match bc ge → bc sp = BCstack →
    ∃ valu2,
      numbering_holds
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu2 ge (Vptr sp Ptrofs.zero) (Regmap.set dst v rs) m
        (add_load n dst chunk addr args ap)

def add_builtin_holdsStatement : Prop :=
  ∀ (valu1 : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering) (bf : builtin_function) (args : List (builtin_arg reg))
    (res : builtin_res reg) (vargs : List val) (vres : val),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu1 ge sp rs m n →
    eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs) sp m args vargs →
    builtin_function_sem
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) bf vargs = some vres →
    ∃ valu2,
      numbering_holds
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu2 ge sp (regmap_setres res vres rs) m
        (add_builtin n res bf args)

def set_unknown_holdsStatement : Prop :=
  ∀ (valu : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering) (r : reg) (v : val),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge sp (Regmap.set r v rs) m (set_unknown n r)

def set_res_unknown_holdsStatement : Prop :=
  ∀ (valu : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering) (r : builtin_res reg) (v : val),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge sp (regmap_setres r v rs) m (set_res_unknown n r)

def kill_eqs_charactStatement : Prop :=
  ∀ (pred : rhs → Bool) (l : valnum) (strict : Bool) (r : rhs)
    (eqs : List equation),
    Eq l strict r ∈ kill_eqs pred eqs →
    pred r = false ∧ Eq l strict r ∈ eqs

def kill_equations_holdStatement : Prop :=
  ∀ (valu : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering) (pred : rhs → Bool) (m' : mem),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    (∀ r v, pred r = false → rhs_valid valu ge sp r →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) valu ge sp m r v →
      rhs_eval_to
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) valu ge sp m' r v) →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge sp rs m' (kill_equations pred n)

def kill_all_loads_holdStatement : Prop :=
  ∀ (valu : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering) (m' : mem),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge sp rs m' (kill_all_loads n)

def kill_loads_after_store_holdsStatement : Prop :=
  ∀ (valu : valuation) (ge : genv) (sp : block) (rs : regset) (m : mem)
    (n : numbering) (addr : addressing) (args : List reg) (a : val)
    (chunk : memory_chunk) (v : val) (m' : mem) (bc : block_classification)
    (approx : VA.t) (ae : aenv) (am : amem),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge (Vptr sp Ptrofs.zero) rs m n →
    eval_addressing ge (Vptr sp Ptrofs.zero) addr
      (args.map (fun r => Regmap.get r rs)) = some a →
    Mem.storev chunk m a v = some m' →
    genv_match bc ge → bc sp = BCstack → ematch bc rs ae →
    approx = VA.State ae am →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge (Vptr sp Ptrofs.zero) rs m'
      (kill_loads_after_store cfg approx n chunk addr args)

def kill_cheap_computations_holdStatement : Prop :=
  ∀ (valu : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge sp rs m (kill_cheap_computations n)

def store_normalized_range_soundStatement : Prop :=
  ∀ (bc : block_classification) (chunk : memory_chunk) (v : val),
    vmatch bc v (store_normalized_range chunk) →
    Val.lessdef (Val.load_result chunk v) v

def add_store_result_holdStatement : Prop :=
  ∀ (valu1 : valuation) (ge : genv) (sp : block) (rs : regset) (m' : mem)
    (n : numbering) (addr : addressing) (args : List reg) (a : val)
    (chunk : memory_chunk) (m : mem) (src : reg) (bc : block_classification)
    (ae : aenv) (approx : VA.t) (am : amem),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu1 ge (Vptr sp Ptrofs.zero) rs m' n →
    eval_addressing ge (Vptr sp Ptrofs.zero) addr
      (args.map (fun r => Regmap.get r rs)) = some a →
    Mem.storev chunk m a (Regmap.get src rs) = some m' →
    genv_match bc ge → bc sp = BCstack → ematch bc rs ae →
    approx = VA.State ae am →
    ∃ valu2,
      numbering_holds
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu2 ge (Vptr sp Ptrofs.zero) rs m'
        (add_store_result cfg approx n chunk addr args src)

def kill_loads_after_storebytes_holdsStatement : Prop :=
  ∀ (valu : valuation) (ge : genv) (sp : block) (rs : regset) (m : mem)
    (n : numbering) (dst : aptr) (b : block) (ofs : ptrofs)
    (bytes : List memval) (m' : mem) (bc : block_classification) (sz : Z),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge (Vptr sp Ptrofs.zero) rs m n →
    pmatch bc b ofs dst →
    Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = some m' →
    genv_match bc ge → bc sp = BCstack →
    bytes.length = zToNat sz → zLe z0 sz →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge (Vptr sp Ptrofs.zero) rs m'
      (kill_loads_after_storebytes n dst sz)

def load_memcpyStatement : Prop :=
  ∀ (m : mem) (b1 : block) (ofs1 sz : Z) (bytes : List memval)
    (b2 : block) (ofs2 : Z) (m' : mem) (chunk : memory_chunk) (i : Z) (v : val),
    Mem.loadbytes m b1 ofs1 sz = some bytes →
    Mem.storebytes m b2 ofs2 bytes = some m' →
    Mem.load chunk m b1 i = some v →
    zLe ofs1 i → zLe (zAdd i (size_chunk chunk)) (zAdd ofs1 sz) →
    zDivide (align_chunk chunk) (zSub ofs2 ofs1) →
    Mem.load chunk m' b2 (zAdd i (zSub ofs2 ofs1)) = some v

def shift_memcpy_eq_wfStatement : Prop :=
  ∀ (src sz delta : Z) (e e' : equation) (next : valnum),
    shift_memcpy_eq src sz delta e = some e' →
    wf_equation next e → wf_equation next e'

def shift_memcpy_eq_holdsStatement : Prop :=
  ∀ (src dst sz : Z) (e e' : equation) (m : mem) (sp : block)
    (bytes : List memval) (m' : mem) (valu : valuation) (ge : genv),
    shift_memcpy_eq src sz (zSub dst src) e = some e' →
    Mem.loadbytes m sp src sz = some bytes →
    Mem.storebytes m sp dst bytes = some m' →
    equation_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge (Vptr sp Ptrofs.zero) m e →
    equation_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge (Vptr sp Ptrofs.zero) m' e'

def add_memcpy_eqs_charactStatement : Prop :=
  ∀ (e' : equation) (src sz delta : Z) (eqs2 eqs1 : List equation),
    e' ∈ add_memcpy_eqs src sz delta eqs1 eqs2 →
    e' ∈ eqs2 ∨ ∃ e, e ∈ eqs1 ∧ shift_memcpy_eq src sz delta e = some e'

def add_memcpy_holdsStatement : Prop :=
  ∀ (m : mem) (bsrc : block) (osrc : ptrofs) (sz : Z) (bytes : List memval)
    (bdst : block) (odst : ptrofs) (m' : mem) (valu : valuation) (ge : genv)
    (sp : block) (rs : regset) (n1 n2 : numbering) (bc : block_classification)
    (asrc adst : aptr),
    Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz = some bytes →
    Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = some m' →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge (Vptr sp Ptrofs.zero) rs m n1 →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge (Vptr sp Ptrofs.zero) rs m' n2 →
    pmatch bc bsrc osrc asrc → pmatch bc bdst odst adst → bc sp = BCstack →
    Ple n1.num_next n2.num_next →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge (Vptr sp Ptrofs.zero) rs m'
      (add_memcpy n1 n2 asrc adst sz)

def transfer_builtin_holdsStatement : Prop :=
  ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls) (ge : genv)
    (f : function) (pc : node) (ef : external_function)
    (args : List (builtin_arg reg)) (res : builtin_res reg) (pc' : node)
    (rs : regset) (sp : block) (m : mem) (vargs : List val) (t : trace)
    (vres : val) (m' : mem) (valu : valuation) (n : numbering) (dm : defmap)
    (vapprox : PMap.t VA.t) (ae : aenv) (am : amem)
    (bc : block_classification) (rm : romem),
    PTree.get pc f.fn_code = some (Ibuiltin ef args res pc') →
    eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs)
      (Vptr sp Ptrofs.zero) m args vargs →
    external_call
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ef (Genv.to_senv ge) vargs m t vres m' →
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge (Vptr sp Ptrofs.zero) rs m n →
    PMap.get pc vapprox = VA.State ae am →
    ematch bc rs ae → romatch bc m rm → mmatch bc m am →
    genv_match bc ge → bc sp = BCstack →
    ∃ valu',
      numbering_holds
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu' ge (Vptr sp Ptrofs.zero)
        (regmap_setres res vres rs) m'
        (transfer cfg f dm vapprox pc n)

def reduce_rec_soundStatement : Prop :=
  ∀ (A : Type)
    (f : (valnum → Option rhs) → A → List valnum → Option (A × List valnum))
    (V : Type) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (sem : A → List val → Option V)
    (f_sound : ∀ eqs valu op args op' args',
      (∀ v rhs, eqs v = some rhs →
        rhs_eval_to
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          valu ge sp m rhs (valu v)) →
      f eqs op args = some (op', args') →
      sem op' (List.map valu args') = sem op (List.map valu args))
    (n : numbering) (valu : valuation),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    ∀ (niter : Nat) (op : A) (args : List valnum) (op' : A)
      (rl' : List reg) (res : V),
      reduce_rec f n niter op args = some (op', rl') →
      sem op (List.map valu args) = some res →
      sem op' (List.map (fun r => Regmap.get r rs) rl') = some res

def reduce_soundStatement : Prop :=
  ∀ (A : Type)
    (f : (valnum → Option rhs) → A → List valnum → Option (A × List valnum))
    (V : Type) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (sem : A → List val → Option V)
    (f_sound : ∀ eqs valu op args op' args',
      (∀ v rhs, eqs v = some rhs →
        rhs_eval_to
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          valu ge sp m rhs (valu v)) →
      f eqs op args = some (op', args') →
      sem op' (List.map valu args') = sem op (List.map valu args))
    (n : numbering) (valu : valuation),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    ∀ (op : A) (rl : List reg) (vl : List valnum) (op' : A) (rl' : List reg)
      (res : V),
      reduce f n op rl vl = (op', rl') →
      List.map valu vl = List.map (fun r => Regmap.get r rs) rl →
      sem op (List.map (fun r => Regmap.get r rs) rl) = some res →
      sem op' (List.map (fun r => Regmap.get r rs) rl') = some res

def reduce_rec_lessdef_soundStatement : Prop :=
  ∀ (A : Type)
    (f : (valnum → Option rhs) → A → List valnum → Option (A × List valnum))
    (ge : genv) (sp : val) (rs : regset) (m : mem)
    (sem : A → List val → Option val)
    (f_sound : ∀ eqs valu op args op' args' r,
      (∀ v rhs, eqs v = some rhs →
        rhs_eval_to
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          valu ge sp m rhs (valu v)) →
      f eqs op args = some (op', args') →
      sem op (List.map valu args) = some r →
      ∃ r', sem op' (List.map valu args') = some r' ∧ Val.lessdef r r')
    (n : numbering) (valu : valuation),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    ∀ (niter : Nat) (op : A) (args : List valnum) (op' : A)
      (rl' : List reg) (r : val),
      reduce_rec f n niter op args = some (op', rl') →
      sem op (List.map valu args) = some r →
      ∃ r',
        sem op' (List.map (fun r => Regmap.get r rs) rl') = some r' ∧
          Val.lessdef r r'

def reduce_lessdef_soundStatement : Prop :=
  ∀ (A : Type)
    (f : (valnum → Option rhs) → A → List valnum → Option (A × List valnum))
    (ge : genv) (sp : val) (rs : regset) (m : mem)
    (sem : A → List val → Option val)
    (f_sound : ∀ eqs valu op args op' args' r,
      (∀ v rhs, eqs v = some rhs →
        rhs_eval_to
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          valu ge sp m rhs (valu v)) →
      f eqs op args = some (op', args') →
      sem op (List.map valu args) = some r →
      ∃ r', sem op' (List.map valu args') = some r' ∧ Val.lessdef r r')
    (n : numbering) (valu : valuation),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m n →
    ∀ (op : A) (rl : List reg) (vl : List valnum) (op' : A)
      (rl' : List reg) (r : val),
      reduce f n op rl vl = (op', rl') →
      List.map valu vl = List.map (fun r => Regmap.get r rs) rl →
      sem op (List.map (fun r => Regmap.get r rs) rl) = some r →
      ∃ r',
        sem op' (List.map (fun r => Regmap.get r rs) rl') = some r' ∧
          Val.lessdef r r'

def analysis_correct_1Statement : Prop :=
  ∀ (ge : genv) (sp : val) (rs : regset) (m : mem) (f : function)
    (dm : defmap) (vapprox : PMap.t VA.t) (approx : PMap.t numbering)
    (pc pc' : node) (i : instruction),
    CSE.analyze
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg f dm vapprox = some approx →
    PTree.get pc f.fn_code = some i →
    pc' ∈ successors_instr i →
    (∃ valu, numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m
      (transfer cfg f dm vapprox pc (PMap.get pc approx))) →
    ∃ valu, numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu ge sp rs m (PMap.get pc' approx)

def analysis_correct_entryStatement : Prop :=
  ∀ (ge : genv) (sp : val) (rs : regset) (m : mem) (f : function)
    (dm : defmap) (vapprox : PMap.t VA.t) (approx : PMap.t numbering),
    CSE.analyze
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg f dm vapprox = some approx →
    ∃ valu, numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) valu ge sp rs m
      (PMap.get f.fn_entrypoint approx)

def symbols_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ id : ident,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id

def senv_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    Senv.equiv (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def functions_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ (v : val) (f : fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      ∃ cu tf,
        Genv.find_funct (Genv.globalenv tprog) v = some tf ∧
        CSE.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (prog_defmap cu) (romem_for cfg cu) f = OK tf ∧
        linkorder cu prog

def funct_ptr_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ (b : block) (f : fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      ∃ cu tf,
        Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
        CSE.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (prog_defmap cu) (romem_for cfg cu) f = OK tf ∧
        linkorder cu prog

def sig_preservedStatement : Prop :=
  ∀ (dm : defmap) (rm : romem) (f tf : fundef),
    CSE.transf_fundef
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg dm rm f = OK tf →
    funsig tf = funsig f

def regs_lessdef_regsStatement : Prop :=
  ∀ (rs1 rs2 : regset), regs_lessdef rs1 rs2 →
    ∀ (rl : List reg),
      Val.lessdef_list
        (List.map (fun r => Regmap.get r rs1) rl)
        (List.map (fun r => Regmap.get r rs2) rl)

def set_reg_lessdefStatement : Prop :=
  ∀ (r : reg) (v1 v2 : val) (rs1 rs2 : regset),
    Val.lessdef v1 v2 → regs_lessdef rs1 rs2 →
    regs_lessdef (Regmap.set r v1 rs1) (Regmap.set r v2 rs2)

def init_regs_lessdefStatement : Prop :=
  ∀ (rl : List reg) (vl1 vl2 : List val),
    Val.lessdef_list vl1 vl2 →
    regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl)

def find_function_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ (ros : Sum reg ident) (rs : regset) (fd : fundef) (rs' : regset),
      find_function (Genv.globalenv prog) ros rs = some fd →
      regs_lessdef rs rs' →
      ∃ cu tfd,
        find_function (Genv.globalenv tprog) ros rs' = some tfd ∧
        CSE.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (prog_defmap cu) (romem_for cfg cu) fd = OK tfd ∧
        linkorder cu prog

def transf_step_correctStatement : Prop :=
  ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog tprog : program), match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ (s1 : state) (t : trace) (s2 : state),
      RTL.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) s1 t s2 →
      ∀ s1', match_states
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg prog s1 s1' →
        sound_state
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg prog s1 →
        (∃ s2',
          RTL.step
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            xi (Genv.globalenv tprog) s1' t s2' ∧
          match_states
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) cfg prog s2 s2') ∨
        (∃ s2' n,
          plus (RTL.step
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi)
            (Genv.globalenv tprog) s1' t s2' ∧
          eventually
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            prog xi n s2 (fun s3 => match_states
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) cfg prog s3 s2'))

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program), match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ st1, RTL.initial_state prog st1 →
      ∃ st2, RTL.initial_state tprog st2 ∧ match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (prog : program) (st1 st2 : state) (r : int),
    match_states
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog st1 st2 →
    RTL.final_state st1 r → RTL.final_state st2 r

def transf_program_correctStatement : Prop :=
  ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog tprog : program), match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    forward_simulation
      (RTL.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog)
      (RTL.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tprog)

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSE
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Coqlib

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem transf_program_match : ∀ cfg, transf_program_matchStatement cfg := by
  intro cfg p tp h
  letI : Linker RTL.program := by
    change Linker (CompCert4Lean.Common.AST.program
      (CompCert4Lean.Common.AST.fundef RTL.function) Unit)
    exact @Linker_prog (CompCert4Lean.Common.AST.fundef RTL.function) Unit
      (Linker_fundef RTL.function) Linker_unit
  unfold CompCert4Lean.Backend.CSE.transf_program
    CompCert4Lean.Common.AST.transform_partial_program
    CompCert4Lean.Common.AST.transform_partial_program2 at h
  have hlist :
      ∀ (xs : List (ident × globdef RTL.fundef Unit))
        (ys : List (ident × globdef RTL.fundef Unit)),
        transf_globdefs (fun _ f => CSE.transf_fundef cfg (prog_defmap p)
          (romem_for cfg p) f)
            (fun _ v => .OK v) xs = .OK ys →
          list_forall2
            (match_ident_globdef
              (fun q f tf => CSE.transf_fundef cfg (prog_defmap q)
                (romem_for cfg q) f = .OK tf)
              (fun x y : Unit => x = y) p) xs ys := by
    intro xs
    induction xs with
    | nil =>
        intro ys hys
        cases hys
        exact list_forall2.nil _
    | cons hd tl ih =>
        intro ys hys
        cases hd with
        | mk id gd =>
            cases gd with
            | Gfun f =>
                cases hf : CSE.transf_fundef cfg (prog_defmap p) (romem_for cfg p) f with
                | Error msg => simp [transf_globdefs, hf] at hys
                | OK tf =>
                    cases ht : transf_globdefs (fun _ f => CSE.transf_fundef cfg (prog_defmap p)
                      (romem_for cfg p) f) (fun _ v => .OK v) tl with
                    | Error msg => simp [transf_globdefs, hf, ht] at hys
                    | OK ysTail =>
                        simp only [transf_globdefs, hf, ht] at hys
                        cases hys
                        apply list_forall2.cons
                        · constructor
                          · rfl
                          · apply match_globdef.match_globdef_fun (ctx' := p)
                            · exact linkorder_refl _
                            · exact hf
                        · exact ih ysTail ht
            | Gvar v =>
                cases ht : transf_globdefs (fun _ f => CSE.transf_fundef cfg (prog_defmap p)
                  (romem_for cfg p) f) (fun _ v => .OK v) tl with
                | Error msg => simp [transf_globdefs, transf_globvar, ht] at hys
                | OK ysTail =>
                    simp only [transf_globdefs, transf_globvar, ht] at hys
                    cases hys
                    apply list_forall2.cons
                    · constructor
                      · rfl
                      · apply match_globdef.match_globdef_var
                        exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                    · exact ih ysTail ht
  cases hdefs : transf_globdefs (fun _ f => CSE.transf_fundef cfg (prog_defmap p)
      (romem_for cfg p) f) (fun _ v => .OK v) p.prog_defs with
  | Error msg => simp [hdefs] at h
  | OK defs =>
      simp only [hdefs] at h
      cases h
      unfold match_prog match_program match_program_gen
      exact ⟨hlist p.prog_defs defs hdefs, rfl, rfl⟩

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Lib.Coqlib

theorem valu_agree_refl : valu_agree_reflStatement := by
  intro valu upto v h
  rfl

theorem valnums_val_exten : valnums_val_extenStatement := by
  intro valu1 upto valu2 hagree vl hlt
  induction vl with
  | nil => rfl
  | cons v vl ih =>
      change valu2 v :: List.map valu2 vl = valu1 v :: List.map valu1 vl
      rw [hagree v (hlt v (by exact List.Mem.head _))]
      exact congrArg (fun xs => valu1 v :: xs)
        (ih (fun w hw => hlt w (List.Mem.tail _ hw)))

theorem wf_equation_incr : wf_equation_incrStatement := by
  intro next1 next2 e h ple
  cases e with
  | Eq l strict r =>
      change (Plt l next1 ∧ wf_rhs next1 r) at h
      change (Plt l next2 ∧ wf_rhs next2 r)
      constructor
      · exact Nat.lt_of_lt_of_le h.1 ple
      · intro v hv
        exact Nat.lt_of_lt_of_le (h.2 v hv) ple

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Lib.Coqlib

theorem builtin_arg_val_exten : builtin_arg_val_extenStatement := by
  intro valu1 upto valu2 hagree ge sp m a v harg hlt
  induction harg with
  | eval_BA x =>
      rw [← hagree x (hlt x (by simp [params_of_builtin_arg]))]
      exact eval_BA x
  | eval_BA_int n => exact eval_BA_int n
  | eval_BA_long n => exact eval_BA_long n
  | eval_BA_float n => exact eval_BA_float n
  | eval_BA_single n => exact eval_BA_single n
  | eval_BA_loadstack chunk ofs v hload => exact eval_BA_loadstack chunk ofs v hload
  | eval_BA_addrstack ofs => exact eval_BA_addrstack ofs
  | eval_BA_loadglobal chunk id ofs v hload => exact eval_BA_loadglobal chunk id ofs v hload
  | eval_BA_addrglobal id ofs => exact eval_BA_addrglobal id ofs
  | eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      apply eval_BA_splitlong hi lo vhi vlo
      · apply ihhi
        intro vn hvn
        apply hlt vn
        simp [params_of_builtin_arg, hvn]
      · apply ihlo
        intro vn hvn
        apply hlt vn
        simp [params_of_builtin_arg, hvn]
  | eval_BA_addptr a1 a2 v1 v2 h1 h2 ih1 ih2 =>
      apply eval_BA_addptr a1 a2 v1 v2
      · apply ih1
        intro vn hvn
        apply hlt vn
        simp [params_of_builtin_arg, hvn]
      · apply ih2
        intro vn hvn
        apply hlt vn
        simp [params_of_builtin_arg, hvn]

theorem builtin_args_val_exten : builtin_args_val_extenStatement := by
  intro valu1 upto valu2 hagree ge sp m al vl hargs hlt
  unfold eval_builtin_args at hargs ⊢
  induction hargs with
  | nil => exact list_forall2.nil _
  | cons =>
      rename_i a1 al1 b1 bl1 ha hal ih
      apply list_forall2.cons
      · apply builtin_arg_val_exten valu1 upto valu2 hagree ge sp m a1 b1 ha
        intro vn hvn
        apply hlt vn
        change vn ∈ params_of_builtin_arg a1 ++ params_of_builtin_args al1
        exact List.mem_append.mpr (Or.inl hvn)
      · apply ih
        intro vn hvn
        apply hlt vn
        change vn ∈ params_of_builtin_arg a1 ++ params_of_builtin_args al1
        exact List.mem_append.mpr (Or.inr hvn)

theorem rhs_eval_to_exten
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    rhs_eval_to_extenStatement := by
  intro valu1 upto valu2 hagree ge sp m r v hev hlt
  induction hev with
  | op_eval_to op vl v hop =>
      apply op_eval_to
      rw [valnums_val_exten valu1 upto valu2 hagree vl hlt]
      exact hop
  | load_eval_to chunk addr vl a v p ha hl =>
      apply load_eval_to
      · rw [valnums_val_exten valu1 upto valu2 hagree vl hlt]
        exact ha
      · exact hl
  | builtin_eval_to bf args vargs v hargs hsem =>
      apply builtin_eval_to
      · apply builtin_args_val_exten valu1 upto valu2 hagree ge sp m args vargs hargs
        exact hlt
      · exact hsem

theorem rhs_valid_exten : rhs_valid_extenStatement := by
  intro valu1 upto valu2 hagree ge sp r hvalid hlt
  induction hvalid with
  | op_valid sp op vl => exact op_valid sp op vl
  | load_valid sp chunk addr vl p b ofs bc ha hpmatch hgenv hstack =>
      apply load_valid sp chunk addr vl p b ofs bc
      · rw [valnums_val_exten valu1 upto valu2 hagree vl hlt]
        exact ha
      · exact hpmatch
      · exact hgenv
      · exact hstack
  | builtin_valid sp bf args => exact builtin_valid sp bf args

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain

theorem equation_holds_exten
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    equation_holds_extenStatement := by
  intro valu1 upto valu2 hagree ge sp m e heq hwf
  cases e with
  | Eq l strict r =>
      cases hwf with
      | intro hl hr =>
          cases heq with
          | eq_holds_strict _ _ hev hvalid =>
              apply eq_holds_strict
              · rw [hagree l hl]
                apply rhs_eval_to_exten valu1 upto valu2 hagree ge sp m r (valu1 l)
                  hev hr
              · apply rhs_valid_exten valu1 upto valu2 hagree ge sp r hvalid
                exact hr
          | eq_holds_lessdef _ _ v hev hle hvalid =>
              apply eq_holds_lessdef l r v
              · apply rhs_eval_to_exten valu1 upto valu2 hagree ge sp m r v hev
                exact hr
              · rw [hagree l hl]
                exact hle
              · apply rhs_valid_exten valu1 upto valu2 hagree ge sp r hvalid
                exact hr

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Lib.Coqlib

theorem valnum_reg_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    valnum_reg_holdsStatement := by
  intro valu1 ge sp rs m n r n' v hnum hval
  unfold CompCert4Lean.Backend.CSEdomain.valnum at *
  change positive at r
  change Regmap.t CompCert4Lean.Common.Values.val at rs
  unfold CSE.valnum_reg at hval
  cases hget : PTree.get r n.num_reg with
  | some v' =>
      simp [hget] at hval
      cases hval
      letI : DecidableEq positive := fun a b =>
        match peq a b with
        | .left h => isTrue h
        | .right h => isFalse h
      refine ⟨valu1, hnum, ?_, ?_, ?_, ?_⟩
      · exact hnum.num_holds_reg r _ hget
      · exact valu_agree_refl valu1 n.num_next
      · exact hnum.num_holds_wf.wf_num_reg r _ hget
      · exact Ple_refl _
  | none =>
      simp [hget] at hval
      cases hval
      let valu2 : valuation := fun vn =>
        match peq vn n.num_next with
        | .left _ => PMap.get r rs
        | .right _ => valu1 vn
      have hagree : valu_agree valu1 valu2 n.num_next := by
        intro vn hvn
        simp only [valu2]
        cases hpeq : peq vn n.num_next with
        | left heq => exact False.elim ((Plt_ne _ _ hvn) heq)
        | right _ => rfl
      have hpleSucc : Ple n.num_next (PArith.BinPos.Pos.succ n.num_next) := by
        exact Nat.le_of_lt (Plt_succ _)
      have hreg_same : PTree.get r (PTree.set r n.num_next n.num_reg) = some n.num_next := by
        have h := @PTree.gsspec_proof CompCert4Lean.Backend.CSEdomain.valnum
          r r n.num_next n.num_reg
        cases hpeq : peq r r with
        | left _ => simpa [hpeq] using h
        | right hne => exact False.elim (hne rfl)
      have hreg_other : ∀ r0 : positive, r0 ≠ r →
          PTree.get r0 (PTree.set r n.num_next n.num_reg) = PTree.get r0 n.num_reg := by
        intro r0 hne
        have h := @PTree.gsspec_proof CompCert4Lean.Backend.CSEdomain.valnum
          r0 r n.num_next n.num_reg
        cases hpeq : peq r0 r with
        | left heq => exact False.elim (hne heq)
        | right _ => simpa [hpeq, PTree.t] using h
      have hval_same : PTree.get n.num_next
          (PTree.set n.num_next [r] n.num_val.2) = some [r] := by
        have h := PTree.gsspec_proof n.num_next n.num_next [r] n.num_val.2
        cases hpeq : peq n.num_next n.num_next with
        | left _ => simpa [hpeq] using h
        | right hne => exact False.elim (hne rfl)
      have hval_other : ∀ v0 : positive, v0 ≠ n.num_next →
          PTree.get v0 (PTree.set n.num_next [r] n.num_val.2) =
            PTree.get v0 n.num_val.2 := by
        intro v0 hne
        change PTree.get v0 (PTree.set n.num_next [r]
          (show PTree.t (List positive) from n.num_val.2)) =
          PTree.get v0 (show PTree.t (List positive) from n.num_val.2)
        have h := PTree.gsspec_proof v0 n.num_next [r] n.num_val.2
        cases hpeq : peq v0 n.num_next with
        | left heq => exact False.elim (hne heq)
        | right _ => simpa [hpeq, PTree.t] using h
      refine ⟨valu2, ?_, ?_, hagree, ?_, ?_⟩
      · constructor
        · constructor
          · intro e he
            exact wf_equation_incr n.num_next (PArith.BinPos.Pos.succ n.num_next) e
              (hnum.num_holds_wf.wf_num_eqs e he) hpleSucc
          · intro r0 v0 hget0
            change positive at v0
            cases hreg : peq r0 r with
            | left heq =>
              subst r0
              rw [hreg_same] at hget0
              cases hget0
              exact Plt_succ (show positive from n.num_next)
            | right hne =>
              rw [hreg_other r0 hne] at hget0
              exact Plt_trans_succ _ _
                (hnum.num_holds_wf.wf_num_reg r0 v0 (by simpa using hget0))
          · intro r0 v0 hr0
            change positive at r0
            change r0 ∈ PMap.get v0 (PMap.set n.num_next [r] n.num_val) at hr0
            change PTree.get r0 (PTree.set r n.num_next n.num_reg) = some v0
            unfold PMap.get PMap.set at hr0
            cases hv : peq v0 n.num_next with
            | left hev =>
                subst v0
                rw [hval_same] at hr0
                change r0 ∈ [r] at hr0
                simp at hr0
                cases hreg : peq r0 r with
                | left heq => subst r0; exact hreg_same
                | right hne => exact False.elim (hne (by simpa using hr0))
            | right hne =>
                rw [hval_other v0 hne] at hr0
                simp [hv] at hr0
                cases hreg : peq r0 r with
                | left heq =>
                    subst r0
                    have hold := hnum.num_holds_wf.wf_num_val r v0 (by
                      change r ∈ PMap.get v0 n.num_val
                      exact hr0)
                    rw [hget] at hold
                    cases hold
                | right hneReg =>
                    rw [hreg_other r0 hneReg]
                    exact hnum.num_holds_wf.wf_num_val r0 v0 hr0
        · intro e he
          exact equation_holds_exten valu1 n.num_next valu2 hagree ge sp m e
            (hnum.num_holds_eq e he)
            (hnum.num_holds_wf.wf_num_eqs e he)
        · intro r0 v0 hget0
          change PMap.get r0 rs = valu2 v0
          change positive at r0
          unfold valu2
          cases hreg : peq r0 r with
          | left heq =>
            subst r0
            rw [hreg_same] at hget0
            cases hget0
            cases hv : peq n.num_next n.num_next with
            | left _ => simp [valu2, hv]
            | right hne => exact False.elim (hne rfl)
          | right hne =>
            rw [hreg_other r0 hne] at hget0
            have hvneq : v0 ≠ n.num_next := by
              intro hv
              exact (Plt_ne _ _ (hnum.num_holds_wf.wf_num_reg r0 v0 hget0)) hv
            cases hv : peq v0 n.num_next with
            | left hvEq => exact False.elim (hvneq hvEq)
            | right _ =>
                simp [valu2, hv]
                exact hnum.num_holds_reg r0 v0 hget0
      · unfold valu2
        cases hpeq : peq n.num_next n.num_next with
        | left heq => simp [hpeq]
        | right hne => exact False.elim (hne rfl)
      · exact Plt_succ _
      · exact hpleSucc

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Lib.Coqlib

theorem valnum_regs_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    valnum_regs_holdsStatement := by
  intro rl valu1 ge sp rs m n n' vl hnum hval
  have pltPle : ∀ (a b c : positive), Plt a b → Ple b c → Plt a c := by
    intro a b c hab hbc
    change PArith.BinPos.Pos.to_nat a < PArith.BinPos.Pos.to_nat b at hab
    change PArith.BinPos.Pos.to_nat b ≤ PArith.BinPos.Pos.to_nat c at hbc
    change PArith.BinPos.Pos.to_nat a < PArith.BinPos.Pos.to_nat c
    exact Nat.lt_of_lt_of_le hab hbc
  induction rl generalizing valu1 n n' vl with
  | nil =>
      simp [CSE.valnum_regs] at hval
      cases hval
      subst n'
      subst vl
      refine ⟨valu1, hnum, ?_, valu_agree_refl valu1 n.num_next, ?_, ?_⟩
      · rfl
      · intro v hv
        cases hv
      · exact Ple_refl _
  | cons a rl ih =>
      cases h1 : CSE.valnum_reg n a with
      | mk n1 v1 =>
          cases h2 : CSE.valnum_regs n1 rl with
          | mk n2 vs =>
              simp [CSE.valnum_regs, h1, h2] at hval
              cases hval
              subst n'
              subst vl
              obtain ⟨valu2, hn2, heq1, hag12, hlt1, hle1⟩ :=
                valnum_reg_holds valu1 ge sp rs m n a n1 v1 hnum h1
              obtain ⟨valu3, hn3, heq2, hag23, hlt2, hle2⟩ :=
                ih (valu1 := valu2) (n := n1) (n' := n2) (vl := vs)
                  hn2 h2
              refine ⟨valu3, hn3, ?_, ?_, ?_, ?_⟩
              · simp only [List.map]
                rw [heq2, heq1, ← hag23 v1 hlt1]
              · intro v hv
                exact (hag23 v (pltPle _ _ _ hv hle1)).trans (hag12 v hv)
              · intro v hv
                simp only [List.mem_cons] at hv
                rcases hv with hv | hv
                · subst v
                  exact pltPle _ _ _ hlt1 hle2
                · exact hlt2 v hv
              · exact Ple_trans _ _ _ hle1 hle2

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events

theorem valnum_builtin_arg_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    valnum_builtin_arg_holdsStatement := by
  intro ge sp rs m a v heval valu1 n n' a' hnum hval
  have pltPle : ∀ (x y z : positive), Plt x y → Ple y z → Plt x z := by
    intro x y z hxy hyz
    change PArith.BinPos.Pos.to_nat x < PArith.BinPos.Pos.to_nat y at hxy
    change PArith.BinPos.Pos.to_nat y ≤ PArith.BinPos.Pos.to_nat z at hyz
    change PArith.BinPos.Pos.to_nat x < PArith.BinPos.Pos.to_nat z
    exact Nat.lt_of_lt_of_le hxy hyz
  induction heval generalizing valu1 n n' a' with
  | eval_BA x =>
      cases hreg : CSE.valnum_reg n x with
      | mk n1 v1 =>
        simp [CSE.valnum_builtin_arg, hreg] at hval
        cases hval
        subst n'
        subst a'
        obtain ⟨valu2, hn2, hget, hag, hlt, hle⟩ :=
          valnum_reg_holds valu1 ge sp rs m n x n1 v1 hnum hreg
        refine ⟨valu2, hn2, ?_, hag, ?_, hle⟩
        · rw [hget]
          exact eval_BA v1
        · intro vn hvn
          simp [params_of_builtin_arg] at hvn
          subst vn
          exact hlt
  | eval_BA_int n0 =>
      simp [CSE.valnum_builtin_arg] at hval
      cases hval
      subst n'
      subst a'
      refine ⟨valu1, hnum, ?_, ?_, ?_, ?_⟩
      · exact eval_BA_int n0
      · exact valu_agree_refl valu1 n.num_next
      · simp [params_of_builtin_arg]
      · exact Ple_refl _
  | eval_BA_long n0 =>
      simp [CSE.valnum_builtin_arg] at hval
      cases hval
      subst n'
      subst a'
      refine ⟨valu1, hnum, ?_, ?_, ?_, ?_⟩
      · exact eval_BA_long n0
      · exact valu_agree_refl valu1 n.num_next
      · simp [params_of_builtin_arg]
      · exact Ple_refl _
  | eval_BA_float n0 =>
      simp [CSE.valnum_builtin_arg] at hval
      cases hval
      subst n'
      subst a'
      refine ⟨valu1, hnum, ?_, ?_, ?_, ?_⟩
      · exact eval_BA_float n0
      · exact valu_agree_refl valu1 n.num_next
      · simp [params_of_builtin_arg]
      · exact Ple_refl _
  | eval_BA_single n0 =>
      simp [CSE.valnum_builtin_arg] at hval
      cases hval
      subst n'
      subst a'
      refine ⟨valu1, hnum, ?_, ?_, ?_, ?_⟩
      · exact eval_BA_single n0
      · exact valu_agree_refl valu1 n.num_next
      · simp [params_of_builtin_arg]
      · exact Ple_refl _
  | eval_BA_loadstack chunk ofs v0 hload =>
      simp [CSE.valnum_builtin_arg] at hval
      cases hval
      subst n'
      subst a'
      refine ⟨valu1, hnum, ?_, ?_, ?_, ?_⟩
      · exact eval_BA_loadstack chunk ofs v0 hload
      · exact valu_agree_refl valu1 n.num_next
      · simp [params_of_builtin_arg]
      · exact Ple_refl _
  | eval_BA_addrstack ofs =>
      simp [CSE.valnum_builtin_arg] at hval
      cases hval
      subst n'
      subst a'
      refine ⟨valu1, hnum, ?_, ?_, ?_, ?_⟩
      · exact eval_BA_addrstack ofs
      · exact valu_agree_refl valu1 n.num_next
      · simp [params_of_builtin_arg]
      · exact Ple_refl _
  | eval_BA_loadglobal chunk id ofs v0 hload =>
      simp [CSE.valnum_builtin_arg] at hval
      cases hval
      subst n'
      subst a'
      refine ⟨valu1, hnum, ?_, ?_, ?_, ?_⟩
      · exact eval_BA_loadglobal chunk id ofs v0 hload
      · exact valu_agree_refl valu1 n.num_next
      · simp [params_of_builtin_arg]
      · exact Ple_refl _
  | eval_BA_addrglobal id ofs =>
      simp [CSE.valnum_builtin_arg] at hval
      cases hval
      subst n'
      subst a'
      refine ⟨valu1, hnum, ?_, ?_, ?_, ?_⟩
      · exact eval_BA_addrglobal id ofs
      · exact valu_agree_refl valu1 n.num_next
      · simp [params_of_builtin_arg]
      · exact Ple_refl _
  | eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      cases h1 : CSE.valnum_builtin_arg n hi with
      | mk n1 hi' =>
        cases h2 : CSE.valnum_builtin_arg n1 lo with
        | mk n2 lo' =>
          simp [CSE.valnum_builtin_arg, h1, h2] at hval
          cases hval
          subst n'
          subst a'
          obtain ⟨valu2, hn2, heval_hi, hag12, hlt_hi, hle1⟩ :=
            ihhi (valu1 := valu1) (n := n) (n' := n1) (a' := hi') hnum h1
          obtain ⟨valu3, hn3, heval_lo, hag23, hlt_lo, hle2⟩ :=
            ihlo (valu1 := valu2) (n := n1) (n' := n2) (a' := lo') hn2 h2
          refine ⟨valu3, hn3, ?_, ?_, ?_, ?_⟩
          · apply eval_BA_splitlong hi' lo' vhi vlo
            · apply builtin_arg_val_exten valu2 n1.num_next valu3 hag23
                ge sp m hi' vhi heval_hi
              intro vn hvn
              exact hlt_hi vn hvn
            · exact heval_lo
          · intro vn hvn
            exact (hag23 vn (pltPle vn n.num_next n1.num_next hvn hle1)).trans
              (hag12 vn hvn)
          · intro vn hvn
            change vn ∈ params_of_builtin_arg hi' ++ params_of_builtin_arg lo' at hvn
            rcases List.mem_append.mp hvn with hleft | hright
            · exact pltPle vn n1.num_next n2.num_next (hlt_hi vn hleft) hle2
            · exact hlt_lo vn hright
          · exact Ple_trans _ _ _ hle1 hle2
  | eval_BA_addptr a1 a2 v1 v2 h1eval h2eval ih1 ih2 =>
      cases h1 : CSE.valnum_builtin_arg n a1 with
      | mk n1 a1' =>
        cases h2 : CSE.valnum_builtin_arg n1 a2 with
        | mk n2 a2' =>
          simp [CSE.valnum_builtin_arg, h1, h2] at hval
          cases hval
          subst n'
          subst a'
          obtain ⟨valu2, hn2, heval_a1, hag12, hlt_a1, hle1⟩ :=
            ih1 (valu1 := valu1) (n := n) (n' := n1) (a' := a1') hnum h1
          obtain ⟨valu3, hn3, heval_a2, hag23, hlt_a2, hle2⟩ :=
            ih2 (valu1 := valu2) (n := n1) (n' := n2) (a' := a2') hn2 h2
          refine ⟨valu3, hn3, ?_, ?_, ?_, ?_⟩
          · apply eval_BA_addptr a1' a2' v1 v2
            · apply builtin_arg_val_exten valu2 n1.num_next valu3 hag23
                ge sp m a1' v1 heval_a1
              intro vn hvn
              exact hlt_a1 vn hvn
            · exact heval_a2
          · intro vn hvn
            exact (hag23 vn (pltPle vn n.num_next n1.num_next hvn hle1)).trans
              (hag12 vn hvn)
          · intro vn hvn
            change vn ∈ params_of_builtin_arg a1' ++ params_of_builtin_arg a2' at hvn
            rcases List.mem_append.mp hvn with hleft | hright
            · exact pltPle vn n1.num_next n2.num_next (hlt_a1 vn hleft) hle2
            · exact hlt_a2 vn hright
          · exact Ple_trans _ _ _ hle1 hle2

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events

theorem valnum_builtin_args_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    valnum_builtin_args_holdsStatement := by
  intro ge sp rs m al vl hargs
  unfold eval_builtin_args at hargs ⊢
  have pltPle : ∀ (x y z : positive), Plt x y → Ple y z → Plt x z := by
    intro x y z hxy hyz
    change PArith.BinPos.Pos.to_nat x < PArith.BinPos.Pos.to_nat y at hxy
    change PArith.BinPos.Pos.to_nat y ≤ PArith.BinPos.Pos.to_nat z at hyz
    change PArith.BinPos.Pos.to_nat x < PArith.BinPos.Pos.to_nat z
    exact Nat.lt_of_lt_of_le hxy hyz
  induction hargs with
  | nil =>
      intro valu1 n n' al' hnum hval
      simp [CSE.valnum_builtin_args] at hval
      cases hval
      subst n'
      subst al'
      refine ⟨valu1, hnum, ?_, valu_agree_refl valu1 n.num_next, ?_, ?_⟩
      · exact list_forall2.nil _
      · intro v hv
        cases hv
      · exact Ple_refl _
  | cons =>
      rename_i a1 al b1 bl ha hal ih
      intro valu1 n n' al' hnum hval
      cases h1 : CSE.valnum_builtin_arg n a1 with
      | mk n1 a1' =>
          cases h2 : CSE.valnum_builtin_args n1 al with
          | mk n2 al'' =>
              simp [CSE.valnum_builtin_args, h1, h2] at hval
              cases hval
              subst n'
              subst al'
              obtain ⟨valu2, hn2, heval1, hag12, hlt1, hle1⟩ :=
                valnum_builtin_arg_holds ge sp rs m a1 b1 ha valu1 n n1 a1' hnum h1
              obtain ⟨valu3, hn3, heval2, hag23, hlt2, hle2⟩ :=
                ih valu2 n1 n2 al'' hn2 h2
              refine ⟨valu3, hn3, ?_, ?_, ?_, ?_⟩
              · apply list_forall2.cons
                · apply builtin_arg_val_exten valu2 n1.num_next valu3 hag23 ge sp m
                    a1' b1 heval1
                  intro vn hvn
                  exact hlt1 vn hvn
                · exact heval2
              · intro vn hvn
                exact (hag23 vn (pltPle _ _ _ hvn hle1)).trans (hag12 vn hvn)
              · intro vn hvn
                change vn ∈ params_of_builtin_arg a1' ++ params_of_builtin_args al'' at hvn
                rcases List.mem_append.mp hvn with hleft | hright
                · exact pltPle _ _ _ (hlt1 vn hleft) hle2
                · exact hlt2 vn hright
              · exact Ple_trans _ _ _ hle1 hle2

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Lib.Coqlib

theorem eval_builtin_args_trivial : eval_builtin_args_trivialStatement := by
  intro ge sp rs m rl
  unfold eval_builtin_args
  induction rl with
  | nil => exact list_forall2.nil _
  | cons r rl ih =>
      simp only [List.map]
      apply list_forall2.cons
      · exact eval_BA r
      · exact ih

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof
theorem find_valnum_rhs'_charact : find_valnum_rhs'_charactStatement := by
  intro rh v eqs
  induction eqs with
  | nil => simp [CSE.find_valnum_rhs']
  | cons e eqs ih =>
      cases e with
      | Eq v' strict rh' =>
          simp only [CSE.find_valnum_rhs']
          intro hv
          by_cases h : CSEdomain.compat_rhs rh rh'
          · have hv' : v' = v := by simpa [h] using hv
            cases hv'
            exact ⟨strict, rh', List.mem_cons_self, CSEdomain.compat_rhs_sound rh rh' h⟩
          · obtain ⟨s, r'', hm, hc⟩ := ih (by rw [if_neg h] at hv; exact hv)
            exact ⟨s, r'', List.mem_cons_of_mem _ hm, hc⟩
end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Lib.Coqlib

theorem find_valnum_num_charact : find_valnum_num_charactStatement := by
  intro v r eqs
  induction eqs with
  | nil =>
      simp [CSE.find_valnum_num]
  | cons e eqs ih =>
      cases e with
      | Eq v' strict r' =>
          simp only [CSE.find_valnum_num]
          intro h
          cases hs : strict with
          | false =>
              simp [hs] at h
              exact List.mem_cons_of_mem _ (ih h)
          | true =>
              cases hp : peq v v' with
              | left hv =>
                  simp [hs, hp] at h
                  cases h
                  subst v'
                  exact List.mem_cons_self
              | right hne =>
                  simp [hs, hp] at h
                  exact List.mem_cons_of_mem _ (ih h)

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Lib.Maps

theorem reg_valnum_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    reg_valnum_soundStatement := by
  intro n v r valu ge sp rs m hreg hnum
  unfold CSE.reg_valnum at hreg
  cases h : PMap.get v n.num_val with
  | nil =>
      simp [h] at hreg
  | cons r1 rl =>
      simp [h] at hreg
      cases hreg
      have hmem : r ∈ PMap.get v n.num_val := by
        rw [h]
        exact List.mem_cons_self
      have hget : PTree.get r n.num_reg = some v :=
        hnum.num_holds_wf.wf_num_val r v hmem
      exact hnum.num_holds_reg r v hget

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSE

theorem regs_valnums_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    regs_valnums_soundStatement := by
  intro n valu ge sp rs m vl
  induction vl with
  | nil =>
      intro rl hholds hregs
      simp [CSE.regs_valnums] at hregs
      cases hregs
      rfl
  | cons v vs ih =>
      intro rl hholds hregs
      simp only [CSE.regs_valnums] at hregs
      cases hrv : CSE.reg_valnum n v with
      | none =>
          simp [hrv] at hregs
      | some r1 =>
          cases hrest : CSE.regs_valnums n vs with
          | none =>
              simp [hrv, hrest] at hregs
          | some rl1 =>
              simp [hrv, hrest] at hregs
              cases hregs
              have hhead : Registers.Regmap.get r1 rs = valu v :=
                CompCert4Lean.Backend.CSEproof.reg_valnum_sound
                  n v r1 valu ge sp rs m hrv hholds
              change Registers.Regmap.get r1 rs :: List.map (fun r => Registers.Regmap.get r rs) rl1 =
                valu v :: List.map valu vs
              rw [hhead]
              exact congrArg (fun xs => valu v :: xs) (ih rl1 hholds hrest)

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values

private theorem cse_eval_builtin_arg_determ
    {A : Type} (ge : Senv.t)
    (e : A → val) (sp : val) (m : mem) {a : builtin_arg A} {v : val}
    (h : eval_builtin_arg ge e sp m a v) :
    ∀ {v' : val}, eval_builtin_arg ge e sp m a v' → v' = v := by
  induction h with
  | eval_BA x =>
      intro v' h'
      cases h'
      rfl
  | eval_BA_int n =>
      intro v' h'
      cases h'
      rfl
  | eval_BA_long n =>
      intro v' h'
      cases h'
      rfl
  | eval_BA_float n =>
      intro v' h'
      cases h'
      rfl
  | eval_BA_single n =>
      intro v' h'
      cases h'
      rfl
  | eval_BA_loadstack chunk ofs v load =>
      intro v' h'
      cases h' with
      | eval_BA_loadstack _ _ v' load' =>
          exact Option.some.inj (load'.symm.trans load)
  | eval_BA_addrstack ofs =>
      intro v' h'
      cases h'
      rfl
  | eval_BA_loadglobal chunk id ofs v load =>
      intro v' h'
      cases h' with
      | eval_BA_loadglobal _ _ _ v' load' =>
          exact Option.some.inj (load'.symm.trans load)
  | eval_BA_addrglobal id =>
      intro v' h'
      cases h'
      rfl
  | eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      intro v' h'
      cases h' with
      | eval_BA_splitlong _ _ vhi' vlo' hhi' hlo' =>
          have hhi_eq : vhi' = vhi := ihhi hhi'
          have hlo_eq : vlo' = vlo := ihlo hlo'
          cases hhi_eq
          cases hlo_eq
          rfl
  | eval_BA_addptr a1 a2 v1 v2 h1 h2 ih1 ih2 =>
      intro v' h'
      cases h' with
      | eval_BA_addptr _ _ v1' v2' h1' h2' =>
          have h1_eq : v1' = v1 := ih1 h1'
          have h2_eq : v2' = v2 := ih2 h2'
          cases h1_eq
          cases h2_eq
          rfl

private theorem cse_eval_builtin_args_determ
    {A : Type} (ge : Senv.t)
    (e : A → val) (sp : val) (m : mem)
    {al : List (builtin_arg A)} {vl : List val}
    (h : eval_builtin_args ge e sp m al vl) :
    ∀ {vl' : List val}, eval_builtin_args ge e sp m al vl' → vl' = vl := by
  unfold eval_builtin_args at h ⊢
  induction h with
  | nil =>
      intro vl' h'
      cases h'
      rfl
  | cons a1 b1 hp ht ih =>
      intro vl' h'
      cases h' with
      | cons _ b1' hp' ht' =>
          have hb : b1' = b1 := cse_eval_builtin_arg_determ ge e sp m hp hp'
          have ht_eq : _ := ih ht'
          cases hb
          cases ht_eq
          rfl

theorem rhs_eval_to_inj
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    rhs_eval_to_injStatement := by
  intro valu ge sp m rh v1 v2 h1 h2
  induction h1 with
  | op_eval_to op vl v hEval =>
      cases h2 with
      | op_eval_to _ _ v2 hEval2 =>
          exact Option.some.inj (hEval.symm.trans hEval2)
  | load_eval_to chunk addr vl a v p hAddr hLoad =>
      cases h2 with
      | load_eval_to _ _ _ a2 v2 _ hAddr2 hLoad2 =>
          have ha : a2 = a := Option.some.inj (hAddr2.symm.trans hAddr)
          subst a2
          exact Option.some.inj (hLoad.symm.trans hLoad2)
  | builtin_eval_to bf args vargs v hArgs hSem =>
      cases h2 with
      | builtin_eval_to _ _ vargs2 v2 hArgs2 hSem2 =>
          have hvargs : vargs2 = vargs :=
            cse_eval_builtin_args_determ (Genv.to_senv ge) valu sp m hArgs hArgs2
          subst vargs2
          exact Option.some.inj (hSem.symm.trans hSem2)

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

private theorem cse_pmap_get_set {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) :
    PMap.get i (PMap.set j x m) =
      match peq i j with
      | .left _ => x
      | .right _ => PMap.get i m := by
  unfold PMap.get PMap.set
  rw [PTree.gsspec_proof]
  cases h : peq i j with
  | left hij => simp [h]
  | right hne => simp [h]

private theorem cse_forget_reg_charact
    (n : CSEdomain.numbering)
    (rd r : reg)
    (v : positive) :
    wf_numbering n →
    r ∈ PMap.get v (CSE.forget_reg n rd) →
    r ≠ rd ∧ r ∈ PMap.get v n.num_val := by
  intro hnum hmem
  change positive at v
  unfold CSE.forget_reg at hmem
  cases hget : PTree.get rd n.num_reg with
  | none =>
      have hmem' : r ∈ PMap.get v n.num_val := by
        simpa [hget] using hmem
      constructor
      · intro hrd
        subst r
        have hreg := hnum.wf_num_val rd v hmem'
        rw [hget] at hreg
        cases hreg
      · exact hmem'
  | some v0 =>
      change positive at v0
      rw [hget] at hmem
      rw [cse_pmap_get_set] at hmem
      cases hv : peq v v0 with
      | left hvv =>
          subst v
          simp only [hv] at hmem
          have hrem :=
            CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_remove
              peq (PMap.get v0 n.num_val) r rd hmem
          exact ⟨hrem.2, hrem.1⟩
      | right hvv =>
          simp only [hv] at hmem
          constructor
          · intro hrd
            subst r
            have hreg := hnum.wf_num_val rd v hmem
            rw [hget] at hreg
            cases hreg
            exact (hvv rfl).elim
          · exact hmem

theorem update_reg_charact
    :
    update_reg_charactStatement := by
  intro n rd vd r v hnum hmem
  change positive at vd v
  dsimp [CSE.update_reg] at hmem
  rw [cse_pmap_get_set] at hmem
  cases hv : peq v vd with
  | left hvv =>
      subst v
      simp only [hv] at hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst r
        change CSEdomain.valnum at vd
        have hset := @PTree.gsspec_proof valnum rd rd vd n.num_reg
        cases hrd : peq rd rd with
        | left _ => simpa [hrd] using hset
        | right hne => exact (hne rfl).elim
      ·
        have hforget := cse_forget_reg_charact n rd r vd hnum htail
        change CSEdomain.valnum at vd
        have hset := @PTree.gsspec_proof valnum r rd vd n.num_reg
        cases hrd : peq r rd with
        | left heq => exact (hforget.1 heq).elim
        | right hne =>
            have hreg := hnum.wf_num_val r vd hforget.2
            have hset' : PTree.get r (PTree.set rd vd n.num_reg) =
                PTree.get r n.num_reg := by
              simpa [hrd] using hset
            exact hset'.trans hreg
  | right hvv =>
      simp only [hv] at hmem
      have hforget := cse_forget_reg_charact n rd r v hnum hmem
      change CSEdomain.valnum at v vd
      have hset := @PTree.gsspec_proof valnum r rd vd n.num_reg
      cases hrd : peq r rd with
      | left heq => exact (hforget.1 heq).elim
      | right hne =>
          have hreg := hnum.wf_num_val r v hforget.2
          have hset' : PTree.get r (PTree.set rd vd n.num_reg) =
              PTree.get r n.num_reg := by
            simpa [hrd] using hset
          exact hset'.trans hreg

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

private theorem cse_find_valnum_rhs_charact :
    ∀ (rh : rhs) (v : valnum) (eqs : List equation),
      CSE.find_valnum_rhs rh eqs = some v →
      ∃ rh', Eq v true rh' ∈ eqs ∧ rhs_compat rh rh' := by
  intro rh v eqs
  induction eqs with
  | nil => simp [CSE.find_valnum_rhs]
  | cons e eqs ih =>
      cases e with
      | Eq v' strict rh' =>
          simp only [CSE.find_valnum_rhs]
          intro h
          cases strict with
          | false =>
              rcases ih h with ⟨r'', hm, hs⟩
              exact ⟨r'', List.mem_cons_of_mem _ hm, hs⟩
          | true =>
              by_cases hc : CSEdomain.compat_rhs rh rh' = true
              · have hv : v' = v := by simpa [hc] using h
                subst v'
                exact ⟨rh', List.mem_cons_self, CSEdomain.compat_rhs_sound rh rh' hc⟩
              · rcases ih (by simpa [hc] using h) with ⟨r'', hm, hs⟩
                exact ⟨r'', List.mem_cons_of_mem _ hm, hs⟩

private theorem cse_add_rhs_holds_some
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (valu1 : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering) (rd : reg) (rh : rhs) (rs' : regset)
    (hnum : numbering_holds valu1 ge sp rs m n)
    (hvalid : rhs_valid valu1 ge sp rh)
    (hev : rhs_eval_to valu1 ge sp m rh (Regmap.get rd rs'))
    (hwf : wf_rhs n.num_next rh)
    (hsame : ∀ r, r ≠ rd → Regmap.get r rs' = Regmap.get r rs)
    (vres : valnum)
    (hfind : CSE.find_valnum_rhs rh n.num_eqs = some vres) :
    ∃ valu2, numbering_holds valu2 ge sp rs' m (CSE.add_rhs n rd rh) := by
  rcases cse_find_valnum_rhs_charact rh vres n.num_eqs hfind with ⟨rh', hIn, hcompat⟩
  have hwfe := hnum.num_holds_wf.wf_num_eqs _ hIn
  have hEq := hnum.num_holds_eq _ hIn
  have hev' := rhs_eval_to_compat valu1 ge sp m rh (Regmap.get rd rs') rh' hev hcompat
  have hval : Regmap.get rd rs' = valu1 vres := by
    cases hEq with
    | eq_holds_strict _ _ hevEq _ =>
        exact rhs_eval_to_inj valu1 ge sp m rh' (Regmap.get rd rs') (valu1 vres) hev' hevEq
  refine ⟨valu1, ?_⟩
  unfold CSE.add_rhs
  rw [hfind]
  constructor
  · constructor
    · intro e he
      exact hnum.num_holds_wf.wf_num_eqs e he
    · intro r v hget
      have hs := @PTree.gsspec_proof valnum r rd vres n.num_reg
      cases hp : peq r rd with
      | left heq =>
          subst r
          rw [show PTree.get rd (PTree.set rd vres n.num_reg) = some vres by
            simpa [hp] using hs] at hget
          cases hget
          exact hwfe.1
      | right hne =>
          rw [show PTree.get r (PTree.set rd vres n.num_reg) = PTree.get r n.num_reg by
            simpa [hp] using hs] at hget
          exact hnum.num_holds_wf.wf_num_reg r v hget
    · intro r v hr
      exact update_reg_charact n rd vres r v hnum.num_holds_wf hr
  · intro e he
    exact hnum.num_holds_eq e he
  · intro r v hget
    have hs := @PTree.gsspec_proof valnum r rd vres n.num_reg
    cases hp : peq r rd with
    | left heq =>
        subst r
        rw [show PTree.get rd (PTree.set rd vres n.num_reg) = some vres by
          simpa [hp] using hs] at hget
        cases hget
        exact hval
    | right hne =>
        rw [show PTree.get r (PTree.set rd vres n.num_reg) = PTree.get r n.num_reg by
          simpa [hp] using hs] at hget
        calc
          Regmap.get r rs' = Regmap.get r rs := hsame r hne
          _ = valu1 v := hnum.num_holds_reg r v hget

theorem add_rhs_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    add_rhs_holdsStatement := by
  intro valu1 ge sp rs m n rd rh rs' hnum hvalid hev hwf hsame
  cases hfind : CSE.find_valnum_rhs rh n.num_eqs with
  | some vres => exact cse_add_rhs_holds_some valu1 ge sp rs m n rd rh rs' hnum hvalid hev hwf hsame vres hfind
  | none =>
      let valu2 : valuation := fun vn =>
        match peq vn n.num_next with
        | .left _ => Regmap.get rd rs'
        | .right _ => valu1 vn
      have hagree : valu_agree valu1 valu2 n.num_next := by
        intro vn hvn
        simp only [valu2]
        cases hp : peq vn n.num_next with
        | left heq => exact False.elim ((Plt_ne _ _ hvn) heq)
        | right _ => rfl
      have hpleSucc : Ple n.num_next (PArith.BinPos.Pos.succ n.num_next) := Nat.le_of_lt (Plt_succ _)
      have hreg_same : PTree.get rd (PTree.set rd n.num_next n.num_reg) = some n.num_next := by
        have h := @PTree.gsspec_proof valnum rd rd n.num_next n.num_reg
        cases hp : peq rd rd with
        | left _ => simpa [hp] using h
        | right hne => exact False.elim (hne rfl)
      have hreg_other : ∀ r0 : positive, r0 ≠ rd →
          PTree.get r0 (PTree.set rd n.num_next n.num_reg) = PTree.get r0 n.num_reg := by
        intro r0 hne
        have h := @PTree.gsspec_proof valnum r0 rd n.num_next n.num_reg
        cases hp : peq r0 rd with
        | left heq => exact False.elim (hne heq)
        | right _ => simpa [hp, PTree.t] using h
      have hnext : valu2 n.num_next = Regmap.get rd rs' := by
        unfold valu2
        cases hp : peq n.num_next n.num_next with
        | left _ => simp [hp]
        | right hne => exact False.elim (hne rfl)
      refine ⟨valu2, ?_⟩
      simp only [CSE.add_rhs, hfind]
      constructor
      · constructor
        · intro e he
          rcases List.mem_cons.mp he with he | he
          · subst e
            constructor
            · exact Plt_succ _
            · intro v hv
              exact Plt_trans_succ _ _ (hwf v hv)
          · exact wf_equation_incr n.num_next (PArith.BinPos.Pos.succ n.num_next) e
              (hnum.num_holds_wf.wf_num_eqs e he) hpleSucc
        · intro r v hget
          change positive at v
          cases hp : peq r rd with
          | left heq =>
              subst r
              rw [hreg_same] at hget
              cases hget
              exact Plt_succ _
          | right hne =>
              rw [hreg_other r hne] at hget
              exact Plt_trans_succ _ _ (hnum.num_holds_wf.wf_num_reg r v hget)
        · intro r v hr
          exact update_reg_charact n rd n.num_next r v hnum.num_holds_wf hr
      · intro e he
        rcases List.mem_cons.mp he with he | he
        · subst e
          apply eq_holds_strict n.num_next rh
          · rw [hnext]
            exact rhs_eval_to_exten valu1 n.num_next valu2 hagree ge sp m rh
              (Regmap.get rd rs') hev hwf
          · exact rhs_valid_exten valu1 n.num_next valu2 hagree ge sp rh hvalid hwf
        · exact equation_holds_exten valu1 n.num_next valu2 hagree ge sp m e
            (hnum.num_holds_eq e he) (hnum.num_holds_wf.wf_num_eqs e he)
      · intro r v hget
        change positive at r v
        change Regmap.get r rs' = valu2 v
        cases hp : peq r rd with
        | left heq =>
            subst r
            rw [hreg_same] at hget
            cases hget
            exact hnext.symm
        | right hne =>
            unfold valu2
            rw [hreg_other r hne] at hget
            have hvneq : v ≠ n.num_next := by
              intro hv
              exact (Plt_ne _ _ (hnum.num_holds_wf.wf_num_reg r v hget)) hv
            cases hv : peq v n.num_next with
            | left hvEq => exact False.elim (hvneq hvEq)
            | right _ =>
                simp [hv]
                exact hsame r hne ▸ hnum.num_holds_reg r v hget

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.X86.Op
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Globalenvs

private theorem cse_forget_reg_charact_suffix
    (n : CSEdomain.numbering)
    (rd r : reg)
    (v : positive) :
    wf_numbering n →
    r ∈ PMap.get v (CSE.forget_reg n rd) →
    r ≠ rd ∧ r ∈ PMap.get v n.num_val := by
  intro hnum hmem
  change positive at v
  unfold CSE.forget_reg at hmem
  cases hget : PTree.get rd n.num_reg with
  | none =>
      have hmem' : r ∈ PMap.get v n.num_val := by
        simpa [hget] using hmem
      constructor
      · intro hrd
        subst r
        have hreg := hnum.wf_num_val rd v hmem'
        rw [hget] at hreg
        cases hreg
      · exact hmem'
  | some v0 =>
      change positive at v0
      rw [hget] at hmem
      rw [cse_pmap_get_set] at hmem
      cases hv : peq v v0 with
      | left hvv =>
          subst v
          simp only [hv] at hmem
          have hrem :=
            CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_remove
              peq (PMap.get v0 n.num_val) r rd hmem
          exact ⟨hrem.2, hrem.1⟩
      | right hvv =>
          simp only [hv] at hmem
          constructor
          · intro hrd
            subst r
            have hreg := hnum.wf_num_val rd v hmem
            rw [hget] at hreg
            cases hreg
            exact (hvv rfl).elim
          · exact hmem

theorem set_unknown_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    set_unknown_holdsStatement := by
  intro valu ge sp rs m n r v hnum
  change Regmap.t val at rs
  constructor
  · constructor
    · intro e he
      exact hnum.num_holds_wf.wf_num_eqs e he
    · intro r0 v0 hget
      change Plt v0 n.num_next
      change PTree.get r0 (PTree.remove r n.num_reg) = some v0 at hget
      by_cases hne : r0 = r
      · subst r0
        have hnone := PTree.grs_proof r n.num_reg
        rw [hnone] at hget
        cases hget
      · have hsame := PTree.gro_proof (m := n.num_reg) hne
        rw [hsame] at hget
        exact hnum.num_holds_wf.wf_num_reg r0 v0 hget
    · intro r0 v0 hmem
      change r0 ∈ PMap.get v0 (CSE.forget_reg n r) at hmem
      change PTree.get r0 (PTree.remove r n.num_reg) = some v0
      have hforget := cse_forget_reg_charact_suffix n r r0 v0 hnum.num_holds_wf hmem
      by_cases hne : r0 = r
      · exact (hforget.1 hne).elim
      · have hsame := PTree.gro_proof (m := n.num_reg) hne
        rw [hsame]
        exact hnum.num_holds_wf.wf_num_val r0 v0 hforget.2
  · intro e he
    exact hnum.num_holds_eq e he
  · intro r0 v0 hget
    change PTree.get r0 (PTree.remove r n.num_reg) = some v0 at hget
    by_cases hne : r0 = r
    · subst r0
      have hnone := PTree.grs_proof r n.num_reg
      rw [hnone] at hget
      cases hget
    · have hsame := PTree.gro_proof (m := n.num_reg) hne
      rw [hsame] at hget
      change reg at r0
      rw [Regmap.gso_proof _ _ _ _ _ hne]
      exact hnum.num_holds_reg r0 v0 hget

private theorem cse_add_op_move_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (valu1 : valuation) (ge : genv) (sp : val) (rs : regset) (m : mem)
    (n : numbering) (src dst : reg) (v : val)
    (hnum : numbering_holds valu1 ge sp rs m n)
    (heval : eval_operation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge sp Omove [Regmap.get src rs] m = some v) :
    ∃ valu2, numbering_holds valu2 ge sp (Regmap.set dst v rs) m
      (CSE.add_op n dst Omove [src]) := by
  change Regmap.t val at rs
  have hv : Regmap.get src rs = v := by
    change some (Regmap.get src rs) = some v at heval
    exact Option.some.inj heval
  cases hVN : CSE.valnum_reg n src with
  | mk n1 vsrc =>
      rcases valnum_reg_holds valu1 ge sp rs m n src n1 vsrc hnum hVN with
        ⟨valu2, hnum2, hsrc, hagree, hlt, hple⟩
      refine ⟨valu2, ?_⟩
      simp only [CSE.add_op, is_move_operation]
      rw [hVN]
      constructor
      · constructor
        · intro e he
          exact hnum2.num_holds_wf.wf_num_eqs e he
        · intro r0 v0 hget
          change Plt v0 n1.num_next
          have hs := @PTree.gsspec_proof valnum r0 dst vsrc n1.num_reg
          cases hp : peq r0 dst with
          | left heq =>
              subst r0
              rw [hs, hp] at hget
              cases hget
              exact hlt
          | right hne =>
              rw [hs, hp] at hget
              exact hnum2.num_holds_wf.wf_num_reg r0 v0 hget
        · intro r0 v0 hmem
          exact update_reg_charact n1 dst vsrc r0 v0 hnum2.num_holds_wf hmem
      · intro e he
        exact hnum2.num_holds_eq e he
      · intro r0 v0 hget
        change reg at r0
        have hs := @PTree.gsspec_proof valnum r0 dst vsrc n1.num_reg
        cases hp : peq r0 dst with
        | left heq =>
            subst r0
            rw [hs, hp] at hget
            cases hget
            rw [Regmap.gss_proof]
            exact hv.symm.trans hsrc
        | right hne =>
            rw [hs, hp] at hget
            rw [Regmap.gso_proof _ _ _ _ _ hne]
            exact hnum2.num_holds_reg r0 v0 hget

theorem add_load_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    add_load_holdsStatement := by
  intro valu1 ge sp rs m n addr args ap b ofs chunk v dst bc hnum haddr hload hpmatch hgenv hstack
  change Regmap.t val at rs
  cases hVN : CSE.valnum_regs n args with
  | mk n1 vl =>
      rcases valnum_regs_holds args valu1 ge (Vptr sp CompCert4Lean.Lib.Integers.Ptrofs.zero) rs m n n1 vl hnum hVN with
        ⟨valu2, hnum2, hmap, hagree, hwf, hple⟩
      have haddr2 := haddr
      rw [hmap] at haddr2
      have hvalid : rhs_valid valu2 ge (Vptr sp CompCert4Lean.Lib.Integers.Ptrofs.zero)
          (Load chunk addr vl ap) :=
        rhs_valid.load_valid sp chunk addr vl ap b ofs bc haddr2 hpmatch hgenv hstack
      have hev0 : rhs_eval_to valu2 ge (Vptr sp CompCert4Lean.Lib.Integers.Ptrofs.zero) m
          (Load chunk addr vl ap) v :=
        rhs_eval_to.load_eval_to chunk addr vl (Vptr b ofs) v ap haddr2 hload
      have hev : rhs_eval_to valu2 ge (Vptr sp CompCert4Lean.Lib.Integers.Ptrofs.zero) m
          (Load chunk addr vl ap) (Regmap.get dst (Regmap.set dst v rs)) := by
        rw [Regmap.gss_proof]
        exact hev0
      have hwfrhs : wf_rhs n1.num_next (Load chunk addr vl ap) := by
        intro vn hvn
        exact hwf vn hvn
      have hsame : ∀ r, r ≠ dst →
          Regmap.get r (Regmap.set dst v rs) = Regmap.get r rs := by
        intro r hne
        exact Regmap.gso_proof _ _ _ _ _ hne
      have hres := add_rhs_holds valu2 ge (Vptr sp CompCert4Lean.Lib.Integers.Ptrofs.zero) rs m n1 dst
        (Load chunk addr vl ap) (Regmap.set dst v rs) hnum2 hvalid hev hwfrhs hsame
      simp only [CSE.add_load]
      rw [hVN]
      exact hres

theorem add_builtin_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    add_builtin_holdsStatement := by
  intro valu1 ge sp rs m n bf args res vargs vres hnum hargs hsem
  change Regmap.t val at rs
  cases res with
  | BR rd =>
      cases hVB : CSE.valnum_builtin_args n args with
      | mk n1 args' =>
          rcases valnum_builtin_args_holds ge sp rs m args vargs hargs valu1 n n1 args' hnum hVB with
            ⟨valu2, hnum2, hargs2, hagree, hwf, hple⟩
          have hvalid : rhs_valid valu2 ge sp (Builtin bf args') :=
            rhs_valid.builtin_valid sp bf args'
          have hev0 : rhs_eval_to valu2 ge sp m (Builtin bf args') vres :=
            rhs_eval_to.builtin_eval_to bf args' vargs vres hargs2 hsem
          have hev : rhs_eval_to valu2 ge sp m (Builtin bf args')
              (Regmap.get rd (Regmap.set rd vres rs)) := by
            rw [Regmap.gss_proof]
            exact hev0
          have hwfrhs : wf_rhs n1.num_next (Builtin bf args') := by
            intro vn hvn
            exact hwf vn hvn
          have hsame : ∀ r, r ≠ rd →
              Regmap.get r (Regmap.set rd vres rs) = Regmap.get r rs := by
            intro r hne
            exact Regmap.gso_proof _ _ _ _ _ hne
          have hres := add_rhs_holds valu2 ge sp rs m n1 rd
            (Builtin bf args') (Regmap.set rd vres rs) hnum2 hvalid hev hwfrhs hsame
          simp only [CSE.add_builtin]
          rw [hVB]
          exact hres
  | BR_none =>
      refine ⟨valu1, ?_⟩
      simpa [CSE.add_builtin, regmap_setres] using hnum
  | BR_splitlong hi lo =>
      refine ⟨valu1, ?_⟩
      simpa [CSE.add_builtin, regmap_setres] using hnum

theorem add_op_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    add_op_holdsStatement := by
  intro valu1 ge sp rs m n op args v dst hnum heval
  change Regmap.t val at rs
  cases hmove : is_move_operation op args with
  | some src =>
      have hshape := @is_move_operation_correct reg op args src hmove
      rcases hshape with ⟨hop, hargs⟩
      subst op
      subst args
      exact cse_add_op_move_holds valu1 ge sp rs m n src dst v hnum heval
  | none =>
      cases hVN : CSE.valnum_regs n args with
      | mk n1 vl =>
          rcases valnum_regs_holds args valu1 ge sp rs m n n1 vl hnum hVN with
            ⟨valu2, hnum2, hmap, hagree, hwf, hple⟩
          have heval2 := heval
          rw [hmap] at heval2
          have hvalid : rhs_valid valu2 ge sp (Op op vl) :=
            rhs_valid.op_valid sp op vl
          have hev : rhs_eval_to valu2 ge sp m (Op op vl)
              (Regmap.get dst (Regmap.set dst v rs)) := by
            apply rhs_eval_to.op_eval_to
            rw [Regmap.gss_proof]
            exact heval2
          have hwfrhs : wf_rhs n1.num_next (Op op vl) := by
            intro vn hvn
            exact hwf vn hvn
          have hsame : ∀ r, r ≠ dst →
              Regmap.get r (Regmap.set dst v rs) = Regmap.get r rs := by
            intro r hne
            exact Regmap.gso_proof _ _ _ _ _ hne
          have hres := add_rhs_holds valu2 ge sp rs m n1 dst (Op op vl)
            (Regmap.set dst v rs) hnum2 hvalid hev hwfrhs hsame
          simp only [CSE.add_op, hmove]
          rw [hVN]
          exact hres

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

theorem set_res_unknown_holds
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    set_res_unknown_holdsStatement := by
  intro valu ge sp rs m n r v hnum
  cases r with
  | BR rd =>
      exact set_unknown_holds valu ge sp rs m n rd v hnum
  | BR_none =>
      simpa [CompCert4Lean.Backend.Registers.regmap_setres, CSE.set_res_unknown] using hnum
  | BR_splitlong hi lo =>
      simpa [CompCert4Lean.Backend.Registers.regmap_setres, CSE.set_res_unknown] using hnum

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain

theorem kill_eqs_charact : kill_eqs_charactStatement := by
  intro pred l strict r eqs
  induction eqs with
  | nil =>
      simp [CSE.kill_eqs]
  | cons e eqs ih =>
      cases e with
      | Eq l' strict' r' =>
          simp only [CSE.kill_eqs]
          cases hpred : pred r' with
          | true =>
              intro hmem
              have hmem' : Eq l strict r ∈ CSE.kill_eqs pred eqs := by
                simpa [hpred] using hmem
              obtain ⟨hfalse, hin⟩ := ih hmem'
              exact ⟨hfalse, List.mem_cons_of_mem _ hin⟩
          | false =>
              intro hmem
              simp [hpred] at hmem
              rcases hmem with hhead | htail
              · rcases hhead with ⟨hl, hs, hr⟩
                subst r
                subst l
                subst strict
                exact ⟨hpred, List.mem_cons_self⟩
              · obtain ⟨hfalse, hin⟩ := ih htail
                exact ⟨hfalse, List.mem_cons_of_mem _ hin⟩

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain

theorem kill_equations_hold
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    kill_equations_holdStatement := by
  intro valu ge sp rs m n pred m' hnum htrans
  unfold CSE.kill_equations
  constructor
  · constructor
    · intro e he
      cases e with
      | Eq l strict r =>
          have hc := kill_eqs_charact pred l strict r n.num_eqs he
          exact hnum.num_holds_wf.wf_num_eqs _ hc.2
    · exact hnum.num_holds_wf.wf_num_reg
    · exact hnum.num_holds_wf.wf_num_val
  · intro e he
    cases e with
    | Eq l strict r =>
        have hc := kill_eqs_charact pred l strict r n.num_eqs he
        have hold := hnum.num_holds_eq _ hc.2
        cases hold with
        | eq_holds_strict _ _ hev hvalid =>
            exact equation_holds.eq_holds_strict l r
              (htrans r (valu l) hc.1 hvalid hev) hvalid
        | eq_holds_lessdef _ _ v hev hld hvalid =>
            exact equation_holds.eq_holds_lessdef l r v
              (htrans r v hc.1 hvalid hev) hld hvalid
  · exact hnum.num_holds_reg

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Common.Events
open CompCert4Lean.X86.Op

private theorem cse_cmpu_bool_ptr64
    (p q : CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool)
    (c : CompCert4Lean.Lib.Integers.comparison)
    (v1 v2 : CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.cmpu_bool p c v1 v2 =
      CompCert4Lean.Common.Values.Val.cmpu_bool q c v1 v2 := by
  cases v1 <;> cases v2 <;>
    simp [CompCert4Lean.Common.Values.Val.cmpu_bool,
      CompCert4Lean.X86_64.Archi.ptr64]

private theorem cse_condition_memory_independent
    (c : condition) (args : List CompCert4Lean.Common.Values.val)
    (m m' : CompCert4Lean.Common.Memory.mem) :
    condition_depends_on_memory c = false →
      eval_condition c args m = eval_condition c args m' := by
  intro hdep
  cases args with
  | nil =>
      cases c <;>
        simp [condition_depends_on_memory, eval_condition,
          CompCert4Lean.X86_64.Archi.ptr64, cse_cmpu_bool_ptr64] at hdep ⊢ <;>
        exact cse_cmpu_bool_ptr64 _ _ _ _ _
  | cons a rest =>
      cases rest with
      | nil =>
          cases c <;>
            simp [condition_depends_on_memory, eval_condition,
              CompCert4Lean.X86_64.Archi.ptr64, cse_cmpu_bool_ptr64] at hdep ⊢ <;>
            exact cse_cmpu_bool_ptr64 _ _ _ _ _
      | cons b rest =>
          cases rest with
          | nil =>
              cases c <;>
                simp [condition_depends_on_memory, eval_condition,
                  CompCert4Lean.X86_64.Archi.ptr64, cse_cmpu_bool_ptr64] at hdep ⊢ <;>
                exact cse_cmpu_bool_ptr64 _ _ _ _ _
          | cons d rest =>
              cases c <;>
                simp [condition_depends_on_memory, eval_condition,
                  CompCert4Lean.X86_64.Archi.ptr64, cse_cmpu_bool_ptr64] at hdep ⊢ <;>
                exact cse_cmpu_bool_ptr64 _ _ _ _ _

set_option maxHeartbeats 1000000 in
private theorem cse_operation_memory_independent
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (F V : Type)
    (ge : CompCert4Lean.Common.Globalenvs.Genv.t F V)
    (sp : CompCert4Lean.Common.Values.val) (op : operation)
    (args : List CompCert4Lean.Common.Values.val)
    (m m' : CompCert4Lean.Common.Memory.mem) :
    op_depends_on_memory op = false →
      eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp op args m =
      eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge sp op args m' := by
  intro hdep
  cases op with
  | Ocmp c =>
      have hcond := cse_condition_memory_independent c args m m' hdep
      cases args with
      | nil =>
          change some (CompCert4Lean.Common.Values.Val.of_optbool
            (eval_condition c [] m)) =
            some (CompCert4Lean.Common.Values.Val.of_optbool
              (eval_condition c [] m'))
          exact congrArg
            (fun x => some (CompCert4Lean.Common.Values.Val.of_optbool x)) hcond
      | cons a rest =>
          cases rest with
          | nil =>
              change some (CompCert4Lean.Common.Values.Val.of_optbool
                (eval_condition c [a] m)) =
                some (CompCert4Lean.Common.Values.Val.of_optbool
                  (eval_condition c [a] m'))
              exact congrArg
                (fun x => some (CompCert4Lean.Common.Values.Val.of_optbool x)) hcond
          | cons b rest =>
              cases rest with
              | nil =>
                  change some (CompCert4Lean.Common.Values.Val.of_optbool
                    (eval_condition c [a, b] m)) =
                    some (CompCert4Lean.Common.Values.Val.of_optbool
                      (eval_condition c [a, b] m'))
                  exact congrArg
                    (fun x => some (CompCert4Lean.Common.Values.Val.of_optbool x)) hcond
              | cons d rest =>
                  change some (CompCert4Lean.Common.Values.Val.of_optbool
                    (eval_condition c (a :: b :: d :: rest) m)) =
                    some (CompCert4Lean.Common.Values.Val.of_optbool
                      (eval_condition c (a :: b :: d :: rest) m'))
                  exact congrArg
                    (fun x => some (CompCert4Lean.Common.Values.Val.of_optbool x)) hcond
  | Osel c ty =>
      cases args with
      | nil =>
          change none = none
          rfl
      | cons v1 rest =>
          cases rest with
          | nil =>
              change none = none
              rfl
          | cons v2 rest =>
              have hcond := cse_condition_memory_independent c rest m m' hdep
              change some (CompCert4Lean.Common.Values.Val.select
                (eval_condition c rest m) v1 v2 ty) =
                some (CompCert4Lean.Common.Values.Val.select
                  (eval_condition c rest m') v1 v2 ty)
              exact congrArg
                (fun x => some (CompCert4Lean.Common.Values.Val.select x v1 v2 ty)) hcond
  | _ =>
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b rest =>
              cases rest with
              | nil => rfl
              | cons c rest => rfl

private theorem cse_builtin_arg_memory_independent
    {A : Type} (m' : CompCert4Lean.Common.Memory.mem)
    (ge : CompCert4Lean.Common.Globalenvs.Senv.t)
    (e : A → CompCert4Lean.Common.Values.val)
    (sp : CompCert4Lean.Common.Values.val)
    (m : CompCert4Lean.Common.Memory.mem)
    (ba : CompCert4Lean.Common.AST.builtin_arg A)
    (v : CompCert4Lean.Common.Values.val) :
    eval_builtin_arg ge e sp m ba v →
    builtin_arg_depends_on_memory ba = false →
    eval_builtin_arg ge e sp m' ba v := by
  intro harg hdep
  cases harg with
  | eval_BA x => exact eval_BA x
  | eval_BA_int n => exact eval_BA_int n
  | eval_BA_long n => exact eval_BA_long n
  | eval_BA_float n => exact eval_BA_float n
  | eval_BA_single n => exact eval_BA_single n
  | eval_BA_loadstack chunk ofs v hload => cases hdep
  | eval_BA_addrstack ofs => exact eval_BA_addrstack ofs
  | eval_BA_loadglobal chunk id ofs v hload => cases hdep
  | eval_BA_addrglobal id ofs => exact eval_BA_addrglobal id ofs
  | eval_BA_splitlong hi lo vhi vlo hhi hlo =>
      simp [builtin_arg_depends_on_memory] at hdep
      exact eval_BA_splitlong hi lo vhi vlo
        (cse_builtin_arg_memory_independent m' ge e sp m hi vhi hhi hdep.1)
        (cse_builtin_arg_memory_independent m' ge e sp m lo vlo hlo hdep.2)
  | eval_BA_addptr a1 a2 v1 v2 h1 h2 =>
      simp [builtin_arg_depends_on_memory] at hdep
      exact eval_BA_addptr a1 a2 v1 v2
        (cse_builtin_arg_memory_independent m' ge e sp m a1 v1 h1 hdep.1)
        (cse_builtin_arg_memory_independent m' ge e sp m a2 v2 h2 hdep.2)

private theorem cse_builtin_args_memory_independent
    {A : Type} (m' : CompCert4Lean.Common.Memory.mem)
    (ge : CompCert4Lean.Common.Globalenvs.Senv.t)
    (e : A → CompCert4Lean.Common.Values.val)
    (sp : CompCert4Lean.Common.Values.val)
    (m : CompCert4Lean.Common.Memory.mem)
    (bal : List (CompCert4Lean.Common.AST.builtin_arg A))
    (vl : List CompCert4Lean.Common.Values.val) :
    eval_builtin_args ge e sp m bal vl →
    builtin_args_depends_on_memory bal = false →
    eval_builtin_args ge e sp m' bal vl := by
  intro hargs hdep
  induction hargs with
  | nil => exact CompCert4Lean.Lib.Coqlib.list_forall2.nil _
  | cons ba v hba hrest ih =>
      simp [builtin_args_depends_on_memory] at hdep
      apply CompCert4Lean.Lib.Coqlib.list_forall2.cons
      · exact cse_builtin_arg_memory_independent m' ge e sp m ba v hba hdep.1
      · exact ih hdep.2

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Common.Events
open CompCert4Lean.X86.Op

theorem kill_all_loads_hold
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    kill_all_loads_holdStatement := by
  intro valu ge sp rs m n m' hnum
  apply kill_equations_hold valu ge sp rs m n CSE.filter_loads m' hnum
  intro rh v hpred hvalid hev
  cases rh with
  | Op op vl =>
      cases hev with
      | op_eval_to op vl v hEval =>
          have hop := cse_operation_memory_independent
            (F := RTL.fundef) (V := Unit) ge sp op (List.map valu vl) m m' hpred
          exact rhs_eval_to.op_eval_to op vl v (by rw [← hop]; exact hEval)
  | Load chunk addr vl p =>
      simp [CSE.filter_loads] at hpred
  | Builtin bf args =>
      cases hev with
      | builtin_eval_to bf args vargs v hArgs hSem =>
          have hargs' : builtin_args_depends_on_memory args = false := by
            simpa [CSE.filter_loads] using hpred
          have hArgs' := cse_builtin_args_memory_independent m'
            (CompCert4Lean.Common.Globalenvs.Genv.to_senv ge) valu sp m args vargs
            hArgs hargs'
          exact rhs_eval_to.builtin_eval_to bf args vargs v hArgs' hSem

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain

theorem kill_cheap_computations_hold
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    kill_cheap_computations_holdStatement := by
  intro valu ge sp rs m n hnum
  apply kill_equations_hold valu ge sp rs m n CSE.filter_cheap m hnum
  intro rh v hpred hvalid hev
  cases rh with
  | Op op vl =>
      simp [CSE.filter_cheap] at hpred
  | Load chunk addr vl p =>
      simp [CSE.filter_cheap] at hpred
  | Builtin bf args =>
      exact hev

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Lib.Coqlib

theorem shift_memcpy_eq_wf : shift_memcpy_eq_wfStatement := by
  intro src sz delta e e' next hshift hwf
  unfold CSE.shift_memcpy_eq at hshift
  cases e with
  | Eq l strict r =>
      cases r with
      | Op op vl => simp at hshift
      | Builtin bf args => simp at hshift
      | Load chunk addr vl p =>
          cases addr with
          | Ainstack ofs =>
              simp at hshift
              rcases hshift with ⟨_, rfl⟩
              change Plt l next ∧ wf_rhs next
                (.Load chunk (.Ainstack _) [] (.Stk _))
              exact ⟨hwf.1, by
                intro v hv
                cases hv
                ⟩
          | _ => simp at hshift

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

theorem add_memcpy_eqs_charact : add_memcpy_eqs_charactStatement := by
  intro e' src sz delta eqs2 eqs1
  induction eqs1 with
  | nil =>
      intro h
      exact Or.inl h
  | cons e eqs ih =>
      intro h
      unfold CSE.add_memcpy_eqs at h
      split at h <;> rename_i hshift
      · rcases ih h with h2 | ⟨e0, he0, hs⟩
        · exact Or.inl h2
        · exact Or.inr ⟨e0, List.mem_cons_of_mem e he0, hs⟩
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inr ⟨e, by simp, hshift⟩
        · rcases ih h with h2 | ⟨e0, he0, hs⟩
          · exact Or.inl h2
          · exact Or.inr ⟨e0, List.mem_cons_of_mem e he0, hs⟩

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain

private theorem reduce_rec_sound_aux_for_reduce_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    reduce_rec_soundStatement := by
  intro A f V ge sp rs m sem f_sound n valu hnum
  intro niter
  induction niter with
  | zero =>
      intro op args op' rl' res hred hsem
      simp [CSE.reduce_rec] at hred
  | succ niter ih =>
      intro op args op' rl' res hred hsem
      cases hstep : f (fun v => CSE.find_valnum_num v n.num_eqs) op args with
      | none =>
          simp [CSE.reduce_rec, hstep] at hred
      | some step =>
          rcases step with ⟨op1, args1⟩
          have hsem1 : sem op1 (List.map valu args1) = some res := by
            have hs : sem op1 (List.map valu args1) = sem op (List.map valu args) :=
              f_sound (fun v => CSE.find_valnum_num v n.num_eqs) valu
                op args op1 args1 (fun v rhs hfind => by
                have heq := hnum.num_holds_eq (Eq v true rhs)
                  (find_valnum_num_charact v rhs n.num_eqs hfind)
                cases heq with
                | eq_holds_strict _ _ heval _ => exact heval) hstep
            exact hs.trans hsem
          cases hrec : CSE.reduce_rec f n niter op1 args1 with
          | none =>
              cases hregs : CSE.regs_valnums n args1 with
              | none =>
                  simp [CSE.reduce_rec, hstep, hrec, hregs] at hred
              | some rl1 =>
                  simp [CSE.reduce_rec, hstep, hrec, hregs] at hred
                  obtain ⟨rfl, rfl⟩ := hred
                  rw [regs_valnums_sound n valu ge sp rs m args1 rl1 hnum hregs]
                  exact hsem1
          | some rec =>
              rcases rec with ⟨op2, rl2⟩
              simp [CSE.reduce_rec, hstep, hrec] at hred
              obtain ⟨rfl, rfl⟩ := hred
              exact ih op1 args1 op2 rl2 res hrec hsem1

theorem reduce_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    reduce_soundStatement := by
  intro A f V ge sp rs m sem f_sound n valu hnum
  intro op rl vl op' rl' res hreduce hmap hsem
  cases hrec : CSE.reduce_rec f n 4 op vl with
  | none =>
      simp [CSE.reduce, hrec] at hreduce
      obtain ⟨rfl, rfl⟩ := hreduce
      exact hsem
  | some rec =>
      rcases rec with ⟨op1, rl1⟩
      simp [CSE.reduce, hrec] at hreduce
      obtain ⟨rfl, rfl⟩ := hreduce
      apply reduce_rec_sound_aux_for_reduce_sound A f V ge sp rs m sem f_sound n valu hnum
        4 op vl op1 rl1 res hrec
      rw [hmap]
      exact hsem

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Common.Values

theorem reduce_rec_lessdef_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    reduce_rec_lessdef_soundStatement := by
  intro A f ge sp rs m sem f_sound n valu hnum
  intro niter
  induction niter with
  | zero =>
      intro op args op' rl' r hred hsem
      simp [CSE.reduce_rec] at hred
  | succ niter ih =>
      intro op args op' rl' r hred hsem
      cases hstep : f (fun v => CSE.find_valnum_num v n.num_eqs) op args with
      | none =>
          simp [CSE.reduce_rec, hstep] at hred
      | some step =>
          rcases step with ⟨op1, args1⟩
          have hex : ∃ r',
              sem op1 (List.map valu args1) = some r' ∧ Val.lessdef r r' := by
            apply f_sound (fun v => CSE.find_valnum_num v n.num_eqs) valu
              op args op1 args1 r
            · intro v rhs hfind
              have heq := hnum.num_holds_eq (Eq v true rhs)
                (find_valnum_num_charact v rhs n.num_eqs hfind)
              cases heq with
              | eq_holds_strict _ _ heval _ => exact heval
            · exact hstep
            · exact hsem
          cases hrec : CSE.reduce_rec f n niter op1 args1 with
          | none =>
              cases hregs : CSE.regs_valnums n args1 with
              | none =>
                  simp [CSE.reduce_rec, hstep, hrec, hregs] at hred
              | some rl1 =>
                  simp [CSE.reduce_rec, hstep, hrec, hregs] at hred
                  obtain ⟨rfl, rfl⟩ := hred
                  obtain ⟨r', hs, hld⟩ := hex
                  refine ⟨r', ?_, hld⟩
                  rw [regs_valnums_sound n valu ge sp rs m args1 rl1 hnum hregs]
                  exact hs
          | some rec =>
              rcases rec with ⟨op2, rl2⟩
              simp [CSE.reduce_rec, hstep, hrec] at hred
              obtain ⟨rfl, rfl⟩ := hred
              obtain ⟨r', hs, hld⟩ := hex
              obtain ⟨r'', hs2, hld2⟩ := ih op1 args1 op2 rl2 r' hrec hs
              refine ⟨r'', hs2, ?_⟩
              cases hld with
              | lessdef_refl => exact hld2
              | lessdef_undef => exact Val.lessdef_undef _

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Common.Values

theorem reduce_lessdef_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    reduce_lessdef_soundStatement := by
  intro A f ge sp rs m sem f_sound n valu hnum
  intro op rl vl op' rl' r hreduce hmap hsem
  cases hrec : CSE.reduce_rec f n 4 op vl with
  | none =>
      simp [CSE.reduce, hrec] at hreduce
      obtain ⟨rfl, rfl⟩ := hreduce
      exact ⟨r, hsem, Val.lessdef_refl r⟩
  | some rec =>
      rcases rec with ⟨op1, rl1⟩
      simp [CSE.reduce, hrec] at hreduce
      obtain ⟨rfl, rfl⟩ := hreduce
      apply reduce_rec_lessdef_sound A f ge sp rs m sem f_sound n valu hnum
        4 op vl op1 rl1 r hrec
      rw [hmap]
      exact hsem

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

theorem analysis_correct_1
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) :
    analysis_correct_1Statement cfg := by
  intro ge sp rs m f dm vapprox approx pc pc' i hanalyze hcode hsucc hsat
  have hsol := CSE.Solver.fixpoint_solution_proof
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (CSE.Solver.law_obligation_proof
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate))
  have hge := hsol RTL.instruction f.fn_code RTL.successors_instr
      (CSE.transfer cfg f dm vapprox)
      f.fn_entrypoint approx pc i pc' hanalyze hcode hsucc
  rcases hsat with ⟨valu, hnum⟩
  refine ⟨valu, ?_⟩
  exact hge valu ge sp rs m hnum

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Common.Values

theorem analysis_correct_entry
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) :
    analysis_correct_entryStatement cfg := by
  intro ge sp rs m f dm vapprox approx hanalyze
  have hsol := CSE.Solver.fixpoint_entry_proof
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (CSE.Solver.law_obligation_proof
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate))
  have hentry := hsol RTL.instruction f.fn_code RTL.successors_instr
      (CSE.transfer cfg f dm vapprox)
      f.fn_entrypoint approx hanalyze
  let valu : valuation := fun _ => Vundef
  refine ⟨valu, ?_⟩
  have hempty : numbering_holds valu ge sp rs m CSE.Solver.L.top := by
    change numbering_holds valu ge sp rs m empty_numbering
    exact empty_numbering_holds valu ge sp rs m
  exact (congrArg (fun n => numbering_holds valu ge sp rs m n) hentry).mpr hempty

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSE
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem cse_symbol_add_global
    {A B V W : Type} (ge1 : Genv.t A V) (ge2 : Genv.t B W) (id : ident)
    (hm : ∀ id', PTree.get id' ge2.genv_symb = PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) := by
  intro id'
  have h2 := @PTree.getSet_equation _ id' id ge2.genv_next ge2.genv_symb
  have h1 := @PTree.getSet_equation _ id' id ge1.genv_next ge1.genv_symb
  by_cases h : id' = id
  · rw [h2, h1]
    simp only [dif_pos h]
    exact congrArg some hn
  · rw [h2, h1]
    simp only [dif_neg h]
    exact hm id'

private theorem cse_match_genvs_add_global
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) (id : ident)
    (g1 : globdef A V) (g2 : globdef B W)
    (hm : Genv.match_genvs R ge1 ge2) (hg : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · exact cse_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @PTree.getSet_equation (globdef A V) b ge1.genv_next g1 ge1.genv_defs
    have h2 := @PTree.getSet_equation (globdef B W) b ge2.genv_next g2 ge2.genv_defs
    by_cases h : b = ge1.genv_next
    · have h' : b = ge2.genv_next := h.trans hm.mge_next.symm
      rw [h1, h2]
      simp only [dif_pos h, dif_pos h']
      exact option_rel.some g1 g2 hg
    · have h' : b ≠ ge2.genv_next := by
        intro hb
        apply h
        exact hb.trans hm.mge_next
      rw [h1, h2]
      simp only [dif_neg h, dif_neg h']
      exact hm.mge_defs b

private theorem cse_match_genvs_add_globals
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (xs : List (ident × globdef A V)) (ys : List (ident × globdef B W))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) (hm : Genv.match_genvs R ge1 ge2) :
    Genv.match_genvs R (Genv.add_globals ge1 xs) (Genv.add_globals ge2 ys) := by
  induction hxy generalizing ge1 ge2 with
  | nil => simpa [Genv.add_globals] using hm
  | @cons a xs b ys hab htail ih =>
      rcases a with ⟨aid, ag⟩
      rcases b with ⟨bid, bg⟩
      change aid = bid ∧ R ag bg at hab
      rcases hab with ⟨rfl, hab⟩
      simp only [Genv.add_globals, List.foldl_cons]
      apply ih
      exact cse_match_genvs_add_global R ge1 ge2 aid ag bg hm hab

private theorem cse_globalenv_match
    {C F1 V1 F2 V2 : Type} [Linker C]
    (mf : C → F1 → F2 → Prop) (mv : V1 → V2 → Prop) (ctx : C)
    (p : CompCert4Lean.Common.AST.program F1 V1)
    (tp : CompCert4Lean.Common.AST.program F2 V2)
    (h : match_program_gen mf mv ctx p tp) :
    Genv.match_genvs (match_globdef mf mv ctx)
      (Genv.globalenv p) (Genv.globalenv tp) := by
  rcases h with ⟨hdefs, hmain, hpub⟩
  unfold Genv.globalenv
  rw [hpub]
  apply cse_match_genvs_add_globals
  · exact hdefs
  · constructor
    · rfl
    · intro id
      rfl
    · intro b
      exact option_rel.none _

theorem symbols_preserved
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    ∀ (cfg : CompilerConfig), symbols_preservedStatement cfg := by
  intro cfg prog tprog hm id
  letI : Linker CompCert4Lean.Backend.RTL.fundef :=
    Linker_fundef CompCert4Lean.Backend.RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker CompCert4Lean.Backend.RTL.program :=
    Linker_prog CompCert4Lean.Backend.RTL.fundef Unit
  unfold match_prog CompCert4Lean.Common.Linking.match_program
    CompCert4Lean.Common.Linking.match_program_gen at hm
  have hg := cse_globalenv_match
    (fun (cu : CompCert4Lean.Backend.RTL.program) f tf =>
      CSE.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu)
          (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f = .OK tf)
    (fun x y : Unit => x = y) prog prog tprog hm
  simpa [Genv.find_symbol] using hg.mge_symb id

end CompCert4Lean.Backend.CSEproof

namespace CompCert4Lean.Backend.CSEproof

open CompCert4Lean.Backend.CSE
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private abbrev CSEproofCompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev CSEproofBinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev CSEproofZOfNat := ZArith.BinInt.Z.of_nat

variable
    [binary64_certificate : CSEproofBinaryNormalizeCertificate
      (CSEproofZOfNat 53) (CSEproofZOfNat 1024)]
    [binary32_certificate : CSEproofBinaryNormalizeCertificate
      (CSEproofZOfNat 24) (CSEproofZOfNat 128)]

private theorem cse_add_globals_public {F V : Type}
    (ge : Genv.t F V) (gl : List (ident × globdef F V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x xs ih =>
      simp only [Genv.add_globals, List.foldl]
      exact ih (Genv.add_global ge x)

theorem senv_preserved : ∀ (cfg : CSEproofCompilerConfig),
    senv_preservedStatement cfg := by
  intro cfg prog tprog hm
  letI : Linker CompCert4Lean.Backend.RTL.fundef :=
    Linker_fundef CompCert4Lean.Backend.RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker CompCert4Lean.Backend.RTL.program :=
    Linker_prog CompCert4Lean.Backend.RTL.fundef Unit
  have hg := cse_globalenv_match
    (fun (cu : CompCert4Lean.Backend.RTL.program) f tf =>
      CSE.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu)
        (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f = .OK tf)
    (fun x y : Unit => x = y) prog prog tprog hm
  unfold Senv.equiv
  constructor
  · intro id
    change Genv.find_symbol (Genv.globalenv tprog) id =
      Genv.find_symbol (Genv.globalenv prog) id
    exact hg.mge_symb id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv tprog) id =
      Genv.public_symbol (Genv.globalenv prog) id
    have ht : (Genv.globalenv tprog).genv_public = tprog.prog_public := by
      unfold Genv.globalenv
      exact cse_add_globals_public _ _
    have hp : (Genv.globalenv prog).genv_public = prog.prog_public := by
      unfold Genv.globalenv
      exact cse_add_globals_public _ _
    unfold Genv.public_symbol
    rw [show Genv.find_symbol (Genv.globalenv tprog) id =
      Genv.find_symbol (Genv.globalenv prog) id by
      simpa [Genv.find_symbol] using hg.mge_symb id]
    unfold match_prog CompCert4Lean.Common.Linking.match_program
      CompCert4Lean.Common.Linking.match_program_gen at hm
    rw [ht, hp, hm.2.2]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv tprog) b =
      Genv.block_is_volatile (Genv.globalenv prog) b
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    cases h1 : PTree.get b (Genv.globalenv prog).genv_defs with
    | none =>
        cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
        | none => rfl
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
    | some gd1 =>
        cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
        | none =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd with
            | some x y hrel =>
                cases hrel with
                | match_globdef_fun ctx' f1 f2 horder htrans => rfl
                | match_globdef_var v1 v2 hvar =>
                    cases hvar
                    rfl

end CompCert4Lean.Backend.CSEproof
