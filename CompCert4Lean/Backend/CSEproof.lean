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
