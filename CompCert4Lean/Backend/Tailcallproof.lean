import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Tailcall

/-!
# Correctness interface for tail-call recognition

Definition-bearing translation of the required surface of CompCert's
`backend/Tailcallproof.v`. Proof obligations assigned to later proof migration
are represented by transparent proposition descriptors.
-/

namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Tailcall
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig

/-! ## Syntactic properties of the transformation -/

def return_measure_rec : Nat → code → node → Nat
  | 0, _, _ => 0
  | n + 1, c, pc =>
      match PTree.get pc c with
      | some (Inop s) => Nat.succ (return_measure_rec n c s)
      | some (Iop _ _ _ s) => Nat.succ (return_measure_rec n c s)
      | _ => 0

def return_measure (c : code) (pc : node) : Nat :=
  return_measure_rec niter c pc

inductive is_return_spec (f : function) : node → reg → Prop where
  | is_return_none {pc r} :
      PTree.get pc f.fn_code = some (Ireturn none) →
      is_return_spec f pc r
  | is_return_some {pc r} :
      PTree.get pc f.fn_code = some (Ireturn (some r)) →
      is_return_spec f pc r
  | is_return_nop {pc r s} :
      PTree.get pc f.fn_code = some (Inop s) →
      is_return_spec f s r →
      return_measure f.fn_code s < return_measure f.fn_code pc →
      is_return_spec f pc r
  | is_return_move {pc r r' s} :
      PTree.get pc f.fn_code = some (Iop Omove [r] r' s) →
      is_return_spec f s r' →
      return_measure f.fn_code s < return_measure f.fn_code pc →
      is_return_spec f pc r

export is_return_spec
  (is_return_none is_return_some is_return_nop is_return_move)

inductive transf_instr_spec (f : function) : instruction → instruction → Prop where
  | transf_instr_tailcall {sig ros args res s} :
      f.fn_stacksize = .Z0 →
      is_return_spec f s res →
      transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
  | unchanged {i} : transf_instr_spec f i i

export transf_instr_spec (transf_instr_tailcall)

/-! The kernel carrier keeps Lean's generated constructor namespaced.  This
source-facing alias restores the pinned Rocq application binder modes for the
default case without changing the relation or its existing constructor. -/
abbrev transf_instr_default (f : function) (i : instruction) :
    transf_instr_spec f i i :=
  @transf_instr_spec.unchanged f i

/-! ## Program and state matching -/

def match_prog (cfg : CompilerConfig) (p tp : program) : Prop :=
  @CompCert4Lean.Common.Linking.match_program
    fundef Unit fundef Unit
    (CompCert4Lean.Common.Linking.Linker_fundef function)
    CompCert4Lean.Common.Linking.Linker_unit
    (fun _ f tf => tf = transf_fundef cfg f) Eq p tp

private abbrev sourceGenv (p : program) : genv := Genv.globalenv p
private abbrev targetGenv (p : program) : genv := Genv.globalenv p

inductive match_stackframes (cfg : CompilerConfig) :
    List stackframe → List stackframe → Prop where
  | match_stackframes_nil : match_stackframes cfg [] []
  | match_stackframes_normal
      (stk stk' : List stackframe) (res : reg) (sp : block) (pc : node)
      (rs rs' : regset) (f : function)
      (hstack : match_stackframes cfg stk stk')
      (hrld : regs_lessdef rs rs') :
      match_stackframes cfg
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res (transf_function cfg f) (Vptr sp Ptrofs.zero) pc rs' :: stk')
  | match_stackframes_tail
      (stk stk' : List stackframe) (res : reg) (sp : block) (pc : node)
      (rs : regset) (f : function)
      (hstack : match_stackframes cfg stk stk')
      (hreturn : is_return_spec f pc res)
      (hstacksize : f.fn_stacksize = .Z0) :
      match_stackframes cfg
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk) stk'

export match_stackframes
  (match_stackframes_nil match_stackframes_normal match_stackframes_tail)

inductive match_states (cfg : CompilerConfig) : state → state → Prop where
  | normal {s sp pc rs m s' rs' m' f} :
      match_stackframes cfg s s' →
      regs_lessdef rs rs' →
      Mem.extends m m' →
      match_states cfg
        (State s f (Vptr sp Ptrofs.zero) pc rs m)
        (State s' (transf_function cfg f) (Vptr sp Ptrofs.zero) pc rs' m')
  | call {s f args m s' args' m'} :
      match_stackframes cfg s s' →
      Val.lessdef_list args args' →
      Mem.extends m m' →
      match_states cfg
        (Callstate s f args m)
        (Callstate s' (transf_fundef cfg f) args' m')
  | return {s v m s' v' m'} :
      match_stackframes cfg s s' →
      Val.lessdef v v' →
      Mem.extends m m' →
      match_states cfg (Returnstate s v m) (Returnstate s' v' m')
  | interm {s sp pc rs m s' m' f r v'} :
      match_stackframes cfg s s' →
      Mem.extends m m' →
      is_return_spec f pc r →
      f.fn_stacksize = .Z0 →
      Val.lessdef (Regmap.get r rs) v' →
      match_states cfg
        (State s f (Vptr sp Ptrofs.zero) pc rs m)
        (Returnstate s' v' m')

/-! The source constructors are exposed as flat aliases with Rocq's explicit
state and proof binders.  The compiler configuration remains an inferred
parameter introduced by the authenticated downstream configuration seam. -/
abbrev match_states_normal
    {cfg : CompilerConfig}
    (s : List stackframe) (sp : block) (pc : node)
    (rs : regset) (m : Mem.mem) (s' : List stackframe)
    (rs' : regset) (m' : Mem.mem) (f : function)
    (hstack : match_stackframes cfg s s')
    (hrld : regs_lessdef rs rs')
    (hmld : Mem.extends m m') :
    match_states cfg
      (State s f (Vptr sp Ptrofs.zero) pc rs m)
      (State s' (transf_function cfg f) (Vptr sp Ptrofs.zero) pc rs' m') :=
  @match_states.normal cfg s sp pc rs m s' rs' m' f hstack hrld hmld

abbrev match_states_call
    {cfg : CompilerConfig}
    (s : List stackframe) (f : fundef) (args : List val)
    (m : Mem.mem) (s' : List stackframe) (args' : List val)
    (m' : Mem.mem)
    (hstack : match_stackframes cfg s s')
    (hargs : Val.lessdef_list args args')
    (hmld : Mem.extends m m') :
    match_states cfg (Callstate s f args m)
      (Callstate s' (transf_fundef cfg f) args' m') :=
  @match_states.call cfg s f args m s' args' m' hstack hargs hmld

abbrev match_states_return
    {cfg : CompilerConfig}
    (s : List stackframe) (v : val) (m : Mem.mem)
    (s' : List stackframe) (v' : val) (m' : Mem.mem)
    (hstack : match_stackframes cfg s s')
    (hval : Val.lessdef v v')
    (hmld : Mem.extends m m') :
    match_states cfg (Returnstate s v m) (Returnstate s' v' m') :=
  @match_states.return cfg s v m s' v' m' hstack hval hmld

abbrev match_states_interm
    {cfg : CompilerConfig}
    (s : List stackframe) (sp : block) (pc : node)
    (rs : regset) (m : Mem.mem) (s' : List stackframe)
    (m' : Mem.mem) (f : function) (r : reg) (v' : val)
    (hstack : match_stackframes cfg s s')
    (hmld : Mem.extends m m')
    (hreturn : is_return_spec f pc r)
    (hstacksize : f.fn_stacksize = .Z0)
    (hval : Val.lessdef (Regmap.get r rs) v') :
    match_states cfg
      (State s f (Vptr sp Ptrofs.zero) pc rs m)
      (Returnstate s' v' m') :=
  @match_states.interm cfg s sp pc rs m s' m' f r v'
    hstack hmld hreturn hstacksize hval

def measure : state → Nat
  | State s f _ pc _ _ =>
      s.length * (niter + 2) + return_measure f.fn_code pc + 1
  | Callstate _ _ _ _ => 0
  | Returnstate s _ _ => s.length * (niter + 2)

/-! ## Exact statement descriptors for later proof migration -/

def return_measure_boundsStatement : Prop :=
  ∀ (f : code) (pc : node), return_measure f pc ≤ niter

def is_return_measure_recStatement : Prop :=
  ∀ (f : function) (n n' : Nat) (pc : node) (r : reg),
    is_return n f pc r = true → n ≤ n' →
    return_measure_rec n f.fn_code pc = return_measure_rec n' f.fn_code pc

def is_return_charactStatement : Prop :=
  ∀ (f : function) (n : Nat) (pc : node) (rret : reg),
    is_return n f pc rret = true → n ≤ niter →
    is_return_spec f pc rret

def transf_instr_charactStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (pc : node) (instr : instruction),
    f.fn_stacksize = .Z0 →
    transf_instr_spec f instr (transf_instr cfg f pc instr)

def transf_instr_lookupStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (pc : node) (i : instruction),
    PTree.get pc f.fn_code = some i →
    ∃ i',
      PTree.get pc (transf_function cfg f).fn_code = some i' ∧
      transf_instr_spec f i i'

def regs_lessdef_init_regsStatement : Prop :=
  ∀ (params : List reg) (vl vl' : List val),
    Val.lessdef_list vl vl' →
    regs_lessdef (init_regs vl params) (init_regs vl' params)

def transf_program_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p : program),
    match_prog cfg p (transf_program cfg p)

def symbols_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ s : ident,
      Genv.find_symbol (targetGenv tprog) s =
        Genv.find_symbol (sourceGenv prog) s

def functions_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ (v : val) (f : fundef),
      Genv.find_funct (sourceGenv prog) v = some f →
      Genv.find_funct (targetGenv tprog) v = some (transf_fundef cfg f)

def funct_ptr_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ (b : block) (f : fundef),
      Genv.find_funct_ptr (sourceGenv prog) b = some f →
      Genv.find_funct_ptr (targetGenv tprog) b = some (transf_fundef cfg f)

def senv_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    Senv.equiv
      (Genv.to_senv (sourceGenv prog))
      (Genv.to_senv (targetGenv tprog))

def sig_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : fundef),
    funsig (transf_fundef cfg f) = funsig f

def stacksize_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function),
    (transf_function cfg f).fn_stacksize = f.fn_stacksize

def find_function_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ (ros : Sum reg ident) (rs rs' : regset) (f : fundef),
      find_function (sourceGenv prog) ros rs = some f →
      regs_lessdef rs rs' →
      find_function (targetGenv tprog) ros rs' = some (transf_fundef cfg f)

def transf_step_correctStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ (s1 : state) (t : trace) (s2 : state),
      step (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (sourceGenv prog) s1 t s2 →
      ∀ s1', match_states cfg s1 s1' →
        (∃ s2',
          step (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            xi (targetGenv tprog) s1' t s2' ∧
          match_states cfg s2 s2') ∨
        (measure s2 < measure s1 ∧ t = E0 ∧ match_states cfg s2 s1')

def transf_initial_statesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ st1, initial_state prog st1 →
      ∃ st2, initial_state tprog st2 ∧ match_states cfg st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
    ∀ st1 st2 r,
      match_states cfg st1 st2 → final_state st1 r → final_state st2 r

def transf_program_correctStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog cfg prog tprog →
    forward_simulation
      (semantics (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog)
      (semantics (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tprog)

end CompCert4Lean.Backend.Tailcallproof

namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Backend.Tailcall
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem transf_program_match : transf_program_matchStatement := by
  letI : Linker RTL.fundef := Linker_fundef RTL.function
  letI : Linker RTL.program := Linker_prog RTL.fundef Unit
  intro cfg p
  unfold match_prog CompCert4Lean.Backend.Tailcall.transf_program
    CompCert4Lean.Common.AST.transform_program
  constructor
  · induction p.prog_defs with
    | nil => exact list_forall2.nil _
    | cons hd tl ih =>
        cases hd with
        | mk id gd =>
            cases gd with
            | Gfun f =>
                change list_forall2 _
                  ((id, Gfun f) :: tl)
                  ((id, Gfun (CompCert4Lean.Backend.Tailcall.transf_fundef cfg f)) ::
                    List.map (transform_program_globdef
                      (CompCert4Lean.Backend.Tailcall.transf_fundef cfg)) tl)
                apply list_forall2.cons
                · constructor
                  · rfl
                  · apply match_globdef.match_globdef_fun (ctx' := p)
                    · exact linkorder_refl _
                    · rfl
                · exact ih
            | Gvar v =>
                change list_forall2 _
                  ((id, Gvar v) :: tl)
                  ((id, Gvar v) ::
                    List.map (transform_program_globdef
                      (CompCert4Lean.Backend.Tailcall.transf_fundef cfg)) tl)
                apply list_forall2.cons
                · constructor
                  · rfl
                  · apply match_globdef.match_globdef_var
                    exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                · exact ih
  · exact ⟨rfl, rfl⟩

end CompCert4Lean.Backend.Tailcallproof
