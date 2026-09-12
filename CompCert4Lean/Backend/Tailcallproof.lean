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

namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Backend.Tailcall
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private theorem is_move_operation_shape {A : Type} (op : operation)
    (args : List A) (a : A)
    (h : is_move_operation op args = some a) :
    op = Omove ∧ args = [a] := by
  cases op with
  | Omove =>
      cases args with
      | nil => simp [is_move_operation] at h
      | cons x xs =>
          cases xs with
          | nil => simpa [is_move_operation] using h
          | cons y ys => simp [is_move_operation] at h
  | _ => simp [is_move_operation] at h

theorem return_measure_bounds : return_measure_boundsStatement := by
  intro c pc
  unfold return_measure
  have h : ∀ n (pc : node), return_measure_rec n c pc ≤ n := by
    intro n
    induction n with
    | zero => intro pc; simp [return_measure_rec]
    | succ n ih =>
        intro pc
        cases hget : PTree.get pc c with
        | none => simp [return_measure_rec, hget]
        | some i =>
            cases i with
            | Inop s =>
                simp [return_measure_rec, hget]
                exact ih s
            | Iop op args dst s =>
                simp [return_measure_rec, hget]
                exact ih s
            | Iload chunk addr args dst s => simp [return_measure_rec, hget]
            | Istore chunk addr args src s => simp [return_measure_rec, hget]
            | Icall sig ros args res s => simp [return_measure_rec, hget]
            | Itailcall sig ros args => simp [return_measure_rec, hget]
            | Ibuiltin ef args res s => simp [return_measure_rec, hget]
            | Icond cond args ifso ifnot => simp [return_measure_rec, hget]
            | Ijumptable arg tbl => simp [return_measure_rec, hget]
            | Ireturn ores => simp [return_measure_rec, hget]
  exact h niter pc

theorem is_return_measure_rec : is_return_measure_recStatement := by
  intro f n
  induction n with
  | zero =>
      intro n' pc r h _
      simp [CompCert4Lean.Backend.Tailcall.is_return] at h
  | succ n ih =>
      intro n' pc r h hle
      cases n' with
      | zero => omega
      | succ n' =>
          cases hget : PTree.get pc f.fn_code with
          | none => simp [CompCert4Lean.Backend.Tailcall.is_return,
              return_measure_rec, hget] at h ⊢
          | some i =>
              cases i with
              | Inop s =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return,
                    return_measure_rec, hget] at h ⊢
                  exact ih n' s r h (by omega)
              | Iop op args dst s =>
                  cases hm : is_move_operation op args with
                  | none =>
                      simp [CompCert4Lean.Backend.Tailcall.is_return,
                        return_measure_rec, hget, hm] at h
                  | some src =>
                      by_cases heq : r = src
                      · simp [CompCert4Lean.Backend.Tailcall.is_return,
                          return_measure_rec, hget, hm, heq] at h ⊢
                        exact ih n' s dst h (by omega)
                      · simp [CompCert4Lean.Backend.Tailcall.is_return,
                          return_measure_rec, hget, hm, heq] at h
              | Iload chunk addr args dst s =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return,
                    return_measure_rec, hget] at h ⊢
              | Istore chunk addr args src s =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return,
                    return_measure_rec, hget] at h ⊢
              | Icall sig ros args res s =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return,
                    return_measure_rec, hget] at h ⊢
              | Itailcall sig ros args =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return,
                    return_measure_rec, hget] at h ⊢
              | Ibuiltin ef args res s =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return,
                    return_measure_rec, hget] at h ⊢
              | Icond cond args ifso ifnot =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return,
                    return_measure_rec, hget] at h ⊢
              | Ijumptable arg tbl =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return,
                    return_measure_rec, hget] at h ⊢
              | Ireturn ores =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return,
                    return_measure_rec, hget] at h ⊢

theorem is_return_charact : is_return_charactStatement := by
  intro f n
  induction n with
  | zero =>
      intro pc r h _
      simp [CompCert4Lean.Backend.Tailcall.is_return] at h
  | succ n ih =>
      intro pc r h hle
      cases hget : PTree.get pc f.fn_code with
      | none =>
          simp [CompCert4Lean.Backend.Tailcall.is_return, hget] at h
      | some i =>
          cases i with
          | Inop s =>
              have hparent := h
              simp [CompCert4Lean.Backend.Tailcall.is_return, hget] at h
              apply is_return_nop (f := f) hget
              · exact ih s r h (by omega)
              · unfold return_measure
                have ep := is_return_measure_rec f (n + 1) niter pc r hparent (by omega)
                have es := is_return_measure_rec f n niter s r h (by omega)
                rw [← ep, ← es]
                simp [return_measure_rec, hget]
          | Iop op args dst s =>
              have hparent := h
              cases hm : is_move_operation op args with
              | none =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return, hget, hm] at h
              | some src =>
                  by_cases heq : r = src
                  · simp [CompCert4Lean.Backend.Tailcall.is_return, hget, hm, heq] at h
                    have hshape := is_move_operation_shape op args src hm
                    rcases hshape with ⟨rfl, rfl⟩
                    subst r
                    apply is_return_move (f := f) hget
                    · exact ih s dst h (by omega)
                    · unfold return_measure
                      have ep := is_return_measure_rec f (n + 1) niter pc src hparent (by omega)
                      have es := is_return_measure_rec f n niter s dst h (by omega)
                      rw [← ep, ← es]
                      simp [return_measure_rec, hget]
                  · simp [CompCert4Lean.Backend.Tailcall.is_return, hget, hm, heq] at h
          | Iload chunk addr args dst s =>
              simp [CompCert4Lean.Backend.Tailcall.is_return, hget] at h
          | Istore chunk addr args src s =>
              simp [CompCert4Lean.Backend.Tailcall.is_return, hget] at h
          | Icall sig ros args res s =>
              simp [CompCert4Lean.Backend.Tailcall.is_return, hget] at h
          | Itailcall sig ros args =>
              simp [CompCert4Lean.Backend.Tailcall.is_return, hget] at h
          | Ibuiltin ef args res s =>
              simp [CompCert4Lean.Backend.Tailcall.is_return, hget] at h
          | Icond cond args ifso ifnot =>
              simp [CompCert4Lean.Backend.Tailcall.is_return, hget] at h
          | Ijumptable arg tbl =>
              simp [CompCert4Lean.Backend.Tailcall.is_return, hget] at h
          | Ireturn ores =>
              cases ores with
              | none => exact is_return_none (f := f) hget
              | some rr =>
                  simp [CompCert4Lean.Backend.Tailcall.is_return, hget] at h
                  subst rr
                  exact is_return_some (f := f) hget

theorem transf_instr_charact : transf_instr_charactStatement := by
  intro cfg f pc instr hstack
  cases instr with
  | Icall sig ros args res s =>
      simp only [CompCert4Lean.Backend.Tailcall.transf_instr]
      split
      · rename_i hb
        have hparts :
            is_return niter f s res = true ∧
              CompCert4Lean.Backend.Conventions.tailcall_is_possible cfg sig = true ∧
              sig.sig_res = f.fn_sig.sig_res := by
          rcases (CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.andb_true_iff _ _).mp hb
            with ⟨hab, hc⟩
          rcases (CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.andb_true_iff _ _).mp hab
            with ⟨ha, hb⟩
          exact ⟨ha, hb, (decide_eq_true_eq.mp hc)⟩
        exact transf_instr_tailcall hstack
          (is_return_charact f niter s res hparts.1 (by omega))
      · exact @transf_instr_spec.unchanged f (Icall sig ros args res s)
  | _ =>
      simp [CompCert4Lean.Backend.Tailcall.transf_instr]
      exact @transf_instr_spec.unchanged f _

end CompCert4Lean.Backend.Tailcallproof

namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values

theorem regs_lessdef_init_regs : regs_lessdef_init_regsStatement := by
  intro params
  induction params with
  | nil =>
      intro vl vl' h
      cases vl with
      | nil =>
          cases vl' with
          | nil =>
              intro r
              change Val.lessdef (Regmap.get r (Regmap.init Vundef))
                (Regmap.get r (Regmap.init Vundef))
              rw [Regmap.gi_proof]
              exact Val.lessdef.lessdef_refl _
          | cons v' vs' => cases h
      | cons v vs =>
          cases vl' with
          | nil => cases h
          | cons v' vs' =>
              intro r
              change Val.lessdef (Regmap.get r (Regmap.init Vundef))
                (Regmap.get r (Regmap.init Vundef))
              rw [Regmap.gi_proof]
              exact Val.lessdef.lessdef_refl _
  | cons r params ih =>
      intro vl vl' h
      cases vl with
      | nil =>
          cases vl' with
          | nil =>
              intro r0
              change Val.lessdef (Regmap.get r0 (Regmap.init Vundef))
                (Regmap.get r0 (Regmap.init Vundef))
              rw [Regmap.gi_proof]
              exact Val.lessdef.lessdef_refl _
          | cons v' vs' =>
              cases h
      | cons v vs =>
          cases vl' with
          | nil =>
              cases h
          | cons v' vs' =>
              cases h with
              | lessdef_list_cons v₁ v₂ vl₁ vl₂ hv htail =>
                  change regs_lessdef
                    (Regmap.set r v (init_regs vs params))
                    (Regmap.set r v' (init_regs vs' params))
                  exact set_reg_lessdef r v v'
                    (init_regs vs params) (init_regs vs' params)
                    hv (ih vs vs' htail)

end CompCert4Lean.Backend.Tailcallproof
namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem tailcall_symbol_add_global
    (ge1 ge2 : Genv.t RTL.fundef Unit) (id : ident)
    (hm : ∀ id', PTree.get id' ge2.genv_symb =
      PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', PTree.get id'
      (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id'
      (PTree.set id ge1.genv_next ge1.genv_symb) := by
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

private theorem tailcall_match_genvs_add_global
    (R : globdef RTL.fundef Unit → globdef RTL.fundef Unit → Prop)
    (ge1 ge2 : Genv.t RTL.fundef Unit) (id : ident)
    (g1 g2 : globdef RTL.fundef Unit)
    (hm : Genv.match_genvs R ge1 ge2) (hg : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · exact tailcall_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @PTree.getSet_equation
      (globdef RTL.fundef Unit) b ge1.genv_next g1 ge1.genv_defs
    have h2 := @PTree.getSet_equation
      (globdef RTL.fundef Unit) b ge2.genv_next g2 ge2.genv_defs
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

private theorem tailcall_match_genvs_add_globals
    (R : globdef RTL.fundef Unit → globdef RTL.fundef Unit → Prop)
    (xs ys : List (ident × globdef RTL.fundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 ge2 : Genv.t RTL.fundef Unit) (hm : Genv.match_genvs R ge1 ge2) :
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
      simpa using (tailcall_match_genvs_add_global R ge1 ge2 aid ag bg hm hab)

private theorem tailcall_globalenvs_match
    (cfg : CompilerConfig)
    (prog tprog : RTL.program)
    (hm : match_prog cfg prog tprog) :
    Genv.match_genvs
      (@match_globdef RTL.program RTL.fundef Unit RTL.fundef Unit
        (@Linker_prog RTL.fundef Unit (Linker_fundef RTL.function) Linker_unit)
        (fun (_ : RTL.program) f tf =>
          tf = CompCert4Lean.Backend.Tailcall.transf_fundef cfg f)
        (fun _ _ : Unit => True) prog)
      (Genv.globalenv prog) (Genv.globalenv tprog) := by
  letI : Linker RTL.fundef := Linker_fundef RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker RTL.program := Linker_prog RTL.fundef Unit
  let R : globdef RTL.fundef Unit → globdef RTL.fundef Unit → Prop :=
    match_globdef
      (fun (_ : RTL.program) f tf =>
        tf = CompCert4Lean.Backend.Tailcall.transf_fundef cfg f)
      (fun _ _ : Unit => True) prog
  have hempty : Genv.match_genvs R
      (Genv.empty_genv RTL.fundef Unit prog.prog_public)
      (Genv.empty_genv RTL.fundef Unit tprog.prog_public) := by
    constructor
    · rfl
    · intro id'
      rfl
    · intro b
      exact option_rel.none R
  have hlist_of : ∀ (xs ys : List (ident × globdef RTL.fundef Unit)),
      list_forall2 (match_ident_globdef
        (fun (_ : RTL.program) f tf =>
          tf = CompCert4Lean.Backend.Tailcall.transf_fundef cfg f)
        (fun x y : Unit => x = y) prog) xs ys →
      list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys := by
    intro xs ys h
    induction h with
    | nil => exact list_forall2.nil _
    | @cons a xs b ys hab htail ih =>
        apply list_forall2.cons
        · constructor
          · exact hab.1
          · simpa [R] using hab.2
        · exact ih
  unfold match_prog match_program match_program_gen at hm
  have hlist := hlist_of prog.prog_defs tprog.prog_defs hm.1
  simpa [Genv.globalenv, R] using
    (tailcall_match_genvs_add_globals R prog.prog_defs tprog.prog_defs hlist
      (Genv.empty_genv RTL.fundef Unit prog.prog_public)
      (Genv.empty_genv RTL.fundef Unit tprog.prog_public) hempty)

private theorem tailcall_function_ptr_translated
    (cfg : CompilerConfig) (prog tprog : RTL.program)
    (hm : match_prog cfg prog tprog)
    (b : block) (f : RTL.fundef)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) b = some f) :
    Genv.find_funct_ptr (Genv.globalenv tprog) b =
      some (CompCert4Lean.Backend.Tailcall.transf_fundef cfg f) := by
  have hg := tailcall_globalenvs_match cfg prog tprog hm
  unfold Genv.find_funct_ptr Genv.find_def at hfind ⊢
  cases h1 : PTree.get b (Genv.globalenv prog).genv_defs with
  | none => simp [h1] at hfind
  | some gd1 =>
      cases gd1 with
      | Gfun f1 =>
          have hf : f1 = f := by simpa [h1] using hfind
          subst f1
          cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
          | none =>
              have hd := hg.mge_defs b
              simp [h1, h2] at hd
              cases hd
          | some gd2 =>
              cases gd2 with
              | Gfun f2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel =>
                      cases hrel with
                      | match_globdef_fun ctx' f1 f2 horder htrans =>
                          simpa using htrans
              | Gvar v2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel => cases hrel
      | Gvar v1 => simp [h1] at hfind

theorem functions_translated : functions_translatedStatement := by
  intro cfg prog tprog hm v f hfind
  unfold Genv.find_funct at hfind ⊢
  cases v with
  | Vundef => simp at hfind
  | Vint n => simp at hfind
  | Vlong n => simp at hfind
  | Vfloat n => simp at hfind
  | Vsingle n => simp at hfind
  | Vptr b ofs =>
      cases hzero : Ptrofs.eq ofs Ptrofs.zero with
      | false => simp [hzero] at hfind
      | true =>
          simp [hzero] at hfind ⊢
          exact tailcall_function_ptr_translated cfg prog tprog hm b f hfind

end CompCert4Lean.Backend.Tailcallproof

namespace CompCert4Lean.Backend.Tailcallproof
open CompCert4Lean.Backend.Tailcall
open CompCert4Lean.Common.AST
theorem sig_preserved : sig_preservedStatement := by
  intro cfg f
  cases f with
  | Internal fn =>
      simp only [CompCert4Lean.Backend.Tailcall.transf_fundef, CompCert4Lean.Common.AST.transf_fundef,
        CompCert4Lean.Backend.RTL.funsig, CompCert4Lean.Backend.Tailcall.transf_function,
        CompCert4Lean.Backend.RTL.transf_function]
      split <;> rfl
  | External ef => rfl
theorem stacksize_preserved : stacksize_preservedStatement := by
  intro cfg f
  unfold CompCert4Lean.Backend.Tailcall.transf_function
  split <;> rfl
end CompCert4Lean.Backend.Tailcallproof

namespace CompCert4Lean.Backend.Tailcallproof

theorem funct_ptr_translated : funct_ptr_translatedStatement := by
  intro cfg prog tprog hm b f hfind
  exact tailcall_function_ptr_translated cfg prog tprog hm b f hfind

end CompCert4Lean.Backend.Tailcallproof
