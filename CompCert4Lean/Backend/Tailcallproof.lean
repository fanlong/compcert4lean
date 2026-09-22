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

private theorem tailcall_add_globals_public {F V : Type}
    (ge : Genv.t F V) (gl : List (ident × globdef F V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x xs ih =>
      simp only [Genv.add_globals, List.foldl]
      exact ih (Genv.add_global ge x)

theorem senv_preserved : senv_preservedStatement := by
  intro cfg prog tprog hm
  unfold Senv.equiv
  have hg := tailcall_globalenvs_match cfg prog tprog hm
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
      exact tailcall_add_globals_public _ _
    have hp : (Genv.globalenv prog).genv_public = prog.prog_public := by
      unfold Genv.globalenv
      exact tailcall_add_globals_public _ _
    unfold Genv.public_symbol
    rw [show Genv.find_symbol (Genv.globalenv tprog) id =
      Genv.find_symbol (Genv.globalenv prog) id by
      simpa [Genv.find_symbol] using hg.mge_symb id]
    unfold match_prog match_program match_program_gen at hm
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

end CompCert4Lean.Backend.Tailcallproof

namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private def tailcallPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem tailcall_wordcore_add_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.add x y).val =
      (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (tailcallPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem tailcall_wordcore_zero_val (bits : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.zero bits).val = 0 := by
  unfold CompCert4Lean.Lib.Integers.WordCore.zero
  run_tac
    let lctx ← getLCtx
    let bF := (lctx.findFromUserName? `bits).get!
    let e ← mkAppM
      (tailcallPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")
      #[mkFVar bF.fvarId,
        mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0]
    closeMainGoal Name.anonymous e

private theorem tailcall_wordcore_val_lt {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    x.val < 2 ^ bits := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (tailcallPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e

private theorem tailcall_ptrofs_add_zero (x : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add x
        CompCert4Lean.Lib.Integers.Ptrofs.zero = x := by
  change CompCert4Lean.Lib.Integers.WordCore.add x
    (CompCert4Lean.Lib.Integers.WordCore.zero
      CompCert4Lean.Lib.Integers.Ptrofs.wordsize) = x
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [tailcall_wordcore_add_val, tailcall_wordcore_zero_val]
  exact Nat.mod_eq_of_lt (tailcall_wordcore_val_lt x)

private theorem tailcall_symbols_preserved
    (cfg : CompilerConfig) (prog tprog : program)
    (hm : match_prog cfg prog tprog) :
    ∀ id, Genv.find_symbol (Genv.globalenv tprog) id =
      Genv.find_symbol (Genv.globalenv prog) id := by
  intro id
  exact (tailcall_globalenvs_match cfg prog tprog hm).mge_symb id

private theorem tailcall_initial_store_init_data
    {prog tprog : program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    (m : _) (b : _) (p : Z) (i : init_data) :
    Genv.store_init_data (Genv.globalenv prog) m b p i =
      Genv.store_init_data (Genv.globalenv tprog) m b p i := by
  cases i with
  | Init_addrof symb ofs =>
      simp [Genv.store_init_data, hsymb symb]
  | _ => rfl

private theorem tailcall_initial_store_init_data_list
    {prog tprog : program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id) :
    ∀ (m : _) (b : _) (p : Z) (il : List init_data),
      Genv.store_init_data_list (Genv.globalenv prog) m b p il =
        Genv.store_init_data_list (Genv.globalenv tprog) m b p il := by
  intro m b p il
  induction il generalizing m b p with
  | nil => rfl
  | cons i rest ih =>
      simp only [Genv.store_init_data_list]
      rw [tailcall_initial_store_init_data hsymb]
      cases h : Genv.store_init_data (Genv.globalenv tprog) m b p i with
      | none => simp [h]
      | some m' =>
          simp only [h]
          exact ih m' b (ZArith.BinInt.Z.add p (init_data_size i))

private theorem tailcall_initial_alloc_global
    (cfg : CompilerConfig)
    [Linker program]
    {prog tprog : program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    {id : ident} {gd tg : globdef fundef Unit}
    (hgd : match_globdef
      (fun (_ : RTL.program) f tf =>
        tf = CompCert4Lean.Backend.Tailcall.transf_fundef cfg f)
      (fun x y : Unit => x = y) prog gd tg)
    (m : _) :
    Genv.alloc_global (Genv.globalenv prog) m (id, gd) =
      Genv.alloc_global (Genv.globalenv tprog) m (id, tg) := by
  cases hgd with
  | match_globdef_fun ctx' f1 f2 horder htrans => rfl
  | match_globdef_var v1 v2 hvar =>
      cases hvar with
      | match_globvar_intro info1 info2 init ro vol hinfo =>
          cases hinfo
          simp only [Genv.alloc_global, CompCert4Lean.Common.Values.block]
          congr 1
          funext m2
          congr 1
          exact tailcall_initial_store_init_data_list hsymb _ _ _ _

private theorem tailcall_initial_alloc_globals
    (cfg : CompilerConfig)
    [Linker program]
    {prog tprog : program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    (gl tgl : List (ident × globdef fundef Unit))
    (hlist : list_forall2
      (match_ident_globdef
        (fun (_ : RTL.program) f tf =>
          tf = CompCert4Lean.Backend.Tailcall.transf_fundef cfg f)
        (fun x y : Unit => x = y) prog) gl tgl) :
    ∀ (m m' : _),
      Genv.alloc_globals (Genv.globalenv prog) m gl = some m' →
        Genv.alloc_globals (Genv.globalenv tprog) m tgl = some m' := by
  induction hlist with
  | nil =>
      intro m m' h
      simpa [Genv.alloc_globals] using h
  | cons hd thd hhd htl ih =>
      intro m m' h
      rcases hhd with ⟨hid, hgd⟩
      rcases hd with ⟨id, gd⟩
      rcases thd with ⟨tid, tgd⟩
      have halloc :
          Genv.alloc_global (Genv.globalenv prog) m (id, gd) =
            Genv.alloc_global (Genv.globalenv tprog) m (tid, tgd) := by
        change id = tid at hid
        subst tid
        exact tailcall_initial_alloc_global cfg hsymb hgd m
      simp only [Genv.alloc_globals] at h ⊢
      rw [halloc] at h
      cases ha : Genv.alloc_global (Genv.globalenv tprog) m (tid, tgd) with
      | none => simp [ha] at h
      | some m1 =>
          simp only [ha] at h ⊢
          exact ih m1 m' h

private theorem tailcall_val_inject_refl (v : val) :
    Val.inject inject_id v v := by
  cases v with
  | Vint i => exact Val.inject.inject_int _
  | Vlong i => exact Val.inject.inject_long _
  | Vfloat f => exact Val.inject.inject_float _
  | Vsingle f => exact Val.inject.inject_single _
  | Vptr b ofs =>
      apply Val.inject.inject_ptr
      · rfl
      · exact (tailcall_ptrofs_add_zero ofs).symm
  | Vundef => exact Val.inject.val_inject_undef _

private theorem tailcall_mem_extends_refl
    (m : CompCert4Lean.Common.Memory.mem) : Mem.extends m m := by
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro b1 b2 delta ofs k p hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change Mem.perm m b1 (ZArith.BinInt.Z.add ofs (.Z0 : Z)) k p
      have hzadd : ZArith.BinInt.Z.add ofs (.Z0 : Z) = ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
        rw [intOfZ_zOfInt]
        simp
      rw [hzadd]
      exact hp
    · intro b1 b2 delta chunk ofs p hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      refine ⟨.Z0, ?_⟩
      apply intOfZ_injective
      change 0 = intOfZ (ZArith.BinInt.Z.mul
        (CompCert4Lean.Common.Memdata.align_chunk chunk) (.Z0 : Z))
      change 0 = intOfZ (zOfInt (intOfZ
        (CompCert4Lean.Common.Memdata.align_chunk chunk) * 0))
      rw [intOfZ_zOfInt]
      simp
    · intro b1 ofs b2 delta hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change memval_inject inject_id
        (ZMap.get ofs (PMap.get b1 m.mem_contents))
        (ZMap.get (ZArith.BinInt.Z.add ofs (.Z0 : Z))
          (PMap.get b1 m.mem_contents))
      have hzadd : ZArith.BinInt.Z.add ofs (.Z0 : Z) = ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
        rw [intOfZ_zOfInt]
        simp
      rw [hzadd]
      cases hmv : ZMap.get ofs (PMap.get b1 m.mem_contents) with
      | Byte n => exact memval_inject.byte _ _
      | Fragment v q n =>
          exact memval_inject.fragment _ _ _ _ _ (tailcall_val_inject_refl v)
      | Undef => exact memval_inject.undef _ _
  · intro b ofs k p hp
    exact Or.inl hp

theorem transf_initial_states : transf_initial_statesStatement := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  intro cfg prog tprog hmatch st1 hinit
  cases hinit with
  | intro b f m0 hmem hsymb hfun hsig =>
      refine ⟨Callstate [] (CompCert4Lean.Backend.Tailcall.transf_fundef cfg f) [] m0, ?_, ?_⟩
      · apply initial_state.intro b
          (CompCert4Lean.Backend.Tailcall.transf_fundef cfg f) m0
        · unfold Genv.init_mem at hmem ⊢
          apply tailcall_initial_alloc_globals cfg (prog := prog) (tprog := tprog)
            (tailcall_symbols_preserved cfg prog tprog hmatch)
            prog.prog_defs tprog.prog_defs hmatch.1
            CompCert4Lean.Common.Memory.Mem.empty m0
          exact hmem
        · change Genv.find_symbol (Genv.globalenv tprog) tprog.prog_main = some b
          rw [hmatch.2.1]
          rw [tailcall_symbols_preserved cfg prog tprog hmatch prog.prog_main]
          exact hsymb
        · exact funct_ptr_translated cfg prog tprog hmatch b f hfun
        · rw [sig_preserved cfg f]
          exact hsig
      · exact match_states_call [] f [] m0 [] [] m0
          match_stackframes_nil (Val.lessdef_list.lessdef_list_nil)
          (tailcall_mem_extends_refl m0)

end CompCert4Lean.Backend.Tailcallproof

namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Backend.RTL

theorem transf_final_states : transf_final_statesStatement := by
  intro cfg prog tprog hprog st1 st2 r hmatch hfinal
  cases hfinal
  cases hmatch
  cases ‹match_stackframes cfg [] _›
  cases ‹CompCert4Lean.Common.Values.Val.lessdef
      (CompCert4Lean.Common.Values.Vint r) _›
  exact final_state.intro r _

end CompCert4Lean.Backend.Tailcallproof

namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Backend.Tailcall
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

theorem transf_instr_lookup : transf_instr_lookupStatement := by
  intro cfg f pc i h
  unfold CompCert4Lean.Backend.Tailcall.transf_function
  split
  · rename_i hcond
    dsimp [CompCert4Lean.Backend.RTL.transf_function]
    rw [@CompCert4Lean.Lib.Maps.PTree.gmap instruction instruction
      (fun p j => CompCert4Lean.Backend.Tailcall.transf_instr cfg f p j)
      (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from pc) f.fn_code]
    refine ⟨CompCert4Lean.Backend.Tailcall.transf_instr cfg f pc i, ?_, ?_⟩
    · simpa [h]
    · apply transf_instr_charact cfg f pc i
      have hparts :=
        (CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.andb_true_iff _ _).mp hcond
      have hstack : f.fn_stacksize =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z0 :=
        decide_eq_true_eq.mp hparts.1
      exact hstack
  · refine ⟨i, h, ?_⟩
    exact .unchanged

end CompCert4Lean.Backend.Tailcallproof

namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Backend.Tailcall
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking

theorem symbols_preserved : symbols_preservedStatement := by
  intro cfg prog tprog hmatch s
  unfold match_prog at hmatch
  exact @CompCert4Lean.Common.Globalenvs.Genv.find_symbol_transf
    fundef fundef Unit
    (CompCert4Lean.Common.Linking.Linker_fundef function)
    CompCert4Lean.Common.Linking.Linker_unit
    (transf_fundef cfg) prog tprog hmatch s

end CompCert4Lean.Backend.Tailcallproof

namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values

theorem find_function_translated : find_function_translatedStatement := by
  intro cfg prog tprog hmatch ros rs rs' f hfind hregs
  cases ros with
  | inl r =>
      simp only [find_function] at hfind ⊢
      have hld := hregs r
      have heq : Regmap.get r rs = Regmap.get r rs' := by
        generalize hv : Regmap.get r rs = v at hfind hld ⊢
        generalize hv' : Regmap.get r rs' = v' at hld ⊢
        cases hld with
        | lessdef_refl v => rfl
        | lessdef_undef v => simp [Genv.find_funct] at hfind
      rw [← heq]
      exact functions_translated cfg prog tprog hmatch _ f hfind
  | inr symb =>
      simp only [find_function] at hfind ⊢
      rw [symbols_preserved cfg prog tprog hmatch symb]
      cases hs : Genv.find_symbol (Genv.globalenv prog) symb with
      | none => simp [sourceGenv, hs] at hfind
      | some b =>
          simp only [sourceGenv, hs] at hfind ⊢
          exact funct_ptr_translated cfg prog tprog hmatch b f hfind

end CompCert4Lean.Backend.Tailcallproof

namespace CompCert4Lean.Backend.Tailcallproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.Tailcall
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private theorem tailcall_empty_range (offset : Z) :
    ¬ (ZArith.BinInt.Z.le .Z0 offset ∧ ZArith.BinInt.Z.lt offset .Z0) := by
  change ¬ ((0 : Int) ≤ intOfZ offset ∧ intOfZ offset < 0)
  omega

variable
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

private theorem tailcall_step_normal
    (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program)
    (programMatch : match_prog cfg prog tprog)
    (stack targetStack : List stackframe) (func : function) (pointer : block)
    (pc : node) (registers targetRegisters : regset) (memory targetMemory : mem)
    (events : trace) (next : state)
    (transition : RTL.step xi (sourceGenv prog)
      (State stack func (Vptr pointer Ptrofs.zero) pc registers memory) events next)
    (stackMatch : match_stackframes cfg stack targetStack)
    (registerMatch : regs_lessdef registers targetRegisters)
    (memoryMatch : Mem.extends memory targetMemory) :
    ∃ targetNext,
      RTL.step xi (targetGenv tprog)
        (State targetStack (Tailcall.transf_function cfg func)
          (Vptr pointer Ptrofs.zero) pc targetRegisters targetMemory) events targetNext ∧
      match_states cfg next targetNext := by
  have symbols := symbols_preserved cfg prog tprog programMatch
  cases transition with
  | exec_Inop _ _ _ _ _ _ successor lookup =>
      obtain ⟨instruction, targetLookup, specification⟩ :=
        transf_instr_lookup cfg func pc _ lookup
      cases specification
      exact ⟨_, RTL.step.exec_Inop _ _ _ _ _ _ _ targetLookup,
        .normal stackMatch registerMatch memoryMatch⟩
  | exec_Iop _ _ _ _ _ _ operation arguments result successor value lookup evaluation =>
      obtain ⟨instruction, targetLookup, specification⟩ :=
        transf_instr_lookup cfg func pc _ lookup
      cases specification
      obtain ⟨targetValue, targetEvaluation, valueMatch⟩ :=
        eval_operation_lessdef _ _ (sourceGenv prog) _ operation _ _ value _ _
          (regs_lessdef_regs _ _ registerMatch arguments) memoryMatch evaluation
      refine ⟨_, RTL.step.exec_Iop _ _ _ _ _ _ operation arguments result successor
        targetValue targetLookup ?_, .normal stackMatch
          (set_reg_lessdef _ _ _ _ _ valueMatch registerMatch) memoryMatch⟩
      rw [eval_operation_preserved _ _ _ _ (sourceGenv prog) (targetGenv tprog) symbols]
      exact targetEvaluation
  | exec_Iload _ _ _ _ _ _ chunk addressing arguments result successor address value
      lookup addressEvaluation load =>
      obtain ⟨instruction, targetLookup, specification⟩ :=
        transf_instr_lookup cfg func pc _ lookup
      cases specification
      obtain ⟨targetAddress, targetEvaluation, addressMatch⟩ :=
        eval_addressing_lessdef _ _ (sourceGenv prog) _ addressing _ _ address
          (regs_lessdef_regs _ _ registerMatch arguments) addressEvaluation
      obtain ⟨targetValue, targetLoad, valueMatch⟩ :=
        Mem.loadv_extends _ _ _ _ _ _ memoryMatch load addressMatch
      refine ⟨_, RTL.step.exec_Iload _ _ _ _ _ _ chunk addressing arguments result
        successor targetAddress targetValue targetLookup ?_ targetLoad,
        .normal stackMatch (set_reg_lessdef _ _ _ _ _ valueMatch registerMatch) memoryMatch⟩
      rw [eval_addressing_preserved _ _ _ _ (sourceGenv prog) (targetGenv tprog) symbols]
      exact targetEvaluation
  | exec_Istore _ _ _ _ _ _ chunk addressing arguments source successor address nextMemory
      lookup addressEvaluation store =>
      obtain ⟨instruction, targetLookup, specification⟩ :=
        transf_instr_lookup cfg func pc _ lookup
      cases specification
      obtain ⟨targetAddress, targetEvaluation, addressMatch⟩ :=
        eval_addressing_lessdef _ _ (sourceGenv prog) _ addressing _ _ address
          (regs_lessdef_regs _ _ registerMatch arguments) addressEvaluation
      obtain ⟨targetNextMemory, targetStore, nextMemoryMatch⟩ :=
        Mem.storev_extends _ _ _ _ _ _ _ _ memoryMatch store addressMatch (registerMatch source)
      refine ⟨_, RTL.step.exec_Istore _ _ _ _ _ _ chunk addressing arguments source
        successor targetAddress targetNextMemory targetLookup ?_ targetStore,
        .normal stackMatch registerMatch nextMemoryMatch⟩
      rw [eval_addressing_preserved _ _ _ _ (sourceGenv prog) (targetGenv tprog) symbols]
      exact targetEvaluation
  | exec_Icall _ _ _ _ _ _ signature callee arguments result successor definition
      lookup find signatureMatch =>
      have targetFind := find_function_translated cfg prog tprog programMatch
        callee registers targetRegisters definition find registerMatch
      have targetSignature := (sig_preserved cfg definition).trans signatureMatch
      obtain ⟨instruction, targetLookup, specification⟩ :=
        transf_instr_lookup cfg func pc _ lookup
      cases specification with
      | transf_instr_tailcall emptyStack returnSequence =>
          obtain ⟨freedMemory, free⟩ := Mem.range_perm_free targetMemory pointer .Z0 .Z0
            (by intro offset range; exact (tailcall_empty_range offset range).elim)
          have nextMemoryMatch : Mem.extends memory freedMemory :=
            Mem.free_right_extends _ _ _ _ _ _ memoryMatch free
              (by intro offset kind permission accessible range
                  exact tailcall_empty_range offset range)
          refine ⟨_, RTL.step.exec_Itailcall _ _ _ _ _ _ signature callee arguments
            (Tailcall.transf_fundef cfg definition) freedMemory targetLookup targetFind
            targetSignature ?_, .call
              (.match_stackframes_tail _ _ _ _ _ _ _ stackMatch returnSequence emptyStack)
              (regs_lessdef_regs _ _ registerMatch arguments) nextMemoryMatch⟩
          simpa only [stacksize_preserved cfg func, emptyStack] using free
      | unchanged =>
          exact ⟨_, RTL.step.exec_Icall _ _ _ _ _ _ signature callee arguments result
            successor (Tailcall.transf_fundef cfg definition) targetLookup targetFind targetSignature,
            .call (.match_stackframes_normal _ _ _ _ _ _ _ _ stackMatch registerMatch)
              (regs_lessdef_regs _ _ registerMatch arguments) memoryMatch⟩
  | exec_Itailcall _ _ _ _ _ _ signature callee arguments definition nextMemory
      lookup find signatureMatch free =>
      obtain ⟨instruction, targetLookup, specification⟩ :=
        transf_instr_lookup cfg func pc _ lookup
      cases specification
      obtain ⟨targetNextMemory, targetFree, nextMemoryMatch⟩ :=
        Mem.free_parallel_extends _ _ _ _ _ _ memoryMatch free
      refine ⟨_, RTL.step.exec_Itailcall _ _ _ _ _ _ signature callee arguments
        (Tailcall.transf_fundef cfg definition) targetNextMemory targetLookup
        (find_function_translated cfg prog tprog programMatch _ _ _ _ find registerMatch)
        ((sig_preserved cfg definition).trans signatureMatch) ?_,
        .call stackMatch (regs_lessdef_regs _ _ registerMatch arguments) nextMemoryMatch⟩
      simpa only [stacksize_preserved cfg func] using targetFree
  | exec_Ibuiltin _ _ _ _ _ _ external arguments result successor values events value
      nextMemory lookup argumentsEvaluation call =>
      obtain ⟨instruction, targetLookup, specification⟩ :=
        transf_instr_lookup cfg func pc _ lookup
      cases specification
      obtain ⟨targetValues, targetArguments, argumentsMatch⟩ :=
        eval_builtin_args_lessdef reg _ _ _ _ _ _ registerMatch memoryMatch
          arguments values argumentsEvaluation
      obtain ⟨targetValue, targetNextMemory, targetCall, valueMatch, nextMemoryMatch, unchanged⟩ :=
        external_call_mem_extends_proof xi external _ _ _ _ _ _ _ _ call memoryMatch argumentsMatch
      have preservedArguments := eval_builtin_args_preserved reg _ _ _ _
        (sourceGenv prog) (targetGenv tprog) _ _ _ symbols _ _ targetArguments
      have preservedCall := external_call_symbols_preserved_proof xi external _ _ _ _ _ _ _
        (senv_preserved cfg prog tprog programMatch) targetCall
      exact ⟨_, RTL.step.exec_Ibuiltin _ _ _ _ _ _ external arguments result successor
        targetValues events targetValue targetNextMemory targetLookup preservedArguments preservedCall,
        .normal stackMatch (set_res_lessdef _ _ _ _ _ valueMatch registerMatch) nextMemoryMatch⟩
  | exec_Icond _ _ _ _ _ _ condition arguments ifso ifnot decision successor
      lookup evaluation successorMatch =>
      obtain ⟨instruction, targetLookup, specification⟩ :=
        transf_instr_lookup cfg func pc _ lookup
      cases specification
      exact ⟨_, RTL.step.exec_Icond _ _ _ _ _ _ condition arguments ifso ifnot decision
        successor targetLookup (eval_condition_lessdef _ _ _ _ _ _
          (regs_lessdef_regs _ _ registerMatch arguments) memoryMatch evaluation) successorMatch,
        .normal stackMatch registerMatch memoryMatch⟩
  | exec_Ijumptable _ _ _ _ _ _ argument table index successor lookup argumentValue nth =>
      obtain ⟨instruction, targetLookup, specification⟩ :=
        transf_instr_lookup cfg func pc _ lookup
      cases specification
      have targetValue := registerMatch argument
      rw [argumentValue] at targetValue
      have targetEquality : Regmap.get argument targetRegisters = Vint index := by
        generalize targetEquation : Regmap.get argument targetRegisters = target at targetValue
        cases targetValue
        rfl
      exact ⟨_, RTL.step.exec_Ijumptable _ _ _ _ _ _ argument table index successor
        targetLookup targetEquality nth, .normal stackMatch registerMatch memoryMatch⟩
  | exec_Ireturn _ _ _ _ _ _ result nextMemory lookup free =>
      obtain ⟨instruction, targetLookup, specification⟩ :=
        transf_instr_lookup cfg func pc _ lookup
      cases specification
      obtain ⟨targetNextMemory, targetFree, nextMemoryMatch⟩ :=
        Mem.free_parallel_extends _ _ _ _ _ _ memoryMatch free
      refine ⟨_, RTL.step.exec_Ireturn _ _ _ _ _ _ result targetNextMemory targetLookup ?_,
        .return stackMatch ?_ nextMemoryMatch⟩
      · simpa only [stacksize_preserved cfg func] using targetFree
      · cases result with
        | none => exact .lessdef_refl _
        | some register => exact registerMatch register

private theorem tailcall_step_interm
    (cfg : CompilerConfig) (xi : ExternalCalls) (prog : program)
    (stack targetStack : List stackframe) (func : function) (pointer : block)
    (pc : node) (registers : regset) (memory targetMemory : mem)
    (result : reg) (targetValue : val) (events : trace) (next : state)
    (transition : RTL.step xi (sourceGenv prog)
      (State stack func (Vptr pointer Ptrofs.zero) pc registers memory) events next)
    (stackMatch : match_stackframes cfg stack targetStack)
    (memoryMatch : Mem.extends memory targetMemory)
    (returnSequence : is_return_spec func pc result)
    (emptyStack : func.fn_stacksize = .Z0)
    (valueMatch : Val.lessdef (Regmap.get result registers) targetValue) :
    measure next < measure (State stack func (Vptr pointer Ptrofs.zero) pc registers memory) ∧
      events = E0 ∧ match_states cfg next (Returnstate targetStack targetValue targetMemory) := by
  cases returnSequence with
  | is_return_none returnLookup =>
      cases transition <;> simp_all only [Option.some.injEq, reduceCtorEq]
      case exec_Ireturn optionResult nextMemory lookup free =>
        cases returnLookup
        refine ⟨?_, trivial, .return stackMatch (.lessdef_undef _) ?_⟩
        · simp only [measure]
          omega
        · exact Mem.free_left_extends _ _ _ _ _ _ memoryMatch free
  | is_return_some returnLookup =>
      cases transition <;> simp_all only [Option.some.injEq, reduceCtorEq]
      case exec_Ireturn optionResult nextMemory lookup free =>
        cases returnLookup
        refine ⟨?_, trivial, .return stackMatch valueMatch ?_⟩
        · simp only [measure]
          omega
        · exact Mem.free_left_extends _ _ _ _ _ _ memoryMatch free
  | is_return_nop returnLookup remaining decreasing =>
      cases transition <;> simp_all only [Option.some.injEq, reduceCtorEq]
      case exec_Inop successor lookup =>
        cases returnLookup
        refine ⟨?_, trivial, .interm stackMatch memoryMatch remaining emptyStack valueMatch⟩
        simp only [measure]
        omega
  | is_return_move returnLookup remaining decreasing =>
      cases transition <;> simp_all only [Option.some.injEq, reduceCtorEq]
      case exec_Iop operation arguments destination successor value lookup evaluation =>
        cases returnLookup
        have valueEquality : Regmap.get result registers = value :=
          Option.some.inj evaluation
        refine ⟨?_, trivial, .interm stackMatch memoryMatch remaining emptyStack ?_⟩
        · simp only [measure]
          omega
        · unfold RTL.regset at registers
          rw [Regmap.gss_proof, ← valueEquality]
          exact valueMatch

theorem transf_step_correct : transf_step_correctStatement := by
  intro cfg xi prog tprog programMatch source events next transition target matching
  cases matching with
  | @normal stack pointer pc registers memory targetStack targetRegisters targetMemory
      func stackMatch registerMatch memoryMatch =>
      exact Or.inl (tailcall_step_normal cfg xi prog tprog programMatch _ _ _ _ _ _ _ _ _ _ _
        transition stackMatch registerMatch memoryMatch)
  | @call stack definition arguments memory targetStack targetArguments targetMemory
      stackMatch argumentMatch memoryMatch =>
      cases transition with
      | exec_function_internal _ func _ _ nextMemory pointer argumentTypes allocation =>
          obtain ⟨targetNextMemory, targetAllocation, nextMemoryMatch⟩ :=
            Mem.alloc_extends _ _ _ _ _ _ .Z0 func.fn_stacksize memoryMatch allocation
              (by exact Int.le_refl _) (by exact Int.le_refl _)
          have fields :
              (Tailcall.transf_function cfg func).fn_sig = func.fn_sig ∧
              (Tailcall.transf_function cfg func).fn_entrypoint = func.fn_entrypoint ∧
              (Tailcall.transf_function cfg func).fn_params = func.fn_params := by
            unfold Tailcall.transf_function
            split <;> exact ⟨rfl, rfl, rfl⟩
          refine Or.inl ⟨_, RTL.step.exec_function_internal targetStack
            (Tailcall.transf_function cfg func) targetArguments targetMemory targetNextMemory
            pointer ?_ ?_, ?_⟩
          · rw [fields.1]
            exact Val.has_argtype_list_lessdef _ _ _ argumentTypes argumentMatch
          · rw [stacksize_preserved cfg func]
            exact targetAllocation
          · rw [fields.2.1, fields.2.2]
            exact .normal stackMatch (regs_lessdef_init_regs _ _ _ argumentMatch) nextMemoryMatch
      | exec_function_external _ external _ value _ _ nextMemory call =>
          obtain ⟨targetValue, targetNextMemory, targetCall, valueMatch, nextMemoryMatch, unchanged⟩ :=
            external_call_mem_extends_proof xi external _ _ _ _ _ _ _ _ call memoryMatch argumentMatch
          have preservedCall := external_call_symbols_preserved_proof xi external _ _ _ _ _ _ _
            (senv_preserved cfg prog tprog programMatch) targetCall
          exact Or.inl ⟨_, RTL.step.exec_function_external _ _ _ _ _ _ _ preservedCall,
            .return stackMatch valueMatch nextMemoryMatch⟩
  | @«return» stack value memory targetStack targetValue targetMemory
      stackMatch valueMatch memoryMatch =>
      cases transition with
      | exec_return result func pointer pc registers callerStack returned memory =>
          cases stackMatch with
          | match_stackframes_normal _ _ _ _ _ _ targetRegisters _ remaining registerMatch =>
              exact Or.inl ⟨_, RTL.step.exec_return _ _ _ _ _ _ _ _,
                .normal remaining (set_reg_lessdef _ _ _ _ _ valueMatch registerMatch) memoryMatch⟩
          | match_stackframes_tail _ _ _ _ _ _ _ remaining returnSequence emptyStack =>
              refine Or.inr ⟨?_, rfl, .interm remaining memoryMatch returnSequence emptyStack ?_⟩
              · have bounded := return_measure_bounds func.fn_code pc
                simp only [measure, List.length_cons, Nat.add_mul, Nat.one_mul]
                omega
              · unfold RTL.regset at registers
                rw [Regmap.gss_proof]
                exact valueMatch
  | @interm stack pointer pc registers memory targetStack targetMemory func result targetValue
      stackMatch memoryMatch returnSequence emptyStack valueMatch =>
      exact Or.inr (tailcall_step_interm cfg xi prog _ _ _ _ _ _ _ _ _ _ _ _ transition
        stackMatch memoryMatch returnSequence emptyStack valueMatch)

theorem transf_program_correct : transf_program_correctStatement := by
  intro cfg xi prog tprog programMatch
  exact CompCert4Lean.Common.Smallstep.forward_simulation_opt
    (RTL.semantics xi prog) (RTL.semantics xi tprog)
    (senv_preserved cfg prog tprog programMatch).2.1
    (match_states cfg)
    (transf_initial_states cfg prog tprog programMatch)
    (transf_final_states cfg prog tprog programMatch)
    measure (transf_step_correct cfg xi prog tprog programMatch)

end CompCert4Lean.Backend.Tailcallproof
