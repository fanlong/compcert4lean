import CompCert4Lean.Backend.Conventions
import CompCert4Lean.Backend.LTL
import CompCert4Lean.Backend.Linear
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.X86.Op

/-!
# Type checking Linear code

Definition-bearing translation of CompCert's `backend/Lineartyping.v`.
Proofs assigned to the later migration phase are represented by exact
transparent proposition descriptors.
-/

namespace CompCert4Lean.Backend.Lineartyping

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Backend.Linear
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev LinearFunction := CompCert4Lean.Backend.Linear.function
private abbrev LinearCode := CompCert4Lean.Backend.Linear.code
private abbrev LinearFundef := CompCert4Lean.Backend.Linear.fundef
private abbrev LinearProgram := CompCert4Lean.Backend.Linear.program
private abbrev LinearState := CompCert4Lean.Backend.Linear.state
private abbrev LinearStackframe := CompCert4Lean.Backend.Linear.stackframe
private abbrev Locset := CompCert4Lean.Backend.Linear.locset

private def boolOfSumbool {P Q : Prop} : Sumbool P Q → Bool
  | .left _ => true
  | .right _ => false

private def mregDecEq : DecidableEq mreg := by
  intro x y
  cases x <;> cases y <;>
    first
    | exact isTrue rfl
    | exact isFalse (by intro h; cases h)

private def slotDecEq : DecidableEq slot := by
  intro x y
  cases x <;> cases y <;>
    first
    | exact isTrue rfl
    | exact isFalse (by intro h; cases h)

private def locDecEq : DecidableEq loc
  | .R r1, .R r2 =>
      match mregDecEq r1 r2 with
      | .isTrue h => .isTrue (congrArg R h)
      | .isFalse h => .isFalse (by
          intro heq
          cases heq
          exact h rfl)
  | .R _, .S _ _ _ => .isFalse (by intro h; cases h)
  | .S _ _ _, .R _ => .isFalse (by intro h; cases h)
  | .S s1 d1 t1, .S s2 d2 t2 =>
      match slotDecEq s1 s2 with
      | .isFalse h => .isFalse (by
          intro heq
          cases heq
          exact h rfl)
      | .isTrue hs =>
          match (inferInstance : Decidable (d1 = d2)) with
          | .isFalse h => .isFalse (by
              intro heq
              cases heq
              exact h rfl)
          | .isTrue hd =>
              match (inferInstance : Decidable (t1 = t2)) with
              | .isFalse h => .isFalse (by
                  intro heq
                  cases heq
                  exact h rfl)
              | .isTrue ht => .isTrue (by
                  subst s2
                  subst d2
                  subst t2
                  rfl)

private def locEq (x y : loc) : Sumbool (x = y) (x ≠ y) :=
  match locDecEq x y with
  | .isTrue h => .left h
  | .isFalse h => .right h

private def zdivideBool (a b : Z) : Bool :=
  boolOfSumbool (CompCert4Lean.Lib.Coqlib.zeq
    (ZArith.BinInt.Z.modulo b a) ZArith.BinInt.Z.Z0)

private abbrev listForallb {A : Type} (f : A → Bool) (l : List A) : Bool :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.forallb f l

/-! ## Instruction typing predicates -/

def slot_valid (cfg : CompilerConfig) (funct : LinearFunction)
    (sl : slot) (ofs : Z) (ty : typ) : Bool :=
  let aligned := zdivideBool (typealign ty) ofs
  match sl with
  | .Local => boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle ZArith.BinInt.Z.Z0 ofs) && aligned
  | .Outgoing => boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle ZArith.BinInt.Z.Z0 ofs) && aligned
  | .Incoming =>
      boolOfSumbool
        (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec locEq
          (S .Incoming ofs ty)
          (regs_of_rpairs (loc_parameters cfg funct.fn_sig))) && aligned

def slot_writable (sl : slot) : Bool :=
  match sl with
  | .Local => true
  | .Outgoing => true
  | .Incoming => false

def loc_valid (cfg : CompilerConfig) (funct : LinearFunction) (l : loc) : Bool :=
  match l with
  | .R _ => true
  | .S .Local ofs ty => slot_valid cfg funct .Local ofs ty
  | .S _ _ _ => false

def wt_builtin_res (ty : typ) (res : builtin_res mreg) : Bool :=
  match res with
  | .BR r => subtype ty (mreg_type r)
  | .BR_none => true
  | .BR_splitlong hi lo => wt_builtin_res Tint hi && wt_builtin_res Tint lo

def wt_instr (cfg : CompilerConfig) (f : LinearFunction) : Linear.instruction → Bool
  | .Lgetstack sl ofs ty r =>
      subtype ty (mreg_type r) && slot_valid cfg f sl ofs ty
  | .Lsetstack _ sl ofs ty =>
      slot_valid cfg f sl ofs ty && slot_writable sl
  | .Lop op args res =>
      match is_move_operation op args with
      | some arg => subtype (mreg_type arg) (mreg_type res)
      | none => subtype (type_of_operation op).2 (mreg_type res)
  | .Lload chunk _ _ dst => subtype (type_of_chunk chunk) (mreg_type dst)
  | .Ltailcall sg _ =>
      boolOfSumbool (CompCert4Lean.Lib.Coqlib.zeq
        (size_arguments cfg sg) ZArith.BinInt.Z.Z0)
  | .Lbuiltin ef args res =>
      wt_builtin_res (proj_sig_res (ef_sig ef)) res &&
        listForallb (loc_valid cfg f) (params_of_builtin_args args)
  | _ => true

def wt_code (cfg : CompilerConfig) (f : LinearFunction) (c : LinearCode) : Bool :=
  listForallb (wt_instr cfg f) c

def wt_function (cfg : CompilerConfig) (f : LinearFunction) : Bool :=
  wt_code cfg f f.fn_code

/-! ## Typing of run-time locations and states -/

def wt_locset (ls : Locset) : Prop :=
  ∀ l, Val.has_type (ls l) (Loc.type l)

def agree_outgoing_arguments (cfg : CompilerConfig) (sg : signature)
    (ls pls : Locset) : Prop :=
  ∀ ty ofs,
    S .Outgoing ofs ty ∈ regs_of_rpairs
      (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg) →
      ls (S .Outgoing ofs ty) = pls (S .Outgoing ofs ty)

def outgoing_undef (ls : Locset) : Prop :=
  ∀ ty ofs, ls (S .Outgoing ofs ty) = Vundef

def wt_fundef (cfg : CompilerConfig) (fd : LinearFundef) : Prop :=
  match fd with
  | .Internal f => wt_function cfg f = true
  | .External _ => True

inductive wt_callstack (cfg : CompilerConfig) : List LinearStackframe → Prop where
  | mkNil : wt_callstack cfg []
  | mkCons (f : LinearFunction) (sp : val) (rs : Locset)
      (c : LinearCode) (s : List LinearStackframe)
      (WTSTK : wt_callstack cfg s)
      (WTF : wt_function cfg f = true)
      (WTC : wt_code cfg f c = true)
      (WTRS : wt_locset rs) :
      wt_callstack cfg (Linear.Stackframe f sp rs c :: s)

def wt_parent_locsetStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : List LinearStackframe),
  wt_callstack cfg s → wt_locset (Linear.parent_locset s)

inductive wt_state (cfg : CompilerConfig) : LinearState → Prop where
  | mkRegular (s : List LinearStackframe) (f : LinearFunction)
      (sp : val) (c : LinearCode) (rs : Locset) (m : mem)
      (WTSTK : wt_callstack cfg s)
      (WTF : wt_function cfg f = true)
      (WTC : wt_code cfg f c = true)
      (WTRS : wt_locset rs) :
      wt_state cfg (Linear.State s f sp c rs m)
  | mkCall (s : List LinearStackframe) (fd : LinearFundef)
      (rs : Locset) (m : mem)
      (WTSTK : wt_callstack cfg s)
      (WTFD : wt_fundef cfg fd)
      (WTRS : wt_locset rs)
      (AGCS : agree_callee_save cfg rs (Linear.parent_locset s))
      (AGARGS : agree_outgoing_arguments cfg (Linear.funsig fd) rs
        (Linear.parent_locset s)) :
      wt_state cfg (Linear.Callstate s fd rs m)
  | mkReturn (s : List LinearStackframe) (rs : Locset) (m : mem)
      (WTSTK : wt_callstack cfg s)
      (WTRS : wt_locset rs)
      (AGCS : agree_callee_save cfg rs (Linear.parent_locset s))
      (UOUT : outgoing_undef rs) :
      wt_state cfg (Linear.Returnstate s rs m)

/-! ## Exact statement descriptors for later proofs -/

def wt_setregStatement : Prop :=
  ∀ (ls : Locset) (r : mreg) (v : val),
    Val.has_type v (mreg_type r) →
      wt_locset ls → wt_locset (Locmap.set (R r) v ls)

def wt_setstackStatement : Prop :=
  ∀ (ls : Locset) (sl : slot) (ofs : Z) (ty : typ) (v : val),
    wt_locset ls → wt_locset (Locmap.set (S sl ofs ty) v ls)

def wt_undef_regsStatement : Prop :=
  ∀ (rs : List mreg) (ls : Locset),
    wt_locset ls → wt_locset (LTL.undef_regs rs ls)

def wt_call_regsStatement : Prop :=
  ∀ (ls : Locset), wt_locset ls → wt_locset (LTL.call_regs ls)

def wt_return_regsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (caller callee : Locset),
    wt_locset caller → wt_locset callee →
      wt_locset (LTL.return_regs cfg caller callee)

def wt_undef_caller_save_regsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (ls : Locset),
    wt_locset ls → wt_locset (LTL.undef_caller_save_regs cfg ls)

def wt_initStatement : Prop := wt_locset (Locmap.init Vundef)

def wt_setpairStatement : Prop :=
  ∀ (sg : signature) (v : val) (rs : Locset),
    Val.has_type v (proj_sig_res sg) →
      wt_locset rs → wt_locset (Locmap.setpair
        (CompCert4Lean.X86.Conventions1.loc_result sg) v rs)

def wt_setresStatement : Prop :=
  ∀ (res : builtin_res mreg) (ty : typ) (v : val) (rs : Locset),
    wt_builtin_res ty res = true →
      Val.has_type v ty → wt_locset rs → wt_locset (Locmap.setres res v rs)

def wt_find_labelStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : LinearFunction) (lbl : Linear.label)
    (c : LinearCode),
    wt_function cfg f = true →
      Linear.find_label lbl f.fn_code = some c → wt_code cfg f c = true

def wt_find_functionStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p : LinearProgram),
    (∀ (i : ident) (fd : LinearFundef),
    (i, Gfun fd) ∈ p.prog_defs → wt_fundef cfg fd) →
    ∀ (ros : Sum mreg ident) (rs : Locset) (f : LinearFundef),
      Linear.find_function (Genv.globalenv p) ros rs = some f → wt_fundef cfg f

def step_type_preservationStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (p : LinearProgram),
    (∀ (i : ident) (fd : LinearFundef),
      (i, Gfun fd) ∈ p.prog_defs → wt_fundef cfg fd) →
    ∀ (S1 : LinearState) (t : trace) (S2 : LinearState),
      Linear.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi (Genv.globalenv p) S1 t S2 →
        wt_state cfg S1 → wt_state cfg S2

def wt_initial_stateStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p : LinearProgram),
    (∀ (i : ident) (fd : LinearFundef),
      (i, Gfun fd) ∈ p.prog_defs → wt_fundef cfg fd) →
    ∀ S : LinearState, Linear.initial_state p S → wt_state cfg S

def wt_state_getstackStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : List LinearStackframe) (f : LinearFunction)
    (sp : val) (sl : slot) (ofs : Z) (ty : typ) (rd : mreg)
    (c : LinearCode) (rs : Locset) (m : mem),
    wt_state cfg (Linear.State s f sp
      (Linear.Lgetstack sl ofs ty rd :: c) rs m) →
      slot_valid cfg f sl ofs ty = true

def wt_state_setstackStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : List LinearStackframe) (f : LinearFunction)
    (sp : val) (sl : slot) (ofs : Z) (ty : typ) (r : mreg)
    (c : LinearCode) (rs : Locset) (m : mem),
    wt_state cfg (Linear.State s f sp
      (Linear.Lsetstack r sl ofs ty :: c) rs m) →
      slot_valid cfg f sl ofs ty = true ∧ slot_writable sl = true

def wt_state_tailcallStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : List LinearStackframe) (f : LinearFunction)
    (sp : val) (sg : signature) (ros : Sum mreg ident) (c : LinearCode)
    (rs : Locset) (m : mem),
    wt_state cfg (Linear.State s f sp
      (Linear.Ltailcall sg ros :: c) rs m) →
      CompCert4Lean.Backend.Conventions.size_arguments cfg sg =
        ZArith.BinInt.Z.Z0

def wt_state_builtinStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : List LinearStackframe) (f : LinearFunction)
    (sp : val) (ef : external_function) (args : List (builtin_arg loc))
    (res : builtin_res mreg) (c : LinearCode) (rs : Locset) (m : mem),
    wt_state cfg (Linear.State s f sp
      (Linear.Lbuiltin ef args res :: c) rs m) →
      listForallb (loc_valid cfg f) (params_of_builtin_args args) = true

def wt_callstate_wt_regsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : List LinearStackframe) (f : LinearFundef)
    (rs : Locset) (m : mem),
    wt_state cfg (Linear.Callstate s f rs m) →
      ∀ r, Val.has_type (rs (R r)) (mreg_type r)

def wt_callstate_agreeStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : List LinearStackframe) (f : LinearFundef)
    (rs : Locset) (m : mem),
    wt_state cfg (Linear.Callstate s f rs m) →
      agree_callee_save cfg rs (Linear.parent_locset s) ∧
        agree_outgoing_arguments cfg (Linear.funsig f) rs (Linear.parent_locset s)

def wt_returnstate_agreeStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : List LinearStackframe) (rs : Locset) (m : mem),
    wt_state cfg (Linear.Returnstate s rs m) →
      agree_callee_save cfg rs (Linear.parent_locset s) ∧ outgoing_undef rs

end CompCert4Lean.Backend.Lineartyping
