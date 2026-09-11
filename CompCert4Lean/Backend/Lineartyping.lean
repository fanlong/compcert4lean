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
  | wt_callstack_nil : wt_callstack cfg []
  | wt_callstack_cons (f : LinearFunction) (sp : val) (rs : Locset)
      (c : LinearCode) (s : List LinearStackframe)
      (WTSTK : wt_callstack cfg s)
      (WTF : wt_function cfg f = true)
      (WTC : wt_code cfg f c = true)
      (WTRS : wt_locset rs) :
      wt_callstack cfg (Linear.Stackframe f sp rs c :: s)

export wt_callstack (wt_callstack_nil wt_callstack_cons)

def wt_parent_locsetStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : List LinearStackframe),
  wt_callstack cfg s → wt_locset (Linear.parent_locset s)

inductive wt_state (cfg : CompilerConfig) : LinearState → Prop where
  | wt_regular_state (s : List LinearStackframe) (f : LinearFunction)
      (sp : val) (c : LinearCode) (rs : Locset) (m : mem)
      (WTSTK : wt_callstack cfg s)
      (WTF : wt_function cfg f = true)
      (WTC : wt_code cfg f c = true)
      (WTRS : wt_locset rs) :
      wt_state cfg (Linear.State s f sp c rs m)
  | wt_call_state (s : List LinearStackframe) (fd : LinearFundef)
      (rs : Locset) (m : mem)
      (WTSTK : wt_callstack cfg s)
      (WTFD : wt_fundef cfg fd)
      (WTRS : wt_locset rs)
      (AGCS : agree_callee_save cfg rs (Linear.parent_locset s))
      (AGARGS : agree_outgoing_arguments cfg (Linear.funsig fd) rs
        (Linear.parent_locset s)) :
      wt_state cfg (Linear.Callstate s fd rs m)
  | wt_return_state (s : List LinearStackframe) (rs : Locset) (m : mem)
      (WTSTK : wt_callstack cfg s)
      (WTRS : wt_locset rs)
      (AGCS : agree_callee_save cfg rs (Linear.parent_locset s))
      (UOUT : outgoing_undef rs) :
      wt_state cfg (Linear.Returnstate s rs m)

export wt_state (wt_regular_state wt_call_state wt_return_state)

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

namespace CompCert4Lean.Backend.Lineartyping

theorem wt_setreg : wt_setregStatement := by
  intro ls r v hv hls l
  unfold CompCert4Lean.Backend.Locations.Locmap.set
  generalize hEq : CompCert4Lean.Backend.Locations.Loc.eq (CompCert4Lean.Backend.Locations.R r) l = e
  cases e with
  | left h =>
      cases h
      simpa [CompCert4Lean.Backend.Locations.Loc.type] using hv
  | right h =>
      generalize hDiff : CompCert4Lean.Backend.Locations.Loc.diff_dec
        (CompCert4Lean.Backend.Locations.R r) l = d
      cases d with
      | left hd => exact hls l
      | right hd => exact trivial

theorem wt_setstack : wt_setstackStatement := by
  intro ls sl ofs ty v hls l
  unfold CompCert4Lean.Backend.Locations.Locmap.set
  generalize hEq : CompCert4Lean.Backend.Locations.Loc.eq
    (CompCert4Lean.Backend.Locations.S sl ofs ty) l = e
  cases e with
  | left h =>
      cases h
      cases ty <;> cases v <;>
        simp [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Common.AST.chunk_of_type,
          CompCert4Lean.Backend.Locations.Loc.type,
          CompCert4Lean.X86_64.Archi.ptr64,
          CompCert4Lean.Common.Values.Val.has_type]
  | right h =>
      generalize hDiff : CompCert4Lean.Backend.Locations.Loc.diff_dec
        (CompCert4Lean.Backend.Locations.S sl ofs ty) l = d
      cases d with
      | left hd => exact hls l
      | right hd => exact trivial

theorem wt_undef_regs : wt_undef_regsStatement := by
  intro rs
  induction rs with
  | nil =>
      intro ls hls
      simpa [CompCert4Lean.Backend.LTL.undef_regs] using hls
  | cons r rs ih =>
      intro ls hls
      apply wt_setreg
      · exact trivial
      · exact ih ls hls

theorem wt_call_regs : wt_call_regsStatement := by
  intro ls hls l
  cases l with
  | R r =>
      simpa [CompCert4Lean.Backend.LTL.call_regs,
        CompCert4Lean.Backend.Locations.Loc.type] using hls
        (CompCert4Lean.Backend.Locations.R r)
  | S sl ofs ty =>
      cases sl with
      | Local =>
          simp [CompCert4Lean.Backend.LTL.call_regs,
            CompCert4Lean.Backend.Locations.Loc.type,
            CompCert4Lean.Common.Values.Val.has_type]
      | Incoming =>
          simpa [CompCert4Lean.Backend.LTL.call_regs,
            CompCert4Lean.Backend.Locations.Loc.type] using hls
            (CompCert4Lean.Backend.Locations.S
              CompCert4Lean.Backend.Locations.Outgoing ofs ty)
      | Outgoing =>
          simp [CompCert4Lean.Backend.LTL.call_regs,
            CompCert4Lean.Backend.Locations.Loc.type,
            CompCert4Lean.Common.Values.Val.has_type]

end CompCert4Lean.Backend.Lineartyping

namespace CompCert4Lean.Backend.Lineartyping

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.LTL
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op

theorem wt_return_regs : wt_return_regsStatement := by
  intro cfg caller callee hcaller hcallee l
  cases l with
  | R r =>
      simp only [CompCert4Lean.Backend.LTL.return_regs,
        CompCert4Lean.Backend.Locations.Loc.type]
      split
      · exact hcaller (R r)
      · exact hcallee (R r)
  | S sl ofs ty =>
      cases sl with
      | Local =>
          simpa [CompCert4Lean.Backend.LTL.return_regs,
            CompCert4Lean.Backend.Locations.Loc.type] using hcaller (S .Local ofs ty)
      | Incoming =>
          simpa [CompCert4Lean.Backend.LTL.return_regs,
            CompCert4Lean.Backend.Locations.Loc.type] using hcaller (S .Incoming ofs ty)
      | Outgoing =>
          simp [CompCert4Lean.Backend.LTL.return_regs,
            CompCert4Lean.Backend.Locations.Loc.type,
            CompCert4Lean.Common.Values.Val.has_type]

theorem wt_undef_caller_save_regs : wt_undef_caller_save_regsStatement := by
  intro cfg ls hls l
  cases l with
  | R r =>
      simp only [CompCert4Lean.Backend.LTL.undef_caller_save_regs,
        CompCert4Lean.Backend.Locations.Loc.type]
      split
      · exact hls (R r)
      · exact trivial
  | S sl ofs ty =>
      cases sl with
      | Local =>
          simpa [CompCert4Lean.Backend.LTL.undef_caller_save_regs,
            CompCert4Lean.Backend.Locations.Loc.type] using hls (S .Local ofs ty)
      | Incoming =>
          simpa [CompCert4Lean.Backend.LTL.undef_caller_save_regs,
            CompCert4Lean.Backend.Locations.Loc.type] using hls (S .Incoming ofs ty)
      | Outgoing =>
          simp [CompCert4Lean.Backend.LTL.undef_caller_save_regs,
            CompCert4Lean.Backend.Locations.Loc.type,
            CompCert4Lean.Common.Values.Val.has_type]

theorem wt_init : wt_initStatement := by
  intro l
  simp [CompCert4Lean.Backend.Locations.Locmap.init,
    CompCert4Lean.Common.Values.Val.has_type]

theorem wt_setpair : wt_setpairStatement := by
  intro sg v rs hv hrs
  cases sg with
  | mk args res cc =>
      cases res <;>
        simp [CompCert4Lean.X86.Conventions1.loc_result,
          CompCert4Lean.X86.Conventions1.loc_result_64,
          CompCert4Lean.X86_64.Archi.ptr64,
          CompCert4Lean.Backend.Locations.Locmap.setpair]
      all_goals
        apply wt_setreg
        · cases v <;> trivial
        · exact hrs

end CompCert4Lean.Backend.Lineartyping

namespace CompCert4Lean.Backend.Lineartyping

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private theorem val_has_type_subtype_local :
    ∀ (ty1 ty2 : typ) (v : val),
      subtype ty1 ty2 = true → Val.has_type v ty1 → Val.has_type v ty2 := by
  intro ty1 ty2 v hsub hv
  cases ty1 <;> cases ty2 <;> cases v <;>
    simp [CompCert4Lean.Common.AST.subtype,
      CompCert4Lean.Common.Values.Val.has_type,
      CompCert4Lean.X86_64.Archi.ptr64] at hsub hv ⊢

theorem wt_setres : wt_setresStatement := by
  intro res
  induction res with
  | BR r =>
      intro ty v rs hres hv hrs
      apply wt_setreg
      · apply val_has_type_subtype_local ty (mreg_type r) v
        · simpa [wt_builtin_res] using hres
        · exact hv
      · exact hrs
  | BR_none =>
      intro ty v rs hres hv hrs
      exact hrs
  | BR_splitlong hi lo ih_hi ih_lo =>
      intro ty v rs hres hv hrs
      simp [wt_builtin_res] at hres
      change wt_locset (Locmap.setres lo (Val.loword v)
        (Locmap.setres hi (Val.hiword v) rs))
      apply ih_lo Tint (Val.loword v)
        (Locmap.setres hi (Val.hiword v) rs) hres.2
      · cases v <;> trivial
      · apply ih_hi Tint (Val.hiword v) rs hres.1
        · cases v <;> trivial
        · exact hrs

end CompCert4Lean.Backend.Lineartyping

namespace CompCert4Lean.Backend.Lineartyping

theorem wt_find_label : wt_find_labelStatement := by
  intro cfg f lbl c hwt hfind
  unfold wt_function at hwt
  have aux : ∀ (code : LinearCode), wt_code cfg f code = true →
      ∀ c, Linear.find_label lbl code = some c → wt_code cfg f c = true := by
    intro code
    induction code with
    | nil =>
        intro hwt c hfind
        simp [Linear.find_label] at hfind
    | cons i il ih =>
        intro hwt c hfind
        simp only [Linear.find_label] at hfind
        have hwt' : wt_instr cfg f i = true ∧ wt_code cfg f il = true := by
          simpa [wt_code, listForallb,
            CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.forallb] using hwt
        by_cases hl : Linear.is_label lbl i
        · simp [hl] at hfind
          have hc : il = c := Option.some.inj hfind
          subst c
          exact hwt'.2
        · simp [hl] at hfind
          exact ih hwt'.2 c hfind
  exact aux f.fn_code hwt c hfind

end CompCert4Lean.Backend.Lineartyping

namespace CompCert4Lean.Backend.Lineartyping

theorem wt_parent_locset : wt_parent_locsetStatement := by
  intro cfg s hstk
  induction hstk with
  | wt_callstack_nil =>
      simpa [Linear.parent_locset, wt_initStatement] using wt_init
  | @wt_callstack_cons f sp rs c s hstk hwtf hwtc hwtrs ih =>
      simpa [Linear.parent_locset] using hwtrs

end CompCert4Lean.Backend.Lineartyping

namespace CompCert4Lean.Backend.Lineartyping

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Lib.Integers

private theorem find_def_add_globals_local {F V : Type}
    (gl : List (ident × globdef F V)) (ge : Genv.t F V)
    (b : CompCert4Lean.Common.Values.block)
    (g : globdef F V) :
    Genv.find_def (Genv.add_globals ge gl) b = some g →
      (∃ id, (id, g) ∈ gl) ∨ Genv.find_def ge b = some g := by
  induction gl generalizing ge with
  | nil =>
      intro h
      exact Or.inr h
  | cons idg tl ih =>
      intro h
      have hstep := ih (ge := Genv.add_global ge idg) h
      rcases hstep with hmem | hprev
      · rcases hmem with ⟨id', hmem⟩
        exact Or.inl ⟨id', by simp [hmem]⟩
      · rcases idg with ⟨id, gd⟩
        simp only [Genv.add_global, Genv.find_def] at hprev
        by_cases hb : b = ge.genv_next
        · subst b
          have hval : (some gd : Option (globdef F V)) = some g :=
            (CompCert4Lean.Lib.Maps.PTree.gss ge.genv_next gd ge.genv_defs).symm.trans hprev
          have hg : gd = g := Option.some.inj hval
          subst g
          exact Or.inl ⟨id, by simp⟩
        · have hprev' := CompCert4Lean.Lib.Maps.PTree.gso
              gd ge.genv_defs hb
          have hprev'' := hprev'.symm.trans hprev
          exact Or.inr (by simpa [Genv.find_def] using hprev'')

theorem wt_find_function : wt_find_functionStatement := by
  intro cfg p hprog ros rs f hfind
  unfold Linear.find_function at hfind
  cases ros with
  | inl r =>
      have hinv := Genv.find_funct_inv (F := LinearFundef) (V := Unit)
        (Genv.globalenv p) (rs (R r)) f hfind
      rcases hinv with ⟨b, hb⟩
      have hfun : Genv.find_funct (Genv.globalenv p)
          (Vptr b (CompCert4Lean.Lib.Integers.Ptrofs.zero)) = some f := by
        rw [← hb]
        exact hfind
      have hptr : Genv.find_funct_ptr (Genv.globalenv p) b = some f := by
        rw [Genv.find_funct_find_funct_ptr] at hfun
        exact hfun
      unfold Genv.find_funct_ptr at hptr
      cases hd : Genv.find_def (Genv.globalenv p) b with
      | none => simp [hd] at hptr
      | some gd =>
          cases gd with
          | Gfun f' =>
              have hf : f' = f := Option.some.inj (by simpa [hd] using hptr)
              subst f'
              have hmem : ∃ id, (id, Gfun f) ∈ p.prog_defs := by
                have hcases := find_def_add_globals_local (gl := p.prog_defs)
                  (ge := Genv.empty_genv LinearFundef Unit p.prog_public) (b := b)
                  (g := Gfun f) (by simpa [Genv.globalenv] using hd)
                rcases hcases with hcases | hempty
                · exact hcases
                · have : False := by
                    simpa [Genv.empty_genv, Genv.find_def,
                      CompCert4Lean.Lib.Maps.PTree.empty,
                      CompCert4Lean.Lib.Maps.PTree.get] using hempty
                  contradiction
              rcases hmem with ⟨id, hmem⟩
              exact hprog id f (by simpa using hmem)
          | Gvar v => simp [hd] at hptr
  | inr symb =>
      cases hs : Genv.find_symbol (Genv.globalenv p) symb with
      | none => simp [hs] at hfind
      | some b =>
          have hptr : Genv.find_funct_ptr (Genv.globalenv p) b = some f := by
            simpa [hs] using hfind
          unfold Genv.find_funct_ptr at hptr
          cases hd : Genv.find_def (Genv.globalenv p) b with
          | none => simp [hd] at hptr
          | some gd =>
              cases gd with
              | Gfun f' =>
                  have hf : f' = f := Option.some.inj (by simpa [hd] using hptr)
                  subst f'
                  have hmem : ∃ id, (id, Gfun f) ∈ p.prog_defs := by
                    have hcases := find_def_add_globals_local (gl := p.prog_defs)
                      (ge := Genv.empty_genv LinearFundef Unit p.prog_public) (b := b)
                      (g := Gfun f) (by simpa [Genv.globalenv] using hd)
                    rcases hcases with hcases | hempty
                    · exact hcases
                    · have : False := by
                        simpa [Genv.empty_genv, Genv.find_def,
                          CompCert4Lean.Lib.Maps.PTree.empty,
                          CompCert4Lean.Lib.Maps.PTree.get] using hempty
                      contradiction
                  rcases hmem with ⟨id, hmem⟩
                  exact hprog id f (by simpa using hmem)
              | Gvar v => simp [hd] at hptr

end CompCert4Lean.Backend.Lineartyping
