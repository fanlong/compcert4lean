import CompCert4Lean.Backend.Conventions
import CompCert4Lean.Backend.Linear
import CompCert4Lean.Backend.Locations
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Lib.Iteration
import CompCert4Lean.Lib.Maps
import CompCert4Lean.X86.Conventions1

/-!
# Debug-variable live-range analysis

Definition-bearing translation of CompCert's `backend/Debugvar.v`.  The
caller-save set is obtained from the explicit immutable compiler
configuration used by the translated x86 conventions.
-/

namespace CompCert4Lean.Backend.Debugvar

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Conventions1
open CompCert4Lean.X86.Machregs

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool

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
  | .S sl1 ofs1 ty1, .S sl2 ofs2 ty2 =>
      match slotDecEq sl1 sl2 with
      | .isFalse h => .isFalse (by
          intro heq
          cases heq
          exact h rfl)
      | .isTrue hs =>
          match (inferInstance : Decidable (ofs1 = ofs2)) with
          | .isFalse h => .isFalse (by
              intro heq
              cases heq
              exact h rfl)
          | .isTrue ho =>
              match (inferInstance : Decidable (ty1 = ty2)) with
              | .isFalse h => .isFalse (by
                  intro heq
                  cases heq
                  exact h rfl)
              | .isTrue ht => .isTrue (by
                  subst sl2
                  subst ofs2
                  subst ty2
                  rfl)

private instance : DecidableEq mreg := mregDecEq
private instance : DecidableEq slot := slotDecEq
private instance : DecidableEq loc := locDecEq

private abbrev pos2 : positive := PArith.BinPos.Pos.of_nat 2
private abbrev pos3 : positive := PArith.BinPos.Pos.of_nat 3
private abbrev pos4 : positive := PArith.BinPos.Pos.of_nat 4

/-! ## Safe debug expressions and availability states -/

def safe_builtin_arg {A : Type} (a : builtin_arg A) : Prop :=
  match a with
  | .BA _ | .BA_int _ | .BA_long _ | .BA_float _ | .BA_single _ => True
  | .BA_splitlong hi lo => safe_builtin_arg hi ∧ safe_builtin_arg lo
  | _ => False

def debuginfo : Type := { a : builtin_arg loc // safe_builtin_arg a }

def normalize_debug_1 (a : builtin_arg loc) : Option debuginfo :=
  match a with
  | .BA x => some ⟨.BA x, True.intro⟩
  | .BA_int n => some ⟨.BA_int n, True.intro⟩
  | .BA_long n => some ⟨.BA_long n, True.intro⟩
  | .BA_float n => some ⟨.BA_float n, True.intro⟩
  | .BA_single n => some ⟨.BA_single n, True.intro⟩
  | .BA_splitlong (.BA hi) (.BA lo) =>
      some ⟨.BA_splitlong (.BA hi) (.BA lo), And.intro True.intro True.intro⟩
  | _ => none

def normalize_debug (l : List (builtin_arg loc)) : Option debuginfo :=
  match l with
  | [] => none
  | a :: rest =>
      match a with
      | .BA_int _ | .BA_long _ | .BA_float _ | .BA_single _ =>
          match normalize_debug rest with
          | some i => some i
          | none => normalize_debug_1 a
      | _ => normalize_debug_1 a

def avail : Type := List (ident × debuginfo)

def set_state (v : ident) (i : debuginfo) (s : avail) : avail :=
  match s with
  | [] => [(v, i)]
  | (v', i') :: rest =>
      match PArith.BinPos.Pos.compare v v' with
      | .Eq => (v, i) :: rest
      | .Lt => (v, i) :: s
      | .Gt => (v', i') :: set_state v i rest

def remove_state (v : ident) (s : avail) : avail :=
  match s with
  | [] => []
  | (v', i') :: rest =>
      match PArith.BinPos.Pos.compare v v' with
      | .Eq => rest
      | .Lt => s
      | .Gt => (v', i') :: remove_state v rest

def set_debug_info (v : ident) (info : List (builtin_arg loc)) (s : avail) : avail :=
  match normalize_debug info with
  | some a => set_state v a s
  | none => remove_state v s

def arg_no_overlap (a : builtin_arg loc) (l : loc) : Bool :=
  match a with
  | .BA l' =>
      match Loc.diff_dec l' l with
      | .left _ => false
      | .right _ => true
  | .BA_splitlong hi lo => arg_no_overlap hi l && arg_no_overlap lo l
  | _ => true

def kill (l : loc) (s : avail) : avail :=
  s.filter (fun vi => arg_no_overlap vi.2.1 l)

def kill_res (r : builtin_res mreg) (s : avail) : avail :=
  match r with
  | .BR r => kill (.R r) s
  | .BR_none => s
  | .BR_splitlong hi lo => kill_res hi (kill_res lo s)

def arg_preserved (cfg : CompilerConfig) (a : builtin_arg loc) : Bool :=
  match a with
  | .BA (.R r) =>
      !(destroyed_at_call cfg).any (fun r' => decide (r = r'))
  | .BA (.S _ _ _) => true
  | .BA_splitlong hi lo => arg_preserved cfg hi && arg_preserved cfg lo
  | _ => true

def kill_at_call (cfg : CompilerConfig) (s : avail) : avail :=
  s.filter (fun vi => arg_preserved cfg vi.2.1)

private def locEq (x y : loc) : Sumbool (x = y) (x ≠ y) :=
  match locDecEq x y with
  | .isTrue h => .left h
  | .isFalse h => .right h

def eq_arg (a1 a2 : builtin_arg loc) : Sumbool (a1 = a2) (a1 ≠ a2) :=
  CompCert4Lean.Common.AST.eq_builtin_arg locEq a1 a2

def eq_debuginfo (i1 i2 : debuginfo) : Sumbool (i1 = i2) (i1 ≠ i2) := by
  match eq_arg i1.1 i2.1 with
  | .left h =>
      exact .left (by
        cases i1 with
        | mk a ha =>
          cases i2 with
          | mk b hb =>
            cases h
            rfl)
  | .right h =>
      exact .right (by
        intro heq
        exact h (congrArg Subtype.val heq))

def join : avail → avail → avail
  | [], _ => []
  | _, [] => []
  | (v1, i1) :: rest1, (v2, i2) :: rest2 =>
      match PArith.BinPos.Pos.compare v1 v2 with
      | .Eq =>
          match eq_debuginfo i1 i2 with
          | .left _ => (v1, i1) :: join rest1 rest2
          | .right _ => join rest1 rest2
      | .Lt => join rest1 ((v2, i2) :: rest2)
      | .Gt => join ((v1, i1) :: rest1) rest2
termination_by s1 s2 => s1.length + s2.length

private def debuginfoDecEq : DecidableEq debuginfo := by
  intro x y
  match eq_debuginfo x y with
  | .left h => exact .isTrue h
  | .right h => exact .isFalse h

private def availDecEq : DecidableEq avail
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by intro h; cases h)
  | _ :: _, [] => .isFalse (by intro h; cases h)
  | (v1, i1) :: rest1, (v2, i2) :: rest2 =>
      match CompCert4Lean.Lib.Coqlib.peq v1 v2 with
      | .left hv =>
          match debuginfoDecEq i1 i2 with
          | .isTrue hi =>
              match availDecEq rest1 rest2 with
              | .isTrue hr => .isTrue (by cases hv; cases hi; cases hr; rfl)
              | .isFalse hr => .isFalse (by
                  intro h
                  apply hr
                  cases hv
                  cases hi
                  exact congrArg List.tail h)
          | .isFalse hi => .isFalse (by
              intro h
              cases h
              exact hi rfl)
      | .right hv => .isFalse (by
          intro h
          cases h
          exact hv rfl)

def eq_state (s1 s2 : avail) : Sumbool (s1 = s2) (s1 ≠ s2) :=
  match availDecEq s1 s2 with
  | .isTrue h => .left h
  | .isFalse h => .right h

def top : avail := []

def labelmap : Type := PTree.t avail × Bool

def get_label (lbl : label) (lm : labelmap) : Option avail :=
  PTree.get lbl lm.1

def update_label (lbl : label) (s1 : avail) (lm : labelmap) : labelmap × avail :=
  match get_label lbl lm with
  | none => ((PTree.set lbl s1 lm.1, true), s1)
  | some s2 =>
      let s := join s1 s2
      match eq_state s s2 with
      | .left _ => (lm, s2)
      | .right _ => ((PTree.set lbl s lm.1, true), s)

def update_labels (lbls : List label) (s : avail) (lm : labelmap) : labelmap :=
  match lbls with
  | [] => lm
  | lbl1 :: rest => update_labels rest s (update_label lbl1 s lm).1

/-! ## Classification and transfer -/

def is_debug_setvar (ef : external_function) : Option ident :=
  match ef with
  | .EF_debug k txt _ =>
      if h : k = pos2 then some txt else none
  | _ => none

def is_builtin_debug_setvar (i : instruction) : Option ident :=
  match i with
  | .Lbuiltin ef _ .BR_none => is_debug_setvar ef
  | _ => none

def transfer (cfg : CompilerConfig) (lm : labelmap) (before : Option avail)
    (i : instruction) : labelmap × Option avail :=
  match before with
  | none =>
      match i with
      | .Llabel lbl => (lm, get_label lbl lm)
      | _ => (lm, none)
  | some s =>
      match i with
      | .Lgetstack _ _ _ rd => (lm, some (kill (.R rd) s))
      | .Lsetstack _ sl ofs ty => (lm, some (kill (.S sl ofs ty) s))
      | .Lop _ _ dst => (lm, some (kill (.R dst) s))
      | .Lload _ _ _ dst => (lm, some (kill (.R dst) s))
      | .Lstore _ _ _ _ => (lm, before)
      | .Lcall _ _ => (lm, some (kill_at_call cfg s))
      | .Ltailcall _ _ => (lm, none)
      | .Lbuiltin ef args res =>
          let s' :=
            match is_debug_setvar ef with
            | some v => set_debug_info v args s
            | none => s
          (lm, some (kill_res res s'))
      | .Llabel lbl =>
          let r := update_label lbl s lm
          (r.1, some r.2)
      | .Lgoto lbl =>
          let r := update_label lbl s lm
          (r.1, none)
      | .Lcond _ _ lbl =>
          let r := update_label lbl s lm
          (r.1, before)
      | .Ljumptable _ lbls => (update_labels lbls s lm, none)
      | .Lreturn => (lm, none)

def ana_code (cfg : CompilerConfig) (lm : labelmap) (before : Option avail)
    (c : code) : labelmap :=
  match c with
  | [] => lm
  | i :: rest =>
      let r := transfer cfg lm before i
      ana_code cfg r.1 r.2 rest

def ana_iter (cfg : CompilerConfig) (c : code) (lm : labelmap) : Sum labelmap labelmap :=
  let lm' := ana_code cfg (lm.1, false) (some top) c
  if lm'.2 then .inr lm' else .inl lm'

def ana_function (cfg : CompilerConfig) (f : function) : Option labelmap :=
  CompCert4Lean.Lib.Iteration.PrimIter.iterate labelmap labelmap
    (ana_iter cfg f.fn_code)
    (PTree.empty _, false)

/-! ## Code transformation -/

def diff : avail → avail → avail
  | [], _ => []
  | (v1, i1) :: rest1, [] => (v1, i1) :: rest1
  | (v1, i1) :: rest1, (v2, i2) :: rest2 =>
      match PArith.BinPos.Pos.compare v1 v2 with
      | .Eq =>
          match eq_debuginfo i1 i2 with
          | .left _ => diff rest1 rest2
          | .right _ => (v1, i1) :: diff rest1 rest2
      | .Lt => (v1, i1) :: diff rest1 ((v2, i2) :: rest2)
      | .Gt => diff ((v1, i1) :: rest1) rest2
termination_by s1 s2 => s1.length + s2.length

def delta_state (before after : Option avail) : avail × avail :=
  match before, after with
  | none, none => ([], [])
  | some b, none => (b, [])
  | none, some a => ([], a)
  | some b, some a => (diff b a, diff a b)

def add_start_range (vi : ident × debuginfo) (c : code) : code :=
  let (v, i) := vi
  .Lbuiltin (.EF_debug pos3 v []) [i.1] .BR_none :: c

def add_end_range (vi : ident × debuginfo) (c : code) : code :=
  let (v, _) := vi
  .Lbuiltin (.EF_debug pos4 v []) [] .BR_none :: c

def add_delta_ranges (before after : Option avail) (c : code) : code :=
  let (killed, born) := delta_state before after
  killed.foldr add_end_range (born.foldr add_start_range c)

def skip_debug_setvar (cfg : CompilerConfig) (lm : labelmap) (before : Option avail)
    (c : code) : Option avail :=
  match c with
  | [] => before
  | i :: rest =>
      match is_builtin_debug_setvar i with
      | some _ =>
          let r := transfer cfg lm before i
          skip_debug_setvar cfg lm r.2 rest
      | none => before

def transf_code (cfg : CompilerConfig) (lm : labelmap) (before : Option avail)
    (c : code) : code :=
  match c with
  | [] => []
  | .Lgoto lbl1 :: .Llabel lbl2 :: rest =>
      let after := get_label lbl2 lm
      .Lgoto lbl1 :: .Llabel lbl2 ::
        add_delta_ranges before after (transf_code cfg lm after rest)
  | i :: rest =>
      let r := transfer cfg lm before i
      let after := skip_debug_setvar cfg lm r.2 rest
      i :: add_delta_ranges before after (transf_code cfg lm after rest)

private def bytesToString : List UInt8 → RocqString
  | [] => .EmptyString
  | byte :: rest => .String byte (bytesToString rest)

private def analysisDivergesText : RocqString :=
  bytesToString [68, 101, 98, 117, 103, 118, 97, 114, 58, 32, 97, 110, 97, 108,
    121, 115, 105, 115, 32, 100, 105, 118, 101, 114, 103, 101, 115]

def transf_function (cfg : CompilerConfig) (f : function) : res function :=
  match ana_function cfg f with
  | none => Error (msg analysisDivergesText)
  | some lm =>
      OK
        { fn_sig := f.fn_sig
          fn_stacksize := f.fn_stacksize
          fn_code := transf_code cfg lm (some top) f.fn_code }

def transf_fundef (cfg : CompilerConfig) (fd : fundef) : res fundef :=
  CompCert4Lean.Common.AST.transf_partial_fundef (transf_function cfg) fd

def transf_program (cfg : CompilerConfig) (p : program) : res program :=
  CompCert4Lean.Common.AST.transform_partial_program (transf_fundef cfg) p

end CompCert4Lean.Backend.Debugvar
