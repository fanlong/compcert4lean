import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Config
import CompCert4Lean.Backend.Locations
import CompCert4Lean.X86.Conventions1

/-!
# Backend calling conventions

Definition-bearing translation of CompCert's `backend/Conventions.v`. Proof
declarations assigned to later proof migration are represented by exact
transparent proposition descriptors. The processor-dependent convention API's
immutable compiler configuration is threaded through every source definition
that observes argument placement or the callee-save classification.
-/

namespace CompCert4Lean.Backend.Conventions

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z

private abbrev z0 : Z := .Z0
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zGe := ZArith.BinInt.Z.ge
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zMax := ZArith.BinInt.Z.max

private abbrev listFoldLeft {A B : Type} (f : A → B → A)
    (l : List B) (a0 : A) : A :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.fold_left f l a0

private abbrev listForallb {A : Type} (f : A → Bool) (l : List A) : Bool :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.forallb f l

private abbrev locArguments :=
  CompCert4Lean.X86.Conventions1.loc_arguments

private abbrev locArgumentAcceptable :=
  CompCert4Lean.X86.Conventions1.loc_argument_acceptable

private abbrev isCalleeSave :=
  CompCert4Lean.X86.Conventions1.is_callee_save

private abbrev locResult :=
  CompCert4Lean.X86.Conventions1.loc_result

/-! ## Acceptable argument locations -/

def loc_arguments_acceptable_2Statement : Prop :=
  ∀ (cfg : CompilerConfig) (s : signature) (l : loc),
    l ∈ regs_of_rpairs (locArguments cfg s) →
      locArgumentAcceptable cfg l

/-! ## Stack size of function arguments -/

def max_outgoing_1 (accu : Z) : loc → Z
  | .S .Outgoing ofs ty =>
      zMax accu (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty))
  | _ => accu

def max_outgoing_2 (accu : Z) : rpair loc → Z
  | .One l => max_outgoing_1 accu l
  | .Twolong l1 l2 => max_outgoing_1 (max_outgoing_1 accu l1) l2

def size_arguments (cfg : CompilerConfig) (s : signature) : Z :=
  listFoldLeft max_outgoing_2 (locArguments cfg s) z0

def fold_max_outgoing_aboveStatement : Prop :=
  ∀ (l : List (rpair loc)) (n : Z),
    zGe (listFoldLeft max_outgoing_2 l n) n

def loc_arguments_boundedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : signature) (ofs : Z) (ty : typ),
    S Outgoing ofs ty ∈ regs_of_rpairs (locArguments cfg s) →
      zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty))
        (size_arguments cfg s)

/-! ## Location of function parameters -/

def parameter_of_argument : loc → loc
  | .S .Outgoing n ty => .S .Incoming n ty
  | l => l

def loc_parameters (cfg : CompilerConfig) (s : signature) : List (rpair loc) :=
  (locArguments cfg s).map (map_rpair parameter_of_argument)

def incoming_slot_in_parametersStatement : Prop :=
  ∀ (cfg : CompilerConfig) (ofs : Z) (ty : typ) (sg : signature),
    S Incoming ofs ty ∈ regs_of_rpairs (loc_parameters cfg sg) →
      S Outgoing ofs ty ∈ regs_of_rpairs (locArguments cfg sg)

/-! ## Tail calls -/

def tailcall_possible (cfg : CompilerConfig) (s : signature) : Prop :=
  ∀ l, l ∈ regs_of_rpairs (locArguments cfg s) →
    match l with
    | .R _ => True
    | .S _ _ _ => False

def tailcall_is_possible (cfg : CompilerConfig) (sg : signature) : Bool :=
  listForallb
    (fun l =>
      match l with
      | .R _ => true
      | .S _ _ _ => false)
    (regs_of_rpairs (locArguments cfg sg))

def tailcall_is_possible_correctStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : signature),
    tailcall_is_possible cfg s = true → tailcall_possible cfg s

def zero_size_arguments_tailcall_possibleStatement : Prop :=
  ∀ (cfg : CompilerConfig) (sg : signature),
    size_arguments cfg sg = z0 → tailcall_possible cfg sg

/-! ## Callee-save locations -/

def callee_save_loc (cfg : CompilerConfig) : loc → Prop
  | .R r => isCalleeSave cfg r = true
  | .S sl _ _ => sl ≠ Outgoing

def agree_callee_save (cfg : CompilerConfig) (ls1 ls2 : Locmap.t) : Prop :=
  ∀ l, callee_save_loc cfg l → ls1 l = ls2 l

/-! ## Assigning result locations -/

def locmap_get_set_loc_resultStatement : Prop :=
  ∀ (cfg : CompilerConfig) (sg : signature) (v : val) (rs : Locmap.t)
      (l : loc),
    (match l with
      | .R r => isCalleeSave cfg r = true
      | .S _ _ _ => True) →
      Locmap.setpair (locResult sg) v rs l = rs l

def locmap_get_set_loc_result_callee_saveStatement : Prop :=
  ∀ (cfg : CompilerConfig) (sg : signature) (v : val) (rs : Locmap.t)
      (l : loc),
    callee_save_loc cfg l →
      Locmap.setpair (locResult sg) v rs l = rs l

end CompCert4Lean.Backend.Conventions
