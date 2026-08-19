import CompCert4Lean.Backend.CSEdomain
import CompCert4Lean.X86.Op

/-!
# Combined x86 operations and addressing modes

Definition-bearing translation of CompCert's `x86/CombineOp.v`.  Only the
three declarations assigned to this module are exported; the address-folding
branches remain local implementation detail of `combine_addr`.
-/

namespace CompCert4Lean.X86.CombineOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.X86.Op

private abbrev positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
private abbrev condition := CompCert4Lean.X86.Op.condition
private abbrev addressing := CompCert4Lean.X86.Op.addressing
private abbrev rhs := CompCert4Lean.Backend.CSEdomain.rhs

def valnum : Type := positive

def combine_cond' (cond : condition) (args : List valnum) : Option Bool :=
  match cond with
  | .Ccomp c | .Ccompu c | .Ccompl c | .Ccomplu c =>
      match args with
      | [x, y] => CompCert4Lean.Backend.CSEdomain.combine_comparison c x y
      | _ => none
  | _ => none

def combine_addr (get : valnum → Option rhs) (addr : addressing)
    (args : List valnum) : Option (addressing × List valnum) :=
  if CompCert4Lean.X86_64.Archi.ptr64 then
    match addr, args with
    | .Aindexed n, [x] =>
        match get x with
        | some (.Op (.Oleal a) ys) =>
            match CompCert4Lean.X86.Op.offset_addressing a n with
            | some a' => some (a', ys)
            | none => none
        | _ => none
    | _, _ => none
  else
    match addr, args with
    | .Aindexed n, [x] =>
        match get x with
        | some (.Op (.Olea a) ys) =>
            match CompCert4Lean.X86.Op.offset_addressing a n with
            | some a' => some (a', ys)
            | none => none
        | _ => none
    | _, _ => none

end CompCert4Lean.X86.CombineOp
