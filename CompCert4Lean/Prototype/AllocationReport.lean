import CompCert4Lean.Prototype.Services

namespace CompCert4Lean.Prototype

open Lean Backend Common.AST Cfrontend

def reportResult {α : Type} : Common.Errors.res α → Except String α
  | .OK value => .ok value
  | .Error errors => .error (errorText errors)

def allocationReport (configuration : Config.CompilerConfig) (inlining : Inlining.InliningConfig)
    (context : Allocator.AllocationContext)
    (source : Csyntax.program) (fresh : SimplExpr.FreshIdentContext) : Except String Json := do
  let options := configuration.options
  let clight ← reportResult (SimplExpr.transl_program fresh source)
  let clight ← reportResult (SimplLocals.transf_program configuration clight)
  let csharp ← reportResult (Cshmgen.transl_program clight)
  let cminor ← reportResult (Cminorgen.transl_program csharp)
  let selected ← reportResult (Selection.sel_program configuration (selectionFor configuration) cminor)
  let rtl ← reportResult (RTLgen.transl_program selected)
  let rtl := if options.optimTailcalls then Tailcall.transf_program configuration rtl else rtl
  let rtl ← reportResult (Inlining.transf_program inlining rtl)
  let rtl := Renumber.transf_program rtl
  let rtl := if options.optimCSE && options.optimConstprop then
    LoopUnroll.transf_program LoopUnroll.acyclic_paths rtl else rtl
  let rtl := if options.optimConstprop then
    Constprop.transf_program configuration rtl else rtl
  let rtl := if options.optimCSE && options.optimConstprop then
    LoopUnroll.transf_program LoopUnroll.small_loops rtl else rtl
  let rtl := if options.optimConstprop then Renumber.transf_program rtl else rtl
  let rtl ← reportResult (if options.optimCSE then CSE.transf_program configuration rtl else .OK rtl)
  let rtl ← reportResult (if options.optimRedundancy then Deadcode.transf_program configuration rtl else .OK rtl)
  let rtl ← reportResult (Unusedglob.transform_program rtl)
  let mut reports := #[]
  for (identifier, definition) in rtl.prog_defs do
    if let .Gfun (.Internal function) := definition then
      let (target, stats) ← Allocator.allocate configuration context function
      let types ← reportResult (RTLtyping.type_function configuration function)
      let _ ← reportResult (Allocation.check_function configuration function target types)
      let moves := (Lib.Maps.PTree.elements target.fn_code).foldl (fun count (_, block) =>
        block.foldl (fun count instruction => match instruction with
          | .Lop .Omove _ _ => count + 1
          | _ => count) count) 0
      reports := reports.push (.mkObj [
        ("identifier", toJson (Allocator.regKey identifier)),
        ("spills", toJson stats.spills), ("reloads", toJson stats.reloads),
        ("moves", toJson moves), ("stackWords", toJson stats.stackWords),
        ("rounds", toJson stats.rounds), ("reloadsReused", toJson stats.reloadsReused),
        ("coalesced", toJson stats.coalesced), ("movesRemoved", toJson stats.movesRemoved)])
  return .arr reports

end CompCert4Lean.Prototype
