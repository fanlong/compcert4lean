import CompCert4Lean.Config
import CompCert4Lean.Driver.Compopts
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Cfrontend.Csyntax
import CompCert4Lean.Cfrontend.Clight
import CompCert4Lean.Cfrontend.Csem
import CompCert4Lean.Cfrontend.Cstrategy
import CompCert4Lean.Cfrontend.SimplExpr
import CompCert4Lean.Cfrontend.SimplLocals
import CompCert4Lean.Cfrontend.Cshmgen
import CompCert4Lean.Cfrontend.Cminorgen
import CompCert4Lean.Cfrontend.SimplExprproof
import CompCert4Lean.Cfrontend.SimplLocalsproof
import CompCert4Lean.Cfrontend.Cshmgenproof
import CompCert4Lean.Cfrontend.Cminorgenproof
import CompCert4Lean.Backend.Cminor
import CompCert4Lean.Backend.CminorSel
import CompCert4Lean.Backend.Selection
import CompCert4Lean.Backend.RTLgen
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Backend.LTL
import CompCert4Lean.Backend.Linear
import CompCert4Lean.Backend.Mach
import CompCert4Lean.Backend.Tailcall
import CompCert4Lean.Backend.Inlining
import CompCert4Lean.Backend.Renumber
import CompCert4Lean.Backend.Constprop
import CompCert4Lean.Backend.CSE
import CompCert4Lean.Backend.Deadcode
import CompCert4Lean.Backend.Unusedglob
import CompCert4Lean.Backend.Allocation
import CompCert4Lean.Backend.Tunneling
import CompCert4Lean.Backend.Linearize
import CompCert4Lean.Backend.CleanupLabels
import CompCert4Lean.Backend.Debugvar
import CompCert4Lean.Backend.Stacking
import CompCert4Lean.Backend.Selectionproof
import CompCert4Lean.Backend.RTLgenproof
import CompCert4Lean.Backend.Tailcallproof
import CompCert4Lean.Backend.Inliningproof
import CompCert4Lean.Backend.Renumberproof
import CompCert4Lean.Backend.Constpropproof
import CompCert4Lean.Backend.CSEproof
import CompCert4Lean.Backend.Deadcodeproof
import CompCert4Lean.Backend.Unusedglobproof
import CompCert4Lean.Backend.Allocproof
import CompCert4Lean.Backend.Tunnelingproof
import CompCert4Lean.Backend.Linearizeproof
import CompCert4Lean.Backend.CleanupLabelsproof
import CompCert4Lean.Backend.Debugvarproof
import CompCert4Lean.Backend.Stackingproof
import CompCert4Lean.X86.Asm
import CompCert4Lean.X86.Asmgen
import CompCert4Lean.X86.Asmgenproof

/-!
# The compiler driver

This module keeps the compiler pipeline pure.  The five source printer
parameters are transparent `Unit` callbacks; executable diagnostic sinks live
in `CompCert4Lean.Driver.Diagnostics`.
-/

namespace CompCert4Lean.Driver.Compiler

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend
open CompCert4Lean.Backend
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Backend.RTLgen
open CompCert4Lean.X86
open CompCert4Lean.X86.Asmgen

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev BexactInverseCertificate :=
  CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private def ofString (s : String) : RocqString :=
  (String.toUTF8 s).toList.foldr
    (fun byte tail => .String byte tail) .EmptyString

/-! ## The source printer parameters -/

def print_Clight (_ : Clight.program) : Unit := ()
def print_Cminor (_ : Cminor.program) : Unit := ()
def print_RTL (_ : Z) (_ : RTL.program) : Unit := ()
def print_LTL (_ : LTL.program) : Unit := ()
def print_Mach (_ : Mach.program) : Unit := ()

/-! ## Generic driver combinators -/

def print {A : Type} (printer : A → Unit) (prog : A) : A :=
  let _ := printer prog
  prog

def time {A B : Type} (_name : RocqString) (f : A → B) : A → B := f

def total_if {A : Type} (flag : Unit → Bool) (f : A → A) (prog : A) : A :=
  if flag () then f prog else prog

def partial_if {A : Type} (flag : Unit → Bool) (f : A → Res A) (prog : A) : Res A :=
  if flag () then f prog else .OK prog

def match_if {A : Type} (flag : Unit → Bool) (rel : A → A → Prop) : A → A → Prop :=
  if flag () then rel else Eq

private def mapRes {A B : Type} (x : Res A) (f : A → B) : Res B :=
  match x with
  | .Error message => .Error message
  | .OK value => .OK (f value)

private def bindRes {A B : Type} (x : Res A) (f : A → Res B) : Res B :=
  match x with
  | .Error message => .Error message
  | .OK value => f value

/-! ## Executable pass pipelines -/

def transf_rtl_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (inlineCfg : Inlining.InliningConfig)
    (oracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (f : RTL.program) : Res Asm.program :=
  let p0 : Res RTL.program := .OK f
  let p1 := mapRes p0 (print (print_RTL (ZArith.BinInt.Z.of_nat 0)))
  let p2 := mapRes p1
    (total_if (fun _ => Compopts.optim_tailcalls cfg)
      (time (ofString "Tail calls") (Tailcall.transf_program cfg)))
  let p3 := mapRes p2 (print (print_RTL (ZArith.BinInt.Z.of_nat 1)))
  let p4 := bindRes p3 (time (ofString "Inlining") (Inlining.transf_program inlineCfg))
  let p5 := mapRes p4 (print (print_RTL (ZArith.BinInt.Z.of_nat 2)))
  let p6 := mapRes p5 (time (ofString "Renumbering") Renumber.transf_program)
  let p7 := mapRes p6 (print (print_RTL (ZArith.BinInt.Z.of_nat 3)))
  let p8 := mapRes p7
    (total_if (fun _ => Compopts.optim_constprop cfg)
      (time (ofString "Constant propagation")
        (Constprop.transf_program
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)))
  let p9 := mapRes p8 (print (print_RTL (ZArith.BinInt.Z.of_nat 4)))
  let p10 := mapRes p9
    (total_if (fun _ => Compopts.optim_constprop cfg)
      (time (ofString "Renumbering") Renumber.transf_program))
  let p11 := mapRes p10 (print (print_RTL (ZArith.BinInt.Z.of_nat 5)))
  let p12 := bindRes p11
    (partial_if (fun _ => Compopts.optim_CSE cfg)
      (time (ofString "CSE")
        (CSE.transf_program
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)))
  let p13 := mapRes p12 (print (print_RTL (ZArith.BinInt.Z.of_nat 6)))
  let p14 := bindRes p13
    (partial_if (fun _ => Compopts.optim_redundancy cfg)
      (time (ofString "Redundancy elimination")
        (Deadcode.transf_program
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)))
  let p15 := mapRes p14 (print (print_RTL (ZArith.BinInt.Z.of_nat 7)))
  let p16 := bindRes p15 (time (ofString "Unused globals") Unusedglob.transform_program)
  let p17 := mapRes p16 (print (print_RTL (ZArith.BinInt.Z.of_nat 8)))
  let p18 := bindRes p17 (time (ofString "Register allocation") (Allocation.transf_program cfg oracle))
  let p19 := mapRes p18 (print print_LTL)
  let p20 := mapRes p19 (time (ofString "Branch tunneling") Tunneling.tunnel_program)
  let p21 := bindRes p20
    (time (ofString "CFG linearization")
      (Linearize.transf_program enumerationService))
  let p22 := mapRes p21 (time (ofString "Label cleanup") CleanupLabels.transf_program)
  let p23 := bindRes p22
    (partial_if (fun _ => Compopts.debug cfg)
      (time (ofString "Debugging info for local variables") (Debugvar.transf_program cfg)))
  let p24 := bindRes p23 (time (ofString "Mach generation") (Stacking.transf_program cfg))
  let p25 := mapRes p24 (print print_Mach)
  bindRes p25 (time (ofString "Asm generation") Asmgen.transf_program)

def transf_cminor_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (p : Cminor.program) : Res Asm.program :=
  let p0 : Res Cminor.program := .OK p
  let p1 := mapRes p0 (print print_Cminor)
  let p2 := bindRes p1
    (time (ofString "Instruction selection")
      (Selection.sel_program
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg selectionOracle))
  let p3 := bindRes p2 (time (ofString "RTL generation") RTLgen.transl_program)
  bindRes p3
    (transf_rtl_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg inlineCfg regallocOracle enumerationService)

def transf_clight_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (p : Clight.program) : Res Asm.program :=
  let p0 : Res Clight.program := .OK p
  let p1 := mapRes p0 (print print_Clight)
  let p2 := bindRes p1 (time (ofString "Simplification of locals") (SimplLocals.transf_program cfg))
  let p3 := bindRes p2 (time (ofString "C#minor generation") Cshmgen.transl_program)
  let p4 := bindRes p3 (time (ofString "Cminor generation") Cminorgen.transl_program)
  bindRes p4
    (transf_cminor_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService)

def transf_c_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (ctx : SimplExpr.FreshIdentContext)
    (p : Csyntax.program) : Res CompCert4Lean.X86.Asm.program :=
  let p1 := SimplExpr.transl_program
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) ctx p
  bindRes p1
    (transf_clight_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService)

/-! ## Relational compiler surface -/

/- The pass list is represented by its source-shaped composed matching
   relation.  The individual simulation proofs remain statement descriptors in
   the later proof-migration phase. -/
def CompCert's_passes
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (p : Csyntax.program) (tp : Asm.program) : Prop :=
  ∃ p1 : Clight.program,
  ∃ p2 : Clight.program,
  ∃ p3 : Csharpminor.program,
  ∃ p4 : Cminor.program,
  ∃ p5 : CminorSel.program,
  ∃ p6 : RTL.program,
  ∃ p7 : RTL.program,
  ∃ p8 : RTL.program,
  ∃ p9 : RTL.program,
  ∃ p10 : RTL.program,
  ∃ p11 : RTL.program,
  ∃ p12 : RTL.program,
  ∃ p13 : RTL.program,
  ∃ p14 : RTL.program,
  ∃ p15 : LTL.program,
  ∃ p16 : LTL.program,
  ∃ p17 : Linear.program,
  ∃ p18 : Linear.program,
  ∃ p19 : Linear.program,
  ∃ p20 : Mach.program,
    SimplExprproof.match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) p p1 ∧
    SimplLocalsproof.match_prog cfg p1 p2 ∧
    Cshmgenproof.match_prog p2 p3 ∧
    Cminorgenproof.match_prog p3 p4 ∧
    Selectionproof.match_prog cfg selectionOracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) p4 p5 ∧
    RTLgenproof.match_prog p5 p6 ∧
    match_if (fun _ => Compopts.optim_tailcalls cfg)
      (Tailcallproof.match_prog cfg) p6 p7 ∧
    Inliningproof.match_prog inlineCfg p7 p8 ∧
    Renumberproof.match_prog p8 p9 ∧
    match_if (fun _ => Compopts.optim_constprop cfg)
      (Constpropproof.match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg) p9 p10 ∧
    match_if (fun _ => Compopts.optim_constprop cfg)
      Renumberproof.match_prog p10 p11 ∧
    match_if (fun _ => Compopts.optim_CSE cfg)
      (CSEproof.match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg) p11 p12 ∧
    match_if (fun _ => Compopts.optim_redundancy cfg)
      (Deadcodeproof.match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg) p12 p13 ∧
    Unusedglobproof.match_prog p13 p14 ∧
    Allocproof.match_prog cfg regallocOracle p14 p15 ∧
    Tunnelingproof.match_prog p15 p16 ∧
    Linearizeproof.match_prog enumerationService p16 p17 ∧
    CleanupLabelsproof.match_prog p17 p18 ∧
    match_if (fun _ => Compopts.debug cfg)
      (Debugvarproof.match_prog cfg) p18 p19 ∧
    Stackingproof.match_prog cfg p19 p20 ∧
    Asmgenproof.match_prog p20 tp

def match_prog
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig) (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (p : Csyntax.program) (tp : Asm.program) : Prop :=
  CompCert's_passes
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (binary64_inverse_certificate := binary64_inverse_certificate)
    (binary32_inverse_certificate := binary32_inverse_certificate)
    cfg selectionOracle inlineCfg regallocOracle enumerationService p tp

/-! ## Exact statement descriptors for the later proof phase -/

def print_identityStatement : Prop :=
  ∀ {A : Type} (printer : A → Unit) (prog : A),
    print printer prog = prog

def compose_print_identityStatement : Prop :=
  ∀ {A : Type} (x : Res A) (f : A → Unit),
    mapRes x (print f) = x

def total_if_matchStatement : Prop :=
  ∀ {A : Type} (flag : Unit → Bool) (f : A → A)
    (rel : A → A → Prop) (prog : A),
    (∀ p, rel p (f p)) →
    rel prog (total_if flag f prog)

def partial_if_matchStatement : Prop :=
  ∀ {A : Type} (flag : Unit → Bool) (f : A → Res A)
    (rel : A → A → Prop) (prog tprog : A),
    (∀ p tp, f p = .OK tp → rel p tp) →
    partial_if flag f prog = .OK tprog →
    rel prog tprog

def transf_c_program_matchStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig) (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (ctx : SimplExpr.FreshIdentContext) (p : Csyntax.program) (tp : Asm.program),
    transf_c_program
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg selectionOracle inlineCfg regallocOracle enumerationService ctx p = .OK tp →
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService p tp

def forward_simulation_identityStatement : Prop :=
  ∀ (sem : semantics), forward_simulation sem sem

def match_if_simulationStatement : Prop :=
  ∀ {A : Type} (sem : A → semantics) (flag : Unit → Bool)
    (transf : A → A → Prop) (prog tprog : A),
    match_if flag transf prog tprog →
    (∀ p tp, transf p tp → forward_simulation (sem p) (sem tp)) →
    forward_simulation (sem prog) (sem tprog)

def cstrategy_semantic_preservationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig) (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (xi : ExternalCalls)
    (p : Csyntax.program) (tp : Asm.program),
    match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg selectionOracle inlineCfg regallocOracle enumerationService p tp →
    forward_simulation
      (Cstrategy.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi p)
      (Asm.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi tp) ∧
    backward_simulation
      (atomic (Cstrategy.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi p))
      (Asm.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi tp)

def c_semantic_preservationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig) (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (xi : ExternalCalls)
    (p : Csyntax.program) (tp : Asm.program),
    match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg selectionOracle inlineCfg regallocOracle enumerationService p tp →
    backward_simulation
      (Csem.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi p)
      (Asm.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi tp)

def transf_c_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig) (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (ctx : SimplExpr.FreshIdentContext) (xi : ExternalCalls)
    (p : Csyntax.program) (tp : Asm.program),
    transf_c_program
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg selectionOracle inlineCfg regallocOracle enumerationService ctx p = .OK tp →
    backward_simulation
      (Csem.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi p)
      (Asm.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi tp)

end CompCert4Lean.Driver.Compiler
