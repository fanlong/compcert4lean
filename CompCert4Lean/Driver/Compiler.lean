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

def apply_total (A B : Type) (x : Res A) (f : A → B) : Res B :=
  match x with
  | .Error message => .Error message
  | .OK value => .OK (f value)

def apply_partial (A B : Type) (x : Res A) (f : A → Res B) : Res B :=
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
  let p1 := apply_total _ _ p0 (print (print_RTL (ZArith.BinInt.Z.of_nat 0)))
  let p2 := apply_total _ _ p1
    (total_if (fun _ => Compopts.optim_tailcalls cfg)
      (time (ofString "Tail calls") (Tailcall.transf_program cfg)))
  let p3 := apply_total _ _ p2 (print (print_RTL (ZArith.BinInt.Z.of_nat 1)))
  let p4 := apply_partial _ _ p3 (time (ofString "Inlining") (Inlining.transf_program inlineCfg))
  let p5 := apply_total _ _ p4 (print (print_RTL (ZArith.BinInt.Z.of_nat 2)))
  let p6 := apply_total _ _ p5 (time (ofString "Renumbering") Renumber.transf_program)
  let p7 := apply_total _ _ p6 (print (print_RTL (ZArith.BinInt.Z.of_nat 3)))
  let p8 := apply_total _ _ p7
    (total_if (fun _ => Compopts.optim_constprop cfg)
      (time (ofString "Constant propagation")
        (Constprop.transf_program
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)))
  let p9 := apply_total _ _ p8 (print (print_RTL (ZArith.BinInt.Z.of_nat 4)))
  let p10 := apply_total _ _ p9
    (total_if (fun _ => Compopts.optim_constprop cfg)
      (time (ofString "Renumbering") Renumber.transf_program))
  let p11 := apply_total _ _ p10 (print (print_RTL (ZArith.BinInt.Z.of_nat 5)))
  let p12 := apply_partial _ _ p11
    (partial_if (fun _ => Compopts.optim_CSE cfg)
      (time (ofString "CSE")
        (CSE.transf_program
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)))
  let p13 := apply_total _ _ p12 (print (print_RTL (ZArith.BinInt.Z.of_nat 6)))
  let p14 := apply_partial _ _ p13
    (partial_if (fun _ => Compopts.optim_redundancy cfg)
      (time (ofString "Redundancy elimination")
        (Deadcode.transf_program
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)))
  let p15 := apply_total _ _ p14 (print (print_RTL (ZArith.BinInt.Z.of_nat 7)))
  let p16 := apply_partial _ _ p15 (time (ofString "Unused globals") Unusedglob.transform_program)
  let p17 := apply_total _ _ p16 (print (print_RTL (ZArith.BinInt.Z.of_nat 8)))
  let p18 := apply_partial _ _ p17 (time (ofString "Register allocation") (Allocation.transf_program cfg oracle))
  let p19 := apply_total _ _ p18 (print print_LTL)
  let p20 := apply_total _ _ p19 (time (ofString "Branch tunneling") Tunneling.tunnel_program)
  let p21 := apply_partial _ _ p20
    (time (ofString "CFG linearization")
      (Linearize.transf_program enumerationService))
  let p22 := apply_total _ _ p21 (time (ofString "Label cleanup") CleanupLabels.transf_program)
  let p23 := apply_partial _ _ p22
    (partial_if (fun _ => Compopts.debug cfg)
      (time (ofString "Debugging info for local variables") (Debugvar.transf_program cfg)))
  let p24 := apply_partial _ _ p23 (time (ofString "Mach generation") (Stacking.transf_program cfg))
  let p25 := apply_total _ _ p24 (print print_Mach)
  apply_partial _ _ p25 (time (ofString "Asm generation") Asmgen.transf_program)

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
  let p1 := apply_total _ _ p0 (print print_Cminor)
  let p2 := apply_partial _ _ p1
    (time (ofString "Instruction selection")
      (Selection.sel_program
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg selectionOracle))
  let p3 := apply_partial _ _ p2 (time (ofString "RTL generation") RTLgen.transl_program)
  apply_partial _ _ p3
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
  let p1 := apply_total _ _ p0 (print print_Clight)
  let p2 := apply_partial _ _ p1 (time (ofString "Simplification of locals") (SimplLocals.transf_program cfg))
  let p3 := apply_partial _ _ p2 (time (ofString "C#minor generation") Cshmgen.transl_program)
  let p4 := apply_partial _ _ p3 (time (ofString "Cminor generation") Cminorgen.transl_program)
  apply_partial _ _ p4
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
  let p0 : Res Csyntax.program := .OK p
  let p1 := apply_partial _ _ p0
    (time (ofString "Clight generation")
      (SimplExpr.transl_program
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ctx))
  apply_partial _ _ p1
    (transf_clight_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService)

/-! ## Relational compiler surface -/

/-! The source pass list is typed by the language linker carried by each
   `Pass`.  Csyntax and Clight use the certified Ctypes program linkers; the
   remaining AST program linkers are the generic source linkers.  The
   `TransfLink` fields below are companion obligations: their propositions are
   preserved now and their proof terms are supplied by the later proof phase.
-/

private def csyntaxLanguage
    (certificate : Ctypes.Linker_program_obligations) : Language where
  lang_prog := Csyntax.program
  lang_link := Ctypes.Linker_program Csyntax.function certificate

private def clightLanguage
    (certificate : Ctypes.Linker_program_obligations) : Language where
  lang_prog := Clight.program
  lang_link := Ctypes.Linker_program Clight.function certificate

private def csharpminorLinker : Linker Csharpminor.program :=
  @Linker_prog Csharpminor.fundef Unit
    (Linker_fundef Csharpminor.function) Linker_unit

private def cminorLinker : Linker Cminor.program :=
  @Linker_prog Cminor.fundef Unit
    (Linker_fundef Cminor.function) Linker_unit

private def cminorSelLinker : Linker CminorSel.program :=
  @Linker_prog CminorSel.fundef Unit
    (Linker_fundef CminorSel.function) Linker_unit

private def rtlLinker : Linker RTL.program :=
  @Linker_prog RTL.fundef Unit
    (Linker_fundef RTL.function) Linker_unit

private def ltlLinker : Linker LTL.program :=
  @Linker_prog LTL.fundef Unit
    (Linker_fundef LTL.function) Linker_unit

private def linearLinker : Linker Linear.program :=
  @Linker_prog Linear.fundef Unit
    (Linker_fundef Linear.function) Linker_unit

private def machLinker : Linker Mach.program :=
  @Linker_prog Mach.fundef Unit
    (Linker_fundef Mach.function) Linker_unit

private def asmLinker : Linker Asm.program :=
  @Linker_prog Asm.fundef Unit
    (Linker_fundef Asm.function) Linker_unit

private def csharpminorLanguage : Language where
  lang_prog := Csharpminor.program
  lang_link := csharpminorLinker

private def cminorLanguage : Language where
  lang_prog := Cminor.program
  lang_link := cminorLinker

private def cminorSelLanguage : Language where
  lang_prog := CminorSel.program
  lang_link := cminorSelLinker

private def rtlLanguage : Language where
  lang_prog := RTL.program
  lang_link := rtlLinker

private def ltlLanguage : Language where
  lang_prog := LTL.program
  lang_link := ltlLinker

private def linearLanguage : Language where
  lang_prog := Linear.program
  lang_link := linearLinker

private def machLanguage : Language where
  lang_prog := Mach.program
  lang_link := machLinker

private def asmLanguage : Language where
  lang_prog := Asm.program
  lang_link := asmLinker

def TransfIfLink {A : Type} {LA : Linker A}
    (flag : Unit → Bool) (transf : A → A → Prop)
    (TL : TransfLink transf) : TransfLink (match_if flag transf) where
  transf_link := by
    unfold match_if
    split
    · exact TL.transf_link
    · intro p1 p2 tp1 tp2 p h hp1 hp2
      subst tp1
      subst tp2
      exact ⟨p, h, rfl⟩

structure CompilerPassCertificates
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (csyntaxLinkerCertificate : Ctypes.Linker_program_obligations)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations) : Prop where
  simplExpr :
    @TransfLink Csyntax.program Clight.program
      (Ctypes.Linker_program Csyntax.function csyntaxLinkerCertificate)
      (Ctypes.Linker_program Clight.function clightLinkerCertificate)
      (fun p tp => SimplExprproof.match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) p tp)
  simplLocals :
    @TransfLink Clight.program Clight.program
      (Ctypes.Linker_program Clight.function clightLinkerCertificate)
      (Ctypes.Linker_program Clight.function clightLinkerCertificate)
      (SimplLocalsproof.match_prog cfg)
  cshmgen :
    @TransfLink Clight.program Csharpminor.program
      (Ctypes.Linker_program Clight.function clightLinkerCertificate)
      csharpminorLinker
      Cshmgenproof.match_prog
  cminorgen :
    @TransfLink Csharpminor.program Cminor.program
      csharpminorLinker
      cminorLinker
      Cminorgenproof.match_prog
  selection :
    @TransfLink Cminor.program CminorSel.program
      cminorLinker
      cminorSelLinker
      (fun p tp => Selectionproof.match_prog
        cfg selectionOracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) p tp)
  rtlgen :
    @TransfLink CminorSel.program RTL.program
      cminorSelLinker
      rtlLinker
      RTLgenproof.match_prog
  tailcall :
    @TransfLink RTL.program RTL.program
      rtlLinker
      rtlLinker
      (Tailcallproof.match_prog cfg)
  inlining :
    @TransfLink RTL.program RTL.program
      rtlLinker
      rtlLinker
      (Inliningproof.match_prog inlineCfg)
  renumber :
    @TransfLink RTL.program RTL.program
      rtlLinker
      rtlLinker
      Renumberproof.match_prog
  constprop :
    @TransfLink RTL.program RTL.program
      rtlLinker
      rtlLinker
      (Constpropproof.match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg)
  renumberConstprop :
    @TransfLink RTL.program RTL.program
      rtlLinker
      rtlLinker
      Renumberproof.match_prog
  cse :
    @TransfLink RTL.program RTL.program
      rtlLinker
      rtlLinker
      (CSEproof.match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg)
  deadcode :
    @TransfLink RTL.program RTL.program
      rtlLinker
      rtlLinker
      (Deadcodeproof.match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg)
  unusedglob :
    Unusedglobproof.TransfSelectionLinkStatement
  allocation :
    @TransfLink RTL.program LTL.program
      rtlLinker
      ltlLinker
      (Allocproof.match_prog cfg regallocOracle)
  tunneling :
    @TransfLink LTL.program LTL.program
      ltlLinker
      ltlLinker
      Tunnelingproof.match_prog
  linearize :
    @TransfLink LTL.program Linear.program
      ltlLinker
      linearLinker
      (Linearizeproof.match_prog enumerationService)
  cleanupLabels :
    @TransfLink Linear.program Linear.program
      linearLinker
      linearLinker
      CleanupLabelsproof.match_prog
  debugvar :
    @TransfLink Linear.program Linear.program
      linearLinker
      linearLinker
      (Debugvarproof.match_prog cfg)
  stacking :
    @TransfLink Linear.program Mach.program
      linearLinker
      machLinker
      (Stackingproof.match_prog cfg)
  asmgen :
    @TransfLink Mach.program Asm.program
      machLinker
      asmLinker
      Asmgenproof.match_prog

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
    (csyntaxLinkerCertificate : Ctypes.Linker_program_obligations)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations)
    (passCertificates : CompilerPassCertificates
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService
      csyntaxLinkerCertificate clightLinkerCertificate) :
    Passes (csyntaxLanguage csyntaxLinkerCertificate) (asmLanguage) :=
  let pass1 : Pass (csyntaxLanguage csyntaxLinkerCertificate)
      (clightLanguage clightLinkerCertificate) :=
    { pass_match := fun p tp => SimplExprproof.match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) p tp
      pass_match_link := passCertificates.simplExpr }
  let pass2 : Pass (clightLanguage clightLinkerCertificate)
      (clightLanguage clightLinkerCertificate) :=
    { pass_match := SimplLocalsproof.match_prog cfg
      pass_match_link := passCertificates.simplLocals }
  let pass3 : Pass (clightLanguage clightLinkerCertificate)
      csharpminorLanguage :=
    { pass_match := Cshmgenproof.match_prog
      pass_match_link := passCertificates.cshmgen }
  let pass4 : Pass csharpminorLanguage cminorLanguage :=
    { pass_match := Cminorgenproof.match_prog
      pass_match_link := passCertificates.cminorgen }
  let pass5 : Pass cminorLanguage cminorSelLanguage :=
    { pass_match := fun p tp => Selectionproof.match_prog cfg selectionOracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) p tp
      pass_match_link := passCertificates.selection }
  let pass6 : Pass cminorSelLanguage rtlLanguage :=
    { pass_match := RTLgenproof.match_prog
      pass_match_link := passCertificates.rtlgen }
  let pass7 : Pass rtlLanguage rtlLanguage :=
    { pass_match := match_if (fun _ => Compopts.optim_tailcalls cfg)
        (Tailcallproof.match_prog cfg)
      pass_match_link := @TransfIfLink RTL.program rtlLinker
        (fun _ => Compopts.optim_tailcalls cfg)
        (Tailcallproof.match_prog cfg) passCertificates.tailcall }
  let pass8 : Pass rtlLanguage rtlLanguage :=
    { pass_match := Inliningproof.match_prog inlineCfg
      pass_match_link := passCertificates.inlining }
  let pass9 : Pass rtlLanguage rtlLanguage :=
    { pass_match := Renumberproof.match_prog
      pass_match_link := passCertificates.renumber }
  let pass10 : Pass rtlLanguage rtlLanguage :=
    { pass_match := match_if (fun _ => Compopts.optim_constprop cfg)
        (Constpropproof.match_prog
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)
      pass_match_link := @TransfIfLink RTL.program rtlLinker
        (fun _ => Compopts.optim_constprop cfg)
        (Constpropproof.match_prog
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)
        passCertificates.constprop }
  let pass11 : Pass rtlLanguage rtlLanguage :=
    { pass_match := match_if (fun _ => Compopts.optim_constprop cfg)
        Renumberproof.match_prog
      pass_match_link := @TransfIfLink RTL.program rtlLinker
        (fun _ => Compopts.optim_constprop cfg)
        Renumberproof.match_prog passCertificates.renumberConstprop }
  let pass12 : Pass rtlLanguage rtlLanguage :=
    { pass_match := match_if (fun _ => Compopts.optim_CSE cfg)
        (CSEproof.match_prog
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)
      pass_match_link := @TransfIfLink RTL.program rtlLinker
        (fun _ => Compopts.optim_CSE cfg)
        (CSEproof.match_prog
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)
        passCertificates.cse }
  let pass13 : Pass rtlLanguage rtlLanguage :=
    { pass_match := match_if (fun _ => Compopts.optim_redundancy cfg)
        (Deadcodeproof.match_prog
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)
      pass_match_link := @TransfIfLink RTL.program rtlLinker
        (fun _ => Compopts.optim_redundancy cfg)
        (Deadcodeproof.match_prog
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg)
        passCertificates.deadcode }
  let pass14 : Pass rtlLanguage rtlLanguage :=
    { pass_match := Unusedglobproof.match_prog
      pass_match_link := passCertificates.unusedglob }
  let pass15 : Pass rtlLanguage ltlLanguage :=
    { pass_match := Allocproof.match_prog cfg regallocOracle
      pass_match_link := passCertificates.allocation }
  let pass16 : Pass ltlLanguage ltlLanguage :=
    { pass_match := Tunnelingproof.match_prog
      pass_match_link := passCertificates.tunneling }
  let pass17 : Pass ltlLanguage linearLanguage :=
    { pass_match := Linearizeproof.match_prog enumerationService
      pass_match_link := passCertificates.linearize }
  let pass18 : Pass linearLanguage linearLanguage :=
    { pass_match := CleanupLabelsproof.match_prog
      pass_match_link := passCertificates.cleanupLabels }
  let pass19 : Pass linearLanguage linearLanguage :=
    { pass_match := match_if (fun _ => Compopts.debug cfg)
        (Debugvarproof.match_prog cfg)
      pass_match_link := @TransfIfLink Linear.program linearLinker
        (fun _ => Compopts.debug cfg)
        (Debugvarproof.match_prog cfg) passCertificates.debugvar }
  let pass20 : Pass linearLanguage machLanguage :=
    { pass_match := Stackingproof.match_prog cfg
      pass_match_link := passCertificates.stacking }
  let pass21 : Pass machLanguage asmLanguage :=
    { pass_match := Asmgenproof.match_prog
      pass_match_link := passCertificates.asmgen }
  pass_cons pass1 (pass_cons pass2 (pass_cons pass3 (pass_cons pass4
    (pass_cons pass5 (pass_cons pass6 (pass_cons pass7 (pass_cons pass8
      (pass_cons pass9 (pass_cons pass10 (pass_cons pass11 (pass_cons pass12
        (pass_cons pass13 (pass_cons pass14 (pass_cons pass15 (pass_cons pass16
          (pass_cons pass17 (pass_cons pass18 (pass_cons pass19 (pass_cons pass20
            (pass_cons pass21 (pass_nil asmLanguage)))))))))))))))))))))

def match_prog
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig) (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (csyntaxLinkerCertificate : Ctypes.Linker_program_obligations)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations)
    (passCertificates : CompilerPassCertificates
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService
      csyntaxLinkerCertificate clightLinkerCertificate)
    (p : Csyntax.program) (tp : Asm.program) : Prop :=
  pass_match (compose_passes (CompCert's_passes
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (binary64_inverse_certificate := binary64_inverse_certificate)
    (binary32_inverse_certificate := binary32_inverse_certificate)
    cfg selectionOracle inlineCfg regallocOracle enumerationService
    csyntaxLinkerCertificate clightLinkerCertificate passCertificates)) p tp

/-! ## Exact statement descriptors for the later proof phase -/

def print_identityStatement : Prop :=
  ∀ (A : Type) (printer : A → Unit) (prog : A),
    print printer prog = prog

def compose_print_identityStatement : Prop :=
  ∀ (A : Type) (x : Res A) (f : A → Unit),
    apply_total _ _ x (print f) = x

def total_if_matchStatement : Prop :=
  ∀ (A : Type) (flag : Unit → Bool) (f : A → A)
    (rel : A → A → Prop) (prog : A),
    (∀ p, rel p (f p)) →
    match_if flag rel prog (total_if flag f prog)

def partial_if_matchStatement : Prop :=
  ∀ (A : Type) (flag : Unit → Bool) (f : A → Res A)
    (rel : A → A → Prop) (prog tprog : A),
    (∀ p tp, f p = .OK tp → rel p tp) →
    partial_if flag f prog = .OK tprog →
    match_if flag rel prog tprog

def transf_c_program_matchStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig) (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (csyntaxLinkerCertificate : Ctypes.Linker_program_obligations)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations)
    (passCertificates : CompilerPassCertificates
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService
      csyntaxLinkerCertificate clightLinkerCertificate)
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
      cfg selectionOracle inlineCfg regallocOracle enumerationService
      csyntaxLinkerCertificate clightLinkerCertificate passCertificates p tp

def forward_simulation_identityStatement : Prop :=
  ∀ (sem : semantics), forward_simulation sem sem

def match_if_simulationStatement : Prop :=
  ∀ (A : Type) (sem : A → semantics) (flag : Unit → Bool)
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
    (csyntaxLinkerCertificate : Ctypes.Linker_program_obligations)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations)
    (passCertificates : CompilerPassCertificates
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService
      csyntaxLinkerCertificate clightLinkerCertificate)
    (xi : ExternalCalls)
    (p : Csyntax.program) (tp : Asm.program),
    match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg selectionOracle inlineCfg regallocOracle enumerationService
        csyntaxLinkerCertificate clightLinkerCertificate passCertificates p tp →
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
    (csyntaxLinkerCertificate : Ctypes.Linker_program_obligations)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations)
    (passCertificates : CompilerPassCertificates
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService
      csyntaxLinkerCertificate clightLinkerCertificate)
    (xi : ExternalCalls)
    (p : Csyntax.program) (tp : Asm.program),
    match_prog
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg selectionOracle inlineCfg regallocOracle enumerationService
        csyntaxLinkerCertificate clightLinkerCertificate passCertificates p tp →
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
    (csyntaxLinkerCertificate : Ctypes.Linker_program_obligations)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations)
    (passCertificates : CompilerPassCertificates
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService
      csyntaxLinkerCertificate clightLinkerCertificate)
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

namespace CompCert4Lean.Driver.Compiler

theorem print_identity : print_identityStatement := by
  intro A printer prog
  rfl

theorem total_if_match : total_if_matchStatement := by
  intro A flag f rel prog h
  unfold match_if total_if
  cases hflag : flag () with
  | false => simp [hflag]
  | true => exact h prog

theorem partial_if_match : partial_if_matchStatement := by
  intro A flag f rel prog tprog hrel hres
  unfold partial_if at hres
  unfold match_if
  cases hflag : flag () with
  | false =>
      simp [hflag] at hres
      cases hres
      rfl
  | true =>
      simp [hflag] at hres
      exact hrel prog tprog hres

theorem forward_simulation_identity : forward_simulation_identityStatement := by
  intro sem
  refine CompCert4Lean.Common.Smallstep.forward_simulation.Forward_simulation
    (order := fun _ _ : Unit => False)
    (match_states := fun _ s1 s2 => s2 = s1) ?_
  have wfFalse : WellFounded (fun _ _ : Unit => False) := by
    exact ⟨fun i => Acc.intro i (by
      intro j h
      exact False.elim h)⟩
  refine {
    fsim_order_wf := wfFalse
    fsim_match_initial_states := by
      intro s1 hs1
      exact ⟨(), s1, hs1, rfl⟩
    fsim_match_final_states := by
      intro i s1 s2 r hmatch hfinal
      cases hmatch
      exact hfinal
    fsim_simulation := by
      intro s1 t s1' hstep i s2 hmatch
      cases hmatch
      refine ⟨(), s1', ?_, rfl⟩
      left
      exact CompCert4Lean.Common.Smallstep.plus_left s1 t hstep
        (CompCert4Lean.Common.Smallstep.star_refl _ _ s1')
        (by exact (List.append_nil t).symm)
    fsim_public_preserved := by
      intro id
      rfl }

end CompCert4Lean.Driver.Compiler

namespace CompCert4Lean.Driver.Compiler

theorem compose_print_identity : compose_print_identityStatement := by
  intro A x f
  cases x with
  | Error message => rfl
  | OK value => rfl

theorem match_if_simulation : match_if_simulationStatement := by
  intro A sem flag transf prog tprog hmatch htrans
  unfold match_if at hmatch
  cases hflag : flag () with
  | true =>
      simp [hflag] at hmatch
      exact htrans prog tprog hmatch
  | false =>
      simp [hflag] at hmatch
      cases hmatch
      exact forward_simulation_identity (sem prog)

end CompCert4Lean.Driver.Compiler
