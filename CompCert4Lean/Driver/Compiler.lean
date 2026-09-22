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

namespace CompCert4Lean.Driver.Compiler

open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend
open CompCert4Lean.Backend
open CompCert4Lean.X86

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem transf_c_program_match
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)] :
    transf_c_program_matchStatement := by
  intro cfg selectionOracle inlineCfg regallocOracle enumerationService
    csyntaxLinkerCertificate clightLinkerCertificate passCertificates ctx prog target compiled
  unfold transf_c_program transf_clight_program transf_cminor_program transf_rtl_program at compiled
  simp only [time, print, apply_total, apply_partial] at compiled
  repeat first
    | contradiction
    | split at *
  all_goals
    simp_all only [CompCert4Lean.Common.Errors.res.OK.injEq]
    subst_vars
    simp only [match_prog, CompCert's_passes, compose_passes, pass_compose,
      pass_identity]
    refine ⟨_, SimplExprproof.transf_program_match ctx _ _ (by assumption), ?_⟩
    refine ⟨_, SimplLocalsproof.match_transf_program cfg _ _ (by assumption), ?_⟩
    refine ⟨_, Cshmgenproof.transf_program_match _ _ (by assumption), ?_⟩
    refine ⟨_, Cminorgenproof.transf_program_match _ _ (by assumption), ?_⟩
    refine ⟨_, Selectionproof.transf_program_match cfg selectionOracle _ _ (by assumption), ?_⟩
    refine ⟨_, RTLgenproof.transf_program_match _ _ (by assumption), ?_⟩
    refine ⟨_, total_if_match _ _ _ _ _ (Tailcallproof.transf_program_match cfg), ?_⟩
    refine ⟨_, Inliningproof.transf_program_match inlineCfg _ _ (by assumption), ?_⟩
    refine ⟨_, Renumberproof.transf_program_match _, ?_⟩
    refine ⟨_, total_if_match _ _ _ _ _ (Constpropproof.transf_program_match cfg), ?_⟩
    refine ⟨_, total_if_match _ _ _ _ _ Renumberproof.transf_program_match, ?_⟩
    refine ⟨_, partial_if_match _ _ _ _ _ _ (CSEproof.transf_program_match cfg) (by assumption), ?_⟩
    refine ⟨_, partial_if_match _ _ _ _ _ _ (Deadcodeproof.transf_program_match cfg) (by assumption), ?_⟩
    refine ⟨_, Unusedglobproof.transf_program_match _ _ (by assumption), ?_⟩
    refine ⟨_, Allocproof.transf_program_match cfg regallocOracle _ _ (by assumption), ?_⟩
    refine ⟨_, Tunnelingproof.transf_program_match _, ?_⟩
    refine ⟨_, Linearizeproof.transf_program_match enumerationService _ _ (by assumption), ?_⟩
    refine ⟨_, CleanupLabelsproof.transf_program_match _, ?_⟩
    refine ⟨_, partial_if_match _ _ _ _ _ _ (Debugvarproof.transf_program_match cfg) (by assumption), ?_⟩
    refine ⟨_, Stackingproof.transf_program_match cfg _ _ (by assumption), ?_⟩
    exact ⟨target, Asmgenproof.transf_program_match _ _ compiled, rfl⟩

end CompCert4Lean.Driver.Compiler

namespace CompCert4Lean.Driver.Compiler

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem compiler_globvar_eq {VarInfo : Type} {sourceVar tv : globvar VarInfo}
    (hypothesis : match_globvar Eq sourceVar tv) : sourceVar = tv := by
  cases hypothesis with
  | match_globvar_intro sourceInfo targetInfo init ro vo hij => cases hij; rfl

private theorem compiler_glob_mono {Context SourceFunction TargetFunction SourceVarInfo TargetVarInfo : Type} [LC : Linker Context]
    (relation : Context → SourceFunction → TargetFunction → Prop)
    (varRelation : SourceVarInfo → TargetVarInfo → Prop) {context nextContext : Context} {global : globdef SourceFunction SourceVarInfo} {tg : globdef TargetFunction TargetVarInfo}
    (hypothesis : match_globdef relation varRelation context global tg) (hcd : LC.linkorder context nextContext) :
    match_globdef relation varRelation nextContext global tg := by
  cases hypothesis with
  | match_globdef_fun context' sourceFunction tf hc hr =>
      exact match_globdef_fun relation varRelation nextContext context' sourceFunction tf
        (LC.linkorder_trans _ _ _ hc hcd) hr
  | match_globdef_var sourceVar tv hv => exact match_globdef_var relation varRelation nextContext sourceVar tv hv

private theorem compiler_link_glob {Context SourceFunction TargetFunction SourceVarInfo TargetVarInfo : Type}
    [LC : Linker Context] [LF : Linker SourceFunction] [LG : Linker TargetFunction] [LV : Linker SourceVarInfo] [LTV : Linker TargetVarInfo]
    (relation : Context → SourceFunction → TargetFunction → Prop)
    (varRelation : SourceVarInfo → TargetVarInfo → Prop)
    (hf : ∀ c1 c2 f1 tf1 f2 tf2 sourceFunction,
      LF.link f1 f2 = some sourceFunction → relation c1 f1 tf1 → relation c2 f2 tf2 →
      ∃ tf, LG.link tf1 tf2 = some tf ∧ (relation c1 sourceFunction tf ∨ relation c2 sourceFunction tf))
    (hv : ∀ source1 source2 source target1 target2,
      link_vardef source1 source2 = some source →
      match_globvar varRelation source1 target1 →
      match_globvar varRelation source2 target2 →
      ∃ target, link_vardef target1 target2 = some target ∧
        match_globvar varRelation source target)
    {c1 c2 context : Context} {g1 g2 global : globdef SourceFunction SourceVarInfo} {tg1 tg2 : globdef TargetFunction TargetVarInfo}
    (hc1 : LC.linkorder c1 context) (hc2 : LC.linkorder c2 context)
    (hl : link_def g1 g2 = some global)
    (h1 : match_globdef relation varRelation c1 g1 tg1)
    (h2 : match_globdef relation varRelation c2 g2 tg2) :
    ∃ tg, link_def tg1 tg2 = some tg ∧ match_globdef relation varRelation context global tg := by
  cases h1 with
  | match_globdef_fun u1 f1 tf1 hu1 hr1 =>
    cases h2 with
    | match_globdef_var sourceVar tv hv => simp [link_def] at hl
    | match_globdef_fun u2 f2 tf2 hu2 hr2 =>
      cases heq : LF.link f1 f2 with
      | none => simp [link_def, heq] at hl
      | some sourceFunction =>
        simp only [link_def, heq, Option.some.injEq] at hl
        subst global
        obtain ⟨tf, ht, hr⟩ := hf u1 u2 f1 tf1 f2 tf2 sourceFunction heq hr1 hr2
        refine ⟨.Gfun tf, by simp [link_def, ht], ?_⟩
        cases hr with
        | inl hr =>
            exact match_globdef_fun relation varRelation context u1 sourceFunction tf
              (LC.linkorder_trans _ _ _ hu1 hc1) hr
        | inr hr =>
            exact match_globdef_fun relation varRelation context u2 sourceFunction tf
              (LC.linkorder_trans _ _ _ hu2 hc2) hr
  | match_globdef_var v1 tv1 hv1 =>
    cases h2 with
    | match_globdef_fun u2 f2 tf2 hu2 hr2 => simp [link_def] at hl
    | match_globdef_var v2 tv2 hv2 =>
      cases heq : link_vardef v1 v2 with
      | none => simp [link_def, heq] at hl
      | some sourceVar =>
        simp only [link_def, heq, Option.some.injEq] at hl
        subst global
        obtain ⟨targetVar, linkedVars, matchedVars⟩ := hv _ _ _ _ _ heq hv1 hv2
        exact ⟨.Gvar targetVar, by simp [link_def, linkedVars],
          match_globdef_var relation varRelation context _ _ matchedVars⟩

private theorem compiler_link_succeeds {SourceFunction VarInfo : Type} [LF : Linker SourceFunction] [LV : Linker VarInfo]
    (p1 p2 : CompCert4Lean.Common.AST.program SourceFunction VarInfo)
    (hm : p1.prog_main = p2.prog_main)
    (hc : ∀ id g1 g2, PTree.get id (prog_defmap p1) = some g1 →
      PTree.get id (prog_defmap p2) = some g2 →
      id ∈ p1.prog_public ∧ id ∈ p2.prog_public ∧ ∃ global, link_def g1 g2 = some global) :
    link_prog p1 p2 = some {
      prog_defs := PTree.elements (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2))
      prog_public := p1.prog_public ++ p2.prog_public
      prog_main := p1.prog_main } := by
  have hall : PTree_Properties.for_all (prog_defmap p1) (link_prog_check p1 p2) = true := by
    apply (PTree_Properties.for_all_correct_proof _ _ _).mpr
    intro id g1 hget1
    unfold link_prog_check
    cases hget2 : PTree.get id (prog_defmap p2) with
    | none => rfl
    | some g2 =>
      obtain ⟨hp1, hp2, global, hg⟩ := hc id g1 g2 hget1 hget2
      cases hd1 : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec peq id p1.prog_public with
      | right hn => exact (hn hp1).elim
      | left _ =>
        cases hd2 : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec peq id p2.prog_public with
        | right hn => exact (hn hp2).elim
        | left _ => simp [hg]
  unfold link_prog
  cases hd : ident_eq p1.prog_main p2.prog_main with
  | right hn => exact (hn hm).elim
  | left _ => simp only [hall, ite_true]




private theorem compiler_option_right {Source Target : Type} {relation : Source → Target → Prop}
    {optional : Option Source} {targetValue : Target} (hypothesis : option_rel relation optional (some targetValue)) :
    ∃ sourceValue, optional = some sourceValue ∧ relation sourceValue targetValue := by
  cases hypothesis with
  | some sourceValue targetValue hr => exact ⟨sourceValue, rfl, hr⟩

private theorem compiler_merge_related {Source Target : Type}
    (r1 r2 relation : Source → Target → Prop)
    (sourceFunction : Option Source → Option Source → Option Source)
    (tf : Option Target → Option Target → Option Target)
    (hnn : sourceFunction none none = none) (htnn : tf none none = none)
    (hnl : ∀ sourceValue, sourceFunction (some sourceValue) none = some sourceValue)
    (htnl : ∀ targetValue, tf (some targetValue) none = some targetValue)
    (hnr : ∀ sourceValue, sourceFunction none (some sourceValue) = some sourceValue)
    (htnr : ∀ targetValue, tf none (some targetValue) = some targetValue)
    (hm1 : ∀ sourceValue targetValue, r1 sourceValue targetValue → relation sourceValue targetValue) (hm2 : ∀ sourceValue targetValue, r2 sourceValue targetValue → relation sourceValue targetValue)
    {o1 o2 : Option Source} {t1 t2 : Option Target}
    (h1 : option_rel r1 o1 t1) (h2 : option_rel r2 o2 t2)
    (hl : ∀ sourceValue targetValue leftTarget rightTarget, o1 = some sourceValue → o2 = some targetValue → r1 sourceValue leftTarget → r2 targetValue rightTarget →
      option_rel relation (sourceFunction (some sourceValue) (some targetValue)) (tf (some leftTarget) (some rightTarget))) :
    option_rel relation (sourceFunction o1 o2) (tf t1 t2) := by
  cases h1 with
  | none =>
    cases h2 with
    | none => rw [hnn, htnn]; exact option_rel.none relation
    | some targetValue rightTarget hr => rw [hnr, htnr]; exact option_rel.some targetValue rightTarget (hm2 targetValue rightTarget hr)
  | some sourceValue leftTarget hr =>
    cases h2 with
    | none => rw [hnl, htnl]; exact option_rel.some sourceValue leftTarget (hm1 sourceValue leftTarget hr)
    | some targetValue rightTarget hr' => exact hl sourceValue targetValue leftTarget rightTarget rfl rfl hr hr'

private theorem compiler_link_ast {Context SourceFunction TargetFunction SourceVarInfo TargetVarInfo : Type}
    [LC : Linker Context] [LF : Linker SourceFunction] [LG : Linker TargetFunction] [LV : Linker SourceVarInfo] [LTV : Linker TargetVarInfo]
    (relation : Context → SourceFunction → TargetFunction → Prop)
    (varRelation : SourceVarInfo → TargetVarInfo → Prop)
    (hf : ∀ c1 c2 f1 tf1 f2 tf2 sourceFunction,
      LF.link f1 f2 = some sourceFunction → relation c1 f1 tf1 → relation c2 f2 tf2 →
      ∃ tf, LG.link tf1 tf2 = some tf ∧ (relation c1 sourceFunction tf ∨ relation c2 sourceFunction tf))
    (hv : ∀ source1 source2 source target1 target2,
      link_vardef source1 source2 = some source →
      match_globvar varRelation source1 target1 →
      match_globvar varRelation source2 target2 →
      ∃ target, link_vardef target1 target2 = some target ∧
        match_globvar varRelation source target)
    (c1 c2 context : Context)
    (p1 p2 : CompCert4Lean.Common.AST.program SourceFunction SourceVarInfo)
    (tp1 tp2 : CompCert4Lean.Common.AST.program TargetFunction TargetVarInfo)
    (sourceProgram : CompCert4Lean.Common.AST.program SourceFunction SourceVarInfo)
    (hl : link_prog p1 p2 = some sourceProgram)
    (h1 : match_program_gen relation varRelation c1 p1 tp1)
    (h2 : match_program_gen relation varRelation c2 p2 tp2)
    (hc1 : LC.linkorder c1 context) (hc2 : LC.linkorder c2 context) :
    ∃ tp, link_prog tp1 tp2 = some tp ∧
      match_program_gen relation varRelation context sourceProgram tp := by
  obtain ⟨hmain, hcompat, hp⟩ := link_prog_inv_proof p1 p2 sourceProgram hl
  have hd1 := match_program_defmap relation varRelation c1 p1 tp1 h1
  have hd2 := match_program_defmap relation varRelation c2 p2 tp2 h2
  let tp : CompCert4Lean.Common.AST.program TargetFunction TargetVarInfo := {
    prog_defs := PTree.elements
      (PTree.combine link_prog_merge (prog_defmap tp1) (prog_defmap tp2))
    prog_public := tp1.prog_public ++ tp2.prog_public
    prog_main := tp1.prog_main }
  refine ⟨tp, ?_, ?_⟩
  · apply compiler_link_succeeds
    · exact h1.2.1.trans (hmain.trans h2.2.1.symm)
    · intro id tg1 tg2 ht1 ht2
      have hm1 := hd1 id
      have hm2 := hd2 id
      rw [ht1] at hm1
      rw [ht2] at hm2
      obtain ⟨g1, hg1, hr1⟩ := compiler_option_right hm1
      obtain ⟨g2, hg2, hr2⟩ := compiler_option_right hm2
      obtain ⟨hpub1, hpub2, global, hg⟩ := hcompat id g1 g2 hg1 hg2
      obtain ⟨tg, htg, _⟩ := compiler_link_glob relation varRelation hf hv hc1 hc2 hg hr1 hr2
      exact ⟨h1.2.2.symm ▸ hpub1, h2.2.2.symm ▸ hpub2, tg, htg⟩
  · constructor
    · rw [hp]
      apply PTree.elements_canonical_order'
      intro id
      rw [PTree.gcombine_proof (f := link_prog_merge) (by rfl),
        PTree.gcombine_proof (f := link_prog_merge) (by rfl)]
      apply compiler_merge_related
        (match_globdef relation varRelation c1) (match_globdef relation varRelation c2) (match_globdef relation varRelation context)
        link_prog_merge link_prog_merge rfl rfl
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ _ hr => compiler_glob_mono relation varRelation hr hc1)
        (fun _ _ hr => compiler_glob_mono relation varRelation hr hc2) (hd1 id) (hd2 id)
      intro g1 g2 tg1 tg2 hg1 hg2 hr1 hr2
      obtain ⟨_, _, global, hg⟩ := hcompat id g1 g2 hg1 hg2
      obtain ⟨tg, htg, hr⟩ := compiler_link_glob relation varRelation hf hv hc1 hc2 hg hr1 hr2
      simp only [link_prog_merge, hg, htg]
      exact option_rel.some global tg hr
    · rw [hp]
      exact ⟨h1.2.1, by simp only [tp, h1.2.2, h2.2.2]⟩

private theorem compiler_link_fundef {Context Source Target : Type}
    (relation : Context → fundef Source → fundef Target → Prop)
    (internalShape : ∀ context source target,
      relation context (.Internal source) target → ∃ body, target = .Internal body)
    (externalShape : ∀ context external target,
      relation context (.External external) target → target = .External external)
    (context1 context2 : Context) (source1 : fundef Source) (target1 : fundef Target)
    (source2 : fundef Source) (target2 : fundef Target) (linked : fundef Source)
    (linkedSource : link_fundef source1 source2 = some linked)
    (matched1 : relation context1 source1 target1)
    (matched2 : relation context2 source2 target2) :
    ∃ target, link_fundef target1 target2 = some target ∧
      (relation context1 linked target ∨ relation context2 linked target) := by
  cases source1 with
  | Internal body1 =>
    obtain ⟨targetBody, rfl⟩ := internalShape _ _ _ matched1
    cases source2 with
    | Internal body2 => cases linkedSource
    | External external =>
      cases externalShape _ _ _ matched2
      cases external <;> simp only [link_fundef] at linkedSource
      all_goals first
        | contradiction
        | cases linkedSource; exact ⟨_, rfl, Or.inl matched1⟩
  | External external1 =>
    cases externalShape _ _ _ matched1
    cases source2 with
    | Internal body2 =>
      obtain ⟨targetBody, rfl⟩ := internalShape _ _ _ matched2
      cases external1 <;> simp only [link_fundef] at linkedSource
      all_goals first
        | contradiction
        | cases linkedSource; exact ⟨_, rfl, Or.inr matched2⟩
    | External external2 =>
      cases externalShape _ _ _ matched2
      cases compared : external_function_eq external1 external2 with
      | left same =>
        simp only [link_fundef, compared, Option.some.injEq] at linkedSource
        cases linkedSource
        exact ⟨_, by simp only [link_fundef, compared], Or.inl matched1⟩
      | right different => simp only [link_fundef, compared] at linkedSource; contradiction

private theorem compiler_match_link {Source Target : Type}
    (relation : program (fundef Source) Unit → fundef Source → fundef Target → Prop)
    (internalShape : ∀ context source target,
      relation context (.Internal source) target → ∃ body, target = .Internal body)
    (externalShape : ∀ context external target,
      relation context (.External external) target → target = .External external) :
    TransfLink (match_program relation Eq) := by
  constructor
  intro source1 source2 target1 target2 linked linkedSource matched1 matched2
  have orders := Linker.link_linkorder source1 source2 linked linkedSource
  refine compiler_link_ast relation Eq
    (compiler_link_fundef relation internalShape externalShape)
    ?_
    source1 source2 linked source1 source2 target1 target2 linked
    linkedSource matched1 matched2 orders.1 orders.2
  intro source1 source2 source target1 target2 linkedSource matched1 matched2
  cases compiler_globvar_eq matched1
  cases compiler_globvar_eq matched2
  refine ⟨source, linkedSource, ?_⟩
  cases source
  exact match_globvar_intro Eq _ _ _ _ _ rfl

private theorem compiler_partial_link {Source Target : Type}
    (transform : program (fundef Source) Unit → Source → Res Target) :
    TransfLink (match_program
      (fun context source target => transf_partial_fundef (transform context) source = .OK target)
      Eq) := by
  apply compiler_match_link
  · intro context source target matched
    simp only [transf_partial_fundef] at matched
    split at matched
    · contradiction
    · cases matched
      exact ⟨_, rfl⟩
  · intro context external target matched
    exact (CompCert4Lean.Common.Errors.res.OK.inj matched).symm

private theorem compiler_total_link {Source Target : Type}
    (transform : program (fundef Source) Unit → Source → Target) :
    TransfLink (match_program
      (fun context source target => target = transf_fundef (transform context) source)
      Eq) := by
  apply compiler_match_link
  · intro context source target matched
    exact ⟨_, matched⟩
  · intro context external target matched
    exact matched

open CompCert4Lean.Cfrontend
open CompCert4Lean.Backend
open CompCert4Lean.X86

private theorem compiler_certificates_from_cshmgen
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (csyntaxLinkerCertificate clightLinkerCertificate : Ctypes.Linker_program_obligations)
    (cshmgenLink : @TransfLink Clight.program Csharpminor.program
      (Ctypes.Linker_program Clight.function clightLinkerCertificate)
      csharpminorLinker Cshmgenproof.match_prog) :
    CompilerPassCertificates cfg selectionOracle inlineCfg regallocOracle enumerationService
      csyntaxLinkerCertificate clightLinkerCertificate where
  simplExpr := SimplExprproof.TransfSimplExprLink csyntaxLinkerCertificate clightLinkerCertificate
  simplLocals := SimplLocalsproof.TransfSimplLocalsLink cfg clightLinkerCertificate
  cshmgen := cshmgenLink
  cminorgen := compiler_partial_link _
  selection := by
    apply compiler_match_link
    · intro context source target matched
      obtain ⟨helpers, _, translated⟩ := matched
      simp only [Selection.sel_fundef, transf_partial_fundef] at translated
      split at translated
      · contradiction
      · cases translated
        exact ⟨_, rfl⟩
    · intro context external target matched
      obtain ⟨helpers, _, translated⟩ := matched
      exact (CompCert4Lean.Common.Errors.res.OK.inj translated).symm
  rtlgen := compiler_partial_link _
  tailcall := compiler_total_link _
  inlining := compiler_partial_link _
  renumber := compiler_total_link _
  constprop := compiler_total_link _
  renumberConstprop := compiler_total_link _
  cse := compiler_partial_link _
  deadcode := compiler_partial_link _
  unusedglob := Unusedglobproof.transfSelectionLink_certificate_proof.link
  allocation := compiler_partial_link _
  tunneling := compiler_total_link _
  linearize := compiler_partial_link _
  cleanupLabels := compiler_total_link _
  debugvar := compiler_partial_link _
  stacking := compiler_partial_link _
  asmgen := compiler_partial_link _

private theorem compiler_list_map {Source Target : Type}
    (before after : Source → Target → Prop)
    (convert : ∀ source target, before source target → after source target)
    {sources : List Source} {targets : List Target}
    (matched : list_forall2 before sources targets) : list_forall2 after sources targets := by
  induction matched with
  | nil => exact .nil after
  | cons source target head tail induction =>
    exact .cons source target (convert source target head) induction

private theorem compiler_cshmgen_match_iff
    (certificate : Ctypes.Linker_program_obligations)
    (source : Clight.program) (target : Csharpminor.program) :
    Cshmgenproof.match_prog source target ↔
      @match_program_gen Clight.program Clight.fundef Ctypes.type Csharpminor.fundef Unit
        (Ctypes.Linker_program Clight.function certificate)
        Cshmgenproof.match_fundef (fun _ _ => True) source
        (Ctypes.program_of_program source) target := by
  letI : Linker Clight.program := Ctypes.Linker_program Clight.function certificate
  have globals : ∀ (sourceGlobal : globdef Clight.fundef Ctypes.type)
      (targetGlobal : globdef Csharpminor.fundef Unit),
      (match sourceGlobal, targetGlobal with
      | .Gfun sourceFunction, .Gfun targetFunction =>
          ∃ context, Ctypes.linkorder_program context source ∧
            Cshmgenproof.match_fundef context sourceFunction targetFunction
      | .Gvar sourceVar, .Gvar targetVar =>
          True ∧ sourceVar.gvar_init = targetVar.gvar_init ∧
            sourceVar.gvar_readonly = targetVar.gvar_readonly ∧
            sourceVar.gvar_volatile = targetVar.gvar_volatile
      | _, _ => False) ↔
      match_globdef Cshmgenproof.match_fundef (fun _ _ => True) source
        sourceGlobal targetGlobal := by
    intro sourceGlobal targetGlobal
    constructor
    · intro matched
      cases sourceGlobal with
      | Gfun sourceFunction =>
        cases targetGlobal with
        | Gfun targetFunction =>
          obtain ⟨context, ordered, translated⟩ := matched
          exact match_globdef_fun _ _ _ _ _ _ ordered translated
        | Gvar targetVar => exact matched.elim
      | Gvar sourceVar =>
        cases targetGlobal with
        | Gfun targetFunction => exact matched.elim
        | Gvar targetVar =>
          obtain ⟨_, sameInit, sameReadonly, sameVolatile⟩ := matched
          cases sourceVar
          cases targetVar
          simp only at sameInit sameReadonly sameVolatile
          subst_vars
          exact match_globdef_var _ _ _ _ _ (match_globvar_intro _ _ _ _ _ _ trivial)
    · intro matched
      cases matched with
      | match_globdef_fun context sourceFunction targetFunction ordered translated =>
        exact ⟨context, ordered, translated⟩
      | match_globdef_var sourceVar targetVar matchedVars =>
        cases matchedVars
        exact ⟨trivial, rfl, rfl, rfl⟩
  constructor
  · rintro ⟨matched, sameMain, samePublic⟩
    exact ⟨compiler_list_map _ _ (fun _ _ head => ⟨head.1, (globals _ _).mp head.2⟩)
      matched, sameMain, samePublic⟩
  · rintro ⟨matched, sameMain, samePublic⟩
    exact ⟨compiler_list_map _ _ (fun _ _ head => ⟨head.1, (globals _ _).mpr head.2⟩)
      matched, sameMain, samePublic⟩

private theorem compiler_cshmgen_link_fundef
    (context1 context2 : Clight.program)
    (source1 : Clight.fundef) (target1 : Csharpminor.fundef)
    (source2 : Clight.fundef) (target2 : Csharpminor.fundef) (linked : Clight.fundef)
    (linkedSource : Ctypes.link_fundef source1 source2 = some linked)
    (matched1 : Cshmgenproof.match_fundef context1 source1 target1)
    (matched2 : Cshmgenproof.match_fundef context2 source2 target2) :
    ∃ target, link_fundef target1 target2 = some target ∧
      (Cshmgenproof.match_fundef context1 linked target ∨
        Cshmgenproof.match_fundef context2 linked target) := by
  have original1 := matched1
  have original2 := matched2
  cases matched1 with
  | match_fundef_internal sourceBody1 targetBody1 translated1 =>
    cases matched2 with
    | match_fundef_internal sourceBody2 targetBody2 translated2 => cases linkedSource
    | match_fundef_external external args result convention signature =>
      cases external <;> simp only [Ctypes.link_fundef] at linkedSource
      all_goals first
        | contradiction
        | cases linkedSource; exact ⟨_, rfl, Or.inl original1⟩
  | match_fundef_external external1 args1 result1 convention1 signature1 =>
    cases matched2 with
    | match_fundef_internal sourceBody2 targetBody2 translated2 =>
      cases external1 <;> simp only [Ctypes.link_fundef] at linkedSource
      all_goals first
        | contradiction
        | cases linkedSource; exact ⟨_, rfl, Or.inr original2⟩
    | match_fundef_external external2 args2 result2 convention2 signature2 =>
      simp only [Ctypes.link_fundef] at linkedSource
      repeat first
        | contradiction
        | split at linkedSource
      all_goals
        cases linkedSource
        exact ⟨_, by simp_all only [link_fundef], Or.inl original1⟩

private theorem compiler_cshmgen_link_var
    (source1 source2 source : globvar Ctypes.type) (target1 target2 : globvar Unit)
    (linkedSource : link_vardef source1 source2 = some source)
    (matched1 : match_globvar (fun _ _ => True) source1 target1)
    (matched2 : match_globvar (fun _ _ => True) source2 target2) :
    ∃ target, link_vardef target1 target2 = some target ∧
      match_globvar (fun _ _ => True) source target := by
  cases matched1 with
  | match_globvar_intro sourceInfo1 targetInfo1 init1 readonly1 volatile1 matched1 =>
    cases matched2 with
    | match_globvar_intro sourceInfo2 targetInfo2 init2 readonly2 volatile2 matched2 =>
      cases targetInfo1
      cases targetInfo2
      simp only [link_vardef] at linkedSource
      repeat first
        | contradiction
        | split at linkedSource
      all_goals
        cases linkedSource
      all_goals
        refine ⟨{ gvar_info := (), gvar_init := _, gvar_readonly := _, gvar_volatile := _ },
          ?_, match_globvar_intro _ _ _ _ _ _ trivial⟩
        simp_all [link_vardef, Linker.link]

private theorem compiler_cshmgen_link
    (certificate : Ctypes.Linker_program_obligations) :
    @TransfLink Clight.program Csharpminor.program
      (Ctypes.Linker_program Clight.function certificate)
      csharpminorLinker Cshmgenproof.match_prog := by
  letI : Linker Clight.program := Ctypes.Linker_program Clight.function certificate
  refine @TransfLink.mk Clight.program Csharpminor.program
    (Ctypes.Linker_program Clight.function certificate) csharpminorLinker
    Cshmgenproof.match_prog ?_
  intro source1 source2 target1 target2 source linkedSource matched1 matched2
  have orders := certificate.link_linkorder source1 source2 source linkedSource
  have matched1' := (compiler_cshmgen_match_iff certificate source1 target1).mp matched1
  have matched2' := (compiler_cshmgen_match_iff certificate source2 target2).mp matched2
  change Ctypes.link_program certificate.composite_defs source1 source2 = some source at linkedSource
  unfold Ctypes.link_program at linkedSource
  cases linkedAst : link (Ctypes.program_of_program source1) (Ctypes.program_of_program source2) with
  | none => simp only [linkedAst] at linkedSource; contradiction
  | some sourceAst =>
    obtain ⟨target, linkedTarget, matchedTarget⟩ :=
      @compiler_link_ast Clight.program Clight.fundef Csharpminor.fundef Ctypes.type Unit
      (Ctypes.Linker_program Clight.function certificate)
      (Ctypes.Linker_fundef Clight.function) (Linker_fundef Csharpminor.function)
      Ctypes.Linker_types Linker_unit
      Cshmgenproof.match_fundef (fun _ _ => True)
      compiler_cshmgen_link_fundef compiler_cshmgen_link_var
      source1 source2 source
      (Ctypes.program_of_program source1) (Ctypes.program_of_program source2)
      target1 target2 sourceAst linkedAst matched1' matched2' orders.1 orders.2
    cases linkedTypes : Ctypes.lift_option (Ctypes.link_composite_defs source1.prog_types source2.prog_types) with
    | inright absent => simp only [linkedAst, linkedTypes] at linkedSource; contradiction
    | inleft types =>
      simp only [linkedAst, linkedTypes] at linkedSource
      cases Option.some.inj linkedSource
      exact ⟨target, linkedTarget, (compiler_cshmgen_match_iff certificate _ _).mpr matchedTarget⟩

theorem compilerPassCertificates_proof
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (csyntaxLinkerCertificate clightLinkerCertificate : Ctypes.Linker_program_obligations) :
    CompilerPassCertificates cfg selectionOracle inlineCfg regallocOracle enumerationService
      csyntaxLinkerCertificate clightLinkerCertificate :=
  compiler_certificates_from_cshmgen cfg selectionOracle inlineCfg regallocOracle enumerationService
    csyntaxLinkerCertificate clightLinkerCertificate (compiler_cshmgen_link clightLinkerCertificate)

end CompCert4Lean.Driver.Compiler

namespace CompCert4Lean.Driver.Compiler

open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend
open CompCert4Lean.Backend
open CompCert4Lean.X86

set_option maxRecDepth 4096 in
theorem cstrategy_semantic_preservation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)] :
    cstrategy_semantic_preservationStatement := by
  intro cfg selectionOracle inlineCfg regallocOracle enumerationService
    csyntaxLinkerCertificate clightLinkerCertificate passCertificates providers source target matched
  simp only [match_prog, CompCert's_passes, compose_passes, pass_compose, pass_identity] at matched
  rcases matched with ⟨program1, match1, program2, match2, program3, match3,
    program4, match4, program5, match5, program6, match6, program7, match7,
    program8, match8, program9, match9, program10, match10, program11, match11,
    program12, match12, program13, match13, program14, match14, program15, match15,
    program16, match16, program17, match17, program18, match18, program19, match19,
    program20, match20, program21, match21, sameTarget⟩
  subst target
  have forward : forward_simulation (Cstrategy.semantics providers source)
      (Asm.semantics cfg providers program21) := by
    refine compose_forward_simulations _ _ _
      (SimplExprproof.transl_program_correct providers _ _ match1) ?_
    refine compose_forward_simulations _ _ _
      (SimplLocalsproof.transf_program_correct cfg providers _ _ match2) ?_
    refine compose_forward_simulations _ _ _
      (Cshmgenproof.transl_program_correct providers _ _ match3) ?_
    refine compose_forward_simulations _ _ _
      (Cminorgenproof.transl_program_correct providers _ _ match4) ?_
    refine compose_forward_simulations _ _ _
      (Selectionproof.transf_program_correct cfg selectionOracle providers _ _ match5) ?_
    refine compose_forward_simulations _ _ _
      (RTLgenproof.transf_program_correct providers _ _ match6) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (RTL.semantics providers) _ _ _ _ match7
        (Tailcallproof.transf_program_correct cfg providers)) ?_
    refine compose_forward_simulations _ _ _
      (Inliningproof.transf_program_correct providers inlineCfg _ _ match8) ?_
    refine compose_forward_simulations _ _ _
      (Renumberproof.transf_program_correct providers _ _ match9) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (RTL.semantics providers) _ _ _ _ match10
        (Constpropproof.transf_program_correct cfg providers)) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (RTL.semantics providers) _ _ _ _ match11
        (Renumberproof.transf_program_correct providers)) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (RTL.semantics providers) _ _ _ _ match12
        (CSEproof.transf_program_correct cfg providers)) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (RTL.semantics providers) _ _ _ _ match13
        (fun source target => Deadcodeproof.transf_program_correct cfg source target providers)) ?_
    refine compose_forward_simulations _ _ _
      (Unusedglobproof.transf_program_correct providers _ _ match14) ?_
    refine compose_forward_simulations _ _ _
      (Allocproof.transf_program_correct cfg regallocOracle providers _ _ match15) ?_
    refine compose_forward_simulations _ _ _
      (Tunnelingproof.transf_program_correct cfg providers _ _ match16) ?_
    refine compose_forward_simulations _ _ _
      (Linearizeproof.transf_program_correct cfg providers enumerationService _ _ match17) ?_
    refine compose_forward_simulations _ _ _
      (CleanupLabelsproof.transf_program_correct cfg providers _ _ match18) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (Linear.semantics cfg providers) _ _ _ _ match19
        (Debugvarproof.transf_program_correct cfg providers)) ?_
    refine compose_forward_simulations _ _ _
      (Stackingproof.transf_program_correct cfg providers Asmgenproof0.return_address_offset
        Asmgenproof.return_address_exists _ _
        (Bounds.function_bounds_bound_local_pos_proof cfg)
        (Bounds.function_bounds_bound_outgoing_pos_proof cfg)
        (Bounds.function_bounds_bound_stack_data_pos_proof cfg)
        (Bounds.function_bounds_used_callee_save_norepet_proof cfg)
        (Bounds.function_bounds_used_callee_save_prop_proof cfg) match20) ?_
    exact Asmgenproof.transf_program_correct cfg providers _ _ match21
  refine ⟨forward, forward_to_backward_simulation _ _ ?_ ?_ ?_⟩
  · exact factor_forward_simulation _ _ forward
      (Asm.semantics_determinate_proof cfg providers program21).sd_traces
  · exact atomic_receptive _ (Cstrategy.semantics_strongly_receptive providers source)
  · exact Asm.semantics_determinate_proof cfg providers program21

end CompCert4Lean.Driver.Compiler

namespace CompCert4Lean.Driver.Compiler

open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend
open CompCert4Lean.X86

theorem c_semantic_preservation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)] :
    c_semantic_preservationStatement := by
  intro cfg selectionOracle inlineCfg regallocOracle enumerationService
    csyntaxLinkerCertificate clightLinkerCertificate passCertificates providers source target matched
  exact compose_backward_simulation _ _ _
    (Asm.semantics_determinate_proof cfg providers target).sd_traces
    (factor_backward_simulation _ _
      (Cstrategy.strategy_simulation providers source)
      (Csem.semantics_single_events providers source)
      (Cstrategy.semantics_strongly_receptive providers source).ssr_well_behaved)
    (cstrategy_semantic_preservation cfg selectionOracle inlineCfg regallocOracle enumerationService
      csyntaxLinkerCertificate clightLinkerCertificate passCertificates providers source target matched).2

end CompCert4Lean.Driver.Compiler
