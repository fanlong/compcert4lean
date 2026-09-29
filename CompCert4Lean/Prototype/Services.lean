import CompCert4Lean.Prototype.Json
import CompCert4Lean.Allocator.Allocator
import CompCert4Lean.Prototype.RuntimeHelpers

namespace CompCert4Lean.Prototype

open CompCert4Lean
open Common.AST Common.Errors
open Backend Backend.Locations
open Foundation.Numbers.Rocq.Coq
open Lib.Maps

abbrev z := ZArith.BinInt.Z.of_nat

instance : Flocq.Core.FLX.Prec_gt_0 (z 53) := by change (0 : Int) < 53; decide
instance : Flocq.Core.FLX.Prec_gt_0 (z 24) := by change (0 : Int) < 24; decide
instance : Flocq.IEEE754.BinarySingleNaN.Prec_lt_emax (z 53) (z 1024) :=
  ⟨by change (53 : Int) < 1024; decide⟩
instance : Flocq.IEEE754.BinarySingleNaN.Prec_lt_emax (z 24) (z 128) :=
  ⟨by change (24 : Int) < 128; decide⟩
instance : Flocq.IEEE754.Binary.BinaryNormalizeCertificate (z 53) (z 1024) :=
  Flocq.IEEE754.Binary.binary64_normalize_certificate_proof
instance : Flocq.IEEE754.Binary.BinaryNormalizeCertificate (z 24) (z 128) :=
  Flocq.IEEE754.Binary.binary32_normalize_certificate_proof
instance : Lib.IEEE754_extra.Bexact_inverse_certificate (z 53) (z 1024) :=
  Lib.IEEE754_extra.binary64_exact_inverse_certificate_proof
instance : Lib.IEEE754_extra.Bexact_inverse_certificate (z 24) (z 128) :=
  Lib.IEEE754_extra.binary32_exact_inverse_certificate_proof

def cfg := Config.pinnedLinuxX86_64 false 0 false false false false false

def optimizedCfg := Config.pinnedLinuxX86_64 false 2 true true true true false

def selectionFor (configuration : Config.CompilerConfig) : Selection.SelectionOracle :=
  { compileSwitch := compileSwitch
    ifConversionHeuristic := ifConversion configuration.options.optimConstprop }

def selectionOracle : Selection.SelectionOracle := selectionFor cfg

def inlineCfg : Inlining.InliningConfig :=
  { enabled := false, functionsCalledOnce := false,
    inlineStatus := fun _ => .noinline, isStatic := fun _ => false }

def enumeration : Linearize.EnumerationService := enumerateBlocks

def enumerationFor (configuration : Config.CompilerConfig) : Linearize.EnumerationService :=
  if configuration.options.optimCSE && configuration.options.optimConstprop then enumerateLoopBlocks
  else enumeration

end CompCert4Lean.Prototype
