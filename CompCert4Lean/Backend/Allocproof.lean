import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Allocation
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Backend.LTL
import CompCert4Lean.Backend.Conventions
import CompCert4Lean.Backend.RTLtyping
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.FSetDecide
import CompCert4Lean.Lib.FSetFacts
import CompCert4Lean.Lib.FSetProperties
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps
import CompCert4Lean.X86_64.Archi

/-!
# Correctness surface for register allocation

Definition-bearing translation of CompCert's `backend/Allocproof.v`.  The
executable relations assigned to this packet are retained directly; proof
obligations assigned to the later proof-migration phase are represented by
transparent proposition descriptors below.
-/

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.RTLtyping
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.Conventions1
open CompCert4Lean.X86.Machregs

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev RegallocOracle := CompCert4Lean.Backend.Allocation.RegallocOracle
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

/-! ## The six generated finite-set applications -/

private abbrev EqSetE :=
  CompCert4Lean.Lib.FSetInterface.OrderedType.toDecidableType EqSet.E
private abbrev EqSetM :=
  (CompCert4Lean.Lib.FSetAVLplus.Make.toSfun EqSet.E).toWSfun
private abbrev EqSet2E :=
  CompCert4Lean.Lib.FSetInterface.OrderedType.toDecidableType EqSet2.E
private abbrev EqSet2M :=
  (CompCert4Lean.Lib.FSetAVLplus.Make.toSfun EqSet2.E).toWSfun

namespace ESF

def ESF : CompCert4Lean.Lib.FSetFacts.Facts EqSetE EqSetM :=
  CompCert4Lean.Lib.FSetFacts.WFacts_fun.make EqSetE EqSetM

abbrev E_ST := CompCert4Lean.Lib.FSetFacts.WFacts_fun.E_ST ESF
abbrev Empty_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Empty_m ESF
abbrev Empty_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Empty_s_m ESF
abbrev Empty_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Empty_s_m_Proper ESF
abbrev Equal_ST := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Equal_ST ESF
abbrev In_eq_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.In_eq_iff ESF
abbrev In_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.In_m ESF
abbrev In_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.In_s_m ESF
abbrev SubsetSetoid := CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid ESF
abbrev SubsetSetoid_Reflexive := CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid_Reflexive ESF
abbrev SubsetSetoid_Transitive := CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid_Transitive ESF
abbrev SubsetSetoid_relation := CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid_relation ESF
abbrev Subset_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Subset_m ESF
abbrev Subset_refl := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Subset_refl ESF
abbrev Subset_trans := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Subset_trans ESF
abbrev add_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_b ESF
abbrev add_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_iff ESF
abbrev add_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_m ESF
abbrev add_neq_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_neq_b ESF
abbrev add_neq_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_neq_iff ESF
abbrev add_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_s_m ESF
abbrev add_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_s_m_Proper ESF
abbrev diff_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_b ESF
abbrev diff_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_iff ESF
abbrev diff_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_m ESF
abbrev diff_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_s_m ESF
abbrev diff_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_s_m_Proper ESF
abbrev elements_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.elements_b ESF
abbrev elements_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.elements_iff ESF
abbrev empty_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.empty_b ESF
abbrev empty_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.empty_iff ESF
abbrev eqb := CompCert4Lean.Lib.FSetFacts.WFacts_fun.eqb ESF
abbrev equal_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.equal_iff ESF
abbrev equal_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.equal_m ESF
abbrev exists_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.exists_b ESF
abbrev exists_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.exists_iff ESF
abbrev filter_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_b ESF
abbrev filter_equal := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_equal ESF
abbrev filter_ext := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_ext ESF
abbrev filter_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_iff ESF
abbrev filter_subset := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_subset ESF
abbrev for_all_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.for_all_b ESF
abbrev for_all_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.for_all_iff ESF
abbrev inter_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_b ESF
abbrev inter_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_iff ESF
abbrev inter_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_m ESF
abbrev inter_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_s_m ESF
abbrev inter_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_s_m_Proper ESF
abbrev is_empty_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.is_empty_iff ESF
abbrev is_empty_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.is_empty_m ESF
abbrev mem_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_b ESF
abbrev mem_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_iff ESF
abbrev mem_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_m ESF
abbrev not_mem_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.not_mem_iff ESF
abbrev remove_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_b ESF
abbrev remove_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_iff ESF
abbrev remove_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_m ESF
abbrev remove_neq_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_neq_b ESF
abbrev remove_neq_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_neq_iff ESF
abbrev remove_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_s_m ESF
abbrev remove_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_s_m_Proper ESF
abbrev singleton_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.singleton_b ESF
abbrev singleton_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.singleton_iff ESF
abbrev singleton_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.singleton_m ESF
abbrev subset_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.subset_iff ESF
abbrev subset_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.subset_m ESF
abbrev union_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_b ESF
abbrev union_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_iff ESF
abbrev union_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_m ESF
abbrev union_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_s_m ESF
abbrev union_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_s_m_Proper ESF

end ESF

namespace ESP

def ESP : CompCert4Lean.Lib.FSetProperties.Properties EqSetE EqSetM :=
  ⟨CompCert4Lean.Lib.FSetDecide.WDecide_fun.make EqSetE EqSetM⟩

abbrev Dec := CompCert4Lean.Lib.FSetProperties.Dec EqSetE EqSetM
abbrev FM := CompCert4Lean.Lib.FSetProperties.WProperties_fun.FM ESP

abbrev Add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Add EqSetE EqSetM
abbrev Add_Equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Add_Equal EqSetE EqSetM
abbrev Add_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Add_add EqSetE EqSetM
abbrev Add_remove :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Add_remove EqSetE EqSetM
abbrev Equal_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Equal_cardinal EqSetE EqSetM
abbrev Equal_remove :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Equal_remove EqSetE EqSetM
abbrev In_dec :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.In_dec EqSetE EqSetM
abbrev add_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_add EqSetE EqSetM
abbrev add_cardinal_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_cardinal_1 EqSetE EqSetM
abbrev add_cardinal_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_cardinal_2 EqSetE EqSetM
abbrev add_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_equal EqSetE EqSetM
abbrev add_fold :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_fold EqSetE EqSetM
abbrev add_remove :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_remove EqSetE EqSetM
abbrev add_union_singleton :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_union_singleton EqSetE EqSetM
abbrev cardinal_0 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_0 EqSetE EqSetM
abbrev cardinal_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_1 EqSetE EqSetM
abbrev cardinal_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_2 EqSetE EqSetM
abbrev cardinal_Empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_Empty EqSetE EqSetM
abbrev cardinal_fold :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_fold EqSetE EqSetM
abbrev cardinal_inv_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_inv_1 EqSetE EqSetM
abbrev cardinal_inv_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_inv_2 EqSetE EqSetM
abbrev cardinal_inv_2b :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_inv_2b EqSetE EqSetM
abbrev cardinal_m :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_m EqSetE EqSetM
abbrev cardinal_m_Proper :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_m_Proper EqSetE EqSetM
abbrev diff_inter_all :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.diff_inter_all EqSetE EqSetM
abbrev diff_inter_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.diff_inter_cardinal EqSetE EqSetM
abbrev diff_inter_empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.diff_inter_empty EqSetE EqSetM
abbrev diff_subset :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.diff_subset EqSetE EqSetM
abbrev diff_subset_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.diff_subset_equal EqSetE EqSetM
abbrev double_inclusion :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.double_inclusion EqSetE EqSetM
abbrev elements_Empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.elements_Empty EqSetE EqSetM
abbrev elements_empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.elements_empty EqSetE EqSetM
abbrev empty_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_cardinal EqSetE EqSetM
abbrev empty_diff_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_diff_1 EqSetE EqSetM
abbrev empty_diff_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_diff_2 EqSetE EqSetM
abbrev empty_inter_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_inter_1 EqSetE EqSetM
abbrev empty_inter_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_inter_2 EqSetE EqSetM
abbrev empty_is_empty_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_is_empty_1 EqSetE EqSetM
abbrev empty_is_empty_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_is_empty_2 EqSetE EqSetM
abbrev empty_union_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_union_1 EqSetE EqSetM
abbrev empty_union_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_union_2 EqSetE EqSetM
abbrev equal_refl :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.equal_refl EqSetE EqSetM
abbrev equal_sym :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.equal_sym EqSetE EqSetM
abbrev equal_trans :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.equal_trans EqSetE EqSetM
abbrev fold_0 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_0 EqSetE EqSetM
abbrev fold_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_1 EqSetE EqSetM
abbrev fold_1b :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_1b EqSetE EqSetM
abbrev fold_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_2 EqSetE EqSetM
abbrev fold_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_add EqSetE EqSetM
abbrev fold_commutes :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_commutes EqSetE EqSetM
abbrev fold_diff_inter :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_diff_inter EqSetE EqSetM
abbrev fold_empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_empty EqSetE EqSetM
abbrev fold_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_equal EqSetE EqSetM
abbrev fold_identity :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_identity EqSetE EqSetM
abbrev fold_init :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_init EqSetE EqSetM
abbrev fold_plus :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_plus EqSetE EqSetM
abbrev fold_rec :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_rec EqSetM
abbrev fold_rec_bis :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_rec_bis EqSetM
abbrev fold_rec_nodep :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_rec_nodep EqSetM
abbrev fold_rec_weak :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_rec_weak EqSetM
abbrev fold_rel :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_rel EqSetM
abbrev fold_spec_right :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_spec_right EqSetE EqSetM
abbrev fold_union :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_union EqSetE EqSetM
abbrev fold_union_inter :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_union_inter EqSetE EqSetM
abbrev in_subset :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.in_subset EqSetE EqSetM
abbrev inter_Add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_Add EqSetE EqSetM
abbrev inter_Add_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_Add_2 EqSetE EqSetM
abbrev inter_add_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_add_1 EqSetE EqSetM
abbrev inter_add_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_add_2 EqSetE EqSetM
abbrev inter_assoc :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_assoc EqSetE EqSetM
abbrev inter_equal_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_equal_1 EqSetE EqSetM
abbrev inter_equal_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_equal_2 EqSetE EqSetM
abbrev inter_subset_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_subset_1 EqSetE EqSetM
abbrev inter_subset_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_subset_2 EqSetE EqSetM
abbrev inter_subset_3 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_subset_3 EqSetE EqSetM
abbrev inter_subset_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_subset_equal EqSetE EqSetM
abbrev inter_sym :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_sym EqSetE EqSetM
abbrev not_in_union :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.not_in_union EqSetE EqSetM
abbrev of_list :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.of_list EqSetE EqSetM
abbrev of_list_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.of_list_1 EqSetE EqSetM
abbrev of_list_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.of_list_2 EqSetE EqSetM
abbrev of_list_3 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.of_list_3 EqSetE EqSetM
abbrev remove_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_add EqSetE EqSetM
abbrev remove_cardinal_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_cardinal_1 EqSetE EqSetM
abbrev remove_cardinal_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_cardinal_2 EqSetE EqSetM
abbrev remove_diff_singleton :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_diff_singleton EqSetE EqSetM
abbrev remove_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_equal EqSetE EqSetM
abbrev remove_fold_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_fold_1 EqSetE EqSetM
abbrev remove_fold_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_fold_2 EqSetE EqSetM
abbrev remove_singleton_empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_singleton_empty EqSetE EqSetM
abbrev set_induction :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.set_induction EqSetM
abbrev set_induction_bis :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.set_induction_bis EqSetM
abbrev singleton_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.singleton_cardinal EqSetE EqSetM
abbrev singleton_equal_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.singleton_equal_add EqSetE EqSetM
abbrev subset_add_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_add_2 EqSetE EqSetM
abbrev subset_add_3 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_add_3 EqSetE EqSetM
abbrev subset_antisym :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_antisym EqSetE EqSetM
abbrev subset_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_cardinal EqSetE EqSetM
abbrev subset_cardinal_lt :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_cardinal_lt EqSetE EqSetM
abbrev subset_diff :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_diff EqSetE EqSetM
abbrev subset_empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_empty EqSetE EqSetM
abbrev subset_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_equal EqSetE EqSetM
abbrev subset_refl :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_refl EqSetE EqSetM
abbrev subset_remove_3 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_remove_3 EqSetE EqSetM
abbrev subset_trans :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_trans EqSetE EqSetM
abbrev to_list :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.to_list EqSetE EqSetM
abbrev union_Add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_Add EqSetE EqSetM
abbrev union_Equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_Equal EqSetE EqSetM
abbrev union_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_add EqSetE EqSetM
abbrev union_assoc :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_assoc EqSetE EqSetM
abbrev union_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_cardinal EqSetE EqSetM
abbrev union_cardinal_inter :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_cardinal_inter EqSetE EqSetM
abbrev union_cardinal_le :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_cardinal_le EqSetE EqSetM
abbrev union_equal_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_equal_1 EqSetE EqSetM
abbrev union_equal_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_equal_2 EqSetE EqSetM
abbrev union_inter_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_inter_1 EqSetE EqSetM
abbrev union_inter_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_inter_2 EqSetE EqSetM
abbrev union_inter_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_inter_cardinal EqSetE EqSetM
abbrev union_remove_add_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_remove_add_1 EqSetE EqSetM
abbrev union_remove_add_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_remove_add_2 EqSetE EqSetM
abbrev union_subset_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_1 EqSetE EqSetM
abbrev union_subset_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_2 EqSetE EqSetM
abbrev union_subset_3 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_3 EqSetE EqSetM
abbrev union_subset_4 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_4 EqSetE EqSetM
abbrev union_subset_5 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_5 EqSetE EqSetM
abbrev union_subset_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_equal EqSetE EqSetM
abbrev union_sym :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_sym EqSetE EqSetM

end ESP

namespace ESD

def ESD : CompCert4Lean.Lib.FSetDecide.Decide EqSetE EqSetM :=
  CompCert4Lean.Lib.FSetDecide.WDecide_fun.make EqSetE EqSetM
abbrev F : CompCert4Lean.Lib.FSetDecide.F EqSetE EqSetM :=
  CompCert4Lean.Backend.Allocproof.ESD.ESD.F
def FSetDecideAuxiliary :
    CompCert4Lean.Lib.FSetDecide.WDecide_fun.FSetDecideAuxiliary EqSetE EqSetM :=
  ⟨ESD⟩
def FSetDecideTestCases :
    CompCert4Lean.Lib.FSetDecide.WDecide_fun.FSetDecideTestCases EqSetE EqSetM :=
  ⟨ESD⟩
def FSetLogicalFacts :
    CompCert4Lean.Lib.FSetDecide.WDecide_fun.FSetLogicalFacts EqSetE EqSetM :=
  ⟨ESD⟩

end ESD

namespace ESF2

def ESF2 : CompCert4Lean.Lib.FSetFacts.Facts EqSet2E EqSet2M :=
  CompCert4Lean.Lib.FSetFacts.WFacts_fun.make EqSet2E EqSet2M

abbrev E_ST := CompCert4Lean.Lib.FSetFacts.WFacts_fun.E_ST ESF2
abbrev Empty_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Empty_m ESF2
abbrev Empty_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Empty_s_m ESF2
abbrev Empty_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Empty_s_m_Proper ESF2
abbrev Equal_ST := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Equal_ST ESF2
abbrev In_eq_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.In_eq_iff ESF2
abbrev In_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.In_m ESF2
abbrev In_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.In_s_m ESF2
abbrev SubsetSetoid := CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid ESF2
abbrev SubsetSetoid_Reflexive := CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid_Reflexive ESF2
abbrev SubsetSetoid_Transitive := CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid_Transitive ESF2
abbrev SubsetSetoid_relation := CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid_relation ESF2
abbrev Subset_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Subset_m ESF2
abbrev Subset_refl := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Subset_refl ESF2
abbrev Subset_trans := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Subset_trans ESF2
abbrev add_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_b ESF2
abbrev add_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_iff ESF2
abbrev add_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_m ESF2
abbrev add_neq_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_neq_b ESF2
abbrev add_neq_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_neq_iff ESF2
abbrev add_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_s_m ESF2
abbrev add_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_s_m_Proper ESF2
abbrev diff_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_b ESF2
abbrev diff_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_iff ESF2
abbrev diff_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_m ESF2
abbrev diff_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_s_m ESF2
abbrev diff_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_s_m_Proper ESF2
abbrev elements_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.elements_b ESF2
abbrev elements_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.elements_iff ESF2
abbrev empty_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.empty_b ESF2
abbrev empty_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.empty_iff ESF2
abbrev eqb := CompCert4Lean.Lib.FSetFacts.WFacts_fun.eqb ESF2
abbrev equal_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.equal_iff ESF2
abbrev equal_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.equal_m ESF2
abbrev exists_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.exists_b ESF2
abbrev exists_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.exists_iff ESF2
abbrev filter_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_b ESF2
abbrev filter_equal := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_equal ESF2
abbrev filter_ext := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_ext ESF2
abbrev filter_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_iff ESF2
abbrev filter_subset := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_subset ESF2
abbrev for_all_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.for_all_b ESF2
abbrev for_all_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.for_all_iff ESF2
abbrev inter_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_b ESF2
abbrev inter_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_iff ESF2
abbrev inter_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_m ESF2
abbrev inter_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_s_m ESF2
abbrev inter_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_s_m_Proper ESF2
abbrev is_empty_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.is_empty_iff ESF2
abbrev is_empty_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.is_empty_m ESF2
abbrev mem_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_b ESF2
abbrev mem_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_iff ESF2
abbrev mem_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_m ESF2
abbrev not_mem_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.not_mem_iff ESF2
abbrev remove_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_b ESF2
abbrev remove_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_iff ESF2
abbrev remove_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_m ESF2
abbrev remove_neq_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_neq_b ESF2
abbrev remove_neq_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_neq_iff ESF2
abbrev remove_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_s_m ESF2
abbrev remove_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_s_m_Proper ESF2
abbrev singleton_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.singleton_b ESF2
abbrev singleton_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.singleton_iff ESF2
abbrev singleton_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.singleton_m ESF2
abbrev subset_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.subset_iff ESF2
abbrev subset_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.subset_m ESF2
abbrev union_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_b ESF2
abbrev union_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_iff ESF2
abbrev union_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_m ESF2
abbrev union_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_s_m ESF2
abbrev union_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_s_m_Proper ESF2

end ESF2

namespace ESP2

def ESP2 : CompCert4Lean.Lib.FSetProperties.Properties EqSet2E EqSet2M :=
  ⟨CompCert4Lean.Lib.FSetDecide.WDecide_fun.make EqSet2E EqSet2M⟩

abbrev Dec := CompCert4Lean.Lib.FSetProperties.Dec EqSet2E EqSet2M
abbrev FM := CompCert4Lean.Lib.FSetProperties.WProperties_fun.FM ESP2

abbrev Add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Add EqSet2E EqSet2M
abbrev Add_Equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Add_Equal EqSet2E EqSet2M
abbrev Add_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Add_add EqSet2E EqSet2M
abbrev Add_remove :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Add_remove EqSet2E EqSet2M
abbrev Equal_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Equal_cardinal EqSet2E EqSet2M
abbrev Equal_remove :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.Equal_remove EqSet2E EqSet2M
abbrev In_dec :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.In_dec EqSet2E EqSet2M
abbrev add_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_add EqSet2E EqSet2M
abbrev add_cardinal_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_cardinal_1 EqSet2E EqSet2M
abbrev add_cardinal_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_cardinal_2 EqSet2E EqSet2M
abbrev add_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_equal EqSet2E EqSet2M
abbrev add_fold :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_fold EqSet2E EqSet2M
abbrev add_remove :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_remove EqSet2E EqSet2M
abbrev add_union_singleton :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.add_union_singleton EqSet2E EqSet2M
abbrev cardinal_0 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_0 EqSet2E EqSet2M
abbrev cardinal_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_1 EqSet2E EqSet2M
abbrev cardinal_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_2 EqSet2E EqSet2M
abbrev cardinal_Empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_Empty EqSet2E EqSet2M
abbrev cardinal_fold :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_fold EqSet2E EqSet2M
abbrev cardinal_inv_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_inv_1 EqSet2E EqSet2M
abbrev cardinal_inv_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_inv_2 EqSet2E EqSet2M
abbrev cardinal_inv_2b :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_inv_2b EqSet2E EqSet2M
abbrev cardinal_m :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_m EqSet2E EqSet2M
abbrev cardinal_m_Proper :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.cardinal_m_Proper EqSet2E EqSet2M
abbrev diff_inter_all :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.diff_inter_all EqSet2E EqSet2M
abbrev diff_inter_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.diff_inter_cardinal EqSet2E EqSet2M
abbrev diff_inter_empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.diff_inter_empty EqSet2E EqSet2M
abbrev diff_subset :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.diff_subset EqSet2E EqSet2M
abbrev diff_subset_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.diff_subset_equal EqSet2E EqSet2M
abbrev double_inclusion :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.double_inclusion EqSet2E EqSet2M
abbrev elements_Empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.elements_Empty EqSet2E EqSet2M
abbrev elements_empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.elements_empty EqSet2E EqSet2M
abbrev empty_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_cardinal EqSet2E EqSet2M
abbrev empty_diff_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_diff_1 EqSet2E EqSet2M
abbrev empty_diff_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_diff_2 EqSet2E EqSet2M
abbrev empty_inter_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_inter_1 EqSet2E EqSet2M
abbrev empty_inter_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_inter_2 EqSet2E EqSet2M
abbrev empty_is_empty_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_is_empty_1 EqSet2E EqSet2M
abbrev empty_is_empty_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_is_empty_2 EqSet2E EqSet2M
abbrev empty_union_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_union_1 EqSet2E EqSet2M
abbrev empty_union_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.empty_union_2 EqSet2E EqSet2M
abbrev equal_refl :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.equal_refl EqSet2E EqSet2M
abbrev equal_sym :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.equal_sym EqSet2E EqSet2M
abbrev equal_trans :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.equal_trans EqSet2E EqSet2M
abbrev fold_0 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_0 EqSet2E EqSet2M
abbrev fold_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_1 EqSet2E EqSet2M
abbrev fold_1b :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_1b EqSet2E EqSet2M
abbrev fold_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_2 EqSet2E EqSet2M
abbrev fold_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_add EqSet2E EqSet2M
abbrev fold_commutes :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_commutes EqSet2E EqSet2M
abbrev fold_diff_inter :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_diff_inter EqSet2E EqSet2M
abbrev fold_empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_empty EqSet2E EqSet2M
abbrev fold_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_equal EqSet2E EqSet2M
abbrev fold_identity :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_identity EqSet2E EqSet2M
abbrev fold_init :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_init EqSet2E EqSet2M
abbrev fold_plus :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_plus EqSet2E EqSet2M
abbrev fold_rec :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_rec EqSet2M
abbrev fold_rec_bis :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_rec_bis EqSet2M
abbrev fold_rec_nodep :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_rec_nodep EqSet2M
abbrev fold_rec_weak :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_rec_weak EqSet2M
abbrev fold_rel :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_rel EqSet2M
abbrev fold_spec_right :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_spec_right EqSet2E EqSet2M
abbrev fold_union :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_union EqSet2E EqSet2M
abbrev fold_union_inter :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.fold_union_inter EqSet2E EqSet2M
abbrev in_subset :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.in_subset EqSet2E EqSet2M
abbrev inter_Add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_Add EqSet2E EqSet2M
abbrev inter_Add_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_Add_2 EqSet2E EqSet2M
abbrev inter_add_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_add_1 EqSet2E EqSet2M
abbrev inter_add_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_add_2 EqSet2E EqSet2M
abbrev inter_assoc :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_assoc EqSet2E EqSet2M
abbrev inter_equal_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_equal_1 EqSet2E EqSet2M
abbrev inter_equal_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_equal_2 EqSet2E EqSet2M
abbrev inter_subset_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_subset_1 EqSet2E EqSet2M
abbrev inter_subset_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_subset_2 EqSet2E EqSet2M
abbrev inter_subset_3 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_subset_3 EqSet2E EqSet2M
abbrev inter_subset_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_subset_equal EqSet2E EqSet2M
abbrev inter_sym :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.inter_sym EqSet2E EqSet2M
abbrev not_in_union :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.not_in_union EqSet2E EqSet2M
abbrev of_list :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.of_list EqSet2E EqSet2M
abbrev of_list_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.of_list_1 EqSet2E EqSet2M
abbrev of_list_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.of_list_2 EqSet2E EqSet2M
abbrev of_list_3 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.of_list_3 EqSet2E EqSet2M
abbrev remove_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_add EqSet2E EqSet2M
abbrev remove_cardinal_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_cardinal_1 EqSet2E EqSet2M
abbrev remove_cardinal_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_cardinal_2 EqSet2E EqSet2M
abbrev remove_diff_singleton :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_diff_singleton EqSet2E EqSet2M
abbrev remove_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_equal EqSet2E EqSet2M
abbrev remove_fold_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_fold_1 EqSet2E EqSet2M
abbrev remove_fold_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_fold_2 EqSet2E EqSet2M
abbrev remove_singleton_empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.remove_singleton_empty EqSet2E EqSet2M
abbrev set_induction :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.set_induction EqSet2M
abbrev set_induction_bis :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.set_induction_bis EqSet2M
abbrev singleton_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.singleton_cardinal EqSet2E EqSet2M
abbrev singleton_equal_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.singleton_equal_add EqSet2E EqSet2M
abbrev subset_add_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_add_2 EqSet2E EqSet2M
abbrev subset_add_3 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_add_3 EqSet2E EqSet2M
abbrev subset_antisym :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_antisym EqSet2E EqSet2M
abbrev subset_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_cardinal EqSet2E EqSet2M
abbrev subset_cardinal_lt :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_cardinal_lt EqSet2E EqSet2M
abbrev subset_diff :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_diff EqSet2E EqSet2M
abbrev subset_empty :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_empty EqSet2E EqSet2M
abbrev subset_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_equal EqSet2E EqSet2M
abbrev subset_refl :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_refl EqSet2E EqSet2M
abbrev subset_remove_3 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_remove_3 EqSet2E EqSet2M
abbrev subset_trans :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.subset_trans EqSet2E EqSet2M
abbrev to_list :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.to_list EqSet2E EqSet2M
abbrev union_Add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_Add EqSet2E EqSet2M
abbrev union_Equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_Equal EqSet2E EqSet2M
abbrev union_add :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_add EqSet2E EqSet2M
abbrev union_assoc :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_assoc EqSet2E EqSet2M
abbrev union_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_cardinal EqSet2E EqSet2M
abbrev union_cardinal_inter :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_cardinal_inter EqSet2E EqSet2M
abbrev union_cardinal_le :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_cardinal_le EqSet2E EqSet2M
abbrev union_equal_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_equal_1 EqSet2E EqSet2M
abbrev union_equal_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_equal_2 EqSet2E EqSet2M
abbrev union_inter_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_inter_1 EqSet2E EqSet2M
abbrev union_inter_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_inter_2 EqSet2E EqSet2M
abbrev union_inter_cardinal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_inter_cardinal EqSet2E EqSet2M
abbrev union_remove_add_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_remove_add_1 EqSet2E EqSet2M
abbrev union_remove_add_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_remove_add_2 EqSet2E EqSet2M
abbrev union_subset_1 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_1 EqSet2E EqSet2M
abbrev union_subset_2 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_2 EqSet2E EqSet2M
abbrev union_subset_3 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_3 EqSet2E EqSet2M
abbrev union_subset_4 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_4 EqSet2E EqSet2M
abbrev union_subset_5 :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_5 EqSet2E EqSet2M
abbrev union_subset_equal :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_subset_equal EqSet2E EqSet2M
abbrev union_sym :=
  CompCert4Lean.Lib.FSetProperties.WProperties_fun.union_sym EqSet2E EqSet2M

end ESP2

namespace ESD2

def ESD2 : CompCert4Lean.Lib.FSetDecide.Decide EqSet2E EqSet2M :=
  CompCert4Lean.Lib.FSetDecide.WDecide_fun.make EqSet2E EqSet2M
abbrev F : CompCert4Lean.Lib.FSetDecide.F EqSet2E EqSet2M :=
  CompCert4Lean.Backend.Allocproof.ESD2.ESD2.F
def FSetDecideAuxiliary :
    CompCert4Lean.Lib.FSetDecide.WDecide_fun.FSetDecideAuxiliary EqSet2E EqSet2M :=
  ⟨ESD2⟩
def FSetDecideTestCases :
    CompCert4Lean.Lib.FSetDecide.WDecide_fun.FSetDecideTestCases EqSet2E EqSet2M :=
  ⟨ESD2⟩
def FSetLogicalFacts :
    CompCert4Lean.Lib.FSetDecide.WDecide_fun.FSetLogicalFacts EqSet2E EqSet2M :=
  ⟨ESD2⟩

end ESD2

def match_prog (cfg : CompilerConfig) (oracle : RegallocOracle)
    (p : RTL.program) (tp : LTL.program) : Prop :=
  @match_program RTL.fundef Unit LTL.fundef Unit
    (Linker_fundef RTL.function) Linker_unit
    (fun _ f tf => CompCert4Lean.Backend.Allocation.transf_fundef cfg oracle f = .OK tf)
    Eq p tp

def expand_move (m : move) : LTL.instruction :=
  match m with
  | MV (R src) (R dst) => Lop Omove [src] dst
  | MV (S sl ofs ty) (R dst) => Lgetstack sl ofs ty dst
  | MV (R src) (S sl ofs ty) => Lsetstack src sl ofs ty
  | MV (S _ _ _) (S _ _ _) => Lreturn
  | MVmakelong src1 src2 dst => Lop Omakelong [src1, src2] dst
  | MVlowlong src dst => Lop Olowlong [src] dst
  | MVhighlong src dst => Lop Ohighlong [src] dst

def expand_moves (mv : moves) (k : LTL.bblock) : LTL.bblock :=
  List.append (List.map expand_move mv) k

def wf_move (m : move) : Prop :=
  match m with
  | MV (S _ _ _) (S _ _ _) => False
  | _ => True

def wf_moves (mv : moves) : Prop :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.Forall wf_move mv

inductive expand_block_shape : block_shape → RTL.instruction → LTL.bblock → Prop where
  | ebs_nop (mv : moves) (s : RTL.node) (k : LTL.bblock) :
      wf_moves mv →
      expand_block_shape (BSnop mv s) (Inop s)
        (expand_moves mv (Lbranch s :: k))
  | ebs_move (src dst : reg) (mv : moves) (s : RTL.node) (k : LTL.bblock) :
      wf_moves mv →
      expand_block_shape (BSmove src dst mv s) (Iop Omove [src] dst s)
        (expand_moves mv (Lbranch s :: k))
  | ebs_makelong (src1 src2 dst : reg) (mv : moves) (s : RTL.node)
      (k : LTL.bblock) :
      wf_moves mv → CompCert4Lean.X86_64.Archi.splitlong = true →
      expand_block_shape (BSmakelong src1 src2 dst mv s)
        (Iop Omakelong [src1, src2] dst s)
        (expand_moves mv (Lbranch s :: k))
  | ebs_lowlong (src dst : reg) (mv : moves) (s : RTL.node)
      (k : LTL.bblock) :
      wf_moves mv → CompCert4Lean.X86_64.Archi.splitlong = true →
      expand_block_shape (BSlowlong src dst mv s) (Iop Olowlong [src] dst s)
        (expand_moves mv (Lbranch s :: k))
  | ebs_highlong (src dst : reg) (mv : moves) (s : RTL.node)
      (k : LTL.bblock) :
      wf_moves mv → CompCert4Lean.X86_64.Archi.splitlong = true →
      expand_block_shape (BShighlong src dst mv s) (Iop Ohighlong [src] dst s)
        (expand_moves mv (Lbranch s :: k))
  | ebs_op (op : operation) (args : List reg) (res : reg) (mv1 : moves)
      (args' : List CompCert4Lean.X86.Machregs.mreg)
      (res' : CompCert4Lean.X86.Machregs.mreg) (mv2 : moves) (s : RTL.node)
      (k : LTL.bblock) :
      wf_moves mv1 → wf_moves mv2 →
      expand_block_shape (BSop op args res mv1 args' res' mv2 s)
        (Iop op args res s)
        (expand_moves mv1 (Lop op args' res' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_op_dead (op : operation) (args : List reg) (res : reg) (mv : moves)
      (s : RTL.node) (k : LTL.bblock) :
      wf_moves mv →
      expand_block_shape (BSopdead op args res mv s)
        (Iop op args res s) (expand_moves mv (Lbranch s :: k))
  | ebs_load (chunk : memory_chunk) (addr : addressing) (args : List reg)
      (dst : reg) (mv1 : moves)
      (args' : List CompCert4Lean.X86.Machregs.mreg)
      (dst' : CompCert4Lean.X86.Machregs.mreg)
      (mv2 : moves) (s : RTL.node) (k : LTL.bblock) :
      wf_moves mv1 → wf_moves mv2 →
      expand_block_shape (BSload chunk addr args dst mv1 args' dst' mv2 s)
        (Iload chunk addr args dst s)
        (expand_moves mv1
          (Lload chunk addr args' dst' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_load2 (addr addr2 : addressing) (args : List reg) (dst : reg)
      (mv1 : moves) (args1' : List CompCert4Lean.X86.Machregs.mreg)
      (dst1' : CompCert4Lean.X86.Machregs.mreg) (mv2 : moves)
      (args2' : List CompCert4Lean.X86.Machregs.mreg)
      (dst2' : CompCert4Lean.X86.Machregs.mreg) (mv3 : moves) (s : RTL.node)
      (k : LTL.bblock) :
      wf_moves mv1 → wf_moves mv2 → wf_moves mv3 →
      CompCert4Lean.X86_64.Archi.splitlong = true →
      offset_addressing addr (ZArith.BinInt.Z.of_nat 4) = some addr2 →
      expand_block_shape (BSload2 addr addr2 args dst mv1 args1' dst1' mv2
        args2' dst2' mv3 s) (Iload Mint64 addr args dst s)
        (expand_moves mv1
          (Lload Mint32 addr args1' dst1' ::
            expand_moves mv2 (Lload Mint32 addr2 args2' dst2' ::
              expand_moves mv3 (Lbranch s :: k))))
  | ebs_load2_1 (addr : addressing) (args : List reg) (dst : reg)
      (mv1 : moves) (args' : List CompCert4Lean.X86.Machregs.mreg)
      (dst' : CompCert4Lean.X86.Machregs.mreg) (mv2 : moves)
      (s : RTL.node) (k : LTL.bblock) :
      wf_moves mv1 → wf_moves mv2 →
      CompCert4Lean.X86_64.Archi.splitlong = true →
      expand_block_shape (BSload2_1 addr args dst mv1 args' dst' mv2 s)
        (Iload Mint64 addr args dst s)
        (expand_moves mv1 (Lload Mint32 addr args' dst' ::
          expand_moves mv2 (Lbranch s :: k)))
  | ebs_load2_2 (addr addr2 : addressing) (args : List reg) (dst : reg)
      (mv1 : moves) (args' : List CompCert4Lean.X86.Machregs.mreg)
      (dst' : CompCert4Lean.X86.Machregs.mreg) (mv2 : moves)
      (s : RTL.node) (k : LTL.bblock) :
      wf_moves mv1 → wf_moves mv2 →
      CompCert4Lean.X86_64.Archi.splitlong = true →
      offset_addressing addr (ZArith.BinInt.Z.of_nat 4) = some addr2 →
      expand_block_shape (BSload2_2 addr addr2 args dst mv1 args' dst' mv2 s)
        (Iload Mint64 addr args dst s)
        (expand_moves mv1 (Lload Mint32 addr2 args' dst' ::
          expand_moves mv2 (Lbranch s :: k)))
  | ebs_load_dead (chunk : memory_chunk) (addr : addressing) (args : List reg)
      (dst : reg) (mv : moves) (s : RTL.node) (k : LTL.bblock) :
      wf_moves mv →
      expand_block_shape (BSloaddead chunk addr args dst mv s)
        (Iload chunk addr args dst s) (expand_moves mv (Lbranch s :: k))
  | ebs_store (chunk : memory_chunk) (addr : addressing) (args : List reg)
      (src : reg) (mv1 : moves)
      (args' : List CompCert4Lean.X86.Machregs.mreg)
      (src' : CompCert4Lean.X86.Machregs.mreg)
      (s : RTL.node) (k : LTL.bblock) :
      wf_moves mv1 →
      expand_block_shape (BSstore chunk addr args src mv1 args' src' s)
        (Istore chunk addr args src s)
        (expand_moves mv1 (Lstore chunk addr args' src' :: Lbranch s :: k))
  | ebs_store2 (addr addr2 : addressing) (args : List reg) (src : reg)
      (mv1 : moves) (args1' : List CompCert4Lean.X86.Machregs.mreg)
      (src1' : CompCert4Lean.X86.Machregs.mreg) (mv2 : moves)
      (args2' : List CompCert4Lean.X86.Machregs.mreg)
      (src2' : CompCert4Lean.X86.Machregs.mreg) (s : RTL.node) (k : LTL.bblock) :
      wf_moves mv1 → wf_moves mv2 →
      CompCert4Lean.X86_64.Archi.splitlong = true →
      offset_addressing addr (ZArith.BinInt.Z.of_nat 4) = some addr2 →
      expand_block_shape (BSstore2 addr addr2 args src mv1 args1' src1'
        mv2 args2' src2' s) (Istore Mint64 addr args src s)
        (expand_moves mv1 (Lstore Mint32 addr args1' src1' ::
          expand_moves mv2 (Lstore Mint32 addr2 args2' src2' ::
            Lbranch s :: k)))
  | ebs_call (sg : signature) (ros : Sum reg ident) (args : List reg)
      (res : reg) (mv1 : moves) (ros' : Sum mreg ident) (mv2 : moves)
      (s : RTL.node) (k : LTL.bblock) :
      wf_moves mv1 → wf_moves mv2 →
      expand_block_shape (BScall sg ros args res mv1 ros' mv2 s)
        (Icall sg ros args res s)
        (expand_moves mv1 (Lcall sg ros' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_tailcall (sg : signature) (ros : Sum reg ident) (args : List reg)
      (mv : moves) (ros' : Sum mreg ident) (k : LTL.bblock) :
      wf_moves mv →
      expand_block_shape (BStailcall sg ros args mv ros')
        (Itailcall sg ros args) (expand_moves mv (Ltailcall sg ros' :: k))
  | ebs_builtin (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (mv1 : moves) (args' : List (builtin_arg loc))
      (res' : builtin_res mreg) (mv2 : moves) (s : RTL.node)
      (k : LTL.bblock) :
      wf_moves mv1 → wf_moves mv2 →
      expand_block_shape (BSbuiltin ef args res mv1 args' res' mv2 s)
        (Ibuiltin ef args res s)
        (expand_moves mv1
          (Lbuiltin ef args' res' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_cond (cond : condition) (args : List reg) (mv : moves)
      (args' : List mreg) (s1 s2 : RTL.node) (k : LTL.bblock) :
      wf_moves mv →
      expand_block_shape (BScond cond args mv args' s1 s2)
        (Icond cond args s1 s2) (expand_moves mv (Lcond cond args' s1 s2 :: k))
  | ebs_jumptable (arg : reg) (mv : moves) (arg' : mreg)
      (tbl : List RTL.node) (k : LTL.bblock) :
      wf_moves mv →
      expand_block_shape (BSjumptable arg mv arg' tbl) (Ijumptable arg tbl)
        (expand_moves mv (Ljumptable arg' tbl :: k))
  | ebs_return (optarg : Option reg) (mv : moves) (k : LTL.bblock) :
      wf_moves mv →
      expand_block_shape (BSreturn optarg mv) (Ireturn optarg)
        (expand_moves mv (Lreturn :: k))

export expand_block_shape
  (ebs_nop ebs_move ebs_makelong ebs_lowlong ebs_highlong ebs_op ebs_op_dead
   ebs_load ebs_load2 ebs_load2_1 ebs_load2_2 ebs_load_dead ebs_store
   ebs_store2 ebs_call ebs_tailcall ebs_builtin ebs_cond ebs_jumptable
   ebs_return)

def sel_val (k : equation_kind) (v : val) : val :=
  match k with
  | Full => v
  | Low => Val.loword v
  | High => Val.hiword v

def satisf (rs : RTL.regset) (ls : LTL.locset) (e : eqs) : Prop :=
  ∀ q, EqSet.In q e →
    Val.lessdef (sel_val (ekind q) (Regmap.get (ereg q) rs)) (ls (eloc q))

inductive transf_function_spec (cfg : CompilerConfig) (oracle : RegallocOracle)
    (f : RTL.function) (tf : LTL.function) : Prop where
  | transf_function_spec_intro (env : regenv) (an : PMap.t (res eqs)) (mv : moves)
      (k : LTL.bblock) (e1 e2 : eqs)
      (hwt : wt_function cfg f env)
      (hanalyze : analyze cfg f env (pair_codes f tf) = some an)
      (hentry : PTree.get tf.fn_entrypoint tf.fn_code =
        some (expand_moves mv (Lbranch f.fn_entrypoint :: k)))
      (hmoves : wf_moves mv)
      (htransfer : transfer cfg f env (pair_codes f tf) f.fn_entrypoint
        (PMap.get f.fn_entrypoint an) = .OK e1)
      (htrack : track_moves env mv e1 = some e2)
      (hcompat : compat_entry f.fn_params (loc_parameters cfg tf.fn_sig) e2 = true)
      (hundef : can_undef destroyed_at_function_entry e2 = true)
      (hstack : f.fn_stacksize = tf.fn_stacksize)
      (hsig : f.fn_sig = tf.fn_sig) :
      transf_function_spec cfg oracle f tf

export transf_function_spec (transf_function_spec_intro)

inductive match_stackframes
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompilerConfig) (oracle : RegallocOracle)
    (xi : ExternalCalls) (tprog : LTL.program) :
    List RTL.stackframe → List LTL.stackframe → signature → Prop where
  | match_stackframes_nil (sg : signature) (hres : sg.sig_res = Xint) :
      match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog [] [] sg
  | match_stackframes_cons (resultReg : reg) (f : RTL.function) (sp : val) (pc : RTL.node)
      (rs : RTL.regset) (s : List RTL.stackframe) (tf : LTL.function)
      (bb : LTL.bblock) (ls : LTL.locset) (ts : List LTL.stackframe)
      (sg : signature) (an : PMap.t (res eqs)) (e : eqs) (env : regenv)
      (hstacks : match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog s ts tf.fn_sig)
      (hfun : transf_function cfg oracle f = .OK tf)
      (hanalyze : analyze cfg f env (pair_codes f tf) = some an)
      (heq : transfer cfg f env (pair_codes f tf) pc (PMap.get pc an) = .OK e)
      (hwtf : wt_function cfg f env)
      (hwtrs : wt_regset env rs)
      (hwtres : env resultReg = proj_sig_res sg)
      (hsteps : ∀ v ls1 m,
        Val.lessdef v (Locmap.getpair (map_rpair R (loc_result sg)) ls1) →
        Val.has_type v (env resultReg) → agree_callee_save cfg ls ls1 →
        ∃ ls2,
          star (LTL.step
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            cfg xi) (Genv.globalenv tprog)
            (LTL.Block ts tf sp bb ls1 m) E0 (LTL.State ts tf sp pc ls2 m) ∧
          satisf (Regmap.set resultReg v rs) ls2 e) :
      match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog
        (RTL.Stackframe resultReg f sp pc rs :: s)
        (LTL.Stackframe tf sp ls bb :: ts) sg

export match_stackframes (match_stackframes_nil match_stackframes_cons)

inductive match_states
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompilerConfig) (oracle : RegallocOracle)
    (xi : ExternalCalls) (tprog : LTL.program) : RTL.state → LTL.state → Prop where
  | match_states_intro (s : List RTL.stackframe) (f : RTL.function) (sp : val)
      (pc : RTL.node) (rs : RTL.regset) (m : mem) (ts : List LTL.stackframe)
      (tf : LTL.function) (ls : LTL.locset) (m' : mem)
      (an : PMap.t (res eqs)) (e : eqs) (env : regenv)
      (hstacks : match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog s ts tf.fn_sig)
      (hfun : transf_function cfg oracle f = .OK tf)
      (hanalyze : analyze cfg f env (pair_codes f tf) = some an)
      (heq : transfer cfg f env (pair_codes f tf) pc (PMap.get pc an) = .OK e)
      (hsat : satisf rs ls e) (hmem : Mem.extends m m')
      (hwtf : wt_function cfg f env) (hwtrs : wt_regset env rs) :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog (RTL.State s f sp pc rs m)
        (LTL.State ts tf sp pc ls m')
  | match_states_call (s : List RTL.stackframe) (f : RTL.fundef) (args : List val)
      (m : mem) (ts : List LTL.stackframe) (tf : LTL.fundef)
      (ls : LTL.locset) (m' : mem)
      (hstacks : match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog s ts (LTL.funsig tf))
      (hfun : transf_fundef cfg oracle f = .OK tf)
      (hargs : Val.lessdef_list args
        ((loc_arguments cfg (LTL.funsig tf)).map (fun p => Locmap.getpair p ls)))
      (hag : agree_callee_save cfg (LTL.parent_locset ts) ls)
      (hmem : Mem.extends m m')
      (hwtargs : Val.has_type_list args (proj_sig_args (LTL.funsig tf))) :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog (RTL.Callstate s f args m)
        (LTL.Callstate ts tf ls m')
  | match_states_return (s : List RTL.stackframe) (result : val) (m : mem)
      (ts : List LTL.stackframe) (ls : LTL.locset) (m' : mem) (sg : signature)
      (hstacks : match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog s ts sg)
      (hres : Val.lessdef result
        (Locmap.getpair (map_rpair R (loc_result sg)) ls))
      (hag : agree_callee_save cfg (LTL.parent_locset ts) ls)
      (hmem : Mem.extends m m')
      (hwtres : Val.has_type result (proj_sig_res sg)) :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog (RTL.Returnstate s result m)
        (LTL.Returnstate ts ls m')

export match_states (match_states_intro match_states_call match_states_return)

/-! ## Exact statement descriptors -/

def transf_program_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle)
    (p : RTL.program) (tp : LTL.program),
    transf_program cfg oracle p = .OK tp → match_prog cfg oracle p tp

def expand_moves_consStatement : Prop :=
  ∀ (m : move) (accu : List move) (b : LTL.bblock),
    expand_moves (m :: accu).reverse b =
      expand_moves accu.reverse (expand_move m :: b)

def extract_moves_soundStatement : Prop :=
  ∀ (b : LTL.bblock) (mv : moves) (b' : LTL.bblock),
    extract_moves [] b = (mv, b') →
      wf_moves mv ∧ b = expand_moves mv b'

def extract_moves_ext_soundStatement : Prop :=
  ∀ (b : LTL.bblock) (mv : moves) (b' : LTL.bblock),
    extract_moves_ext [] b = (mv, b') →
      wf_moves mv ∧ b = expand_moves mv b'

def check_succ_soundStatement : Prop :=
  ∀ (s : LTL.node) (b : LTL.bblock), check_succ s b = true →
    ∃ k : List LTL.instruction, b = Lbranch s :: k

def pair_instr_block_soundStatement : Prop :=
  ∀ (i : RTL.instruction) (b : LTL.bblock) (bsh : block_shape),
    pair_instr_block i b = some bsh → expand_block_shape bsh i b

def matching_instr_blockStatement : Prop :=
  ∀ (f1 : RTL.function) (f2 : LTL.function) (pc : positive)
    (bsh : block_shape) (i : RTL.instruction),
    PTree.get pc (pair_codes f1 f2) = some bsh →
    PTree.get pc f1.fn_code = some i →
    ∃ b : LTL.bblock,
      PTree.get pc f2.fn_code = some b ∧ expand_block_shape bsh i b

def satisf_incrStatement : Prop :=
  ∀ (rs : RTL.regset) (ls : LTL.locset) (e1 e2 : eqs),
    satisf rs ls e2 → EqSet.Subset e1 e2 → satisf rs ls e1

def add_equation_lessdefStatement : Prop :=
  ∀ (rs : RTL.regset) (ls : LTL.locset) (q : equation) (e : eqs),
    satisf rs ls (add_equation q e) →
      Val.lessdef (sel_val q.ekind (Regmap.get q.ereg rs)) (ls q.eloc)

def add_equation_satisfStatement : Prop :=
  ∀ (rs : RTL.regset) (ls : LTL.locset) (q : equation) (e : eqs),
    satisf rs ls (add_equation q e) → satisf rs ls e

def add_equations_satisfStatement : Prop :=
  ∀ (rs : RTL.regset) (ls : LTL.locset) (rl : List reg) (ml : List mreg)
    (e e' : eqs),
    add_equations rl ml e = some e' → satisf rs ls e' → satisf rs ls e

def add_equations_lessdefStatement : Prop :=
  ∀ (rs : RTL.regset) (ls : LTL.locset) (rl : List reg) (ml : List mreg)
    (e e' : eqs),
    add_equations rl ml e = some e' → satisf rs ls e' →
      Val.lessdef_list (rl.map (fun r => Regmap.get r rs)) (LTL.reglist ls ml)

def add_equations_args_satisfStatement : Prop :=
  ∀ (rs : RTL.regset) (ls : LTL.locset) (rl : List reg) (tyl : List typ)
    (ll : List (rpair loc)) (e e' : eqs),
    add_equations_args rl tyl ll e = some e' → satisf rs ls e' → satisf rs ls e

def val_longofwords_eq_1Statement : Prop :=
  ∀ (v : val), Val.has_type v Tlong →
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    Val.longofwords (Val.hiword v) (Val.loword v) = v

def val_longofwords_eq_2Statement : Prop :=
  ∀ (v : val), Val.has_type v Tlong →
    CompCert4Lean.X86_64.Archi.splitlong = true →
    Val.longofwords (Val.hiword v) (Val.loword v) = v

def add_equations_args_lessdefStatement : Prop :=
  ∀ (rs : RTL.regset) (ls : LTL.locset) (rl : List reg) (tyl : List typ)
    (ll : List (rpair loc)) (e e' : eqs),
    add_equations_args rl tyl ll e = some e' → satisf rs ls e' →
    Val.has_type_list (rl.map (fun r => Regmap.get r rs)) tyl →
    Val.lessdef_list (rl.map (fun r => Regmap.get r rs))
      (ll.map (fun p => Locmap.getpair p ls))

def add_equation_ros_satisfStatement : Prop :=
  ∀ (rs : RTL.regset) (ls : LTL.locset) (ros : Sum reg ident)
    (mos : Sum mreg ident) (e e' : eqs),
    add_equation_ros ros mos e = some e' → satisf rs ls e' → satisf rs ls e

def select_reg_l_monotoneStatement : Prop :=
  ∀ (r : reg) (q1 q2 : OrderedEquation.t),
    (OrderedEquation.eq q1 q2 ∨ OrderedEquation.lt q1 q2) →
    select_reg_l r q1 = true → select_reg_l r q2 = true

def select_reg_h_monotoneStatement : Prop :=
  ∀ (r : reg) (q1 q2 : OrderedEquation.t),
    (OrderedEquation.eq q1 q2 ∨ OrderedEquation.lt q2 q1) →
    select_reg_h r q1 = true → select_reg_h r q2 = true

def select_reg_charactStatement : Prop :=
  ∀ (r : reg) (q : equation),
    (select_reg_l r q = true ∧ select_reg_h r q = true) ↔ q.ereg = r

def reg_unconstrained_soundStatement : Prop :=
  ∀ (r : reg) (e : eqs) (q : EqSet.elt),
    reg_unconstrained r e = true → EqSet.In q e → q.ereg ≠ r

def reg_unconstrained_satisfStatement : Prop :=
  ∀ (r : reg) (e : eqs) (rs : RTL.regset) (ls : LTL.locset) (v : val),
    reg_unconstrained r e = true → satisf rs ls e →
      satisf (Regmap.set r v rs) ls e

def select_loc_l_monotoneStatement : Prop :=
  ∀ (l : loc) (q1 q2 : «OrderedEquation'».t),
    («OrderedEquation'».eq q1 q2 ∨ «OrderedEquation'».lt q1 q2) →
    select_loc_l l q1 = true → select_loc_l l q2 = true

def select_loc_h_monotoneStatement : Prop :=
  ∀ (l : loc) (q1 q2 : «OrderedEquation'».t),
    («OrderedEquation'».eq q1 q2 ∨ «OrderedEquation'».lt q2 q1) →
    select_loc_h l q1 = true → select_loc_h l q2 = true

def select_loc_charactStatement : Prop :=
  ∀ (l : loc) (q : equation),
    (select_loc_l l q = false ∨ select_loc_h l q = false) ↔
      Loc.diff l q.eloc

def loc_unconstrained_soundStatement : Prop :=
  ∀ (l : loc) (e : eqs) (q : EqSet.elt),
    loc_unconstrained l e = true → EqSet.In q e → Loc.diff l q.eloc

def loc_unconstrained_satisfStatement : Prop :=
  ∀ (rs : RTL.regset) (ls : LTL.locset) (k : equation_kind) (r : reg)
    (mr : mreg) (e : eqs) (v : val),
    let l := R mr
    satisf rs ls (remove_equation { ekind := k, ereg := r, eloc := l } e) →
    loc_unconstrained (R mr)
      (remove_equation { ekind := k, ereg := r, eloc := l } e) = true →
    Val.lessdef (sel_val k (Regmap.get r rs)) v →
    satisf rs (Locmap.set l v ls) e

def reg_loc_unconstrained_soundStatement : Prop :=
  ∀ (r : reg) (l : loc) (e : eqs) (q : EqSet.elt),
    reg_loc_unconstrained r l e = true → EqSet.In q e →
      q.ereg ≠ r ∧ Loc.diff l q.eloc

def parallel_assignment_satisfStatement : Prop :=
  ∀ (k : equation_kind) (r : reg) (mr : mreg) (e : eqs)
    (rs : RTL.regset) (ls : LTL.locset) (v v' : val),
    let l := R mr
    Val.lessdef (sel_val k v) v' →
    reg_loc_unconstrained r (R mr)
      (remove_equation { ekind := k, ereg := r, eloc := l } e) = true →
    satisf rs ls (remove_equation { ekind := k, ereg := r, eloc := l } e) →
    satisf (Regmap.set r v rs) (Locmap.set l v' ls) e

def in_elements_between_1Statement : Prop :=
  ∀ (r1 : reg) (s : EqSet.t) (q : EqSet.elt),
    EqSet.In q (EqSet.elements_between (select_reg_l r1) (select_reg_h r1) s) ↔
      EqSet.In q s ∧ q.ereg = r1

def in_subst_regStatement : Prop :=
  ∀ (r1 r2 : reg) (q : EqSet.elt) (e : eqs), EqSet.In q e →
    (q.ereg = r1 ∧
      EqSet.In { ekind := q.ekind, ereg := r2, eloc := q.eloc }
        (subst_reg r1 r2 e)) ∨
    (q.ereg ≠ r1 ∧ EqSet.In q (subst_reg r1 r2 e))

def subst_reg_satisfStatement : Prop :=
  ∀ (src dst : reg) (rs : RTL.regset) (ls : LTL.locset) (e : eqs),
    satisf rs ls (subst_reg dst src e) →
      satisf (Regmap.set dst (Regmap.get src rs) rs) ls e

def in_subst_reg_kindStatement : Prop :=
  ∀ (r1 : reg) (k1 : equation_kind) (r2 : reg) (k2 : equation_kind)
    (q : EqSet.elt) (e : eqs), EqSet.In q e →
    (((q.ereg, q.ekind) = (r1, k1) ∧
      EqSet.In { ekind := k2, ereg := r2, eloc := q.eloc }
        (subst_reg_kind r1 k1 r2 k2 e)) ∨
      EqSet.In q (subst_reg_kind r1 k1 r2 k2 e))

def subst_reg_kind_satisf_makelongStatement : Prop :=
  ∀ (src1 src2 dst : reg) (rs : RTL.regset) (ls : LTL.locset) (e : eqs),
    let e1 := subst_reg_kind dst High src1 Full e
    let e2 := subst_reg_kind dst Low src2 Full e1
    reg_unconstrained dst e2 = true → satisf rs ls e2 →
    satisf (Regmap.set dst
      (Val.longofwords (Regmap.get src1 rs) (Regmap.get src2 rs)) rs) ls e

def subst_reg_kind_satisf_lowlongStatement : Prop :=
  ∀ (src dst : reg) (rs : RTL.regset) (ls : LTL.locset) (e : eqs),
    let e1 := subst_reg_kind dst Full src Low e
    reg_unconstrained dst e1 = true → satisf rs ls e1 →
      satisf (Regmap.set dst (Val.loword (Regmap.get src rs)) rs) ls e

def subst_reg_kind_satisf_highlongStatement : Prop :=
  ∀ (src dst : reg) (rs : RTL.regset) (ls : LTL.locset) (e : eqs),
    let e1 := subst_reg_kind dst Full src High e
    reg_unconstrained dst e1 = true → satisf rs ls e1 →
      satisf (Regmap.set dst (Val.hiword (Regmap.get src rs)) rs) ls e

def partial_fold_indStatement : Prop :=
  ∀ (A : Type) (P : EqSet2.t → A → Prop)
    (f : EqSet2.elt → A → Option A) (init final : A) (s : EqSet2.t),
    EqSet2.fold (fun q opte => match opte with
      | none => none
      | some e => f q e) s (some init) = some final →
    (∀ s', EqSet2.Empty s' → P s' init) →
    (∀ x a' a'' s' s'',
      EqSet2.In x s → ¬ EqSet2.In x s' → ESP2.Add x s' s'' →
      f x a' = some a'' → P s' a' → P s'' a'') →
    P s final

def in_subst_locStatement : Prop :=
  ∀ (l1 l2 : loc) (q : EqSet.elt) (e e' : eqs), EqSet.In q e →
    subst_loc l1 l2 e = some e' →
    (q.eloc = l1 ∧
      EqSet.In { ekind := q.ekind, ereg := q.ereg, eloc := l2 } e') ∨
    (Loc.diff l1 q.eloc ∧ EqSet.In q e')

def loc_type_compat_charactStatement : Prop :=
  ∀ (env : regenv) (l : loc) (e : eqs) (q : EqSet.elt),
    loc_type_compat env l e = true → EqSet.In q e →
    subtype (sel_type q.ekind (env q.ereg)) (Loc.type l) = true ∨
      Loc.diff l q.eloc

def well_typed_move_charactStatement : Prop :=
  ∀ (env : regenv) (l : loc) (e : eqs) (k : equation_kind)
    (r : reg) (rs : RTL.regset),
    well_typed_move env l e = true →
    EqSet.In { ekind := k, ereg := r, eloc := l } e →
    wt_regset env rs →
    match l with
    | R _ => True
    | S _ _ ty => Val.has_type (sel_val k (Regmap.get r rs)) ty

def val_lessdef_normalizeStatement : Prop :=
  ∀ (v v' : val) (ty : typ), Val.has_type v ty → Val.lessdef v v' →
    Val.lessdef v (Val.load_result (chunk_of_type ty) v')

def in_subst_loc_partStatement : Prop :=
  ∀ (l1 l2 : loc) (k : equation_kind) (q : EqSet.elt) (e e' : eqs),
    EqSet.In q e → subst_loc_part l1 l2 k e = some e' →
    (q.eloc = l1 ∧ q.ekind = k ∧
      EqSet.In { ekind := Full, ereg := q.ereg, eloc := l2 } e') ∨
    (Loc.diff l1 q.eloc ∧ EqSet.In q e')

def subst_loc_part_satisf_lowlongStatement : Prop :=
  ∀ (src dst : mreg) (rs : RTL.regset) (ls : LTL.locset) (e e' : eqs),
    subst_loc_part (R dst) (R src) Low e = some e' → satisf rs ls e' →
      satisf rs (Locmap.set (R dst) (Val.loword (ls (R src))) ls) e

def subst_loc_part_satisf_highlongStatement : Prop :=
  ∀ (src dst : mreg) (rs : RTL.regset) (ls : LTL.locset) (e e' : eqs),
    subst_loc_part (R dst) (R src) High e = some e' → satisf rs ls e' →
      satisf rs (Locmap.set (R dst) (Val.hiword (ls (R src))) ls) e

def in_subst_loc_pairStatement : Prop :=
  ∀ (l1 l2 l2' : loc) (q : EqSet.elt) (e e' : eqs), EqSet.In q e →
    subst_loc_pair l1 l2 l2' e = some e' →
    (q.eloc = l1 ∧ q.ekind = Full ∧
      EqSet.In { ekind := High, ereg := q.ereg, eloc := l2 } e' ∧
      EqSet.In { ekind := Low, ereg := q.ereg, eloc := l2' } e') ∨
    (Loc.diff l1 q.eloc ∧ EqSet.In q e')

def long_type_compat_charactStatement : Prop :=
  ∀ (env : regenv) (l : loc) (e : eqs) (q : EqSet.elt),
    long_type_compat env l e = true → EqSet.In q e →
      subtype (env q.ereg) Tlong = true ∨ Loc.diff l q.eloc

def subst_loc_pair_satisf_makelongStatement : Prop :=
  ∀ (env : regenv) (src1 src2 dst : mreg) (rs : RTL.regset)
    (ls : LTL.locset) (e e' : eqs),
    subst_loc_pair (R dst) (R src1) (R src2) e = some e' →
    long_type_compat env (R dst) e = true → wt_regset env rs →
    satisf rs ls e' → CompCert4Lean.X86_64.Archi.ptr64 = false →
    satisf rs (Locmap.set (R dst)
      (Val.longofwords (ls (R src1)) (ls (R src2))) ls) e

def can_undef_soundStatement : Prop :=
  ∀ (e : eqs) (ml : List mreg) (q : EqSet.elt),
    can_undef ml e = true → EqSet.In q e →
      Loc.notin q.eloc (ml.map R)

def undef_regs_outsideStatement : Prop :=
  ∀ (ml : List mreg) (ls : LTL.locset) (l : loc),
    Loc.notin l (ml.map R) → LTL.undef_regs ml ls l = ls l

def can_undef_satisfStatement : Prop :=
  ∀ (ml : List mreg) (e : eqs) (rs : RTL.regset) (ls : LTL.locset),
    can_undef ml e = true → satisf rs ls e →
      satisf rs (LTL.undef_regs ml ls) e

def can_undef_except_soundStatement : Prop :=
  ∀ (lx : loc) (e : eqs) (ml : List mreg) (q : EqSet.elt),
    can_undef_except lx ml e = true → EqSet.In q e → Loc.diff q.eloc lx →
      Loc.notin q.eloc (ml.map R)

def subst_loc_undef_satisfStatement : Prop :=
  ∀ (env : regenv) (src dst : loc) (rs : RTL.regset) (ls : LTL.locset)
    (ml : List mreg) (e e' : eqs),
    subst_loc dst src e = some e' → well_typed_move env dst e = true →
    can_undef_except dst ml e = true → wt_regset env rs → satisf rs ls e' →
      satisf rs (Locmap.set dst (ls src) (LTL.undef_regs ml ls)) e

def transfer_use_def_satisfStatement : Prop :=
  ∀ (args : List reg) (resultReg : reg) (args' : List mreg)
    (resultMreg : mreg) (und : List mreg) (e e' : eqs)
    (rs : RTL.regset) (ls : LTL.locset),
    transfer_use_def args resultReg args' resultMreg und e = some e' →
    satisf rs ls e' →
    Val.lessdef_list (args.map (fun r => Regmap.get r rs))
      (LTL.reglist ls args') ∧
    ∀ v v', Val.lessdef v v' →
      satisf (Regmap.set resultReg v rs)
        (Locmap.set (R resultMreg) v' (LTL.undef_regs und ls)) e

def add_equations_res_lessdefStatement : Prop :=
  ∀ (r : reg) (ty : typ) (l : rpair mreg) (e e' : eqs)
    (rs : RTL.regset) (ls : LTL.locset),
    add_equations_res r ty l e = some e' → satisf rs ls e' →
    Val.has_type (Regmap.get r rs) ty →
      Val.lessdef (Regmap.get r rs) (Locmap.getpair (map_rpair R l) ls)

def return_regs_agree_callee_saveStatement : Prop :=
  ∀ (cfg : CompilerConfig) (caller callee : Locmap.t),
    agree_callee_save cfg caller (LTL.return_regs cfg caller callee)

def no_caller_saves_soundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (e : eqs) (q : EqSet.elt),
    no_caller_saves cfg e = true → EqSet.In q e →
      callee_save_loc cfg q.eloc

def val_hiword_longofwordsStatement : Prop :=
  ∀ (v1 v2 : val), Val.lessdef (Val.hiword (Val.longofwords v1 v2)) v1

def val_loword_longofwordsStatement : Prop :=
  ∀ (v1 v2 : val), Val.lessdef (Val.loword (Val.longofwords v1 v2)) v2

def function_return_satisfStatement : Prop :=
  ∀ (cfg : CompilerConfig) (rs : RTL.regset) (lsBefore : LTL.locset)
    (lsAfter : Locmap.t) (resultReg : reg) (resultLoc : rpair mreg)
    (sg : signature) (e e' : eqs) (v : val),
    resultLoc = loc_result sg →
    remove_equations_res resultReg resultLoc e = some e' →
    satisf rs lsBefore e' →
    ((regs_of_rpair resultLoc).map R).all
      (fun l => reg_loc_unconstrained resultReg l e') = true →
    no_caller_saves cfg e' = true →
    Val.lessdef v (Locmap.getpair (map_rpair R resultLoc) lsAfter) →
    agree_callee_save cfg lsBefore lsAfter →
      satisf (Regmap.set resultReg v rs) lsAfter e

def compat_left_soundStatement : Prop :=
  ∀ (r : reg) (l : loc) (e : eqs) (q : EqSet.elt),
    compat_left r l e = true → EqSet.In q e → q.ereg = r →
      q.ekind = Full ∧ q.eloc = l

def compat_left2_soundStatement : Prop :=
  ∀ (r : reg) (l1 l2 : loc) (e : eqs) (q : EqSet.elt),
    compat_left2 r l1 l2 e = true → EqSet.In q e → q.ereg = r →
      (q.ekind = High ∧ q.eloc = l1) ∨ (q.ekind = Low ∧ q.eloc = l2)

def compat_entry_satisfStatement : Prop :=
  ∀ (rl : List reg) (ll : List (rpair loc)) (e : eqs),
    compat_entry rl ll e = true →
    ∀ (vl : List val) (ls : Locmap.t),
      Val.lessdef_list vl (ll.map (fun p => Locmap.getpair p ls)) →
      satisf (RTL.init_regs vl rl) ls e

def call_regs_param_valuesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (sg : signature) (ls : LTL.locset),
    (loc_parameters cfg sg).map (fun p => Locmap.getpair p (LTL.call_regs ls)) =
      (loc_arguments cfg sg).map (fun p => Locmap.getpair p ls)

def return_regs_arg_valuesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (sg : signature) (ls1 ls2 : LTL.locset),
    tailcall_is_possible cfg sg = true →
    (loc_arguments cfg sg).map
      (fun p => Locmap.getpair p (LTL.return_regs cfg ls1 ls2)) =
    (loc_arguments cfg sg).map (fun p => Locmap.getpair p ls2)

def find_function_tailcallStatement : Prop :=
  ∀ (cfg : CompilerConfig) (tge : LTL.genv) (ros : Sum mreg ident)
    (ls1 ls2 : LTL.locset),
    ros_compatible_tailcall cfg ros = true →
      LTL.find_function tge ros (LTL.return_regs cfg ls1 ls2) =
        LTL.find_function tge ros ls2

def loadv_int64_splitStatement : Prop :=
  ∀ (m : mem) (a v : val), Mem.loadv Mint64 m a = some v →
    CompCert4Lean.X86_64.Archi.splitlong = true →
    ∃ v1 v2,
      Mem.loadv Mint32 m a = some
        (if CompCert4Lean.X86_64.Archi.big_endian then v1 else v2) ∧
      Mem.loadv Mint32 m
        (Val.add a (Vint (CompCert4Lean.Lib.Integers.Int.repr
          (ZArith.BinInt.Z.of_nat 4)))) = some
          (if CompCert4Lean.X86_64.Archi.big_endian then v2 else v1) ∧
      Val.lessdef (Val.hiword v) v1 ∧ Val.lessdef (Val.loword v) v2

def add_equations_builtin_arg_satisfStatement : Prop :=
  ∀ (env : regenv) (rs : RTL.regset) (ls : LTL.locset)
    (arg : builtin_arg reg) (arg' : builtin_arg loc) (e e' : eqs),
    add_equations_builtin_arg env arg arg' e = some e' →
      satisf rs ls e' → satisf rs ls e

def add_equations_builtin_arg_lessdefStatement : Prop :=
  ∀ (env : regenv) (ge : RTL.genv) (sp : val) (rs : RTL.regset)
    (ls : LTL.locset) (m : mem) (arg : builtin_arg reg) (v : val),
    eval_builtin_arg (Genv.to_senv ge) (fun r => Regmap.get r rs)
      sp m arg v →
    ∀ (e e' : eqs) (arg' : builtin_arg loc),
      add_equations_builtin_arg env arg arg' e = some e' →
      satisf rs ls e' → wt_regset env rs →
      ∃ v', eval_builtin_arg (Genv.to_senv ge) ls sp m arg' v' ∧
        Val.lessdef v v'

def add_equations_builtin_args_satisfStatement : Prop :=
  ∀ (env : regenv) (rs : RTL.regset) (ls : LTL.locset)
    (args : List (builtin_arg reg)) (args' : List (builtin_arg loc))
    (e e' : eqs),
    add_equations_builtin_args env args args' e = some e' →
      satisf rs ls e' → satisf rs ls e

def add_equations_builtin_args_lessdefStatement : Prop :=
  ∀ (env : regenv) (ge : RTL.genv) (sp : val) (rs : RTL.regset)
    (ls : LTL.locset) (m tm : mem) (args : List (builtin_arg reg))
    (vl : List val),
    eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs)
      sp m args vl →
    ∀ (args' : List (builtin_arg loc)) (e e' : eqs),
      add_equations_builtin_args env args args' e = some e' →
      satisf rs ls e' → wt_regset env rs → Mem.extends m tm →
      ∃ vl', eval_builtin_args (Genv.to_senv ge) ls sp tm args' vl' ∧
        Val.lessdef_list vl vl'

def add_equations_debug_args_satisfStatement : Prop :=
  ∀ (env : regenv) (rs : RTL.regset) (ls : LTL.locset)
    (args : List (builtin_arg reg)) (args' : List (builtin_arg loc))
    (e e' : eqs),
    add_equations_debug_args env args args' e = some e' →
      satisf rs ls e' → satisf rs ls e

def add_equations_debug_args_evalStatement : Prop :=
  ∀ (env : regenv) (ge : RTL.genv) (sp : val) (rs : RTL.regset)
    (ls : LTL.locset) (m tm : mem) (args : List (builtin_arg reg))
    (vl : List val),
    eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs)
      sp m args vl →
    ∀ (args' : List (builtin_arg loc)) (e e' : eqs),
      add_equations_debug_args env args args' e = some e' →
      satisf rs ls e' → wt_regset env rs → Mem.extends m tm →
      ∃ vl', eval_builtin_args (Genv.to_senv ge) ls sp tm args' vl'

def add_equations_builtin_evalStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ef : external_function) (env : regenv)
    (args : List (builtin_arg reg)) (args' : List (builtin_arg loc))
    (e1 e2 : eqs) (m1 m1' : mem) (rs : RTL.regset) (ls : LTL.locset)
    (ge : RTL.genv) (sp : val) (vargs : List val) (t : trace)
    (vres : val) (m2 : mem),
    wt_regset env rs →
    (match ef with
      | EF_debug _ _ _ => add_equations_debug_args env args args' e1
      | _ => add_equations_builtin_args env args args' e1) = some e2 →
    Mem.extends m1 m1' → satisf rs ls e2 →
    eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs)
      sp m1 args vargs →
    external_call
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ef (Genv.to_senv ge) vargs m1 t vres m2 →
    satisf rs ls e1 ∧
    ∃ vargs' vres' m2',
      eval_builtin_args (Genv.to_senv ge) ls sp m1' args' vargs' ∧
      external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge) vargs' m1' t vres' m2' ∧
      Val.lessdef vres vres' ∧ Mem.extends m2 m2'

def parallel_set_builtin_res_satisfStatement : Prop :=
  ∀ (env : regenv) (resultReg : builtin_res reg)
    (resultLoc : builtin_res mreg) (e0 e1 : eqs)
    (rs : RTL.regset) (ls : LTL.locset) (v v' : val),
    remove_equations_builtin_res env resultReg resultLoc e0 = some e1 →
    (params_of_builtin_res resultReg).all (fun r => reg_unconstrained r e1) = true →
    (params_of_builtin_res resultLoc).all
      (fun mr => loc_unconstrained (R mr) e1) = true →
    satisf rs ls e1 → Val.lessdef v v' →
      satisf (regmap_setres resultReg v rs) (Locmap.setres resultLoc v' ls) e0

def analyze_successorsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : RTL.function) (env : regenv)
    (bsh : PTree.t block_shape) (an : PMap.t (res eqs)) (pc : positive)
    (bs : block_shape) (s : LTL.node) (e : eqs),
    analyze cfg f env bsh = some an → PTree.get pc bsh = some bs →
    s ∈ successors_block_shape bs → PMap.get pc an = .OK e →
    ∃ e', transfer cfg f env bsh s (PMap.get s an) = .OK e' ∧
      EqSet.Subset e' e

def satisf_successorsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : RTL.function) (env : regenv)
    (bsh : PTree.t block_shape) (an : PMap.t (res eqs)) (pc : positive)
    (bs : block_shape) (s : LTL.node) (e : eqs)
    (rs : RTL.regset) (ls : LTL.locset),
    analyze cfg f env bsh = some an → PTree.get pc bsh = some bs →
    s ∈ successors_block_shape bs → PMap.get pc an = .OK e →
    satisf rs ls e →
    ∃ e', transfer cfg f env bsh s (PMap.get s an) = .OK e' ∧
      satisf rs ls e'

def transf_function_invStatement : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle)
    (f : RTL.function) (tf : LTL.function),
    transf_function cfg oracle f = .OK tf →
      transf_function_spec cfg oracle f tf

def invert_codeStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : RTL.function) (env : regenv)
    (tf : LTL.function) (pc : positive) (i : RTL.instruction)
    (opte : res eqs) (e : eqs),
    wt_function cfg f env → PTree.get pc f.fn_code = some i →
    transfer cfg f env (pair_codes f tf) pc opte = .OK e →
    ∃ eafter bsh bb,
      opte = .OK eafter ∧
      PTree.get pc (pair_codes f tf) = some bsh ∧
      PTree.get pc tf.fn_code = some bb ∧
      expand_block_shape bsh i bb ∧
      transfer_aux cfg f env bsh eafter = some e ∧
      wt_instr cfg f env i

def symbols_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle)
    (prog : RTL.program) (tprog : LTL.program),
    match_prog cfg oracle prog tprog → ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id

def senv_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle)
    (prog : RTL.program) (tprog : LTL.program),
    match_prog cfg oracle prog tprog →
      Senv.equiv (Genv.to_senv (Genv.globalenv prog))
        (Genv.to_senv (Genv.globalenv tprog))

def functions_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle)
    (prog : RTL.program) (tprog : LTL.program),
    match_prog cfg oracle prog tprog →
    ∀ (v : val) (f : RTL.fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      ∃ tf : LTL.fundef,
        Genv.find_funct (Genv.globalenv tprog) v = some tf ∧
        transf_fundef cfg oracle f = .OK tf

def function_ptr_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle)
    (prog : RTL.program) (tprog : LTL.program),
    match_prog cfg oracle prog tprog →
    ∀ (b : block) (f : RTL.fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      ∃ tf : LTL.fundef,
        Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
        transf_fundef cfg oracle f = .OK tf

def sig_function_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle)
    (f : RTL.fundef) (tf : LTL.fundef),
    transf_fundef cfg oracle f = .OK tf → LTL.funsig tf = RTL.funsig f

def find_function_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle)
    (prog : RTL.program) (tprog : LTL.program),
    match_prog cfg oracle prog tprog →
    ∀ (ros : Sum reg ident) (rs : RTL.regset) (fd : RTL.fundef)
      (ros' : Sum mreg ident) (e e' : eqs) (ls : LTL.locset),
      RTL.find_function (Genv.globalenv prog) ros rs = some fd →
      add_equation_ros ros ros' e = some e' → satisf rs ls e' →
      ∃ tfd : LTL.fundef,
        LTL.find_function (Genv.globalenv tprog) ros' ls = some tfd ∧
        transf_fundef cfg oracle fd = .OK tfd

def exec_movesStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (tprog : LTL.program)
    (mv : moves) (env : regenv) (rs : RTL.regset)
    (s : List LTL.stackframe) (f : LTL.function) (sp : val)
    (bb : LTL.bblock) (m : mem) (e e' : eqs) (ls : LTL.locset),
    track_moves env mv e = some e' → wf_moves mv → satisf rs ls e' →
    wt_regset env rs →
    ∃ ls', star (LTL.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg xi) (Genv.globalenv tprog)
      (LTL.Block s f sp (expand_moves mv bb) ls m) E0
      (LTL.Block s f sp bb ls' m) ∧ satisf rs ls' e

def match_stackframes_change_sigStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle) (xi : ExternalCalls)
    (tprog : LTL.program) (s : List RTL.stackframe)
    (ts : List LTL.stackframe) (sg sg' : signature),
    match_stackframes
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg oracle xi tprog s ts sg →
    sg'.sig_res = sg.sig_res →
      match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog s ts sg'

def addressing_not_longStatement : Prop :=
  ∀ (cfg : CompilerConfig) (env : regenv) (f : RTL.function)
    (addr : addressing) (args : List reg) (dst : reg) (s : RTL.node) (r : reg),
    wt_instr cfg f env (Iload Mint64 addr args dst s) →
    CompCert4Lean.X86_64.Archi.splitlong = true → r ∈ args → r ≠ dst

def step_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle) (xi : ExternalCalls)
    (prog : RTL.program) (tprog : LTL.program),
    match_prog cfg oracle prog tprog →
    ∀ (S1 : RTL.state) (t : trace) (S2 : RTL.state),
      RTL.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) S1 t S2 → wt_state cfg S1 →
      ∀ S1', match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg oracle xi tprog S1 S1' →
      ∃ S2', plus (LTL.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi) (Genv.globalenv tprog) S1' t S2' ∧
        match_states
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg oracle xi tprog S2 S2'

def initial_states_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle) (xi : ExternalCalls)
    (prog : RTL.program) (tprog : LTL.program),
    match_prog cfg oracle prog tprog →
    ∀ st1, RTL.initial_state prog st1 →
      ∃ st2, LTL.initial_state tprog st2 ∧
        match_states
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg oracle xi tprog st1 st2

def final_states_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle) (xi : ExternalCalls)
    (tprog : LTL.program) (st1 : RTL.state) (st2 : LTL.state)
    (r : CompCert4Lean.Lib.Integers.Int.int),
    match_states
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg oracle xi tprog st1 st2 →
      RTL.final_state st1 r → LTL.final_state st2 r

def wt_progStatement : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle)
    (prog : RTL.program) (tprog : LTL.program),
    match_prog cfg oracle prog tprog → wt_program cfg prog

def transf_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (oracle : RegallocOracle) (xi : ExternalCalls)
    (prog : RTL.program) (tprog : LTL.program),
    match_prog cfg oracle prog tprog →
      forward_simulation
        (RTL.semantics
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi prog)
        (LTL.semantics
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg xi tprog)

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem transf_program_match : transf_program_matchStatement := by
  intro cfg oracle p tp h
  letI : Linker RTL.program := by
    change Linker (CompCert4Lean.Common.AST.program
      (CompCert4Lean.Common.AST.fundef RTL.function) Unit)
    exact @Linker_prog (CompCert4Lean.Common.AST.fundef RTL.function) Unit
      (Linker_fundef RTL.function) Linker_unit
  unfold CompCert4Lean.Backend.Allocation.transf_program
    CompCert4Lean.Common.AST.transform_partial_program
    CompCert4Lean.Common.AST.transform_partial_program2 at h
  have hlist :
      ∀ (xs : List (ident × globdef RTL.fundef Unit))
        (ys : List (ident × globdef LTL.fundef Unit)),
        transf_globdefs (fun _ f => transf_fundef cfg oracle f)
            (fun _ v => .OK v) xs = .OK ys →
          list_forall2
            (match_ident_globdef
              (fun _ f tf => transf_fundef cfg oracle f = .OK tf)
              (fun x y : Unit => x = y) p) xs ys := by
    intro xs
    induction xs with
    | nil =>
        intro ys hys
        cases hys
        exact list_forall2.nil _
    | cons hd tl ih =>
        intro ys hys
        cases hd with
        | mk id gd =>
            cases gd with
            | Gfun f =>
                cases hf : transf_fundef cfg oracle f with
                | Error msg => simp [transf_globdefs, hf] at hys
                | OK tf =>
                    cases ht : transf_globdefs (fun _ f => transf_fundef cfg oracle f)
                      (fun _ v => .OK v) tl with
                    | Error msg => simp [transf_globdefs, hf, ht] at hys
                    | OK ysTail =>
                        simp only [transf_globdefs, hf, ht] at hys
                        cases hys
                        apply list_forall2.cons
                        · constructor
                          · rfl
                          · apply match_globdef.match_globdef_fun (ctx' := p)
                            · exact linkorder_refl _
                            · exact hf
                        · exact ih ysTail ht
            | Gvar v =>
                cases ht : transf_globdefs (fun _ f => transf_fundef cfg oracle f)
                  (fun _ v => .OK v) tl with
                | Error msg => simp [transf_globdefs, transf_globvar, ht] at hys
                | OK ysTail =>
                    simp only [transf_globdefs, transf_globvar, ht] at hys
                    cases hys
                    apply list_forall2.cons
                    · constructor
                      · rfl
                      · apply match_globdef.match_globdef_var
                        exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                    · exact ih ysTail ht
  cases hdefs : transf_globdefs (fun _ f => transf_fundef cfg oracle f)
      (fun _ v => .OK v) p.prog_defs with
  | Error msg => simp [hdefs] at h
  | OK defs =>
      simp only [hdefs] at h
      cases h
      unfold match_prog match_program match_program_gen
      exact ⟨hlist p.prog_defs defs hdefs, rfl, rfl⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Op
open CompCert4Lean.Lib.Coqlib

theorem expand_moves_cons : expand_moves_consStatement := by
  intro m accu b
  change List.append (List.map expand_move (m :: accu).reverse) b =
    List.append (List.map expand_move accu.reverse) (expand_move m :: b)
  rw [List.reverse_cons, List.map_append]
  exact List.append_assoc _ _ _

private theorem wf_moves_reverse {mv : CompCert4Lean.Backend.Allocation.moves}
    (h : wf_moves mv) :
    wf_moves (List.reverse mv) := by
  unfold wf_moves at h ⊢
  apply (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.Forall_forall wf_move _).2
  intro m hm
  apply (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.Forall_forall wf_move _).1 h m
  change m ∈ (show List move from mv)
  exact List.mem_reverse.mp hm

private theorem is_move_operation_correct_local {A : Type} (op : operation)
    (args : List A) (a : A) (h : is_move_operation op args = some a) :
    op = Omove ∧ args = [a] := by
  cases op with
  | Omove =>
      cases args with
      | nil => simp [is_move_operation] at h
      | cons x xs =>
          cases xs with
          | nil => simp [is_move_operation] at h ⊢; exact h
          | cons y ys => simp [is_move_operation] at h
  | _ => simp [is_move_operation] at h

private theorem extract_moves_aux :
    ∀ (b : LTL.bblock)
      (accu : CompCert4Lean.Backend.Allocation.moves)
      (mv : CompCert4Lean.Backend.Allocation.moves) (b' : LTL.bblock),
      extract_moves accu b = (mv, b') →
      wf_moves accu →
      wf_moves mv ∧ expand_moves (List.reverse accu) b = expand_moves mv b' := by
  intro b
  induction b with
  | nil =>
      intro accu mv b' h hacc
      simp [extract_moves] at h
      cases h
      exact ⟨wf_moves_reverse hacc, rfl⟩
  | cons a b ih =>
      intro accu mv b' h hacc
      cases a with
      | Lgetstack sl ofs ty dst =>
          simp only [extract_moves] at h
          have hh := ih (MV (S sl ofs ty) (R dst) :: accu) mv b' h
            (.cons (by simp [wf_move]) hacc)
          rcases hh with ⟨hmv, heq⟩
          constructor
          · exact hmv
          · simpa [expand_moves, expand_move] using
              (expand_moves_cons (MV (S sl ofs ty) (R dst)) accu b).symm.trans heq
      | Lsetstack src sl ofs ty =>
          simp only [extract_moves] at h
          have hh := ih (MV (R src) (S sl ofs ty) :: accu) mv b' h
            (.cons (by simp [wf_move]) hacc)
          rcases hh with ⟨hmv, heq⟩
          constructor
          · exact hmv
          · simpa [expand_moves, expand_move] using
              (expand_moves_cons (MV (R src) (S sl ofs ty)) accu b).symm.trans heq
      | Lop op args res =>
          cases hm : is_move_operation op args with
          | none =>
              simp [extract_moves, hm] at h
              cases h
              exact ⟨wf_moves_reverse hacc, rfl⟩
          | some arg =>
              rcases is_move_operation_correct_local op args arg hm with
                ⟨hop, hargs⟩
              subst op
              subst args
              simp [extract_moves, hm] at h
              have hh := ih (MV (R arg) (R res) :: accu) mv b' h
                (.cons (by simp [wf_move]) hacc)
              rcases hh with ⟨hmv, heq⟩
              constructor
              · exact hmv
              · simpa [expand_moves, expand_move] using
                  (expand_moves_cons (MV (R arg) (R res)) accu b).symm.trans heq
      | Lload chunk addr args dst =>
          simp [extract_moves] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lstore chunk addr args src =>
          simp [extract_moves] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lcall sg ros =>
          simp [extract_moves] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Ltailcall sg ros =>
          simp [extract_moves] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lbuiltin ef args res =>
          simp [extract_moves] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lbranch succ =>
          simp [extract_moves] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lcond cond args ifso ifnot =>
          simp [extract_moves] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Ljumptable arg tbl =>
          simp [extract_moves] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lreturn =>
          simp [extract_moves] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩

theorem extract_moves_sound : extract_moves_soundStatement := by
  intro b mv b' h
  exact extract_moves_aux b [] mv b' h .nil

private theorem extract_moves_ext_aux :
    ∀ (b : LTL.bblock)
      (accu : CompCert4Lean.Backend.Allocation.moves)
      (mv : CompCert4Lean.Backend.Allocation.moves) (b' : LTL.bblock),
      extract_moves_ext accu b = (mv, b') →
      wf_moves accu →
      wf_moves mv ∧ expand_moves (List.reverse accu) b = expand_moves mv b' := by
  intro b
  induction b with
  | nil =>
      intro accu mv b' h hacc
      simp [extract_moves_ext] at h
      cases h
      exact ⟨wf_moves_reverse hacc, rfl⟩
  | cons a b ih =>
      intro accu mv b' h hacc
      cases a with
      | Lgetstack sl ofs ty dst =>
          simp only [extract_moves_ext] at h
          have hh := ih (MV (S sl ofs ty) (R dst) :: accu) mv b' h
            (.cons (by simp [wf_move]) hacc)
          rcases hh with ⟨hmv, heq⟩
          constructor
          · exact hmv
          · simpa [expand_moves, expand_move] using
              (expand_moves_cons (MV (S sl ofs ty) (R dst)) accu b).symm.trans heq
      | Lsetstack src sl ofs ty =>
          simp only [extract_moves_ext] at h
          have hh := ih (MV (R src) (S sl ofs ty) :: accu) mv b' h
            (.cons (by simp [wf_move]) hacc)
          rcases hh with ⟨hmv, heq⟩
          constructor
          · exact hmv
          · simpa [expand_moves, expand_move] using
              (expand_moves_cons (MV (R src) (S sl ofs ty)) accu b).symm.trans heq
      | Lop op args res =>
          cases hc : classify_operation op args with
          | operation_Omove arg =>
              simp [extract_moves_ext, hc] at h
              have hh := ih (MV (R arg) (R res) :: accu) mv b' h
                (.cons (by simp [wf_move]) hacc)
              rcases hh with ⟨hmv, heq⟩
              constructor
              · exact hmv
              · simpa [expand_moves, expand_move] using
                  (expand_moves_cons (MV (R arg) (R res)) accu b).symm.trans heq
          | operation_Omakelong arg1 arg2 =>
              simp [extract_moves_ext, hc] at h
              have hh := ih (MVmakelong arg1 arg2 res :: accu) mv b' h
                (.cons (by simp [wf_move]) hacc)
              rcases hh with ⟨hmv, heq⟩
              constructor
              · exact hmv
              · simpa [expand_moves, expand_move] using
                  (expand_moves_cons (MVmakelong arg1 arg2 res) accu b).symm.trans heq
          | operation_Olowlong arg =>
              simp [extract_moves_ext, hc] at h
              have hh := ih (MVlowlong arg res :: accu) mv b' h
                (.cons (by simp [wf_move]) hacc)
              rcases hh with ⟨hmv, heq⟩
              constructor
              · exact hmv
              · simpa [expand_moves, expand_move] using
                  (expand_moves_cons (MVlowlong arg res) accu b).symm.trans heq
          | operation_Ohighlong arg =>
              simp [extract_moves_ext, hc] at h
              have hh := ih (MVhighlong arg res :: accu) mv b' h
                (.cons (by simp [wf_move]) hacc)
              rcases hh with ⟨hmv, heq⟩
              constructor
              · exact hmv
              · simpa [expand_moves, expand_move] using
                  (expand_moves_cons (MVhighlong arg res) accu b).symm.trans heq
          | operation_other op' args' =>
              simp [extract_moves_ext, hc] at h
              cases h
              exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lload chunk addr args dst =>
          simp [extract_moves_ext] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lstore chunk addr args src =>
          simp [extract_moves_ext] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lcall sg ros =>
          simp [extract_moves_ext] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Ltailcall sg ros =>
          simp [extract_moves_ext] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lbuiltin ef args res =>
          simp [extract_moves_ext] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lbranch succ =>
          simp [extract_moves_ext] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lcond cond args ifso ifnot =>
          simp [extract_moves_ext] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Ljumptable arg tbl =>
          simp [extract_moves_ext] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩
      | Lreturn =>
          simp [extract_moves_ext] at h
          cases h
          exact ⟨wf_moves_reverse hacc, rfl⟩

theorem extract_moves_ext_sound : extract_moves_ext_soundStatement := by
  intro b mv b' h
  exact extract_moves_ext_aux b [] mv b' h .nil

theorem check_succ_sound : check_succ_soundStatement := by
  intro s b h
  cases b with
  | nil => simp [check_succ] at h
  | cons i tl =>
      cases i with
      | Lbranch s' =>
          cases hp : peq s s' with
          | left heq =>
              simp only [check_succ, hp] at h
              change true = true at h
              subst s'
              exact ⟨tl, rfl⟩
          | right hne =>
              simp only [check_succ, hp] at h
              change false = true at h
              cases h
      | _ => simp [check_succ] at h

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

namespace ESF

theorem remove_iff_proof : remove_iff := by
  intro s x y
  constructor
  · intro h
    exact ⟨EqSetM.remove_3 s x y h, fun hxy => EqSetM.remove_1 s x y hxy h⟩
  · rintro ⟨hy, hxy⟩
    exact EqSetM.remove_2 s x y hxy hy

theorem add_iff_proof : add_iff := by
  intro s x y
  constructor
  · intro h
    by_cases hxy : EqSetE.eq x y
    · exact Or.inl hxy
    · exact Or.inr (EqSetM.add_3 s x y hxy h)
  · intro h
    cases h with
    | inl hxy => exact EqSetM.add_1 s x y hxy
    | inr hy => exact EqSetM.add_2 s x y hy

end ESF

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LTL

private theorem ebs_opdead_from_parse_local
    (op : CompCert4Lean.X86.Op.operation)
    (args : List CompCert4Lean.Backend.Registers.reg)
    (res : CompCert4Lean.Backend.Registers.reg) (s : RTL.node)
    (b : LTL.bblock) (mv : moves) (b1 : LTL.bblock)
    (hmv : extract_moves [] b = (mv, b1))
    (hs : check_succ s b1 = true) :
    expand_block_shape (BSopdead op args res mv s) (Iop op args res s) b := by
  rcases extract_moves_sound b mv b1 hmv with ⟨hwf, hb⟩
  rcases check_succ_sound s b1 hs with ⟨k, hk⟩
  subst b1
  rw [hb]
  exact ebs_op_dead op args res mv s k hwf

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

namespace ESP

noncomputable def fold_rec_proof : fold_rec := by
  intro A P f i s hEmpty hStep
  have of_list_in :
      ∀ (l : List EqSetE.t) (x : EqSetE.t),
        EqSetM.In x (List.foldr EqSetM.add EqSetM.empty l) ↔
          CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x l := by
    intro l
    induction l with
    | nil =>
        intro x
        constructor
        · intro hx
          exact False.elim (EqSetM.empty_1 x hx)
        · intro hx
          cases hx
    | cons y l ih =>
        intro x
        simp only [List.foldr]
        constructor
        · intro hx
          rw [CompCert4Lean.Backend.Allocproof.ESF.add_iff_proof] at hx
          rcases hx with hxy | hxl
          · exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_hd y l
              (EqSetE.eq_sym _ _ hxy)
          · exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_tl y l ((ih x).mp hxl)
        · intro hx
          cases hx with
          | cons_hd _ _ hxy =>
              apply (CompCert4Lean.Backend.Allocproof.ESF.add_iff_proof _ y x).mpr
              exact Or.inl (EqSetE.eq_sym _ _ hxy)
          | cons_tl _ _ hxl =>
              apply (CompCert4Lean.Backend.Allocproof.ESF.add_iff_proof _ y x).mpr
              exact Or.inr ((ih x).mpr hxl)
  have inA_append :
      ∀ (l₁ l₂ : List EqSetE.t) (x : EqSetE.t),
        CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x (l₁ ++ l₂) ↔
          CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x l₁ ∨
            CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x l₂ := by
    intro l₁ l₂ x
    change CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
        EqSetE.eq x (l₁ ++ l₂) ↔
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
          EqSetE.eq x l₁ ∨
        CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
          EqSetE.eq x l₂
    rw [CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA_alt,
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA_alt,
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA_alt]
    constructor
    · rintro ⟨y, hxy, hy⟩
      rcases List.mem_append.mp hy with hy₁ | hy₂
      · exact Or.inl ⟨y, hxy, hy₁⟩
      · exact Or.inr ⟨y, hxy, hy₂⟩
    · rintro (⟨y, hxy, hy⟩ | ⟨y, hxy, hy⟩)
      · exact ⟨y, hxy, List.mem_append.mpr (Or.inl hy)⟩
      · exact ⟨y, hxy, List.mem_append.mpr (Or.inr hy)⟩
  have inA_reverse :
      ∀ (l : List EqSetE.t) (x : EqSetE.t),
        CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x l.reverse ↔
          CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x l := by
    intro l x
    change CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
        EqSetE.eq x l.reverse ↔
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA EqSetE.eq x l
    rw [CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA_alt,
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA_alt]
    constructor
    · rintro ⟨y, hxy, hy⟩
      exact ⟨y, hxy, List.mem_reverse.mp hy⟩
    · rintro ⟨y, hxy, hy⟩
      exact ⟨y, hxy, List.mem_reverse.mpr hy⟩
  have nodup_append_single :
      ∀ (l : List EqSetE.t) (x : EqSetE.t),
        CompCert4Lean.Lib.FSetInterface.NoDupA EqSetE.eq l →
          ¬ CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x l →
          CompCert4Lean.Lib.FSetInterface.NoDupA EqSetE.eq (l ++ [x]) := by
    intro l
    induction l with
    | nil =>
        intro x _ _
        apply CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA.cons
        · intro h
          cases h
        · exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA.nil
    | cons y l ih =>
        intro x hnd hnot
        cases hnd with
        | cons hny htail =>
            apply CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA.cons
            · intro hy
              rcases (inA_append l [x] y).mp hy with hyL | hyX
              · exact hny hyL
              · cases hyX with
                | cons_hd _ _ hyx =>
                    exact hnot (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_hd
                      y l (EqSetE.eq_sym _ _ hyx))
                | cons_tl _ _ hyx => cases hyx
            · exact ih x htail (by
                intro hx
                exact hnot (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_tl y l hx))
  have nodup_reverse :
      ∀ (l : List EqSetE.t),
        CompCert4Lean.Lib.FSetInterface.NoDupA EqSetE.eq l →
          CompCert4Lean.Lib.FSetInterface.NoDupA EqSetE.eq l.reverse := by
    intro l
    induction l with
    | nil =>
        intro _
        exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA.nil
    | cons y l ih =>
        intro hnd
        cases hnd with
        | cons hny htail =>
            have hnot : ¬ CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq y l.reverse := by
              intro hy
              exact hny ((inA_reverse l y).mp hy)
            have h := nodup_append_single l.reverse y (ih htail) hnot
            simpa [List.reverse_cons] using h
  rw [EqSetM.fold_1]
  rw [List.foldl_eq_foldr_reverse]
  let l : List EqSetE.t := (EqSetM.elements s).reverse
  have hsame : ∀ x, EqSetM.In x s ↔
      CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x l := by
    intro x
    constructor
    · intro hx
      exact (inA_reverse (EqSetM.elements s) x).mpr
        ((EqSetM.elements_1 s x) hx)
    · intro hx
      exact (EqSetM.elements_2 s x) ((inA_reverse (EqSetM.elements s) x).mp hx)
  have hnd : CompCert4Lean.Lib.FSetInterface.NoDupA EqSetE.eq l := by
    exact nodup_reverse (EqSetM.elements s) (EqSetM.elements_3w s)
  have nodup_cons_inv :
      ∀ (x : EqSetE.t) (l : List EqSetE.t),
        CompCert4Lean.Lib.FSetInterface.NoDupA EqSetE.eq (x :: l) →
          (¬ CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x l ∧
            CompCert4Lean.Lib.FSetInterface.NoDupA EqSetE.eq l) := by
    intro x l h
    cases h with
    | cons hnot htail => exact ⟨hnot, htail⟩
  have fold_ind :
      ∀ (l : List EqSetE.t) (s₀ : EqSetM.t),
        (∀ x, EqSetM.In x s₀ ↔
          CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x l) →
        (∀ x, CompCert4Lean.Lib.FSetInterface.InA EqSetE.eq x l →
          EqSetM.In x s) →
        CompCert4Lean.Lib.FSetInterface.NoDupA EqSetE.eq l →
        P s₀ (List.foldr (fun x a => f x a) i l) := by
    intro l
    induction l with
    | nil =>
        intro s₀ hsame₀ _ _
        apply hEmpty
        intro x hx
        cases (hsame₀ x).mp hx
    | cons x l ih =>
        intro s₀ hsame₀ hsource₀ hnd₀
        have hnd' := nodup_cons_inv x l hnd₀
        have hnot := hnd'.1
        have htail := hnd'.2
        apply hStep x (List.foldr (fun x a => f x a) i l)
              (List.foldr EqSetM.add EqSetM.empty l) s₀
        · exact hsource₀ x
                (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_hd
                  x l (EqSetE.eq_refl x))
        · intro hx
          exact hnot ((of_list_in l x).mp hx)
        · intro y
          constructor
          · intro hy
            cases (hsame₀ y).mp hy with
            | cons_hd _ _ hxy => exact Or.inl (EqSetE.eq_sym _ _ hxy)
            | cons_tl _ _ hyl => exact Or.inr ((of_list_in l y).mpr hyl)
          · intro hy
            rcases hy with hyx | hyl
            · exact (hsame₀ y).mpr
                    (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_hd
                      x l (EqSetE.eq_sym _ _ hyx))
            · exact (hsame₀ y).mpr
                    (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_tl
                      x l ((of_list_in l y).mp hyl))
        · exact ih (List.foldr EqSetM.add EqSetM.empty l)
            (fun y => of_list_in l y)
            (fun y hyl => hsource₀ y
              (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_tl
                x l hyl)) htail
  exact fold_ind l s hsame (fun x hx => (hsame x).mpr hx) hnd

end ESP

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation

theorem satisf_incr : satisf_incrStatement := by
  intro rs ls e1 e2 hs hsub q hq
  exact hs q (hsub q hq)

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation

theorem add_equation_lessdef : add_equation_lessdefStatement := by
  intro rs ls q e hsat
  apply hsat q
  exact EqSet.add_1 e.eqs1 q q (EqSet.E.eq_refl q)

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation

theorem add_equation_satisf : add_equation_satisfStatement := by
  intro rs ls q e hsat q' hq'
  exact hsat q' (EqSet.add_2 e.eqs1 q q' hq')

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation

theorem add_equations_satisf : add_equations_satisfStatement := by
  intro rs ls rl ml e e' hrun hsat
  induction rl generalizing ml e e' with
  | nil =>
      cases ml with
      | nil =>
          simp [add_equations] at hrun
          cases hrun
          exact hsat
      | cons m ms =>
          simp [add_equations] at hrun
  | cons r rl ih =>
      cases ml with
      | nil =>
          simp [add_equations] at hrun
      | cons m ms =>
          simp only [add_equations] at hrun
          have hmid : satisf rs ls
              (add_equation { ekind := .Full, ereg := r, eloc := .R m } e) :=
            ih (ml := ms)
              (e := add_equation { ekind := .Full, ereg := r, eloc := .R m } e)
              (e' := e') hrun hsat
          exact add_equation_satisf rs ls
            { ekind := .Full, ereg := r, eloc := .R m } e hmid

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.Values

theorem add_equations_lessdef : add_equations_lessdefStatement := by
  intro rs ls rl ml e e' hrun hsat
  induction rl generalizing ml e e' with
  | nil =>
      cases ml with
      | nil =>
          exact Val.lessdef_list_nil
      | cons m ms =>
          simp [add_equations] at hrun
  | cons r rl ih =>
      cases ml with
      | nil =>
          simp [add_equations] at hrun
      | cons m ms =>
          simp only [add_equations] at hrun
          apply Val.lessdef_list_cons
          · apply add_equation_lessdef (rs := rs) (ls := ls)
              (q := { ekind := .Full, ereg := r, eloc := .R m }) (e := e)
            exact add_equations_satisf (rs := rs) (ls := ls) (rl := rl)
              (ml := ms)
              (e := add_equation { ekind := .Full, ereg := r, eloc := .R m } e)
              (e' := e') hrun hsat
          · exact ih (ml := ms)
              (e := add_equation { ekind := .Full, ereg := r, eloc := .R m } e)
              (e' := e') hrun hsat

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.AST

theorem add_equations_args_satisf : add_equations_args_satisfStatement := by
  intro rs ls rl tyl ll e e' hrun hsat
  induction rl generalizing tyl ll e e' with
  | nil =>
      cases tyl with
      | nil =>
          cases ll with
          | nil =>
              simp [add_equations_args] at hrun
              cases hrun
              exact hsat
          | cons p ps =>
              simp [add_equations_args] at hrun
      | cons ty tys =>
          cases ll <;> simp [add_equations_args] at hrun
  | cons r rl ih =>
      cases tyl with
      | nil =>
          cases ll <;> simp [add_equations_args] at hrun
      | cons ty tys =>
          cases ll with
          | nil =>
              simp [add_equations_args] at hrun
          | cons p ps =>
              cases p with
              | One l =>
                  simp only [add_equations_args] at hrun
                  have hmid : satisf rs ls
                      (add_equation { ekind := .Full, ereg := r, eloc := l } e) :=
                    ih (tyl := tys) (ll := ps)
                      (e := add_equation { ekind := .Full, ereg := r, eloc := l } e)
                      (e' := e') hrun hsat
                  exact add_equation_satisf rs ls
                    { ekind := .Full, ereg := r, eloc := l } e hmid
              | Twolong hi lo =>
                  by_cases hty : ty = Tlong
                  · simp [add_equations_args, hty,
                      CompCert4Lean.X86_64.Archi.ptr64] at hrun
                  · simp [add_equations_args, hty] at hrun

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

theorem val_longofwords_eq_1 : val_longofwords_eq_1Statement := by
  intro v hv hptr
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

theorem val_longofwords_eq_2 : val_longofwords_eq_2Statement := by
  intro v hv hsplit
  apply val_longofwords_eq_1 v hv
  exact CompCert4Lean.X86_64.Archi.splitlong_ptr32 hsplit

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation

theorem add_equation_ros_satisf : add_equation_ros_satisfStatement := by
  intro rs ls ros mos e e' hrun hsat
  cases ros with
  | inl r =>
      cases mos with
      | inl mr =>
          simp [add_equation_ros] at hrun
          rcases hrun with ⟨rfl, rfl⟩
          exact add_equation_satisf rs ls
            { ekind := .Full, ereg := r, eloc := .R mr } e hsat
      | inr id => simp [add_equation_ros] at hrun
  | inr id =>
      cases mos with
      | inl mr => simp [add_equation_ros] at hrun
      | inr id' =>
          simp [add_equation_ros] at hrun
          rcases hrun with ⟨_, rfl⟩
          exact hsat

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem select_reg_l_monotone : select_reg_l_monotoneStatement := by
  intro r q1 q2 hord hsel
  unfold select_reg_l PArith.BinPos.Pos.leb at hsel ⊢
  have hrle : PArith.BinPos.Pos.to_nat r ≤
      PArith.BinPos.Pos.to_nat q1.ereg := by
    split at hsel
    · exact ‹PArith.BinPos.Pos.to_nat r ≤ PArith.BinPos.Pos.to_nat q1.ereg›
    · simp at hsel
  rcases hord with rfl | hlt
  · exact hsel
  · rcases hlt with hreg | ⟨hreq, _⟩
    · have hreg' : PArith.BinPos.Pos.to_nat q1.ereg <
          PArith.BinPos.Pos.to_nat q2.ereg := hreg
      have hqle : PArith.BinPos.Pos.to_nat r ≤
          PArith.BinPos.Pos.to_nat q2.ereg := Nat.le_trans hrle (Nat.le_of_lt hreg')
      split
      · rfl
      · exfalso
        exact ‹¬ PArith.BinPos.Pos.to_nat r ≤
          PArith.BinPos.Pos.to_nat q2.ereg› hqle
    · rw [← hreq]
      exact hsel

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Registers

private theorem allocproof_longofwords_lessdef
    (v1 v2 v1' v2' : val) :
    Val.lessdef v1 v1' → Val.lessdef v2 v2' →
      Val.lessdef (Val.longofwords v1 v2) (Val.longofwords v1' v2') := by
  intro h1 h2
  cases h1 with
  | lessdef_refl v1 =>
      cases h2 with
      | lessdef_refl v2 => exact Val.lessdef_refl _
      | lessdef_undef v2' =>
          simpa [Val.longofwords] using
            (Val.lessdef_undef (Val.longofwords v1 v2'))
  | lessdef_undef v1' =>
      simpa [Val.longofwords] using
        (Val.lessdef_undef (Val.longofwords v1' v2'))

theorem add_equations_args_lessdef : add_equations_args_lessdefStatement := by
  intro rs ls rl tyl ll e e' hrun hsat htypes
  induction rl generalizing tyl ll e e' with
  | nil =>
      cases tyl with
      | nil =>
          cases ll with
          | nil =>
              simp [add_equations_args] at hrun
              cases hrun
              exact Val.lessdef_list_nil
          | cons p ps => simp [add_equations_args] at hrun
      | cons ty tys =>
          cases ll <;> simp [add_equations_args] at hrun
  | cons r rl ih =>
      cases tyl with
      | nil =>
          cases ll <;> simp [add_equations_args] at hrun
      | cons ty tys =>
          cases ll with
          | nil => simp [add_equations_args] at hrun
          | cons p ps =>
              cases p with
              | One l =>
                  simp only [add_equations_args] at hrun
                  rcases htypes with ⟨hty, htypes⟩
                  apply Val.lessdef_list_cons
                  · apply add_equation_lessdef (rs := rs) (ls := ls)
                      (q := { ekind := .Full, ereg := r, eloc := l }) (e := e)
                    exact add_equations_args_satisf (rs := rs) (ls := ls)
                      (rl := rl) (tyl := tys) (ll := ps)
                      (e := add_equation { ekind := .Full, ereg := r, eloc := l } e)
                      (e' := e') hrun hsat
                  · exact ih (tyl := tys) (ll := ps)
                      (e := add_equation { ekind := .Full, ereg := r, eloc := l } e)
                      (e' := e') hrun hsat htypes
              | Twolong hi lo =>
                  by_cases hty : ty = Tlong
                  · subst ty
                    simp [add_equations_args] at hrun
                    rcases hrun with ⟨hptr, hrun⟩
                    rcases htypes with ⟨hty, htypes⟩
                    apply Val.lessdef_list_cons
                    · change Val.lessdef (Regmap.get r rs)
                        (Val.longofwords (ls hi) (ls lo))
                      rw [← val_longofwords_eq_1 (Regmap.get r rs) hty hptr]
                      apply allocproof_longofwords_lessdef
                      · exact add_equation_lessdef (rs := rs) (ls := ls)
                          (q := { ekind := .High, ereg := r, eloc := hi }) (e := e) <|
                            add_equation_satisf rs ls
                              { ekind := .Low, ereg := r, eloc := lo }
                              (add_equation { ekind := .High, ereg := r, eloc := hi } e)
                              (add_equations_args_satisf (rs := rs) (ls := ls)
                                (rl := rl) (tyl := tys) (ll := ps)
                                (e := add_equation { ekind := .Low, ereg := r, eloc := lo }
                                  (add_equation { ekind := .High, ereg := r, eloc := hi } e))
                                (e' := e') hrun hsat)
                      · exact add_equation_lessdef (rs := rs) (ls := ls)
                          (q := { ekind := .Low, ereg := r, eloc := lo })
                          (e := add_equation { ekind := .High, ereg := r, eloc := hi } e) <| by
                            exact add_equations_args_satisf (rs := rs) (ls := ls)
                              (rl := rl) (tyl := tys) (ll := ps)
                              (e := add_equation { ekind := .Low, ereg := r, eloc := lo }
                                (add_equation { ekind := .High, ereg := r, eloc := hi } e))
                              (e' := e') hrun hsat
                    · exact ih (tyl := tys) (ll := ps)
                        (e := add_equation { ekind := .Low, ereg := r, eloc := lo }
                          (add_equation { ekind := .High, ereg := r, eloc := hi } e))
                        (e' := e') hrun hsat htypes
                  · simp [add_equations_args, hty] at hrun

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem select_reg_h_monotone : select_reg_h_monotoneStatement := by
  intro r q1 q2 hord hsel
  unfold select_reg_h PArith.BinPos.Pos.leb at hsel ⊢
  have hreq : PArith.BinPos.Pos.to_nat q1.ereg ≤
      PArith.BinPos.Pos.to_nat r := by
    split at hsel
    · exact ‹PArith.BinPos.Pos.to_nat q1.ereg ≤
        PArith.BinPos.Pos.to_nat r›
    · simp at hsel
  rcases hord with rfl | hlt
  · exact hsel
  · rcases hlt with hreg | ⟨hreg, _⟩
    · have hreg' : PArith.BinPos.Pos.to_nat q2.ereg <
          PArith.BinPos.Pos.to_nat q1.ereg := hreg
      have hqle : PArith.BinPos.Pos.to_nat q2.ereg ≤
          PArith.BinPos.Pos.to_nat r :=
        Nat.le_trans (Nat.le_of_lt hreg') hreq
      split
      · rfl
      · exfalso
        exact ‹¬ PArith.BinPos.Pos.to_nat q2.ereg ≤
          PArith.BinPos.Pos.to_nat r› hqle
    · rw [hreg]
      exact hsel

theorem select_reg_charact : select_reg_charactStatement := by
  intro r q
  unfold select_reg_l select_reg_h PArith.BinPos.Pos.leb
  constructor
  · intro h
    rcases h with ⟨hl, hh⟩
    have hl' : PArith.BinPos.Pos.to_nat r ≤
        PArith.BinPos.Pos.to_nat q.ereg := by
      split at hl
      · exact ‹PArith.BinPos.Pos.to_nat r ≤
          PArith.BinPos.Pos.to_nat q.ereg›
      · simp at hl
    have hh' : PArith.BinPos.Pos.to_nat q.ereg ≤
        PArith.BinPos.Pos.to_nat r := by
      split at hh
      · exact ‹PArith.BinPos.Pos.to_nat q.ereg ≤
          PArith.BinPos.Pos.to_nat r›
      · simp at hh
    change posToNat r ≤ posToNat q.ereg at hl'
    change posToNat q.ereg ≤ posToNat r at hh'
    apply posToNat_injective
    omega
  · intro h
    have hq : q.ereg = r := h
    simp [hq]

theorem reg_unconstrained_sound : reg_unconstrained_soundStatement := by
  intro r e q hunc hq
  intro heq
  have hboth : select_reg_l r q = true ∧ select_reg_h r q = true :=
    (select_reg_charact r q).2 heq
  have habove : ∀ x1 x2,
      OrderedEquation.eq x1 x2 ∨ OrderedEquation.lt x1 x2 →
      select_reg_l r x1 = true → select_reg_l r x2 = true := by
    intro x1 x2 hlt hx
    exact select_reg_l_monotone r x1 x2 hlt hx
  have hbelow : ∀ x1 x2,
      OrderedEquation.eq x1 x2 ∨ OrderedEquation.lt x2 x1 →
      select_reg_h r x1 = true → select_reg_h r x2 = true := by
    intro x1 x2 hlt hx
    exact select_reg_h_monotone r x1 x2 hlt hx
  have hmem : EqSet.mem_between (select_reg_l r) (select_reg_h r) e.eqs1 = true :=
    EqSet.mem_between_2_proof (select_reg_l r) (select_reg_h r)
      habove hbelow q e.eqs1 hq hboth.1 hboth.2
  unfold reg_unconstrained at hunc
  simp [hmem] at hunc

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.Values

theorem reg_unconstrained_satisf : reg_unconstrained_satisfStatement := by
  intro r e rs ls v hunc hsat
  unfold satisf at hsat ⊢
  intro q hq
  by_cases heq : q.ereg = r
  · exact False.elim ((reg_unconstrained_sound r e q hunc hq) heq)
  · have hget : CompCert4Lean.Backend.Registers.Regmap.get q.ereg
        (CompCert4Lean.Backend.Registers.Regmap.set r v rs) =
        CompCert4Lean.Backend.Registers.Regmap.get q.ereg rs :=
      CompCert4Lean.Backend.Registers.Regmap.gso_proof val q.ereg r v rs heq
    rw [hget]
    exact hsat q hq

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations

theorem select_loc_l_monotone : select_loc_l_monotoneStatement := by
  intro l q1 q2 hord hsel
  unfold select_loc_l at hsel ⊢
  rcases hord with heq | hlt
  · subst q2
    exact hsel
  · have hloc : Locations.OrderedLoc.lt q1.eloc q2.eloc ∨
        q1.eloc = q2.eloc := by
      rcases hlt with hltloc | hrest
      · exact Or.inl hltloc
      · exact Or.inr hrest.1
    rcases hloc with hltloc | hloc
    · cases hcmp2 : Locations.OrderedLoc.compare q2.eloc
          (Locations.OrderedLoc.diff_low_bound l) with
      | LT hq2lt =>
          exfalso
          have hq1lt : Locations.OrderedLoc.lt q1.eloc
              (Locations.OrderedLoc.diff_low_bound l) := by
            exact Locations.OrderedLoc.lt_trans q1.eloc q2.eloc
              (Locations.OrderedLoc.diff_low_bound l) hltloc hq2lt
          cases hcmp1 : Locations.OrderedLoc.compare q1.eloc
                (Locations.OrderedLoc.diff_low_bound l) with
          | LT _ =>
              simp [hcmp1] at hsel
          | EQ hq1eq =>
              exact Locations.OrderedLoc.lt_not_eq q1.eloc
                (Locations.OrderedLoc.diff_low_bound l) hq1lt hq1eq
          | GT hq1gt =>
              have hcycle : Locations.OrderedLoc.lt q1.eloc q1.eloc :=
                Locations.OrderedLoc.lt_trans q1.eloc
                  (Locations.OrderedLoc.diff_low_bound l) q1.eloc hq1lt hq1gt
              exact Locations.OrderedLoc.lt_not_eq q1.eloc q1.eloc hcycle rfl
      | GT hq2gt =>
          simp
      | EQ hq2eq =>
          simp
    · cases hcmp2 : Locations.OrderedLoc.compare q2.eloc
          (Locations.OrderedLoc.diff_low_bound l) with
      | LT hq2lt =>
          exfalso
          have hq1lt : Locations.OrderedLoc.lt q1.eloc
              (Locations.OrderedLoc.diff_low_bound l) := by
            simpa [hloc] using hq2lt
          cases hcmp1 : Locations.OrderedLoc.compare q1.eloc
                (Locations.OrderedLoc.diff_low_bound l) with
          | LT _ =>
              simp [hcmp1] at hsel
          | EQ hq1eq =>
              exact Locations.OrderedLoc.lt_not_eq q1.eloc
                (Locations.OrderedLoc.diff_low_bound l) hq1lt hq1eq
          | GT hq1gt =>
              have hcycle : Locations.OrderedLoc.lt q1.eloc q1.eloc :=
                Locations.OrderedLoc.lt_trans q1.eloc
                  (Locations.OrderedLoc.diff_low_bound l) q1.eloc hq1lt hq1gt
              exact Locations.OrderedLoc.lt_not_eq q1.eloc q1.eloc hcycle rfl
      | GT hq2gt =>
          simp
      | EQ hq2eq =>
          simp

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations

theorem select_loc_h_monotone : select_loc_h_monotoneStatement := by
  intro l q1 q2 hord hsel
  unfold select_loc_h at hsel ⊢
  rcases hord with heq | hlt
  · subst q2
    exact hsel
  · have hloc : Locations.OrderedLoc.lt q2.eloc q1.eloc ∨
        q2.eloc = q1.eloc := by
      rcases hlt with hltloc | hrest
      · exact Or.inl hltloc
      · exact Or.inr hrest.1
    rcases hloc with hltloc | hloc
    · cases hcmp2 : Locations.OrderedLoc.compare q2.eloc
          (Locations.OrderedLoc.diff_high_bound l) with
      | LT hq2lt =>
          simp
      | EQ hq2eq =>
          simp
      | GT hq2gt =>
          have hq1lt : Locations.OrderedLoc.lt
              (Locations.OrderedLoc.diff_high_bound l) q1.eloc :=
            Locations.OrderedLoc.lt_trans
              (Locations.OrderedLoc.diff_high_bound l) q2.eloc q1.eloc
              hq2gt hltloc
          cases hcmp1 : Locations.OrderedLoc.compare q1.eloc
                (Locations.OrderedLoc.diff_high_bound l) with
          | LT hq1lt' =>
              exfalso
              have hcycle : Locations.OrderedLoc.lt
                  (Locations.OrderedLoc.diff_high_bound l)
                  (Locations.OrderedLoc.diff_high_bound l) :=
                Locations.OrderedLoc.lt_trans
                  (Locations.OrderedLoc.diff_high_bound l) q1.eloc
                  (Locations.OrderedLoc.diff_high_bound l) hq1lt hq1lt'
              exact Locations.OrderedLoc.lt_not_eq
                (Locations.OrderedLoc.diff_high_bound l)
                (Locations.OrderedLoc.diff_high_bound l) hcycle rfl
          | EQ hq1eq =>
              exfalso
              exact Locations.OrderedLoc.lt_not_eq
                (Locations.OrderedLoc.diff_high_bound l) q1.eloc
                hq1lt hq1eq.symm
          | GT hq1gt =>
              exfalso
              simp [hcmp1] at hsel
    · cases hcmp2 : Locations.OrderedLoc.compare q2.eloc
          (Locations.OrderedLoc.diff_high_bound l) with
      | LT hq2lt =>
          simp
      | EQ hq2eq =>
          simp
      | GT hq2gt =>
          exfalso
          have hq1gt : Locations.OrderedLoc.lt
              (Locations.OrderedLoc.diff_high_bound l) q1.eloc := by
            simpa [hloc] using hq2gt
          cases hcmp1 : Locations.OrderedLoc.compare q1.eloc
                (Locations.OrderedLoc.diff_high_bound l) with
          | LT hq1lt =>
              have hcycle : Locations.OrderedLoc.lt
                  (Locations.OrderedLoc.diff_high_bound l)
                  (Locations.OrderedLoc.diff_high_bound l) :=
                Locations.OrderedLoc.lt_trans
                  (Locations.OrderedLoc.diff_high_bound l) q1.eloc
                  (Locations.OrderedLoc.diff_high_bound l) hq1gt hq1lt
              exact Locations.OrderedLoc.lt_not_eq
                (Locations.OrderedLoc.diff_high_bound l)
                (Locations.OrderedLoc.diff_high_bound l) hcycle rfl
          | EQ hq1eq =>
              exact Locations.OrderedLoc.lt_not_eq
                (Locations.OrderedLoc.diff_high_bound l) q1.eloc
                hq1gt hq1eq.symm
          | GT hq1gt =>
              simp [hcmp1] at hsel

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem allocproof_orderedloc_outside_interval_diff :
    ∀ l l' : Locations.loc,
      Locations.OrderedLoc.lt l'
          (Locations.OrderedLoc.diff_low_bound l) ∨
        Locations.OrderedLoc.lt (Locations.OrderedLoc.diff_high_bound l) l' →
      Locations.Loc.diff l l' := by
  intro l l' h
  cases l with
  | R r =>
      cases l' with
      | R r' =>
          rcases h with h | h
          · intro heq
            subst r'
            exact CompCert4Lean.Lib.Coqlib.Plt_strict _ h
          · intro heq
            subst r'
            exact CompCert4Lean.Lib.Coqlib.Plt_strict _ h
      | S sl ofs ty =>
          trivial
  | S sl ofs ty =>
      cases l' with
      | R r =>
          trivial
      | S sl' ofs' ty' =>
          have zlt_int : ∀ a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt a b →
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
            intro a b hab
            exact hab
          have zle_int : ∀ a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le a b →
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
            intro a b hab
            exact hab
          have zadd_int : ∀ a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add a b) =
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
            intro a b
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          have zsub_int : ∀ a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub a b) =
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
            intro a b
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          have zone_int :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1) = 1 := by
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          have zofnat_int : ∀ n : Nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) =
                Int.ofNat n := by
            intro n
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          by_cases hslots : sl = sl'
          · subst sl'
            have hslotlt : ¬ Locations.OrderedSlot.lt sl sl := by
              intro hh
              exact Locations.OrderedSlot.lt_not_eq_proof sl sl hh rfl
            simp [Locations.OrderedLoc.lt, hslotlt,
              Locations.OrderedLoc.diff_low_bound,
              Locations.OrderedLoc.diff_high_bound, Locations.Loc.diff] at h ⊢
            rcases h with h | h
            · rcases h with h | ⟨heq, hty⟩
              · right
                have hz :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs'
                        (Locations.typesize ty')) ofs := by
                  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs'
                        (Locations.typesize ty')) ≤
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
                  rw [zadd_int]
                  have h' := zlt_int _ _ h
                  rw [zsub_int, zone_int] at h'
                  cases ty' <;>
                    simp [Locations.typesize, zofnat_int] at * <;>
                    omega
                exact hz
              · have hsize :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                        (Locations.typesize ty') ≤ 1 := by
                  cases ty' with
                  | Tint =>
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1) ≤ 1
                      rw [zofnat_int]
                      exact Int.le_refl _
                  | Tfloat =>
                      exfalso
                      change 5 < 4 at hty
                      omega
                  | Tlong =>
                      exfalso
                      change 6 < 4 at hty
                      omega
                  | Tsingle =>
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1) ≤ 1
                      rw [zofnat_int]
                      exact Int.le_refl _
                  | Tany32 =>
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1) ≤ 1
                      rw [zofnat_int]
                      exact Int.le_refl _
                  | Tany64 =>
                      exfalso
                      change 4 < 4 at hty
                      omega
                right
                have hz :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                        ofs' (Locations.typesize ty')) ofs := by
                  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                        ofs' (Locations.typesize ty')) ≤
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
                  rw [heq, zadd_int, zsub_int, zone_int]
                  omega
                exact hz
            · rcases h with h | ⟨heq, hty⟩
              · left
                have hz :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
                        (Locations.typesize ty)) ofs' := by
                  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
                        (Locations.typesize ty)) ≤
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs'
                  rw [zadd_int]
                  have h' := zlt_int _ _ h
                  rw [zsub_int, zadd_int, zone_int] at h'
                  omega
                exact hz
              · exfalso
                cases ty' <;>
                  first
                  | (revert hty; decide)
                  | contradiction
          · exact Or.inl hslots


private theorem allocproof_orderedloc_diff_outside_interval :
    ∀ l l' : Locations.loc,
      Locations.Loc.diff l l' →
        Locations.OrderedLoc.lt l'
            (Locations.OrderedLoc.diff_low_bound l) ∨
          Locations.OrderedLoc.lt (Locations.OrderedLoc.diff_high_bound l) l' := by
  intro l l' h
  cases l with
  | R r =>
      cases l' with
      | R r' =>
          cases hc : Locations.OrderedLoc.compare (R r') (R r) with
          | LT hlt => exact Or.inl hlt
          | EQ heq =>
              exfalso
              apply h
              cases heq
              rfl
          | GT hgt => exact Or.inr hgt
      | S sl ofs ty =>
          exact Or.inr trivial
  | S sl ofs ty =>
      cases l' with
      | R r =>
          exact Or.inl trivial
      | S sl' ofs' ty' =>
          have zlt_int : ∀ a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt a b →
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
            intro a b hab
            exact hab
          have zle_int : ∀ a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le a b →
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
            intro a b hab
            exact hab
          have zadd_int : ∀ a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add a b) =
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
            intro a b
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          have zsub_int : ∀ a b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub a b) =
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
            intro a b
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          have zone_int :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1) = 1 := by
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          have zofnat_int : ∀ n : Nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) =
                Int.ofNat n := by
            intro n
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          by_cases hslots : sl = sl'
          · subst sl'
            simp [Locations.Loc.diff] at h
            have h' := Or.symm h
            rcases h' with h | h
            · have hbefore :
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs' +
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Locations.typesize ty') ≤
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs := by
                have hh := zle_int _ _ h
                simpa [zadd_int] using hh
              left
              unfold Locations.OrderedLoc.lt
              right
              constructor
              · exact rfl
              · by_cases hlt :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs' <
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs - 1
                · left
                  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs' <
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub ofs
                        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1))
                  rw [zsub_int, zone_int]
                  exact hlt
                · right
                  constructor
                  · apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
                    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs' =
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub ofs
                            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1))
                    have hsize :
                        1 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                          (Locations.typesize ty') := by
                      cases ty' <;>
                        first
                        | (change 1 ≤ 1; exact Int.le_refl _)
                        | (change 1 ≤ 2; omega)
                    have hle :
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs - 1 ≤
                          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs' :=
                      Int.le_of_not_gt hlt
                    have hbefore :
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs' +
                            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                              (Locations.typesize ty') ≤
                          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs := by
                      have hh := zle_int _ _ h
                      simpa [zadd_int] using hh
                    have heq :
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs' =
                          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs - 1 := by
                      omega
                    rw [zsub_int, zone_int]
                    exact heq
                  · cases ty' with
                    | Tint =>
                        change posToNat (posOfNat 2) < posToNat (posOfNat 4)
                        rw [posToNat_posOfNat (by omega), posToNat_posOfNat (by omega)]
                        omega
                    | Tfloat =>
                        exfalso
                        have hsz :
                            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                              (Locations.typesize Common.AST.Tfloat) = 2 := by
                          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 2) = 2
                          rw [zofnat_int]
                          rfl
                        omega
                    | Tlong =>
                        exfalso
                        have hsz :
                            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                              (Locations.typesize Common.AST.Tlong) = 2 := by
                          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 2) = 2
                          rw [zofnat_int]
                          rfl
                        omega
                    | Tsingle =>
                        change posToNat (posOfNat 3) < posToNat (posOfNat 4)
                        rw [posToNat_posOfNat (by omega), posToNat_posOfNat (by omega)]
                        omega
                    | Tany32 =>
                        change posToNat (posOfNat 1) < posToNat (posOfNat 4)
                        rw [posToNat_posOfNat (by omega), posToNat_posOfNat (by omega)]
                        omega
                    | Tany64 =>
                        exfalso
                        have hsz :
                            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                              (Locations.typesize Common.AST.Tany64) = 2 := by
                          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 2) = 2
                          rw [zofnat_int]
                          rfl
                        omega
            · right
              unfold Locations.OrderedLoc.lt
              right
              constructor
              · exact rfl
              · left
                change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
                        (Locations.typesize ty))
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1)) <
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs'
                have hh := zle_int _ _ h
                rw [zsub_int, zadd_int, zone_int] at ⊢
                rw [zadd_int] at hh
                omega
          · cases hc : Locations.OrderedSlot.compare sl' sl with
            | LT hlt => exact Or.inl (Or.inl hlt)
            | EQ heq => exact False.elim (hslots heq.symm)
            | GT hgt => exact Or.inr (Or.inl hgt)


theorem select_loc_charact : select_loc_charactStatement := by
  intro l q
  unfold select_loc_l select_loc_h
  constructor
  · intro h
    rcases h with h | h
    · cases hcmp : Locations.OrderedLoc.compare q.eloc
          (Locations.OrderedLoc.diff_low_bound l) with
      | LT hlt =>
          exact allocproof_orderedloc_outside_interval_diff l q.eloc
            (Or.inl hlt)
      | EQ heq => simp [hcmp] at h
      | GT hgt => simp [hcmp] at h
    · cases hcmp : Locations.OrderedLoc.compare q.eloc
          (Locations.OrderedLoc.diff_high_bound l) with
      | LT hlt => simp [hcmp] at h
      | EQ heq => simp [hcmp] at h
      | GT hgt =>
          exact allocproof_orderedloc_outside_interval_diff l q.eloc
            (Or.inr hgt)
  · intro h
    rcases allocproof_orderedloc_diff_outside_interval l q.eloc h with h | h
    · left
      cases hcmp : Locations.OrderedLoc.compare q.eloc
          (Locations.OrderedLoc.diff_low_bound l) with
      | LT hlt => simp [hcmp]
      | EQ heq =>
          exact False.elim (Locations.OrderedLoc.lt_not_eq
            q.eloc (Locations.OrderedLoc.diff_low_bound l) h heq)
      | GT hgt =>
          exfalso
          have hcycle : Locations.OrderedLoc.lt q.eloc q.eloc :=
            Locations.OrderedLoc.lt_trans q.eloc
              (Locations.OrderedLoc.diff_low_bound l) q.eloc h hgt
          exact Locations.OrderedLoc.lt_not_eq q.eloc q.eloc hcycle rfl
    · right
      cases hcmp : Locations.OrderedLoc.compare q.eloc
          (Locations.OrderedLoc.diff_high_bound l) with
      | LT hlt =>
          exfalso
          have hcycle : Locations.OrderedLoc.lt
              (Locations.OrderedLoc.diff_high_bound l)
              (Locations.OrderedLoc.diff_high_bound l) :=
            Locations.OrderedLoc.lt_trans
              (Locations.OrderedLoc.diff_high_bound l) q.eloc
              (Locations.OrderedLoc.diff_high_bound l) h hlt
          exact Locations.OrderedLoc.lt_not_eq
            (Locations.OrderedLoc.diff_high_bound l)
            (Locations.OrderedLoc.diff_high_bound l) hcycle rfl
      | EQ heq =>
          exact False.elim (Locations.OrderedLoc.lt_not_eq
            (Locations.OrderedLoc.diff_high_bound l) q.eloc h heq.symm)
      | GT hgt => simp [hcmp]


end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations

theorem loc_unconstrained_sound : loc_unconstrained_soundStatement := by
  intro l e q hunc hq
  unfold loc_unconstrained at hunc
  cases hsl : select_loc_l l q with
  | false =>
      exact (select_loc_charact l q).1 (Or.inl hsl)
  | true =>
      cases hsh : select_loc_h l q with
      | false =>
          exact (select_loc_charact l q).1 (Or.inr hsh)
      | true =>
          have hmem :
              EqSet2.mem_between (select_loc_l l) (select_loc_h l) e.eqs2 = true :=
            EqSet2.mem_between_2_proof (select_loc_l l) (select_loc_h l)
              (select_loc_l_monotone l) (select_loc_h_monotone l) q e.eqs2
              ((e.eqs_same q).mpr hq) hsl hsh
          simp [hmem] at hunc

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values

theorem loc_unconstrained_satisf : loc_unconstrained_satisfStatement := by
  intro rs ls k r mr e v
  dsimp
  intro hsat hunc hld
  unfold satisf at hsat ⊢
  intro q hq
  let q0 : equation := { ekind := k, ereg := r, eloc := R mr }
  by_cases heq : q = q0
  · subst q
    dsimp [q0]
    have hset : Locmap.set (R mr) v ls (R mr) = v := by
      simpa using (Locmap.gss (R mr) v ls)
    rw [hset]
    exact hld
  · have hqrem : EqSet.In q (remove_equation q0 e).eqs1 := by
      unfold remove_equation
      apply EqSet.remove_2 e.eqs1 q0 q
      · intro h
        exact heq h.symm
      · exact hq
    have hdiff : Loc.diff (R mr) q.eloc :=
      loc_unconstrained_sound (R mr) (remove_equation q0 e) q hunc hqrem
    rw [Locmap.gso (R mr) v ls q.eloc hdiff]
    exact hsat q hqrem

theorem reg_loc_unconstrained_sound : reg_loc_unconstrained_soundStatement := by
  intro r l e q hunc hq
  have hboth : reg_unconstrained r e = true ∧ loc_unconstrained l e = true := by
    simpa [reg_loc_unconstrained] using hunc
  exact ⟨reg_unconstrained_sound r e q hboth.1 hq,
    loc_unconstrained_sound l e q hboth.2 hq⟩

theorem parallel_assignment_satisf : parallel_assignment_satisfStatement := by
  intro k r mr e rs ls v v'
  dsimp
  intro hld hunc hsat
  unfold satisf at hsat ⊢
  intro q hq
  let q0 : equation := { ekind := k, ereg := r, eloc := R mr }
  have hunc' : reg_unconstrained r (remove_equation q0 e) = true ∧
      loc_unconstrained (R mr) (remove_equation q0 e) = true := by
    simpa [reg_loc_unconstrained, q0] using hunc
  by_cases heq : q = q0
  · subst q
    dsimp [q0]
    have hregset : Regmap.get r (Regmap.set r v rs) = v := by
      exact Regmap.gss_proof val r v rs
    have hlocset : Locmap.set (R mr) v' ls (R mr) = v' := by
      simpa using (Locmap.gss (R mr) v' ls)
    rw [hregset, hlocset]
    exact hld
  · have hqrem : EqSet.In q (remove_equation q0 e).eqs1 := by
      unfold remove_equation
      apply EqSet.remove_2 e.eqs1 q0 q
      · intro h
        exact heq h.symm
      · exact hq
    have hreg : q.ereg ≠ r := reg_unconstrained_sound r
      (remove_equation q0 e) q hunc'.1 hqrem
    have hloc : Loc.diff (R mr) q.eloc := loc_unconstrained_sound (R mr)
      (remove_equation q0 e) q hunc'.2 hqrem
    rw [Regmap.gso_proof val q.ereg r v rs hreg]
    rw [Locmap.gso (R mr) v' ls q.eloc hloc]
    exact hsat q hqrem

theorem in_elements_between_1 : in_elements_between_1Statement := by
  intro r1 s q
  rw [EqSet.elements_between_iff_proof (select_reg_l r1) (select_reg_h r1)
    (select_reg_l_monotone r1) (select_reg_h_monotone r1)]
  constructor
  · rintro ⟨hmem, hl, hh⟩
    exact ⟨hmem, (select_reg_charact r1 q).1 ⟨hl, hh⟩⟩
  · rintro ⟨hmem, heq⟩
    have hb := (select_reg_charact r1 q).2 heq
    exact ⟨hmem, hb.1, hb.2⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation

theorem in_subst_reg : in_subst_regStatement := by
  intro r1 r2 q e hq
  let f : EqSet.elt → eqs → eqs := fun x out =>
    add_equation { ekind := x.ekind, ereg := r2, eloc := x.eloc }
      (remove_equation x out)
  let elt : EqSet.t :=
    EqSet.elements_between (select_reg_l r1) (select_reg_h r1) e.eqs1
  have helt : ∀ x, EqSet.In x elt ↔ EqSet.In x e ∧ x.ereg = r1 := by
    intro x
    exact in_elements_between_1 r1 e.eqs1 x
  have hP : EqSet.In q elt →
      EqSet.In { ekind := q.ekind, ereg := r2, eloc := q.eloc }
        (EqSet.fold f elt e).eqs1 := by
    have hP' := ESP.fold_rec_proof eqs
      (fun s a => {h : EqSet.In q s →
        EqSet.In { ekind := q.ekind, ereg := r2, eloc := q.eloc } a.eqs1 // True})
      f e elt
      (by
        intro s hs
        refine ⟨?_, trivial⟩
        intro h
        exact False.elim (hs q h))
      (by
        intro x a s' s'' hx hnot hadd hPa
        refine ⟨?_, trivial⟩
        intro hqmem
        rcases (hadd q).mp hqmem with hqx | hqold
        · apply (ESF.add_iff_proof _ _ _).mpr
          left
          cases hqx
          exact EqSetE.eq_refl _
        · have hqnew : EqSet.In
              { ekind := q.ekind, ereg := r2, eloc := q.eloc } a.eqs1 := hPa.1 hqold
          by_cases hxeq : x = { ekind := q.ekind, ereg := r2, eloc := q.eloc }
          · apply (ESF.add_iff_proof _ _ _).mpr
            left
            cases hxeq
            exact EqSetE.eq_refl _
          · apply (ESF.add_iff_proof _ _ _).mpr
            right
            apply (ESF.remove_iff_proof _ _ _).mpr
            exact ⟨hqnew, hxeq⟩)
    exact hP'.1
  have hQ : ¬ EqSet.In q elt → EqSet.In q (EqSet.fold f elt e).eqs1 := by
    have hQ' := ESP.fold_rec_proof eqs
      (fun s a => {h : ¬ EqSet.In q s → EqSet.In q a.eqs1 // True})
      f e elt
      (by
        intro s hs
        refine ⟨?_, trivial⟩
        intro hnot
        exact hq)
      (by
        intro x a s' s'' hx hnot hadd hPa
        refine ⟨?_, trivial⟩
        intro hqmem
        have hqx : ¬ EqSetE.eq x q := by
          intro hxeq
          exact hqmem ((hadd q).mpr (Or.inl hxeq))
        have hqold : ¬ EqSet.In q s' := by
          intro hq'
          exact hqmem ((hadd q).mpr (Or.inr hq'))
        have hqa : EqSet.In q a.eqs1 := hPa.1 hqold
        apply (ESF.add_iff_proof _ _ _).mpr
        right
        apply (ESF.remove_iff_proof _ _ _).mpr
        exact ⟨hqa, hqx⟩)
    exact hQ'.1
  by_cases hqe : EqSet.In q elt
  · left
    exact ⟨(helt q).mp hqe |>.2, hP hqe⟩
  · right
    exact ⟨by
      intro heq
      apply hqe
      exact (helt q).mpr ⟨hq, heq⟩,
      hQ hqe⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values

theorem subst_reg_satisf : subst_reg_satisfStatement := by
  intro src dst rs ls e hsat
  unfold satisf at hsat ⊢
  intro q hq
  rcases in_subst_reg dst src q e hq with hq' | hq'
  · rcases hq' with ⟨hqd, hmem⟩
    have hval := hsat
      { ekind := q.ekind, ereg := src, eloc := q.eloc } hmem
    rw [hqd, Regmap.gss_proof val dst (Regmap.get src rs) rs]
    simpa using hval
  · rcases hq' with ⟨hqd, hmem⟩
    rw [Regmap.gso_proof val q.ereg dst (Regmap.get src rs) rs hqd]
    exact hsat q hmem

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation

theorem in_subst_reg_kind : in_subst_reg_kindStatement := by
  intro r1 k1 r2 k2 q e hq
  let elt : EqSet.t :=
    EqSet.elements_between (select_reg_l r1) (select_reg_h r1) e.eqs1
  have helt : ∀ x, EqSet.In x elt ↔ EqSet.In x e ∧ x.ereg = r1 := by
    intro x
    exact in_elements_between_1 r1 e.eqs1 x
  let f : EqSet.elt → eqs → eqs := fun x out =>
    match IndexedEqKind.eq x.ekind k1 with
    | .left _ =>
        add_equation { ekind := k2, ereg := r2, eloc := x.eloc }
          (remove_equation x out)
    | .right _ => out
  have hfold : EqSet.fold f elt e = subst_reg_kind r1 k1 r2 k2 e := by
    unfold subst_reg_kind
    apply congrArg (fun g => EqSet.fold g elt e)
    funext x out
    cases x with
    | mk ekind ereg eloc =>
        cases h : IndexedEqKind.eq ekind k1 with
        | left heq =>
            dsimp [f]
            rw [h]
            change (if true = true then
              add_equation { ekind := k2, ereg := r2, eloc := eloc }
                (remove_equation { ekind := ekind, ereg := ereg, eloc := eloc } out) else out) =
              add_equation { ekind := k2, ereg := r2, eloc := eloc }
                (remove_equation { ekind := ekind, ereg := ereg, eloc := eloc } out)
            simp
        | right hneq =>
            dsimp [f]
            rw [h]
            change (if false = true then
              add_equation { ekind := k2, ereg := r2, eloc := eloc }
                (remove_equation { ekind := ekind, ereg := ereg, eloc := eloc } out) else out) = out
            simp
  have hP : EqSet.In q elt → q.ekind = k1 →
      EqSet.In { ekind := k2, ereg := r2, eloc := q.eloc }
        (EqSet.fold f elt e).eqs1 := by
    have hP' := ESP.fold_rec_proof eqs
      (fun s a => {h : EqSet.In q s → q.ekind = k1 →
        EqSet.In { ekind := k2, ereg := r2, eloc := q.eloc } a.eqs1 // True})
      f e elt
      (by
        intro s hs
        refine ⟨?_, trivial⟩
        intro hmem _
        exact False.elim (hs q hmem))
      (by
        intro x a s' s'' hx hnot hadd hPa
        refine ⟨?_, trivial⟩
        intro hqmem hkq
        rcases (hadd q).mp hqmem with hqx | hqold
        · subst x
          cases hkind : IndexedEqKind.eq q.ekind k1 with
          | left heq =>
              simp only [f, hkind]
              apply (ESF.add_iff_proof _ _ _).mpr
              left
              exact EqSetE.eq_refl _
          | right hneq =>
              exact False.elim (hneq hkq)
        · have hqnew : EqSet.In
              { ekind := k2, ereg := r2, eloc := q.eloc } a.eqs1 :=
            hPa.1 hqold hkq
          cases hkind : IndexedEqKind.eq x.ekind k1 with
          | left heq =>
              simp only [f, hkind]
              by_cases hxeq : ESF.ESF.E.eq x
                  { ekind := k2, ereg := r2, eloc := q.eloc }
              · apply (ESF.add_iff_proof _ _ _).mpr
                left
                cases hxeq
                exact EqSetE.eq_refl _
              · apply (ESF.add_iff_proof _ _ _).mpr
                right
                apply (ESF.remove_iff_proof _ _ _).mpr
                exact ⟨hqnew, hxeq⟩
          | right hneq =>
              simp only [f, hkind]
              exact hqnew)
    exact hP'.1
  have hQ : (¬ EqSet.In q elt ∨ q.ekind ≠ k1) →
      EqSet.In q (EqSet.fold f elt e).eqs1 := by
    have hQ' := ESP.fold_rec_proof eqs
      (fun s a => {h : (¬ EqSet.In q s ∨ q.ekind ≠ k1) →
        EqSet.In q a.eqs1 // True})
      f e elt
      (by
        intro s hs
        refine ⟨?_, trivial⟩
        intro _
        exact hq)
      (by
        intro x a s' s'' hx hnot hadd hPa
        refine ⟨?_, trivial⟩
        intro hcond
        rcases hcond with hnotq | hqk
        · have hqnot : ¬ EqSet.In q s' := by
            intro hq'
            exact hnotq ((hadd q).mpr (Or.inr hq'))
          have hqa : EqSet.In q a.eqs1 :=
            hPa.1 (Or.inl hqnot)
          cases hkind : IndexedEqKind.eq x.ekind k1 with
          | left heq =>
              simp only [f, hkind]
              have hxeq : ¬ EqSetE.eq x q := by
                intro hxq
                apply hnotq
                apply (hadd q).mpr
                left
                exact hxq
              apply (ESF.add_iff_proof _ _ _).mpr
              right
              apply (ESF.remove_iff_proof _ _ _).mpr
              exact ⟨hqa, hxeq⟩
          | right hneq =>
              simp only [f, hkind]
              exact hqa
        · have hqa : EqSet.In q a.eqs1 :=
            hPa.1 (Or.inr hqk)
          cases hkind : IndexedEqKind.eq x.ekind k1 with
          | left heq =>
              simp only [f, hkind]
              have hxeq : ¬ EqSetE.eq x q := by
                intro hxq
                apply hqk
                rw [← hxq]
                exact heq
              apply (ESF.add_iff_proof _ _ _).mpr
              right
              apply (ESF.remove_iff_proof _ _ _).mpr
              exact ⟨hqa, hxeq⟩
          | right hneq =>
              simp only [f, hkind]
              exact hqa)
    exact hQ'.1
  by_cases hqe : EqSet.In q elt
  · by_cases hqk : q.ekind = k1
    · left
      refine ⟨?_, ?_⟩
      · have hr : q.ereg = r1 := (helt q).mp hqe |>.2
        exact Prod.ext hr hqk
      · rw [← hfold]
        exact hP hqe hqk
    · right
      rw [← hfold]
      exact hQ (Or.inr hqk)
  · right
    rw [← hfold]
    exact hQ (Or.inl hqe)

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values

theorem subst_reg_kind_satisf_lowlong :
    subst_reg_kind_satisf_lowlongStatement := by
  intro src dst rs ls e e1 hunc hsat
  unfold satisf at hsat ⊢
  intro q hq
  rcases in_subst_reg_kind dst .Full src .Low q e hq with hchanged | hsame
  · rcases hchanged with ⟨hpair, hmem⟩
    have hreg : q.ereg = dst := congrArg Prod.fst hpair
    have hkind : q.ekind = .Full := congrArg Prod.snd hpair
    have hval := hsat
      { ekind := .Low, ereg := src, eloc := q.eloc } hmem
    simpa [hreg, hkind, sel_val,
      Regmap.gss_proof val dst (Val.loword (Regmap.get src rs)) rs] using hval
  · have hne : q.ereg ≠ dst :=
      reg_unconstrained_sound dst (subst_reg_kind dst .Full src .Low e) q
        hunc hsame
    rw [Regmap.gso_proof val q.ereg dst
      (Val.loword (Regmap.get src rs)) rs hne]
    exact hsat q hsame

theorem subst_reg_kind_satisf_highlong :
    subst_reg_kind_satisf_highlongStatement := by
  intro src dst rs ls e e1 hunc hsat
  unfold satisf at hsat ⊢
  intro q hq
  rcases in_subst_reg_kind dst .Full src .High q e hq with hchanged | hsame
  · rcases hchanged with ⟨hpair, hmem⟩
    have hreg : q.ereg = dst := congrArg Prod.fst hpair
    have hkind : q.ekind = .Full := congrArg Prod.snd hpair
    have hval := hsat
      { ekind := .High, ereg := src, eloc := q.eloc } hmem
    simpa [hreg, hkind, sel_val,
      Regmap.gss_proof val dst (Val.hiword (Regmap.get src rs)) rs] using hval
  · have hne : q.ereg ≠ dst :=
      reg_unconstrained_sound dst (subst_reg_kind dst .Full src .High e) q
        hunc hsame
    rw [Regmap.gso_proof val q.ereg dst
      (Val.hiword (Regmap.get src rs)) rs hne]
    exact hsat q hsame

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

namespace RetryESF2

theorem add_iff_proof_retry : CompCert4Lean.Backend.Allocproof.ESF2.add_iff := by
  intro s x y
  constructor
  · intro h
    by_cases hxy : EqSet2E.eq x y
    · exact Or.inl hxy
    · exact Or.inr (EqSet2M.add_3 s x y hxy h)
  · intro h
    cases h with
    | inl hxy => exact EqSet2M.add_1 s x y hxy
    | inr hy => exact EqSet2M.add_2 s x y hy

end RetryESF2

namespace ESP2

noncomputable def fold_rec_proof : CompCert4Lean.Backend.Allocproof.ESP2.fold_rec := by
  intro A P f i s hEmpty hStep
  have of_list_in :
      ∀ (l : List EqSet2E.t) (x : EqSet2E.t),
        EqSet2M.In x (List.foldr EqSet2M.add EqSet2M.empty l) ↔
          CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x l := by
    intro l
    induction l with
    | nil =>
        intro x
        constructor
        · intro hx
          exact False.elim (EqSet2M.empty_1 x hx)
        · intro hx
          cases hx
    | cons y l ih =>
        intro x
        simp only [List.foldr]
        constructor
        · intro hx
          rw [CompCert4Lean.Backend.Allocproof.RetryESF2.add_iff_proof_retry] at hx
          rcases hx with hxy | hxl
          · exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_hd y l
              (EqSet2E.eq_sym _ _ hxy)
          · exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_tl y l ((ih x).mp hxl)
        · intro hx
          cases hx with
          | cons_hd _ _ hxy =>
              apply (CompCert4Lean.Backend.Allocproof.RetryESF2.add_iff_proof_retry _ y x).mpr
              exact Or.inl (EqSet2E.eq_sym _ _ hxy)
          | cons_tl _ _ hxl =>
              apply (CompCert4Lean.Backend.Allocproof.RetryESF2.add_iff_proof_retry _ y x).mpr
              exact Or.inr ((ih x).mpr hxl)
  have inA_append :
      ∀ (l₁ l₂ : List EqSet2E.t) (x : EqSet2E.t),
        CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x (l₁ ++ l₂) ↔
          CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x l₁ ∨
            CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x l₂ := by
    intro l₁ l₂ x
    change CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
        EqSet2E.eq x (l₁ ++ l₂) ↔
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
          EqSet2E.eq x l₁ ∨
        CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
          EqSet2E.eq x l₂
    rw [CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA_alt,
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA_alt,
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA_alt]
    constructor
    · rintro ⟨y, hxy, hy⟩
      rcases List.mem_append.mp hy with hy₁ | hy₂
      · exact Or.inl ⟨y, hxy, hy₁⟩
      · exact Or.inr ⟨y, hxy, hy₂⟩
    · rintro (⟨y, hxy, hy⟩ | ⟨y, hxy, hy⟩)
      · exact ⟨y, hxy, List.mem_append.mpr (Or.inl hy)⟩
      · exact ⟨y, hxy, List.mem_append.mpr (Or.inr hy)⟩
  have inA_reverse :
      ∀ (l : List EqSet2E.t) (x : EqSet2E.t),
        CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x l.reverse ↔
          CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x l := by
    intro l x
    change CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
        EqSet2E.eq x l.reverse ↔
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA EqSet2E.eq x l
    rw [CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA_alt,
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA_alt]
    constructor
    · rintro ⟨y, hxy, hy⟩
      exact ⟨y, hxy, List.mem_reverse.mp hy⟩
    · rintro ⟨y, hxy, hy⟩
      exact ⟨y, hxy, List.mem_reverse.mpr hy⟩
  have nodup_append_single :
      ∀ (l : List EqSet2E.t) (x : EqSet2E.t),
        CompCert4Lean.Lib.FSetInterface.NoDupA EqSet2E.eq l →
          ¬ CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x l →
          CompCert4Lean.Lib.FSetInterface.NoDupA EqSet2E.eq (l ++ [x]) := by
    intro l
    induction l with
    | nil =>
        intro x _ _
        apply CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA.cons
        · intro h
          cases h
        · exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA.nil
    | cons y l ih =>
        intro x hnd hnot
        cases hnd with
        | cons hny htail =>
            apply CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA.cons
            · intro hy
              rcases (inA_append l [x] y).mp hy with hyL | hyX
              · exact hny hyL
              · cases hyX with
                | cons_hd _ _ hyx =>
                    exact hnot (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_hd
                      y l (EqSet2E.eq_sym _ _ hyx))
                | cons_tl _ _ hyx => cases hyx
            · exact ih x htail (by
                intro hx
                exact hnot (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_tl y l hx))
  have nodup_reverse :
      ∀ (l : List EqSet2E.t),
        CompCert4Lean.Lib.FSetInterface.NoDupA EqSet2E.eq l →
          CompCert4Lean.Lib.FSetInterface.NoDupA EqSet2E.eq l.reverse := by
    intro l
    induction l with
    | nil =>
        intro _
        exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA.nil
    | cons y l ih =>
        intro hnd
        cases hnd with
        | cons hny htail =>
            have hnot : ¬ CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq y l.reverse := by
              intro hy
              exact hny ((inA_reverse l y).mp hy)
            have h := nodup_append_single l.reverse y (ih htail) hnot
            simpa [List.reverse_cons] using h
  rw [EqSet2M.fold_1]
  rw [List.foldl_eq_foldr_reverse]
  let l : List EqSet2E.t := (EqSet2M.elements s).reverse
  have hsame : ∀ x, EqSet2M.In x s ↔
      CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x l := by
    intro x
    constructor
    · intro hx
      exact (inA_reverse (EqSet2M.elements s) x).mpr
        ((EqSet2M.elements_1 s x) hx)
    · intro hx
      exact (EqSet2M.elements_2 s x) ((inA_reverse (EqSet2M.elements s) x).mp hx)
  have hnd : CompCert4Lean.Lib.FSetInterface.NoDupA EqSet2E.eq l := by
    exact nodup_reverse (EqSet2M.elements s) (EqSet2M.elements_3w s)
  have nodup_cons_inv :
      ∀ (x : EqSet2E.t) (l : List EqSet2E.t),
        CompCert4Lean.Lib.FSetInterface.NoDupA EqSet2E.eq (x :: l) →
          (¬ CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x l ∧
            CompCert4Lean.Lib.FSetInterface.NoDupA EqSet2E.eq l) := by
    intro x l h
    cases h with
    | cons hnot htail => exact ⟨hnot, htail⟩
  have fold_ind :
      ∀ (l : List EqSet2E.t) (s₀ : EqSet2M.t),
        (∀ x, EqSet2M.In x s₀ ↔
          CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x l) →
        (∀ x, CompCert4Lean.Lib.FSetInterface.InA EqSet2E.eq x l →
          EqSet2M.In x s) →
        CompCert4Lean.Lib.FSetInterface.NoDupA EqSet2E.eq l →
        P s₀ (List.foldr (fun x a => f x a) i l) := by
    intro l
    induction l with
    | nil =>
        intro s₀ hsame₀ _ _
        apply hEmpty
        intro x hx
        cases (hsame₀ x).mp hx
    | cons x l ih =>
        intro s₀ hsame₀ hsource₀ hnd₀
        have hnd' := nodup_cons_inv x l hnd₀
        have hnot := hnd'.1
        have htail := hnd'.2
        apply hStep x (List.foldr (fun x a => f x a) i l)
              (List.foldr EqSet2M.add EqSet2M.empty l) s₀
        · exact hsource₀ x
                (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_hd
                  x l (EqSet2E.eq_refl x))
        · intro hx
          exact hnot ((of_list_in l x).mp hx)
        · intro y
          constructor
          · intro hy
            cases (hsame₀ y).mp hy with
            | cons_hd _ _ hxy => exact Or.inl (EqSet2E.eq_sym _ _ hxy)
            | cons_tl _ _ hyl => exact Or.inr ((of_list_in l y).mpr hyl)
          · intro hy
            rcases hy with hyx | hyl
            · exact (hsame₀ y).mpr
                    (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_hd
                      x l (EqSet2E.eq_sym _ _ hyx))
            · exact (hsame₀ y).mpr
                    (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_tl
                      x l ((of_list_in l y).mp hyl))
        · exact ih (List.foldr EqSet2M.add EqSet2M.empty l)
            (fun y => of_list_in l y)
            (fun y hyl => hsource₀ y
              (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA.cons_tl
                x l hyl)) htail
  exact fold_ind l s hsame (fun x hx => (hsame x).mpr hx) hnd

end ESP2
end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.RTLtyping

theorem val_lessdef_normalize : val_lessdef_normalizeStatement := by
  intro v v' ty hv hld
  cases hld with
  | lessdef_refl =>
      rw [Val.load_result_same v ty hv]
      exact Val.lessdef_refl _
  | lessdef_undef =>
      exact Val.lessdef_undef _

theorem loc_type_compat_charact : loc_type_compat_charactStatement := by
  intro env l e q hcompat hq
  unfold loc_type_compat at hcompat
  have hiff := EqSet2.for_all_between_iff_proof
    (fun q : EqSet2.elt => CompCert4Lean.Common.AST.subtype
      (sel_type q.ekind (env q.ereg)) (Loc.type l))
    (select_loc_l l) (select_loc_h l)
    (by
      intro q₁ q₂ hqeq
      subst q₂
      rfl)
    (select_loc_l_monotone l) (select_loc_h_monotone l) e.eqs2
  rw [hiff] at hcompat
  cases hll : select_loc_l l q with
  | false =>
      right
      exact (select_loc_charact l q).mp (Or.inl hll)
  | true =>
      cases hhh : select_loc_h l q with
      | false =>
          right
          exact (select_loc_charact l q).mp (Or.inr hhh)
      | true =>
          left
          exact hcompat q ((e.eqs_same q).mpr hq) hll hhh

theorem well_typed_move_charact : well_typed_move_charactStatement := by
  intro env l e k r rs hmove hq hwt
  unfold well_typed_move at hmove
  cases l with
  | R mr => trivial
  | S sl ofs ty =>
      have hc := loc_type_compat_charact env (S sl ofs ty) e
        { ekind := k, ereg := r, eloc := S sl ofs ty } hmove hq
      rcases hc with hsub | hdiff
      · apply Val.has_subtype
        · simpa [Loc.type] using hsub
        · cases k with
          | Full => simpa [sel_val, sel_type] using hwt r
          | Low =>
              generalize hval : CompCert4Lean.Backend.Registers.Regmap.get r rs = v
              cases v <;>
                simp [hval, sel_val, sel_type, Val.loword, Val.has_type]
          | High =>
              generalize hval : CompCert4Lean.Backend.Registers.Regmap.get r rs = v
              cases v <;>
                simp [hval, sel_val, sel_type, Val.hiword, Val.has_type]
      · exfalso
        apply Loc.diff_not_eq (S sl ofs ty) (S sl ofs ty)
        · simpa using hdiff
        · rfl

private theorem partial_fold_eqs
    (P : EqSet2M.t → eqs → Prop)
    (f : EqSet2.elt → eqs → Option eqs) (init final : eqs) (s : EqSet2M.t) :
    EqSet2.fold (fun q opte => match opte with
      | none => none
      | some e => f q e) s (some init) = some final →
    (∀ s', EqSet2.Empty s' → P s' init) →
    (∀ x a' a'' s' s'',
      EqSet2.In x s → ¬ EqSet2.In x s' → ESP2.Add x s' s'' →
      f x a' = some a'' → P s' a' → P s'' a'') →
    P s final := by
  intro hfold hEmpty hStep
  let g : EqSet2.elt → Option eqs → Option eqs := fun x oa =>
    match oa with
    | none => none
    | some a => f x a
  let Q := fun (s : EqSet2M.t) oa =>
    {h : match oa with
      | none => True
      | some a => P s a // True}
  have hQ := ESP2.fold_rec_proof (A := Option eqs) (P := Q) (f := g)
      (i := some init) (s := s)
      (by
        intro s' hs'
        exact ⟨hEmpty s' hs', trivial⟩)
      (by
        intro x oa s' s'' hx hnot hadd hPa
        cases oa with
        | none => exact ⟨trivial, trivial⟩
        | some a =>
            cases hfa : f x a with
            | none =>
                simp only [g, hfa]
                exact ⟨trivial, trivial⟩
            | some a' =>
                simp only [g, hfa]
                exact ⟨hStep x a a' s' s'' hx hnot hadd hfa hPa.1, trivial⟩)
  have hQ' : Q s (some final) := by
    rw [← hfold]
    change Q s (EqSet2.fold g s (some init))
    exact hQ
  exact hQ'.1

theorem in_subst_loc : in_subst_locStatement := by
  intro l1 l2 q e e' hq hsubst
  unfold subst_loc at hsubst
  let elt : EqSet2.t :=
    EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) e.eqs2
  let q2 : EqSet2.E.t := q
  change equation at q2
  let f : EqSet2.elt → eqs → Option eqs := fun q0 out =>
    if decide (l1 = q0.eloc) = true then
      some (add_equation { ekind := q0.ekind, ereg := q0.ereg, eloc := l2 }
        (remove_equation q0 out))
    else none
  let P : EqSet2M.t → eqs → Prop := fun s0 e0 =>
    EqSet2.In q2 s0 → q.eloc = l1 ∧
      EqSet.In ({ q with eloc := l2 } : EqSet.elt) e0.eqs1
  have hP : P elt e' := by
    apply partial_fold_eqs P f e e' elt (by
      change EqSet2.fold (fun q opte => match opte with
        | none => none
        | some e => f q e) elt (some e) = some e' at hsubst
      exact hsubst)
    · intro s' hs' h
      exact False.elim (hs' q h)
    · intro x a' a'' s' s'' hx hnot hadd hfa hPa hqmem
      dsimp [f] at hfa ⊢
      change equation at x
      by_cases hxeq : l1 = x.eloc
      · simp [hxeq] at hfa
        cases hfa
        rcases (hadd q2).mp hqmem with hqx | hqold
        · have hqeq : x = q2 := hqx
          subst x
          refine ⟨?_, ?_⟩
          · simpa [q2] using hxeq.symm
          · apply EqSet.add_1
            exact EqSet.E.eq_refl _
        · have hqnew := hPa hqold
          refine ⟨hqnew.1, ?_⟩
          let qt : equation := { ekind := q.ekind, ereg := q.ereg, eloc := l2 }
          by_cases hxeq' : x = qt
          · subst x
            apply EqSet.add_1
            exact EqSet.E.eq_refl _
          · apply EqSet.add_2
            apply EqSet.remove_2 _ _ _
            · intro heq
              apply hxeq'
              exact heq
            · exact hqnew.2
      · simp [hxeq] at hfa
  let Q : EqSet2M.t → eqs → Prop := fun s0 e0 =>
    ¬ EqSet2.In q2 s0 → EqSet.In q e0.eqs1
  have hQ : Q elt e' := by
    apply partial_fold_eqs Q f e e' elt (by
      change EqSet2.fold (fun q opte => match opte with
        | none => none
        | some e => f q e) elt (some e) = some e' at hsubst
      exact hsubst)
    · intro s' hs' _
      exact hq
    · intro x a' a'' s' s'' hx hnot hadd hfa hQa hqnot
      dsimp [f] at hfa ⊢
      change equation at x
      by_cases hxeq : l1 = x.eloc
      · simp [hxeq] at hfa
        cases hfa
        have hqx : ¬ EqSet2.In q2 s' := by
          intro hq'
          exact hqnot ((hadd q2).mpr (Or.inr hq'))
        have hqold := hQa hqx
        have hqnew : ¬ EqSet.E.eq x q := by
          intro hxeq'
          exact hqnot ((hadd q2).mpr (Or.inl hxeq'))
        apply EqSet.add_2
        apply EqSet.remove_2 _ _ _ hqnew
        exact hqold
      · simp [hxeq] at hfa
  by_cases hqe : EqSet2.In q2 elt
  · left
    exact ⟨(hP hqe).1, (hP hqe).2⟩
  · right
    have hdiff : Loc.diff l1 q.eloc := by
      apply (select_loc_charact l1 q).1
      cases hll : select_loc_l l1 q with
      | false => exact Or.inl rfl
      | true =>
          cases hhh : select_loc_h l1 q with
          | false => exact Or.inr rfl
          | true =>
              exfalso
              apply hqe
              exact (EqSet2.elements_between_iff_proof (select_loc_l l1)
                (select_loc_h l1) (select_loc_l_monotone l1)
                (select_loc_h_monotone l1) q2 e.eqs2).mpr
                ⟨(e.eqs_same q).mpr hq, hll, hhh⟩
    exact ⟨hdiff, hQ hqe⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations

theorem in_subst_loc_part : in_subst_loc_partStatement := by
  intro l1 l2 k q e e' hq hsubst
  let elt : EqSet2.t :=
    EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) e.eqs2
  let q2 : EqSet2.E.t := q
  change equation at q2
  let f : EqSet2.elt → eqs → Option eqs := fun q0 out =>
    if decide (l1 = q0.eloc) = true then
      match IndexedEqKind.eq q0.ekind k with
      | .left _ =>
          some (add_equation { ekind := Full, ereg := q0.ereg, eloc := l2 }
            (remove_equation q0 out))
      | .right _ => none
    else none
  have hfold :
      EqSet2.fold (fun q0 opte => match opte with
        | none => none
        | some e0 => f q0 e0) elt (some e) = subst_loc_part l1 l2 k e := by
    unfold subst_loc_part
    apply congrArg (fun g => EqSet2.fold g elt (some e))
    funext x out
    cases x with
    | mk ekind ereg eloc =>
        cases out with
        | none => rfl
        | some out =>
            cases hloc : decide (l1 = eloc) with
            | false =>
                have hne : ¬ l1 = eloc := by
                  intro heq
                  subst eloc
                  simp at hloc
                simp [f, hloc, hne]
            | true =>
                have heq : l1 = eloc := of_decide_eq_true hloc
                cases hkind : IndexedEqKind.eq ekind k with
                | left heqk =>
                    simp [f, hloc, heq, hkind] <;> rfl
                | right hneq =>
                    simp [f, hloc, heq, hkind] <;> rfl
  have hsubst' :
      EqSet2.fold (fun q0 opte => match opte with
        | none => none
        | some e0 => f q0 e0) elt (some e) = some e' := by
    rw [hfold]
    exact hsubst
  let P : EqSet2M.t → eqs → Prop := fun s0 e0 =>
    EqSet2.In q2 s0 → q.eloc = l1 ∧ q.ekind = k ∧
      EqSet.In ({ ekind := Full, ereg := q.ereg, eloc := l2 } : EqSet.elt) e0.eqs1
  have hP : P elt e' := by
    apply partial_fold_eqs P f e e' elt hsubst'
    · intro s' hs' h
      exact False.elim (hs' q h)
    · intro x a' a'' s' s'' hx hnot hadd hfa hPa hqmem
      dsimp [f] at hfa ⊢
      change equation at x
      by_cases hxeq : l1 = x.eloc
      · cases hkind : IndexedEqKind.eq x.ekind k with
        | left heqk =>
            simp [hxeq, hkind] at hfa
            cases hfa
            rcases (hadd q2).mp hqmem with hqx | hqold
            · have hqeq : x = q2 := hqx
              subst x
              refine ⟨?_, ?_, ?_⟩
              · simpa [q2] using hxeq.symm
              · exact heqk
              · apply EqSet.add_1
                exact EqSet.E.eq_refl _
            · have hqnew := hPa hqold
              refine ⟨hqnew.1, hqnew.2.1, ?_⟩
              let qt : equation := { ekind := Full, ereg := q.ereg, eloc := l2 }
              by_cases hxeq' : x = qt
              · subst x
                apply EqSet.add_1
                exact EqSet.E.eq_refl _
              · apply EqSet.add_2
                apply EqSet.remove_2 _ _ _
                · intro heq
                  apply hxeq'
                  exact heq
                · exact hqnew.2.2
        | right hneq =>
            simp [hxeq, hkind] at hfa
      · simp [hxeq] at hfa
  let Q : EqSet2M.t → eqs → Prop := fun s0 e0 =>
    ¬ EqSet2.In q2 s0 → EqSet.In q e0.eqs1
  have hQ : Q elt e' := by
    apply partial_fold_eqs Q f e e' elt hsubst'
    · intro s' hs' _
      exact hq
    · intro x a' a'' s' s'' hx hnot hadd hfa hQa hqnot
      dsimp [f] at hfa ⊢
      change equation at x
      by_cases hxeq : l1 = x.eloc
      · cases hkind : IndexedEqKind.eq x.ekind k with
        | left heqk =>
            simp [hxeq, hkind] at hfa
            cases hfa
            have hqx : ¬ EqSet2.In q2 s' := by
              intro hq'
              exact hqnot ((hadd q2).mpr (Or.inr hq'))
            have hqold := hQa hqx
            have hqnew : ¬ EqSet.E.eq x q := by
              intro hxeq'
              exact hqnot ((hadd q2).mpr (Or.inl hxeq'))
            apply EqSet.add_2
            apply EqSet.remove_2 _ _ _ hqnew
            exact hqold
        | right hneq =>
            simp [hxeq, hkind] at hfa
      · simp [hxeq] at hfa
  by_cases hqe : EqSet2.In q2 elt
  · left
    exact hP hqe
  · right
    have hdiff : Loc.diff l1 q.eloc := by
      apply (select_loc_charact l1 q).1
      cases hll : select_loc_l l1 q with
      | false => exact Or.inl rfl
      | true =>
          cases hhh : select_loc_h l1 q with
          | false => exact Or.inr rfl
          | true =>
              exfalso
              apply hqe
              exact (EqSet2.elements_between_iff_proof (select_loc_l l1)
                (select_loc_h l1) (select_loc_l_monotone l1)
                (select_loc_h_monotone l1) q2 e.eqs2).mpr
                ⟨(e.eqs_same q).mpr hq, hll, hhh⟩
    exact ⟨hdiff, hQ hqe⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values

theorem subst_loc_part_satisf_lowlong :
    subst_loc_part_satisf_lowlongStatement := by
  intro src dst rs ls e e' hsubst hsat
  unfold satisf at hsat ⊢
  intro q hq
  change CompCert4Lean.Backend.Registers.Regmap.t val at rs
  change CompCert4Lean.Backend.Locations.Locmap.t at ls
  change equation at q
  rcases in_subst_loc_part (R dst) (R src) Low q e e' hq hsubst with hchanged | hsame
  · rcases hchanged with ⟨hqloc, hqkind, hmem⟩
    have hval := hsat
      { ekind := Full, ereg := q.ereg, eloc := R src } hmem
    have loword_lessdef_local : ∀ (v v' : val),
        Val.lessdef v v' → Val.lessdef (Val.loword v) (Val.loword v') := by
      intro v v' hv
      cases hv with
      | lessdef_refl v => exact Val.lessdef.lessdef_refl _
      | lessdef_undef v => exact Val.lessdef.lessdef_undef _
    have hval' : Val.lessdef (Regmap.get q.ereg rs) (ls (R src)) := by
      simpa [sel_val] using hval
    rw [hqloc, hqkind, Locmap.gss]
    change Val.lessdef (Val.loword (Regmap.get q.ereg rs)) (Val.loword (ls (R src)))
    exact loword_lessdef_local _ _ hval'
  · rcases hsame with ⟨hdiff, hmem⟩
    rw [Locmap.gso _ _ _ _ hdiff]
    exact hsat q hmem

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values

theorem subst_loc_part_satisf_highlong :
    subst_loc_part_satisf_highlongStatement := by
  intro src dst rs ls e e' hsubst hsat
  unfold satisf at hsat ⊢
  intro q hq
  change CompCert4Lean.Backend.Registers.Regmap.t val at rs
  change CompCert4Lean.Backend.Locations.Locmap.t at ls
  change equation at q
  rcases in_subst_loc_part (R dst) (R src) High q e e' hq hsubst with hchanged | hsame
  · rcases hchanged with ⟨hqloc, hqkind, hmem⟩
    have hval := hsat
      { ekind := Full, ereg := q.ereg, eloc := R src } hmem
    have hiword_lessdef_local : ∀ (v v' : val),
        Val.lessdef v v' → Val.lessdef (Val.hiword v) (Val.hiword v') := by
      intro v v' hv
      cases hv with
      | lessdef_refl v => exact Val.lessdef.lessdef_refl _
      | lessdef_undef v => exact Val.lessdef.lessdef_undef _
    have hval' : Val.lessdef (Regmap.get q.ereg rs) (ls (R src)) := by
      simpa [sel_val] using hval
    rw [hqloc, hqkind, Locmap.gss]
    change Val.lessdef (Val.hiword (Regmap.get q.ereg rs)) (Val.hiword (ls (R src)))
    exact hiword_lessdef_local _ _ hval'
  · rcases hsame with ⟨hdiff, hmem⟩
    rw [Locmap.gso _ _ _ _ hdiff]
    exact hsat q hmem

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations

theorem in_subst_loc_pair : in_subst_loc_pairStatement := by
  intro l1 l2 l2' q e e' hq hsubst
  let elt : EqSet2.t :=
    EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) e.eqs2
  let q2 : EqSet2.E.t := q
  change equation at q2
  let f : EqSet2.elt → eqs → Option eqs := fun q0 out =>
    if decide (l1 = q0.eloc) = true then
      match IndexedEqKind.eq q0.ekind Full with
      | .left _ =>
          some (add_equation { ekind := High, ereg := q0.ereg, eloc := l2 }
            (add_equation { ekind := Low, ereg := q0.ereg, eloc := l2' }
              (remove_equation q0 out)))
      | .right _ => none
    else none
  have hfold :
      EqSet2.fold (fun q0 opte => match opte with
        | none => none
        | some e0 => f q0 e0) elt (some e) = subst_loc_pair l1 l2 l2' e := by
    unfold subst_loc_pair
    apply congrArg (fun g => EqSet2.fold g elt (some e))
    funext x out
    cases x with
    | mk ekind ereg eloc =>
        cases out with
        | none => rfl
        | some out =>
            cases hloc : decide (l1 = eloc) with
            | false =>
                have hne : ¬ l1 = eloc := by
                  intro heq
                  subst eloc
                  simp at hloc
                simp [f, hloc, hne]
            | true =>
                have heq : l1 = eloc := of_decide_eq_true hloc
                cases hkind : IndexedEqKind.eq ekind Full with
                | left heqk =>
                    simp [f, hloc, heq, hkind] <;> rfl
                | right hneq =>
                    simp [f, hloc, heq, hkind] <;> rfl
  have hsubst' :
      EqSet2.fold (fun q0 opte => match opte with
        | none => none
        | some e0 => f q0 e0) elt (some e) = some e' := by
    rw [hfold]
    exact hsubst
  let P : EqSet2M.t → eqs → Prop := fun s0 e0 =>
    EqSet2.In q2 s0 → q.eloc = l1 ∧ q.ekind = Full ∧
      EqSet.In ({ ekind := High, ereg := q.ereg, eloc := l2 } : EqSet.elt) e0.eqs1 ∧
      EqSet.In ({ ekind := Low, ereg := q.ereg, eloc := l2' } : EqSet.elt) e0.eqs1
  have hP : P elt e' := by
    apply partial_fold_eqs P f e e' elt hsubst'
    · intro s' hs' h
      exact False.elim (hs' q h)
    · intro x a' a'' s' s'' hx hnot hadd hfa hPa hqmem
      dsimp [f] at hfa ⊢
      change equation at x
      by_cases hxeq : l1 = x.eloc
      · cases hkind : IndexedEqKind.eq x.ekind Full with
        | left heqk =>
            simp [hxeq, hkind] at hfa
            cases hfa
            rcases (hadd q2).mp hqmem with hqx | hqold
            · have hqeq : x = q2 := hqx
              subst x
              refine ⟨?_, heqk, ?_, ?_⟩
              · simpa [q2] using hxeq.symm
              · apply EqSet.add_1
                exact EqSet.E.eq_refl _
              · apply EqSet.add_2
                apply EqSet.add_1
                exact EqSet.E.eq_refl _
            · have hqnew := hPa hqold
              have hhigh : EqSet.In
                  ({ ekind := High, ereg := q.ereg, eloc := l2 } : EqSet.elt)
                  (add_equation { ekind := High, ereg := x.ereg, eloc := l2 }
                    (add_equation { ekind := Low, ereg := x.ereg, eloc := l2' }
                      (remove_equation x a'))).eqs1 := by
                by_cases heqhigh :
                    ({ ekind := High, ereg := q.ereg, eloc := l2 } : equation) =
                      { ekind := High, ereg := x.ereg, eloc := l2 }
                · apply EqSet.add_1
                  exact heqhigh.symm
                · apply EqSet.add_2
                  apply EqSet.add_2
                  have hxhigh : ¬ EqSet.E.eq x
                      ({ ekind := High, ereg := q.ereg, eloc := l2 } : equation) := by
                    intro h
                    subst x
                    cases heqk
                  apply EqSet.remove_2 _ _ _ hxhigh
                  exact hqnew.2.2.1
              have hlow : EqSet.In
                  ({ ekind := Low, ereg := q.ereg, eloc := l2' } : EqSet.elt)
                  (add_equation { ekind := High, ereg := x.ereg, eloc := l2 }
                    (add_equation { ekind := Low, ereg := x.ereg, eloc := l2' }
                      (remove_equation x a'))).eqs1 := by
                by_cases heqlow :
                    ({ ekind := Low, ereg := q.ereg, eloc := l2' } : equation) =
                      { ekind := Low, ereg := x.ereg, eloc := l2' }
                · apply EqSet.add_2
                  apply EqSet.add_1
                  exact heqlow.symm
                · apply EqSet.add_2
                  apply EqSet.add_2
                  have hxlow : ¬ EqSet.E.eq x
                      ({ ekind := Low, ereg := q.ereg, eloc := l2' } : equation) := by
                    intro h
                    subst x
                    cases heqk
                  apply EqSet.remove_2 _ _ _ hxlow
                  exact hqnew.2.2.2
              exact ⟨hqnew.1, hqnew.2.1, hhigh, hlow⟩
        | right hneq =>
            simp [hxeq, hkind] at hfa
      · simp [hxeq] at hfa
  let Q : EqSet2M.t → eqs → Prop := fun s0 e0 =>
    ¬ EqSet2.In q2 s0 → EqSet.In q e0.eqs1
  have hQ : Q elt e' := by
    apply partial_fold_eqs Q f e e' elt hsubst'
    · intro s' hs' _
      exact hq
    · intro x a' a'' s' s'' hx hnot hadd hfa hQa hqnot
      dsimp [f] at hfa ⊢
      change equation at x
      by_cases hxeq : l1 = x.eloc
      · cases hkind : IndexedEqKind.eq x.ekind Full with
        | left heqk =>
            simp [hxeq, hkind] at hfa
            cases hfa
            have hqx : ¬ EqSet2.In q2 s' := by
              intro hq'
              exact hqnot ((hadd q2).mpr (Or.inr hq'))
            have hqold := hQa hqx
            have hqnew : ¬ EqSet.E.eq x q := by
              intro hxeq'
              exact hqnot ((hadd q2).mpr (Or.inl hxeq'))
            let qh : equation := { ekind := High, ereg := x.ereg, eloc := l2 }
            let ql : equation := { ekind := Low, ereg := x.ereg, eloc := l2' }
            by_cases hq_high : q = qh
            · subst q
              apply EqSet.add_1
              exact EqSet.E.eq_refl _
            · apply EqSet.add_2
              by_cases hq_low : q = ql
              · subst q
                apply EqSet.add_1
                exact EqSet.E.eq_refl _
              · apply EqSet.add_2
                apply EqSet.remove_2 _ _ _ hqnew
                exact hqold
        | right hneq =>
            simp [hxeq, hkind] at hfa
      · simp [hxeq] at hfa
  by_cases hqe : EqSet2.In q2 elt
  · left
    exact hP hqe
  · right
    have hdiff : Loc.diff l1 q.eloc := by
      apply (select_loc_charact l1 q).1
      cases hll : select_loc_l l1 q with
      | false => exact Or.inl rfl
      | true =>
          cases hhh : select_loc_h l1 q with
          | false => exact Or.inr rfl
          | true =>
              exfalso
              apply hqe
              exact (EqSet2.elements_between_iff_proof (select_loc_l l1)
                (select_loc_h l1) (select_loc_l_monotone l1)
                (select_loc_h_monotone l1) q2 e.eqs2).mpr
                ⟨(e.eqs_same q).mpr hq, hll, hhh⟩
    exact ⟨hdiff, hQ hqe⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
theorem undef_regs_outside : undef_regs_outsideStatement := by
  intro ml ls l hnot
  induction ml with
  | nil => rfl
  | cons m ms ih =>
      simp [CompCert4Lean.Backend.LTL.undef_regs] at *
      rw [Locmap.gso (R m) Common.Values.Vundef
        (CompCert4Lean.Backend.LTL.undef_regs ms ls) l
        (Loc.diff_sym l (R m) hnot.1)]
      exact ih hnot.2
end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
theorem can_undef_sound : can_undef_soundStatement := by
  intro e ml
  induction ml with
  | nil =>
      intro q hcan hq
      trivial
  | cons m ms ih =>
      intro q hcan hq
      simp [can_undef, Bool.and_eq_true] at hcan
      refine ⟨Loc.diff_sym (R m) q.eloc
        (loc_unconstrained_sound (R m) e q hcan.1 hq), ?_⟩
      apply ih q hcan.2 hq
end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
theorem long_type_compat_charact : long_type_compat_charactStatement := by
  intro env l e q hcompat hq
  unfold long_type_compat at hcompat
  have hiff := EqSet2.for_all_between_iff_proof
    (fun q : EqSet2.elt => subtype (env q.ereg) Tlong)
    (select_loc_l l) (select_loc_h l)
    (by
      intro q₁ q₂ hqeq
      subst q₂
      rfl)
    (select_loc_l_monotone l) (select_loc_h_monotone l) e.eqs2
  rw [hiff] at hcompat
  cases hll : select_loc_l l q with
  | false =>
      right
      exact (select_loc_charact l q).mp (Or.inl hll)
  | true =>
      cases hhh : select_loc_h l q with
      | false =>
          right
          exact (select_loc_charact l q).mp (Or.inr hhh)
      | true =>
          left
          exact hcompat q ((e.eqs_same q).mpr hq) hll hhh
end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.AST
theorem subst_loc_pair_satisf_makelong :
    subst_loc_pair_satisf_makelongStatement := by
  intro env src1 src2 dst rs ls e e' hsubst hcompat hwt hsat hptr
  unfold satisf at hsat ⊢
  intro q hq
  rcases (in_subst_loc_pair (R dst) (R src1) (R src2) q e e' hq hsubst) with
    ⟨hloc, hkind, hhigh, hlow⟩ | ⟨hdiff, hq'⟩
  · rw [hloc, hkind]
    have hlong : subtype (env q.ereg) Tlong = true := by
      rcases long_type_compat_charact env (R dst) e q hcompat hq with h | h
      · exact h
      · exact False.elim ((Loc.diff_not_eq (R dst) q.eloc h) hloc.symm)
    have hhigh' := hsat _ hhigh
    have hlow' := hsat _ hlow
    have hvaltype : Val.has_type (Regmap.get q.ereg rs) Tlong := by
      apply Val.has_subtype (env q.ereg) Tlong (Regmap.get q.ereg rs) hlong
      exact hwt q.ereg
    rw [Locmap.gss (R dst)
      (Val.longofwords (ls (R src1)) (ls (R src2))) ls]
    simp only [sel_val]
    rw [← val_longofwords_eq_1 (Regmap.get q.ereg rs) hvaltype hptr]
    apply allocproof_longofwords_lessdef
    · exact hhigh'
    · exact hlow'
  · rw [Locmap.gso (R dst)
      (Val.longofwords (ls (R src1)) (ls (R src2))) ls q.eloc hdiff]
    exact hsat q hq'
end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
theorem can_undef_except_sound : can_undef_except_soundStatement := by
  intro lx e ml q hcan hq hdiff
  induction ml with
  | nil => simp [Loc.notin]
  | cons m ms ih =>
      simp [can_undef_except, Bool.and_eq_true, Bool.or_eq_true] at hcan
      rcases hcan with ⟨hmcase, hrest⟩
      have hm : Loc.diff q.eloc (R m) := by
        rcases hmcase with heq | hunc
        · exact heq ▸ hdiff
        · exact Loc.diff_sym _ _ (loc_unconstrained_sound (R m) e q hunc hq)
      exact ⟨hm, ih hrest⟩
end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
theorem can_undef_satisf : can_undef_satisfStatement := by
  intro ml e rs ls hcan hsat q hq
  have hn := can_undef_sound e ml q hcan hq
  rw [undef_regs_outside ml ls q.eloc hn]
  exact hsat q hq
end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values

theorem subst_loc_undef_satisf : subst_loc_undef_satisfStatement := by
  intro env src dst rs ls ml e e' hsubst hmove hcan hwt hsat
  unfold satisf at hsat ⊢
  intro q hq
  change equation at q
  rcases in_subst_loc dst src q e e' hq hsubst with hchanged | hsame
  · rcases hchanged with ⟨hqloc, hmem⟩
    subst dst
    cases q with
    | mk k r l =>
        have hchar := well_typed_move_charact env l e k r rs hmove hq hwt
        cases l with
        | R mr =>
            change Val.lessdef (sel_val k (Regmap.get r rs))
              ((Locmap.set (R mr) (ls src) (LTL.undef_regs ml ls)) (R mr))
            have hset := Locmap.gss (R mr) (ls src) (LTL.undef_regs ml ls)
            rw [hset]
            simpa [sel_val] using (hsat { ekind := k, ereg := r, eloc := src } hmem)
        | S sl ofs ty =>
            change Val.lessdef (sel_val k (Regmap.get r rs))
              ((Locmap.set (S sl ofs ty) (ls src) (LTL.undef_regs ml ls))
                (S sl ofs ty))
            have hset := Locmap.gss (S sl ofs ty) (ls src) (LTL.undef_regs ml ls)
            rw [hset]
            exact val_lessdef_normalize _ _ _ hchar (by
              simpa [sel_val] using
                (hsat { ekind := k, ereg := r, eloc := src } hmem))
  · rcases hsame with ⟨hdiff, hmem⟩
    cases q with
    | mk k r l =>
        change Val.lessdef (sel_val k (Regmap.get r rs))
          ((Locmap.set dst (ls src) (LTL.undef_regs ml ls)) l)
        have hset := Locmap.gso dst (ls src) (LTL.undef_regs ml ls) l hdiff
        rw [hset]
        rw [undef_regs_outside ml ls l]
        · exact hsat { ekind := k, ereg := r, eloc := l } hmem
        · exact can_undef_except_sound dst e ml { ekind := k, ereg := r, eloc := l }
            hcan hq (Loc.diff_sym _ _ hdiff)

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.Values

theorem transfer_use_def_satisf : transfer_use_def_satisfStatement := by
  intro args resultReg args' resultMreg und e e' rs ls htrans hsat
  unfold transfer_use_def at htrans
  let e1 := remove_equation
    { ekind := .Full, ereg := resultReg, eloc := .R resultMreg } e
  change ((if (reg_loc_unconstrained resultReg (.R resultMreg) e1 &&
      can_undef und e1) = true then add_equations args args' e1 else none) = some e') at htrans
  by_cases hc : (reg_loc_unconstrained resultReg (.R resultMreg) e1 &&
      can_undef und e1) = true
  · simp [hc] at htrans
    have hc' : reg_loc_unconstrained resultReg (.R resultMreg) e1 = true ∧
        can_undef und e1 = true := by
      simpa [Bool.and_eq_true] using hc
    constructor
    · exact add_equations_lessdef rs ls args args' e1 e' htrans hsat
    · intro v v' hld
      apply parallel_assignment_satisf .Full resultReg resultMreg e rs
        (LTL.undef_regs und ls) v v'
      · exact hld
      · simpa [e1, reg_loc_unconstrained] using hc'.1
      · apply can_undef_satisf und e1 rs ls
        · simpa [e1, reg_loc_unconstrained] using hc'.2
        · apply add_equations_satisf rs ls args args' e1 e' htrans hsat
  · simp [hc] at htrans

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Conventions

theorem return_regs_agree_callee_save : return_regs_agree_callee_saveStatement := by
  intro cfg caller callee l hl
  cases l with
  | R r =>
      change CompCert4Lean.X86.Conventions1.is_callee_save cfg r = true at hl
      by_cases h : CompCert4Lean.X86.Conventions1.is_callee_save cfg r = true
      · simp [LTL.return_regs, h]
      · exact False.elim (h hl)
  | S sl ofs ty =>
      cases sl with
      | Local => rfl
      | Incoming => rfl
      | Outgoing => exact False.elim (hl rfl)

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Conventions

theorem no_caller_saves_sound : no_caller_saves_soundStatement := by
  intro cfg e q hno hq
  unfold no_caller_saves at hno
  let f : EqSet.elt → Bool := fun q =>
    match q.eloc with
    | .R r => CompCert4Lean.X86.Conventions1.is_callee_save cfg r
    | .S .Outgoing _ _ => false
    | .S _ _ _ => true
  have hcompat : CompCert4Lean.Lib.FSetInterface.compat_bool
      OrderedEquation.eq f := by
    intro q1 q2 hEq
    cases hEq
    rfl
  have hall : EqSet.For_all (fun q => f q = true) e.eqs1 := by
    apply EqSet.for_all_2 e.eqs1 f hcompat
    exact hno
  have hq' : f q = true := hall q hq
  unfold callee_save_loc
  cases hloc : q.eloc with
  | R r =>
      simpa [f, hloc] using hq'
  | S sl ofs ty =>
      cases sl with
      | Outgoing => simp [f, hloc] at hq'
      | Local => simp [f, hloc]
      | Incoming => simp [f, hloc]

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers

theorem add_equations_res_lessdef : add_equations_res_lessdefStatement := by
  intro r ty p e e' rs ls hrun hsat htype
  cases p with
  | One mr =>
      simp [add_equations_res] at hrun
      rcases hrun with rfl
      exact add_equation_lessdef (rs := rs) (ls := ls)
        (q := { ekind := .Full, ereg := r, eloc := .R mr }) (e := e) hsat
  | Twolong hi lo =>
      by_cases hty : ty = Tlong
      · subst ty
        simp [add_equations_res] at hrun
        rcases hrun with ⟨hptr, hrun⟩
        change Val.lessdef (Regmap.get r rs)
          (Val.longofwords (ls (R hi)) (ls (R lo)))
        rw [← val_longofwords_eq_1 (Regmap.get r rs) htype hptr]
        have hsat_nested : satisf rs ls
            (add_equation { ekind := .Low, ereg := r, eloc := .R lo }
              (add_equation { ekind := .High, ereg := r, eloc := .R hi } e)) := by
          rw [hrun]
          exact hsat
        have hsat_high : satisf rs ls
            (add_equation { ekind := .High, ereg := r, eloc := .R hi } e) :=
          add_equation_satisf rs ls
            { ekind := .Low, ereg := r, eloc := .R lo }
            (add_equation { ekind := .High, ereg := r, eloc := .R hi } e)
            hsat_nested
        apply allocproof_longofwords_lessdef
        · exact add_equation_lessdef (rs := rs) (ls := ls)
            (q := { ekind := .High, ereg := r, eloc := .R hi }) (e := e)
            hsat_high
        · exact add_equation_lessdef (rs := rs) (ls := ls)
            (q := { ekind := .Low, ereg := r, eloc := .R lo })
            (e := add_equation { ekind := .High, ereg := r, eloc := .R hi } e)
            hsat_nested
      · simp [add_equations_res, hty] at hrun

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

private theorem ap_word_val_lt {bits : Nat} (x : WordCore.Word bits) :
    x.val < 2 ^ bits := by
  exact (WordCore.Word.toFin x).isLt

private theorem ap_word_unsigned_nat {bits : Nat} (w : WordCore.Word bits) :
    WordCore.unsigned w = ZArith.BinInt.Z.of_nat w.val := by
  have hw : ZArith.BinInt.Z.le Z0 (WordCore.unsigned w) := by
    have h := w.intrange.1
    change (-1 : Int) < intOfZ (WordCore.unsigned w) at h
    change 0 ≤ intOfZ (WordCore.unsigned w)
    omega
  exact (ZArith.Znat.Z2Nat.id (WordCore.unsigned w) hw).symm

private theorem ap_word_repr_val_nat (bits n : Nat) :
    (WordCore.repr bits (ZArith.BinInt.Z.of_nat n)).val = n % (2 ^ bits) := by
  simp
  run_tac
    let pieces := "_private.CompCert4Lean.Lib.Integers.0.CompCert4Lean.Lib.Integers.WordCore.residue_zOfNat".splitOn "."
    let nm := pieces.foldl (fun acc s => if s = "0" then Lean.Name.num acc 0 else Lean.Name.str acc s) Lean.Name.anonymous
    let g ← Lean.Elab.Tactic.getMainGoal
    let goals ← g.apply (Lean.mkConst nm)
    Lean.Elab.Tactic.replaceMainGoal goals

private theorem ap_word_shl_val {bits : Nat} (x y : WordCore.Word bits) :
    (WordCore.shl x y).val = (x.val * 2 ^ y.val) % (2 ^ bits) := by
  change (WordCore.repr bits
    (ZArith.BinInt.Z.shiftl (WordCore.unsigned x) (WordCore.unsigned y))).val = _
  rw [ap_word_unsigned_nat x, ap_word_unsigned_nat y]
  rw [show ZArith.BinInt.Z.shiftl (ZArith.BinInt.Z.of_nat x.val)
      (ZArith.BinInt.Z.of_nat y.val) =
      ZArith.BinInt.Z.of_nat (x.val * 2 ^ y.val) by
    unfold ZArith.BinInt.Z.shiftl
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte]
    rw [Int.natCast_mul, Int.natCast_pow]
    rfl]
  exact ap_word_repr_val_nat bits (x.val * 2 ^ y.val)

private theorem ap_word_or_val {bits : Nat} (x y : WordCore.Word bits) :
    (WordCore.or x y).val = Nat.lor x.val y.val := by
  unfold WordCore.or
  rw [ap_word_repr_val_nat]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (ap_word_val_lt x) (ap_word_val_lt y))

private theorem ap_word_shru_val {bits : Nat} (x y : WordCore.Word bits) :
    (WordCore.shru x y).val = x.val / 2 ^ y.val := by
  change (WordCore.repr bits
    (ZArith.BinInt.Z.shiftr (WordCore.unsigned x) (WordCore.unsigned y))).val = _
  rw [ap_word_unsigned_nat x, ap_word_unsigned_nat y]
  rw [show ZArith.BinInt.Z.shiftr (ZArith.BinInt.Z.of_nat x.val)
      (ZArith.BinInt.Z.of_nat y.val) =
      ZArith.BinInt.Z.of_nat (x.val / 2 ^ y.val) by
    unfold ZArith.BinInt.Z.shiftr
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte]
    rw [Int.natCast_ediv, Int.natCast_pow]
    rfl]
  rw [ap_word_repr_val_nat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (ap_word_val_lt x))

private theorem ap_hi_ofwords (hi lo : CompCert4Lean.Lib.Integers.Int.int) :
    Int64.hiword (Int64.ofwords hi lo) = hi := by
  have hhi : hi.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize :=
    ap_word_val_lt hi
  have hlo : lo.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize :=
    ap_word_val_lt lo
  have hshift :
      (WordCore.repr Int64.wordsize
        CompCert4Lean.Lib.Integers.Int.zwordsize).val = 32 := by
    change (WordCore.repr Int64.wordsize
      (ZArith.BinInt.Z.of_nat 32)).val = 32
    rw [ap_word_repr_val_nat]
    decide
  apply WordCore.ext_of_val_eq
  unfold Int64.hiword
  simp only [CompCert4Lean.Lib.Integers.Int.repr, Int64.unsigned, Int64.shru]
  rw [ap_word_unsigned_nat, ap_word_repr_val_nat]
  unfold Int64.ofwords
  simp only [Int64.or, Int64.shl, Int64.repr,
    CompCert4Lean.Lib.Integers.Int.unsigned]
  rw [ap_word_shru_val, ap_word_or_val, ap_word_shl_val]
  rw [@ap_word_unsigned_nat CompCert4Lean.Lib.Integers.Int.wordsize hi,
    ap_word_repr_val_nat]
  rw [@ap_word_unsigned_nat CompCert4Lean.Lib.Integers.Int.wordsize lo,
    ap_word_repr_val_nat]
  rw [hshift]
  have hpowle :
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize ≤ 2 ^ Int64.wordsize := by
    decide
  have hhi64 : hi.val < 2 ^ Int64.wordsize :=
    Nat.lt_of_lt_of_le hhi hpowle
  have hlo64 : lo.val < 2 ^ Int64.wordsize :=
    Nat.lt_of_lt_of_le hlo hpowle
  rw [Nat.mod_eq_of_lt hhi64, Nat.mod_eq_of_lt hlo64]
  have hprod : hi.val * 2 ^ 32 < 2 ^ Int64.wordsize := by
    change hi.val * 2 ^ 32 < 2 ^ 64
    change hi.val < 2 ^ 32 at hhi
    omega
  rw [Nat.mod_eq_of_lt hprod]
  change (((hi.val * 2 ^ 32) ||| lo.val) / 2 ^ 32) %
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize = hi.val
  have hor := @Nat.or_div_two_pow (hi.val * 2 ^ 32) lo.val 32
  rw [hor]
  have hdivlo : lo.val / 2 ^ 32 = 0 := Nat.div_eq_of_lt hlo
  rw [hdivlo, Nat.or_zero]
  rw [Nat.mul_comm, Nat.mul_div_right hi.val (Nat.two_pow_pos 32)]
  exact Nat.mod_eq_of_lt hhi

open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Values.Val

theorem val_hiword_longofwords : val_hiword_longofwordsStatement := by
  intro v1 v2
  cases v1 with
  | Vundef =>
      exact Val.lessdef_undef _
  | Vint hi =>
      cases v2 with
      | Vint lo =>
          change Val.lessdef
            (val.Vint (Int64.hiword (Int64.ofwords hi lo))) (val.Vint hi)
          rw [ap_hi_ofwords hi lo]
          exact Val.lessdef_refl _
      | _ =>
          exact Val.lessdef_undef _
  | Vlong _ =>
      exact Val.lessdef_undef _
  | Vfloat _ =>
      exact Val.lessdef_undef _
  | Vsingle _ =>
      exact Val.lessdef_undef _
  | Vptr _ _ =>
      exact Val.lessdef_undef _

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Values.Val

private theorem ap_lo_ofwords (hi lo : CompCert4Lean.Lib.Integers.Int.int) :
    Int64.loword (Int64.ofwords hi lo) = lo := by
  have hhi : hi.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize :=
    ap_word_val_lt hi
  have hlo : lo.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize :=
    ap_word_val_lt lo
  have hshift :
      (WordCore.repr Int64.wordsize
        CompCert4Lean.Lib.Integers.Int.zwordsize).val = 32 := by
    change (WordCore.repr Int64.wordsize
      (ZArith.BinInt.Z.of_nat 32)).val = 32
    rw [ap_word_repr_val_nat]
    decide
  apply WordCore.ext_of_val_eq
  unfold Int64.loword
  simp only [CompCert4Lean.Lib.Integers.Int.repr, Int64.unsigned]
  rw [ap_word_unsigned_nat, ap_word_repr_val_nat]
  unfold Int64.ofwords
  simp only [Int64.or, Int64.shl, Int64.repr,
    CompCert4Lean.Lib.Integers.Int.unsigned]
  rw [ap_word_or_val, ap_word_shl_val]
  rw [@ap_word_unsigned_nat CompCert4Lean.Lib.Integers.Int.wordsize hi,
    ap_word_repr_val_nat]
  rw [@ap_word_unsigned_nat CompCert4Lean.Lib.Integers.Int.wordsize lo,
    ap_word_repr_val_nat]
  rw [hshift]
  have hpowle :
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize ≤ 2 ^ Int64.wordsize := by
    decide
  have hhi64 : hi.val < 2 ^ Int64.wordsize :=
    Nat.lt_of_lt_of_le hhi hpowle
  have hlo64 : lo.val < 2 ^ Int64.wordsize :=
    Nat.lt_of_lt_of_le hlo hpowle
  rw [Nat.mod_eq_of_lt hhi64, Nat.mod_eq_of_lt hlo64]
  have hprod : hi.val * 2 ^ 32 < 2 ^ Int64.wordsize := by
    change hi.val * 2 ^ 32 < 2 ^ 64
    change hi.val < 2 ^ 32 at hhi
    omega
  rw [Nat.mod_eq_of_lt hprod]
  change ((hi.val * 2 ^ 32) ||| lo.val) %
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize = lo.val
  rw [Nat.or_mod_two_pow]
  change (hi.val * 2 ^ 32) % 2 ^ 32 ||| lo.val % 2 ^ 32 = lo.val
  change lo.val < 2 ^ 32 at hlo
  rw [Nat.mul_comm, Nat.mul_mod_right, Nat.mod_eq_of_lt hlo, Nat.zero_or]

theorem val_loword_longofwords : val_loword_longofwordsStatement := by
  intro v1 v2
  cases v1 with
  | Vundef =>
      exact Val.lessdef_undef _
  | Vint hi =>
      cases v2 with
      | Vint lo =>
          change Val.lessdef
            (val.Vint (Int64.loword (Int64.ofwords hi lo))) (val.Vint lo)
          rw [ap_lo_ofwords hi lo]
          exact Val.lessdef_refl _
      | _ =>
          exact Val.lessdef_undef _
  | Vlong _ =>
      exact Val.lessdef_undef _
  | Vfloat _ =>
      exact Val.lessdef_undef _
  | Vsingle _ =>
      exact Val.lessdef_undef _
  | Vptr _ _ =>
      exact Val.lessdef_undef _

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations

theorem compat_left_sound : compat_left_soundStatement := by
  intro r l e q hcompat hq hreg
  unfold compat_left at hcompat
  have hiff := EqSet.for_all_between_iff_proof
    (fun q : EqSet.elt =>
      match q.ekind with
      | .Full => decide (l = q.eloc)
      | _ => false)
    (select_reg_l r) (select_reg_h r)
    (by
      intro q₁ q₂ hqeq
      cases hqeq
      rfl)
    (select_reg_l_monotone r) (select_reg_h_monotone r) e.eqs1
  have hsel := (select_reg_charact r q).2 hreg
  have hp := hiff.mp hcompat q hq hsel.1 hsel.2
  cases hkind : q.ekind with
  | Full =>
      constructor
      · rfl
      · have hl : l = q.eloc :=
          of_decide_eq_true (by simpa [hkind] using hp)
        exact hl.symm
  | Low =>
      simp [hkind] at hp
  | High =>
      simp [hkind] at hp

theorem compat_left2_sound : compat_left2_soundStatement := by
  intro r l1 l2 e q hcompat hq hreg
  unfold compat_left2 at hcompat
  have hiff := EqSet.for_all_between_iff_proof
    (fun q : EqSet.elt =>
      match q.ekind with
      | .High => decide (l1 = q.eloc)
      | .Low => decide (l2 = q.eloc)
      | .Full => false)
    (select_reg_l r) (select_reg_h r)
    (by
      intro q₁ q₂ hqeq
      cases hqeq
      rfl)
    (select_reg_l_monotone r) (select_reg_h_monotone r) e.eqs1
  have hsel := (select_reg_charact r q).2 hreg
  have hp := hiff.mp hcompat q hq hsel.1 hsel.2
  cases hkind : q.ekind with
  | Full =>
      simp [hkind] at hp
  | Low =>
      right
      constructor
      · rfl
      · have hl : l2 = q.eloc :=
          of_decide_eq_true (by simpa [hkind] using hp)
        exact hl.symm
  | High =>
      left
      constructor
      · rfl
      · have hl : l1 = q.eloc :=
          of_decide_eq_true (by simpa [hkind] using hp)
        exact hl.symm

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

private theorem ap_lessdef_trans {v1 v2 v3 : val}
    (h12 : Val.lessdef v1 v2) (h23 : Val.lessdef v2 v3) :
    Val.lessdef v1 v3 := by
  cases h12 with
  | lessdef_refl => exact h23
  | lessdef_undef => exact Val.lessdef_undef _

private theorem ap_loword_lessdef {v1 v2 : val}
    (h : Val.lessdef v1 v2) :
    Val.lessdef (Val.loword v1) (Val.loword v2) := by
  cases h with
  | lessdef_refl => exact Val.lessdef_refl _
  | lessdef_undef => exact Val.lessdef_undef _

private theorem ap_hiword_lessdef {v1 v2 : val}
    (h : Val.lessdef v1 v2) :
    Val.lessdef (Val.hiword v1) (Val.hiword v2) := by
  cases h with
  | lessdef_refl => exact Val.lessdef_refl _
  | lessdef_undef => exact Val.lessdef_undef _

theorem function_return_satisf : function_return_satisfStatement := by
  intro cfg rs lsBefore lsAfter resultReg resultLoc sg e e' v
  intro _ hremove hsat huncon hno hv hagree
  cases resultLoc with
  | One mr =>
      have he' : e' = remove_equation
          { ekind := .Full, ereg := resultReg, eloc := .R mr } e := by
        simpa [remove_equations_res] using hremove.symm
      subst e'
      have huncon' : reg_loc_unconstrained resultReg (R mr)
          (remove_equation
            { ekind := .Full, ereg := resultReg, eloc := .R mr } e) = true := by
        simpa [regs_of_rpair] using huncon
      unfold satisf
      intro q hq
      let q0 : equation :=
        { ekind := .Full, ereg := resultReg, eloc := .R mr }
      by_cases heq : q = q0
      · subst q
        have hget : Regmap.get resultReg (Regmap.set resultReg v rs) = v :=
          Regmap.gss_proof val resultReg v rs
        change Val.lessdef
          (Regmap.get resultReg (Regmap.set resultReg v rs)) (lsAfter (R mr))
        rw [hget]
        simpa [map_rpair, Locmap.getpair] using hv
      · have hqrem : EqSet.In q (remove_equation q0 e).eqs1 := by
          unfold remove_equation
          apply EqSet.remove_2 e.eqs1 q0 q
          · intro h
            exact heq h.symm
          · exact hq
        have hreg : q.ereg ≠ resultReg :=
          (reg_loc_unconstrained_sound resultReg (R mr)
            (remove_equation q0 e) q (by simpa [q0] using huncon') hqrem).1
        rw [Regmap.gso_proof val q.ereg resultReg v rs hreg]
        have hcallee := no_caller_saves_sound cfg
          (remove_equation q0 e) q (by simpa [q0] using hno) hqrem
        rw [← hagree q.eloc hcallee]
        exact hsat q (by simpa [q0] using hqrem)
  | Twolong hi lo =>
      by_cases hsame : lo = hi
      · subst lo
        simp [remove_equations_res] at hremove
      · have he' : e' =
            remove_equation
              { ekind := .Low, ereg := resultReg, eloc := .R lo }
              (remove_equation
                { ekind := .High, ereg := resultReg, eloc := .R hi } e) := by
          simpa [remove_equations_res, hsame] using hremove.symm
        subst e'
        have huncon' :
            reg_loc_unconstrained resultReg (R hi)
                (remove_equation
                  { ekind := .Low, ereg := resultReg, eloc := .R lo }
                  (remove_equation
                    { ekind := .High, ereg := resultReg, eloc := .R hi } e)) = true ∧
              reg_loc_unconstrained resultReg (R lo)
                (remove_equation
                  { ekind := .Low, ereg := resultReg, eloc := .R lo }
                  (remove_equation
                    { ekind := .High, ereg := resultReg, eloc := .R hi } e)) = true := by
          simpa [regs_of_rpair] using huncon
        unfold satisf
        intro q hq
        let qlo : equation :=
          { ekind := .Low, ereg := resultReg, eloc := .R lo }
        let qhi : equation :=
          { ekind := .High, ereg := resultReg, eloc := .R hi }
        by_cases heqlo : q = qlo
        · subst q
          have hld := ap_lessdef_trans (ap_loword_lessdef hv)
            (val_loword_longofwords (lsAfter (R hi)) (lsAfter (R lo)))
          have hget : Regmap.get resultReg (Regmap.set resultReg v rs) = v :=
            Regmap.gss_proof val resultReg v rs
          change Val.lessdef
            (Val.loword (Regmap.get resultReg (Regmap.set resultReg v rs)))
            (lsAfter (R lo))
          rw [hget]
          exact hld
        · by_cases heqhi : q = qhi
          · subst q
            have hld := ap_lessdef_trans (ap_hiword_lessdef hv)
              (val_hiword_longofwords (lsAfter (R hi)) (lsAfter (R lo)))
            have hget : Regmap.get resultReg (Regmap.set resultReg v rs) = v :=
              Regmap.gss_proof val resultReg v rs
            change Val.lessdef
              (Val.hiword (Regmap.get resultReg (Regmap.set resultReg v rs)))
              (lsAfter (R hi))
            rw [hget]
            exact hld
          · have hqrem : EqSet.In q
                (remove_equation qlo (remove_equation qhi e)).eqs1 := by
              unfold remove_equation
              apply EqSet.remove_2 (remove_equation qhi e).eqs1 qlo q
              · intro h
                exact heqlo h.symm
              · unfold remove_equation
                apply EqSet.remove_2 e.eqs1 qhi q
                · intro h
                  exact heqhi h.symm
                · exact hq
            have hreg : q.ereg ≠ resultReg :=
              (reg_loc_unconstrained_sound resultReg (R hi)
                (remove_equation qlo (remove_equation qhi e)) q
                (by simpa [qlo, qhi] using huncon'.1) hqrem).1
            rw [Regmap.gso_proof val q.ereg resultReg v rs hreg]
            have hcallee := no_caller_saves_sound cfg
              (remove_equation qlo (remove_equation qhi e)) q
              (by simpa [qlo, qhi] using hno) hqrem
            rw [← hagree q.eloc hcallee]
            exact hsat q (by simpa [qlo, qhi] using hqrem)

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

theorem find_function_tailcall : find_function_tailcallStatement := by
  intro cfg tge ros ls1 ls2 hcompat
  unfold ros_compatible_tailcall at hcompat
  cases ros with
  | inl r =>
      have hsave : CompCert4Lean.X86.Conventions1.is_callee_save cfg r = false := by
        simpa using hcompat
      simp [LTL.find_function, return_regs, hsave]
  | inr id =>
      rfl

private theorem ap_call_regs_parameter_loc
    (cfg : CompCert4Lean.Config.CompilerConfig) (sg : signature)
    (ls : LTL.locset) (l : loc)
    (hl : l ∈ regs_of_rpairs
      (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg)) :
    LTL.call_regs ls (parameter_of_argument l) = ls l := by
  have hacc := loc_arguments_acceptable_2 cfg sg l hl
  cases l with
  | R r => rfl
  | S sl ofs ty =>
      cases sl with
      | Local =>
          simp [CompCert4Lean.X86.Conventions1.loc_argument_acceptable] at hacc
      | Incoming =>
          simp [CompCert4Lean.X86.Conventions1.loc_argument_acceptable] at hacc
      | Outgoing => rfl

theorem call_regs_param_values : call_regs_param_valuesStatement := by
  intro cfg sg ls
  unfold loc_parameters
  simp only [List.map_map]
  apply CompCert4Lean.Lib.Coqlib.list_map_exten
  intro p hp
  cases p with
  | One l =>
      change ls l = LTL.call_regs ls (parameter_of_argument l)
      apply (ap_call_regs_parameter_loc cfg sg ls l _).symm
      exact in_regs_of_rpairs loc l (One l) (by simp [regs_of_rpair])
        (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg) hp
  | Twolong hi lo =>
      simp only [Function.comp_apply, map_rpair, Locmap.getpair]
      rw [ap_call_regs_parameter_loc cfg sg ls hi,
        ap_call_regs_parameter_loc cfg sg ls lo]
      · exact in_regs_of_rpairs loc lo (Twolong hi lo)
          (by simp [regs_of_rpair])
          (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg) hp
      · exact in_regs_of_rpairs loc hi (Twolong hi lo)
          (by simp [regs_of_rpair])
          (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg) hp

private theorem ap_return_regs_argument_loc
    (cfg : CompCert4Lean.Config.CompilerConfig) (sg : signature)
    (ls1 ls2 : LTL.locset)
    (hpossible : tailcall_is_possible cfg sg = true)
    (l : loc) (hl : l ∈ regs_of_rpairs
      (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg)) :
    LTL.return_regs cfg ls1 ls2 l = ls2 l := by
  have htail := tailcall_is_possible_correct cfg sg hpossible l hl
  have hacc := loc_arguments_acceptable_2 cfg sg l hl
  cases l with
  | R r =>
      change CompCert4Lean.X86.Conventions1.is_callee_save cfg r = false at hacc
      change (if CompCert4Lean.X86.Conventions1.is_callee_save cfg r = true then
          ls1 (R r) else ls2 (R r)) = ls2 (R r)
      simp [hacc]
  | S sl ofs ty =>
      simp at htail

theorem return_regs_arg_values : return_regs_arg_valuesStatement := by
  intro cfg sg ls1 ls2 hpossible
  apply CompCert4Lean.Lib.Coqlib.list_map_exten
  intro p hp
  cases p with
  | One l =>
      change ls2 l = LTL.return_regs cfg ls1 ls2 l
      apply (ap_return_regs_argument_loc cfg sg ls1 ls2 hpossible l _).symm
      exact in_regs_of_rpairs loc l (One l) (by simp [regs_of_rpair])
        (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg) hp
  | Twolong hi lo =>
      simp only [Locmap.getpair]
      rw [ap_return_regs_argument_loc cfg sg ls1 ls2 hpossible hi,
        ap_return_regs_argument_loc cfg sg ls1 ls2 hpossible lo]
      · exact in_regs_of_rpairs loc lo (Twolong hi lo)
          (by simp [regs_of_rpair])
          (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg) hp
      · exact in_regs_of_rpairs loc hi (Twolong hi lo)
          (by simp [regs_of_rpair])
          (CompCert4Lean.X86.Conventions1.loc_arguments cfg sg) hp

private theorem ap_rtl_gss (r : reg) (v : val) (rs : RTL.regset) :
    Regmap.get r (Regmap.set r v rs) = v := by
  change Regmap.t val at rs
  exact Regmap.gss_proof val r v rs

private theorem ap_rtl_gso (i j : reg) (v : val) (rs : RTL.regset)
    (hij : i ≠ j) :
    Regmap.get i (Regmap.set j v rs) = Regmap.get i rs := by
  change Regmap.t val at rs
  exact Regmap.gso_proof val i j v rs hij

theorem compat_entry_satisf : compat_entry_satisfStatement := by
  intro rl
  induction rl with
  | nil =>
      intro ll e hcomp vl ls hvl
      cases ll with
      | nil =>
          cases vl with
          | nil =>
              unfold satisf
              intro q hq
              change equation at q
              rw [show Regmap.get q.ereg (RTL.init_regs [] []) = Vundef by
                exact Regmap.gi_proof val q.ereg Vundef]
              cases q.ekind <;> exact Val.lessdef_undef _
          | cons v vs =>
              cases hvl
      | cons p ps =>
          simp [compat_entry] at hcomp
  | cons r rs ih =>
      intro ll e hcomp vl ls hvl
      cases ll with
      | nil =>
          simp [compat_entry] at hcomp
      | cons p ps =>
          cases p with
          | One l =>
              simp only [compat_entry, Bool.and_eq_true] at hcomp
              rcases hcomp with ⟨hleft, htail⟩
              cases vl with
              | nil => cases hvl
              | cons v vs =>
                  cases hvl with
                  | lessdef_list_cons _ _ _ _ hv hvs =>
                      unfold satisf
                      intro q hq
                      change equation at q
                      change Val.lessdef
                        (sel_val q.ekind
                          (Regmap.get q.ereg
                            (Regmap.set r v (RTL.init_regs vs rs))))
                        (ls q.eloc)
                      by_cases heq : q.ereg = r
                      · rw [heq, ap_rtl_gss]
                        have hc := compat_left_sound r l e q hleft hq heq
                        rcases hc with ⟨hk, hl⟩
                        rw [hk, hl]
                        exact hv
                      · rw [ap_rtl_gso q.ereg r v (RTL.init_regs vs rs) heq]
                        exact ih ps e htail vs ls hvs q hq
          | Twolong hi lo =>
              simp only [compat_entry, Bool.and_eq_true] at hcomp
              rcases hcomp with ⟨hleft, htail⟩
              cases vl with
              | nil => cases hvl
              | cons v vs =>
                  cases hvl with
                  | lessdef_list_cons _ _ _ _ hv hvs =>
                      unfold satisf
                      intro q hq
                      change equation at q
                      change Val.lessdef
                        (sel_val q.ekind
                          (Regmap.get q.ereg
                            (Regmap.set r v (RTL.init_regs vs rs))))
                        (ls q.eloc)
                      by_cases heq : q.ereg = r
                      · rw [heq, ap_rtl_gss]
                        have hc := compat_left2_sound r hi lo e q hleft hq heq
                        apply Or.elim hc
                        · intro hcHigh
                          rw [hcHigh.1, hcHigh.2]
                          have hld := ap_lessdef_trans (ap_hiword_lessdef hv)
                            (val_hiword_longofwords (ls hi) (ls lo))
                          simpa [sel_val] using hld
                        · intro hcLow
                          rw [hcLow.1, hcLow.2]
                          have hld := ap_lessdef_trans (ap_loword_lessdef hv)
                            (val_loword_longofwords (ls hi) (ls lo))
                          simpa [sel_val] using hld
                      · rw [ap_rtl_gso q.ereg r v (RTL.init_regs vs rs) heq]
                        exact ih ps e htail vs ls hvs q hq

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

theorem loadv_int64_split : loadv_int64_splitStatement := by
  intro m a v hload hsplit
  simp [CompCert4Lean.X86_64.Archi.splitlong,
    CompCert4Lean.X86_64.Archi.ptr64] at hsplit

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events

theorem add_equations_builtin_arg_satisf :
    add_equations_builtin_arg_satisfStatement := by
  intro env rs ls arg arg' e e' hrun hsat
  induction arg generalizing arg' e e' with
  | BA r =>
      cases arg' with
      | BA l =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨rfl, rfl⟩
          exact add_equation_satisf rs ls _ _ hsat
      | BA_splitlong hi lo =>
          cases hi with
          | BA hi =>
              cases lo with
              | BA lo =>
                  change (if decide (env r = Tlong) &&
                      CompCert4Lean.X86_64.Archi.splitlong then
                    some (add_equation { ekind := .Low, ereg := r, eloc := lo }
                      (add_equation { ekind := .High, ereg := r, eloc := hi } e))
                  else none) = some e' at hrun
                  split at hrun
                  · cases hrun
                    exact add_equation_satisf rs ls _ _
                      (add_equation_satisf rs ls _ _ hsat)
                  · cases hrun
              | _ => simp [add_equations_builtin_arg] at hrun
          | _ => simp [add_equations_builtin_arg] at hrun
      | BA_int n' => simp [add_equations_builtin_arg] at hrun
      | BA_long n' => simp [add_equations_builtin_arg] at hrun
      | BA_float f' => simp [add_equations_builtin_arg] at hrun
      | BA_single f' => simp [add_equations_builtin_arg] at hrun
      | BA_loadstack chunk' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addrstack ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_loadglobal chunk' id' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addrglobal id' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addptr a1' a2' => simp [add_equations_builtin_arg] at hrun
  | BA_int n =>
      cases arg' with
      | BA l => simp [add_equations_builtin_arg] at hrun
      | BA_splitlong hi lo => simp [add_equations_builtin_arg] at hrun
      | BA_int n' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨_, rfl⟩
          exact hsat
      | BA_long n' => simp [add_equations_builtin_arg] at hrun
      | BA_float f' => simp [add_equations_builtin_arg] at hrun
      | BA_single f' => simp [add_equations_builtin_arg] at hrun
      | BA_loadstack chunk' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addrstack ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_loadglobal chunk' id' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addrglobal id' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addptr a1' a2' => simp [add_equations_builtin_arg] at hrun
  | BA_long n =>
      cases arg' with
      | BA_long n' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨_, rfl⟩
          exact hsat
      | _ => simp [add_equations_builtin_arg] at hrun
  | BA_float n =>
      cases arg' with
      | BA_float f' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨_, rfl⟩
          exact hsat
      | _ => simp [add_equations_builtin_arg] at hrun
  | BA_single n =>
      cases arg' with
      | BA_single f' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨_, rfl⟩
          exact hsat
      | _ => simp [add_equations_builtin_arg] at hrun
  | BA_loadstack chunk ofs =>
      cases arg' with
      | BA_loadstack chunk' ofs' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨_, rfl⟩
          exact hsat
      | _ => simp [add_equations_builtin_arg] at hrun
  | BA_addrstack ofs =>
      cases arg' with
      | BA_addrstack ofs' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨_, rfl⟩
          exact hsat
      | _ => simp [add_equations_builtin_arg] at hrun
  | BA_loadglobal chunk id ofs =>
      cases arg' with
      | BA_loadglobal chunk' id' ofs' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨_, rfl⟩
          exact hsat
      | _ => simp [add_equations_builtin_arg] at hrun
  | BA_addrglobal id ofs =>
      cases arg' with
      | BA_addrglobal id' ofs' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨_, rfl⟩
          exact hsat
      | _ => simp [add_equations_builtin_arg] at hrun
  | BA_splitlong hi lo ih_hi ih_lo =>
      cases arg' with
      | BA l => simp [add_equations_builtin_arg] at hrun
      | BA_splitlong hi' lo' =>
          change (match add_equations_builtin_arg env hi hi' e with
            | none => none
            | some e1 => add_equations_builtin_arg env lo lo' e1) = some e' at hrun
          split at hrun
          · cases hrun
          · rename_i e1 hfirst
            exact ih_hi hi' e e1 hfirst (ih_lo lo' e1 e' hrun hsat)
      | BA_int n' => simp [add_equations_builtin_arg] at hrun
      | BA_long n' => simp [add_equations_builtin_arg] at hrun
      | BA_float f' => simp [add_equations_builtin_arg] at hrun
      | BA_single f' => simp [add_equations_builtin_arg] at hrun
      | BA_loadstack chunk' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addrstack ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_loadglobal chunk' id' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addrglobal id' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addptr a1' a2' => simp [add_equations_builtin_arg] at hrun
  | BA_addptr a1 a2 ih_a1 ih_a2 =>
      cases arg' with
      | BA l => simp [add_equations_builtin_arg] at hrun
      | BA_splitlong hi lo => simp [add_equations_builtin_arg] at hrun
      | BA_int n' => simp [add_equations_builtin_arg] at hrun
      | BA_long n' => simp [add_equations_builtin_arg] at hrun
      | BA_float f' => simp [add_equations_builtin_arg] at hrun
      | BA_single f' => simp [add_equations_builtin_arg] at hrun
      | BA_loadstack chunk' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addrstack ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_loadglobal chunk' id' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addrglobal id' ofs' => simp [add_equations_builtin_arg] at hrun
      | BA_addptr a1' a2' =>
          change (match add_equations_builtin_arg env a1 a1' e with
            | none => none
            | some e1 => add_equations_builtin_arg env a2 a2' e1) = some e' at hrun
          split at hrun
          · cases hrun
          · rename_i e1 hfirst
            exact ih_a1 a1' e e1 hfirst (ih_a2 a2' e1 e' hrun hsat)

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values

/- deferred lessdef proof -/
/-
  intro env ge sp rs ls m arg v hEval
  induction hEval with
  | eval_BA x =>
      intro e e' arg' hrun hsat hwt
      cases arg' <;> simp [add_equations_builtin_arg] at hrun
  | eval_BA_int n =>
      intro e e' arg' hrun hsat hwt
      cases arg' <;> simp [add_equations_builtin_arg] at hrun
  | eval_BA_long n =>
      intro e e' arg' hrun hsat hwt
      cases arg' <;> simp [add_equations_builtin_arg] at hrun
  | eval_BA_float n =>
      intro e e' arg' hrun hsat hwt
      cases arg' <;> simp [add_equations_builtin_arg] at hrun
  | eval_BA_single n =>
      intro e e' arg' hrun hsat hwt
      cases arg' <;> simp [add_equations_builtin_arg] at hrun
  | eval_BA_loadstack chunk ofs v hload =>
      intro e e' arg' hrun hsat hwt
      cases arg' <;> simp [add_equations_builtin_arg] at hrun
  | eval_BA_addrstack ofs =>
      intro e e' arg' hrun hsat hwt
      cases arg' <;> simp [add_equations_builtin_arg] at hrun
  | eval_BA_loadglobal chunk id ofs v hload =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_loadglobal chunk' id' ofs' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨⟨hchunk, hid⟩, hofs, rfl⟩
          have hc : chunk = chunk' := (of_decide_eq_true hchunk)
          have hi : id = id' := (of_decide_eq_true hid)
          have ho : ofs = ofs' := by
            unfold CompCert4Lean.Lib.Integers.Ptrofs.eq WordCore.eq at hofs
            apply WordCore.ext
            exact of_decide_eq_true hofs
          subst hc; subst hi; subst ho
          exact ⟨v, eval_BA_loadglobal _ _ _ _ hload, Val.lessdef_refl _⟩
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_addrglobal id ofs =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_addrglobal id' ofs' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨⟨hid, hofs⟩, rfl⟩
          have hi : id = id' := (of_decide_eq_true hid)
          have ho : ofs = ofs' := by
            unfold CompCert4Lean.Lib.Integers.Ptrofs.eq WordCore.eq at hofs
            apply WordCore.ext
            exact of_decide_eq_true hofs
          subst hi; subst ho
          exact ⟨_, eval_BA_addrglobal _ _, Val.lessdef_refl _⟩
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_splitlong hi' lo' =>
          change (match add_equations_builtin_arg env hi hi' e with
            | none => none
            | some e1 => add_equations_builtin_arg env lo lo' e1) = some e' at hrun
          split at hrun
          · cases hrun
          · rename_i e1 hfirst
            obtain ⟨vhi', hhi', ldhi⟩ := ihhi e e1 hi' hfirst hsat hwt
            obtain ⟨vlo', hlo', ldlo⟩ := ihlo e1 e' lo' hrun hsat hwt
            exact ⟨Val.longofwords vhi' vlo',
              eval_BA_splitlong _ _ _ _ hhi' hlo',
              allocproof_longofwords_lessdef _ _ _ _ ldhi ldlo⟩
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_addptr a1 a2 v1 v2 ha1 ha2 iha1 iha2 =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_addptr a1' a2' =>
          change (match add_equations_builtin_arg env a1 a1' e with
            | none => none
            | some e1 => add_equations_builtin_arg env a2 a2' e1) = some e' at hrun
          split at hrun
          · cases hrun
          · rename_i e1 hfirst
            obtain ⟨v1', h1', ld1⟩ := iha1 e e1 a1' hfirst hsat hwt
            obtain ⟨v2', h2', ld2⟩ := iha2 e1 e' a2' hrun hsat hwt
            refine ⟨(if CompCert4Lean.X86_64.Archi.ptr64 then Val.addl v1' v2' else Val.add v1' v2'),
              eval_BA_addptr _ _ _ _ h1' h2', ?_⟩
            cases CompCert4Lean.X86_64.Archi.ptr64 <;>
              first | exact Val.lessdef_refl _ | exact Val.lessdef_refl _
      | _ => simp [add_equations_builtin_arg] at hrun

end CompCert4Lean.Backend.Allocproof
-/

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST

theorem add_equations_builtin_args_satisf :
    add_equations_builtin_args_satisfStatement := by
  intro env rs ls args args' e e' hrun hsat
  induction args generalizing args' e e' with
  | nil =>
      cases args' with
      | nil =>
          simp [add_equations_builtin_args] at hrun
          cases hrun
          exact hsat
      | cons a' rest => simp [add_equations_builtin_args] at hrun
  | cons a rest ih =>
      cases args' with
      | nil => simp [add_equations_builtin_args] at hrun
      | cons a' rest' =>
          change (match add_equations_builtin_arg env a a' e with
            | none => none
            | some e1 => add_equations_builtin_args env rest rest' e1) = some e' at hrun
          split at hrun
          · cases hrun
          · rename_i e1 hfirst
            exact add_equations_builtin_arg_satisf env rs ls a a' e e1 hfirst
              (ih rest' e1 e' hrun hsat)

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values

private theorem pgo_cdbe_int_eq_true
    (x y : CompCert4Lean.Lib.Integers.int)
    (h : CompCert4Lean.Lib.Integers.Int.eq x y = true) : x = y := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (x.intval = y.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem pgo_cdbe_int64_eq_true
    (x y : CompCert4Lean.Lib.Integers.int64)
    (h : CompCert4Lean.Lib.Integers.Int64.eq x y = true) : x = y := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (x.intval = y.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int64.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem pgo_cdbe_add_lessdef (v1 v1' v2 v2' : val)
    (h1 : Val.lessdef v1 v1') (h2 : Val.lessdef v2 v2') :
    Val.lessdef (Val.add v1 v2) (Val.add v1' v2') := by
  cases h1 with
  | lessdef_refl v1 =>
      cases h2 with
      | lessdef_refl v2 => exact Val.lessdef_refl _
      | lessdef_undef v2' =>
          simpa [Val.add] using (Val.lessdef_undef (Val.add v1 v2'))
  | lessdef_undef v1' =>
      simpa [Val.add] using (Val.lessdef_undef (Val.add v1' v2'))

private theorem pgo_cdbe_addl_lessdef (v1 v1' v2 v2' : val)
    (h1 : Val.lessdef v1 v1') (h2 : Val.lessdef v2 v2') :
    Val.lessdef (Val.addl v1 v2) (Val.addl v1' v2') := by
  cases h1 with
  | lessdef_refl v1 =>
      cases h2 with
      | lessdef_refl v2 => exact Val.lessdef_refl _
      | lessdef_undef v2' =>
          simpa [Val.addl] using (Val.lessdef_undef (Val.addl v1 v2'))
  | lessdef_undef v1' =>
      simpa [Val.addl] using (Val.lessdef_undef (Val.addl v1' v2'))

theorem add_equations_builtin_arg_lessdef :
    add_equations_builtin_arg_lessdefStatement := by
  intro env ge sp rs ls m arg v hEval
  induction hEval with
  | eval_BA r =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA l =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨rfl, rfl⟩
          exact ⟨ls l, eval_BA l, add_equation_lessdef rs ls _ _ hsat⟩
      | BA_splitlong hi lo =>
          cases hi with
          | BA hi =>
              cases lo with
              | BA lo =>
                  simp [add_equations_builtin_arg,
                    CompCert4Lean.X86_64.Archi.splitlong,
                    CompCert4Lean.X86_64.Archi.ptr64] at hrun
              | _ => simp [add_equations_builtin_arg] at hrun
          | _ => simp [add_equations_builtin_arg] at hrun
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_int n =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_int n' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨heq, rfl⟩
          have hn : n = n' := pgo_cdbe_int_eq_true n n' heq
          cases hn
          exact ⟨Vint n, eval_BA_int n, Val.lessdef_refl _⟩
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_long n =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_long n' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨heq, rfl⟩
          have hn : n = n' := pgo_cdbe_int64_eq_true n n' heq
          cases hn
          exact ⟨Vlong n, eval_BA_long n, Val.lessdef_refl _⟩
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_float n =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_float n' =>
          cases heq : CompCert4Lean.Lib.Floats.Float.eq_dec n n' with
          | left h =>
              cases h
              simp [add_equations_builtin_arg, heq] at hrun
              cases hrun
              exact ⟨Vfloat n, eval_BA_float n, Val.lessdef_refl _⟩
          | right h =>
              simp [add_equations_builtin_arg, heq] at hrun
              cases hrun.1
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_single n =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_single n' =>
          cases heq : CompCert4Lean.Lib.Floats.Float32.eq_dec n n' with
          | left h =>
              cases h
              simp [add_equations_builtin_arg, heq] at hrun
              cases hrun
              exact ⟨Vsingle n, eval_BA_single n, Val.lessdef_refl _⟩
          | right h =>
              simp [add_equations_builtin_arg, heq] at hrun
              cases hrun.1
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_loadstack chunk ofs v hload =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_loadstack chunk' ofs' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨⟨hchunk, hofs⟩, rfl⟩
          have ho : ofs = ofs' := by
            unfold CompCert4Lean.Lib.Integers.Ptrofs.eq
              CompCert4Lean.Lib.Integers.WordCore.eq at hofs
            apply CompCert4Lean.Lib.Integers.WordCore.ext
            exact of_decide_eq_true hofs
          cases hdec : chunk_eq chunk chunk' with
          | left hc =>
              cases hc
              cases ho
              exact ⟨v, eval_BA_loadstack _ _ _ hload, Val.lessdef_refl _⟩
          | right hc =>
              rw [hdec] at hchunk
              cases hchunk
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_addrstack ofs =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_addrstack ofs' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨hofs, rfl⟩
          have ho : ofs = ofs' := by
            unfold CompCert4Lean.Lib.Integers.Ptrofs.eq
              CompCert4Lean.Lib.Integers.WordCore.eq at hofs
            apply CompCert4Lean.Lib.Integers.WordCore.ext
            exact of_decide_eq_true hofs
          cases ho
          exact ⟨_, eval_BA_addrstack _, Val.lessdef_refl _⟩
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_loadglobal chunk id ofs v hload =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_loadglobal chunk' id' ofs' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨⟨⟨hchunk, hid⟩, hofs⟩, rfl⟩
          have ho : ofs = ofs' := by
            unfold CompCert4Lean.Lib.Integers.Ptrofs.eq
              CompCert4Lean.Lib.Integers.WordCore.eq at hofs
            apply CompCert4Lean.Lib.Integers.WordCore.ext
            exact of_decide_eq_true hofs
          cases hchunkDec : chunk_eq chunk chunk' with
          | left hc =>
              cases hc
              cases hidDec : ident_eq id id' with
              | left hi =>
                  cases hi
                  cases ho
                  exact ⟨v, eval_BA_loadglobal _ _ _ _ hload, Val.lessdef_refl _⟩
              | right hi =>
                  rw [hidDec] at hid
                  cases hid
          | right hc =>
              rw [hchunkDec] at hchunk
              cases hchunk
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_addrglobal id ofs =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_addrglobal id' ofs' =>
          simp [add_equations_builtin_arg] at hrun
          rcases hrun with ⟨⟨hid, hofs⟩, rfl⟩
          have ho : ofs = ofs' := by
            unfold CompCert4Lean.Lib.Integers.Ptrofs.eq
              CompCert4Lean.Lib.Integers.WordCore.eq at hofs
            apply CompCert4Lean.Lib.Integers.WordCore.ext
            exact of_decide_eq_true hofs
          cases hidDec : ident_eq id id' with
          | left hi =>
              cases hi
              cases ho
              exact ⟨_, eval_BA_addrglobal _ _, Val.lessdef_refl _⟩
          | right hi =>
              rw [hidDec] at hid
              cases hid
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_splitlong hi' lo' =>
          change (match add_equations_builtin_arg env hi hi' e with
            | none => none
            | some e1 => add_equations_builtin_arg env lo lo' e1) = some e' at hrun
          split at hrun
          · cases hrun
          · rename_i e1 hfirst
            have hsat1 : satisf rs ls e1 :=
              add_equations_builtin_arg_satisf env rs ls lo lo' e1 e' hrun hsat
            obtain ⟨vhi', hhi', ldhi⟩ := ihhi e e1 hi' hfirst hsat1 hwt
            obtain ⟨vlo', hlo', ldlo⟩ := ihlo e1 e' lo' hrun hsat hwt
            exact ⟨Val.longofwords vhi' vlo',
              eval_BA_splitlong _ _ _ _ hhi' hlo',
              allocproof_longofwords_lessdef _ _ _ _ ldhi ldlo⟩
      | _ => simp [add_equations_builtin_arg] at hrun
  | eval_BA_addptr a1 a2 v1 v2 ha1 ha2 iha1 iha2 =>
      intro e e' arg' hrun hsat hwt
      cases arg' with
      | BA_addptr a1' a2' =>
          change (match add_equations_builtin_arg env a1 a1' e with
            | none => none
            | some e1 => add_equations_builtin_arg env a2 a2' e1) = some e' at hrun
          split at hrun
          · cases hrun
          · rename_i e1 hfirst
            have hsat1 : satisf rs ls e1 :=
              add_equations_builtin_arg_satisf env rs ls a2 a2' e1 e' hrun hsat
            obtain ⟨v1', h1', ld1⟩ := iha1 e e1 a1' hfirst hsat1 hwt
            obtain ⟨v2', h2', ld2⟩ := iha2 e1 e' a2' hrun hsat hwt
            refine ⟨(if CompCert4Lean.X86_64.Archi.ptr64 then
                Val.addl v1' v2' else Val.add v1' v2'),
              eval_BA_addptr _ _ _ _ h1' h2', ?_⟩
            cases hptr : CompCert4Lean.X86_64.Archi.ptr64 with
            | false => exact pgo_cdbe_add_lessdef _ _ _ _ ld1 ld2
            | true => exact pgo_cdbe_addl_lessdef _ _ _ _ ld1 ld2
      | _ => simp [add_equations_builtin_arg] at hrun

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Integers.Ptrofs
open Lean Elab Tactic Meta

private def pgo_memdataPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Common") "Memdata"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem pgo_ptrofs_add_zero
    (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add ofs
      (CompCert4Lean.Lib.Integers.Ptrofs.repr (.Z0 : Z)) = ofs := by
  run_tac
    let lctx ← getLCtx
    let ofsF := (lctx.findFromUserName? `ofs).get!
    let e ← mkAppM
      (pgo_memdataPrivateName "CompCert4Lean.Common.Memdata.memdata_ptrofs_add_zero")
      #[mkFVar ofsF.fvarId]
    closeMainGoal Name.anonymous e

private theorem pgo_zadd_zero (x : Z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add x (.Z0) = x := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x + 0)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp

private theorem pgo_val_inject_lessdef (v v' : val) :
    Val.inject CompCert4Lean.Common.Values.inject_id v v' → Val.lessdef v v' := by
  intro h
  cases h with
  | inject_int n => exact Val.lessdef_refl _
  | inject_long n => exact Val.lessdef_refl _
  | inject_float n => exact Val.lessdef_refl _
  | inject_single n => exact Val.lessdef_refl _
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      rcases hpair with ⟨rfl, rfl⟩
      have hz0 := pgo_ptrofs_add_zero ofs1
      rw [hz0] at hofs
      have hz : ofs2 = ofs1 := hofs
      cases hz
      exact Val.lessdef_refl _
  | val_inject_undef v => exact Val.lessdef_undef _

private theorem pgo_getN_memval_lessdef :
    ∀ (N : Nat) (p : Z) (c1 c2 : ZMap.t memval),
      (∀ i, ZArith.BinInt.Z.le p i ∧
          ZArith.BinInt.Z.lt i (ZArith.BinInt.Z.add p (ZArith.BinInt.Z.of_nat N)) →
        memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) →
      CompCert4Lean.Lib.Coqlib.list_forall2 memval_lessdef
        (Mem.getN N p c1) (Mem.getN N p c2) := by
  intro N
  induction N with
  | zero =>
      intro p c1 c2 hN
      exact CompCert4Lean.Lib.Coqlib.list_forall2_nil _
  | succ N ih =>
      intro p c1 c2 hN
      apply CompCert4Lean.Lib.Coqlib.list_forall2.cons
      · apply hN p
        constructor
        · change intOfZ p ≤ intOfZ p
          omega
        · change intOfZ p < intOfZ
            (ZArith.BinInt.Z.add p (ZArith.BinInt.Z.of_nat (N + 1)))
          simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
          omega
      · change CompCert4Lean.Lib.Coqlib.list_forall2 memval_lessdef
          (Mem.getN N (ZArith.BinInt.Z.add p (ZArith.BinInt.Z.of_nat 1)) c1)
          (Mem.getN N (ZArith.BinInt.Z.add p (ZArith.BinInt.Z.of_nat 1)) c2)
        apply ih
        intro i hi
        apply hN i
        rcases hi with ⟨hile, hilt⟩
        constructor
        · change intOfZ p ≤ intOfZ i
          change intOfZ (ZArith.BinInt.Z.add p (ZArith.BinInt.Z.of_nat 1)) ≤
            intOfZ i at hile
          simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hile
          omega
        · change intOfZ i < intOfZ
            (ZArith.BinInt.Z.add p (ZArith.BinInt.Z.of_nat (N + 1)))
          change intOfZ i < intOfZ
            (ZArith.BinInt.Z.add
              (ZArith.BinInt.Z.add p (ZArith.BinInt.Z.of_nat 1))
              (ZArith.BinInt.Z.of_nat N)) at hilt
          simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hilt ⊢
          omega

private theorem pgo_loadv_extends
    (chunk : memory_chunk) (m tm : mem) (addr : val) (v : val)
    (hext : Mem.extends m tm) (hload : Mem.loadv chunk m addr = some v) :
    ∃ v', Mem.loadv chunk tm addr = some v' ∧ Val.lessdef v v' := by
  cases addr with
  | Vundef => simp [Mem.loadv] at hload
  | Vint n => simp [Mem.loadv] at hload
  | Vlong n => simp [Mem.loadv] at hload
  | Vfloat n => simp [Mem.loadv] at hload
  | Vsingle n => simp [Mem.loadv] at hload
  | Vptr b ofs =>
      have hvalid := Mem.load_valid_access m chunk b
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) v hload
      have hvalid' : Mem.valid_access tm chunk b
          (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) Readable := by
        constructor
        · intro i hi
          have hp := hext.mext_inj.mi_perm b b (.Z0) i Cur Readable (by rfl)
            (hvalid.1 i hi)
          simpa [pgo_zadd_zero] using hp
        · exact hvalid.2
      rcases Mem.valid_access_load tm chunk b
          (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) hvalid' with
        ⟨v', hload'⟩
      refine ⟨v', hload', ?_⟩
      rw [Mem.load_result chunk m b
          (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) v hload,
        Mem.load_result chunk tm b
          (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) v' hload']
      apply pgo_val_inject_lessdef
      apply decode_val_inject
      have hsize : ZArith.BinInt.Z.of_nat (size_chunk_nat chunk) = size_chunk chunk :=
        (size_chunk_conv chunk).symm
      apply pgo_getN_memval_lessdef
      intro i hi
      have hp := hvalid.1 i (by
        rcases hi with ⟨hilo, hihi⟩
        constructor
        · exact hilo
        · simpa [hsize] using hihi)
      have hm := hext.mext_inj.mi_memval b i b (.Z0) (by rfl) hp
      change memval_inject CompCert4Lean.Common.Values.inject_id
        (ZMap.get i (PMap.get b m.mem_contents))
        (ZMap.get i (PMap.get b tm.mem_contents))
      simpa [pgo_zadd_zero] using hm

private theorem pgo_eval_builtin_arg_extends
    {A : Type} (ge : Senv.t) (e : A → val) (sp : val) (m tm : mem)
    (hext : Mem.extends m tm) :
    ∀ (a : builtin_arg A) (v : val),
      eval_builtin_arg ge e sp m a v →
      ∃ v', eval_builtin_arg ge e sp tm a v' ∧ Val.lessdef v v' := by
  intro a v h
  induction h with
  | eval_BA x => exact ⟨e x, eval_BA x, Val.lessdef_refl _⟩
  | eval_BA_int n => exact ⟨Vint n, eval_BA_int n, Val.lessdef_refl _⟩
  | eval_BA_long n => exact ⟨Vlong n, eval_BA_long n, Val.lessdef_refl _⟩
  | eval_BA_float n => exact ⟨Vfloat n, eval_BA_float n, Val.lessdef_refl _⟩
  | eval_BA_single n => exact ⟨Vsingle n, eval_BA_single n, Val.lessdef_refl _⟩
  | eval_BA_loadstack chunk ofs v hload =>
      rcases pgo_loadv_extends chunk m tm (Val.offset_ptr sp ofs) v hext hload with
        ⟨v', hload', hld⟩
      exact ⟨v', eval_BA_loadstack _ _ _ hload', hld⟩
  | eval_BA_addrstack ofs =>
      exact ⟨Val.offset_ptr sp ofs, eval_BA_addrstack _, Val.lessdef_refl _⟩
  | eval_BA_loadglobal chunk id ofs v hload =>
      rcases pgo_loadv_extends chunk m tm (Senv.symbol_address ge id ofs) v hext hload with
        ⟨v', hload', hld⟩
      exact ⟨v', eval_BA_loadglobal _ _ _ _ hload', hld⟩
  | eval_BA_addrglobal id ofs =>
      exact ⟨Senv.symbol_address ge id ofs, eval_BA_addrglobal id ofs, Val.lessdef_refl _⟩
  | eval_BA_splitlong hi lo vhi vlo hhi hlo ihi ihlo =>
      rcases ihi with ⟨vhi', hhi', ldhi⟩
      rcases ihlo with ⟨vlo', hlo', ldlo⟩
      exact ⟨Val.longofwords vhi' vlo', eval_BA_splitlong _ _ _ _ hhi' hlo',
        allocproof_longofwords_lessdef _ _ _ _ ldhi ldlo⟩
  | eval_BA_addptr a1 a2 v1 v2 h1 h2 ih1 ih2 =>
      rcases ih1 with ⟨v1', h1', ld1⟩
      rcases ih2 with ⟨v2', h2', ld2⟩
      refine ⟨(if CompCert4Lean.X86_64.Archi.ptr64 then Val.addl v1' v2' else Val.add v1' v2'),
        eval_BA_addptr _ _ _ _ h1' h2', ?_⟩
      cases hptr : CompCert4Lean.X86_64.Archi.ptr64 with
      | false => exact pgo_cdbe_add_lessdef _ _ _ _ ld1 ld2
      | true => exact pgo_cdbe_addl_lessdef _ _ _ _ ld1 ld2

theorem add_equations_builtin_args_lessdef :
    add_equations_builtin_args_lessdefStatement := by
  intro env ge sp rs ls m tm args vl hEval
  unfold eval_builtin_args at hEval ⊢
  induction hEval with
  | nil =>
      intro args' e e' hrun hsat hwt hext
      cases args' with
      | nil =>
          simp [add_equations_builtin_args] at hrun
          cases hrun
          exact ⟨[], CompCert4Lean.Lib.Coqlib.list_forall2.nil _, Val.lessdef_list_nil⟩
      | cons arg' args' =>
          simp [add_equations_builtin_args] at hrun
  | @cons arg args v vl harg htail ih =>
      intro args' e e' hrun hsat hwt hext
      cases args' with
      | nil =>
          simp [add_equations_builtin_args] at hrun
      | cons arg' args' =>
          change (match add_equations_builtin_arg env arg arg' e with
            | none => none
            | some e1 => add_equations_builtin_args env args args' e1) = some e' at hrun
          split at hrun
          · cases hrun
          · rename_i e1 hfirst
            have hsat1 : satisf rs ls e1 :=
              add_equations_builtin_args_satisf env rs ls args args' e1 e' hrun hsat
            obtain ⟨v', harg', ld⟩ :=
              add_equations_builtin_arg_lessdef env ge sp rs ls m arg v harg
                e e1 arg' hfirst hsat1 hwt
            obtain ⟨v'', harg'', ldmem⟩ :=
              pgo_eval_builtin_arg_extends (Genv.to_senv ge) ls sp m tm hext
                arg' v' harg'
            obtain ⟨vl', htail', ldlist⟩ :=
              ih args' e1 e' hrun hsat hwt hext
            have ld' : Val.lessdef v v'' := by
              cases ld with
              | lessdef_refl => exact ldmem
              | lessdef_undef => exact Val.lessdef_undef _
            exact ⟨v'' :: vl',
              CompCert4Lean.Lib.Coqlib.list_forall2.cons _ _ harg'' htail',
              Val.lessdef_list_cons _ _ _ _ ld' ldlist⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST

theorem add_equations_debug_args_satisf :
    add_equations_debug_args_satisfStatement := by
  intro env rs ls args args' e e' hrun hsat
  induction args generalizing args' e e' with
  | nil =>
      cases args' with
      | nil =>
          simp [add_equations_debug_args] at hrun
          cases hrun
          exact hsat
      | cons a' rest =>
          simp [add_equations_debug_args] at hrun
  | cons a rest ih =>
      cases args' with
      | nil =>
          simp [add_equations_debug_args] at hrun
          rw [hrun]
          exact hsat
      | cons a' rest' =>
          change (match add_equations_builtin_arg env a a' e with
            | none => add_equations_debug_args env rest (a' :: rest') e
            | some e1 => add_equations_debug_args env rest rest' e1) = some e' at hrun
          split at hrun
          · exact ih (a' :: rest') e e' hrun hsat
          · rename_i e1 hfirst
            have hsat1 : satisf rs ls e1 :=
              ih rest' e1 e' hrun hsat
            exact add_equations_builtin_arg_satisf env rs ls a a' e e1 hfirst hsat1

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs

theorem add_equations_debug_args_eval :
    add_equations_debug_args_evalStatement := by
  intro env ge sp rs ls m tm args vl hEval
  unfold eval_builtin_args at hEval ⊢
  induction hEval with
  | nil =>
      intro args' e e' hrun hsat hwt hext
      cases args' with
      | nil =>
          exact ⟨[], CompCert4Lean.Lib.Coqlib.list_forall2.nil _⟩
      | cons arg' args' =>
          simp [add_equations_debug_args] at hrun
  | @cons arg args v vl harg htail ih =>
      intro args' e e' hrun hsat hwt hext
      cases args' with
      | nil =>
          exact ⟨[], CompCert4Lean.Lib.Coqlib.list_forall2.nil _⟩
      | cons arg' args' =>
          change (match add_equations_builtin_arg env arg arg' e with
            | none => add_equations_debug_args env args (arg' :: args') e
            | some e1 => add_equations_debug_args env args args' e1) = some e' at hrun
          split at hrun
          · exact ih (arg' :: args') e e' hrun hsat hwt hext
          · rename_i e1 hfirst
            have hsat1 : satisf rs ls e1 :=
              add_equations_debug_args_satisf env rs ls args args' e1 e' hrun hsat
            obtain ⟨v', harg', ld⟩ :=
              add_equations_builtin_arg_lessdef env ge sp rs ls m arg v harg
                e e1 arg' hfirst hsat1 hwt
            obtain ⟨v'', harg'', ldmem⟩ :=
              pgo_eval_builtin_arg_extends (Genv.to_senv ge) ls sp m tm hext
                arg' v' harg'
            obtain ⟨vl', htail'⟩ :=
              ih args' e1 e' hrun hsat hwt hext
            exact ⟨v'' :: vl',
              CompCert4Lean.Lib.Coqlib.list_forall2.cons _ _ harg'' htail'⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

theorem parallel_set_builtin_res_satisf :
    parallel_set_builtin_res_satisfStatement := by
  intro env resultReg resultLoc e0 e1 rs ls v v'
  intro hremove hreg hloc hsat hld
  cases resultReg with
  | BR r =>
      cases resultLoc with
      | BR mr =>
          have he1 : e1 = remove_equation
              { ekind := .Full, ereg := r, eloc := .R mr } e0 := by
            simpa [remove_equations_builtin_res] using hremove.symm
          subst e1
          apply parallel_assignment_satisf .Full r mr e0 rs ls v v'
          · simpa [sel_val] using hld
          · simp [params_of_builtin_res, reg_loc_unconstrained] at hreg hloc ⊢
            exact ⟨hreg, hloc⟩
          · exact hsat
      | BR_none =>
          simp [remove_equations_builtin_res] at hremove
      | BR_splitlong hiRes loRes =>
          cases hiRes with
          | BR hi =>
              cases loRes with
              | BR lo =>
                  by_cases htype : env r ≠ Tlong
                  · simp [remove_equations_builtin_res, htype] at hremove
                  · have htype' : env r = Tlong := Classical.byContradiction htype
                    by_cases hsame : hi = lo
                    · simp [remove_equations_builtin_res, htype', hsame] at hremove
                    · have he1 : e1 =
                          remove_equation
                            { ekind := .Low, ereg := r, eloc := .R lo }
                            (remove_equation
                              { ekind := .High, ereg := r, eloc := .R hi } e0) := by
                        simpa [remove_equations_builtin_res, htype', hsame] using hremove.symm
                      subst e1
                      simp [params_of_builtin_res] at hreg hloc
                      unfold satisf at hsat ⊢
                      intro q hq
                      change equation at q
                      change Regmap.t val at rs
                      change Locmap.t at ls
                      let qlo : equation :=
                        { ekind := .Low, ereg := r, eloc := .R lo }
                      let qhi : equation :=
                        { ekind := .High, ereg := r, eloc := .R hi }
                      by_cases heqlo : q = qlo
                      · subst q
                        have hlow : Val.lessdef (Val.loword v) (Val.loword v') := by
                          cases hld with
                          | lessdef_refl => exact Val.lessdef_refl _
                          | lessdef_undef => exact Val.lessdef_undef _
                        have hget : Regmap.get r (Regmap.set r v rs) = v :=
                          Regmap.gss_proof val r v rs
                        have hset :
                            Locmap.set (R lo) (Val.loword v')
                                (Locmap.set (R hi) (Val.hiword v') ls) (R lo) =
                              Val.loword v' := by
                          simpa using Locmap.gss (R lo) (Val.loword v')
                            (Locmap.set (R hi) (Val.hiword v') ls)
                        change Val.lessdef
                          (Val.loword (Regmap.get r (Regmap.set r v rs)))
                          (Locmap.set (R lo) (Val.loword v')
                            (Locmap.set (R hi) (Val.hiword v') ls) (R lo))
                        rw [hget, hset]
                        exact hlow
                      · by_cases heqhi : q = qhi
                        · subst q
                          have hhigh : Val.lessdef (Val.hiword v) (Val.hiword v') := by
                            cases hld with
                            | lessdef_refl => exact Val.lessdef_refl _
                            | lessdef_undef => exact Val.lessdef_undef _
                          have hget : Regmap.get r (Regmap.set r v rs) = v :=
                            Regmap.gss_proof val r v rs
                          have hdiff : Loc.diff (R lo) (R hi) := by
                            exact fun h => hsame h.symm
                          change Val.lessdef
                            (Val.hiword (Regmap.get r (Regmap.set r v rs)))
                            (Locmap.set (R lo) (Val.loword v')
                              (Locmap.set (R hi) (Val.hiword v') ls) (R hi))
                          rw [hget]
                          rw [Locmap.gso (R lo) (Val.loword v')
                            (Locmap.set (R hi) (Val.hiword v') ls) (R hi) hdiff]
                          rw [Locmap.gss]
                          exact hhigh
                        · have hqrem : EqSet.In q
                              (remove_equation qlo (remove_equation qhi e0)).eqs1 := by
                            unfold remove_equation
                            apply EqSet.remove_2 (remove_equation qhi e0).eqs1 qlo q
                            · intro h
                              exact heqlo h.symm
                            · unfold remove_equation
                              apply EqSet.remove_2 e0.eqs1 qhi q
                              · intro h
                                exact heqhi h.symm
                              · exact hq
                          have hregdiff : q.ereg ≠ r :=
                            reg_unconstrained_sound r
                              (remove_equation qlo (remove_equation qhi e0)) q
                              (by simpa [qlo, qhi] using hreg) hqrem
                          have hlodiff : Loc.diff (R lo) q.eloc :=
                            loc_unconstrained_sound (R lo)
                              (remove_equation qlo (remove_equation qhi e0)) q
                              (by simpa [qlo, qhi] using hloc.2) hqrem
                          have hhidiff : Loc.diff (R hi) q.eloc :=
                            loc_unconstrained_sound (R hi)
                              (remove_equation qlo (remove_equation qhi e0)) q
                              (by simpa [qlo, qhi] using hloc.1) hqrem
                          change Val.lessdef
                            (sel_val q.ekind (Regmap.get q.ereg (Regmap.set r v rs)))
                            (Locmap.set (R lo) (Val.loword v')
                              (Locmap.set (R hi) (Val.hiword v') ls) q.eloc)
                          rw [Regmap.gso_proof val q.ereg r v rs hregdiff]
                          rw [Locmap.gso (R lo) (Val.loword v')
                            (Locmap.set (R hi) (Val.hiword v') ls) q.eloc hlodiff]
                          rw [Locmap.gso (R hi) (Val.hiword v') ls q.eloc hhidiff]
                          exact hsat q (by simpa [qlo, qhi] using hqrem)
              | BR_none =>
                  simp [remove_equations_builtin_res] at hremove
              | BR_splitlong _ _ =>
                  simp [remove_equations_builtin_res] at hremove
          | BR_none =>
              simp [remove_equations_builtin_res] at hremove
          | BR_splitlong _ _ =>
              simp [remove_equations_builtin_res] at hremove
  | BR_none =>
      cases resultLoc with
      | BR _ => simp [remove_equations_builtin_res] at hremove
      | BR_none =>
          simp [remove_equations_builtin_res] at hremove
          subst e1
          simpa [regmap_setres, Locmap.setres] using hsat
      | BR_splitlong _ _ => simp [remove_equations_builtin_res] at hremove
  | BR_splitlong _ _ =>
      cases resultLoc <;> simp [remove_equations_builtin_res] at hremove

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Maps

theorem analyze_successors : analyze_successorsStatement := by
  intro cfg f env bsh an pc bs s e hAnalyze hBsh hSucc hAn
  unfold analyze at hAnalyze
  have hsol :=
    CompCert4Lean.Backend.Kildall.Backward_Dataflow_Solver.fixpoint_allnodes_solution
      (LAT := CompCert4Lean.Backend.Allocation.DS.L)
      (NS := CompCert4Lean.Backend.Kildall.NodeSetBackward)
      (CompCert4Lean.Backend.Allocation.DS.law_obligation_proof.1)
      CompCert4Lean.Backend.Kildall.NodeSetBackward.law_obligation_proof
      bsh successors_block_shape (transfer cfg f env bsh) an pc bs s hAnalyze hBsh hSucc
  change (match PMap.get pc an, transfer cfg f env bsh s (PMap.get s an) with
    | .OK a, .OK b => EqSet.Subset b a
    | .Error _, _ => True
    | _, .Error _ => False) at hsol
  rw [hAn] at hsol
  cases htransfer : transfer cfg f env bsh s (PMap.get s an) with
  | Error msg =>
      simp [htransfer] at hsol
  | OK e' =>
      refine ⟨e', rfl, ?_⟩
      simpa [htransfer] using hsol

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Maps

theorem satisf_successors : satisf_successorsStatement := by
  intro cfg f env bsh an pc bs s e rs ls hAnalyze hBsh hSucc hAn hSat
  obtain ⟨e', hTransfer, hSubset⟩ :=
    analyze_successors cfg f env bsh an pc bs s e hAnalyze hBsh hSucc hAn
  exact ⟨e', hTransfer, satisf_incr rs ls e' e hSat hSubset⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking

theorem symbols_preserved : symbols_preservedStatement := by
  intro cfg oracle prog tprog hmatch id
  letI : Linker RTL.fundef := Linker_fundef RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker RTL.program := Linker_prog RTL.fundef Unit
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch
  exact Genv.find_symbol_match RTL.program RTL.fundef Unit LTL.fundef Unit
    (fun _ f tf => transf_fundef cfg oracle f = .OK tf) Eq
    prog prog tprog hmatch id

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking

theorem senv_preserved : senv_preservedStatement := by
  intro cfg oracle prog tprog hmatch
  letI : Linker RTL.fundef := Linker_fundef RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker RTL.program := Linker_prog RTL.fundef Unit
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch
  exact Genv.senv_match RTL.program RTL.fundef Unit LTL.fundef Unit
    (fun _ f tf => transf_fundef cfg oracle f = .OK tf) Eq
    prog prog tprog hmatch

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking

theorem functions_translated : functions_translatedStatement := by
  intro cfg oracle prog tprog hmatch v f hfind
  letI : Linker RTL.fundef := Linker_fundef RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker RTL.program := Linker_prog RTL.fundef Unit
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch
  rcases Genv.find_funct_match RTL.program RTL.fundef Unit LTL.fundef Unit
    (fun _ f tf => transf_fundef cfg oracle f = .OK tf) Eq
    prog prog tprog hmatch v f hfind with ⟨_, tf, hfindtf, htrans, _⟩
  exact ⟨tf, hfindtf, htrans⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking

theorem function_ptr_translated : function_ptr_translatedStatement := by
  intro cfg oracle prog tprog hmatch b f hfind
  letI : Linker RTL.fundef := Linker_fundef RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker RTL.program := Linker_prog RTL.fundef Unit
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch
  rcases Genv.find_funct_ptr_match RTL.program RTL.fundef Unit LTL.fundef Unit
    (fun _ f tf => transf_fundef cfg oracle f = .OK tf) Eq
    prog prog tprog hmatch b f hfind with ⟨_, tf, hfindtf, htrans, _⟩
  exact ⟨tf, hfindtf, htrans⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST

theorem sig_function_translated : sig_function_translatedStatement := by
  intro cfg oracle f tf h
  cases f with
  | Internal fn =>
      unfold CompCert4Lean.Backend.Allocation.transf_fundef
        CompCert4Lean.Common.AST.transf_partial_fundef at h
      cases htr : CompCert4Lean.Backend.Allocation.transf_function cfg oracle fn with
      | Error msg => simp [htr] at h
      | OK tf' =>
          simp [htr] at h
          cases h
          unfold CompCert4Lean.Backend.Allocation.transf_function at htr
          cases ht : CompCert4Lean.Backend.RTLtyping.type_function cfg fn with
          | Error msg => simp [ht] at htr
          | OK env =>
              cases ho : CompCert4Lean.Backend.Allocation.regalloc oracle fn with
              | Error msg => simp [ht, ho] at htr
              | OK tf0 =>
                  cases hc : CompCert4Lean.Backend.Allocation.check_function cfg fn tf0 env with
                  | Error msg => simp [ht, ho, hc] at htr
                  | OK u =>
                      simp [ht, ho, hc] at htr
                      cases htr
                      unfold CompCert4Lean.Backend.Allocation.check_function at hc
                      cases ha : CompCert4Lean.Backend.Allocation.analyze cfg fn env
                          (CompCert4Lean.Backend.Allocation.pair_codes fn tf') with
                      | none => simp [ha] at hc
                      | some an =>
                          simp [ha] at hc
                          unfold CompCert4Lean.Backend.Allocation.check_entrypoints at hc
                          cases he : CompCert4Lean.Backend.Allocation.transfer cfg fn env
                              (CompCert4Lean.Backend.Allocation.pair_codes fn tf')
                              fn.fn_entrypoint
                              (CompCert4Lean.Lib.Maps.PMap.get fn.fn_entrypoint an) with
                          | Error msg => simp [he] at hc
                          | OK e1 =>
                              simp [he] at hc
                              cases hx : CompCert4Lean.Backend.Allocation.check_entrypoints_aux
                                  cfg fn tf' env e1 with
                              | none => simp [hx] at hc
                              | some u' =>
                                  simp [hx] at hc
                                  unfold CompCert4Lean.Backend.Allocation.check_entrypoints_aux at hx
                                  cases hp : CompCert4Lean.Backend.Allocation.pair_entrypoints fn tf' with
                                  | none => simp [hp] at hx
                                  | some mv =>
                                      cases htm : CompCert4Lean.Backend.Allocation.track_moves env mv e1 with
                                      | none => simp [hp, htm] at hx
                                      | some e2 =>
                                          simp [hp, htm] at hx
                                          have hsigbool := hx.2.2.2
                                          cases hsigeq : signature_eq fn.fn_sig tf'.fn_sig with
                                          | left hsig => exact hsig.symm
                                          | right hne =>
                                              rw [hsigeq] at hsigbool
                                              cases hsigbool
  | External ef =>
      simp [CompCert4Lean.Backend.Allocation.transf_fundef,
        CompCert4Lean.Common.AST.transf_partial_fundef] at h
      cases h
      rfl

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking

theorem find_function_translated : find_function_translatedStatement := by
  intro cfg oracle prog tprog hmatch ros rs fd ros' e e' ls hfind hros hsat
  cases ros with
  | inl r =>
      cases ros' with
      | inl mr =>
          simp [add_equation_ros] at hros
          rcases hros with ⟨rfl, rfl⟩
          simp only [RTL.find_function] at hfind
          have hfind' : Genv.find_funct (Genv.globalenv prog)
              (CompCert4Lean.Backend.Registers.Regmap.get r rs) = some fd := by
            simpa [RTL.find_function] using hfind
          have hld := add_equation_lessdef rs ls
            { ekind := Full, ereg := r, eloc := .R mr } e hsat
          have hld' : CompCert4Lean.Common.Values.Val.lessdef
              (CompCert4Lean.Backend.Registers.Regmap.get r rs)
              (ls (CompCert4Lean.Backend.Locations.R mr)) := by
            simpa [sel_val] using hld
          clear hsat hld
          generalize hsrc : CompCert4Lean.Backend.Registers.Regmap.get r rs = vs
              at hfind' hld'
          generalize htgt : ls (CompCert4Lean.Backend.Locations.R mr) = vt at hld'
          cases hld' with
          | lessdef_refl v =>
              rcases functions_translated cfg oracle prog tprog hmatch
                  vs fd hfind' with
                ⟨tf, hfindtf, htrans⟩
              refine ⟨tf, ?_, htrans⟩
              change Genv.find_funct (Genv.globalenv tprog)
                (ls (CompCert4Lean.Backend.Locations.R mr)) = some tf
              rw [htgt]
              exact hfindtf
          | lessdef_undef v =>
              simp [Genv.find_funct] at hfind'
      | inr id' =>
          simp [add_equation_ros] at hros
  | inr id =>
      cases ros' with
      | inl mr =>
          simp [add_equation_ros] at hros
      | inr id' =>
          simp [add_equation_ros] at hros
          cases hEq : ident_eq id id' with
          | left heq =>
              have hb := hros.1
              rw [hEq] at hb
              change (true : Bool) = true at hb
              cases heq
              rcases hros with ⟨_, rfl⟩
              simp only [RTL.find_function, LTL.find_function] at hfind ⊢
              rw [symbols_preserved cfg oracle prog tprog hmatch id]
              cases hs : Genv.find_symbol (Genv.globalenv prog) id with
              | none => simp [hs] at hfind
              | some b =>
                  simp only [hs] at hfind ⊢
                  exact function_ptr_translated cfg oracle prog tprog hmatch b fd hfind
          | right hne =>
              have hb := hros.1
              rw [hEq] at hb
              change (false : Bool) = true at hb
              cases hb

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Events
open CompCert4Lean.X86.Op
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

set_option maxHeartbeats 0 in
theorem exec_moves
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    exec_movesStatement := by
  intro cfg xi tprog mv env rs s f sp bb m e e' ls htrack hwf hsat hwt
  induction mv generalizing e e' ls with
  | nil =>
      simp [track_moves, expand_moves] at htrack
      cases htrack
      exact ⟨ls, star_refl _ _ _, hsat⟩
  | cons a mv ih =>
      cases hwf with
      | cons hhead htail =>
          cases a with
          | MV src dst =>
              change (match track_moves env mv e with
                | none => none
                | some e1 =>
                    if can_undef_except dst (destroyed_by_move src dst) e1 &&
                        well_typed_move env dst e1 then
                      subst_loc dst src e1
                    else none) = some e' at htrack
              cases hrec : track_moves env mv e with
              | none => simp [hrec] at htrack
              | some e1 =>
                  rw [hrec] at htrack
                  cases hc : (can_undef_except dst (destroyed_by_move src dst) e1 &&
                    well_typed_move env dst e1) with
                  | false => simp [hc] at htrack
                  | true =>
                      simp [hc] at htrack
                      have hct : can_undef_except dst (destroyed_by_move src dst) e1 = true ∧
                          well_typed_move env dst e1 = true := by
                        simpa [Bool.and_eq_true] using hc
                      have hsat1 := subst_loc_undef_satisf env src dst rs ls
                        (destroyed_by_move src dst) e1 e' htrack hct.2 hct.1 hwt hsat
                      rcases ih (e := e) (e' := e1)
                        (ls := Locmap.set dst (ls src)
                          (undef_regs (destroyed_by_move src dst) ls))
                        hrec htail hsat1 with ⟨ls', hstar, hsat'⟩
                      refine ⟨ls', ?_, hsat'⟩
                      cases src with
                      | R rsrc =>
                          cases dst with
                          | R rdst =>
                              apply star_left
                              · apply CompCert4Lean.Backend.LTL.step.exec_Lop (v := ls (R rsrc))
                                · rfl
                                · rfl
                              · exact hstar
                              · rfl
                          | S sl ofs ty =>
                              apply star_left
                              · apply CompCert4Lean.Backend.LTL.step.exec_Lsetstack
                                rfl
                              · exact hstar
                              · rfl
                      | S sl ofs ty =>
                          cases dst with
                          | R rdst =>
                              apply star_left
                              · apply CompCert4Lean.Backend.LTL.step.exec_Lgetstack
                                rfl
                              · exact hstar
                              · rfl
                          | S sl' ofs' ty' =>
                              exact False.elim hhead
          | MVmakelong src1 src2 dst =>
              change (if CompCert4Lean.X86_64.Archi.ptr64 then none else
                match track_moves env mv e with
                | none => none
                | some e1 =>
                    if long_type_compat env (R dst) e1 then
                      subst_loc_pair (R dst) (R src1) (R src2) e1
                    else none) = some e' at htrack
              have hptr : CompCert4Lean.X86_64.Archi.ptr64 = false := by
                cases hp : CompCert4Lean.X86_64.Archi.ptr64 with
                | false => exact rfl
                | true => simp [hp] at htrack
              cases hrec : track_moves env mv e with
              | none => simp [hrec, hptr] at htrack
              | some e1 =>
                  rw [hptr, hrec] at htrack
                  cases hc : long_type_compat env (R dst) e1 with
                  | false => simp [hc] at htrack
                  | true =>
                      simp [hc] at htrack
                      have hsat1 := subst_loc_pair_satisf_makelong env src1 src2 dst rs ls
                        e1 e' htrack (by exact hc) hwt hsat hptr
                      rcases ih (e := e) (e' := e1)
                        (ls := Locmap.set (R dst)
                          (Val.longofwords (ls (R src1)) (ls (R src2))) ls)
                        hrec htail hsat1 with ⟨ls', hstar, hsat'⟩
                      refine ⟨ls', ?_, hsat'⟩
                      apply star_left
                      · apply CompCert4Lean.Backend.LTL.step.exec_Lop
                          (v := Val.longofwords (ls (R src1)) (ls (R src2)))
                        · rfl
                        · rfl
                      · exact hstar
                      · rfl
          | MVlowlong src dst =>
              change (if CompCert4Lean.X86_64.Archi.ptr64 then none else
                match track_moves env mv e with
                | none => none
                | some e1 => subst_loc_part (R dst) (R src) Low e1) = some e' at htrack
              have hptr : CompCert4Lean.X86_64.Archi.ptr64 = false := by
                cases hp : CompCert4Lean.X86_64.Archi.ptr64 with
                | false => exact rfl
                | true => simp [hp] at htrack
              cases hrec : track_moves env mv e with
              | none => simp [hrec, hptr] at htrack
              | some e1 =>
                  rw [hptr, hrec] at htrack
                  have hsat1 := subst_loc_part_satisf_lowlong src dst rs ls e1 e'
                    htrack hsat
                  rcases ih (e := e) (e' := e1)
                    (ls := Locmap.set (R dst) (Val.loword (ls (R src))) ls)
                    hrec htail hsat1 with ⟨ls', hstar, hsat'⟩
                  refine ⟨ls', ?_, hsat'⟩
                  apply star_left
                  · apply CompCert4Lean.Backend.LTL.step.exec_Lop
                      (v := Val.loword (ls (R src)))
                    · rfl
                    · rfl
                  · exact hstar
                  · rfl
          | MVhighlong src dst =>
              change (if CompCert4Lean.X86_64.Archi.ptr64 then none else
                match track_moves env mv e with
                | none => none
                | some e1 => subst_loc_part (R dst) (R src) High e1) = some e' at htrack
              have hptr : CompCert4Lean.X86_64.Archi.ptr64 = false := by
                cases hp : CompCert4Lean.X86_64.Archi.ptr64 with
                | false => exact rfl
                | true => simp [hp] at htrack
              cases hrec : track_moves env mv e with
              | none => simp [hrec, hptr] at htrack
              | some e1 =>
                  rw [hptr, hrec] at htrack
                  have hsat1 := subst_loc_part_satisf_highlong src dst rs ls e1 e'
                    htrack hsat
                  rcases ih (e := e) (e' := e1)
                    (ls := Locmap.set (R dst) (Val.hiword (ls (R src))) ls)
                    hrec htail hsat1 with ⟨ls', hstar, hsat'⟩
                  refine ⟨ls', ?_, hsat'⟩
                  apply star_left
                  · apply CompCert4Lean.Backend.LTL.step.exec_Lop
                      (v := Val.hiword (ls (R src)))
                    · rfl
                    · rfl
                  · exact hstar
                  · rfl

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

theorem match_stackframes_change_sig
    [binary64_certificate : BinaryNormalizeCertificate
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)] :
    match_stackframes_change_sigStatement := by
  intro cfg oracle xi tprog s ts sg sg' hmatch hres
  cases hmatch with
  | match_stackframes_nil sg0 hsg0 =>
      exact match_stackframes_nil sg' (hres.trans hsg0)
  | @match_stackframes_cons resultReg f sp pc rs s tf bb ls ts sg0 an e env
      hstacks hfun hanalyze heq hwtf hwtrs hwtres hsteps =>
      apply match_stackframes_cons resultReg f sp pc rs s tf bb ls ts sg'
        an e env hstacks hfun hanalyze heq hwtf hwtrs
      · simpa [CompCert4Lean.Common.AST.proj_sig_res, hres] using hwtres
      · intro v ls1 m hv hty hag
        apply hsteps v ls1 m
        · have hlr := CompCert4Lean.X86.Conventions1.loc_result_exten sg' sg hres
          simpa [hlr] using hv
        · exact hty
        · exact hag

theorem addressing_not_long : addressing_not_longStatement := by
  intro cfg env f addr args dst s r hwt hsplit hr
  simp [CompCert4Lean.X86_64.Archi.splitlong,
    CompCert4Lean.X86_64.Archi.ptr64] at hsplit

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Values

private theorem allocproof_val_inject_refl
    (v : CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.inject
      CompCert4Lean.Common.Values.inject_id v v := by
  cases v with
  | Vint i => exact CompCert4Lean.Common.Values.Val.inject.inject_int _
  | Vlong i => exact CompCert4Lean.Common.Values.Val.inject.inject_long _
  | Vfloat f => exact CompCert4Lean.Common.Values.Val.inject.inject_float _
  | Vsingle f => exact CompCert4Lean.Common.Values.Val.inject.inject_single _
  | Vptr b ofs =>
      apply CompCert4Lean.Common.Values.Val.inject.inject_ptr
      · rfl
      · exact (pgo_ptrofs_add_zero ofs).symm
  | Vundef => exact CompCert4Lean.Common.Values.Val.inject.val_inject_undef _

private theorem allocproof_mem_extends_refl
    (m : CompCert4Lean.Common.Memory.mem) :
    CompCert4Lean.Common.Memory.Mem.extends m m := by
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro b1 b2 delta ofs k p hmap hp
      have hpair : (b1, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) =
          (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change CompCert4Lean.Common.Memory.Mem.perm m b1
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
          (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) k p
      have hz : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
          (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) = ofs := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs + 0)) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        simp
      rw [hz]
      exact hp
    · intro b1 b2 delta chunk ofs p hmap hp
      have hpair : (b1, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) =
          (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      refine ⟨.Z0, ?_⟩
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      change 0 = CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
          (CompCert4Lean.Common.Memdata.align_chunk chunk)
          (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z))
      change 0 = CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Common.Memdata.align_chunk chunk) * 0))
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      simp
    · intro b1 ofs b2 delta hmap hp
      have hpair : (b1, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) =
          (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change CompCert4Lean.Common.Memdata.memval_inject
        CompCert4Lean.Common.Values.inject_id
        (CompCert4Lean.Lib.Maps.ZMap.get ofs
          (CompCert4Lean.Lib.Maps.PMap.get b1 m.mem_contents))
        (CompCert4Lean.Lib.Maps.ZMap.get
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
            (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z))
          (CompCert4Lean.Lib.Maps.PMap.get b1 m.mem_contents))
      have hz : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
          (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) = ofs := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs + 0)) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        simp
      rw [hz]
      cases hmv : CompCert4Lean.Lib.Maps.ZMap.get ofs
          (CompCert4Lean.Lib.Maps.PMap.get b1 m.mem_contents) with
      | Byte n => exact CompCert4Lean.Common.Memdata.memval_inject.byte _ _
      | Fragment v q n =>
          exact CompCert4Lean.Common.Memdata.memval_inject.fragment _ _ _ _ _
            (allocproof_val_inject_refl v)
      | Undef => exact CompCert4Lean.Common.Memdata.memval_inject.undef _ _
  · intro b ofs k p hp
    exact Or.inl hp

theorem initial_states_simulation
    [binary64_certificate : BinaryNormalizeCertificate
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)] :
    initial_states_simulationStatement := by
  letI : Linker RTL.fundef := Linker_fundef RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker RTL.program := Linker_prog RTL.fundef Unit
  intro cfg oracle xi prog tprog hmatch st1 hinit
  cases hinit with
  | intro b f m0 hmem hsymb hfun hsig =>
      rcases function_ptr_translated cfg oracle prog tprog hmatch b f hfun with
        ⟨tf, hfindtf, htrans⟩
      refine ⟨LTL.Callstate [] tf
        (CompCert4Lean.Backend.Locations.Locmap.init
          CompCert4Lean.Common.Values.Vundef) m0, ?_, ?_⟩
      · apply LTL.initial_state.intro b tf m0
        · unfold Genv.init_mem at hmem ⊢
          exact Genv.init_mem_transf_partial
            RTL.fundef LTL.fundef Unit
            (fun f => CompCert4Lean.Backend.Allocation.transf_fundef cfg oracle f)
            prog tprog hmatch m0 hmem
        · change Genv.find_symbol (Genv.globalenv tprog) tprog.prog_main = some b
          have hmatch' := hmatch
          unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch'
          rw [hmatch'.2.1]
          rw [symbols_preserved cfg oracle prog tprog hmatch prog.prog_main]
          exact hsymb
        · exact hfindtf
        · rw [sig_function_translated cfg oracle f tf htrans]
          exact hsig
      · apply match_states_call
        · apply match_stackframes_nil
          rw [sig_function_translated cfg oracle f tf htrans]
          rw [hsig]
          rfl
        · exact htrans
        · rw [sig_function_translated cfg oracle f tf htrans, hsig]
          have hloc : CompCert4Lean.X86.Conventions1.loc_arguments cfg
              CompCert4Lean.Common.AST.signature_main = [] := by
            unfold CompCert4Lean.X86.Conventions1.loc_arguments
            cases hwin : CompCert4Lean.X86_64.Archi.win64 cfg <;>
              simp [hwin, CompCert4Lean.X86.Conventions1.loc_arguments_win64,
                CompCert4Lean.X86.Conventions1.loc_arguments_elf64,
                CompCert4Lean.X86.Conventions1.loc_arguments_32,
                CompCert4Lean.Common.AST.proj_sig_args,
                CompCert4Lean.Common.AST.signature_main,
                CompCert4Lean.X86_64.Archi.ptr64]
          rw [hloc]
          exact CompCert4Lean.Common.Values.Val.lessdef_list_nil
        · intro l hl
          rfl
        · exact allocproof_mem_extends_refl m0
        · rw [sig_function_translated cfg oracle f tf htrans, hsig]
          simp [CompCert4Lean.Common.AST.proj_sig_args,
            CompCert4Lean.Common.AST.signature_main]
          trivial

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Backend.RTLtyping

theorem wt_prog : wt_progStatement := by
  intro cfg oracle prog tprog hmatch
  letI : Linker RTL.fundef := Linker_fundef RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker RTL.program := Linker_prog RTL.fundef Unit
  unfold wt_program
  intro i fd hmem
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch
  rcases hmatch with ⟨hdefs, _, _⟩
  rcases @list_forall2_in_left _ _ _ _ _ _ hdefs hmem with ⟨ig', _, hrel⟩
  rcases ig' with ⟨i', gd'⟩
  simp only [match_ident_globdef] at hrel
  rcases hrel with ⟨_, hgd⟩
  cases fd with
  | Internal f =>
      change CompCert4Lean.Backend.RTLtyping.wt_fundef cfg
        (CompCert4Lean.Common.AST.fundef.Internal f)
      cases gd' with
      | Gfun tf =>
          cases hgd with
          | match_globdef_fun _ _ _ _ hfun =>
              unfold CompCert4Lean.Backend.Allocation.transf_fundef
                CompCert4Lean.Common.AST.transf_partial_fundef at hfun
              unfold CompCert4Lean.Backend.Allocation.transf_function at hfun
              cases htype : CompCert4Lean.Backend.RTLtyping.type_function cfg f with
              | Error msg =>
                  simp only [htype] at hfun
                  cases hfun
              | OK env =>
                  simp only [htype] at hfun
                  cases horacle : CompCert4Lean.Backend.Allocation.regalloc oracle f with
                  | Error msg =>
                      simp only [horacle] at hfun
                      cases hfun
                  | OK tf0 =>
                      simp only [horacle] at hfun
                      cases hcheck : CompCert4Lean.Backend.Allocation.check_function
                          cfg f tf0 env with
                      | Error msg =>
                          simp only [hcheck] at hfun
                          cases hfun
                      | OK unit =>
                          simp [hcheck] at hfun
                          cases hfun
                          exact wt_function_internal f env
                            (CompCert4Lean.Backend.RTLtyping.type_function_correct
                              cfg f env htype)
      | Gvar v => cases hgd
  | External ef =>
      change CompCert4Lean.Backend.RTLtyping.wt_fundef cfg
        (CompCert4Lean.Common.AST.fundef.External ef)
      cases gd' with
      | Gfun tf =>
          cases hgd with
          | match_globdef_fun _ _ _ _ hfun =>
              simp [CompCert4Lean.Backend.Allocation.transf_fundef] at hfun
              cases hfun
              exact wt_fundef_external ef
      | Gvar v => cases hgd

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
open CompCert4Lean.X86.Conventions1

private theorem allocproof_lessdef_vint
    (r : CompCert4Lean.Lib.Integers.Int.int) (v : CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.lessdef (CompCert4Lean.Common.Values.Vint r) v →
      v = CompCert4Lean.Common.Values.Vint r := by
  intro h
  cases h with
  | lessdef_refl => rfl

theorem final_states_simulation
    [binary64_certificate : BinaryNormalizeCertificate
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)] :
    final_states_simulationStatement := by
  intro cfg oracle xi tprog st1 st2 r hmatch hfinal
  cases hfinal
  cases hmatch with
  | match_states_return s result m ts ls m' sg hstacks hres hag hmem hwtres =>
      cases hstacks with
      | match_stackframes_nil sg hsig =>
          have hres' :
              Locmap.getpair (map_rpair R (loc_result sg)) ls =
                CompCert4Lean.Common.Values.Vint r :=
            allocproof_lessdef_vint r _ hres
          apply LTL.final_state.intro ls m' r
          have hloc : loc_result sg = loc_result signature_main :=
            loc_result_exten sg signature_main hsig
          change Locmap.getpair (map_rpair R (loc_result signature_main)) ls =
            CompCert4Lean.Common.Values.Vint r
          rw [← hloc]
          exact hres'

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LTL
open CompCert4Lean.X86.Op
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib

private theorem local_parse_branch
    (b : LTL.bblock) (mv : moves) (b1 : LTL.bblock) (s : RTL.node)
    (hmv : extract_moves [] b = (mv, b1))
    (hs : check_succ s b1 = true) :
    ∃ k, wf_moves mv ∧ b = expand_moves mv (Lbranch s :: k) := by
  rcases extract_moves_sound b mv b1 hmv with ⟨hwf, hb⟩
  rcases check_succ_sound s b1 hs with ⟨k, hk⟩
  subst b1
  refine ⟨k, hwf, ?_⟩
  simpa [expand_moves] using hb

private theorem local_parse_op
    (b : LTL.bblock) (mv1 : moves) (b1 : LTL.bblock)
    (op : operation) (args' : List CompCert4Lean.X86.Machregs.mreg) (res' : CompCert4Lean.X86.Machregs.mreg)
    (mv2 : moves) (b2 b3 : LTL.bblock) (s : RTL.node)
    (hm1 : extract_moves [] b = (mv1, b1))
    (hhead : b1 = Lop op args' res' :: b2)
    (hm2 : extract_moves [] b2 = (mv2, b3))
    (hs : check_succ s b3 = true) :
    ∃ k, wf_moves mv1 ∧ wf_moves mv2 ∧
      b = expand_moves mv1
        (Lop op args' res' :: expand_moves mv2 (Lbranch s :: k)) := by
  rcases extract_moves_sound b mv1 b1 hm1 with ⟨hwf1, hb1⟩
  rcases extract_moves_sound b2 mv2 b3 hm2 with ⟨hwf2, hb2⟩
  rcases check_succ_sound s b3 hs with ⟨k, hk⟩
  subst b3
  rw [hhead] at hb1
  refine ⟨k, hwf1, hwf2, ?_⟩
  have hb2' : b2 = expand_moves mv2 (Lbranch s :: k) := by
    simpa [expand_moves] using hb2
  rw [hb2'] at hb1
  simpa [expand_moves, List.append_assoc] using hb1

private theorem local_pair_Iop
    (op : operation) (args : List reg) (res : reg) (s : RTL.node)
    (b : LTL.bblock) (bsh : block_shape)
    (h : pair_Iop_block op args res s b = some bsh) :
    expand_block_shape bsh (Iop op args res s) b := by
  unfold pair_Iop_block at h
  cases hm1 : extract_moves [] b with
  | mk mv1 b1 =>
      simp only [hm1] at h
      cases hb1 : b1 with
      | nil => simp [hb1, check_succ] at h
      | cons hd tl =>
          cases hd with
          | Lop op' args' res' =>
              cases hm2 : extract_moves [] tl with
              | mk mv2 b3 =>
                  simp only [hb1] at h
                  rw [hm2] at h
                  cases heq : eq_operation op op' with
                  | left hop =>
                      cases hs : check_succ s b3 with
                      | false => simp [hb1, hm2, heq, hs] at h
                      | true =>
                          simp [hb1, hm2, heq, hs] at h
                          rcases h with ⟨_, hshape⟩
                          cases hshape
                          subst b1
                          rcases local_parse_op b mv1 (Lop op' args' res' :: tl)
                            op' args' res' mv2 tl b3 s hm1 (by rfl) hm2 hs with
                            ⟨k, hwf1, hwf2, hb⟩
                          subst op'
                          rw [hb]
                          exact ebs_op op args res mv1 args' res' mv2 s k hwf1 hwf2
                  | right hne =>
                      simp [hb1, heq] at h
                      rcases h with ⟨⟨hbool, _⟩, _⟩
                      change false = true at hbool
                      cases hbool
          | Lbranch succ =>
              cases hs : check_succ s (Lbranch succ :: tl) with
              | false => simp [hb1, hs] at h
              | true =>
                  simp [hb1, hs] at h
                  cases h
                  subst b1
                  exact ebs_opdead_from_parse_local op args res s b mv1
                    (Lbranch succ :: tl) hm1 hs
          | Lgetstack sl ofs ty dst => simp [hb1, check_succ] at h
          | Lsetstack src sl ofs ty => simp [hb1, check_succ] at h
          | Lload chunk addr args' dst => simp [hb1, check_succ] at h
          | Lstore chunk addr args' src => simp [hb1, check_succ] at h
          | Lcall sg ros => simp [hb1, check_succ] at h
          | Ltailcall sg ros => simp [hb1, check_succ] at h
          | Lbuiltin ef args' res' => simp [hb1, check_succ] at h
          | Lcond cond args' s1 s2 => simp [hb1, check_succ] at h
          | Ljumptable arg tbl => simp [hb1, check_succ] at h
          | Lreturn => simp [hb1, check_succ] at h

private theorem local_parse_load
    (b : LTL.bblock) (mv1 : moves) (b1 : LTL.bblock)
    (chunk : memory_chunk) (addr : addressing)
    (args' : List CompCert4Lean.X86.Machregs.mreg)
    (dst' : CompCert4Lean.X86.Machregs.mreg)
    (mv2 : moves) (b2 b3 : LTL.bblock) (s : RTL.node)
    (hm1 : extract_moves [] b = (mv1, b1))
    (hhead : b1 = Lload chunk addr args' dst' :: b2)
    (hm2 : extract_moves [] b2 = (mv2, b3))
    (hs : check_succ s b3 = true) :
    ∃ k, wf_moves mv1 ∧ wf_moves mv2 ∧
      b = expand_moves mv1
        (Lload chunk addr args' dst' :: expand_moves mv2 (Lbranch s :: k)) := by
  rcases extract_moves_sound b mv1 b1 hm1 with ⟨hwf1, hb1⟩
  rcases extract_moves_sound b2 mv2 b3 hm2 with ⟨hwf2, hb2⟩
  rcases check_succ_sound s b3 hs with ⟨k, hk⟩
  subst b3
  rw [hhead] at hb1
  refine ⟨k, hwf1, hwf2, ?_⟩
  have hb2' : b2 = expand_moves mv2 (Lbranch s :: k) := by
    simpa [expand_moves] using hb2
  rw [hb2'] at hb1
  simpa [expand_moves, List.append_assoc] using hb1

private theorem local_parse_store
    (b : LTL.bblock) (mv1 : moves) (b1 : LTL.bblock)
    (chunk : memory_chunk) (addr : addressing)
    (args' : List CompCert4Lean.X86.Machregs.mreg)
    (src' : CompCert4Lean.X86.Machregs.mreg)
    (b2 : LTL.bblock) (s : RTL.node)
    (hm1 : extract_moves [] b = (mv1, b1))
    (hhead : b1 = Lstore chunk addr args' src' :: b2)
    (hs : check_succ s b2 = true) :
    ∃ k, wf_moves mv1 ∧
      b = expand_moves mv1 (Lstore chunk addr args' src' :: Lbranch s :: k) := by
  rcases extract_moves_sound b mv1 b1 hm1 with ⟨hwf1, hb1⟩
  rcases check_succ_sound s b2 hs with ⟨k, hk⟩
  subst b2
  rw [hhead] at hb1
  refine ⟨k, hwf1, ?_⟩
  simpa [expand_moves] using hb1

private theorem local_parse_call
    (b : LTL.bblock) (mv1 : moves) (b1 : LTL.bblock)
    (sg : signature) (ros' : Sum CompCert4Lean.X86.Machregs.mreg ident)
    (mv2 : moves) (b2 b3 : LTL.bblock) (s : RTL.node)
    (hm1 : extract_moves_ext [] b = (mv1, b1))
    (hhead : b1 = Lcall sg ros' :: b2)
    (hm2 : extract_moves_ext [] b2 = (mv2, b3))
    (hs : check_succ s b3 = true) :
    ∃ k, wf_moves mv1 ∧ wf_moves mv2 ∧
      b = expand_moves mv1
        (Lcall sg ros' :: expand_moves mv2 (Lbranch s :: k)) := by
  rcases extract_moves_ext_sound b mv1 b1 hm1 with ⟨hwf1, hb1⟩
  rcases extract_moves_ext_sound b2 mv2 b3 hm2 with ⟨hwf2, hb2⟩
  rcases check_succ_sound s b3 hs with ⟨k, hk⟩
  subst b3
  rw [hhead] at hb1
  refine ⟨k, hwf1, hwf2, ?_⟩
  have hb2' : b2 = expand_moves mv2 (Lbranch s :: k) := by
    simpa [expand_moves] using hb2
  rw [hb2'] at hb1
  simpa [expand_moves, List.append_assoc] using hb1

private theorem local_parse_tailcall
    (b : LTL.bblock) (mv : moves) (b1 : LTL.bblock)
    (sg : signature) (ros' : Sum CompCert4Lean.X86.Machregs.mreg ident)
    (tail : LTL.bblock)
    (hm : extract_moves_ext [] b = (mv, b1))
    (hhead : b1 = Ltailcall sg ros' :: tail) :
    ∃ k, wf_moves mv ∧ b = expand_moves mv (Ltailcall sg ros' :: k) := by
  rcases extract_moves_ext_sound b mv b1 hm with ⟨hwf, hb⟩
  rw [hhead] at hb
  exact ⟨tail, hwf, by simpa [expand_moves] using hb⟩

private theorem local_parse_builtin
    (b : LTL.bblock) (mv1 : moves) (b1 : LTL.bblock)
    (ef : external_function)
    (args' : List (builtin_arg CompCert4Lean.Backend.Locations.loc)) (res' : builtin_res CompCert4Lean.X86.Machregs.mreg)
    (mv2 : moves) (b2 b3 : LTL.bblock) (s : RTL.node)
    (hm1 : extract_moves [] b = (mv1, b1))
    (hhead : b1 = Lbuiltin ef args' res' :: b2)
    (hm2 : extract_moves [] b2 = (mv2, b3))
    (hs : check_succ s b3 = true) :
    ∃ k, wf_moves mv1 ∧ wf_moves mv2 ∧
      b = expand_moves mv1
        (Lbuiltin ef args' res' :: expand_moves mv2 (Lbranch s :: k)) := by
  rcases extract_moves_sound b mv1 b1 hm1 with ⟨hwf1, hb1⟩
  rcases extract_moves_sound b2 mv2 b3 hm2 with ⟨hwf2, hb2⟩
  rcases check_succ_sound s b3 hs with ⟨k, hk⟩
  subst b3
  rw [hhead] at hb1
  refine ⟨k, hwf1, hwf2, ?_⟩
  have hb2' : b2 = expand_moves mv2 (Lbranch s :: k) := by
    simpa [expand_moves] using hb2
  rw [hb2'] at hb1
  simpa [expand_moves, List.append_assoc] using hb1

private theorem local_pair_instr : pair_instr_block_soundStatement := by
  intro i b bsh hpair
  cases i with
  | Inop s =>
      cases hm : extract_moves [] b with
      | mk mv b1 =>
          simp [pair_instr_block, hm] at hpair
          rcases hpair with ⟨hsucc, rfl⟩
          rcases local_parse_branch b mv b1 s hm hsucc with ⟨k, hwf, hb⟩
          rw [hb]
          exact ebs_nop mv s k hwf
  | Iop op args res s =>
      cases hc : classify_operation op args with
      | operation_Omove arg =>
          cases hm : extract_moves [] b with
          | mk mv b1 =>
              simp [pair_instr_block, hc, hm] at hpair
              rcases hpair with ⟨hsucc, rfl⟩
              rcases local_parse_branch b mv b1 s hm hsucc with ⟨k, hwf, hb⟩
              rw [hb]
              exact ebs_move arg res mv s k hwf
      | operation_Omakelong arg1 arg2 =>
          simp [pair_instr_block, hc, CompCert4Lean.X86_64.Archi.splitlong] at hpair
          exact local_pair_Iop Omakelong [arg1, arg2] res s b bsh hpair
      | operation_Olowlong arg =>
          simp [pair_instr_block, hc, CompCert4Lean.X86_64.Archi.splitlong] at hpair
          exact local_pair_Iop Olowlong [arg] res s b bsh hpair
      | operation_Ohighlong arg =>
          simp [pair_instr_block, hc, CompCert4Lean.X86_64.Archi.splitlong] at hpair
          exact local_pair_Iop Ohighlong [arg] res s b bsh hpair
      | operation_other _ _ =>
          simp [pair_instr_block, hc] at hpair
          exact local_pair_Iop op args res s b bsh hpair
  | Iload chunk addr args dst s =>
      cases hm1 : extract_moves [] b with
      | mk mv1 b1 =>
          cases hb1 : b1 with
          | nil =>
              simp [pair_instr_block, hm1, hb1,
                CompCert4Lean.X86_64.Archi.splitlong,
                CompCert4Lean.X86_64.Archi.ptr64, check_succ] at hpair
          | cons hd b2 =>
              cases hd with
              | Lload chunk' addr' args' dst' =>
                  cases hm2 : extract_moves [] b2 with
                  | mk mv2 b3 =>
                      cases hchunk : chunk_eq chunk chunk' with
                      | left hchunkEq =>
                          cases haddr : eq_addressing addr addr' with
                          | left haddrEq =>
                              cases hs : check_succ s b3 with
                              | false =>
                                  simp [pair_instr_block, hm1, hb1, hm2,
                                    CompCert4Lean.X86_64.Archi.splitlong,
                                    CompCert4Lean.X86_64.Archi.ptr64,
                                    hchunk, haddr, hs] at hpair
                              | true =>
                                  simp [pair_instr_block, hm1, hb1, hm2,
                                    CompCert4Lean.X86_64.Archi.splitlong,
                                    CompCert4Lean.X86_64.Archi.ptr64,
                                    hchunk, haddr, hs] at hpair
                                  rcases hpair with ⟨_, hshape⟩
                                  cases hshape
                                  subst b1
                                  rcases local_parse_load b mv1 (Lload chunk' addr' args' dst' :: b2)
                                    chunk' addr' args' dst' mv2 b2 b3 s hm1 (by rfl) hm2 hs with
                                    ⟨k, hwf1, hwf2, hb⟩
                                  subst chunk'
                                  subst addr'
                                  rw [hb]
                                  exact ebs_load chunk addr args dst mv1 args' dst' mv2 s k hwf1 hwf2
                          | right haddrNe =>
                              simp [pair_instr_block, hm1, hb1, hm2,
                                CompCert4Lean.X86_64.Archi.splitlong,
                                CompCert4Lean.X86_64.Archi.ptr64,
                                hchunk, haddr] at hpair
                              rcases hpair with ⟨⟨⟨_, haddrbad⟩, _⟩, _⟩
                              change false = true at haddrbad
                              cases haddrbad
                      | right hchunkNe =>
                          simp [pair_instr_block, hm1, hb1, hm2,
                            CompCert4Lean.X86_64.Archi.splitlong,
                            CompCert4Lean.X86_64.Archi.ptr64,
                            hchunk] at hpair
                          rcases hpair with ⟨⟨⟨hchunkbad, _⟩, _⟩, _⟩
                          change false = true at hchunkbad
                          cases hchunkbad
              | _ =>
                  simp [pair_instr_block, hm1, hb1,
                    CompCert4Lean.X86_64.Archi.splitlong,
                    CompCert4Lean.X86_64.Archi.ptr64] at hpair
                  rcases hpair with ⟨hsucc, hshape⟩
                  cases hshape
                  subst b1
                  rcases local_parse_branch b mv1 _ s hm1 hsucc with ⟨k, hwf, hb⟩
                  rw [hb]
                  exact ebs_load_dead chunk addr args dst mv1 s k hwf

  | Istore chunk addr args src s =>
      cases hm1 : extract_moves [] b with
      | mk mv1 b1 =>
          cases hb1 : b1 with
          | nil =>
              simp [pair_instr_block, hm1, hb1,
                CompCert4Lean.X86_64.Archi.splitlong,
                CompCert4Lean.X86_64.Archi.ptr64] at hpair
          | cons hd b2 =>
              cases hd with
              | Lstore chunk' addr' args' src' =>
                  cases hchunk : chunk_eq chunk chunk' with
                  | left hchunkEq =>
                      cases haddr : eq_addressing addr addr' with
                      | left haddrEq =>
                          cases hs : check_succ s b2 with
                          | false =>
                              simp [pair_instr_block, hm1, hb1,
                                CompCert4Lean.X86_64.Archi.splitlong,
                                CompCert4Lean.X86_64.Archi.ptr64,
                                hchunk, haddr, hs] at hpair
                          | true =>
                              simp [pair_instr_block, hm1, hb1,
                                CompCert4Lean.X86_64.Archi.splitlong,
                                CompCert4Lean.X86_64.Archi.ptr64,
                                hchunk, haddr, hs] at hpair
                              rcases hpair with ⟨_, hshape⟩
                              cases hshape
                              subst b1
                              rcases local_parse_store b mv1 (Lstore chunk' addr' args' src' :: b2)
                                chunk' addr' args' src' b2 s hm1 (by rfl) hs with
                                ⟨k, hwf1, hb⟩
                              subst chunk'
                              subst addr'
                              rw [hb]
                              exact ebs_store chunk addr args src mv1 args' src' s k hwf1
                      | right haddrNe =>
                          simp [pair_instr_block, hm1, hb1,
                            CompCert4Lean.X86_64.Archi.splitlong,
                            CompCert4Lean.X86_64.Archi.ptr64,
                            hchunk, haddr] at hpair
                          rcases hpair with ⟨⟨⟨_, haddrbad⟩, _⟩, _⟩
                          change false = true at haddrbad
                          cases haddrbad
                  | right hchunkNe =>
                      simp [pair_instr_block, hm1, hb1,
                        CompCert4Lean.X86_64.Archi.splitlong,
                        CompCert4Lean.X86_64.Archi.ptr64,
                        hchunk] at hpair
                      rcases hpair with ⟨⟨⟨hchunkbad, _⟩, _⟩, _⟩
                      change false = true at hchunkbad
                      cases hchunkbad
              | _ =>
                  simp [pair_instr_block, hm1, hb1,
                    CompCert4Lean.X86_64.Archi.splitlong,
                    CompCert4Lean.X86_64.Archi.ptr64] at hpair

  | Icall sg ros args res s =>
      cases hm1 : extract_moves_ext [] b with
      | mk mv1 b1 =>
          cases hb1 : b1 with
          | nil =>
              simp [pair_instr_block, hm1, hb1] at hpair
          | cons hd b2 =>
              cases hd with
              | Lcall sg' ros' =>
                  cases hm2 : extract_moves_ext [] b2 with
                  | mk mv2 b3 =>
                      cases hsg : signature_eq sg sg' with
                      | left hsgEq =>
                          cases hs : check_succ s b3 with
                          | false =>
                              simp [pair_instr_block, hm1, hb1, hm2, hsg, hs] at hpair
                          | true =>
                              simp [pair_instr_block, hm1, hb1, hm2, hsg, hs] at hpair
                              rcases hpair with ⟨_, hshape⟩
                              cases hshape
                              subst b1
                              rcases local_parse_call b mv1 (Lcall sg' ros' :: b2)
                                sg' ros' mv2 b2 b3 s hm1 (by rfl) hm2 hs with
                                ⟨k, hwf1, hwf2, hb⟩
                              subst sg'
                              rw [hb]
                              exact ebs_call sg ros args res mv1 ros' mv2 s k hwf1 hwf2
                      | right hsgNe =>
                          simp [pair_instr_block, hm1, hb1, hm2, hsg] at hpair
                          rcases hpair with ⟨⟨hbad, _⟩, _⟩
                          change false = true at hbad
                          cases hbad
              | _ =>
                  simp [pair_instr_block, hm1, hb1] at hpair

  | Itailcall sg ros args =>
      cases hm : extract_moves_ext [] b with
      | mk mv b1 =>
          cases hb1 : b1 with
          | nil => simp [pair_instr_block, hm, hb1] at hpair
          | cons hd tail =>
              cases hd with
              | Ltailcall sg' ros' =>
                  cases hsg : signature_eq sg sg' with
                  | left hsgEq =>
                      simp [pair_instr_block, hm, hb1, hsg] at hpair
                      rcases hpair with ⟨_, hshape⟩
                      cases hshape
                      subst b1
                      rcases local_parse_tailcall b mv (Ltailcall sg' ros' :: tail)
                        sg' ros' tail hm (by rfl) with ⟨k, hwf, hb⟩
                      subst sg'
                      rw [hb]
                      exact ebs_tailcall sg ros args mv ros' k hwf
                  | right hsgNe =>
                      simp [pair_instr_block, hm, hb1, hsg] at hpair
                      rcases hpair with ⟨hbad, _⟩
                      change false = true at hbad
                      cases hbad
              | _ => simp [pair_instr_block, hm, hb1] at hpair

  | Ibuiltin ef args res s =>
      cases hm1 : extract_moves [] b with
      | mk mv1 b1 =>
          cases hb1 : b1 with
          | nil => simp [pair_instr_block, hm1, hb1] at hpair
          | cons hd b2 =>
              cases hd with
              | Lbuiltin ef' args' res' =>
                  cases hm2 : extract_moves [] b2 with
                  | mk mv2 b3 =>
                      cases hef : external_function_eq ef ef' with
                      | left hefEq =>
                          cases hs : check_succ s b3 with
                          | false => simp [pair_instr_block, hm1, hb1, hm2, hef, hs] at hpair
                          | true =>
                              simp [pair_instr_block, hm1, hb1, hm2, hef, hs] at hpair
                              rcases hpair with ⟨_, hshape⟩
                              cases hshape
                              subst b1
                              rcases local_parse_builtin b mv1 (Lbuiltin ef' args' res' :: b2)
                                ef' args' res' mv2 b2 b3 s hm1 (by rfl) hm2 hs with
                                ⟨k, hwf1, hwf2, hb⟩
                              subst ef'
                              rw [hb]
                              exact ebs_builtin ef args res mv1 args' res' mv2 s k hwf1 hwf2
                      | right hefNe =>
                          simp [pair_instr_block, hm1, hb1, hm2, hef] at hpair
                          rcases hpair with ⟨⟨hbad, _⟩, _⟩
                          change false = true at hbad
                          cases hbad
              | _ => simp [pair_instr_block, hm1, hb1] at hpair

  | Icond cond args s1 s2 =>
      cases hm : extract_moves [] b with
      | mk mv b1 =>
          cases hb1 : b1 with
          | nil => simp [pair_instr_block, hm, hb1] at hpair
          | cons hd tail =>
              cases hd with
              | Lcond cond' args' s1' s2' =>
                  cases hcond : eq_condition cond cond' with
                  | left hcondEq =>
                      cases hs1 : CompCert4Lean.Lib.Coqlib.peq s1 s1' with
                      | left hs1Eq =>
                          cases hs2 : CompCert4Lean.Lib.Coqlib.peq s2 s2' with
                          | left hs2Eq =>
                              simp [pair_instr_block, hm, hb1, hcond, hs1, hs2] at hpair
                              rcases hpair with ⟨_, hshape⟩
                              cases hshape
                              subst cond'
                              subst s1'
                              subst s2'
                              rcases extract_moves_sound b mv b1 hm with ⟨hwf, hb⟩
                              rw [hb1] at hb
                              rw [hb]
                              exact ebs_cond cond args mv args' s1 s2 tail hwf
                          | right hs2Ne =>
                              simp [pair_instr_block, hm, hb1, hcond, hs1, hs2] at hpair
                              rcases hpair with ⟨⟨⟨_, _⟩, hbad⟩, _⟩
                              change false = true at hbad
                              cases hbad
                      | right hs1Ne =>
                          simp [pair_instr_block, hm, hb1, hcond, hs1] at hpair
                          rcases hpair with ⟨⟨⟨_, hbad⟩, _⟩, _⟩
                          change false = true at hbad
                          cases hbad
                  | right hcondNe =>
                      simp [pair_instr_block, hm, hb1, hcond] at hpair
                      rcases hpair with ⟨⟨⟨hbad, _⟩, _⟩, _⟩
                      change false = true at hbad
                      cases hbad
              | _ => simp [pair_instr_block, hm, hb1] at hpair
  | Ijumptable arg tbl =>
      cases hm : extract_moves [] b with
      | mk mv b1 =>
          cases hb1 : b1 with
          | nil => simp [pair_instr_block, hm, hb1] at hpair
          | cons hd tail =>
              cases hd with
              | Ljumptable arg' tbl' =>
                  cases htbl : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.list_eq_dec peq tbl tbl' with
                  | left htblEq =>
                      simp [pair_instr_block, hm, hb1, htbl] at hpair
                      rcases hpair with ⟨_, hshape⟩
                      cases hshape
                      rcases extract_moves_sound b mv b1 hm with ⟨hwf, hb⟩
                      rw [hb1] at hb
                      rw [hb]
                      subst tbl'
                      exact ebs_jumptable arg mv arg' tbl tail hwf
                  | right htblNe =>
                      simp [pair_instr_block, hm, hb1, htbl] at hpair
                      rcases hpair with ⟨hbad, _⟩
                      change false = true at hbad
                      cases hbad
              | _ => simp [pair_instr_block, hm, hb1] at hpair
  | Ireturn optarg =>
      cases hm : extract_moves_ext [] b with
      | mk mv b1 =>
          cases hb1 : b1 with
          | nil => simp [pair_instr_block, hm, hb1] at hpair
          | cons hd tail =>
              cases hd with
              | Lreturn =>
                  simp [pair_instr_block, hm, hb1] at hpair
                  cases hpair
                  rcases extract_moves_ext_sound b mv b1 hm with ⟨hwf, hb⟩
                  rw [hb1] at hb
                  rw [hb]
                  exact ebs_return optarg mv tail hwf
              | _ => simp [pair_instr_block, hm, hb1] at hpair

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Lib.Maps

 theorem matching_instr_block : matching_instr_blockStatement := by
  intro f1 f2 pc bsh i hpair hcode
  unfold pair_codes at hpair
  have hg := CompCert4Lean.Lib.Maps.PTree.gcombine_proof
    (A := RTL.instruction) (B := LTL.bblock) (C := block_shape)
    (f := fun oi ob =>
      match oi, ob with
      | some i, some b => pair_instr_block i b
      | _, _ => none) (by rfl) f1.fn_code f2.fn_code pc
  have hpair' :
      (match PTree.get pc f1.fn_code, PTree.get pc f2.fn_code with
       | some i, some b => pair_instr_block i b
       | _, _ => none) = some bsh := by
    calc
      (match PTree.get pc f1.fn_code, PTree.get pc f2.fn_code with
       | some i, some b => pair_instr_block i b
       | _, _ => none) =
          PTree.get pc (PTree.combine
            (fun oi ob =>
              match oi, ob with
              | some i, some b => pair_instr_block i b
              | _, _ => none)
            f1.fn_code f2.fn_code) := hg.symm
      _ = some bsh := hpair
  rw [hcode] at hpair'
  cases hblock : PTree.get pc f2.fn_code with
  | none =>
      simp [hblock] at hpair'
  | some b =>
      refine ⟨b, rfl, ?_⟩
      apply local_pair_instr i b bsh
      simpa [hblock] using hpair'

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values

theorem subst_reg_kind_satisf_makelong :
    subst_reg_kind_satisf_makelongStatement := by
  intro src1 src2 dst rs ls e e1 e2 hunc hsat
  unfold satisf at hsat ⊢
  intro q hq
  rcases in_subst_reg_kind dst .High src1 .Full q e hq with hhigh | hsame
  · rcases hhigh with ⟨hpair, hmem⟩
    rcases in_subst_reg_kind dst .Low src2 .Full
        { ekind := .Full, ereg := src1, eloc := q.eloc } e1 hmem with
      hlow | hmem'
    · have hkind : (equation_kind.Full) = .Low := congrArg Prod.snd hlow.1
      cases hkind
    · have hreg : q.ereg = dst := congrArg Prod.fst hpair
      have hkind : q.ekind = .High := congrArg Prod.snd hpair
      rw [hreg, hkind, Regmap.gss_proof val dst
        (Val.longofwords (Regmap.get src1 rs) (Regmap.get src2 rs)) rs]
      exact ap_lessdef_trans
        (val_hiword_longofwords (Regmap.get src1 rs) (Regmap.get src2 rs))
        (hsat _ hmem')
  · rcases in_subst_reg_kind dst .Low src2 .Full q e1 hsame with hlow | hmem
    · rcases hlow with ⟨hpair, hmem'⟩
      have hreg : q.ereg = dst := congrArg Prod.fst hpair
      have hkind : q.ekind = .Low := congrArg Prod.snd hpair
      rw [hreg, hkind, Regmap.gss_proof val dst
        (Val.longofwords (Regmap.get src1 rs) (Regmap.get src2 rs)) rs]
      exact ap_lessdef_trans
        (val_loword_longofwords (Regmap.get src1 rs) (Regmap.get src2 rs))
        (hsat _ hmem')
    · have hne : q.ereg ≠ dst := reg_unconstrained_sound dst e2 q hunc hmem
      rw [Regmap.gso_proof val q.ereg dst
        (Val.longofwords (Regmap.get src1 rs) (Regmap.get src2 rs)) rs hne]
      exact hsat q hmem

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation

theorem partial_fold_ind : partial_fold_indStatement := by
  intro A P f init final s hfold hEmpty hStep
  let g : EqSet2.elt → Option A → Option A := fun x oa =>
    match oa with
    | none => none
    | some a => f x a
  let Q := fun (s : EqSet2M.t) oa =>
    {h : match oa with
      | none => True
      | some a => P s a // True}
  have hQ := ESP2.fold_rec_proof (A := Option A) (P := Q) (f := g)
      (i := some init) (s := s)
      (by
        intro s' hs'
        exact ⟨hEmpty s' hs', trivial⟩)
      (by
        intro x oa s' s'' hx hnot hadd hPa
        cases oa with
        | none => exact ⟨trivial, trivial⟩
        | some a =>
            cases hfa : f x a with
            | none =>
                simp only [g, hfa]
                exact ⟨trivial, trivial⟩
            | some a' =>
                simp only [g, hfa]
                exact ⟨hStep x a a' s' s'' hx hnot hadd hfa hPa.1, trivial⟩)
  have hQ' : Q s (some final) := by
    rw [← hfold]
    change Q s (EqSet2.fold g s (some init))
    exact hQ
  exact hQ'.1

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers

private theorem ap_builtin_add_zero (x : Z) : zOfInt (intOfZ x + 0) = x := by
  simp [zOfInt_intOfZ]

private theorem ap_builtin_id_no_overlap (m : mem) :
    Mem.meminj_no_overlap inject_id m := by
  intro b1 b1' d1 b2 b2' d2 ofs1 ofs2 hne h1 h2 _ _
  have h1' : (b1, (.Z0 : Z)) = (b1', d1) := Option.some.inj h1
  have h2' : (b2, (.Z0 : Z)) = (b2', d2) := Option.some.inj h2
  cases h1'
  cases h2'
  exact Or.inl hne

private theorem ap_builtin_store_extends : Mem.store_within_extendsStatement := by
  intro chunk m1 m2 b ofs v1 n1 v2 hext hs hv
  obtain ⟨n2, hs2, hi⟩ := Mem.store_mapped_inj inject_id chunk m1 b ofs v1 n1
    m2 b .Z0 v2 hext.mext_inj hs (ap_builtin_id_no_overlap m1) rfl
    ((val_inject_id v1 v2).mpr hv)
  change Mem.store chunk m2 b (zOfInt (intOfZ ofs + 0)) v2 = some n2 at hs2
  rw [ap_builtin_add_zero] at hs2
  refine ⟨n2, hs2, ?_⟩
  constructor
  · rw [Mem.nextblock_store _ _ _ _ _ _ hs, Mem.nextblock_store _ _ _ _ _ _ hs2]
    exact hext.mext_next
  · exact hi
  · intro b' ofs' k p hp
    obtain hp | hn := hext.mext_perm_inv b' ofs' k p
      (Mem.perm_store_2 _ _ _ _ _ _ hs2 _ _ _ _ hp)
    · exact Or.inl (Mem.perm_store_1 _ _ _ _ _ _ hs _ _ _ _ hp)
    · exact Or.inr (fun h => hn (Mem.perm_store_2 _ _ _ _ _ _ hs _ _ _ _ h))

private theorem ap_builtin_storebytes_extends : Mem.storebytes_within_extendsStatement := by
  intro m1 m2 b ofs bytes1 n1 bytes2 hext hs hv
  obtain ⟨n2, hs2, hi⟩ := Mem.storebytes_mapped_inj inject_id m1 b ofs bytes1 n1
    m2 b .Z0 bytes2 hext.mext_inj hs (ap_builtin_id_no_overlap m1) rfl hv
  change Mem.storebytes m2 b (zOfInt (intOfZ ofs + 0)) bytes2 = some n2 at hs2
  rw [ap_builtin_add_zero] at hs2
  refine ⟨n2, hs2, ?_⟩
  constructor
  · rw [Mem.nextblock_storebytes _ _ _ _ _ hs, Mem.nextblock_storebytes _ _ _ _ _ hs2]
    exact hext.mext_next
  · exact hi
  · intro b' ofs' k p hp
    obtain hp | hn := hext.mext_perm_inv b' ofs' k p
      (Mem.perm_storebytes_2 _ _ _ _ _ hs2 _ _ _ _ hp)
    · exact Or.inl (Mem.perm_storebytes_1 _ _ _ _ _ hs _ _ _ _ hp)
    · exact Or.inr (fun h => hn (Mem.perm_storebytes_2 _ _ _ _ _ hs _ _ _ _ h))

private theorem ap_builtin_free_extends : Mem.free_parallel_extendsStatement := by
  intro m1 m2 b lo hi n1 hext hf
  have hr := Mem.range_perm_inj inject_id m1 m2 b lo hi Cur Freeable b .Z0
    hext.mext_inj (Mem.free_range_perm _ _ _ _ _ hf) rfl
  change Mem.range_perm m2 b (zOfInt (intOfZ lo + 0))
    (zOfInt (intOfZ hi + 0)) Cur Freeable at hr
  rw [ap_builtin_add_zero, ap_builtin_add_zero] at hr
  obtain ⟨n2, hf2⟩ := Mem.range_perm_free m2 b lo hi hr
  refine ⟨n2, hf2, ?_⟩
  constructor
  · rw [Mem.nextblock_free _ _ _ _ _ hf, Mem.nextblock_free _ _ _ _ _ hf2]
    exact hext.mext_next
  · apply Mem.free_right_inj inject_id n1 m2 b lo hi n2
      (Mem.free_left_inj inject_id m1 m2 b lo hi n1 hext.mext_inj hf) hf2
    intro b' delta ofs k p hmap hp hb
    have heq : (b', (.Z0 : Z)) = (b, delta) := Option.some.inj hmap
    cases heq
    change intOfZ lo ≤ intOfZ (zOfInt (intOfZ ofs + 0)) ∧
      intOfZ (zOfInt (intOfZ ofs + 0)) < intOfZ hi at hb
    rw [ap_builtin_add_zero] at hb
    exact Mem.perm_free_2 _ _ _ _ _ hf _ _ _ hb hp
  · intro b' ofs k p hp
    obtain hp1 | hn := hext.mext_perm_inv b' ofs k p
      (Mem.perm_free_3 _ _ _ _ _ hf2 _ _ _ _ hp)
    · obtain ⟨hb, hlo, hhi⟩ | hp1' := Mem.perm_free_inv _ _ _ _ _ hf _ _ _ _ hp1
      · subst b'
        exact False.elim (Mem.perm_free_2 _ _ _ _ _ hf2 _ _ _ ⟨hlo, hhi⟩ hp)
      · exact Or.inl hp1'
    · exact Or.inr (fun h => hn (Mem.perm_free_3 _ _ _ _ _ hf _ _ _ _ h))

private theorem ap_builtin_alloc_extends
    (m1 m2 : mem) (lo hi : Z) (n1 : mem) (b : block)
    (hext : Mem.extends m1 m2) (ha : Mem.alloc m1 lo hi = (n1, b)) :
    ∃ n2, Mem.alloc m2 lo hi = (n2, b) ∧ Mem.extends n1 n2 := by
  cases ha2 : Mem.alloc m2 lo hi with
  | mk n2 b2 =>
    have hb : b2 = b := by
      rw [Mem.alloc_result _ _ _ _ _ ha2, Mem.alloc_result _ _ _ _ _ ha]
      exact hext.mext_next.symm
    subst b2
    have hperm : ∀ ofs k p, intOfZ lo ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi → Mem.perm n2 b ofs k p := by
      intro ofs k p hr
      exact Mem.perm_implies _ _ _ _ _ _
        (Mem.perm_alloc_2 _ _ _ _ _ ha2 _ _ hr) (perm_F_any p)
    refine ⟨n2, rfl, ?_⟩
    constructor
    · rw [Mem.nextblock_alloc _ _ _ _ _ ha, Mem.nextblock_alloc _ _ _ _ _ ha2,
        hext.mext_next]
    · apply Mem.alloc_left_mapped_inj inject_id m1 n2 lo hi n1 b b .Z0
        (Mem.alloc_right_inj inject_id m1 m2 lo hi b n2 hext.mext_inj ha2) ha
        (Mem.valid_new_block _ _ _ _ _ ha2)
      · intro chunk _
        refine ⟨.Z0, ?_⟩
        apply intOfZ_injective
        change 0 = intOfZ (zOfInt (intOfZ (align_chunk chunk) * 0))
        rw [intOfZ_zOfInt]
        simp
      · intro ofs k p hr
        change Mem.perm n2 b (zOfInt (intOfZ ofs + 0)) k p
        rw [ap_builtin_add_zero]
        exact hperm ofs k p hr
      · rfl
    · intro b' ofs k p hp
      by_cases hb : b' = b
      · subst b'
        apply Or.inl
        exact Mem.perm_implies _ _ _ _ _ _
          (Mem.perm_alloc_2 _ _ _ _ _ ha _ _
            (Mem.perm_alloc_3 _ _ _ _ _ ha2 _ _ _ hp)) (perm_F_any p)
      · obtain hp1 | hn := hext.mext_perm_inv b' ofs k p
          (Mem.perm_alloc_4 _ _ _ _ _ ha2 _ _ _ _ hp hb)
        · exact Or.inl (Mem.perm_alloc_1 _ _ _ _ _ ha _ _ _ _ hp1)
        · exact Or.inr (fun h => hn (Mem.perm_alloc_4 _ _ _ _ _ ha _ _ _ _ h hb))

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Lib.Integers

private theorem ap_builtin_lessdef_one {v : val} {vs : List val}
    (h : Val.lessdef_list [v] vs) :
    ∃ v', vs = [v'] ∧ Val.lessdef v v' := by
  cases h with
  | lessdef_list_cons v1 v2 vl1 vl2 hv ht =>
    cases ht
    exact ⟨v2, rfl, hv⟩

private theorem ap_builtin_lessdef_two {v w : val} {vs : List val}
    (h : Val.lessdef_list [v, w] vs) :
    ∃ v' w', vs = [v', w'] ∧ Val.lessdef v v' ∧ Val.lessdef w w' := by
  cases h with
  | lessdef_list_cons v1 v2 vl1 vl2 hv ht =>
    obtain ⟨w', hw, hl⟩ := ap_builtin_lessdef_one ht
    subst vl2
    exact ⟨v2, w', rfl, hv, hl⟩

private theorem ap_builtin_call_extends
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) (ge : Senv.t)
    (vargs : List val) (m1 : mem) (t : trace) (vres : val) (m2 m1' : mem)
    (vargs' : List val)
    (hc : external_call xi ef ge vargs m1 t vres m2)
    (hext : Mem.extends m1 m1') (hargs : Val.lessdef_list vargs vargs') :
    ∃ vres' m2', external_call xi ef ge vargs' m1' t vres' m2' ∧
      Val.lessdef vres vres' ∧ Mem.extends m2 m2' := by
  cases ef with
  | EF_external name sg =>
    obtain ⟨v', m', hcall, hval, hmem, _⟩ :=
      (external_functions_properties xi name sg).ec_mem_extends
        ge vargs m1 t vres m2 m1' vargs' hc hext hargs
    exact ⟨v', m', hcall, hval, hmem⟩
  | EF_inline_asm text sg clobbers =>
    obtain ⟨v', m', hcall, hval, hmem, _⟩ :=
      (inline_assembly_properties xi text sg).ec_mem_extends
        ge vargs m1 t vres m2 m1' vargs' hc hext hargs
    exact ⟨v', m', hcall, hval, hmem⟩
  | EF_builtin name sg | EF_runtime name sg =>
    change builtin_or_external_sem xi name sg ge vargs m1 t vres m2 at hc
    change ∃ vres' m2', builtin_or_external_sem xi name sg ge vargs' m1' t vres' m2' ∧
      Val.lessdef vres vres' ∧ Mem.extends m2 m2'
    unfold builtin_or_external_sem at hc ⊢
    cases hlookup : CompCert4Lean.Common.Builtins.lookup_builtin_function name sg with
    | some bf =>
      rw [hlookup] at hc
      obtain ⟨v', hcall, hval⟩ := known_builtin_sem_lessdef bf ge vargs m1 t vres m2
        ge vargs' m1' hc hargs
      cases hc
      exact ⟨v', m1', hcall, hval, hext⟩
    | none =>
      rw [hlookup] at hc
      obtain ⟨v', m', hcall, hval, hmem, _⟩ :=
        (external_functions_properties xi name sg).ec_mem_extends
          ge vargs m1 t vres m2 m1' vargs' hc hext hargs
      exact ⟨v', m', hcall, hval, hmem⟩
  | EF_vload chunk =>
    cases hc with
    | volatile_load_sem_intro b ofs m t v hl =>
      obtain ⟨vptr, rfl, hp⟩ := ap_builtin_lessdef_one hargs
      cases hp
      obtain ⟨v', hload, hval⟩ := volatile_load_extends ge chunk m1 b ofs t vres m1' hl hext
      exact ⟨v', m1', volatile_load_sem_intro b ofs m1' t v' hload, hval, hext⟩
  | EF_vstore chunk =>
    cases hc with
    | volatile_store_sem_intro b ofs m v t n hs =>
      obtain ⟨vptr, v', rfl, hp, hv⟩ := ap_builtin_lessdef_two hargs
      cases hp
      cases hs with
      | volatile_store_vol id ev v hvol hfind hmatch =>
        refine ⟨Vundef, m1', volatile_store_sem_intro b ofs m1' v' _ m1' ?_,
          Val.lessdef_refl _, hext⟩
        exact volatile_store_vol chunk m1' b ofs id ev v' hvol hfind
          (eventval_match_lessdef ge ev (type_of_chunk chunk) _ _ hmatch
            (Val.load_result_lessdef chunk v v' hv))
      | volatile_store_nonvol =>
        rename_i hvol hstore
        obtain ⟨n', hstore', hext'⟩ := ap_builtin_store_extends chunk m1 m1' b
          (Ptrofs.unsigned ofs) v m2 v' hext hstore hv
        exact ⟨Vundef, n', volatile_store_sem_intro b ofs m1' v' _ n'
          (volatile_store_nonvol chunk m1' b ofs v' n' hvol hstore'),
          Val.lessdef_refl _, hext'⟩
  | EF_malloc =>
    cases hc with
    | extcall_malloc_sem_intro sz m n b n' ha hs =>
      obtain ⟨v', rfl, hv⟩ := ap_builtin_lessdef_one hargs
      change Val.lessdef (.Vlong _) v' at hv
      cases hv
      obtain ⟨n2, ha2, hext2⟩ := ap_builtin_alloc_extends m1 m1' _ _ n b hext ha
      obtain ⟨n2', hs2, hext2'⟩ := ap_builtin_store_extends _ n n2 b _ _ m2 _
        hext2 hs (Val.lessdef_refl _)
      exact ⟨Vptr b Ptrofs.zero, n2', extcall_malloc_sem_intro sz m1' n2 b n2' ha2 hs2,
        Val.lessdef_refl _, hext2'⟩
  | EF_free =>
    cases hc with
    | extcall_free_sem_ptr b lo sz m n hl hf =>
      obtain ⟨v', rfl, hv⟩ := ap_builtin_lessdef_one hargs
      cases hv
      obtain ⟨sz', hl', hsz⟩ := Mem.load_extends _ m1 m1' b _ _ hext hl
      change Val.lessdef (.Vlong _) sz' at hsz
      cases hsz
      obtain ⟨n', hf', hext'⟩ := ap_builtin_free_extends m1 m1' b _ _ m2 hext hf
      exact ⟨Vundef, n', extcall_free_sem_ptr b lo sz m1' n' hl' hf',
        Val.lessdef_refl _, hext'⟩
    | extcall_free_sem_null m =>
      obtain ⟨v', rfl, hv⟩ := ap_builtin_lessdef_one hargs
      change Val.lessdef (.Vlong _) v' at hv
      cases hv
      exact ⟨Vundef, m1', extcall_free_sem_null m1', Val.lessdef_refl _, hext⟩
  | EF_memcpy sz al =>
    cases hc with
    | extcall_memcpy_sem_intro bd od bs os m bytes n hal hsz hsa hsrc hdst hno hl hs =>
      obtain ⟨v1, v2, rfl, hv1, hv2⟩ := ap_builtin_lessdef_two hargs
      cases hv1
      cases hv2
      obtain ⟨bytes', hl', hbytes⟩ := Mem.loadbytes_inj inject_id m1 m1' sz bs
        (Ptrofs.unsigned os) bs .Z0 bytes hext.mext_inj hl rfl
      change Mem.loadbytes m1' bs (zOfInt (intOfZ (Ptrofs.unsigned os) + 0)) sz =
        some bytes' at hl'
      rw [ap_builtin_add_zero] at hl'
      obtain ⟨n', hs', hext'⟩ := ap_builtin_storebytes_extends m1 m1' bd
        (Ptrofs.unsigned od) bytes m2 bytes' hext hs hbytes
      exact ⟨Vundef, n', extcall_memcpy_sem_intro bd od bs os m1' bytes' n'
        hal hsz hsa hsrc hdst hno hl' hs', Val.lessdef_refl _, hext'⟩
  | EF_annot kind text targs =>
    cases hc with
    | extcall_annot_sem_intro evs hm =>
      exact ⟨Vundef, m1', extcall_annot_sem_intro vargs' m1' evs
        (eventval_list_match_lessdef ge evs targs vargs hm vargs' hargs),
        Val.lessdef_refl _, hext⟩
  | EF_annot_val kind text targ =>
    cases hc with
    | extcall_annot_val_sem_intro v m ev hm =>
      obtain ⟨v', rfl, hv⟩ := ap_builtin_lessdef_one hargs
      exact ⟨v', m1', extcall_annot_val_sem_intro v' m1' ev
        (eventval_match_lessdef ge ev targ vres v' hm hv), hv, hext⟩
  | EF_debug kind text targs =>
    cases hc
    exact ⟨Vundef, m1', extcall_debug_sem_intro vargs' m1', Val.lessdef_refl _, hext⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs

theorem add_equations_builtin_eval
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    add_equations_builtin_evalStatement := by
  intro xi ef env args args' e1 e2 m1 m1' rs ls ge sp vargs t vres m2
    hwt hrun hext hsat heval hcall
  have hdefault : add_equations_builtin_args env args args' e1 = some e2 →
      satisf rs ls e1 ∧
      ∃ vargs' vres' m2',
        eval_builtin_args (Genv.to_senv ge) ls sp m1' args' vargs' ∧
        external_call xi ef (Genv.to_senv ge) vargs' m1' t vres' m2' ∧
        Val.lessdef vres vres' ∧ Mem.extends m2 m2' := by
    intro hargs
    refine ⟨add_equations_builtin_args_satisf env rs ls args args' e1 e2 hargs hsat, ?_⟩
    obtain ⟨vargs', heval', hless⟩ := add_equations_builtin_args_lessdef env ge sp rs ls
      m1 m1' args vargs heval args' e1 e2 hargs hsat hwt hext
    obtain ⟨vres', m2', hcall', hres, hmem⟩ := ap_builtin_call_extends xi ef
      (Genv.to_senv ge) vargs m1 t vres m2 m1' vargs' hcall hext hless
    exact ⟨vargs', vres', m2', heval', hcall', hres, hmem⟩
  cases ef <;> try exact hdefault hrun
  case EF_debug kind text targs =>
    refine ⟨add_equations_debug_args_satisf env rs ls args args' e1 e2 hrun hsat, ?_⟩
    obtain ⟨vargs', heval'⟩ := add_equations_debug_args_eval env ge sp rs ls m1 m1'
      args vargs heval args' e1 e2 hrun hsat hwt hext
    cases hcall
    exact ⟨vargs', Vundef, m1', heval', extcall_debug_sem_intro vargs' m1',
      Val.lessdef_refl _, hext⟩

end CompCert4Lean.Backend.Allocproof

namespace CompCert4Lean.Backend.Allocproof

open CompCert4Lean.Backend.Allocation
open CompCert4Lean.Backend.RTLtyping
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps

theorem transf_function_inv : transf_function_invStatement := by
  intro cfg oracle f tf h
  unfold CompCert4Lean.Backend.Allocation.transf_function at h
  cases ht : CompCert4Lean.Backend.RTLtyping.type_function cfg f with
  | Error msg => simp [ht] at h
  | OK env =>
      cases ho : CompCert4Lean.Backend.Allocation.regalloc oracle f with
      | Error msg => simp [ht, ho] at h
      | OK tf0 =>
          cases hc : CompCert4Lean.Backend.Allocation.check_function cfg f tf0 env with
          | Error msg => simp [ht, ho, hc] at h
          | OK u =>
              simp [ht, ho, hc] at h
              cases h
              unfold CompCert4Lean.Backend.Allocation.check_function at hc
              cases ha : CompCert4Lean.Backend.Allocation.analyze cfg f env
                  (CompCert4Lean.Backend.Allocation.pair_codes f tf) with
              | none => simp [ha] at hc
              | some an =>
                  simp [ha] at hc
                  unfold CompCert4Lean.Backend.Allocation.check_entrypoints at hc
                  cases he : CompCert4Lean.Backend.Allocation.transfer cfg f env
                      (CompCert4Lean.Backend.Allocation.pair_codes f tf)
                      f.fn_entrypoint (PMap.get f.fn_entrypoint an) with
                  | Error msg => simp [he] at hc
                  | OK e1 =>
                      simp [he] at hc
                      cases hx : CompCert4Lean.Backend.Allocation.check_entrypoints_aux
                          cfg f tf env e1 with
                      | none => simp [hx] at hc
                      | some u' =>
                          simp [hx] at hc
                          unfold CompCert4Lean.Backend.Allocation.check_entrypoints_aux at hx
                          cases hp : CompCert4Lean.Backend.Allocation.pair_entrypoints f tf with
                          | none => simp [hp] at hx
                          | some mv =>
                              cases htm : CompCert4Lean.Backend.Allocation.track_moves env mv e1 with
                              | none => simp [hp, htm] at hx
                              | some e2 =>
                                  simp [hp, htm] at hx
                                  have hentry : ∃ k : List LTL.instruction,
                                      PTree.get tf.fn_entrypoint tf.fn_code =
                                        some (expand_moves mv (Lbranch f.fn_entrypoint :: k)) ∧
                                      wf_moves mv := by
                                    unfold CompCert4Lean.Backend.Allocation.pair_entrypoints at hp
                                    cases hcode : PTree.get tf.fn_entrypoint tf.fn_code with
                                    | none => simp [hcode] at hp
                                    | some b =>
                                        cases hm : extract_moves_ext [] b with
                                        | mk mv' b1 =>
                                            simp [hcode, hm] at hp
                                            cases hs : check_succ f.fn_entrypoint b1 with
                                            | false => simp [hs] at hp
                                            | true =>
                                                simp [hs] at hp
                                                cases hp
                                                rcases extract_moves_ext_sound b mv b1 hm with
                                                  ⟨hwf, hb⟩
                                                rcases check_succ_sound f.fn_entrypoint b1 hs with
                                                  ⟨k, hk⟩
                                                subst b1
                                                exact ⟨k, congrArg (fun x => some x) hb, hwf⟩
                                  rcases hentry with ⟨k, hcode, hmv⟩
                                  have hsig : f.fn_sig = tf.fn_sig := by
                                    have hbool := hx.2.2.2
                                    cases hs : signature_eq f.fn_sig tf.fn_sig with
                                    | left heq => exact heq
                                    | right hne => rw [hs] at hbool; cases hbool
                                  have hcompat :
                                      compat_entry f.fn_params
                                        (CompCert4Lean.Backend.Conventions.loc_parameters cfg tf.fn_sig) e2 = true := by
                                    simpa [hsig] using hx.1
                                  have hundef : can_undef CompCert4Lean.X86.Machregs.destroyed_at_function_entry e2 = true := by
                                    exact hx.2.1
                                  have hstack : f.fn_stacksize = tf.fn_stacksize := by
                                    have hbool := hx.2.2.1
                                    cases hs : CompCert4Lean.Lib.Coqlib.zeq f.fn_stacksize tf.fn_stacksize with
                                    | left heq => exact heq
                                    | right hne => rw [hs] at hbool; cases hbool
                                  exact transf_function_spec_intro env an mv k e1 e2
                                    (CompCert4Lean.Backend.RTLtyping.type_function_correct cfg f env ht)
                                    ha hcode hmv he htm hcompat hundef hstack hsig

end CompCert4Lean.Backend.Allocproof
