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
