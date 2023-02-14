
import topology.basic
import topology.compact_open
import data.nat.prime
import data.real.basic
import data.real.irrational
import data.complex.basic
import data.fin.basic
import geometry.euclidean.basic
import analysis.inner_product_space.pi_L2
import algebra.group.defs
import algebra.field.basic
import combinatorics.configuration
import ring_theory.polynomial.basic
import group_theory.free_group
import combinatorics.simple_graph.basic
import ring_theory.integral_closure
import data.fintype.card
import category_theory.category.basic
import ring_theory.discrete_valuation_ring
import group_theory.torsion
import linear_algebra.matrix.charpoly.basic
import algebra.order.absolute_value
import analysis.convex.basic
import topology.uniform_space.uniform_convergence_topology
import topology.sequences
import analysis.normed.group.infinite_sum
import data.nat.choose.sum
import group_theory.specific_groups.cyclic
import group_theory.order_of_element
import analysis.mean_inequalities
import analysis.normed_space.banach
import topology.algebra.continuous_monoid_hom
import linear_algebra.matrix.symmetric
import analysis.inner_product_space.spectrum
import ring_theory.class_group
import ring_theory.dedekind_domain.basic
import ring_theory.principal_ideal_domain
import model_theory.satisfiability
import probability.integration
import ring_theory.simple_module
import category_theory.preadditive.schur
import representation_theory.maschke
import topology.paracompact
import combinatorics.simple_graph.coloring
--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
 
--OUTPUT 1
theorem dual_hom_iso {G H : Type*} [add_comm_group G] [add_comm_group H] [fintype G] [fintype H] {f : G → H} (hf : is_group_hom f) :
  (finsupp.total_on_dual f).comp (finsupp.total_on_dual f.to_add_monoid_hom) = f :=
begin
  ext,
  rw [finsupp.total_on_dual_apply, finsupp.total_on_dual_apply, finsupp.total_on_dual_apply],
  rw [finsupp.sum_apply, finsupp.sum_apply, finsupp.sum_apply],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, finsupp.sum_single_index],
  rw [finsupp.sum

--OUTPUT 2
theorem dual_hom_iso (G H : Type) [add_comm_group G] [add_comm_group H] [fintype G] [fintype H] [decidable_eq H] [decidable_eq G] (f : G →+* H) :
  (f.to_add_monoid_hom).to_linear_map.to_add_monoid_hom ≃ (f.to_add_monoid_hom).to_linear_map.to_add_monoid_hom :=
begin
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equiv,
  apply linear_equiv.symm,
  apply linear_equiv.to_add_monoid_hom_equ

--OUTPUT 3
theorem dual_hom_iso (G H : Type*) [add_comm_group G] [add_comm_group H] [fintype G] [fintype H] (f : G → H) [is_group_hom f] :
  (fintype.equiv_fin (fintype.dual G) (fintype.dual H)).to_fun ∘ (fintype.dual f) = fintype.dual (fintype.equiv_fin G H).to_fun ∘ f :=
begin
  ext x,
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply],
  rw [fintype.dual_equiv_fin_apply, fintype.dual_equiv_fin_apply, fintype.dual

