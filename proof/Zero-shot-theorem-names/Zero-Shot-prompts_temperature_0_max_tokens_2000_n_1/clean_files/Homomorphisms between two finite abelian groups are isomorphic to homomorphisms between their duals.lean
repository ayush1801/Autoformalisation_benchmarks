
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
theorem dual_hom_iso (G H : Type*) [group G] [group H] [fintype G] [fintype H] [decidable_eq G] [decidable_eq H] :
  (G →* H) ≃ (G^* →* H^*) :=
begin
  apply equiv.of_bijective (λ f, f.to_add_monoid_hom.to_linear_map)
    (λ f, f.to_add_monoid_hom.to_add_monoid_hom)
    (λ f, by { ext, simp [f.to_add_monoid_hom.to_linear_map, f.to_add_monoid_hom.to_add_monoid_hom] })
    (λ f, by { ext, simp [f.to_add_monoid_hom.to_linear_map, f.to_add_monoid_hom.to_add_monoid_hom] })

