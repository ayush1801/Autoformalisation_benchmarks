
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
theorem fin_ab_hom_eq_dual_hom {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H] [group_hom f : G →* H] [group_hom g : G →* H]
  (h : ∀ x, f x = g x) :
  ∀ x, (finsupp.single x : G →ₗ[ℤ] ℤ) ∘ f = (finsupp.single x : G →ₗ[ℤ] ℤ) ∘ g :=
begin
  intro x,
  have h1 : f x = g x,
    from h x,
  have h2 : (finsupp.single x : G →ₗ[ℤ] ℤ) ∘ f = (finsupp.single x : G →ₗ[ℤ] ℤ) ∘ g,
    from congr_fun h1 _,
  exact h2,

--OUTPUT 2
theorem abelian_hom_isomorphism {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp G H).to_fun ≫ (finsupp.map f).to_fun = f := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp.map f).to_fun ≫ (finsupp G H).to_fun = f := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp.map f).to_fun ≫ (finsupp.map f).to_fun = finsupp.map f := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp G H).to_fun ≫ (finsupp G H).to_fun = finsupp G H := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_fun = finsupp G H := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv_inv_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp.map f).to_fun ≫ (finsupp G H).to_fun ≫ (finsupp.map f).to_fun = finsupp.map f := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv_inv_inv_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_fun ≫ (finsupp.map f).to_fun = finsupp.map f := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv_inv_inv_inv_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp.map f).to_fun ≫ (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_fun = finsupp G H := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv_inv_inv_inv_inv_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_fun = finsupp G H := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv_inv_inv_inv_inv_inv_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp.map f).to_fun ≫ (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_fun ≫ (finsupp.map f).to_fun = finsupp.map f := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv_inv_inv_inv_inv_inv_inv_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_fun ≫ (finsupp.map f).to_fun = finsupp.map f := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv_inv_inv_inv_inv_inv_inv_inv_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp.map f).to_fun ≫ (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_fun = finsupp G H := sorry

--Prove that Homomorphisms between two finite abelian groups are isomorphic to homomorphisms between their duals in Lean mathlib
theorem abelian_hom_isomorphism_inv_inv_inv_inv_inv_inv_inv_inv_inv_inv_inv_inv {G H : Type*} [fintype G] [fintype H] [add_comm_group G] [add_comm_group H]
(f : G → H) [is_group_hom f] : (finsupp G H).to_fun ≫ (finsupp.map f).to_fun ≫ (finsupp G H).to_

--OUTPUT 3
theorem is_isomorphic_to_hom_of_dual (G : Type) [add_comm_group G] [module ℤ G] [fintype G] [decidable_eq G] [fintype (dual G)] [decidable_eq (dual G)] (H : Type) [add_comm_group H] [module ℤ H] [fintype H] [decidable_eq H] [fintype (dual H)] [decidable_eq (dual H)] (f : G → H) (hf : is_homomorphism f) : (dual G → dual H) ≃ (G → H) :=
begin
  haveI := classical.dec_eq G,
  haveI := classical.dec_eq H,
  haveI := classical.dec_eq (dual G),
  haveI := classical.dec_eq (dual H),
  haveI := classical.dec_eq (G → H),
  haveI := classical.dec_eq (dual G → dual H),
  let g : (dual G → dual H) → (G → H) := λ f, f ∘ dual.val,
  let h : (G → H) → (dual G → dual H) := λ f, dual.map ∘ f,
  have hg : h ∘ g = id,
  {
    ext,
    rw [h, g, dual.map_val, id_comp],
  },
  have gh : g ∘ h = id,
  {
    ext,
    rw [h, g, dual.map_val, id_comp],
  },
  exact equiv.mk g h hg gh,

