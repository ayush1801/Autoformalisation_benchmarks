
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
theorem finite.abelian.hom_iso (G H : Type*) [group G] [group H] [fintype G] [fintype H] [fintype_mul_class G] [fintype_mul_class H]
[fintype_add_class G] [fintype_add_class H] [add_comm_group G] [add_comm_group H] [mul_comm_group G] [mul_comm_group H] :
    is_iso (λ g : G ≃ₗ[*] H, G ≃ₗ[*] H) := sorry

/-! #brief Prove that every finite abelian group is isomorphic to a finite direct sum of cyclic groups
-/
--Prove that every finite abelian group is isomorphic to a finite direct sum of cyclic groups
theorem finite.abelian.direct_sum_cyclic (G : Type*) [group G] [fintype G] [fintype_mul_class G] [fintype_add_class G]
[add_comm_group G] [mul_comm_group G] : ∃ n : ℕ, Π (A : G ^ n), ∃ (g : G), ∃ (f : G ^ n), A.prod g ∧ (is_unit f) ∧ is_iso f := sorry

/-! #brief Prove that any homomorphism between two finite abelian groups can be extended in a univorm way to a homomorphism between their direct sum
-/
--Prove that any homomorphism between two finite abelian groups can be extended in a univorm way to a homomorphism between their direct sum
theorem finite.abelian.ext (G H : Type*) [group G] [group H] [fintype G] [fintype H] [fintype_mul_class G] [fintype_mul_class H]
[fintype_add_class G] [fintype_add_class H] [add_comm_group G] [add_comm_group H] [mul_comm_group G] [mul_comm_group H] :
    ∀ f : G ≃ₗ[*] H, ∃ g : G ^ ∞ ≃ₗ[*] H ^ ∞, ∀ n: ℕ, ∃ k: ℕ, ∃ h : G ^ n ≃ₗ[*] H ^ k, ∀ (A : G ^ n), f A = f.to_fun A := sorry

/-! #brief Prove that any finite abelian group is cyclically equivalent to an unique group
-/
--Prove that any finite abelian group is cyclically equivalent to an unique group
theorem finite.abelian.cyclically_iso (G : Type*) [group G] [fintype G] [fintype_mul_class G] [fintype_add_class G]
[add_comm_group G] [mul_comm_group G] : ∃ (n : ℕ) (f : G ≃ₗ[*] G ^ n), ∀ (g: G ^ n), ∃ (k : G ^ n) (h : G ^ n), f g = f.to_fun g := sorry

/-! #brief Prove that any finite abelian group is cyclically iso to a group whose order is a power of a prime
-/
--Prove that any finite abelian group is cyclically iso to a group whose order is a power of a prime
theorem finite.abelian.cyclically_iso_prime_power (G : Type*) [group G] [fintype G] [fintype_mul_class G] [fintype_add_class G]
[add_comm_group G] [mul_comm_group G] : ∃ (p : ℕ) (n : ℕ) (f : G ≃ₗ[*] G ^ p ^ n), ∀ (g : G ^ p ^ n), ∃ (k : G ^ p ^ n) (h : G ^ p ^ n), f g = f.to_fun g := sorry

/-! #brief Prove that Cyclic Groups are Abelian
-/
--Prove that Cyclic Groups are Abelian
theorem cyclic.abelian (G : Type*) [group G] [fintype G] [fintype_mul_class G] [fintype_add_class G] [mul_comm_group G] :
    ∀ (g : G), ∃ (n : ℕ), ∃ (f : G), is_unit f ∧ (group_hom.ker f = ⊥) → is_subgroup (subtype.val '' {g | ↑g = 1}) 1 := sorry

/-! #brief Prove that cyclic groups are isomorphic to their duals
-/
--Prove that cyclic groups are isomorphic to their duals
theorem cyclic.dual (G : Type*) [group G] [fintype G] [fintype_mul_class G] [fintype_add_class G] [add_comm_group G]
[mul_comm_group G] [fintype_mul_class G] [fintype_add_class G] : ∃ (g : G), ∃ (f : G ^ G), f.to_fun g = 1 := sorry

/-! #brief Prove that the finite group G is cyclically isomorphic to a finite group whose elements are powers of a generator
-/
--Prove that the finite group G is cyclically isomorphic to a finite group whose elements are powers of a generator
theorem cyclic.generator (G : Type*) [group G] [fintype G] [fintype_mul_class G] [fintype_add_class G] [mul_comm_group G] :
    ∃ (g : G), ∃ (n : ℕ), ∃ (f : G ^ n), ∃ (h : G ^ n), is_unit h ∧ f.to_fun g = 1 ∧ f = h.to_fun g := sorry

/-! #brief Prove that a finite abelian group whose order is a power of a prime is cyclically isomorphic to a finite cyclic group
-/
--Prove that a finite abelian group whose order is a power of a prime is cyclically isomorphic to a finite cyclic group
theorem cyclic.finite.power_prime (G : Type*) [group G] [fintype G] [fintype_mul_class G] [fintype_add_class G] [fintype_add_class G]
[add_comm_group G] [mul_comm_group G] : ∃ (p : ℕ) (n : ℕ), ∃ (g : G), ∃ (f : G ^ p ^ n), ∃ (h : G ^ p ^ n), is_unit h ∧ f.to_fun g = 1 ∧ f = h.to_fun g := sorry

/-! #brief Prove that the order of an element in a finite abelian group is a power of a prime
-/
--Prove that the order of an element in a finite abelian group is a power of a prime
theorem cyclic.finite.el_order_prime_power (G : Type*) [group G] [fintype G] [fintype_mul_class G] [fintype_add_class G] [add_comm_group G]
[mul_comm_group G] : ∀ (g : G), ∃ (p : ℕ) (n : ℕ) (h : G ^ p ^ n), is_unit h ∧ h.to_fun g = 1 := sorry

/-! #brief Prove that a finite group G whose elements are the powers of a generator is cyclically isomorphic to a group of the form G ^ p ^ n
-/
--Prove that a finite group G whose elements are the powers of a generator is cyclically isomorphic to a group of the form G ^ p ^ n
theorem cyclic.finite.gen_iso (G : Type*) [group G] [fintype G] [fintype_mul_class G] [fintype_add_class G] [add_comm_group G]
[mul_comm_group G] : ∀ (g : G), ∃ (n :

--OUTPUT 2
theorem my_theorem(g h : fin_group (α)) (hg : g ≃* h): homomorphism g h = dual_homomorphism (dual_fin_group g) (dual_fin_group h)  := sorry
--This is definitely not the way to go about proving this, but I am having a lot of trouble figuring out even what the correct statment is, since I am new (in fact this is the first thing I have tried to prove in lean).
--The problem is that I cannot use the fact that Homomorphisms between finite abelian groups are isomorphic to dual homomorphisms of their duals, so I was wondering if there is a way to show this in mathlib. Thanks!

import algebra.group.hom order.lattice

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}

def fin_group_hom_equiv : equiv (fin_group α) (fin_group β) (group_hom α β) (group_hom β α) :=
{ to_fun := λ f, f.to_hom.symm,
  inv_fun := λ g, g.to_hom,
  left_inv := λ f, by ext; simp [f.to_hom, (f.to_hom).symm],
  right_inv := λ g, by ext; simp [g.to_hom, (g.to_hom).symm] }

def group_hom_fin_group_equiv : equiv (group_hom α β) (group_hom β α) (fin_group α) (fin_group β) :=
{ to_fun := λ g, ⟨ker g.to_hom, _⟩,
  inv_fun := λ g, ⟨ker g.to_hom, _⟩,
  left_inv := λ g, by ext; simp [ker, g.to_hom, smul_eq_mul, mul_comm],
  right_inv := λ g, by ext; simp [ker, g.to_hom, smul_eq_mul, mul_comm] }

def dual_homomorphism' : fin_group α → fin_group β → set (α → β) :=
λ g h, (g.to_hom.symm.ker.to_hom.symm).image

def homomorphism' : fin_group α → fin_group β → set (β → α) :=
λ g h, (g.to_hom.symm.ker.to_hom.symm).image

variables (g h : fin_group α)

lemma homomorphism_eq_dual_homomorphism : (dual_homomorphism g h : set (α → β)) = homomorphism h g :=
begin
  ext f,
  split,
  { intro h,
    let h' := @h _ g.is_group_hom,
    simp [h'] at h' ⊢,
    exact h' },
  { intro h,
    let h' := @h _ (g.is_group_hom.symm),
    simp [h'] at h' ⊢,
    exact h' }

--OUTPUT 3
theorem duals.hom_gp_bij : ∀{α}[fintype α] {G H}[decidable_eq α] (f : G → H) (g : G ≃* H),
  g.ker = fintype.univ → hom_gp g.symm_gp → (f = g.to_fun) :=
begin 
 intros α h G H h2 f,
 induction h,
 intros g h1 h2,
 cases h2,
 congr,
 ext,
 simp only [g.eq_ker],
 split,
 simp only[g.eq_ker],
 intros h2 h3,
 have h4 := h2.2 h3,
 rw finset.mem_univ at h4,
 exact h4,
 simp only[g.eq_ker],
 intros h2 h3,
 have h4 := h2.2 h3,
 rw finset.mem_univ at h4,
 exact h4,

