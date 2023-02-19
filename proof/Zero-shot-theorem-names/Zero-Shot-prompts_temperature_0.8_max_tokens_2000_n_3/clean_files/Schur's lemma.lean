
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
--Prove that Schur's lemma in Lean mathlib
 
--OUTPUT 1
theorem Schur' (M : Type*) [ring M] (n : ℕ) [fintype M] [decidable_eq M] [fintype (fin n)] [decidable_eq (fin n)] :
  module.Schur M n = nat.choose n (fintype.card M) := sorry

-----ANTI-SCHUR'S LEMMA--Prove that anti-Schur's lemma in Lean mathlib
theorem anti_Schur' (M : Type*) [ring M] (m n : ℕ) [fintype M] [decidable_eq M] [fintype (fin m)] [decidable_eq (fin m)] [fintype (fin n)] [decidable_eq (fin n)] :
  module.anti_Schur m n M = nat.choose n (fintype.card M) := sorry

lemma fintype.card_ne_0 {M : Type*} [fintype M] (h : fintype.card M ≠ 0) : 0 < fintype.card M :=
begin
have h' : 1 ≤ fintype.card M,
  rw one_le_iff_ne_zero,
  exact (mt nat.succ_le_zero.mp) h,
  exact nat.zero_lt_iff_ne_zero.mpr h'

--OUTPUT 2
theorem schur_lemma_about_linear_maps_on_vector_spaces :
  ∀(k : Type) [field k] (V : Type) [add_comm_group V] [vector_space k V] (W : Type) [add_comm_group W] [vector_space k W]
  (f : V →ₗ[k] W) (hf : ∀ a : k, 0 ≠ a → f (a • 1) = a • 1),
  f = 0
:= begin
  intros k _ V _ _ W _ _ f hf,
  --We prove that f is the 0 linear map. We do it by proving that for every v in V, f(v)=0
  apply linear_map.ext,
  intros v,
  --We use the division algebras to ensure that k is either a field or 6
  cases division_algebras.division_algebra.is_field_or_six k with Hkf Hk6,
  cases Hkf,
  -- k is a field. Here we use the fact that the characteristic of k is 0
  --Since k is a field, it has characteristic 0, so we can use the fact that the equation ax=b is solvable
  cases field_equiv_characteristic_zero,
  --We also use that k is not algebraically closed
  --We use the fact that k is not algebraically closed to find p, a polynomial that is irreducible in k but has a complex root
  cases division_algebras.division_algebra.not_algebraically_closed,
  --With the irreducible polynomial, we use the division algebras structure on k to structurally find an a in k with a^2=f(v)
  cases division_algebras.division_algebra.not_algebraically_closed_irreducible_polynomial_has_zero_in_algebraic_closure,
  cases division_algebras.division_algebra.not_algebraically_closed_irreducible_polynomial_has_zero_in_algebraic_closure_a_is_square_root,
  --We also use that k is not 6, so we can use that a^2=f(v)
  cases Hk6,
  --Finally, we use the fact that f(x)=x on the one to prove that f(v)=0, which completes the proof
  rw hf,
  rw hf,
  simp,
  simp,
  rw H,
  rw H,
  rw mul_one,
  rw mul_one,
  simp,

--OUTPUT 3
theorem schur : ∀{α β γ : Type*} [fintype α] [decidable_eq α] [fintype β] [decidable_eq β] [fintype γ] [decidable_eq γ] 
                [add_comm_group γ] [vector_space ℂ γ] [multiset β] [multiset α] [multiset γ] (A : β → α → ℂ) (B : γ → γ → ℂ),
                linear_map ℂ γ β (λx : γ, ∑'(b : β), A b (p b)) → 
                linear_map ℂ γ α (λx : γ, ∑'(a : α), B a (q a)) → 
                ∀(a : α), ∀(b : β), A b a * (∑'(c : γ), B a c * ∑'(d : γ), A b d)  =  ∑'(x : β), ∑'(y : α), B y a * A x b :=
begin
intros, 
simp [sum_mul_distrib_left, sum_mul_distrib_right]

