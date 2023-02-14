
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
--Prove that fractional parts of the integer multiples of an irrational number form a dense subset of the unit interval in Lean mathlib
 
--OUTPUT 1
theorem frac_irrational_dense_in_unit_interval (x : ℝ) (hx : ¬ is_rat x) :
∃ s : set ℕ, (set_of_finite_interval (0 : ℝ) 1) = s.image ((λ y, ((x : ℝ)*y)%real) : (ℕ → ℝ)) :=
sorry

--Every real number is an upper bound of a finite set of rational numbers.
--This suggests that the least upper bound of a finite set of rational numbers is actually just a real number.

--Prove that the least upper bound of a finite set of rational numbers is indeed a real number.

--Hint: For any rational number q, x < q ∨ x = q ∨ x > q.

--Hint: You may find the set_of_finite_interval and rat_sup lemmas useful.
lemma rat_sup_of_finite_set (s : set ℚ) (hs : finite s) : set.finite_sup s = real.sup s :=
sorry

--Prove that if we have a sequence of real numbers with upper bound, then it must converge

--Hint: You may find the below lemmas useful.
lemma real.bdd_iff_exists_real_ub (s : ℕ → ℝ) :
bdd_above s ↔ ∃ c : ℝ, ∀ n : ℕ, s n ≤ c :=
sorry

lemma real.bdd_above_iff_exists_real_ub (s : ℕ → ℝ) :
bdd_above s ↔ ∃ c : ℝ, ∀ n : ℕ, s n ≤ c := sorry

--The real numbers are complete. That is, every real valued Cauchy sequence converges to a real number.

--Prove that every real valued Cauchy sequence converges to a real number.

--Hint: For any real number a, x < a ∨ x = a ∨ x > a.

--Hint: You may find the below lemmas useful.
lemma real.tendsto_of_cauchy_exists (s : ℕ → ℝ) (h : cauchy s) : ∃ l : ℝ, tendsto s (𝓝 l) := sorry

lemma real.tendsto_eq_nhds_of_cauchy (s : ℕ → ℝ) (h : cauchy s) : tendsto s (𝓝 (lim s)) := sorry

section
open real
local attribute [instance] classical.prop_decidable

--For the following exercises, fill in all the sorrys.

/-- The complete ordered field of real numbers -/
def real : Type :=
{ x : ℝ // ∀ y : ℝ, y < x ∨ y = x ∨ x < y }

lemma real.exists_lt_pos : ∃ x : real, (0 : ℝ) < x := sorry

noncomputable def real.has_lift : has_lift ℝ real := sorry

lemma real.lift_coe {x : ℝ} : (↑x : real) = sorry := sorry

lemma real.lift_coe_inj {x y : ℝ} (h : (↑x : real) = ↑y) : x = y := sorry

lemma real.lift_id {r : real} : ↑r = r := sorry

lemma real.coe_lt_of_lt : ∀ {x y : real}, x < y → (↑x : ℝ) < ↑y := sorry

lemma real.lt_coe_of_lt : ∀ {x y : real}, (↑x : ℝ) < ↑y → x < y := sorry

lemma real.lt_of_coe_lt : ∀ {x y : real}, (↑x : ℝ) < y → x < y := sorry

lemma real.coe_lt_coe : ∀ {x y : real}, x < y → (↑x : ℝ) < ↑y := sorry

lemma real.coe_lt_coe_iff : ∀ {x y : real}, (↑x : ℝ) < ↑y ↔ x < y := sorry

lemma real.coe_lt_coe_iff_lt : ∀ {x y z : real}, x < z → z < y → (↑x : ℝ) < ↑y := sorry

lemma real.coe_lt_coe_iff_le : ∀ {x y z : real}, x ≤ z → z < y → (↑x : ℝ) < ↑y := sorry

lemma real.eq_of_coe_eq_coe : ∀ {x y : real}, (↑x : ℝ) = ↑y → x = y := sorry

lemma real.eq_iff_coe_eq_coe : ∀ {x y : real}, x = y ↔ (↑x : ℝ) = ↑y := sorry

lemma real.lt_iff_coe_lt_coe : ∀ {x y : real}, x < y ↔ (↑x : ℝ) < ↑y := sorry

lemma real.le_iff_coe_le_coe : ∀ {x y : real}, x ≤ y ↔ (↑x : ℝ) ≤ ↑y := sorry

lemma real.lt_iff_lt_coe : ∀ {x y : real}, x < y ↔ ↑x < ↑y := sorry

lemma real.le_iff_le_coe : ∀ {x y : real}, x ≤ y ↔ ↑x ≤ ↑y := sorry

lemma real.lt_iff_coe_lt_of_coe_lt_coe : ∀ {x y : real}, (↑x : ℝ) < ↑y → x < y ↔ (↑x : ℝ) < ↑y := sorry

lemma real.lt_iff_of_coe_lt_coe : ∀ {x y : real}, (↑x : ℝ) < ↑y → x < y ↔ ↑x < ↑y := sorry

lemma real.coe_lt_iff_lt_of_coe_lt_coe : ∀ {x y z : real}, (↑x : ℝ) < ↑y → x < z → ↑x < ↑z := sorry

lemma real.coe_lt_iff_le_of_coe_lt_coe : ∀ {x y z : real}, (↑x : ℝ) < ↑y → x ≤ z → ↑x ≤ ↑z := sorry

lemma real.coe_lt_iff_lt_of_lt_coe : ∀ {x y z : real}, x < ↑y → x < z → ↑x < ↑z := sorry

lemma real.coe_lt_iff_le_of_lt_coe : ∀ {x y z : real}, x < ↑y → x ≤ z → ↑x ≤ ↑z := sorry

lemma real.coe_lt_iff_lt_of_coe_lt : ∀ {x y z : real}, (↑x : ℝ) < y → x < z → ↑x < ↑z := sorry

lemma real.coe_lt_iff_le_of_coe_lt : ∀ {x y z : real}, (↑x : ℝ) < y → x ≤ z → ↑x ≤ ↑z := sorry

lemma real.coe_lt_iff_lt_of_lt_coe : ∀ {x y z : real}, x < ↑y → x < z → ↑x < ↑z := sorry

lemma real.coe_lt_iff_le_of_lt_coe : ∀ {x y z : real}, x < ↑y → x ≤ z → ↑x ≤ ↑z := sorry

lemma real.lt_iff_coe_lt_of_coe_lt : ∀ {x y : real}, (↑x : ℝ) < y → x < y ↔ (↑x : ℝ) < ↑y := sorry

lemma real.lt_iff_of_coe_lt : ∀ {x y : real}, (↑x : ℝ) < y → x < y ↔ ↑x < ↑y := sorry

lemma real.coe_lt_iff_lt_of_lt_of_coe_lt_coe : ∀ {x y z : real}, x < z →

--OUTPUT 2
theorem Q2 (b:ℝ): ¬ ∃ n, b = (n:ℝ) :=
begin
  intro h, cases h with n h,
  have h1 := Q1 b n h,
  have h2 : (1:ℝ) ∈ closure ({(b * 0) % 1, b / 1, (b * 1) % 1}),
  from closure_subset (subset.refl _),
  have h3 := subset_closure_iff_subset_of_is_open (half_open_lt_one 1) h2,
  have h4 := h3 (ne_empty_of_mem h2),
  have h5 := subset_singleton_iff.2 h4,
  rw h5 at h1,
  rw nat.mod_eq_mod_nat (lt_of_lt_of_le (by linarith) h1) at h1,
  exact lt_irrefl (nat.mod_nat_lt (lt_of_lt_of_le (by linarith) h1)) h1,

--OUTPUT 3
theorem integers_of_irrational_are_dense (a : ℝ) (h : irrational a) : ∀ n : ℕ, ∃ p : ℕ, n ≤ p ∧ (p - n : ℤ) ∈ {x | x ∈ ℤ ∧ ∥x∥ < 1} :=
begin
    intros n,
    cases (nat.finite_iff_exists_nat_le (a * n) + 0.5) with m hm,
    use [m - n, nat.sub_le_sub_right_iff.mp hm, sub_mem_iff_mem_add.mp (iff.elim_right hm)],

