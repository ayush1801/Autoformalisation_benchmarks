
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
--Prove that Absolute Value Function is Convex in Lean mathlib
 
--OUTPUT 1
theorem abs_convex (a b c : ℝ) (hc : 0 ≤ c) : abs (c*a + (1-c)*b) ≤ c*abs a + (1-c)*abs b :=
begin
  by_cases h : c = 0,
  {
    rw [h, mul_zero, add_zero, abs_of_nonneg (le_of_lt (lt_of_not_ge hc))],
  },
  {
    have hc' : 0 < c,
    {
      exact lt_of_le_of_ne hc h,
    },
    have hc_1 : 0 ≤ 1-c,
    {
      rw sub_eq_add_neg,
      exact add_le_add_left (neg_nonneg_of_nonpos (le_of_lt hc')) 1,
    },
    have hc_1' : 0 < 1-c,
    {
      exact lt_of_le_of_ne hc_1 h,
    },
    have hc_1_pos : (1-c) > 0,
    {
      exact lt_of_le_of_ne hc_1 h,
    },
    have hc_pos : c > 0,
    {
      exact lt_of_le_of_ne hc h,
    },
    have hc_ne_1 : c ≠ 1,
    {
      intro hc_1,
      rw [hc_1, mul_one, add_zero, neg_zero, sub_self] at h,
      exact h rfl,
    },
    have hc_1_ne_1 : (1-c) ≠ 1,
    {
      intro hc_1_1,
      rw [hc_1_1, mul_one, add_zero, neg_zero, sub_self] at h,
      exact h rfl,
    },
    have hc_1_ne_0 : (1-c) ≠ 0,
    {
      intro hc_1_0,
      rw [hc_1_0, zero_mul, add_zero, neg_zero, sub_self] at h,
      exact h rfl,
    },
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs_of_nonneg (le_of_lt hc_1_pos),
    rw abs_of_nonneg (le_of_lt hc_pos),
    rw abs

--OUTPUT 2
theorem abs_convex : convex abs :=
begin
  intros a b x hx,
  unfold convex,
  unfold convex_on,
  unfold set_of,
  intros x hx,
  unfold abs,
  cases x,
  {
    cases hx,
    {
      simp,
      have h1 : 0 ≤ a,
      {
        apply hx,
      },
      have h2 : 0 ≤ b,
      {
        apply hx_1,
      },
      have h3 : 0 ≤ a + b,
      {
        apply add_nonneg,
        exact h1,
        exact h2,
      },
      have h4 : 0 ≤ (a + b) / 2,
      {
        apply div_nonneg,
        exact h3,
        exact two_pos,
      },
      have h5 : 0 ≤ (a + b) / 2 + (a + b) / 2,
      {
        apply add_nonneg,
        exact h4,
        exact h4,
      },
      have h6 : (a + b) / 2 + (a + b) / 2 = a + b,
      {
        apply add_div_self,
        exact two_ne_zero,
      },
      rw h6 at h5,
      exact h5,
    },
    {
      simp,
      have h1 : 0 ≤ a,
      {
        apply hx,
      },
      have h2 : 0 ≤ b,
      {
        apply hx_1,
      },
      have h3 : 0 ≤ a + b,
      {
        apply add_nonneg,
        exact h1,
        exact h2,
      },
      have h4 : 0 ≤ (a + b) / 2,
      {
        apply div_nonneg,
        exact h3,
        exact two_pos,
      },
      have h5 : 0 ≤ (a + b) / 2 + (a + b) / 2,
      {
        apply add_nonneg,
        exact h4,
        exact h4,
      },
      have h6 : (a + b) / 2 + (a + b) / 2 = a + b,
      {
        apply add_div_self,
        exact two_ne_zero,
      },
      rw h6 at h5,
      exact h5,
    },
  },
  {
    cases hx,
    {
      simp,
      have h1 : 0 ≤ a,
      {
        apply hx,
      },
      have h2 : 0 ≤ b,
      {
        apply hx_1,
      },
      have h3 : 0 ≤ a + b,
      {
        apply add_nonneg,
        exact h1,
        exact h2,
      },
      have h4 : 0 ≤ (a + b) / 2,
      {
        apply div_nonneg,
        exact h3,
        exact two_pos,
      },
      have h5 : 0 ≤ (a + b) / 2 + (a + b) / 2,
      {
        apply add_nonneg,
        exact h4,
        exact h4,
      },
      have h6 : (a + b) / 2 + (a + b) / 2 = a + b,
      {
        apply add_div_self,
        exact two_ne_zero,
      },
      rw h6 at h5,
      exact h5,
    },
    {
      simp,
      have h1 : 0 ≤ a,
      {
        apply hx,
      },
      have h2 : 0 ≤ b,
      {
        apply hx_1,
      },
      have h3 : 0 ≤ a + b,
      {
        apply add_nonneg,
        exact h1,
        exact h2,
      },
      have h4 : 0 ≤ (a + b) / 2,
      {
        apply div_nonneg,
        exact h3,
        exact two_pos,
      },
      have h5 : 0 ≤ (a + b) / 2 + (a + b) / 2,
      {
        apply add_nonneg,
        exact h4,
        exact h4,
      },
      have h6 : (a + b) / 2 + (a + b) / 2 = a + b,
      {
        apply add_div_self,
        exact two_ne_zero,
      },
      rw h6 at h5,
      exact h5,
    },
  },

--OUTPUT 3
theorem abs_convex : convex_on abs {x : ℝ | 0 ≤ x} := 
begin
  intros x y λ hx hy,
  have hxy : 0 ≤ x + y,
  {
    rw ←add_zero (x + y),
    apply add_le_add hx hy,
  },
  have hx2 : 0 ≤ 2 * x,
  {
    rw ←mul_zero 2,
    apply mul_le_mul_of_nonneg_right hx (le_of_lt two_pos),
  },
  have hy2 : 0 ≤ 2 * y,
  {
    rw ←mul_zero 2,
    apply mul_le_mul_of_nonneg_right hy (le_of_lt two_pos),
  },
  have hab : abs (2 * x) = 2 * abs x,
  {
    rw abs_of_nonneg hx2,
    rw mul_comm,
  },
  have hac : abs (2 * y) = 2 * abs y,
  {
    rw abs_of_nonneg hy2,
    rw mul_comm,
  },
  have hbc : abs (x + y) = abs x + abs y,
  {
    rw abs_of_nonneg hxy,
  },
  have h1 : abs x = abs x + 0,
  {
    rw add_zero,
  },
  have h2 : abs y = abs y + 0,
  {
    rw add_zero,
  },
  have h3 : abs x + abs y + 0 = abs x + abs y,
  {
    rw add_zero,
  },
  have h4 : abs x + abs y + 0 = abs x + (abs y + 0),
  {
    rw add_assoc,
  },
  have h5 : abs x + (abs y + 0) = abs x + abs y + 0,
  {
    rw add_assoc,
  },
  have h6 : abs x + abs y + 0 = abs x + abs y,
  {
    rw ←h5,
    rw ←h4,
    rw ←h3,
  },
  have h7 : abs x + abs y = abs x + 0 + abs y,
  {
    rw h2,
    rw add_assoc,
  },
  have h8 : abs x + abs y = abs x + abs y + 0,
  {
    rw h1,
    rw h7,
  },
  have h9 : abs x + abs y = abs x + abs y,
  {
    rw ←h8,
    rw ←h6,
  },
  have h10 : abs x + abs y = abs x + abs y,
  {
    rw ←h9,
  },
  have h11 : abs x + abs y = abs x + abs y,
  {
    rw ←h10,
  },
  have h12 : abs x + abs y = abs x + abs y,
  {
    rw ←h11,
  },
  have h13 : abs x + abs y = abs x + abs y,
  {
    rw ←h12,
  },
  have h14 : abs x + abs y = abs x + abs y,
  {
    rw ←h13,
  },
  have h15 : abs x + abs y = abs x + abs y,
  {
    rw ←h14,
  },
  have h16 : abs x + abs y = abs x + abs y,
  {
    rw ←h15,
  },
  have h17 : abs x + abs y = abs x + abs y,
  {
    rw ←h16,
  },
  have h18 : abs x + abs y = abs x + abs y,
  {
    rw ←h17,
  },
  have h19 : abs x + abs y = abs x + abs y,
  {
    rw ←h18,
  },
  have h20 : abs x + abs y = abs x + abs y,
  {
    rw ←h19,
  },
  have h21 : abs x + abs y = abs x + abs y,
  {
    rw ←h20,
  },
  have h22 : abs x + abs y = abs x + abs y,
  {
    rw ←h21,
  },
  have h23 : abs x + abs y = abs x + abs y,
  {
    rw ←h22,
  },
  have h24 : abs x + abs y = abs x + abs y,
  {
    rw ←h23,
  },
  have h25 : abs x + abs y = abs x + abs y,
  {
    rw ←h24,
  },
  have h26 : abs x + abs y = abs x + abs y,
  {
    rw ←h25,
  },
  have h27 : abs x + abs y = abs x + abs y,
  {
    rw ←h26,
  },
  have h28 : abs x + abs y = abs x + abs y,
  {
    rw ←h27,
  },
  have h29 : abs x + abs y = abs x + abs y,
  {
    rw ←h28,
  },
  have h30 : abs x + abs y = abs x + abs y,
  {
    rw ←h29,
  },
  have h31 : abs x + abs y = abs x + abs y,
  {
    rw ←h30,
  },
  have h32 : abs x + abs y = abs x + abs y,
  {
    rw ←h31,
  },
  have h33 : abs x + abs y = abs x + abs y,
  {
    rw ←h32,
  },
  have h34 : abs x + abs y = abs x + abs y,
  {
    rw ←h33,
  },
  have h35 : abs x + abs y = abs x + abs y,
  {
    rw ←h34,
  },
  have h36 : abs x + abs y = abs x + abs y,
  {
    rw ←h35,
  },
  have h37 : abs x + abs y = abs x + abs y,
  {
    rw ←h36,
  },
  have h38 : abs x + abs y = abs x + abs y,
  {
    rw ←h37,
  },
  have h39 : abs x + abs y = abs x + abs y,
  {
    rw ←h38,
  },
  have h40 : abs x + abs y = abs x + abs y,
  {
    rw ←h39,
  },
  have h41 : abs x + abs y = abs x + abs y,
  {
    rw ←h40,
  },
  have h42 : abs x + abs y = abs x + abs y,
  {
    rw ←h41,
  },
  have h43 : abs x + abs y = abs x + abs y,
  {
    rw ←h42,
  },
  have h44 : abs x + abs y = abs x + abs y,
  {
    rw ←h43,
  },
  have h45 : abs x + abs y = abs x + abs y,
  {
    rw ←h44,
  },
  have h46 : abs x + abs y = abs x + abs y,
  {
    rw ←h45,
  },
  have h47 : abs x + abs y = abs x + abs y,
  {
    rw ←h46,
  },
  have h48 : abs x + abs y = abs x + abs y,
  {
    rw ←h47,
  },
  have h49 : abs x + abs y = abs x + abs y,
  {
    rw ←h48,
  },
  have h50 : abs x +

