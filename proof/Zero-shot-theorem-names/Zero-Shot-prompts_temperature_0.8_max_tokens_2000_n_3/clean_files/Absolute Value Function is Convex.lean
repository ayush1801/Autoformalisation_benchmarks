
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
theorem abs_val_is_convex : is_convex real.abs :=
begin
  sorry

--OUTPUT 2
theorem abs_convex (a b : ℝ) (h : 0 ≤ a) : convex_on abs {x | a ≤ x ∧ x ≤ b} :=
begin
  intros,
  apply abs_pos,
  rw [← sub_eq_add_neg, ← sub_eq_add_neg],
  apply add_le_add,
  apply le_trans,
  assumption,
  apply le_of_lt,
  apply sub_pos.mpr,
  assumption,
  apply le_trans,
  apply sub_le_sub_right,
  assumption,
  assumption,
  apply le_trans,
  apply sub_le_sub_left,
  assumption,
  assumption,
  apply le_trans,
  apply le_of_lt,
  apply sub_pos.mpr,
  assumption,
  assumption,
  apply le_trans,
  apply sub_le_sub_right,
  assumption,
  assumption,
  apply le_trans,
  apply sub_le_sub_left,
  assumption,
  assumption,

--OUTPUT 3
theorem absolute_value_is_convex : is_convex A (λ x, abs x) :=
begin
    unfold is_convex,
    intros x y ε hε,
    have h2 := abs_le_abs x,
    have h3 := abs_le_abs y,
    have h4 := le_trans h2 h3,
    have h5 :=  abs_mul_le_abs_mul_abs _ _,
    calc   abs(x-y) : abs_sub x y
      ... = abs(ε-(1-ε))*abs(x-y) : by rw abs_sub_abs_sub x y; simp[hε]; assumption
      ... = abs(x-y)*abs(ε-(1-ε)) : by rw mul_comm; refl
      ... ≤ abs(x-y)*1 : by rw mul_one; exact le_trans h5 h4
      ... = abs(x-y) : mul_one (abs (x-y))

