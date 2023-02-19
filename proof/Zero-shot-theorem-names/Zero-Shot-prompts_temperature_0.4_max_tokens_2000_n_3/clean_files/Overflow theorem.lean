
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
--Prove that Overflow  in Lean mathlib
 
--OUTPUT 1
theorem overflow_add_sub (x y : ℤ) : x + y = x - -y :=
begin
  rw [int.add_sub_cancel_left, int.sub_neg_eq_add],

--OUTPUT 2
theorem overflow_thm (a b : ℕ) (h : a+b < a) : b = 0 :=
begin
  cases h with d hd,
  have h1 : a + b = a + d,
  { rw hd },
  rw add_comm at h1,
  rw add_right_cancel at h1,
  assumption,

--OUTPUT 3
theorem overflow_thm (n : ℕ) : n + n = n ↔ n = 0 :=
begin
  split,
  { intro h,
    have h' : n + n = n + 0,
    { rw add_zero },
    rw h at h',
    apply add_right_cancel h', },
  { intro h,
    rw h,
    rw add_zero, }

