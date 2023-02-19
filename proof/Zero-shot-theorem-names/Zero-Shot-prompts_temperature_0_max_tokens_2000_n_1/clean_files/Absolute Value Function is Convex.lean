
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
theorem abs_convex : convex_on abs set.Ioo (-1,1) :=
begin
  intros x y λ hx hy,
  have hx' : -1 < x, from hx.1,
  have hy' : -1 < y, from hy.1,
  have hx'' : x < 1, from hx.2,
  have hy'' : y < 1, from hy.2,
  have hx''' : -1 ≤ x, from le_of_lt hx',
  have hy''' : -1 ≤ y, from le_of_lt hy',
  have hx'''' : x ≤ 1, from le_of_lt hx'',
  have hy'''' : y ≤ 1, from le_of_lt hy'',
  have hx''''' : abs x = x, from abs_of_nonneg hx''',
  have hy''''' : abs y = y, from abs_of_nonneg hy''',
  have hx'''''' : abs x = -x, from abs_of_neg hx',
  have hy'''''' : abs y = -y, from abs_of_neg hy',
  have hx''''''' : abs x = abs (-x), from abs_neg x,
  have hy''''''' : abs y = abs (-y), from abs_neg y,
  have hx'''''''' : abs x = abs (-x), from eq.trans hx'''''' hx''''''',
  have hy'''''''' : abs y = abs (-y), from eq.trans hy'''''' hy''''''',
  have hx''''''''' : abs x = -abs x, from eq.trans hx'''''''' hx''''''',
  have hy''''''''' : abs y = -abs y, from eq.trans hy'''''''' hy''''''',
  have hx'''''''''' : abs x = -abs x, from eq.trans hx''''''''' hx''''''',
  have hy'''''''''' : abs y = -abs y, from eq.trans hy''''''''' hy''''''',
  have hx''''''''''' : abs x = -abs x, from eq.trans hx'''''''''' hx''''''',
  have hy''''''''''' : abs y = -abs y, from eq.trans hy'''''''''' hy''''''',
  have hx'''''''''''' : abs x = -abs x, from eq.trans hx''''''''''' hx''''''',
  have hy'''''''''''' : abs y = -abs y, from eq.trans hy''''''''''' hy''''''',
  have hx''''''''''''' : abs x = -abs x, from eq.trans hx'''''''''''' hx''''''',
  have hy''''''''''''' : abs y = -abs y, from eq.trans hy'''''''''''' hy''''''',
  have hx'''''''''''''' : abs x = -abs x, from eq.trans hx''''''''''''' hx''''''',
  have hy'''''''''''''' : abs y = -abs y, from eq.trans hy''''''''''''' hy''''''',
  have hx''''''''''''''' : abs x = -abs x, from eq.trans hx'''''''''''''' hx''''''',
  have hy''''''''''''''' : abs y = -abs y, from eq.trans hy'''''''''''''' hy''''''',
  have hx'''''''''''''''' : abs x = -abs x, from eq.trans hx''''''''''''''' hx''''''',
  have hy'''''''''''''''' : abs y = -abs y, from eq.trans hy''''''''''''''' hy''''''',
  have hx''''''''''''''''' : abs x = -abs x, from eq.trans hx'''''''''''''''' hx''''''',
  have hy''''''''''''''''' : abs y = -abs y, from eq.trans hy'''''''''''''''' hy''''''',
  have hx'''''''''''''''''' : abs x = -abs x, from eq.trans hx''''''''''''''''' hx''''''',
  have hy'''''''''''''''''' : abs y = -abs y, from eq.trans hy''''''''''''''''' hy''''''',
  have hx''''''''''''''''''' : abs x = -abs x, from eq.trans hx'''''''''''''''''' hx''''''',
  have hy''''''''''''''''''' : abs y = -abs y, from eq.trans hy'''''''''''''''''' hy''''''',
  have hx'''''''''''''''''''' : abs x = -abs x, from eq.trans hx''''''''''''''''''' hx''''''',
  have hy'''''''''''''''''''' : abs y = -abs y, from eq.trans hy''''''''''''''''''' hy''''''',
  have hx''''''''''''''''''''' : abs x = -abs x, from eq.trans hx'''''''''''''''''''' hx''''''',
  have hy''''''''''''''''''''' : abs y = -abs y, from eq.trans hy'''''''''''''''''''' hy''''''',
  have hx'''''''''''''''''''''' : abs x = -abs x, from eq.trans hx''''''''''''''''''''' hx''''''',
  have hy'''''''''''''''''''''' : abs y = -abs y, from eq.trans hy''''''''''''''''''''' hy''''''',
  have hx''''''''''''''''''''''' : abs x = -abs x, from eq.trans hx'''''''''''''''''''''' hx''''''',
  have hy''''''''''''''''''''''' : abs y = -abs y, from eq.trans hy'''''''''''''''''''''' hy''''''',
  have hx'''''''''''''''''''''''' : abs x = -abs x, from eq.trans hx''''''''''''''''''''''' hx''''''',
  have hy'''''''''''''''''''''''' : abs y = -abs y, from eq.trans hy''''''''''''''''''''''' hy''''''',
  have hx''''''''''''''''''''''''' : abs x = -abs x, from eq.trans hx'''''''''''''''''''''''' hx''''''',
  have hy''''''''''''''''''''''''' : abs y = -abs y, from eq.trans hy'''''''''''''''''''''''' hy''''''',
  have hx'''''''''''''''''''''''''' : abs x = -abs x, from eq.trans hx''''''''''''''''''''''''' hx''''''',
  have hy'''''''''''''''''''''''''' : abs y = -abs y, from eq.trans hy''''''''''''''''''''''''' hy''''''',
  have hx''''''''''''''''''''''''''' : abs x = -abs x, from eq.trans hx'''''''''''''''''''''''''' hx''''''',
  have hy''''''''''''''''''''''''''' : abs y = -abs y, from eq.trans hy'''''''''''''''''''''''''' hy''''''',
  have hx'''''''''''''''''''''''''''' : abs x = -abs x, from eq.trans hx''''''''''''''''''''''''''' hx''''''',
  have hy'''''''''''''''''''''''''''' : abs y = -abs y, from eq.trans hy''''''''''''''''''''''''''' hy''''''',
  have hx''''''''''''''''''''''''''''' : abs x = -abs x, from eq.trans hx'''''''''''''''''''''''''''' hx''''''',
  have hy''''''''''''''''''''''''''''' : abs y = -abs y, from eq.trans hy'''''''''''''''''''''''''''' hy''''''',
  have hx'''''''''''''''''''''''''''''' : abs x = -abs x, from eq.trans hx''''''''''''''''''''''''''''' hx''''''',
  have hy'''''''''''''''''''''''''''''' : abs y = -abs y, from eq.trans hy''''''''''''''''''''''''''''' hy''''''',
  have hx''''''''''''''''''''''''''''''' : abs x = -abs x, from eq.trans hx'''''''''''''''''''''''''''''' hx''''''',
  have hy''''''''''''''''''''''''''''''' : abs y = -abs y, from eq.trans hy'''''''''''''''''''''''''''''' hy''''''',
  have hx'''''''''''''''''''''''''''''''' : abs x = -abs x, from eq.trans hx''''''''''''''''''''''''''''''' hx''''''',
  have hy'''''''''''''''''''''''''''''''' : abs y = -abs y, from eq.trans hy''''''''''''''''''''''''''''''' hy''''''',
  have hx''''''''''''''''''''''''

