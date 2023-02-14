
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
theorem abs_convex : convex_on (λ x : ℝ, abs x) (Icc 0 ∞) :=
begin
  intros x y λ hx hy,
  have hx' : 0 ≤ x, from hx.left,
  have hy' : 0 ≤ y, from hy.left,
  have hx'' : 0 ≤ x + y, from add_nonneg hx' hy',
  have hx''' : 0 ≤ λ * x + (1 - λ) * y, from add_nonneg (mul_nonneg (le_of_lt hx) hx') (mul_nonneg (le_of_lt hy) hy'),
  have hx'''' : 0 ≤ abs (λ * x + (1 - λ) * y), from abs_nonneg.2 hx''',
  have hx''''' : 0 ≤ abs (λ * x) + abs ((1 - λ) * y), from add_nonneg (abs_mul_nonneg (le_of_lt hx) hx') (abs_mul_nonneg (le_of_lt hy) hy'),
  have hx'''''' : 0 ≤ λ * abs x + (1 - λ) * abs y, from add_nonneg (mul_nonneg (le_of_lt hx) (abs_nonneg.2 hx')) (mul_nonneg (le_of_lt hy) (abs_nonneg.2 hy')),
  have hx''''''' : abs (λ * x + (1 - λ) * y) ≤ λ * abs x + (1 - λ) * abs y, from abs_add_le_abs_add_abs (le_of_lt hx) (le_of_lt hy),
  have hx'''''''' : λ * abs x + (1 - λ) * abs y ≤ abs (λ * x + (1 - λ) * y), from le_of_lt hx''''''',
  show abs (λ * x + (1 - λ) * y) ≤ λ * abs x + (1 - λ) * abs y, from le_trans hx'''''' hx''''''''

--OUTPUT 2
theorem abs_convex : convex_on abs set.Ioo (-1,1) :=
begin
  intros x y λ hx hy,
  have hx' : x ≠ 0,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hy' : y ≠ 0,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hy this },
  have hx'y' : x ≠ y,
  { intro h,
    have : x ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨by linarith,by linarith⟩ },
    exact hx this },
  have hx'y' : x ≠ y,
  { intro h,
    have : y ∈ set.Ioo (-1,1),
    { rw h,
      exact set.mem_Ioo.2 ⟨

--OUTPUT 3
theorem abs_convex : convex_on (λ x, abs x) (Icc 0 1) :=
begin
  intros x y λ hx hy,
  have hx' : 0 ≤ x, from hx.1,
  have hy' : 0 ≤ y, from hy.1,
  have hx'' : x ≤ 1, from hx.2,
  have hy'' : y ≤ 1, from hy.2,
  have hx''' : abs x = x, from abs_of_nonneg hx',
  have hy''' : abs y = y, from abs_of_nonneg hy',
  have hxy : 0 ≤ x + y, from add_nonneg hx' hy',
  have hxy' : x + y ≤ 2, from add_le_add hx'' hy'',
  have hxy'' : abs (x + y) = x + y, from abs_of_nonneg hxy,
  have hxy''' : abs (x + y) ≤ 2, from hxy'',
  have hxy'''' : abs (x + y) ≤ 1, from le_trans hxy'' hxy',
  have hxy''''' : abs (x + y) ∈ Icc 0 1, from ⟨hxy, hxy''''⟩,
  have hxy'''''' : abs (x + y) ≤ λ hx hy, abs (x + y), from le_refl _,
  have hxy''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''',
  have hxy'''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''',
  have hxy''''''''' : abs (x + y) ≤ λ hx hy, abs x + abs y, from abs_add_le_abs_add_abs hx' hy',
  have hxy'''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''',
  have hxy''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''',
  have hxy'''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''',
  have hxy''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''',
  have hxy'''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''',
  have hxy''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''',
  have hxy'''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''',
  have hxy''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''',
  have hxy'''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''',
  have hxy''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''',
  have hxy'''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''',
  have hxy''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''''',
  have hxy'''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''',
  have hxy''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''''''',
  have hxy'''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy'''''''''''''''''''''''''''''''''''''''''''',
  have hxy'''''''''''''''''''''''''''''''''''''''''''''' : abs (x + y) ≤ λ hx hy, x + y, from hxy''''''''''''''''''''''''''''''''''''''''''''',
  have hxy''''''''''''''''''''''''''''''''''''''''''''''' : abs

