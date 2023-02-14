
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
--Prove that \mathbb{R}^n is paracompact in Lean mathlib
 
--OUTPUT 1
theorem R_n_paracompact : paracompact (real_normed_vector_space.to_topological_space R^n) :=
begin
  apply paracompact_iff_locally_compact_openly_generated.mpr,
    split, apply locally_compact_iff_to_discrete_subset.mp,
      exact discrete_subset_iff_open.mpr zero_mem_ball,
    exact discrete_subspace_iff_open.mpr zero_mem_ball

--OUTPUT 2
theorem paracompact_of_euclidean : paracompact_space ℝ^n := begin
--Use the paracompact_iff_iff_open_cover_leash from mathlib
apply paracompact_iff_iff_open_cover_leash.mpr,
--Use forall_swap in mathlib to prove the iff
apply forall_swap,
--Use classical logic
apply classical.all_comm,
--Prove that \mathbb{R}^n is paracompact given a cover
intros F hF,
--Use the exists_locally_finite_subcover from mathlib
apply exists_locally_finite_subcover,
--Now prove the subcover given a point
intros x hx,unfold_locals,

--Now we set up the proof of the first part of the subcover which is that x is contained in some U in the subcover
--First we use the assumption that F is a cover
cases hF x hx with U hU,
use [U],
--Then we use the definition of a cover
exact hU,

--Now for the second part of the subcover which is that the intersection of U with a ball is contained in the original cover
--First we define U to be the finite subcover, i.e. the finite subcover restricted to a ball
have hF2 : ∀ x : ℝ^n, ∃ (U : set (ℝ^n)) (H : x ∈ U) ,finite {V : set (ℝ^n) | ∃ y, y ∈ U ∧ y ∈ V ∧ V ∈ F},
{
--Use dforall in mathlib
  apply dforall,
  --Use the hF assumption
  apply hF,
},

--Now we set up the proof that the ball is covered for all points
intros y hy,
--Prove the finite subcover
cases hF2 y hy with U hU,
use [U],
--Then prove that U has the required property
exact hU.2,

--Now we prove the finite intersection property
intros U hU,
--Define a ball B around U
have : ∃ B : set (ℝ^n) , ∀ p ∈ B, ∃ q : ℝ^n, q ∈ U ∧ dist p q < d ,
{
--Use exists.intro
  apply exists.intro,
--Define B as the ball around U
  use { p : ℝ^n | ∃ q ∈ U, dist p q < d },
--Now prove that p is in B
  intros p hp,
  --Use exists.intro
  apply exists.intro,
  --Define q to be U
  use [U],
  --Now prove that q is in U
  exact hU.1,
  --Prove that q is in B
  exact hp,
},

--Define the ball B around U
cases this with B hB,
--We use the fact that B is finite
have finiteB : finite B,
{
--We use the fact that U is finite
  have finiteU : finite U,
  {
--Now we use the fact that U is a finite subcover
    apply hU.2,
  },
--Now we use the fact that B is a subset of U with finiteU
  apply finite.subset,
  --Define B as the ball around U
  use { p : ℝ^n | ∃ q ∈ U, dist p q < d },
  have hB2 : ∀ p ∈ B, ∃ q : ℝ^n, q ∈ U ∧ dist p q < d,
  {
    apply hB,
  },
  intros x hx,
  cases hB2 x hx with q hq,
  cases hq with hq2 hq3,
  use [q],
  exact hq2,
},

--We use the fact that U is finite
have finiteU : finite U,
{
--Now we use the fact that U is a finite subcover
  apply hU.2,
},

--Now we get the finite intersection property
have finite_intersection_property : finite (B ∩ U),
{
--Use the fact that B is finite
  apply finite.inter,
  exact finiteU,
  exact finiteB,
},

--Now we use the fact that B is a subset of U with finiteU
use [B],
have hB2 : ∀ p ∈ B, ∃ q : ℝ^n, q ∈ U ∧ dist p q < d,
{
  apply hB,
},
intros x hx,
cases hB2 x hx with q hq,
cases hq with hq2 hq3,
use [q],
exact hq2,
--Now we get that B intersected with U is finite and contained in F
exact finite_intersection_property,

--OUTPUT 3
theorem Rn_paracompact:
    assumes "n > 0"
    shows "paracompact (ℝ^n)"
...

