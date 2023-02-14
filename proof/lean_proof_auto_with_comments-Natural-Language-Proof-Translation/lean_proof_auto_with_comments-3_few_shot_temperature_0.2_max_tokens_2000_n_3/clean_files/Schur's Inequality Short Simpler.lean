
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
/- FEW SHOT PROMPTS TO CODEX(START)
/--`theorem`
Power Set is Closed under Intersection
Let $S$ be a set.

Let $\powerset S$ be the power set of $S$.


Then:
:$\forall A, B \in \powerset S: A \cap B \in \powerset S$
`proof`
Let $A, B \in \powerset S$.

Then by the definition of power set, $A \subseteq S$ and $B \subseteq S$.

From Intersection is Subset we have that $A \cap B \subseteq A$.

It follows from Subset Relation is Transitive that $A \cap B \subseteq S$.

Thus $A \cap B \in \powerset S$ and closure is proved.
{{qed}}
-/
theorem power_set_intersection_closed {α : Type*} (S : set α) : ∀ A B ∈ 𝒫 S, (A ∩ B) ∈ 𝒫 S :=
begin
  -- $A$ and $B$ are sets. $A$ and $B$ belong to power set of $S$
  assume (A : set α) (hA : A ∈ 𝒫 S) (B : set α) (hB : B ∈ 𝒫 S),
  -- Then $A ⊆ S$ and $B ⊆ S$, by power set definition
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by auto [set.subset_of_mem_powerset, set.subset_of_mem_powerset],
  -- Then $(A ∩ B) ⊆ A$, by intersection of set is a subset
  have h2 : (A ∩ B) ⊆ A, from by auto [set.inter_subset_left],
  -- Then $(A ∩ B) ⊆ S$, by subset relation is transitive 
  have h3 : (A ∩ B) ⊆ S, from by auto [set.subset.trans],
  -- Hence $(A ∩ B) ∈  𝒫 S$, by power set definition
  show (A ∩ B) ∈  𝒫 S, from by auto [set.mem_powerset],
end

/--`theorem`
Square of Sum
 :$\forall x, y \in \R: \paren {x + y}^2 = x^2 + 2 x y + y^2$
`proof`
Follows from the distribution of multiplication over addition:

{{begin-eqn}}
{{eqn | l = \left({x + y}\right)^2
      | r = \left({x + y}\right) \cdot \left({x + y}\right)
}}
{{eqn | r = x \cdot \left({x + y}\right) + y \cdot \left({x + y}\right)
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = x \cdot x + x \cdot y + y \cdot x + y \cdot y
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = x^2 + 2xy + y^2
      | c = 
}}
{{end-eqn}}
{{qed}}
-/
theorem square_of_sum (x y : ℝ) : (x + y)^2 = (x^2 + 2*x*y + y^2)
begin
  -- expand the power
  calc (x + y)^2 = (x+y)*(x+y) : by auto [sq]
  -- distributive property of multiplication over addition gives:
  ... = x*(x+y) + y*(x+y) : by auto [add_mul]
  -- applying the above property further gives:
  ... = x*x + x*y + y*x + y*y : by auto [mul_comm, add_mul] using [ring]
  -- rearranging the terms using commutativity and adding gives:
  ... = x^2 + 2*x*y + y^2 : by auto [sq, mul_comm] using [ring]
end

/--`theorem`
Identity of Group is Unique
Let $\struct {G, \circ}$ be a group. Then there is a unique identity element $e \in G$.
`proof`
From Group has Latin Square Property, there exists a unique $x \in G$ such that:
:$a x = b$

and there exists a unique $y \in G$ such that:
:$y a = b$

Setting $b = a$, this becomes:

There exists a unique $x \in G$ such that:
:$a x = a$

and there exists a unique $y \in G$ such that:
:$y a = a$

These $x$ and $y$ are both $e$, by definition of identity element.
{{qed}}
-/
theorem group_identity_unique {G : Type*} [group G] : ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a :=
begin
  -- Group has Latin Square Property
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by auto using [use (a⁻¹ * b)],
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by auto using [use b * a⁻¹], 

  -- Setting $b = a$, this becomes:
  have h3 : ∀ a : G, ∃! x : G, a * x = a, from by auto [h1],
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from by auto [h2],

  -- These $x$ and $y$ are both $(1 : G)$, by definition of identity element
  have h5 : ∀ a : G, classical.some (h3 a).exists = (1 : G), from by auto [exists_unique.unique, h3, classical.some_spec, exists_unique.exists, mul_one],
  have h6 : ∀ a : G, classical.some (h4 a).exists = (1 : G), from by auto [exists_unique.unique, h4, classical.some_spec, exists_unique.exists, one_mul],

  show ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a, from by auto [h3, h4, exists_unique.unique, classical.some_spec, exists_unique.exists] using [use (1 : G)],
end

/--`theorem`
Schur's Inequality Short Simpler
Let $x, y, z \in \R_{\ge 0}$ be positive real numbers such that $x \ge y \ge z \ge 0$.

Let $t \in \R, t > 0$ be a (strictly) positive real number.


Then:
:$x^t \paren {x - y} \paren {x - z} + y^t \paren {y - z} \paren {y - x} + z^t \paren {z - x} \paren {z - y} \ge 0$

`proof`

Consider the expression:
:$\paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}$


We see that every term in the above is non-negative. So, directly:
:$(1): \quad \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z} \ge 0$

$(1) can be rearranged to Schur's inequality.
{{qed}}
-/
theorem 
FEW SHOT PROMPTS TO CODEX(END)-/
--OUTPUT 1
theorem schur_inequality_short_simpler {x y z : ℝ} (h1 : x ≥ y) (h2 : y ≥ z) (h3 : z ≥ 0) (t : ℝ) (h4 : t > 0) : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 :=
begin
  -- Consider the expression:
  have h5 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0,
  {
    -- We see that every term in the above is non-negative. So, directly:
    show (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by auto [mul_nonneg, pow_nonneg, sub_nonneg, h1, h2, h3, h4],
  },
  -- $(1) can be rearranged to Schur's inequality.
  show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by auto [h5, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem schur_inequality_short_simpler (x y z : ℝ) (h1 : x ≥ y) (h2 : y ≥ z) (h3 : z ≥ 0) (t : ℝ) (h4 : t > 0) : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 :=
begin
  -- Consider the expression:
  have h5 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0,
  {
    -- We see that every term in the above is non-negative. So, directly:
    show (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by auto [h1, h2, h3, h4, pow_pos, mul_nonneg, sub_nonneg, sub_nonneg_of_le, sub_nonneg_of_le],
  },

  -- $(1) can be rearranged to Schur's inequality.
  show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by auto [h5, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem schur_inequality_short_simpler (x y z : ℝ) (h1 : x ≥ y) (h2 : y ≥ z) (h3 : z ≥ 0) (t : ℝ) (h4 : t > 0) : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 :=
begin
  -- Consider the expression:
  have h5 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0,
  {
    -- We see that every term in the above is non-negative. So, directly:
    have h5a : (x - y) ≥ 0, from by auto [h1, sub_nonneg],
    have h5b : (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by auto [h1, h2, h3, h4, pow_pos, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub_nonneg, sub
end --Needs more than 2000 tokens!

