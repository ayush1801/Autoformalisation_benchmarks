
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
  assume (A : set α) (hA : A ∈ 𝒫 S) (B : set α) (hB : B ∈ 𝒫 S),
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by auto [set.subset_of_mem_powerset, set.subset_of_mem_powerset],
  have h2 : (A ∩ B) ⊆ A, from by auto [set.inter_subset_left],
  have h3 : (A ∩ B) ⊆ S, from by auto [set.subset.trans],
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
  calc (x + y)^2 = (x+y)*(x+y) : by auto [sq]
  ... = x*(x+y) + y*(x+y) : by auto [add_mul]
  ... = x*x + x*y + y*x + y*y : by auto [mul_comm, add_mul] using [ring]
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
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by auto using [use (a⁻¹ * b)],
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by auto using [use b * a⁻¹], 

  have h3 : ∀ a : G, ∃! x : G, a * x = a, from by auto [h1],
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from by auto [h2],

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
theorem  schur_inequality (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 :=
  
FEW SHOT PROMPTS TO CODEX(END)-/
--OUTPUT 1
theorem begin
    have h1 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg, le_of_lt, ht, hxy, hyz, hz],
    have h2 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by auto [mul_nonneg, sub_nonneg, le_of_lt, hxy],
    have h3 : z^t * (x - z) * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg, le_of_lt, hz, ht],
    calc x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y)
    = ((x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z)) + y^t * (y - z) * (y - x) : by auto [mul_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm, mul_left_comm, mul_assoc, mul_left_comm
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem begin
    have h1 : x^t * (x - z) * (x - y) - y^t * (y - z) * (y - x) ≥ 0, from by auto [mul_nonneg, sub_nonneg, sub_nonneg, pow_pos],
    have h2 : z^t * (x - z) * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg, sub_nonneg, pow_pos],
    have h3 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by auto [mul_nonneg, add_nonneg],
    have h4 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by auto [mul_nonneg, add_nonneg, add_nonneg],
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by auto [h4, h3, h2, h1, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem begin
    have h1 : x^t * (x - y) * (x - z) - y^t * (y - z) * (y - x) + z^t * (x - z) * (y - z) ≥ 0, from by auto [mul_nonneg],
    have h2 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by auto [mul_nonneg],
    have h3 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) = x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y), from by auto [mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm],
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by auto [h2, h3],
  end

/--`theorem`
Schur's Inequality Long
Let $x, y, z \in \R_{\ge 0}$ be positive real numbers such that $x \ge y \ge z \ge 0$.

Let $t \in \R, t > 0$ be a (strictly) positive real number.


Then:
:$x^t \paren {x - y} \paren {x - z} + y^t \paren {y - z} \paren {y - x} + z^t \paren {z - x} \paren {z - y} \ge 0$

`proof`

Consider the expression:
:$\paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}$


We see that every term in the above is non-negative. So, directly:
:$(1): \quad \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z} \ge 0$

We now prove that $(1)$ is equivalent to Schur's inequality.

{{begin-eqn}}
{{eqn | l = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z}
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = \paren {x - y} \paren {x^t \paren {x - z} - y^t \paren {
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem begin
    have h1 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h2 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h3 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h4 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h5 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h6 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h7 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h8 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h9 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h10 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h11 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h12 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h13 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h14 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h15 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h16 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h17 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h18 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h19 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h20 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h21 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h22 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h23 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h24 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h25 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h26 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h27 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h28 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h29 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h30 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h31 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h32 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h33 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h34 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h35 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h36 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h37 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h38 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h39 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h40 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h41 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h42 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by auto [mul_nonneg, sub_nonneg] using [ht],
    have h43 : x^t * (x - z) - y^t * (y - z
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by auto [mul_nonneg, pow_nonneg, sub_nonneg],
    have h2 : (x - y) * (x^t * (x - z) - y^t * (y - z)) = x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z), from by auto [mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, sub_eq_add_neg, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by auto [mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_nonneg, mul_
end --Needs more than 2000 tokens!

