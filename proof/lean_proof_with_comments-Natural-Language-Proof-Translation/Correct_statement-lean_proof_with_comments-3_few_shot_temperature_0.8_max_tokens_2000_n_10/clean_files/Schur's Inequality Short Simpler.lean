
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
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by {split,apply set.subset_of_mem_powerset,exact hA,apply set.subset_of_mem_powerset,exact hB},
  -- Then $(A ∩ B) ⊆ A$, by intersection of set is a subset
  have h2 : (A ∩ B) ⊆ A, from by apply set.inter_subset_left,
  -- Then $(A ∩ B) ⊆ S$, by subset relation is transitive 
  have h3 : (A ∩ B) ⊆ S, from by {apply set.subset.trans h2 h1.left},
  -- Hence $(A ∩ B) ∈  𝒫 S$, by power set definition
  show (A ∩ B) ∈  𝒫 S, from by {apply set.mem_powerset h3},
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
  calc (x + y)^2 = (x+y)*(x+y) : by rw sq
  -- distributive property of multiplication over addition gives:
  ... = x*(x+y) + y*(x+y) : by rw add_mul
  -- applying the above property further gives:
  ... = x*x + x*y + y*x + y*y : by {rw [mul_comm x (x+y),mul_comm y (x+y)], rw [add_mul,add_mul], ring}
  -- rearranging the terms using commutativity and adding gives:
  ... = x^2 + 2*x*y + y^2 : by {repeat {rw ← sq}, rw mul_comm y x, ring}
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
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by {
    assume a b : G, use a⁻¹ * b, obviously, },
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by {
    assume a b : G, use b * a⁻¹, obviously, }, 

  -- Setting $b = a$, this becomes:
  have h3 : ∀ a : G, ∃! x : G, a * x = a, from 
    assume a : G, h1 a a,
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from
    assume a : G, h2 a a,

  -- These $x$ and $y$ are both $(1 : G)$, by definition of identity element
  have h5 : ∀ a : G, classical.some (h3 a).exists = (1 : G), from assume a :G,
    exists_unique.unique (h3 a) (classical.some_spec (exists_unique.exists (h3 a)))
    (mul_one a),
  have h6 : ∀ a : G, classical.some (h4 a).exists = (1 : G), from assume a : G,
    exists_unique.unique (h4 a) (classical.some_spec (exists_unique.exists (h4 a))) (one_mul a), 

  show ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a, from by {
    use (1 : G),
    have h7 : ∀ e : G, (∀ a : G, e * a = a ∧ a * e = a) → e = 1, from by {
      assume (e : G) (hident : ∀ a : G, e * a = a ∧ a * e = a),
      have h8 : ∀ a : G, e = classical.some (h3 a).exists, from assume (a : G),
        exists_unique.unique (h3 a) (hident a).right
        (classical.some_spec (exists_unique.exists (h3 a))), 
      have h9 : ∀ a : G, e = classical.some (h4 a).exists, from assume (a : G),
        exists_unique.unique (h4 a) (hident a).left
        (classical.some_spec (exists_unique.exists (h4 a))),
      show e = (1 : G), from eq.trans (h9 e) (h6 _),     
    },
    exact ⟨by obviously, h7⟩,
  }
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
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from
    calc (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) 
          = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (z^t * (x - z)) * (y - z) : by rw ← mul_assoc
    ... = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (x^t * (x - y)) * (y - z) : by {rw mul_comm (z^t * (x - z)) (y - z),rw ← mul_assoc_right,rw ← pow_mul,rw mul_comm (x^t) (z^t),rw ← mul_assoc_right,rw ← pow_mul,rw mul_comm x z,rw ← ht}
    ... = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (x^t * (x - y)) * (y - z) : by rw ← mul_assoc
    ... = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (x^t * (x - y)) * (y - z) : by rw ← mul_assoc
    ... = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (x^t * (x - y)) * (y - z) : by rw ← mul_assoc
    ... = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (x^t * (y - x)) * (x - z) : by rw mul_comm y x 
    ... = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (y^t * (x - y)) * (x - z) : by rw ← pow_mul
    ... = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (y^t * (x - y)) * (x - z) : by rw ← mul_assoc_right
    ... = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (y^t * (x - z)) * (x - y) : by rw mul_comm (x - y) (x - z)
    ... = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (y^t * (x - z)) * (x - y) : by rw ← mul_assoc_right
    ... = (x - y) * (x^t * (x - z) - y^t * (y - z)) + (y^t * (z - x)) * (x - y) : by rw mul_comm x z
    ... = x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z) + y^t * (z - x) * (x - y) : by rw ← mul_assoc 
    ... = x^t * (x - y) * (x - z) + y^t * (x - y) * (z - x) + y^t * (z - x) * (x - y) : by rw mul_comm y x
    ... = x^t * (x - y) * (x - z) + y^t * (x - z) * (x - y) + y^t * (z - x) * (x - y) : by rw mul_comm x z
    ... = x^t * (x - y) * (x - z) + y^t * (x - z) * (x - y) + z^t * (x - y) * (x - z) : by rw ← pow_mul
    ... = x^t * (x - y) * (x - z) + y^t * (x - z) * (x - y) + z^t * (y - x) * (y - z) : by {rw mul_comm (x - z) (x - y),rw ← mul_assoc_right,rw ← pow_mul,rw mul_comm x z,rw ← mul_assoc_right,rw ← pow_mul,rw mul_comm x z,rw ← mul_assoc_right,rw ← pow_mul,rw mul_comm y x,rw ← mul_assoc_right,rw ← pow_mul,rw mul_comm y x}
    ... = x^t * (x - y) * (x - z) + y^t * (x - z) * (x - y) + z^t * (y - x) * (y - z) : by rw ← mul_assoc
    ... = x^t * (x - y) * (x - z) + y^t * (x - z) * (x - y) + z^t * (y - z) * (y - x) : by rw mul_comm z y
    ... = x^t * (x - y) * (x - z) + y^t * (x - z) * (x - y) + z^t * (y - z) * (y - x) : by rw ← mul_assoc_left
    ... = x^t * (x - y) * (x - z) + y^t * (x - z) * (x - y) + z^t * (y - z) * (y - x) : by rw ← mul_assoc_left
    ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (y - z) * (y - x) : by rw mul_comm x y
    ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (y - z) * (y - x) : by rw ← mul_assoc_right
    ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (y - z) * (y - x) : by rw ← mul_assoc_right
    ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (y - z) * (y - x) : by rw ← mul_assoc_right
    ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (y - x) * (y - z) : by rw mul_comm y x
    ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (x - y) * (y - z) : by rw mul_comm z y
    ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (x - y) * (y - z) : by rw mul_comm (x - y) (y - z)
    ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (x - y) * (y - z) : by rw ← mul_assoc_right
    ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem begin
    -- Consider the expression:
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from
    begin
      have h2 : x ≥ y + z, from le_trans hxy (add_le_add_right (le_of_eq hyz) hz),
      have h3 : 0 ≥ x - y - z, from sub_le_iff_le_add.1 (le_of_eq h2),
      have h4 : 0 ≥ z - (x - y), from sub_le_iff_le_add.2 (le_of_eq h3),
      have h5 : 0 ≥ x - y, from le_trans hz h4,
      have h6 : 0 ≥ (x - y)^2, from by {apply pow_two_nonneg},
      have h7 : (x - y)^2 * 0 ≥ (x - y)^2 * ((x - y)^2 * 0), from by {apply mul_nonneg_of_nonneg_of_nonneg h6,apply mul_nonneg_of_nonneg_of_nonneg h5,apply pow_two_nonneg},
      have h8 : (x - y)^2 * 0 ≥ (x - y)^2 * ((x - z)^2 * 0), from by {
        apply mul_le_of_le_left h7,
        apply ht,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
      },
      have h9 : (x - y)^2 * ((x - z)^2 * 0) ≥ (x - y)^2 * ((x - z)^2 * (y - z)^2), from by {
        rw pow_two_mul,
        rw pow_two_mul,
        apply ht,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
      },
      have h10 : (x - y)^2 * ((x - z)^2 * (y - z)^2) ≥ (x - y)^2 * ((x - z)^2 * (y - z)^2) * 0, from by {
        apply mul_le_of_le_left h9,
        apply ht,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
      },
      have h11 : (x - y)^3 * ((x - z)^2 * (y - z)^2) ≥ (x - y)^2 * ((x - z)^2 * (y - z)^2), from by {
        rw pow_two_mul,
        apply ht,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
      },
      have h12 : (x - y)^2 * ((x - z)^2 * (y - z)^2) ≥ (x - y)^2 * ((x - z)^2 * (y - z)^2), from by {
        apply mul_le_of_le_right h10,
        apply h11,
      },
      have h13 : (x - y)^2 * ((x - z)^2 * (y - z)^2) ≥ (x - y)^2 * ((y - z)^2 * (x - z)^2), from by {
          rw pow_two_mul,
          apply ht,
          apply pow_two_nonneg,
          apply pow_two_nonneg,
          apply pow_two_nonneg,
        },
      have h14 : (x - y)^3 * ((y - z)^2 * (x - z)^2) ≥ (x - y)^2 * ((y - z)^2 * (x - z)^2), from by {
        rw pow_two_mul,
        apply ht,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
      },
      have h15 : (x - y)^2 * ((y - z)^2 * (x - z)^2) ≥ (x - y)^2 * ((y - z)^2 * (x - z)^2), from by {
        apply mul_le_of_le_right h12,
        apply h13,
      },
      have h16 : (x - y)^2 * ((x - z)^2 * y^t) ≥ (x - y)^2 * ((x - z)^2 * (y - z)^2), from by {
        apply mul_le_of_le_right h15,
        apply h14,
      },
      have h17 : (x - y)^2 * ((x - z)^2 * y^t) ≥ (x - y)^2 * ((x - z)^2 * y^t), from by {
        apply mul_le_of_le_right h16,
        apply h11,
      },
      have h18 : (x - y)^2 * ((x - z)^2 * y^t) ≥ (x - y)^2 * (y^t * (x - z)^2), from by {
        rw mul_comm,
        apply h17,
      },
      have h19 : (x - y)^3 * (y^t * (x - z)^2) ≥ (x - y)^2 * (y^t * (x - z)^2), from by {
        rw pow_two_mul,
        apply ht,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
      },
      have h20 : (x - y)^2 * (y^t * (x - z)^2) ≥ (x - y)^2 * (y^t * (x - z)^2), from by {
        apply mul_le_of_le_right h18,
        apply h19,
      },
      have h21 : (x - y)^2 * (y^t * (x - z)^2) ≥ y^t * (x - y)^2 * (x - z)^2, from by {
        rw mul_assoc,
        apply h20,
      },
      have h22 : (x - y)^3 * y^t * (x - z)^2 ≥ y^t * (x - y)^2 * (x - z)^2, from by {
        rw pow_two_mul,
        apply ht,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
      },
      have h23 : y^t * (x - y)^2 * (x - z)^2 ≥ y^t * (x - y)^2 * (x - z)^2, from by {
        apply mul_le_of_le_right h21,
        apply h22,
      },
      have h24 : y^t * (x - y)^2 * (x - z)^2 ≥ (x - y)^2 * y^t * (x - z)^2, from by {
        rw mul_assoc,
        apply h23,
      },
      have h25 : (x - y)^2 * y^t * (x - z)^2 ≥ (x - y)^2 * y^t * (x - z)^2, from by {
        apply mul_le_of_le_right h24,
        apply h19,
      },
      have h26 : (x - y)^2 * y^t * (x - z)^2 ≥ (x - y)^2 * (x - z)^2 * y^t, from by {
        rw mul_comm,
        apply h25,
      },
      have h27 : (x - y)^3 * (x - z)^2 * y^t ≥ (x - y)^2 * (x - z)^2 * y^t, from by {
        rw pow_two_mul,
        apply ht,
        apply pow_two_nonneg,
        apply pow_two_nonneg,
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem begin
    have hxz : x ≥ z, by linarith,
    have hyx : y ≥ x, by linarith,

    have hxz0 : x - z ≥ 0, from by { linarith },
    have hyz0 : y - z ≥ 0, from by { linarith },

    have hxzx : (x - z) * x ≥ 0, from by { linarith },
    have hyzy : (y - z) * y ≥ 0, from by { linarith },

    have hxzx_0 : (x - z) * x > 0, from by { linarith },
    have hyzy_0 : (y - z) * y > 0, from by { linarith },

    have hxy_0 : (x - y) * x > 0, from by { linarith },
    have hyx_0 : (y - x) * y > 0, from by { linarith },

    have hterm1 : x^t * (x - z) * (x - y) ≥ 0, from by { linarith },
    have hterm2 : x^t * (x - y) * (x - z) ≥ 0, from by { linarith },
    have hterm3 : y^t * (y - x) * (y - z) ≥ 0, from by { linarith },
    have hterm4 : y^t * (y - z) * (y - x) ≥ 0, from by { linarith },
    have hterm5 : z^t * (z - x) * (z - y) ≥ 0, from by { linarith },
    have hterm6 : z^t * (z - y) * (z - x) ≥ 0, from by { linarith },

    have hterm7 : x^t * (x - z) * (x - y) = x^t * (x - y) * (x - z), from by linarith,
    have hterm8 : y^t * (y - z) * (y - x) = y^t * (y - x) * (y - z), from by linarith,
    have hterm9 : z^t * (z - y) * (z - x) = z^t * (z - x) * (z - y), from by linarith,

    have hterm10 : x^t * (x - z) * (x - y) ≥ y^t * (y - z) * (y - x), from by linarith,
    have hterm11 : y^t * (y - x) * (y - z) ≥ z^t * (z - x) * (z - y), from by linarith,
    have hterm12 : x^t * (x - y) * (x - z) ≥ z^t * (z - y) * (z - x), from by linarith,

    suffices hterm13 : (x^t * (x - z)) * (x - y) + (y^t * (y - z)) * (y - x) + (z^t * (z - x)) * (z - y) ≥ 0,
    by linarith,

    have hterm14 : x^t * (x - z) * (x - y) - y^t * (y - z) * (y - x) ≥ 0, from by linarith,
    have hterm15 : y^t * (y - z) * (y - x) - z^t * (z - x) * (z - y) ≥ 0, from by linarith,
    have hterm16 : z^t * (z - y) * (z - x) - x^t * (x - y) * (x - z) ≥ 0, from by linarith,

    -- changing the RHS of + to (x - y)*(x^t - y^t) may have automatically used the fact that the expression inside the paren is non-negative,
    -- whereas we cannot use that fact here.
    have hterm17 : (x - y)*(x^t - y^t) ≥ 0, from by linarith,

    have hterm18 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from 
    begin
      suffices hterm19 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥
                          (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z),
      from linarith,
      linarith,
    end,

    calc x^t * (x - z) * (x - y) + y^t * (y - x) * (y - z) + z^t * (z - x) * (z - y) 
        = x^t * (x - z) * (x - y) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) : by linarith
    ... = x^t * (x - z) * (x - y) + y^t * (y - z) * (y - x) : by linarith
    ... ≥ 0 : by linarith
  end

/--`theorem`
Square of Absolute Value is Positive Real Number
For any real number $x \in \R$, $\absval {x}^2 \in \R_{\ge 0}$
`proof`
We have that:
:$\absval{x} = \paren {x^2}^{\frac 1 2}$

Since $x^2 \ge 0$ and $\paren \cdot^{\frac 1 2}$ is a non-decreasing function, we get that:
:$\absval{x}^2 = x^2$
{{qed}}
-/
theorem square_of_absval (x : ℝ) : (abs x)^2 = x^2 :=
begin
  -- $\absval{x} = \paren {x^2}^{\frac 1 2}$
  have h1 : abs x = sqrt x^2,
    from calc abs x = (sqrt (x^2))^2 : by { rw sq, linarith }
  ... = sqrt x^2 : by { rw sq, linarith },

  -- Since $x^2 \ge 0$ and $\paren \cdot^{\frac 1 2}$ is a non-decreasing function, we get that:
  have h2 : (sqrt x^2)^2 ≥ 0, from by { repeat {rw ← sq}, linarith },

  -- $\absval{x}^2 = x^2$
  show (abs x)^2 = x^2, by linarith
end

--OUTPUT 4
theorem by { have h1 : x^t * (x - z) - y^t * (y - z) ≥ 0, from le_of_mul_le_mul_right (sub_nonneg.mpr
    ⟨le_of_eq (zero_mul.mpr hz),sub_nonneg.mpr ⟨le_of_eq (mul_zero.mpr hz),hyz⟩⟩)
    (sub_nonneg (hxy) (hyz)),
  have h2 : x^t * (x - z) - y^t * (y - z) ≥ 0, from le_of_mul_le_mul_left (sub_nonneg.mpr
    ⟨le_of_eq (zero_mul.mpr hz),sub_nonneg.mpr ⟨le_of_eq (mul_zero.mpr hz),hyz⟩⟩)
    (sub_nonneg (hxy) (hyz)),
  have h3 : z^t * (x - z) ≥ 0, from le_of_mul_le_mul_right
    (sub_nonneg.mpr ⟨le_of_eq (zero_mul.mpr hz),sub_nonneg.mpr ⟨le_of_eq
    (mul_zero.mpr hz),hz⟩⟩) ht,
  have h4 : z^t * (y - z) ≥ 0, from le_of_mul_le_mul_right
    (sub_nonneg.mpr ⟨le_of_eq (zero_mul.mpr hz),sub_nonneg.mpr ⟨le_of_eq
    (mul_zero.mpr hz),hz⟩⟩) ht,
  have h5 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0, from mul_nonneg h1
    (sub_nonneg (hxy) (hyz)),
  have h6 : z^t * (x - z) * (y - z) ≥ 0, from mul_nonneg h3 (sub_nonneg (hxy) (hyz)),
  have h7 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from add_nonneg h5 h6,
  have h8 : (x^t * (x - z) - y^t * (y - z)) + (z^t * (x - z) * (y - z)) ≥ 0, from
    le_of_mul_le_mul_left h7 (sub_nonneg (hxy) (hyz)),
  have h9 : (x^t * (x - z) + z^t * (x - z) * (y - z)) - (y^t * (y - z)) ≥ 0, from
    sub_nonneg.mpr ⟨h8,(le_of_mul_le_mul_left (sub_nonneg (hyz) (hxy)) ht)⟩,
  have h10 : (x^t * (x - z) + x^t * (y - z) * (z - x)) - (y^t * (y - z)) ≥ 0, begin
    rw ← sub_eq_add_neg,
    rw sub_right_comm,
    rw ← sub_eq_add_neg,
    rw sub_right_comm,
    rw ← mul_assoc,
    rw mul_comm,
    rw mul_assoc,
    show (x^t * (x - z) + x^t * (y - z) * (z - x)) - (y^t * (y - z)) ≥ 0, from h9,
  end,
  have h11 : (x^t * (x - z) * (x - y) + x^t * (y - z) * (z - x)) - (y^t * (y - z)) ≥ 0, begin
    rw ← sub_eq_add_neg,
    rw sub_right_comm,
    rw ← sub_eq_add_neg,
    rw sub_right_comm,
    rw ← mul_assoc,
    rw mul_comm,
    rw mul_assoc,
    show (x^t * (x - z) * (x - y) + x^t * (y - z) * (z - x)) - (y^t * (y - z)) ≥ 0, from h10,
  end,
  have h12 : (x^t * (x - z) * (x - y) - (y^t * (y - z))) + (x^t * (y - z) * (z - x)) ≥ 0, from
    add_nonneg h11 (mul_nonneg (mul_nonneg (sub_nonneg (hxy) (hyz)) (sub_nonneg (hyz) (hxy))) ht),
  have h13 : (y^t * (y - z) * (y - x)) + (x^t * (y - z) * (z - x)) ≥ 0, from
    le_of_mul_le_mul_left h12 (sub_nonneg (hyz) (hxy)),
  have h14 : (x^t * (y - z) * (z - x)) + (z^t * (z - x) * (y - x)) ≥ 0, from
    le_of_mul_le_mul_left h13 (sub_nonneg (hxy) (hyz)),
  have h15 : (x^t * (y - z) * (z - x)) + (z^t * (x - z) * (y - x)) ≥ 0, from
    le_of_mul_le_mul_right h14 (sub_nonneg (hxy) (hyz)),
  have h16 : (x^t * (y - z) * (x - z)) + (z^t * (x - z) * (y - x)) ≥ 0, from
    le_of_mul_le_mul_left h15 (sub_nonneg (hyz) (hz)),
  have h17 : (y^t * (x - z) * (x - y)) + (z^t * (x - z) * (y - x)) ≥ 0, from
    le_of_mul_le_mul_right h16 (sub_nonneg (hxy) (hyz)),
  have h18 : (y^t * (y - z) * (x - y)) + (z^t * (x - z) * (y - x)) ≥ 0, from
    le_of_mul_le_mul_left h17 (sub_nonneg (hxy) (hyz)),
  have h19 : (x^t * (x - z) * (x - y)) + (y^t * (y - z) * (x - y)) + (z^t * (x - z) * (y - x)) ≥ 0, from
    le_of_mul_le_mul_left h18 (sub_nonneg (hxy) (hyz)),
  have h20 : (x^t * (x - z) * (x - y)) + (y^t * (y - z) * (y - x)) + (z^t * (x - z) * (y - x)) ≥ 0, from
    le_of_mul_le_mul_right h19 (sub_nonneg (hyz) (hz)),
  have h21 : (x^t * (x - z) * (x - y)) + (y^t * (y - z) * (y - x)) + (z^t * (x - z) * (z - y)) ≥ 0, from
    le_of_mul_le_mul_left h20 (sub_nonneg (hz) (hxy)),
  have h22 : (x^t * (x - z) * (x - y)) + (y^t * (y - z) * (y - x)) + (z^t * (z - x) * (z -
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem begin
    have h4 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by {
      rw [sub_eq_add_neg,add_sub_cancel',sub_eq_add_neg] at hxy,
      rw [sub_eq_add_neg,add_sub_cancel',sub_eq_add_neg] at hyz,
      apply sub_nonneg.mpr,
      apply neg_nonpos.mp,
      rw [sub_eq_add_neg,add_sub_cancel',sub_eq_add_neg] at hxy,
      rw [sub_eq_add_neg,add_sub_cancel',sub_eq_add_neg] at hyz,
      apply add_nonpos_of_nonpos_of_nonpos,
      apply sub_nonpos.mpr,
      apply mul_nonpos_of_nonpos_of_nonpos_right,
      exact mul_pos hz ht,
      apply neg_nonneg.mpr,
      apply sub_nonpos.mpr,
      apply mul_nonpos_of_nonpos_of_nonpos_left,
      exact mul_pos hz ht,
      exact mul_nonpos_of_nonneg_of_nonpos hxy ht,
      apply sub_nonpos.mpr,
      exact mul_nonpos_of_nonneg_of_nonpos hyz ht,
      exact mul_nonpos_of_nonneg_of_nonpos hxy ht,
      },
    have h5 : (x - z) * (y - z) ≥ 0, from mul_nonneg hz (sub_nonneg.mpr hyz),
    have h6 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from 
      add_nonneg (mul_nonneg (sub_nonneg.mpr hxy) h4) h5,
    exact calc
      x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥
          0 + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) : 
          by {rw zero_add, apply add_nonneg h6 (mul_nonneg (sub_nonneg.mpr hyz) (mul_nonneg (sub_nonneg.mpr (sub_nonneg.mpr hxy)) ht))}
      ... = y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) + y^t * (y - z) * (y - x) : by {rw add_comm (y^t * (y - z) * (y - x)), rw add_assoc}
      ... = y^t * (y - z) * (y - x) + (z^t * (z - x) * (z - y) + y^t * (y - z) * (y - x)) : by {rw add_comm (z^t * (z - x) * (z - y))} 
      ... = y^t * (y - z) * (y - x) + (y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y)) : by {rw add_comm (z^t * (z - x) * (z - y))} 
      ... =  y^t * (y - z) * (y - x) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) : by {rw add_assoc}
      ... =  2 * y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) : by {rw mul_comm (2 : ℝ) y^t, rw [← two_mul (y^t)], ring}
      ... =  2*y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) + 2*y^t * (y - z) * (y - x) : by {rw ← two_mul (y^t * (y - z) * (y - x)), rw add_comm 2}
      ... =  2*y^t * (y - z) * (y - x) + (z^t * (z - x) * (z - y) + 2*y^t * (y - z) * (y - x)) : by {rw add_comm (z^t * (z - x) * (z - y))}
      ... =  2*y^t * (y - z) * (y - x) + (2*y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y)) : by {rw add_comm (z^t * (z - x) * (z - y))}
      ... =  2*(y^t * (y - z) * (y - x) + y^t * (y - z) * (y - x)) + z^t * (z - x) * (z - y) : by {rw add_assoc}
      ... =  2*(y^t * (y - z) * (y - x) + y^t * (y - z) * (y - x)) + z^t * (z - x) * (z - y) : by {rw add_assoc}
      ... =  2*2*y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) : by {rw ← two_mul (y^t * (y - z) * (y - x)), rw mul_comm (2 : ℝ) 2}
      ... =  4*y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) : by {rw ← two_mul (2*y^t * (y - z) * (y - x)), rw mul_comm (2 : ℝ) 2}
      ... =  4*y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) + 2*z^t * (z - x) * (z - y) : by {rw ← two_mul (z^t * (z - x) * (z - y)), rw add_comm 2} 
      ... =  4*y^t * (y - z) * (y - x) + (z^t * (z - x) * (z - y) + 2*z^t * (z - x) * (z - y)) : by {rw add_comm (z^t * (z - x) * (z - y))} 
      ... =  4*y^t * (y - z) * (y - x) + (2*z^t * (z - x) * (z - y) + z^t * (z - x) * (z - y)) : by {rw add_comm (z^t * (z - x) * (z - y))} 
      ... =  4*y^t * (y - z) * (y - x) + (2*(z^t * (z - x) * (z - y)) + z^t * (z - x) * (z - y)) : by {rw add_assoc}
      ... =  4*y^t * (y - z) * (y - x) + (3*z^t * (z - x) * (z - y)) : by {rw ← two_mul (z^t * (z - x) * (z - y)), rw mul_comm (2 : ℝ) 2}
      ... =  3*y^t * (y - z) * (y - x) + 3*z^t * (z - x) * (z - y) : by
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem begin
    have h1 : ∀ a b c : ℝ, b - a ≤ c → b ≤ a + c, from
      assume a b c : ℝ,
      assume h : b - a ≤ c,
      show b ≤ a + c, from by {rw ← sub_eq_add_neg a b at h, rw ← add_assoc a c (-a) at h, rw add_neg_cancel_left at h, rw add_comm (-a) b at h, exact h},
    have h2 : ∀ a b c : ℝ, a ≤ b → a - c ≤ b - c, from
      assume a b c : ℝ,
      assume h : a ≤ b, show a - c ≤ b - c, from by {rw add_sub_cancel a c at h, rw sub_eq_add_neg b c at h, rw ← add_assoc a c (-c) at h, rw add_neg_cancel_left at h, rw add_comm (-c) b at h, exact h},
    have h3 : ∀ a b c d : ℝ, a ≤ b → a - c ≤ d → b - c ≤ d, from
      assume a b c d : ℝ,
      assume h1 : a ≤ b,
      assume h2 : a - c ≤ d,
      show b - c ≤ d, from by {apply le_trans h2,rw ← add_sub_cancel a b at h1, rw add_sub_cancel at h2, exact h2,},
    have h4 : ∀ a b c d e : ℝ, a ≤ b → a - c ≤ d → b - c ≤ d + e → a - c ≤ d + e, from
      assume a b c d e : ℝ,
      assume h1 : a ≤ b,
      assume h2 : a - c ≤ d,
      assume h3 : b - c ≤ d + e,
      show a - c ≤ d + e, from by {apply le_trans h2, rw ← add_sub_cancel a b at h1, rw add_sub_cancel at h2, exact h2,},
    have h5 : ∀ a b : ℝ, a ≥ b → a - b = a - b, from
      assume a b : ℝ,
      assume h : a ≥ b,
      show a - b = a - b, from eq.refl (a - b),
    have h6 : ∀ a b c d : ℝ, a ≥ b :=
      assume a b c d : ℝ,
      assume h : a ≥ b,
      show a ≥ b, from h,
    have h7 : ∀ a b c d : ℝ, a ≥ b → a - c ≥ b - c, from
      assume a b c d : ℝ,
      assume h : a ≥ b,
      show a - c ≥ b - c, from by {rw ← add_sub_cancel a b at h, rw add_sub_cancel at h, exact h,},
    have h8 : ∀ a b c : ℝ, c > 0 → (b - a) / c ≥ 0, from
      assume a b c : ℝ,
      assume h : c > 0,
      show (b - a) / c ≥ 0, from by {rw ← sub_eq_add_neg a b, rw ← add_comm (-a) b, rw ← add_sub_cancel (-a) 0 at h, rw add_sub_cancel at h,ring, exact h,},
    have h9 : ∀ a b c d : ℝ, a ≥ d → a - b ≥ c → a - b ≥ 0 → (a - d) / b ≥ (c / b : ℝ), from
      assume a b c d : ℝ,
      assume h1 : a ≥ d,
      assume h2 : a - b ≥ c,
      assume h3 : a - b ≥ 0,
      show (a - d) / b ≥ (c / b : ℝ), from by {rw ← add_sub_cancel a d at h1, rw ← add_sub_cancel c b at h2, rw ← add_sub_cancel at h2,simp, rw ← add_sub_cancel, from mul_le_mul_of_nonneg_left h3 (le_of_lt ht),ring, ring, exact h2, exact h1,},
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by {
      rw ← le_sub_iff_add_le,
      apply h9,
      {rw ← sub_eq_add_neg, ring, exact h1,},
      rw ← sub_eq_add_neg, rw ← sub_eq_add_neg, rw ← sub_eq_add_neg, rw ← sub_eq_add_neg, rw add_comm, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, r
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem begin
  -- The expression 
  have h0 : (x - y) * ((x^t) * (x - z) - (y^t) * (y - z)) + z^t * (x - z) * (y - z) ≥ 0,
  { calc ((x - y) * (x^t - y^t)) * (x - z) + z^t * ((x - y) * (x - z)) : by ring
    ... = (x^t - y^t) * ((x - y) * (x - z) + z^t * (x - z)) : by ring
    ... = (x^t - y^t) * (x - y - z^t) * (x - z) : by ring
    ... = (x^t - y^t) * (x - y - z^t + x) * (x - z) : by ring
    ... = (x^t - y^t) * (x^t - y^t) * (x - z) : by ring
    ... ≥ 0 : by apply Schur_inequality 
  },
  have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) = (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) - z^t * (x - z) * (y - z), by {repeat {rw ← mul_assoc}, ring},
  have h2 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, by {have h3 := h1, rw h0 at h3, exact h3},
  have h4 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ - z^t * (x - z) * (y - z), by {exact add_le_add_right h2 (z^t * (x - z) * (y - z))},
  have h5 : (x - y) * (x^t * (x - y) - y^t * (y - y)) ≥ - z^t * (x - y) * (y - y), by {
    have h6 := mul_sub_right_distrib h4,
    have h7 : z^t * (x - z) * (y - z) = z^t * (x - y) * (y - z), from by ring,
    rw h7 at h6,
    have h8 : z^t * (x - y) * (y - z) = z^t * (x - y) * (y - y), by ring,
    rw h8 at h6, exact h6,
  },
  have h9 : (x^t) * (x - y) * (x - y) - (y^t) * (y - y) * (x - y) ≥ - z^t * (x - y) * (y - y), from by rw ← mul_assoc at h5,
  have h10 : (x^t) * (x - y) * (x - y) - (y^t) * (y - y) * (x - y)  + z^t * (y - y) * (z - y) ≥ - z^t * (x - y) * (y - y) + z^t * (y - y) * (z - y), by {exact add_le_add_right h9 (z^t * (y - y) * (z - y))},
  have h11 :  (x^t) * (x - y) * (x - y) + z^t * (z - y) * (y - y)  - (y^t) * (y - y) * (x - y)  ≥ - z^t * (x - y) * (y - y) + z^t * (y - y) * (z - y), by {
    have h12 := h10,
    have h13 := sub_mul_right_distrib h12,
    ring at h13, exact h13,
  },
  have h14 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ z^t * (x - z) * (y - z), from by {rw h0 at h14, exact h14},
  have h15 : (x - y) * (x^t * (x - y) - y^t * (y - y)) ≥ z^t * (x - y) * (y - y), from by {
    have h16 := mul_sub_right_distrib h14,
    have h17 : (x - z) * (y - z) = (x - y) * (y - y), by ring,
    rw h17 at h16, exact h16,
  },
  have h18 : (x^t) * (x - y) * (x - y) - (y^t) * (y - y) * (x - y) ≥ z^t * (x - y) * (y - y), from by {rw ← mul_assoc at h15, exact h15},
  have h19 : (x^t) * (x - y) * (x - y) + z^t * (z - y) * (y - y) - (y^t) * (y - y) * (x - y) ≥ z^t * (x - y) * (y - y) + z^t * (y - y) * (z - y), from by {
    have h20 := add_le_add_right h18 (z^t * (x - y) * (y - y)),
    have h21 := sub_mul_right_distrib h20,
    ring at h21, exact h21,
  },
  rw ← mul_assoc at h11, rw add_assoc at h11, rw ← mul_assoc at h11, rw ← mul_assoc at h19, rw add_assoc at h19, rw ← mul_assoc at h19, ring at h11, ring at h19, 
  have h20 : (x^t) * (x - y) * (x - y) + z^t * (z - y) * (y - y) - (y^t) * (y - y) * (x - y) + z^t * (y - y) * (z - y) = (x^t) * (x - y) * (x - y) + z^t * (z - y) * (y - y) - (y^t) * (y - y) * (x - y) + z^t * (y - y) * (z - y) + y^t * (y - y) * (y - x) - y^t * (y - y) * (y - x), by ring,
  have h21 : (x^t) * (x - y) * (x - y) + z^t * (z - y) * (y - y) - (y^t) * (y - y) * (x - y) ≥ z^t * (x - y) * (y - y) + z^t * (y - y) * (z - y), from by exact h19,
  have h22 : (x^t) * (x - y) * (x - y) + z^t * (z - y) * (y - y) - (y^t) * (y - y) * (x - y) + y^t * (y - y) * (y - x) ≥ z^t * (x - y) * (y - y) + z^t * (y - y) * (z - y) + y^t * (y - y) * (y - x) - y^t * (y - y) * (y - x), from by {exact add_le_add_right h21 (y^t * (y - y) * (y - x))},
  ring at h22, rw ← mul_assoc at h22, rw ← mul_assoc at h22, rw ← mul_assoc at h22, rw ← mul_assoc
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem begin
    have h1 : ∀ A B C D E F G H, A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*C*D + A*B*E*F ≥ 0, from begin
      assume A B C D E F G H,
      have h2 : A*B*C*D + E*F*G*H ≥ 0, from by { rw [mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc], ring},
      have h3 : A*B*E*F ≥ 0, from by { rw [mul_assoc,mul_assoc,mul_assoc,mul_assoc], ring},
      show A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*C*D + A*B*E*F ≥ 0, from by { split, apply h2.trans h3, rw [add_comm,add_comm (A*B*C*D),add_comm (A*B*C*D)], apply h3.trans h2,},
      end,
    have h2 : ∀ A B C D E F G H, A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*E*G ≥ 0, from begin
      assume A B C D E F G H,
      have h3 : A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*C*E*F*G*H ≥ 0, from h1 A B C D E F G H,
      show A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*E*G ≥ 0, from begin 
        rw [mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_comm B C,mul_comm C D,mul_comm D E,mul_comm E F,mul_comm F G,mul_comm G H,mul_comm H A,
            mul_comm A D,mul_comm A H,mul_comm B E,mul_comm B G,
            mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_comm E A,mul_comm A B,mul_comm E B,mul_comm F A,mul_comm A C,mul_comm F C,
            mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_comm G E,mul_comm G C,mul_comm E C,mul_comm H E,mul_comm H D,mul_comm E D,
            mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_comm G A,mul_comm G C,mul_comm A C,mul_comm A B,mul_comm B C],
        exact h3,
        end,
    end,
    have h3 : ∀ A B C D E F G H, A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*F*G ≥ 0, from begin
      assume A B C D E F G H,
      have h4 : A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*E*G ≥ 0, from h2 A B C D E F G H,
      show A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*F*G ≥ 0, from begin
        rw [mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_comm A B,mul_comm B E,mul_comm E G,mul_comm G A,
            mul_comm F B,mul_comm B G,mul_comm F G,mul_comm A C,mul_comm A D,
            mul_comm C D,mul_comm F D,mul_comm D G,mul_comm F G, 
            mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_comm F E,mul_comm E D,mul_comm F D],
        exact h4,
        end,
    end,
    have h4 : ∀ A B C D E F G H, A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*C*F ≥ 0, from begin
      assume A B C D E F G H,
      have h5 : A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*F*G ≥ 0, from h3 A B C D E F G H,
      show A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*C*F ≥ 0, from begin
        rw [mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_comm A B,mul_comm B F,mul_comm F G,mul_comm G A,
            mul_comm A C,mul_comm A D,
            mul_comm C D,mul_comm B C,mul_comm B D,
            mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_comm B F,mul_comm B G,mul_comm F G],
        exact h5,
        end,
    end,
    have h5 : ∀ A B C D E F G H, A*B*C*D + E*F*G*H ≥ 0 ↔ A*C*D*F ≥ 0, from begin
      assume A B C D E F G H,
      have h6 : A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*C*F ≥ 0, from h4 A B C D E F G H,
      show A*B*C*D + E*F*G*H ≥ 0 ↔ A*C*D*F ≥ 0, from begin
        rw [mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_comm A C,mul_comm C D,mul_comm D F,mul_comm F A,
            mul_comm A B,mul_comm B F,
            mul_comm C B,mul_comm C F,mul_comm B F,
            mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_assoc,
            mul_comm C B,mul_comm C D,mul_comm B D],
        exact h6,
        end,
    end,
    have h6 : ∀ A B C D E F G H, A*B*C*D + E*F*G*H ≥ 0 ↔ A*B*D*F ≥ 0, from begin
      assume A B C D E F G H,
      have h7 : A*B*C*D + E*F*G*H ≥ 0 ↔ A*C*D*F ≥ 0, from h5 A B C D E
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem begin
    -- $x, y, z$ are positive real numbers such that $x \ge y \ge z \ge 0$
    assume (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0),
    -- Consider the expression:
    have h2 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from begin
      -- $x - y \ge 0$
      have hxy : (x - y) ≥ 0, from by {apply sub_nonneg.mpr, exact hxy},
      -- $x^t \paren {x - z} - y^t \paren {y - z} \ge 0$
      have h3 : (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {
        have h4 : (x^t * (x - z) - y^t * (y - z)) = ((x^t - y^t) * (x - z) - 0), from by ring,
        rw h4,
        apply sub_nonneg.mpr,
        -- $x^t - y^t = \paren {x^{t - 1} - y^{t - 1}} \paren {x - y} \ge 0$
        have h5 : x^t - y^t = (x^t - y^t) * (x - y), from by ring,
        have h6 : x^t - y^t = x^t * (x - y) - y^t * (x - y), from by ring,
        have hxy : (x - y) ≥ 0, from by {apply sub_nonneg.mpr, exact hxy},
        have h7 : x^t * (x - y) ≥ 0, from by {rw ← h5, apply mul_nonneg.mpr, apply pow_nonneg, exact hxy,},
        have h8 : y^t * (x - y) ≥ 0, from by {rw h6, apply sub_nonneg.mpr, apply mul_nonneg, exact pow_nonneg ht, exact hxy,},
        apply sub_nonneg.mpr,
        exact ⟨h7,h8⟩,
        -- $z^t \paren {x - z} \ge 0$
        have h9 : (z^t * (x - z)) ≥ 0, from by {apply mul_nonneg.mpr, apply pow_nonneg, apply sub_nonneg, exact hxy,},
        exact ⟨h9,hz⟩,
      },
      show (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {
        -- $x - z \ge 0$
        have hxz : (x - z) ≥ 0, from by {apply sub_nonneg.mpr, exact hxy.trans hyz},
        -- $y - z \ge 0$
        have hyz : (y - z) ≥ 0, from by {apply sub_nonneg.mpr, exact hyz},
        have h4 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) = 
          (x - y) * (x - z) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z), from by ring,
        rw h4,
        -- $(x - y) * (x - z) \ge 0$
        have h5 : (x - y) * (x - z) ≥ 0, from by {apply mul_nonneg.mpr, exact ⟨hxy,hxz⟩},
        have h6 : (x - z) ≥ 0, from by {apply sub_nonneg.mpr, exact hxy},
        have h7 : (y - z) ≥ 0, from by {apply sub_nonneg.mpr, exact hyz},
        apply add_nonneg.mpr,
        exact ⟨(mul_nonneg h5 h3),(mul_nonneg h6 h7)⟩,
      },
    }, 
    -- $t \in \R, t > 0$ be a (strictly) positive real number.
    have ht : t > 0, from ht,
    -- $(x - y) \paren {x^t \paren {x - z} - y^t \paren {y - z}} + z^t \paren {x - z} \paren {y - z} \ge 0$
    show (x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y)) ≥ 0, from by {
      -- $x^t \paren {x - y} \paren {x - z} \ge 0$
      have hx : x^t * (x - y) * (x - z) ≥ 0, from by {apply mul_nonneg.mpr, apply ⟨pow_nonneg ht,⟨hxy,hxz⟩⟩},
      -- $y^t \paren {y - z} \paren {y - x} \ge 0$
      have hy : y^t * (y - z) * (y - x) ≥ 0, from by {apply mul_nonneg.mpr, apply ⟨pow_nonneg ht,⟨hyz,hxy⟩⟩},
      -- $z^t \paren {z - x} \paren {z - y} \ge 0$
      have hz : z^t * (z - x) * (z - y) ≥ 0, from by {apply mul_nonneg.mpr, apply ⟨pow_nonneg ht,⟨hz,hxy.trans hyz⟩⟩},
      show (x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y)) ≥ 0, from by {
        have h4 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) = 
          (x^t * (x - z) - y^t * (y - z)) * (x - y) + z^t * (x - z) * (y - z), from by ring,
        rw h4,
        apply add_nonneg.mpr,
        exact ⟨(mul_nonneg hxy h3),(mul_nonneg hz hyz)⟩,
      },
    },
  end

/--`theorem`
Schur's Inequality
Let $x, y, z \in \R_{\ge 0}$ be positive real numbers such that $x \ge y \ge z \ge 0$.

Then:
:$x^3 \paren {x - y} \paren {x - z} + y^3 \paren {y - z} \paren {y - x} + z^3 \paren {z - x} \paren {z - y} \ge 0$

`proof`

Setting $t=3$ in the above proof.
{{qed}}
-/
theorem schur_inequality_short (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) :
  x^3 * (x - y) * (x - z) + y^3 * (y - z) * (y - x) + z^3 * (z - x) * (z - y) ≥ 0 :=
  begin
    -- As a special case of the above lemma
    exact schur_inequality x y z hxy hyz hz (by norm_num),
  end

/--`theorem`
Sum of Associated Bases is Associated
end --Needs more than 2000 tokens!

--OUTPUT 10
theorem  begin
    -- consider the expression
    have h1 : (x-y)*(x^t*(x-z) - y^t*(y-z)) + z^t*(x-z)*(y-z) ≥ 0,
    have h2 : x^t*(x-y)*(x-z) ≥ y^t*(x-y)*(y-z), from by {apply mul_self_le_mul_self_iff, apply mul_nonneg (sub_nonneg.2 hxy), exact ht},
    have h3 : y^t*(x-y)*(y-z) ≥ z^t*(x-z)*(y-z), from by {apply mul_self_le_mul_self_iff, apply mul_nonneg (sub_nonneg.2 hyz), exact ht},
    have h4 : x-y ≥ 0, from by {apply sub_nonneg.2 hxy},
    have h5 : x-z ≥ 0, from by {apply sub_nonneg.2 (ge_of_ge_of_ge hxy hyz)},
    have h6 : y-z ≥ 0, from by {apply sub_nonneg.2 hyz},
    -- So, directly:
    have h7 : (x-y)*(x^t*(x-z) - y^t*(y-z)) ≥ 0, from by {apply mul_nonneg, exact h4, exact sub_nonneg.2 (h2)},
    have h8 : z^t*(x-z)*(y-z) ≥ 0, from by {apply mul_nonneg, exact ht, apply mul_nonneg, exact h5, exact h6},
    show (x-y)*(x^t*(x-z) - y^t*(y-z)) + z^t*(x-z)*(y-z) ≥ 0, from add_nonneg h7 h8,
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by {rw schur_inequality, exact h1},
  end

/--`theorem`
Sum of Two Non-Negative Real Numbers less than Sum of their Square Roots
Let $x, y \in \R_{\ge 0}$ be real numbers greater than or equal to zero.


Then:
:$x + y \le \sqrt {x^2 + y^2}$

`proof`
Follows from Squares of Real Numbers, which says that:
:$(x + y)^2 \ge x^2 + y^2$

and Square Roots are Non-Negative, which says that:
:$\sqrt {x^2 + y^2} \ge 0$

Note that $(x + y)^2 \ge x^2 + y^2$ is merely a rearrangement of Schur's inequality.
{{qed}}
-/
theorem  sum_non_neg_reals_le_sum_square_roots (x y : ℝ) (hx0 : x ≥ 0) (hy0 : y ≥ 0) : x + y ≤ sqrt (x^2 + y^2) :=
  begin
    have h1 : (x+y)^2 ≥ x^2 + y^2, from by {apply squares_of_reals, exact hx0, exact hy0},
    have h2 : sqrt (x^2 + y^2) ≥ 0, from by {apply square_roots_non_neg, exact hx0, exact hy0},
    apply sum_of_squares_le_square_of_sum, exact h1, exact h2,
  end

/--`theorem`
Square Roots are Monotonic
Let $x, y \in \R_{\ge 0}$ be real numbers such that $x \le y$.


Then:
:$\sqrt x \le \sqrt y$

`proof`

We prove this by contradiction.

{{begin-eqn}}
{{eqn | l = \paren {\sqrt x > \sqrt y}
      | r = \sqrt x \ge \sqrt y
}}
{{eqn | r = x > y
      | c = Square Roots are Non-Negative
}}
{{eqn | r = x \le y
      | rw = opposite-hypothesis
}}
{{qed}}
-/
theorem  square_roots_monotonic (x y : ℝ) (hxy : x ≤ y) : sqrt x ≤ sqrt y :=
  begin
    have h1 : sqrt x ≥ sqrt y, from by {apply square_roots_non_neg, exact hxy},
    have h2 : x ≥ y, from by {rw ← sq hxy},
    have h3 : ¬(x > y), from by {rw ← lt_iff_le_not_le hxy, exact h2},
    have h4 : sqrt x > sqrt y, from by {rw lt_iff_le_not_le h1, exact h3},
    contradiction,
  end

/--`theorem`
Product of Two Non-Negative Real Numbers greater than Product of their Square Roots
Let $x, y \in \R_{\ge 0}$ be real numbers greater than or equal to zero.


Then:
:$x y \ge \sqrt {x^2 + y^2}$

`proof`
Compare this with the Sum of Two Non-Negative Real Numbers less than Sum of their Square Roots.

We see that the proof for this theorem is an extension of the proof for that theorem. This is by exploiting the properties of the Cauchy-Schwartz inequality.
{{qed}}
-/
theorem  product_non_neg_reals_ge_product_square_roots (x y : ℝ) (hx0 : x ≥ 0) (hy0 : y ≥ 0) : x * y ≥ sqrt (x^2 + y^2) :=
  begin
    have h1 : (x + y)^2 ≥ x^2 + y^2, from by {apply squares_of_reals, exact hx0, exact hy0},
    have h2 : x^2 + y^2 ≥ 0, from by {apply sum_of_squares_non_neg, exact hx0, exact hy0},
    have h3 : (x + y)^2 ≥ 2*(x*y), from by {apply cauchy_schwartz_inequality h1 h2},
    have h4 : x^2 + y^2 ≥ 2*(x*y), from by {rw sq h3},
    have h5 : x + y ≥ 0, from by {apply add_nonneg, exact hx0, exact hy0},
    have h6 : (x + y)^2 ≥ (x + y)^2, from by {apply pow_le_pow h5 dec_trivial},
    have h7 : (x + y)^2 ≥ x^2 + y^2, from by {rw ← h4, exact h6},
    have h8 : (x + y) ≥ sqrt (x^2 + y^2), from by {apply sum_of_squares_le_square_of_sum, exact h7, exact h2},
    have h9 : x + y ≥ 0, from by {apply add_nonneg, exact hx0, exact hy0},
    have h10 : (x + y) ≥ x + y, from by {apply le_refl (x+y)},
    have h11 : (x + y) ≥ sqrt (x^2 + y^2), from by {rw ← h8, exact h10},
    have h12 : (x + y)^2 ≥ (x + y)^2, from by {apply pow_le_pow h9 dec_trivial},
    have h13 : (x + y)^2 ≥ x^2 + y^2, from by {rw ← h4, exact h12},
    have h14 : (x + y) ≥ sqrt (x^2 + y^2), from by {apply sum_of_squares_le_square_of_sum, exact h13, exact h2},
    have h15 : 1 * (x + y) ≥ sqrt (x^2 + y^2),
end --Needs more than 2000 tokens!

