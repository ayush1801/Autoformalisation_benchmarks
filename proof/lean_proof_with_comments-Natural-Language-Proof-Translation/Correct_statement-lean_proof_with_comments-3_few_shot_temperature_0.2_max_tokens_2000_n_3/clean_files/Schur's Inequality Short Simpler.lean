
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
    -- Consider the expression:
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from
    begin
      -- We see that every term in the above is non-negative. So, directly:
      have h2 : (x - y) ≥ 0, from by {apply sub_nonneg.mpr, exact hxy},
      have h3 : (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {apply sub_nonneg.mpr,
        apply mul_nonneg.mpr, exact ht, exact hz, exact ht, exact hz,
        apply sub_nonneg.mpr, exact hxy, exact hyz,
        apply sub_nonneg.mpr, exact hxy, exact hyz,
      },
      have h4 : (x - z) ≥ 0, from by {apply sub_nonneg.mpr, exact hxy, exact hz},
      have h5 : (y - z) ≥ 0, from by {apply sub_nonneg.mpr, exact hyz, exact hz},
      have h6 : z^t ≥ 0, from by {apply pow_nonneg.mpr, exact hz, exact ht},
      have h7 : (x - z) * (y - z) ≥ 0, from by {apply mul_nonneg.mpr, exact h4, exact h5},
      have h8 : z^t * (x - z) * (y - z) ≥ 0, from by {apply mul_nonneg.mpr, exact h6, exact h7},
      show (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {
        apply add_nonneg.mpr, exact h2, exact h3, exact h8,
      },
    end,
    -- $(1) can be rearranged to Schur's inequality.
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by {
      rw [← mul_assoc x^t (x - y) (x - z), ← mul_assoc y^t (y - z) (y - x), ← mul_assoc z^t (z - x) (z - y), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t * (x - z) - y^t * (y - z)) (z^t * (x - z) * (y - z)), ← mul_assoc (x - y) (x^t
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem begin
    -- Consider the expression:
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {
      -- We see that every term in the above is non-negative. So, directly:
      have h2 : (x - y) ≥ 0, from by {apply sub_nonneg.mpr,exact hxy},
      have h3 : (x - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hxy},
      have h4 : (y - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hyz},
      have h5 : (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {
        have h6 : x^t ≥ 0, from by {apply pow_nonneg,exact hz},
        have h7 : y^t ≥ 0, from by {apply pow_nonneg,exact hz},
        have h8 : x^t * (x - z) ≥ 0, from by {apply mul_nonneg h6 h3},
        have h9 : y^t * (y - z) ≥ 0, from by {apply mul_nonneg h7 h4},
        have h10 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by {apply sub_nonneg.mpr,exact h8},
        exact h10,
      },
      have h11 : z^t * (x - z) * (y - z) ≥ 0, from by {
        have h12 : z^t ≥ 0, from by {apply pow_nonneg,exact hz},
        have h13 : z^t * (x - z) ≥ 0, from by {apply mul_nonneg h12 h3},
        have h14 : z^t * (x - z) * (y - z) ≥ 0, from by {apply mul_nonneg h13 h4},
        exact h14,
      },
      have h15 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {apply mul_nonneg h2 h5},
      have h16 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {apply add_nonneg h15 h11},
      exact h16,
    },
    -- $(1) can be rearranged to Schur's inequality.
    have h17 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by {
      have h18 : x^t * (x - y) * (x - z) ≥ 0, from by {apply mul_nonneg,exact h2,exact h3},
      have h19 : y^t * (y - z) * (y - x) ≥ 0, from by {apply mul_nonneg,exact h4,exact h2},
      have h20 : z^t * (z - x) * (z - y) ≥ 0, from by {apply mul_nonneg,exact h4,exact h3},
      have h21 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) ≥ 0, from by {apply add_nonneg h18 h19},
      have h22 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by {apply add_nonneg h21 h20},
      exact h22,
    },
    exact h17,
  end

/--`theorem`
Schur's Inequality
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
theorem  schur_inequality_long (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 :=
  begin
    -- Consider the expression:
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {
      -- We see that every term in the above is non-negative. So, directly:
      have h2 : (x - y) ≥ 0, from by {apply sub_nonneg.mpr,exact hxy},
      have h3 : (x - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hxy},
      have h4 : (y - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hyz},
      have h5 : (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {
        have h6 : x^t ≥ 0, from by {apply pow_nonneg,exact hz},
        have h7 : y^t ≥ 0, from by {apply pow_nonneg,exact hz},
        have h8 : x^t * (x - z) ≥ 0, from by {apply mul_nonneg h6 h3},
        have h9 : y^t * (y - z) ≥ 0, from by {apply mul_nonneg h7 h4},
        have h10 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by {apply sub_nonneg.mpr,exact h8},
        exact h10,
      },
      have h11 : z^t * (x - z) * (y - z) ≥ 0, from by {
        have h12 : z^t ≥ 0, from by {apply pow_nonneg,exact hz},
        have h13 : z^t * (x - z) ≥ 0, from by {apply mul_nonneg h12 h3},
        have h14 : z^t * (x - z) * (y - z) ≥ 0, from by {apply mul_nonneg h13 h4},
        exact h14,
      },
      have h15 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {apply mul_nonneg h2 h5},
      have h16 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {apply add_nonneg h15 h11},
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem begin
    -- Consider the expression:
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0,
    {
      -- We see that every term in the above is non-negative. So, directly:
      have h2 : (x - y) ≥ 0, from by {apply sub_nonneg.mpr,exact hxy},
      have h3 : (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {
        have h4 : (x - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hxy},
        have h5 : (y - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hyz},
        have h6 : (x^t * (x - z) - y^t * (y - z)) = (x^t - y^t) * (x - z), from by {
          rw [← mul_sub h4 h5,mul_assoc,mul_comm (x^t) (x - z),mul_assoc,mul_comm (x^t) (y - z),mul_assoc,mul_comm (y^t) (x - z),mul_assoc],
          ring,
        },
        have h7 : (x^t - y^t) ≥ 0, from by {apply sub_nonneg.mpr,exact ht},
        show (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {apply mul_nonneg h7 h4,},
      },
      have h8 : (x - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hxy},
      have h9 : (y - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hyz},
      have h10 : z^t * (x - z) * (y - z) ≥ 0, from by {
        apply mul_nonneg h8,
        apply mul_nonneg h9,
        apply pow_nonneg hz ht,
      },
      show (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {
        apply add_nonneg h2,
        apply mul_nonneg h3,
        apply h10,
      },
    },
    -- $(1) can be rearranged to Schur's inequality.
    have h11 : (x - y) * (x^t * (x - z) - y^t * (y - z)) = x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z), from by {
      rw [← mul_sub hxy hz,mul_assoc,mul_comm (x^t) (x - y),mul_assoc,mul_comm (x^t) (x - z),mul_assoc,mul_comm (y^t) (x - y),mul_assoc],
      ring,
    },
    have h12 : z^t * (x - z) * (y - z) = z^t * (z - x) * (z - y), from by {
      rw [← mul_sub hz hxy,mul_assoc,mul_comm (z^t) (z - x),mul_assoc,mul_comm (z^t) (z - y),mul_assoc],
      ring,
    },
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by {
      rw [h11,h12],
      ring,
    },
  end

/--`theorem`
Schur's Inequality
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
theorem  schur_inequality_long (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 :=
  begin
    -- Consider the expression:
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0,
    {
      -- We see that every term in the above is non-negative. So, directly:
      have h2 : (x - y) ≥ 0, from by {apply sub_nonneg.mpr,exact hxy},
      have h3 : (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {
        have h4 : (x - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hxy},
        have h5 : (y - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hyz},
        have h6 : (x^t * (x - z) - y^t * (y - z)) = (x^t - y^t) * (x - z), from by {
          rw [← mul_sub h4 h5,mul_assoc,mul_comm (x^t) (x - z),mul_assoc,mul_comm (x^t) (y - z),mul_assoc,mul_comm (y^t) (x - z),mul_assoc],
          ring,
        },
        have h7 : (x^t - y^t) ≥ 0, from by {apply sub_nonneg.mpr,exact ht},
        show (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {apply mul_nonneg h7 h4,},
      },
      have h8 : (x - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hxy},
      have h9 : (y - z) ≥ 0, from by {apply sub_nonneg.mpr,exact hyz},
      have h10 : z^t * (x - z) * (y - z) ≥ 0, from by {
        apply mul_nonneg h8,
        apply mul_nonneg h9,
        apply pow_nonneg hz ht,
      },
      show (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {
        apply add_nonneg h2,
        apply
end --Needs more than 2000 tokens!

