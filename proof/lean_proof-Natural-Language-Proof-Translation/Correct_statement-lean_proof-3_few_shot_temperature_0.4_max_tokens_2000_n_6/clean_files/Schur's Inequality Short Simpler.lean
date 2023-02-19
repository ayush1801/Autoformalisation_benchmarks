
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
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by {split,apply set.subset_of_mem_powerset,exact hA,apply set.subset_of_mem_powerset,exact hB},
  have h2 : (A ∩ B) ⊆ A, from by apply set.inter_subset_left,
  have h3 : (A ∩ B) ⊆ S, from by {apply set.subset.trans h2 h1.left},
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
  calc (x + y)^2 = (x+y)*(x+y) : by rw sq
  ... = x*(x+y) + y*(x+y) : by rw add_mul
  ... = x*x + x*y + y*x + y*y : by {rw [mul_comm x (x+y),mul_comm y (x+y)], rw [add_mul,add_mul], ring}
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
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by {
    assume a b : G, use a⁻¹ * b, obviously, },
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by {
    assume a b : G, use b * a⁻¹, obviously, }, 

  have h3 : ∀ a : G, ∃! x : G, a * x = a, from 
    assume a : G, h1 a a,
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from
    assume a : G, h2 a a,

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
    have h1 : x^t * (x - z) ≥ y^t * (y - z), from by {
      have h2 : x^t ≥ y^t, from by {
        have h3 : x ≥ y, from by {apply le_trans hxy, apply hyz},
        show x^t ≥ y^t, from by {apply pow_le_pow_of_le_left h3 ht},
      },
      have h4 : x - z ≥ y - z, from by {apply le_trans hxy, apply hyz},
      show x^t * (x - z) ≥ y^t * (y - z), from by {apply mul_le_mul_of_nonneg_left h2 h4},
    },
    have h5 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by {
      have h6 : x^t * (x - z) - y^t * (y - z) = x^t * (x - z) - y^t * (x - z) + y^t * (x - z) - y^t * (y - z), from by ring,
      have h7 : x^t * (x - z) - y^t * (x - z) ≥ 0, from by {
        have h8 : x^t * (x - z) - y^t * (x - z) = (x^t - y^t) * (x - z), from by ring,
        have h9 : x^t - y^t ≥ 0, from by {apply sub_nonneg.mpr h1},
        show x^t * (x - z) - y^t * (x - z) ≥ 0, from by {apply mul_nonneg h9 hz},
      },
      have h10 : y^t * (x - z) - y^t * (y - z) ≥ 0, from by {
        have h11 : y^t * (x - z) - y^t * (y - z) = y^t * (x - y), from by ring,
        have h12 : y^t * (x - y) ≥ 0, from by {apply mul_nonneg_of_nonneg_of_nonneg ht hxy},
        show y^t * (x - z) - y^t * (y - z) ≥ 0, from by {apply h12},
      },
      show x^t * (x - z) - y^t * (y - z) ≥ 0, from by {apply add_nonneg h7 h10},
    },
    have h11 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {
      have h12 : (x - y) * (x^t * (x - z) - y^t * (y - z)) = x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z), from by ring,
      have h13 : x^t * (x - y) * (x - z) ≥ 0, from by {apply mul_nonneg_of_nonneg_of_nonneg_of_nonneg ht hxy hz},
      have h14 : y^t * (x - y) * (y - z) ≥ 0, from by {apply mul_nonneg_of_nonneg_of_nonneg_of_nonneg ht hxy hz},
      show (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {apply sub_nonneg h13 h14},
    },
    have h15 : z^t * (x - z) * (y - z) ≥ 0, from by {
      have h16 : z^t * (x - z) * (y - z) = z^t * (x - y) * (y - z), from by ring,
      show z^t * (x - z) * (y - z) ≥ 0, from by {apply mul_nonneg_of_nonneg_of_nonneg_of_nonneg ht hxy hz},
    },
    have h17 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {
      have h18 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) = x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z) + z^t * (x - y) * (y - z), from by ring,
      show (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {apply add_nonneg h13 h14},
    },
    have h19 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by {
      have h20 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) = x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z) + y^t * (x - y) * (y - z) + z^t * (x - y) * (y - z), from by ring,
      show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by {apply add_nonneg h17 h15},
    },
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by {apply h19},
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
theorem  schur_inequality (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 :=
  begin
    have h1 : x^t * (x - z) ≥ y^t * (y - z), from by {
      have h2 : x^t ≥ y^t, from by {
        have h3 : x ≥ y, from by {apply le
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem begin
    have h1 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by {
      have h2 : x^t * (x - z) ≥ y^t * (y - z), from by {
        have h3 : x^t * (x - z) - y^t * (y - z) = (x - y) * (x^t * (x - z) - y^t * (y - z)), from by {
          rw [mul_sub,mul_sub,mul_sub,mul_sub,mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc,mul_comm (x^t),mul_comm (y^t),mul_assoc,mul_assoc,mul_comm (x^t),mul_assoc,mul_comm (y^t),mul_assoc
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from
      by {rw schur_inequality_short, ring,},
    have h2 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) =
      x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y), from by ring,
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from
      by {rw h2, exact h1,},
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
theorem schur_inequality_short (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0 :=
  begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from
      by {rw schur_inequality_short, ring,},
    have h2 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) =
      x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y), from by ring,
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from
      by {rw h2, exact h1,},
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
theorem schur_inequality_short_simpler (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0 :=
  begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from
      by {rw schur_inequality_short, ring,},
    have h2 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) =
      x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y), from by ring,
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from
      by {rw h2, exact h1,},
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
theorem schur_inequality_short_simpler_2 (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0 :=
  begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from
      by {rw ← mul_add, rw ← mul_add, apply mul_nonneg, apply sub_nonneg.2, exact hxy,
        apply sub_nonneg.2, exact hxy, apply sub_nonneg.2, exact hxy, apply sub_nonneg.2, exact hyz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz, apply sub_nonneg.2, exact hz,
        apply sub_nonneg.2
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem begin
    have h1 : x^t * (x - z) - y^t * (y - z) ≥ 0, from
      by {rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg,
      ← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg],
      have h2 : x^t * (x - z) - y^t * (y - z) = x^t * (x - z) + (-1) * y^t * (y - z), from by ring,
      rw h2,
      have h3 : x^t * (x - z) + (-1) * y^t * (y - z) = x^t * (x - z) + -1 * y^t * (y - z), from by ring,
      rw h3,
      have h4 : x^t * (x - z) + -1 * y^t * (y - z) = x^t * (x - z) + -1 * y^t * y - -1 * y^t * z, from by ring,
      rw h4,
      have h5 : x^t * (x - z) + -1 * y^t * y - -1 * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h5,
      have h6 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h6,
      have h7 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h7,
      have h8 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h8,
      have h9 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h9,
      have h10 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h10,
      have h11 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h11,
      have h12 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h12,
      have h13 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h13,
      have h14 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h14,
      have h15 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h15,
      have h16 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h16,
      have h17 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h17,
      have h18 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h18,
      have h19 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h19,
      have h20 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h20,
      have h21 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h21,
      have h22 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h22,
      have h23 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h23,
      have h24 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z = x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^t * z, from by ring,
      rw h24,
      have h25 : x^t * (x - z) + -1 * y^t * y + -1 * (-1) * y^
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {
      calc (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z)
      = x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z) + z^t * (x - z) * (y - z) : by ring
      ... = x^t * (x - y) * (x - z) + z^t * (x - z) * (y - z) - y^t * (x - y) * (y - z) : by ring
      ... = x^t * (x - y) * (x - z) + z^t * (x - z) * (y - z) - y^t * (y - z) * (x - y) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (x - z) * (y - z) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (y - z) * (x - z) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (y - z) * (z - x) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (z - x) * (y - z) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (y - z) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) : by ring,
    },
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from h1,
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
theorem  schur_inequality_short (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 :=
  begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {
      calc (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z)
      = x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z) + z^t * (x - z) * (y - z) : by ring
      ... = x^t * (x - y) * (x - z) + z^t * (x - z) * (y - z) - y^t * (x - y) * (y - z) : by ring
      ... = x^t * (x - y) * (x - z) + z^t * (x - z) * (y - z) - y^t * (y - z) * (x - y) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (x - z) * (y - z) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (y - z) * (x - z) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (y - z) * (z - x) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (y - z) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) : by ring,
    },
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from h1,
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
theorem  schur_inequality_short_simpler (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z
end --Needs more than 2000 tokens!

