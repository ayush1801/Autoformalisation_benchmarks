
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
theorem 
FEW SHOT PROMPTS TO CODEX(END)-/
--OUTPUT 1
theorem schur_inequality_short_simpler (t : ℝ) (x y z : ℚ) (ht : 0 < t)
(hxy : x ≥ y) (hyz : y ≥ z) (hz0 : 0 ≤ z):
x^t * (x-y) * (x-z) + y^t * (y-z) * (y-x) + z^t * (z-x) * (z-y) ≥ 0 :=
begin
  have h1 : 0 ≤ (x-y) * (x^t * (x-z) - y^t * (y-z)) + z^t * (x-z) * (y-z),
  begin
    -- We see that every term in the above is non-negative. 
    have h2 : x^t * (x-z) ≥ 0,
    begin
      -- $x^t \ge y^t$ because $t \ge 0$, so:
      have h3 : x^t ≥ y^t, from by {
        apply y_leq_x_pow,
        exact ht,
        exact hxy,
        },
      -- $x - z \ge 0$ because $x \ge z$ and so:
      have h4 : x - z ≥ 0, from by {
        apply lt_imp_sub_pos hz0 hxy,
      },
      -- By the above, $x^t * (x - z) \ge y^t * (x - z) \ge 0$
      show x^t * (x - z) ≥ 0, from by {
        apply mul_nonneg h4,
        apply le_of_lt ht,
        apply le_trans h3,
        apply pow_le_pow ht,
        exact hxy,
      },
    end,

    -- $z^t \ge 0$ because $t \ge 0$, so:
    have h5 : z^t ≥ 0, from by {
      apply le_of_lt ht,
      },
    -- $x - z \ge 0$ because $x \ge z$ and so:
    have h6 : x - z ≥ 0, from by {
      apply lt_imp_sub_pos hz0 hxy,
    },
    -- $y - z \ge 0$ because $y \ge z$ and so:
    have h7 : y - z ≥ 0, from by {
      apply lt_imp_sub_pos hz0 hyz,
    },
    -- By the above, $z^t * (x - z) * (y - z) \ge 0$
    have h8 : z^t * (x - z) * (y - z) ≥ 0, from by {
      apply mul_nonneg h6 h7,
      apply le_of_lt ht,
      apply le_trans h5,
      apply pow_le_pow ht,
      exact hyz,
    },
    -- $(x - y) \ge 0$ because $x \ge y$ and so:
    have h9 : x - y ≥ 0, from by {
      apply lt_imp_sub_pos hxy hyz,
    },
    show 0 ≤ (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z),
    by {
      apply add_nonneg;
        apply mul_nonneg h9;
        apply mul_nonneg h2;
        obviously,
    }
  end,
  -- $(1): \quad (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) \ge 0$, by the above.
  -- $z^t * (x - z) * (y - z) = (z^t * (x - z) + (x - y) * (x^t * (x - z) - y^t * (y - z)) - (x - y) * (x^t * (x - z) - y^t * (y - z))) + (x - y) * (x^t * (x - z) - y^t * (y - z))$.
  have h10 : z^t * (x - z) * (y - z) = (z^t * (x - z) + (x - y) * (x^t * (x - z) - y^t * (y - z)) - (x - y) * (x^t * (x - z) - y^t * (y - z))) + (x - y) * (x^t * (x - z) - y^t * (y - z)), by {
    ring,
  },
  -- $(1) = (z^t * (x - z) + (x - y) * (x^t * (x - z) - y^t * (y - z)) - (x - y) * (x^t * (x - z) - y^t * (y - z))) + (x - y) * (x^t * (x - z) - y^t * (y - z))$.
  have h11 : h1 = (z^t * (x - z) + (x - y) * (x^t * (x - z) - y^t * (y - z)) - (x - y) * (x^t * (x - z) - y^t * (y - z))) + (x - y) * (x^t * (x - z) - y^t * (y - z)), by {
    rw h10,
    ring,
  },
  -- By the above two, $(1) = (x - y) * (x^t * (x - z) - y^t * (y - z)) = x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z))$.
  have h12 : h1 = x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z), by {
    rw h11,
    ring,
  },
  -- Similarly, consider the expression:
  have h13 : 0 ≤ (y - x) * (y^t * (y - z) - x^t * (x - z)) + z^t * (y - z) * (x - z),
  begin
    -- $y^t * (y - z) \ge 0$, by similar steps
    have h14 : y^t * (y - z) ≥ 0, from by {
      apply mul_nonneg,
        apply lt_imp_sub_pos hz0 hyz,
        apply le_of_lt ht,
        apply le_trans,
          apply pow_le_pow ht hxy,
          exact hxy,
    },
    -- $z^t \ge 0$, by similar steps
    have h15 : z^t ≥ 0, from by {
      apply le_of_lt ht,
    },
    -- $y - z \ge 0$, by similar steps
    have h16 : y - z ≥ 0, from by {
      apply lt_imp_sub_pos hz0 hyz,
    },
    -- $x - z \ge 0$, by similar steps
    have h17 : x - z ≥ 0, from by {
      apply lt_imp_sub_pos hz0 hxy,
    },
    have h18 : z^t * (y - z) * (x - z) ≥ 0 := by {
      apply mul_nonneg h16 h17,
      apply le_of_lt ht,
      apply le_trans h15,
      apply pow_le_pow ht,
      exact hyz,
    },
    -- $y - x \ge 0$, by similar steps
    have h19 : y - x ≥ 0, from by {
      apply lt_imp_sub_pos hyz hxy,
    },
    show 0 ≤ (y - x) * (y^t * (y - z) - x^t * (x - z)) + z^t * (y - z) * (x - z),
    by {
      apply add_nonneg;
        apply mul_nonneg h19;
        apply mul_nonneg h14;
        obviously,
   
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem schur_short_simpler (x y z : ℝ) (ht : 0 < t) :
    x^t *(x - y)*(x - z) + y^t *(y - z)*(y - x) + z^t *(z - x)*(z - y) ≥ 0 :=
begin
  have h1 : x ≥ y ∧ y ≥ z ∧ z ≥ 0, from by {apply classical.em (x ≥ y),
    exact λ hx_y, by {apply classical.em (y ≥ z),
      exact λ hy_z, by {apply classical.em (z ≥ 0),
        exact λ hz0, ⟨hx_y, hy_z, hz0⟩,
        exact λ hz0, ⟨hx_y, hy_z, hz0.elim⟩,
      },
      exact λ hy_z, x < y ↔ y < x ↔ (y = x) ↔ ¬ (x ≤ y) ↔ ¬ (y ≥ x),
    },
    exact λ hx_y, by {apply classical.em (y ≥ z),
      exact λ hy_z, by {apply classical.em (z ≥ 0),
        exact λ hz0, ⟨hx_y, hy_z, hz0⟩,
        exact λ hz0, ⟨hx_y, hy_z, hz0.elim⟩,
      },
      exact λ hy_z, y < x ↔ x < y ↔ (x = y) ↔ ¬ (y ≤ x) ↔ ¬ (x ≥ y),
    },
  },
  have h1 : (x ≥ y), from h1.left,
  have h2 : (y ≥ z), from h1.right.left,
  have h3 : (z ≥ 0), from h1.right.right,
  have h4 : x > y ∨ x = y, from or.inl h1,
  have h5 : y > z ∨ y = z, from or.inl h2,
  have h6 : z > 0 ∨ z = 0, from or.inr h3,
  have h7 : ∀ x y z : ℝ, (x ≥ y) → (y > z ∨ y = z) → (x > z ∨ x = z), from
    assume x y z : ℝ, assume hx_y, assume hy_z,
    or.cases_on hy_z
      (λ h : y > z, or.inl (le_of_lt hx_y))
      (λ h : y = z, or.inr (h.symm ▸ hx_y)),
  have h8 : x > z ∨ x = z, from h7 x y z h1 h5,
  have h9 : (x > 0), from by {apply lt_of_le_of_ne h3 (mt (le_of_lt ht) (ne.symm (ne_of_lt ht))),},
  have h10 : x > z ∨ x = z, from h7 x z 0 h9 (or.inr h3),
  have h11 : y > z ∨ y = z, from h7 y z 0 h2 (or.inr h3),
  have h12 : y > x ∨ y = x, from h7 y x 0 h2 (or.inr (le_of_lt h1)),
  have h13 : z > x ∨ z = x, from h7 z x 0 h3 (or.inr (le_of_lt h1)),
  have h14 : z > y ∨ z = y, from h7 z y 0 h3 (or.inr (le_of_lt h2)),
  have h15 : ∀ x y z : ℝ, (x > y) → (y ≥ z) → (x ≥ z), from
    assume x y z : ℝ, assume h : x > y, assume k : y ≥ z,
    le_of_lt (lt_of_le_of_lt k h),
  -- directly:
  show x^t *(x - y)*(x - z) + y^t *(y - z)*(y - x) + z^t *(z - x)*(z - y) ≥ 0, from
    by {rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg], 
      rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg], 
      have h16 : ∀ x y z : ℝ, (x ≥ y) → (y > z ∨ y = z) → (x > z ∨ x = z), from
        assume x y z : ℝ, assume hx_y, assume hy_z,
        or.cases_on hy_z
          (λ h : y > z, or.inl (le_of_lt hx_y))
          (λ h : y = z, or.inr (h.symm ▸ hx_y)),
      have h17 : (x - y) > 0, from by {apply lt_of_le_of_ne h1 (mt (le_of_sub_nonneg_left) (ne.symm (ne_of_sub_nonneg_left))),},
      have h18 : (y - z) > 0, from by {apply lt_of_le_of_ne h2 (mt (le_of_sub_nonneg_left) (ne.symm (ne_of_sub_nonneg_left))),},
      have h19 : (z - x) > 0, from by {apply lt_of_sub_nonneg_right,have h20 : z > x, from or.cases_on h13 (λ h : z > x, h) (λ h : z = x, lt_of_le_of_ne h (mt (le_of_lt h9) (ne.symm (ne_of_lt h9)))),exact h20},
      have h20 : (y - x) > 0, from by {apply lt_of_sub_nonneg_right,have h21 : y > x, from or.cases_on h12 (λ h : y > x, h) (λ h : y = x, lt_of_le_of_ne h (mt (le_of_lt h9) (ne.symm (ne_of_lt h9)))),exact h21},
      have h21 : (z - y) > 0, from by {apply lt_of_sub_nonneg_right,have h22 : z > y, from or.cases_on h14 (λ h : z > y, h) (λ h : z = y, lt_of_le_of_ne h (mt (le_of_lt h2) (ne.symm (ne_of_lt h2)))),exact h22},
      have h22 : (x - z) > 0, from by {apply lt_of_sub_nonneg_right,have h23 : x > z, from or.cases_on h10 (λ h : x > z, h) (λ h : x = z, lt_of_le_of_ne h (mt (le_of_lt h9) (ne.symm (ne_of_lt h9)))),exact h23},
      have h23 : (y - z) > 0, from by {apply lt_of_sub_nonneg_right,have h24 : y > z, from or.cases_on h11 (λ h : y > z, h) (λ h : y = z, lt_of_le_of_ne h (mt (le_of_lt h2) (ne.symm (ne_of_lt h2)))),exact h24},
      have h24 : 0 ≤ (x - y), from nonneg_of_le h1,
      have h25 : 0 ≤ (y - z), from nonneg_of_le h2,
      have h26 : 0 ≤ (z - x), from nonneg_of_le (by {apply le_of_lt, exact h9}),
      have h27 : 0 ≤ (y - x), from nonneg_of
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem schur_short (x y z t : ℝ) : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≥ y ∧ y ≥ z ∧ t > 0 →
(x^t * (x-y) * (x-z) + y^t * (y-z) * (y-x) + z^t * (z-x) * (z-y)) ≥ 0 :=
begin
  assume h : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≥ y ∧ y ≥ z ∧ t > 0,
  have h1 : (x - y) * (x^t * (x-z) - y^t * (y-z)) + z^t * (x-z) * (y-z) ≥ 0, by {
    -- Consider the expression:
    suffices : (x - y) * (x^t * (x-z) - y^t * (y-z)) + z^t * (x-z) * (y-z) ≥ 0,
    {show (x - y) * (x^t * (x-z) - y^t * (y-z)) + z^t * (x-z) * (y-z) ≥ 0, from this},
    show (x - y) * (x^t * (x-z) - y^t * (y-z)) + z^t * (x-z) * (y-z) ≥ 0, from by {
      have h2 : x - y > 0 ∧ x^t * (x - z) - y^t * (y - z) > 0, from by {
        split,
        calc x - y = x - y + 0 : by {rw ← add_zero (x-y)}
        ... > 0 : by {apply add_lt_add_right,apply h.left.right.left,},
        rw [mul_add,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_add,mul_one],
        apply add_lt_add_right,
        calc x^t * x - x^t * z = x^t*(x-z) : by {rw ← mul_sub_left x^t (x) (z)}
        ... > 0 : by {apply mul_pos_of_pos_of_nonneg, apply pow_pos (h.left.right.right.right.left.left),
          apply sub_nonneg_of_le (h.left.right.right.right.left.right), },
      },
      have h3 : x - z > 0 ∧ y - z > 0, from by {
        have h3_1 : x - z > 0, from by {apply sub_pos_of_lt h.left.right.right.right.left.right},
        have h3_2 : y - z > 0, from by {apply sub_pos_of_lt h.left.right.right.right.right},
        split, exact h3_1, exact h3_2,
      },
      show (x - y) * (x^t * (x-z) - y^t * (y-z)) + z^t * (x-z) * (y-z) ≥ 0, from by {
        rw [mul_add,mul_assoc,mul_assoc,mul_assoc,mul_assoc],
        apply add_nonneg,
        split,
        have h4 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {
          apply mul_nonneg_of_nonneg_of_nonneg,
          apply h2.left,
          show x^t * (x - z) - y^t * (y - z) ≥ 0, from by {
            apply sub_nonneg_of_le,
            calc x^t * (x - z) - y^t * (y - z)
            = x^t * (x - z) - x^t * (y - z) : by {rw ← mul_sub_left x^t _ _}
            ... ≤ x^t * (x - y) : by {apply sub_le_sub_right},
            calc x^t * (x - y) ≤ x^t * (x - y) * t : by {apply mul_le_mul' (pow_pos (h.left.right.right.right.left.left) t)
              (le_of_lt h.right)
              (h.left.right.right.right.left.right)
              (h.left.right.right.right.right)
              (mul_nonneg (pow_nonneg (h.left.right.right.right.left.left) t) (h.left.right.right.right.left.left)) 
              (mul_nonneg (pow_nonneg (h.left.right.right.right.left.left) t) (h.left.right.right.right.right))
              (mul_nonneg (pow_nonneg (h.left.right.right.right.left.left) t) (h.left.right.right.right.left.left))
              (mul_nonneg (pow_nonneg (h.left.right.right.right.left.left) t) (h.left.right.right.right.right))},
            calc x^t * (x - y) * t ≤ (x^t)^t : by {rw ← pow_mul, apply pow_le_pow (pow_pos (h.left.right.right.right.left.left) t)
              (le_of_lt h.right) (h.left.right.right.right.left.right)},
            calc (x^t)^t ≤ x^t : by {apply pow_le_pow' (h.left.right.right.right.left.left)
              (h.left.right.right.right.left.right)
              (lt_of_le_of_lt (le_of_lt (h.right)) (lt_of_lt_of_le (one_lt_two) (le_of_lt (h.right))))},
          },
        },
        show (x - y) * (x^t * (x-z) - y^t * (y-z)) + z^t * (x-z) * (y-z) ≥ 0, from add_nonneg h4 (mul_nonneg_of_nonneg_of_nonneg
        (h3.left)
        (h3.right)),
      }
    },
  },
  show (x^t * (x-y) * (x-z) + y^t * (y-z) * (y-x) + z^t * (z-x) * (z-y)) ≥ 0, from by {
    have h2 : x - z > 0 ∧ y-x > 0 ∧ z - x > 0 ∧ y - z > 0, from by {
      have h2_1 : x - z > 0, from sub_pos_of_lt h.left.right.right.right.left.right,
      have h2_2 : y - x > 0, from sub_pos_of_lt h.left.right.right.right.right,
      have h2_3 : z - x > 0, from sub_pos_of_lt h.left.right.right.right.right,
      have h2_4 : y - z > 0, from sub_pos_of_lt h.left.right.right.right.right,
      split, exact h2_1, split, exact h2_2, split, exact h2_3, exact h2_4,
    },
    rw [mul_add,mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_add,mul_one,mul_one],
    apply add_nonneg,
    split,
    calc (x^t * (x-z) - y^t * (y-z)) * (x - y) + (x - z) * (y - z) * z^t
    = (x^t * (x-z) - y^t * (y-z)) * (x - y) +
end --Needs more than 2000 tokens!

