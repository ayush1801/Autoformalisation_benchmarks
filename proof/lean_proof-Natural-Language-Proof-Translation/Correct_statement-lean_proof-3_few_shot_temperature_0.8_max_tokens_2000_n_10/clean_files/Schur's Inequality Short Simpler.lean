
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
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {rw [← sub_eq_add_neg,← mul_one z,mul_add], apply (mul_nonneg),
      exact sub_nonneg.mpr ⟨hxy,hyz⟩, apply sub_nonneg,
        {rw ← sub_eq_add_neg at hz,exact add_nonneg_of_nonneg_of_nonneg hz ht,},
        {apply add_nonneg,exact sub_nonneg hxy,rw ← sub_eq_add_neg at hz,
        exact add_nonneg_of_nonneg_of_neg hz ht,}, },
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from by {
      repeat {rw ← mul_assoc},
      rw add_mul,
      rw ← add_comm,
      rw ← add_mul,
      rw ← add_assoc,
      rw ← add_assoc,
      apply add_le_add_left,
      show z^t * (y - z) * (x - z) ≥ 0, from by {
        rw ← mul_assoc,
        repeat {rw mul_comm z,},
        apply mul_nonneg,
        exact ht,
        apply mul_nonneg,
        exact sub_nonneg hyz,
        exact sub_nonneg.mpr ⟨hz,hxy⟩,
      },
      apply h1,
    }
  end

/--`theorem`
Schur's Inequality
Let $x, y, z \in \R_{\ge 0}$ be positive real numbers such that $x \ge y \ge z \ge 0$.

Let $t \in \R, t > 0$ be a (strictly) positive real number.


Then:
:$\paren {x^t - z^t} \paren {y^t - z^t} \ge \paren {y^t - x^t} \paren {z^t - 0}$
{{qed}}
-/
theorem schur_inequality' (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  (x^t - z^t) * (y^t - z^t) ≥ (y^t - x^t) * z^t :=
begin
  rw ← mul_assoc,
  rw ← mul_assoc,
  rw ← mul_assoc,
  rw ← mul_assoc,
  rw ← sub_eq_add_neg,
  rw ← sub_eq_add_neg,
  rw ← sub_eq_add_neg,
  rw ← sub_eq_add_neg,
  apply schur_inequality,
  show x - y ≥ y - x, from by {rw ← sub_eq_add_neg, repeat {rw ← sub_eq_add_neg}, rw sub_eq_add_neg x, rw sub_eq_add_neg y, rw sub_eq_add_neg z, repeat {rw mul_comm}, apply mul_le_mul_right, exact hz,apply sub_nonneg, exact sub_nonneg hxy,exact sub_nonneg hyz,},
  exact hyz,
  exact hz,
  exact ht,
end

--OUTPUT 2
theorem begin
    have h1 : x^t * (x - y) * (x - z) ≥ 0, from mul_nonneg (mul_nonneg (sqrt_nonneg x) (sub_nonneg hxy hz)) (sub_nonneg hxy hz),
    have h2 : y^t * (y - z) * (y - x) ≥ 0, from mul_nonneg (mul_nonneg (sqrt_nonneg y) (sub_nonneg hyz hz)) (sub_nonneg hyz hx),
    have h3 : z^t * (z - x) * (z - y) ≥ 0, from mul_nonneg (mul_nonneg (sqrt_nonneg z) (sub_nonneg hz hx)) (sub_nonneg hz hy),
    have h4 : y^t * (y - z) ≥ 0, from sqrt_nonneg y,
    have h5 : x^t * (x - z) ≥ 0, from sqrt_nonneg x,
    have h6 : y^t * (y - x) ≥ 0, from sqrt_nonneg y,
    have h7 : z^t * (z - x) ≥ 0, from sqrt_nonneg z,
    have h8 : z^t * (z - y) ≥ 0, from sqrt_nonneg z,
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, from
      by {
        calc x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y)
          = x^t * (x - y) * (x - z) + y^t * (y - z)^2 + z^t * (z - x) * (z - y) : by ring
        ... ≥ y^t * (y - z)^2 : by {linarith [h1,h2]}
        ... = y^t * (y - z) * (y - z) + y^t * (y - z) * (z - y) : by ring
        ... = y^t * (y - z) * (y - z) + y^t * (z - y) * (y - z) : by ring
        ... ≥ y^t * (z - y) * (y - z) : by {linarith [h4, h6]}
        ... = z^t * (z - y) * (y - z) : by rw ← sqrt_sqrt,
        },
  end


/--`theorem`
Schur's Inequality Long
Let $x, y, z \in \R_{\ge 0}$ be positive real numbers such that $x \ge y \ge z > 0$.


Then:
:$x^2 \paren {x - y} \paren {x - z} + y^2 \paren {y - z} \paren {y - x} + z^2 \paren {z - x} \paren {z - y} \ge 0$

`proof`
Set $a = x, b = y, c = z$. 
{{qed}}
-/
theorem schur_inequality' (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z > 0)  : 
  x^2 * (x - y) * (x - z) + y^2 * (y - z) * (y - x) + z^2 * (z - x) * (z - y) ≥ 0 :=
begin
  apply schur_inequality x y z hxy hyz (le_of_lt hz) (by {norm_num,simp}),
end

--OUTPUT 3
theorem begin
   -- First, we rearrange the inequality to
    -- (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0
    have h1 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥
    x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z),
    from le_sub (x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y))
    z^t * (x - z) * (y - z),
    rw ← sub_eq_add_neg (x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x)) (z^t * (x - z) * (y - z)) at h1,
    have h2 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z) ≥
    x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z) + z^t * (x - z) * (y - z),
    from le_add' h1 z^t * (x - z) * (y - z),
    rw ← neg_eq_zero_iff_eq (z^t * (x - z) * (y - z)) at h2,
    rw ← neg_eq_zero_iff_eq (x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z)) at h2,

    -- Then, we rearrange the expression to
    -- (x - y) * (x^t * (x - z) - y^t * (y - z)) + (1/t) * (x - y) * (x - z) * (y - z)
    have h3 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z) + z^t * (x - z) * (y - z) ≥
    x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z) + (1/t) * (x - y) * (x - z) * (y - z),
    from add_le_add h2 ((1/t) * (x - y) * (x - z) * (y - z)) (x^t * (x - y) * (x - z))
    (y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z) + (1/t) * (x - y) * (x - z) * (y - z)),
    rw ← sub_eq_add_neg (x^t * (x - y) * (x - z)) (y^t * (y - z) * (y - x)) at h3,
    rw ← sub_eq_add_neg (x^t * (x - y) * (x - z) - y^t * (y - z) * (y - x)) (z^t * (x - z) * (y - z)) at h3,
    rw ← sub_eq_add_neg (x^t * (x - y) * (x - z) - y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z))
    ((1/t) * (x - y) * (x - z) * (y - z)) at h3,
    rw ← add_eq_sub_of_eq (x^t * (x - y) * (x - z) - y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z))
    ((1/t) * (x - y) * (x - z) * (y - z)) at h3,
    rw add_sub_cancel' (x^t * (x - y) * (x - z) - y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z) +
    ((1/t) * (x - y) * (x - z) * (y - z)))
    ((1/t) * (x - y) * (x - z) * (y - z)) at h3,
    rw ← neg_eq_zero_iff_eq (x^t * (x - y) * (x - z) - y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z) +
    ((1/t) * (x - y) * (x - z) * (y - z))) at h3,
    rw neg_eq_zero_iff_eq at h3,
    have h4 : (x^t * (x - y) * (x - z) - y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z) +
    ((1/t) * (x - y) * (x - z) * (y - z))) = 0,
    from h3,

    have h5 : x^t * (x - y) * (x - z) - y^t * (y - z) * (y - x) - z^t * (x - z) * (y - z) +
    ((1/t) * (x - y) * (x - z) * (y - z)) ≥
    (x - y) * (x^t * (x - z) - y^t * (y - z)) + (1/t) * (x - y) * (x - z) * (y - z),
    from le_of_eq h4,


    -- Then, we show that each term on the right hand side is non-negative
    have h6 : (x - y) ≥ 0, from by {rw lt_iff_le_not_le at hxy, assumption},
    have h7 : (x - z) ≥ 0, from le_of_lt hxy,
    have h8 : (y - z) ≥ 0, from le_of_lt hyz,
    have h9 : (1/t) ≥ 0, from by {rw lt_iff_le_not_le at ht,assumption},

    -- Then, we show that each term on the right hand side is non-negative
    have h10 : (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by apply sub_le_self,
    have h11 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0,
    from mul_nonneg h6 h10,
    have h12 : (1/t) * (x - y) * (x - z) * (y - z) ≥ 0,
    from mul_nonneg h9 (mul_nonneg (mul_nonneg h6 h7) h8),
    have h13 : (x - y) * (x^t * (x - z) - y^t * (y - z)) +
    ((1/t) * (x - y) * (x - z) * (y - z)) ≥ 0,
    from add_nonneg h11 h12,
    
    exact (add_le_add h5 h13),

end --Needs more than 2000 tokens!

--OUTPUT 4
theorem begin
    have h1 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥
      (x - y) * ((x^t * (x - z)) - (y^t * (y - z))) + z^t * (z - x) * (y - z), from
    have h1 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥
        (x - y) * x^t * (x - z) - (x - y) * y^t * (y - z) + z^t * (z - x) * (y - z), from
          add_le_add_right (sub_nonneg.2 (le_of_mul_le_mul_right (le_of_lt ht) (sub_nonneg.1 hxy)))
            (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (add_le_add_left (sub_nonneg.1 (sub_nonneg.1 hyz)) 
              (sub_nonneg.1 (sub_nonneg.1 hxy))))))
            (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (add_le_add_left (sub_nonneg.1 (sub_nonneg.1 (sub_nonneg.1 hyz))) 
              (sub_nonneg.1 (sub_nonneg.1 hxy))))))
            (sub_nonneg.2 (sub_nonneg.1 (sub_nonneg.1 hz))),
    have h2 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥
        (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (z - x) * (y - z), 
          from le_of_sub_le_sub h1 (sub_le_sub_right ((x - y) * y^t * (y - z)) (sub_nonneg.2 (le_of_mul_le_mul_right (le_of_lt ht)
            (sub_nonneg.1 (sub_nonneg.1 (sub_nonneg.1 hyz)))))),
    have h3 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥
        (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (z - x) * (y - z) ≥ 0, from 
          add_nonneg (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 
            (sub_nonneg.2 (sub_nonneg.2 (sub_le_sub_right (sub_le_sub_right (sub_nonneg.1 (sub_nonneg.2 (sub_nonneg.2 
              (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 
                (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.1 (sub_nonneg.1 hyz))))))))))))))))))))))))))
            (sub_nonneg.1 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2
              (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 
                (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.1 (sub_nonneg.1 hyz))))))))))))))))))))))) (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 
                  (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 
                    (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.2 (sub_nonneg.1 hz)))))))))))))))))) 0)
  end


end

--OUTPUT 5
theorem begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0,
    calc
      (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z)
      = (x^t - y^t) * (x - y) * (x - z) + z^t * (x - z) * (y - z) 
      : by ring
      ... = (x^t - y^t) * (x - z) * (x - y) + z^t * (x - z) * (y - z) 
      : by {simp only [mul_comm], ring}
      ... = x^t * (x - z) * (x - y) + y^t * (y - z) * (x - y) + z^t * (x - z) * (y - z) 
      : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (x - z) * (y - z)
      : by {simp only [mul_comm], ring}
      ... = x^t * (x - y) * (x - z) + y^t * (y - x) * (y - z) + z^t * (z - x) * (z - y)
      : by {rw ← neg_mul_eq_mul_neg, rw ← one_mul (x - y), repeat {rw ← sub_eq_add_neg}, ring}
      ... ≥ 0 : by {apply add_nonneg, apply add_nonneg, apply mul_nonneg, apply pow_nonneg, 
                    linarith, apply mul_nonneg, apply mul_nonneg, linarith, linarith, 
                    apply pow_nonneg, linarith, apply mul_nonneg, linarith, linarith,
                    apply pow_nonneg, linarith, },
  end

/--`theorem`
Schur's Inequality Long Simpler
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
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0,
    calc
      (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z)
      = (x^t - y^t) * (x - y) * (x - z) + z^t * (x - z) * (y - z) 
      : by ring
      ... = (x^t - y^t) * (x - z) * (x - y) + z^t * (x - z) * (y - z) 
      : by {simp only [mul_comm], ring}
      ... = x^t * (x - z) * (x - y) + y^t * (y - z) * (x - y) + z^t * (x - z) * (y - z) 
      : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (x - y) + z^t * (x - z) * (y - z)
      : by {simp only [mul_comm], ring}
      ... = x^t * (x - y) * (x - z) + y^t * (y - x) * (y - z) + z^t * (z - x) * (z - y)
      : by {rw ← neg_mul_eq_mul_neg, rw ← one_mul (x - y), repeat {rw ← sub_eq_add_neg}, ring}
      ... ≥ 0 : by {apply add_nonneg, apply add_nonneg, apply mul_nonneg, apply pow_nonneg, 
                    linarith, apply mul_nonneg, apply mul_nonneg, linarith, linarith, 
                    apply pow_nonneg, linarith, apply mul_nonneg, linarith, linarith,
                    apply pow_nonneg, linarith, },
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
theorem  schur_inequality_long_w_rearrange (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 :=
  begin
    have h1 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0,
    calc
      (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z)
      = (x^t - y^t
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem begin
    have h1 : x^t * (x - z) - y^t * (y - z) ≥ 0, from by {
      have h1 : x^t * (x - z) ≥ y^t * (y - z), from by {rw exp_mul, apply monotonicity_of_exponential, exact ht, exact hyz,},
      have h2 : x^t * (x - z) ≥ 0, from by {apply mul_nonneg (hypothesis_of_multiplication x^t (x - z)) (hypothesis_of_multiplication (x - z) x^t), exact ht, exact hz,},
      exact le_trans h1 h2,
    },
    have h2 : x - y ≥ 0, from by {exact hxy},
    have h3 : (x - z) * (y - z) ≥ 0, from by {apply mul_nonneg, exact hz, exact hxy,},
    have h4 : y^t * (y - z) * (y - x) ≥ 0, from by {apply mul_nonneg h3, exact hxy,},
    have h5 : z^t * (z - x) * (z - y) ≥ 0, from by {apply mul_nonneg, exact hz,exact hxy,},
    have h6 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0, from by {apply mul_nonneg, exact h2, exact h1,},
    have h7 : x^t * (x - y) * (x - z) ≥ 0, from by {apply mul_nonneg, exact h2, exact hz,},
    have h8 : y^t * (y - z) * (y - x) ≥ 0, from by {apply mul_nonneg, exact h3, exact hz,},
    have h9 : z^t * (z - x) * (z - y) ≥ 0, from by {apply mul_nonneg, exact hz, exact hxy,},
    calc x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) 
      = (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) : by ring
    ... ≥ 0 : by linarith
  end

/--`theorem`
Triangle Inequality for Complex Numbers
Let $z_1, z_2 \in \C$ be complex numbers.

Then:
:$\abs {z_1 + z_2} \le \abs {z_1} + \abs {z_2}$

`proof`
Expanding:
:$\abs {z_1 + z_2} = \sqrt {z_1 z_1^* + z_2 z_2^* + z_1 z_2^* + z_2 z_1^*}$

From the definition of complex number multiplication:
:$\abs {z_1 + z_2} = \sqrt {z_1 z_1^* + z_2 z_2^* + 2 \Re \paren {z_1 z_2^*}}$


The real and imaginary parts, $a$ and $b$ of a complex number $z = a + bi$ are related as follows:
:$\abs {z} = \sqrt {a^2 + b^2}$

From the definition of the norm of a complex number:

{{begin-eqn}}
{{eqn | l = \abs {z_1 z_2^*}
      | r = \Re \paren {z_1 z_2^*} + i \Im \paren {z_1 z_2^*}
      | c = Definition of complex number
}}
{{eqn | r = \abs {z_1} \abs {z_2} \cos \paren {\theta_1 - \theta_2} + i \abs {z_1} \abs {z_2} \sin \paren {\theta_1 - \theta_2}
      | c = Using Euler's form
}}
{{eqn | r = \abs {z_1} \abs {z_2} \cos \paren {\theta_1 - \theta_2}
      | c = Imaginary component is zero
}}
{{end-eqn}}

Then, we have:
:$\abs {z_1} \abs {z_2} \cos \paren {\theta_1 - \theta_2} = \Re \paren {z_1 z_2^*}$

Using the cosine addition formula:
:$\cos \paren {\theta_1 - \theta_2} = \cos \theta_1 \cos \theta_2 + \sin \theta_1 \sin \theta_2$

:$\cos \paren {\theta_1 - \theta_2} = \cos^2 \theta_1 + \cos^2 \theta_2$

:$\cos \paren {\theta_1 - \theta_2} \le 1$

:$\abs {z_1} \abs {z_2} \cos \paren {\theta_1 - \theta_2} \le \abs {z_1} \abs {z_2}$

:$\Re \paren {z_1 z_2^*} \le \abs {z_1} \abs {z_2}$

:$\sqrt {z_1 z_1^* + z_2 z_2^* + 2 \Re \paren {z_1 z_2^*}} \le \sqrt {\paren {\abs {z_1}}^2 + \paren {\abs {z_2}}^2 + 2 \abs {z_1} \abs {z_2}}$

Using the square root function is monotone:
:$\sqrt {z_1 z_1^* + z_2 z_2^* + 2 \Re \paren {z_1 z_2^*}} \le \abs {z_1} + \abs {z_2}$
{{qed}}
-/
theorem triangle_inequality_complex (z1 z2 : ℂ) : abs (z1 + z2) ≤ abs z1 + abs z2 :=
begin
  have h1 : z1 z1^* + z2 z2^* + 2 *Re (z1 z2^*) ≥ 0, from by {
    have h1 : z1 z1^* + z2 z2^* ≥ 0, from by {apply add_nonneg (real.pos_pow_two_ge_zero (β z1)) (real.pos_pow_two_ge_zero (β z2)),},
    have h2 : (2 : ℂ) *Re (z1 z2^*) ≥ 0, from by {rw mul_two, apply mul_nonneg, show (-1 : ℂ) ≥ 0, exact le_of_lt ht, exact Re_nonneg (z1 z2^*),},
    have h3 : z1 z1^* + z2 z2^* + 2 *Re (z1 z2^*) ≥ 0, from by {apply add_nonneg h1 h2,},
    show z1 z1^* + z2 z2^* + 2 *Re (z1 z2^*) ≥ 0, from h3,
  },
  have h2 : abs (z1 + z2) = sqrt (z1 z1^* + z2 z2^* + 2 *Re (z1 z2^*)), from by {rw abs_of_nonneg h1,},
  have h3 : abs (z1 + z2) = sqrt (z1 z1^* + z2 z2^* + 2 *Re (z1 z2^*)), from by {rw abs_of_nonneg h1,},
  have h4 : abs z1 * abs z2 * cos (β z1 - β z2) = Re (z1 z2^*), from by {rw abs_mul abs_of_nonneg (Re_nonneg (z1 z2^*)), rw mul_comm, rw abs_of_nonneg, ring},
 
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem begin
    have h1 : x^t * (x - z) ≥ y^t * (y - z), by {
      apply schur_inequality_long,
      have h2 : z ≥ y, from by {apply le_trans hz hyz,},
      exact ⟨hxy,h2,hz,ht⟩,
    },
    have h3 : x^t * (x - z) * (x - y) ≥ y^t * (x - y) * (y - z), from
      by {apply mul_le_mul h1 (by {apply sub_nonneg, exact hxy}),
      split,
      show x^t * (x - z) ≥ 0, from mul_nonneg (pow_nonneg ht hz) (sub_nonneg hx hz),
      show x - y ≥ 0, from by {apply sub_nonneg, exact hx,},
      },
    have h4 : y^t * (x - y) * (y - z) ≥ z^t * (x - y) * (y - z), from
      by {apply mul_le_mul_of_nonneg_right (pow_nonneg ht hz)
      (by {apply sub_nonneg, exact hyz}),
      split,
      show y^t * (x - y) ≥ 0, from mul_nonneg (pow_nonneg ht hy) (sub_nonneg hy hx),
      show x - y ≥ 0, from by {apply sub_nonneg, exact hx,},},
    have h5 : y^t * (x - y) * (y - z) + z^t * (x - z) * (y - z) ≥ 0, from
      by {rw ← add_assoc y^t ((x - y) * (y - z)) (z^t * (x - z) * (y - z)),
      apply add_le_add, exact h4,
      show z^t * (x - z) * (y - z) ≥ 0, from mul_nonneg (pow_nonneg ht hz)
      (mul_nonneg (by {apply sub_nonneg, exact hx,}) (by {apply sub_nonneg, exact hy,})),
      },
    have h6 : x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z) ≥ 0, from by {
      rw ← add_assoc (x^t * (x - y) * (x - z)) (-y^t * (x - y) * (y - z)) (y^t * (x - y) * (y - z)),
      apply add_le_add_of_le_of_nonpos,
      exact ⟨h3,zero_le_one⟩,
      show -y^t * (x - y) * (y - z) ≤ 0, from by {repeat {rw ← neg_eq_neg_one_mul},
      rw ← mul_assoc, rw ← mul_assoc, apply mul_le_mul_of_nonneg_left h4,
      show -1 ≥ 0, from by {apply neg_nonneg_of_nonpos (by {rw zero_eq_neg_zero,
      apply lt_irrefl 0 ht,}),},},
    },
    have h7 : x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z) + y^t * (x - y) * (y - z) ≥ 0, from
      by {rw ← add_assoc _ _ (y^t * (x - y) * (y - z)),
      apply add_le_add_of_le_of_nonpos, exact h6,
      show y^t * (x - y) * (y - z) ≤ 0,
      from by {rw ← mul_assoc, rw ← mul_assoc,
      apply mul_le_mul_of_nonneg_left (by {apply sub_nonneg, exact hy,}),
      show -1 ≥ 0, from by {apply neg_nonneg_of_nonpos (by {rw zero_eq_neg_zero,
      apply lt_irrefl 0 ht,}),},
      show x - y ≥ 0, from by {apply sub_nonneg, exact hx,},},
      },
    have h8 : x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z) + y^t * (x - y) * (y - z)
      + z^t * (x - z) * (y - z) ≥ 0, from
      by {rw ← add_assoc, apply add_le_add_of_le_of_nonpos,
      show x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z) + y^t * (x - y) * (y - z) ≥ 0,
      from h7,
      show z^t * (x - z) * (y - z) ≤ 0, from by {rw ← mul_assoc, rw ← mul_assoc,
      apply mul_le_mul (by {apply sub_nonneg, exact hy,}) (by {apply sub_nonneg, exact hx,}),
      show z^t ≤ 0, from by {apply le_of_lt, apply lt_of_mul_pos_of_pos_of_pos,
      show 0 < 1, from one_pos,
      show 0 < z ^ t, from mul_pos ht hz,
      show 0 < x - z, from by {apply sub_pos_of_lt, exact hx,},
      },
      },},
    have h9 : y^t * (x - y) * (y - z) + z^t * (x - z) * (y - z) + x^t * (x - y) * (x - z) ≥ 0, from
      by {rw add_comm _ (x^t * (x - y) * (x - z)),
      repeat {rw ← add_assoc},
      apply add_le_add_of_le_of_nonpos,
      show y^t * (x - y) * (y - z) + z^t * (x - z) * (y - z) ≥ 0, from h5,
      show x^t * (x - y) * (x - z) ≤ 0, from by {rw ← mul_assoc,
      apply mul_le_mul (by {apply sub_nonneg, exact hx,}) (by {apply sub_nonneg, exact hy,}),
      show x^t ≤ 0, from by {apply le_of_lt, apply lt_of_mul_pos_of_pos_of_pos,
      show 0 < 1, from one_pos, show 0 < x^t, from mul_pos ht hx,
      show 0 < y - x, from by {apply sub_pos_of_lt, exact hy,},
      },
      },},
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0,
    from by {repeat {rw ← add_assoc}, rw [← add_assoc (y^t * (y - z) * (y - x)) (z^t * (z - x) * (z - y)),
    ← add_assoc (x^t * (x - y) * (x - z)) (y^t * (y - z) * (y - x))],
    rw add_comm (y^t * (y - z) * (y - x)),
    apply add_le_add_of_le_of_nonpos,
    show x^t * (x - y) * (x - z) + y^t * (x - y) * (y - z) + y^t * (y - z) * (y - x) ≥ 0,
    from h8,
    show z^t * (x - z) * (y - z) ≤ 0, from
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem begin
    have h1 : z^t * (x - z) * (y - z) ≥ 0, from mul_nonneg (mul_nonneg (hz.pow ht) (sub_nonneg (le_refl x) (le_refl z)))
      (sub_nonneg (le_refl y) (le_refl z)),
    have h2 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0, from mul_nonneg (sub_nonneg hxy (le_refl y))
    (sub_nonneg (mul_nonneg_of_nonneg_of_nonneg (hxy.pow ht) (sub_nonneg (le_refl x) (le_refl z)))
    (mul_nonneg_of_nonneg_of_nonneg (hyz.pow ht) (sub_nonneg (le_refl y) (le_refl z)))),
    calc x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥
    (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) : by {
      have h3 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥
      z^t * (x - z) * (y - z), from add_nonneg (add_nonneg (mul_nonneg_of_nonneg_of_nonneg (hxy.pow ht)
      (mul_nonneg (sub_nonneg hxy (le_refl z)) (sub_nonneg (le_refl x) (le_refl z))))
      (mul_nonneg_of_nonneg_of_nonneg (hyz.pow ht) (mul_nonneg (sub_nonneg (le_refl y) (le_refl z))
      (sub_nonneg hyz (le_refl x))))) (mul_nonneg (hz.pow ht) (mul_nonneg_of_nonneg_of_nonneg (sub_nonneg (le_refl z) (le_refl x))
      (sub_nonneg (le_refl z) (le_refl y)))),
      have h4 : z^t * (x - z) * (y - z) ≥ 0, from mul_nonneg (mul_nonneg (hz.pow ht) (sub_nonneg (le_refl x) (le_refl z)))
      (sub_nonneg (le_refl y) (le_refl z)),
      have h5 : z^t * (x - z) * (y - z) - z^t * (x - z) * (y - z) ≥ 0, from sub_nonneg h4 h4,
      have h6 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) -
      z^t * (x - z) * (y - z) ≥ 0, from sub_nonneg h3 h4,
      rw ← add_sub_cancel' h6,    },
    calc (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0 : by {rw add_comm, exact add_nonneg h2 h1,}
  end


/--`theorem`
Schur's Inequality Long Simpler
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
theorem  schur_inequality_2 (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 :=
  begin
    have h1 : z^t * (x - z) * (y - z) ≥ 0, from mul_nonneg (mul_nonneg (hz.pow ht) (sub_nonneg (le_refl x) (le_refl z)))
      (sub_nonneg (le_refl y) (le_refl z)),
    have h2 : (x - y) * (x^t * (x - z) - y^t * (y - z)) ≥ 0, from mul_nonneg (sub_nonneg hxy (le_refl y))
    (sub_nonneg (mul_nonneg_of_nonneg_of_nonneg (hxy.pow ht) (sub_nonneg (le_refl x) (le_refl z)))
    (mul_nonneg_of_nonneg_of_nonneg (hyz.pow ht) (sub_nonneg (le_refl y) (le_refl z)))),
    calc x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥
    (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) : by {
      have h3 : x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥
      z^t * (x - z) * (y - z), from add_nonneg (add_nonneg (mul_nonneg_of_nonneg_of_nonneg (hxy.pow ht)
      (mul_nonneg (sub_nonneg hxy (le_refl z)) (sub_nonneg (le_refl x) (le_refl z))))
      (mul_nonneg_of_nonneg_of_nonneg (hyz.pow ht) (mul_nonneg (sub_nonneg (le_refl y) (le_refl z))
      (sub_nonneg hyz (le_refl x))))) (mul_nonneg (hz.pow ht) (mul_nonneg_of_nonneg_of_nonneg (sub_nonneg (le_refl z) (le_refl x))
      (sub_nonneg (le_refl z) (le_refl y)))),
      have h4 : z^t * (x - z) * (y - z) ≥ 0, from mul_nonneg (mul_nonneg (hz.p
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem begin 
    let q : ℝ := x - y,
    calc 0 ≤ (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) : 
      by {
        have h1 : x - z ≥ 0, from by { rw [sub_le_sub_iff_left,sub_le_sub_iff_left] at ⊢ hzyz,
        erw ← hxy,exact hzyz,}
        have h2 : x^t ≥ y^t, from by {rw ← pow_lt_pow_iff_lt,rw ← hxy, rw ← ht, rw add_lt_add_iff_right,
        rw lt_sub_iff_add_lt,have h3 : x > 0, from lt_of_le_of_lt hz h1,exact h3, rw one_lt_two,exact ht},
        have h3 : y - z ≥ 0, from by {rw ← hxy, rw sub_le_sub_iff_left,exact hyz,},
        rw mul_nonneg,rw mul_nonneg,rw mul_nonneg,rw mul_nonneg,
        repeat {rw ← pow_lt_pow_iff_lt,rw ← ht},rwa ← hxy,rwa ← hxy,
        rw ← hxy,exact h2,rw ← ht,rw add_lt_add_iff_right,
        rw lt_sub_iff_add_lt,rw sub_pos_iff,rwa ← hxy,rwa ← hxy,rwa ← hxy,
        have h4 : x - z > 0, from by {rw ← hxy,rw sub_pos_iff,exact h1,},
        have h5 : y - z > 0, from by {rw ← hxy,rw sub_pos_iff,exact h3,},
        rw one_lt_two,exact ht,exact h4,exact h5,
      },
    
    show x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0, 
    from by {
      rw add_mul,rw add_mul,rw add_mul,rw add_mul,rw add_mul,rw add_mul,rw add_mul,
      rw add_mul,rw add_mul,rw mul_comm (x - z) (x^t),rw mul_comm (y - z) (x^t),
      rw sub_eq_zero,rw mul_comm z^t z,rw mul_comm z^t z,rw mul_comm z^t z,rw mul_comm z^t z,
      rw ← sub_eq_add_neg,rw ← sub_eq_add_neg,rw ← sub_eq_add_neg,rw ← sub_eq_add_neg,
      rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,
      rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,
      rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,rw ← mul_neg,
      calc 0 ≤ (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) : this
      ... = x^t * (x - y) * (x - z) - x^t * (x - y) * (y - z) + z^t * (x - z) * (y - z) : by ring
      ... = y^t * y^t * (y - x) * (y - z) - y^t * (x - y) * (y - z) + z^t * (x - z) * (y - z) : by ring
      ... = x^t * x^t * (x - y) * (x - z) - y^t * (x - y) * (y - z) + z^t * (x - z) * (y - z) - y^t * y^t * (y - x) * (y - z) + y^t * y^t * (y - x) * (y - z) : by ring
      ... = x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) : by ring},
  end


/--`theorem`
Schur's Inequality is a Generalization of AM-GM
Let $x, y, z \in \R_{\ge 0}$ be positive real numbers such that that $x \ge y \ge z \ge 0$.

Then:
:$x y z \le \frac {x^3 + y^3 + z^3}3$

`proof`
Consider the following expression:
:$\frac {x^3 + y^3 + z^3}3 - x y z$


This is an increasing function of $x, y, z$.

{{begin-eqn}}
{{eqn | l \frac {x^3 + y^3 + z^3}3 - x y z
      | r \frac 1 3 \paren {5 x^3 - x y^2 - x z^2}
      | c
}}
{{eqn | l \frac {x^3 + y^3 + z^3}3 - x y z
      | r \frac 1 3 \paren {5 y^3 - y x^2 - y z^2}
      | c
}}
{{eqn | l \frac {x^3 + y^3 + z^3}3 - x y z
      | r \frac 1 3 \paren {5 z^3 - z x^2 - z y^2}
      | c
}}
{{end-eqn}}

We see that each of these terms is non-negative.

So, directly:
:$\frac {x^3 + y^3 + z^3}3 - x y z \ge 0$

Thus:

{{begin-eqn}}
{{eqn | l x y z
      | r \frac {x^3 + y^3 + z^3}3
      | c
}}
{{end-eqn}}
{{qed}}
-/
theorem schur_is_amgm (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) :
  x * y * z ≤ ((x^3 + y^3 + z^3)/3) :=
  begin
    have h1 : x^3 - y^2 * x - z^2 * x ≥ 0, from calc
      0 ≤ (x - y) * (x^2 - z^2) : by {rw ← pow_lt_pow_iff_lt,rw ← hxy, rw ← ht, rw add_lt_add_iff_right,rw lt_sub_iff_add_lt,rw sub_pos_iff,rw one_lt_two,exact ht,
      rw sub_pos_iff,exact hz,rw sub_pos_iff,exact hz,rwa ← hxy,rwa ← hxy,}
    ... = x^3 - y^2 * x - z^2 * x : by rwa ← mul_sub,rw ← mul_sub,

    
    have h2 : y^3 - x^2 * y - z^2 * y ≥ 0, from calc
      0 ≤ (y - x) * (y^2 - z^2) : by {rw ← pow_lt_pow_iff_lt,rw
end --Needs more than 2000 tokens!

--OUTPUT 10
theorem begin 
    have h0 : t > 0, from ht,
    have h1 : (x - y) * (x - y) ≥ 0, from by {rw ← sq, apply pow_two},
    have h2 : (y - z) * (y - z) ≥ 0, from by {rw ← sq, apply pow_two},
    have h3 : (x - z) * (x - z) ≥ 0, from by {rw ← sq, apply pow_two},
    have h4 : (x - z) * (x - z) * (x - z) * (x - z) ≥ 0, from by rw ← four,
    have h5 : (y - z) * (y - z) * (y - z) * (y - z) ≥ 0, from by rw ← four,
    have h6 : (x - z) * (x - z) * (x - z) * (x - z) * (x - z) * (x - z) ≥ 0, from by rw ← six,
    have h7 : (y - z) * (y - z) * (y - z) * (y - z) * (y - z) * (y - z) ≥ 0, from by rw ← six,
    have h8 : (x - y) * (x - y) * (x - y) * (x - y) ≥ 0, from by rw ← four,

    have h9 : (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z) ≥ 0, from by {
      calc
      (x - y) * (x^t * (x - z) - y^t * (y - z)) + z^t * (x - z) * (y - z)
      = (x - y) * ((x - z) * x^(t - 1) - (y - z) * y^(t - 1)) + z^t * (x - z) * (y - z) : by {rw ← pow_sub}
      ... = ((x - y) * (x - z) * x^(t - 1)) - ((x - y) * (y - z) * y^(t - 1)) + z^t * (x - z) * (y - z) : by rw mul_sub
      ... = ((x - y) * (x - z)) * (x^(t - 1) - y^(t - 1)) + ((x - y) * (y - z) * y^(t - 1)) + z^t * (x - z) * (y - z) : by rw mul_sub
      ... = ((x - y) * (x - z)) * (x^(t - 1) - y^(t - 1)) + z^t * (x - z) * (y - z) + ((x - y) * (y - z) * y^(t - 1)) : by ring
      ... = (x - y) * (x - z) * x^(t - 1) + (x - y) * (x - z) * (-y^(t - 1)) + z^t * (x - z) * (y - z) + ((x - y) * (y - z) * y^(t - 1)) : by ring
      ... = (x - y) * (x - z) * x^(t - 1) + (x - y) * (x - z) * (-y^(t - 1)) + z^t * (x - z) * (y - z) + (x - y) * (y - z) * y^(t - 1) : by ring
      ... = (x - y) * (x - z) * (x^(t - 1) - y^(t - 1)) + z^t * (x - z) * (y - z) : by ring
      ... = (x - y) * (x - z) * (y^(t - 1) - x^(t - 1)) + z^t * (x - z) * (y - z) : by {rw pow_sub,from h0}
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + z^t * (x - z) * (y - z) : by rw neg_eq_iff_eq_neg
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (z^t * (x - z) * (y - z)) : by ring
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z) * (x - z) * z^(t - 1) : by rw mul_comm
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z) * (x - z) * z^(t - 1) : by ring
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z)^2 * z^(t - 1) : by rw ← pow_sub
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z) * (y - z) * z^(t - 1) : by rw mul_comm
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z)^2 * z^(t - 1) : by rw mul_comm
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z)^2 * z^(t - 1) : by ring
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z) * (y - z) * z^(t - 1) : by rw mul_comm
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z)^2 * z^(t - 1) : by rw mul_comm
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z)^2 * z^(t - 1) : by ring
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z)^2 * z^(t - 1) : by rw mul_comm
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z)^2 * z^(t - 1) : by rw mul_comm
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z) * (y - z) * z^(t - 1) : by ring
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z)^2 * z^(t - 1) : by rw mul_comm
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z)^2 * z^(t - 1) : by rw mul_comm
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z) * (y - z) * z^(t - 1) : by ring
      ... = (x - y) * (x - z) * (-x^(t - 1) + y^(t - 1)) + (y - z)^2 * z^(t - 1) : by rw mul_comm
      ... = (x - y)
end --Needs more than 2000 tokens!

