
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
Density of irrational orbit
The fractional parts of the integer multiples of an irrational number form a dense subset of the unit interval
`proof`
Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
$$
i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,
$$
which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$. Hence,
$$
S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}
$$
is an infinite subset of $\left[0,1\right]$.

By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$. One can thus find pairs of elements of $S$ that are arbitrarily close. Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.

To show that $S$ is dense in $[0, 1]$, consider $y \in[0,1]$, and $\epsilon>0$. Then by selecting $x \in S$ such that $\{x\}<\epsilon$ (which exists as $0$ is a limit point), and $N$ such that $N \cdot\{x\} \leq y<(N+1) \cdot\{x\}$, we get: $|y-\{N x\}|<\epsilon$.

QED
-/
theorem 
FEW SHOT PROMPTS TO CODEX(END)-/
--OUTPUT 1
theorem density_of_orbit_irrational_number :
  ∀ (α : ℝ) (h : ¬ is_rat α), ∃ S : ℕ → ℝ, ∀ x, y ∈ S, x ≠ y ∧ ∀ (ε : ℝ) (p : 0 ≤ ε), ∃ z ∈ S, ε ≥ abs (z - y) :=
begin
  assume (α : ℝ) (h : ¬ is_rat α),
  let S : ℕ → ℝ := λ i : ℕ, (i:ℝ)*α - ↑(floor(i*α)),
  have h1 : ∀ i j : ℕ, S i = S j → i = j, from by {
    assume (i j : ℕ),
    assume h2 : S i = S j,
    let h3 : i*α - ↑(floor(i*α)) = j*α - ↑(floor(j*α)), from 
      by {rw h2},
    have h4 : i*α - ↑(floor(i*α)) = j*α - floor(j*α), from
      by {rw h3},
    have h5 : i*α - floor(i*α) = j*α - floor(j*α), from
      by {rw ← int.coe_nat_sub (floor(i*α)) (floor(j*α)), rw add_comm, ring},

    have h6 : 0 ≤ i*α - floor(i*α), from
      by {rw ← (nat.cast_inj (floor(i*α))).symm, rw ← int.coe_nat_eq_coe_int_iff,
        rw int.nat_abs_of_nonneg, exact (floor_ge_0 _),},
    have h7 : 0 ≤ j*α - floor(j*α), from
      by {rw ← (nat.cast_inj (floor(j*α))).symm, rw ← int.coe_nat_eq_coe_int_iff,
        rw int.nat_abs_of_nonneg, exact (floor_ge_0 _),},

    have h8 : is_rat (i*α - floor(i*α)), from by {exact rat.is_rat_iff_is_int.2 (is_int_iff_exists_int_floor.2 h6)},
    have h9 : is_rat (j*α - floor(j*α)), from by {exact rat.is_rat_iff_is_int.2 (is_int_iff_exists_int_floor.2 h7)},
    have h10 : is_rat ((i*α - floor(i*α)) - (j*α - floor(j*α))), from by {apply rat.is_rat_add_rat_of_rat_rat h8 h9,},

    have h11 : is_rat (i*α - j*α), from by {ring at h5, rw ← h5 at h10, exact h10},
    have h12 : is_rat α, from by {apply rat.is_rat_mul_rat_of_rat h11 i j.symm,},
    have h13 : is_rat α, from by {rw ← (nat.cast_inj i).symm at h12, rw ← (nat.cast_inj j).symm at h12,
      rw mul_comm at h12, rw int.mul_comm at h12, rw int.nat_abs_of_nonneg at h12,
      rw mul_comm at h12, rw int.mul_comm at h12, rw int.nat_abs_of_nonneg at h12,
      exact h12,exact_mod_cast (floor_ge_0 _),}
    ,
    have h14 : is_rat α, from by {rw ← (nat.cast_inj j).symm at h13,
      rw int.nat_abs_of_nonneg at h13,exact h13,exact_mod_cast (floor_ge_0 _),}
    ,
    show i = j, from by {obviously,},
  },
  have h2 : ∀ x ∈ (S '' univ), ∃ y, y ∈ S ∧ y ≠ x, from by {
    assume (x : ℝ),
    assume h3 : ∃ i, x = S i ∧ i ∈ univ,
    have h4 : ∃ i, x = S i, from by {obviously},
    have h5 : ∃ i, x = S i ∧ i ∈ S '' univ, from by {obviously},
    have h6 : ∃ i, x = S i ∧ i ∈ univ, from by {obviously},
    obtain ⟨i, h7⟩ := h6,
    have h8 : ∃ j, x = S j ∧ j ∈ S '' univ, from by {obviously},
    obtain ⟨j, h9⟩ := h8,
    have h10 : ∃ i, x = S i ∧ i ∈ S '' univ, from by {obviously},
    obtain ⟨i, h11⟩ := h10,
    have h12 : x = S i, from by {obviously},
    have h13 : i ∈ S '' univ, from by {obviously},
    obtain ⟨l, h14⟩ := h13,
    have h15 : x = S l, from by {obviously},
    have h16 : l ∈ S '' univ, from by {obviously},
    have h17 : l ∈ S '' univ, from by {obviously},
    have h18 : l ∈ S '' univ, from by {obviously},
    have h19 : i = l, from by {obviously,},
    have h20 : S i = S l, from by {obviously,},
    have h21 : i ≠ l, from by {obviously,},
    have h22 : ∃ j, S j = x ∧ j ∈ S '' univ, from by {obviously,},
    obtain ⟨j, h23⟩ := h22,
    have h24 : ∃ j, S j = x ∧ j ∈ S '' univ, from by {obviously,},
    obtain ⟨j, h25⟩ := h24,
    have h26 : ∃ j, S j = x ∧ j ∈ S '' univ, from by {obviously,},
    obtain ⟨j, h27⟩ := h26,
    have h28 : S j = x, from by {obviously,},
    have h29 : S j = S i, from by {obviously,},
    have h30 : j = i, from by {obviously,},
    have h31 : j ≠ i, from by {obviously,},
    use S j,
    split,
    show S j ∈ S '' univ, from by {obviously},
    show S j ≠ x, from by {obviously},
  },
  have h3 : ∃ S : ℕ → ℝ, ∀ x, y ∈ S, x ≠ y, from by {
    have h3 : ∃ S : ℕ → ℝ, ∀ x, y ∈ S, x ≠ y ∧ ∀ (ε : ℝ) (p : 0 ≤ ε), ∃ z ∈ S, ε ≥ abs (z - y), from by {
      have h3 : ∃ S : ℕ → ℝ, ∀ x, y ∈ S, x ≠ y ∧ ∀ (ε : ℝ) (p : 0 ≤ ε), ∃ z ∈ S, ε ≥ abs (z - y), from by {
        have h3 : ∃ S : ℕ → ℝ, ∀ x, y ∈ S, x ≠ y ∧ ∀ (ε : ℝ) (p : 0 ≤ ε), ∃ z ∈ S, ε ≥ abs (z - y), from by {
          have h3 : ∃ S : ℕ → ℝ, ∀ x, y ∈ S, x ≠ y ∧ ∀ (ε :
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem density_irrational_orbit {α : Type*} [linear_ordered_field α] (α : α) (hα : ¬ is_rat α) : ∃ S : set α, ∀ epsilon : α, epsilon > 0 → ∃ {x ∈ S}, ∥ x ∥ < epsilon ∧ ∀ {x : set α}, x ∈ S → x ≠ 0 :=
begin
  have h1 : ∃! (x : α), x ∈ ℚ, from by {
    use (0 : α), obviously,},
  apply exists.elim h1, assume (x : α) (hx1 : x ∈ ℚ), 
  have hx2 : ¬ x = α, from by {
    assume h2 : x = α,
    have h3 : α ∈ ℚ, from by {
      have h4 : α ∈ ℕ, from by {
        have h5 : x ∈ ℕ, from by {
          have h6 : x ≠ 0, from by {
            assume h7 : x = (0 : α),
            have h8 : α ∈ ℝ, from by {
              have h9 : α ∈ ℚ, from by exact hx1,
              exact ⟨α, h9⟩,
            },
            have h10 : α ∈ ℕ, from by {
              apply is_rat_iff,
              have h11 : (0 : α) ∈ ℚ, from by exact ⟨0, zero_mem⟩,
              rw h7 at h11,
              rw rat_eq_int at h11,
              exact h11.left,
            },
            exact absurd h10 (int.coe_ne_top hα),
          },
          have h13 : rat.num x = 1, from by {
            have h14 : is_rat x, from by {
              have h15 : x ∈ ℝ, from by {
                have h16 : x ∈ ℚ, from by exact hx1,
                exact ⟨x, h16⟩,
              },
              have h17 : nonempty rat, from by {
                have h18 : nonempty ℕ, from by {
                  have h19 : (0 : α) ∈ ℝ, from by {
                    have h20 : (0 : α) ∈ ℚ, from by exact ⟨0, zero_mem⟩,
                    exact ⟨0, h20⟩,
                  },
                  exact ⟨int.nat_abs h19⟩,
                },
                apply int.eq_rat_of_int,
                exact ⟨x, h15, h18⟩,
              },
              cases h17 with (q : rat) (hq : q ∈ ℚ),
              exact ⟨q, hq⟩,
            },
            have h21 : rat.denom x = 1, from by exact int.eq_rat_of_int.mp (rat.num_denom x),
            rw [rat.num_denom_eq_iff_one_int x, h21],
            exact eq.symm (rat.num_eq_of_rat h14)},
            have h22 : rat.denom x = 1, from by exact int.eq_rat_of_int.mp (rat.num_denom x),
            have h23 : rat.num x = 0, from by {
              have h24 : int.nat_abs (rat.num x) = 0, from by {
                rw int.nat_abs_of_nonneg (rat.num_pos' x),
                exact h13,
              },
              exact int.nat_abs_eq_zero_iff.mp h24,
            },
            rw h23,
            rw h22,
            exact eq.symm (rat.eq_of_num_denom x),
          },
        exact absurd h2 h5,  
      },
      exact absurd h4 hα,
    },
    exact absurd h3 (is_rat_iff.mp hα).right,
  },
  have h4 : ∀ epsilon : α, epsilon > 0 → ∃ {x ∈ S}, ∥ x ∥ < epsilon ∧ ∀ {x : set α}, x ∈ S → x ≠ 0, from by {
    assume epsilon : α,
    assume h5 : epsilon > 0,
    let x := epsilon,
    have h6 : ∃! (x : α), x ∈ ℚ, from by {
      use (0 : α), obviously,},
    apply exists.elim h6, assume (x : α) (hx1 : x ∈ ℚ), 
    have y := (1 : α),
    have h7 : ∃ (y : set α), y ∈ S, from by {
      use {y},
      have h8 : y ∈ ℚ, from by exact ⟨0, zero_mem⟩,
      have h9 : y ∈ ℝ, from by exact ⟨y, h8⟩,
      have h10 : y ∈ ℤ, from by exact ⟨0, zero_mem⟩,
      exact ⟨y, h10⟩,
    },
    apply exists.elim h7, assume (z : set α) (hz : z ∈ S),
    use z,
    use hz,
    assume h11 : z = 0,
    have h12 := int.coe_ne_top hα,
    have h13 : 0 ∈ ℚ, from by exact ⟨0, zero_mem⟩,
    repeat {rw h11 at h13},
    repeat {rw is_rat_iff at h13},
    exact h12 h13.left,
  },
  use S,
  exact h4,
end

--OUTPUT 3
theorem density_of_irrational_orbit
: ∀ (α : ℝ) (hα : α ∉ ℚ), ∃ s : ℕ → ℕ, ∀ i : ℕ, ∃ k : ℕ, ∃ (n : ℕ) (hn : k ≠ n), abs ((s k : ℝ) - (s n : ℝ)) < (1 : ℝ) / (2^i) :=
begin
  -- Let $\alpha$ be an irrational number.
  assume (α : ℝ) (hα : α ∉ ℚ),
  -- Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have hA : ∀ (i j : ℕ), i ≠ j → (nat.to_real i * α) % 1 ≠ (nat.to_real j * α) % 1, from by {
    assume (i j : ℕ) (hi : i ≠ j),
    have h1 : ∀ (x : ℝ) (i : ℤ), x % 1 ≠ x - i, from by {
      assume (x : ℝ) (i : ℤ),
      have h1 : (x % 1) + i = x, from by {rw ← int.coe_nat_sub i, rw int.sub_eq_add_neg, rw nat.cast_add, rw nat.cast_add, rw nat.cast_mul, rw nat.cast_mul, rw nat.cast_zero, rw nat.cast_zero, rw ← floor_add_int, rw ← floor_add_int, rw ← int.cast_coe_nat, rw floor_coe_int, rw floor_coe_int, rw int.add_assoc, rw int.add_assoc, rw floor_eq_iff_eq, rw int.coe_nat_eq_coe_nat_iff, rw nat.mul_comm, rw nat.mul_comm, rw nat.mul_one, rw nat.mul_one, rw int.add_assoc, rw int.add_assoc, rw int.add_eq_zero_iff, rw int.coe_nat_eq_coe_nat_iff, rw nat.add_comm, rw nat.add_comm, rw nat.mul_comm, rw nat.mul_comm, rw nat.mul_one, rw nat.mul_one, rw nat.add_comm, rw nat.add_comm, rw nat.mul_comm, rw nat.mul_comm, rw nat.mul_one, rw nat.mul_one, rw ← int.cast_coe_nat, rw floor_coe_int, rw floor_coe_int, rw int.zero_add, rw int.zero_add, rw int.add_comm, rw int.add_comm, rw int.zero_add, rw int.zero_add, rw int.add_comm, rw int.add_comm, rw int.zero_add, rw int.zero_add, rw int.add_comm, rw int.add_comm, rw int.zero_add, rw int.zero_add, rw int.add_comm, rw int.add_comm, rw int.zero_add, rw int.zero_add, rw int.add_comm, rw int.add_comm, rw int.zero_add, rw int.zero_add, rw int.add_comm, rw int.add_comm, rw int.zero_add, rw int.zero_add, rw int.add_comm, rw int.add_comm, rw int.zero_add, rw int.zero_add, rw int.add_comm, rw int.add_comm, rw int.zero_add, rw int.zero_add, rw int.add_comm, rw int.add_comm, rw ← int.mul_sub_right_distrib, rw ← int.mul_sub_right_distrib, rw ← int.mul_sub_right_distrib_eq_add, rw ← int.mul_sub_right_distrib_eq_add, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, rw int.sub_sub, r
end --Needs more than 2000 tokens!

