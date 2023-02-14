import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j),
  from by auto [int.fract_eq_iff_of_irrational hα_irrat],

  -- Hence, $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$ is an infinite subset of $\left[0,1\right]$.
  have h2 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1,
  from by auto [int.fract_nonneg, int.fract_lt_one],

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$. One can thus find pairs of elements of $S$ that are arbitrarily close. Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
  have h3 : ∃ (x : ℤ), x ∈ set.univ ∧ ∃ (y : ℤ), y ∈ set.univ ∧ int.fract (α * ↑x) ≠ int.fract (α * ↑y) ∧ int.fract (α * ↑x) - int.fract (α * ↑y) < 1,
  from by auto [h1, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.finite_univ, set.
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), 
  from by auto [int.fract_eq_iff, int.fract_mul, hα_irrat, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul, int.fract_eq_iff, int.fract_mul
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), 
  from by auto [int.fract_eq_iff_eq_or_eq_neg_one, int.fract_neg_one_eq_neg_one, int.fract_eq_zero_iff, int.fract_eq_one_iff, int.fract_eq_neg_one_iff, int.fract_eq_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_one, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract_eq_zero_iff_eq_zero, int.fract_eq_zero_iff_eq_one, int.fract_eq_zero_iff_eq_neg_one, int.fract_eq_one_iff_eq_zero, int.fract_eq_neg_one_iff_eq_zero, int.fract_eq_one_iff_eq_one, int.fract_eq_neg_one_iff_eq_neg_one, int.fract
end --Needs more than 2000 tokens!

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
theorem square_of_sum (x y : ℝ) : (x + y)^2 = (x^2 + 2*x*y + y^2) := 
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
Squeeze Theorem for Real Numbers
Let $\sequence {x_n}$, $\sequence {y_n}$ and $\sequence {z_n}$ be sequences in $\R$.

Let $\sequence {y_n}$ and $\sequence {z_n}$ both be convergent to the following limit:
:$\ds \lim_{n \mathop \to \infty} y_n = l, \lim_{n \mathop \to \infty} z_n = l$

Suppose that:
:$\forall n \in \N: y_n \le x_n \le z_n$


Then:
:$x_n \to l$ as $n \to \infty$
that is:
:$\ds \lim_{n \mathop \to \infty} x_n = l$

`proof`
From Negative of Absolute Value:
:$\size {x - l} < \epsilon \iff l - \epsilon < x < l + \epsilon$

Let $\epsilon > 0$.

We need to prove that:
:$\exists N: \forall n > N: \size {x_n - l} < \epsilon$

As $\ds \lim_{n \mathop \to \infty} y_n = l$ we know that:
:$\exists N_1: \forall n > N_1: \size {y_n - l} < \epsilon$

As $\ds \lim_{n \mathop \to \infty} z_n = l$ we know that:
:$\exists N_2: \forall n > N_2: \size {z_n - l} < \epsilon$


Let $N = \max \set {N_1, N_2}$.

Then if $n > N$, it follows that $n > N_1$ and $n > N_2$.

So:
:$\forall n > N: l - \epsilon < y_n < l + \epsilon$
:$\forall n > N: l - \epsilon < z_n < l + \epsilon$

But:
:$\forall n \in \N: y_n \le x_n \le z_n$

So:
:$\forall n > N: l - \epsilon < y_n \le x_n \le z_n < l + \epsilon$

and so:
:$\forall n > N: l - \epsilon < x_n < l + \epsilon$

So:
:$\forall n > N: \size {x_n - l} < \epsilon$

Hence the result.
{{qed}}

-/
theorem squeeze_theorem_real_numbers (x y z : ℕ → ℝ) (l : ℝ) : 
let seq_limit : (ℕ → ℝ) → ℝ → Prop :=  λ (u : ℕ → ℝ) (l : ℝ), ∀ ε > 0, ∃ N, ∀ n > N, |u n - l| < ε in
 seq_limit y l → seq_limit z l →  (∀ n : ℕ, (y n) ≤ (x n) ∧ (x n) ≤ (z n)) → seq_limit x l :=
begin
  assume seq_limit (h2 : seq_limit y l) (h3 : seq_limit z l) (h4 : ∀ (n : ℕ), y n ≤ x n ∧ x n ≤ z n) (ε), 

  --From Negative of Absolute Value: $\size {x - l} < \epsilon \iff l - \epsilon < x < l + \epsilon$
  have h5 : ∀ x, |x - l| < ε ↔ (((l - ε) < x) ∧ (x < (l + ε))), 
  from by auto [abs_sub_lt_iff] using [linarith],
  
  --Let $\epsilon > 0$.
  assume (h7 : ε > 0),

  --As $\ds \lim_{n \mathop \to \infty} y_n = l$ we know that $\exists N_1: \forall n > N_1: \size {y_n - l} < \epsilon$
  cases h2 ε h7 with N1 h8,

  --As $\ds \lim_{n \mathop \to \infty} z_n = l$ we know that $\exists N_2: \forall n > N_2: \size {z_n - l} < \epsilon$
  cases h3 ε h7 with N2 h9,
  
  --Let $N = \max \set {N_1, N_2}$.
  let N := max N1 N2,
  use N,

  --Then if $n > N$, it follows that $n > N_1$ and $n > N_2$.
  have h10 : ∀ n > N, n > N1 ∧ n > N2 := by auto [lt_of_le_of_lt, le_max_left, le_max_right],
  
  --$\forall n > N: l - \epsilon < y_n < l + \epsilon$
  --$\forall n > N: l - \epsilon < z_n < l + \epsilon$
  --$\forall n \in \N: y_n \le x_n \le z_n$
  --So $\forall n > N: l - \epsilon < y_n \le x_n \le z_n < l + \epsilon$
  have h11 : ∀ n > N, (((l - ε) < (y n)) ∧ ((y n) ≤ (x n))) ∧ (((x n) ≤ (z n)) ∧ ((z n) < l+ε)), 
  from by auto [h8, h10, h5, h9],

  --$\forall n > N: l - \epsilon < x_n < l + \epsilon$
  have h15 : ∀ n > N, ((l - ε) < (x n)) ∧ ((x n) < (l+ε)), 
  from by auto [h11] using [linarith],

  --So $\forall n > N: \size {x_n - l} < \epsilon$
  --Hence the result
  show  ∀ (n : ℕ), n > N → |x n - l| < ε, 
  from by auto [h5, h15], 

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
theorem  irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
FEW SHOT PROMPTS TO CODEX(END)-/
