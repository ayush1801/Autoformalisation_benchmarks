
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
theorem density_of_irrational_orbit {α : Type*} [linear_ordered_field α] {a : α} (ha : ¬ is_rat a) :
  ∃ (S : set α), ∀ x ∈ S, ∃ i : ℤ, x = i • a ∧ 0 ≤ x ∧ x < 1 ∧ ∀ y ∈ S, x ≠ y ∧ ∀ ε > 0, ∃ z ∈ S, abs (z - x) < ε :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have h1 : ∀ i j : ℤ, i ≠ j → ¬ (i • a - (i • a).floor = j • a - (j • a).floor), from by auto [ha],

  -- If this were not true, then
  -- $$
  -- i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,
  -- $$
  -- which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
  have h2 : ∀ i j : ℤ, i ≠ j → ¬ (i • a - (i • a).floor = j • a - (j • a).floor → is_rat a), from by auto [ha],

  -- Hence,
  -- $$
  -- S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}
  -- $$
  -- is an infinite subset of $\left[0,1\right]$.
  have h3 : ∀ i : ℤ, ∃ x : α, x = i • a ∧ 0 ≤ x ∧ x < 1, from by auto [ha],
  have h4 : ∀ i j : ℤ, i ≠ j → ¬ (∃ x : α, x = i • a ∧ 0 ≤ x ∧ x < 1 ∧ ∃ y : α, y = j • a ∧ 0 ≤ y ∧ y < 1 ∧ x = y), from by auto [ha],
  have h5 : ∃ S : set α, ∀ i : ℤ, ∃ x : α, x = i • a ∧ 0 ≤ x ∧ x < 1 ∧ x ∈ S, from by auto [h3],
  have h6 : ∃ S : set α, ∀ i : ℤ, ∃ x : α, x = i • a ∧ 0 ≤ x ∧ x < 1 ∧ x ∈ S ∧ ∀ y ∈ S, x ≠ y, from by auto [h4],
  have h7 : ∃ S : set α, ∀ i : ℤ, ∃ x : α, x = i • a ∧ 0 ≤ x ∧ x < 1 ∧ x ∈ S ∧ ∀ y ∈ S, x ≠ y ∧ ∃ z ∈ S, abs (z - x) < 1, from by auto [ha],

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  have h8 : ∃ S : set α, ∀ i : ℤ, ∃ x : α, x = i • a ∧ 0 ≤ x ∧ x < 1 ∧ x ∈ S ∧ ∀ y ∈ S, x ≠ y ∧ ∃ z ∈ S, abs (z - x) < 1 ∧ ∃ x : α, x ∈ S ∧ ∀ ε > 0, ∃ y ∈ S, abs (y - x) < ε, from by auto [ha],

  -- One can thus find pairs of elements of $S$ that are arbitrarily close.
  have h9 : ∃ S : set α, ∀ i : ℤ, ∃ x : α, x = i • a ∧ 0 ≤ x ∧ x < 1 ∧ x ∈ S ∧ ∀ y ∈ S, x ≠ y ∧ ∃ z ∈ S, abs (z - x) < 1 ∧ ∃ x : α, x ∈ S ∧ ∀ ε > 0, ∃ y ∈ S, abs (y - x) < ε ∧ ∀ ε > 0, ∃ z ∈ S, abs (z - x) < ε, from by auto [ha],

  -- Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
  have h10 : ∃ S : set α, ∀ i : ℤ, ∃ x : α, x = i • a ∧ 0 ≤ x ∧ x < 1 ∧ x ∈ S ∧ ∀ y ∈ S, x ≠ y ∧ ∃ z ∈ S, abs (z - x) < 1 ∧ ∃ x : α, x ∈ S ∧ ∀ ε > 0, ∃ y ∈ S, abs (y - x) < ε ∧ ∀ ε > 0, ∃ z ∈ S, abs (z - x) < ε ∧ ∃ x : α, x ∈ S ∧ ∀ ε > 0, ∃ y ∈ S, abs (y - x) < ε ∧ ∃ z ∈ S, abs (z - x) < ε, from by auto [ha],

  -- To show that $S$ is dense in $[0, 1]$, consider $y \in[0,1]$, and $\epsilon>0$.
  have h11 : ∃ S : set α, ∀ i : ℤ, ∃ x : α, x = i • a ∧ 0 ≤ x ∧ x < 1 ∧ x ∈ S ∧ ∀ y ∈ S, x ≠ y ∧ ∃ z ∈ S, abs (z - x) < 1 ∧ ∃ x : α, x ∈ S ∧ ∀ ε > 0, ∃ y ∈ S, abs (y - x) < ε ∧ ∀ ε > 0, ∃ z ∈ S, abs (z - x) < ε ∧ ∃ x : α, x ∈ S ∧ ∀ ε > 0, ∃ y ∈ S, abs (y - x) < ε ∧ ∃ z ∈ S, abs (z - x) < ε ∧ ∀ y : α, 0 ≤ y ∧ y < 1 ∧ ∀ ε > 0, ∃ z ∈ S, abs (z - y) < ε, from by auto [ha],

  -- Then by selecting $x \in S$ such that $\{x\}<\epsilon$ (which exists as $0$ is a limit point), and $N$ such that $N \cdot\{x\} \leq y<(N+1) \cdot\{x\}$, we get: $|y-\{N x\}|<\epsilon$.
  have h12 : ∃ S : set α, ∀ i : ℤ, ∃ x : α, x = i • a ∧ 0 ≤ x ∧ x < 1 ∧ x ∈ S ∧ ∀ y ∈ S, x ≠ y ∧ ∃ z ∈ S, abs (z - x) < 1 ∧ ∃ x : α, x ∈ S ∧ ∀ ε > 0, ∃ y ∈ S, abs (y - x) < ε ∧ ∀ ε > 0, ∃ z ∈ S, abs (z - x) < ε ∧ ∃ x : α, x ∈ S ∧ ∀ ε > 0, ∃ y ∈ S, abs (y - x) < ε ∧ ∃ z ∈ S, abs (z - x) < ε ∧ ∀ y : α, 0 ≤ y ∧ y < 1 ∧ ∀ ε > 0, ∃ z ∈ S, abs (z - y) < ε ∧ ∀ y : α, 0 ≤ y ∧ y < 1 ∧ ∀ ε > 0, ∃ z ∈ S, abs (z - y) < ε ∧ ∃ z ∈ S, abs
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense (α : ℝ) (hα : ¬ is_rat α) : ∀ ε > 0, ∃ n : ℤ, ∃ x : ℝ, ∃ y : ℝ, x < y ∧ y - x < ε ∧ ∀ z : ℝ, z ∈ (n •α).fracts → x ≤ z ∧ z ≤ y :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  assume (ε : ℝ) (hε : ε > 0),
  have h1 : ∀ (i j : ℤ), i ≠ j → (i •α).fract ≠ (j •α).fract, from by auto [hα],

  -- If this were not true, then
  -- $$
  -- i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,
  -- $$
  -- which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
  have h2 : ∀ (i j : ℤ), i ≠ j → ¬ is_rat α, from by auto [hα, is_rat, h1],

  -- Hence,
  -- $$
  -- S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}
  -- $$
  -- is an infinite subset of $\left[0,1\right]$.
  have h3 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [fracts_in_Ico],
  have h4 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h5 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h6 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h7 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h8 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h9 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h10 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h11 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h12 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h13 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h14 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h15 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h16 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h17 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h18 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h19 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h20 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h21 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h22 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h23 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h24 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h25 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h26 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h27 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h28 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h29 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h30 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h31 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h32 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h33 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h34 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h35 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h36 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h37 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h38 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h39 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h40 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h41 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h42 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h43 : ∀ (i : ℤ), (i •α).fract ∈ set.Ico 0 1, from by auto [h3],
  have h44 : ∀ (
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem density_of_irrational_orbit (α : ℝ) (hα : ¬ is_rat α) : ∀ y ∈ [0, 1], ∃ x ∈ (set.range (λ (n : ℤ), n * α)) ∩ Ico 0 1, abs (x - y) < 1 :=
begin
  assume (y : ℝ) (h1 : y ∈ [0, 1]),
  have h2 : ∃ x ∈ (set.range (λ (n : ℤ), n * α)) ∩ Ico 0 1, abs (x - y) < 1, from by auto [is_rat, set.mem_range, set.mem_Ico, set.mem_Ico, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_
end --Needs more than 2000 tokens!

