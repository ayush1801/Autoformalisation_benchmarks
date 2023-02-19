
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
theorem irrational_orbit_dense (α : ℝ) (hα : α ≠ 0): ∀x ∈ set.Ico 0 1, ∃y ∈ set.Ico 0 1, (∃i ∈ ℤ, y = i * α + x) :=
begin
  assume a h,
  use [a, 1, 0],
  exact and.intro (and.intro (hα.symm ▸ h) (by norm_num))
  (by norm_num),
end

--OUTPUT 2
theorem density_of_irrational_orbit {α : Type*} [linear_ordered_field α] (α_irr : ∀ q : α, q ∈ ℚ → q ≠ α) (α_pos : 0 < α) : ∀ ε > 0, ∃ ɛ ∈ { i | 0 < i ∧ i ≤ ε } ∩ 𝒫 (ℤ), ∀ a ∈ ℤ, abs (a * α - a * ɛ / ε) < ε :=
begin
  assume (ε : α) (hη : ε > 0),
  have h1 : ∃! x : ℤ, (∃!) (n : ℤ) (h : n * α - n * x / ε ∈ ℤ), from by auto [ℤ.div_mod_unique],
  let S : set ℤ := { x : ℤ | ∃! n : ℤ, n * α - n * x / ε ∈ ℤ },
  have h2 : S ≠ ∅, from by auto [h1, exists_mem_of_ne_empty],
  have h3 : ∃ x : ℤ, ∀ B : set ℤ, x ∈ B ∧ is_bounded_above B → S ⊆ B, from by auto [h2, zorn.zorn],

  let t := classical.some h3,
  have h4 : t ∈ S, from by auto [classical.some_spec, h3],

  let t_0 : ℤ := classical.some (h4).right,
  have h5 : t_0 * α - t_0 * t / ε ∈ ℤ, from by auto [classical.some_spec, h4],

  have h6 : ∃! a : ℤ, (∃! b : ℤ, { a * α - a * b / ε } ⊆ { 0 }), from by auto [exists_mem_of_ne_empty, h1, set.subset.refl],
  let t_1 := classical.some h6,
  have h7 : { t_1 * α - t_1 * t / ε } ⊆ { 0 }, from by auto [classical.some_spec, h6],
  have h8 : t_1 * α - t_1 * t / ε ∈ { 0 }, from by auto [classical.sub_in_sub_set_of_subset],

  have h9 : t_1 * α - t_1 * t / ε ≥ 0, from by auto [h8, set.mem_singleton_iff],
  have h10 : ∀ b ∈ ℤ, (b : α) * α - b * t / ε ≥ 0, from by auto [h9, sub_ge_iff_le_add],
  have h11 : t_1 * α - t_1 * t / ε ≤ ε, from by auto [h10, le_max_iff_le_right],
  have h12 : ∀ a ∈ ℤ, a * α - a * t / ε ≤ ε, from by auto [h11, sub_le_iff_le_add],
  have h13 : ∀ a ∈ ℤ, abs (a * α - a * t / ε) ≤ ε, from by auto [abs_le, h12],
  have h14 : ∀ a ∈ ℤ, abs (a * α - a * t / ε) ∈ { b | 0 < b ∧ b ≤ ε }, from by auto [h13],
  have h15 : ∀ a ∈ ℤ, abs (a * α - a * t / ε) ∈ 𝒫 (ℤ), from by auto [h14, set.mem_powerset],
  have h16 : ∀ a ∈ ℤ, abs (a * α - a * t / ε) ∈ { i | 0 < i ∧ i ≤ ε } ∩ 𝒫 (ℤ), from by auto [h14, h15],
  show ∃ ɛ ∈ { i | 0 < i ∧ i ≤ ε } ∩ 𝒫 (ℤ), ∀ a ∈ ℤ, abs (a * α - a * ɛ / ε) < ε, from by auto [h13, h14] using [use t / ε],
end

--OUTPUT 3
theorem orbit_irrational_dense (α : ℝ) [irrat α] : ∀ ε > 0, ∃ N : ℤ, ∀ m n : ℤ, n > N → m < n → (abs (α*m - α*n)) < ε :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
  assume (ε : ℝ) (hε : ε > 0),
  have h1 : ∀ i j : ℤ, (i ≠ j) → (frac (α*i) ≠ frac (α*j)), from by auto [irrat],

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$. One can thus find pairs of elements of $S$ that are arbitrarily close. 
  have h2 : ∃ z : ℚ, ∀ x : ℕ, ∃ y : ℕ, (z - (1/(y : ℝ))) < (1/(x : ℝ)), from by auto using [rat.exists_rat_btwn_pos],

  -- Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
  have h3 : ∀ x y : ℤ, (frac (α*x) - frac (α*y)) ∈ frac '' (α '' set.range (x-y)), from by auto [mul_comm, mul, mul_comm, mul, sub_mul, irrat, frac_mul_inv],

  -- To show that $S$ is dense in $[0, 1]$, consider $y \in[0,1]$, and $\epsilon>0$. Then by selecting $x \in S$ such that $\{x\}<\epsilon$ (which exists as $0$ is a limit point), and $N$ such that $N \cdot\{x\} \leq y<(N+1) \cdot\{x\}$, we get: $|y-\{N x\}|<\epsilon$.
  have h4 : ∀ y : ℤ, ∃ N : ℤ, ∀ i : ℤ, (i ≤ N) → y < (i+1), from by auto [floor_le],
  have h5 : ∀ y : ℤ, ∃ N : ℤ, ∀ i : ℤ, (i ≥ N) → (i+1) < y, from by auto [floor_lt_iff],

  -- consider $y \in[0,1]$, and $\epsilon>0$. 
  have h6 : ∀ (ε : ℝ) (hε : ε > 0) (y : ℤ), ∃ N : ℤ, ∀ m : ℤ, (m ≤ N) → y < (m+1) ∧ ∃ x : ℤ, ∃ n : ℚ, ((y - (1/(n : ℝ))) < (x/(m+1))),
  begin
    -- let $y' : ℚ$ be such that $y ≤ y' < y+(1/(N : ℝ))$
    assume ε hε y,
    have h2 : ∃ z : ℚ, ∀ x : ℕ, ∃ y : ℕ, (z - (1/(y : ℝ))) < (1/(x : ℝ)), from by auto using [rat.exists_rat_btwn_pos],
    have h3 : ∃ N : ℕ, ∃ x : ℕ, (y - (1/(x : ℝ))) < (1/(N : ℝ)), from by auto using [h2, classical.some_spec],
    -- choose $N$ to be the smallest integer such that $1/(N : ℝ) < ε$
    have h4 : ∃ N : ℕ, ε < (1/(N : ℝ)), from by auto using [rat.exists_rat_lt],
    have h5 : ∃ N : ℕ, 1/(N : ℝ) < ε, from by auto using [rat.one_div_pos_of_pos],
    have h6 : ∀ N : ℕ, (1/(N : ℝ)) < ε → N ≤ nat_abs (((N : ℝ))*ε), from by auto [one_div_le_one_div_iff, mul_le_mul_of_nonneg_left, nat_abs_nonneg],
    have h7 : ∃ Nx : ℕ, (y - (1/(Nx : ℝ))) < (1/(nat_abs (((Nx : ℝ))*ε))), from by auto [nat.find_min, h3, h5, h6],
    have h8 : (y - (1/(nat_abs (((Nx (1/(nat_abs (((Nx : ℝ))*ε)) : ℕ) : ℝ))) : ℝ))) < (1/(nat_abs (((Nx : ℝ))*ε))), from by auto using [h7, nat.find_min_eq],

    -- let $N : ℤ$ be the smallest integer such that $y < N$
    have h9 : ∃ N : ℤ, y < N, from by auto using [h4],
    have h10 : ∀ N : ℤ, (y < N) → ((nat_abs (((N : ℝ))*ε)) ≤ N), from by auto using [rat.one_div_pos_of_pos, one_div_le_one_div_iff, mul_le_mul_of_nonneg_left, nat_abs_nonneg],
    have h11 : ∃ N : ℤ, (y < N) ∧ ((nat_abs (((N : ℝ))*ε)) ≤ N), from by auto [nat.find_min, h9, h10],

    show ∃ N : ℤ, ∀ m : ℤ, (m ≤ N) → y < (m+1) ∧ ∃ x : ℤ, ∃ n : ℚ, ((y - (1/(n : ℝ))) < (x/(m+1))), from by auto [nat.find_min_eq, h11, h8],
  end,

  show ∃ N : ℤ, ∀ m n : ℤ, n > N → m < n → (abs (α*m - α*n)) < ε, from by auto [h6, h1],
end

