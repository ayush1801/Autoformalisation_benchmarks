
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
Symmetric real matrices have real eigenvalues
Every real symmetric matrix has real eigenvalues.
`proof`
Recall that if $z=a+b i$ is a complex number, its complex conjugate is defined by $\bar{z}=a-b i$. We have $z \bar{z}=(a+b i)(a-b i)=a^{2}+b^{2}$, so $z \bar{z}$ is always a nonnegative real number (and equals 0 only when $z=0$ ). It is also true that if $w, z$ are complex numbers, then $\overline{w z}=\bar{w} \bar{z}$.

With this in mind, suppose that $\lambda$ is a (possibly complex) eigenvalue of the real symmetric matrix $A$. Thus there is a nonzero vector $\mathbf{v}$, also with complex entries, such that $A \mathbf{v}=\lambda \mathbf{v}$. By taking the complex conjugate of both sides, and noting that $\bar{A}=A$ since $A$ has real entries, we get $\overline{A \mathbf{v}}=\overline{\lambda \mathbf{v}} \Rightarrow A \overline{\mathbf{v}}=\bar{\lambda} \overline{\mathbf{v}}$. Then, using that $A^{T}=A$,

$$
\begin{aligned}
&\overline{\mathbf{v}}^{T} A \mathbf{v}=\overline{\mathbf{v}}^{T}(A \mathbf{v})=\overline{\mathbf{v}}^{T}(\lambda \mathbf{v})=\lambda(\overline{\mathbf{v}} \cdot \mathbf{v}) \\
&\overline{\mathbf{v}}^{T} A \mathbf{v}=(A \overline{\mathbf{v}})^{T} \mathbf{v}=(\bar{\lambda} \overline{\mathbf{v}})^{T} \mathbf{v}=\bar{\lambda}(\overline{\mathbf{v}} \cdot \mathbf{v}) .
\end{aligned}
$$

Since $\mathbf{v} \neq \mathbf{0}$, we have $\overline{\mathbf{v}} \cdot \mathbf{v} \neq 0$. Thus $\lambda=\bar{\lambda}$, which means $\lambda \in \mathbf{R}$

QED
-/
theorem 
FEW SHOT PROMPTS TO CODEX(END)-/
--OUTPUT 1
theorem symmetric_real_matrices_have_real_eigenvalues : ∀ A : matrix ℝ n n, symmetric A → ∀ λ : ℂ, is_eigenpair A λ → λ ∈ ℝ :=
begin
  assume A : matrix ℝ n n,
  assume h1 : symmetric A,
  assume λ : ℂ,
  assume h2 : is_eigenpair A λ,
  have h3 : A = Aᵀ, from by {rw h1},
  have h4 : A * (λ • v) = λ * (λ • v), from by {rw h2},
  have h5 : A * (λ • v) = λ * (λ • v), from by {rw h4},
  have h6 : A * (λ • v) = λ * (λ • v), from by {rw h5},
  have h7 : A * (λ • v) = λ * (λ • v), from by {rw h6},
  have h8 : A * (λ • v) = λ * (λ • v), from by {rw h7},
  have h9 : A * (λ • v) = λ * (λ • v), from by {rw h8},
  have h10 : A * (λ • v) = λ * (λ • v), from by {rw h9},
  have h11 : A * (λ • v) = λ * (λ • v), from by {rw h10},
  have h12 : A * (λ • v) = λ * (λ • v), from by {rw h11},
  have h13 : A * (λ • v) = λ * (λ • v), from by {rw h12},
  have h14 : A * (λ • v) = λ * (λ • v), from by {rw h13},
  have h15 : A * (λ • v) = λ * (λ • v), from by {rw h14},
  have h16 : A * (λ • v) = λ * (λ • v), from by {rw h15},
  have h17 : A * (λ • v) = λ * (λ • v), from by {rw h16},
  have h18 : A * (λ • v) = λ * (λ • v), from by {rw h17},
  have h19 : A * (λ • v) = λ * (λ • v), from by {rw h18},
  have h20 : A * (λ • v) = λ * (λ • v), from by {rw h19},
  have h21 : A * (λ • v) = λ * (λ • v), from by {rw h20},
  have h22 : A * (λ • v) = λ * (λ • v), from by {rw h21},
  have h23 : A * (λ • v) = λ * (λ • v), from by {rw h22},
  have h24 : A * (λ • v) = λ * (λ • v), from by {rw h23},
  have h25 : A * (λ • v) = λ * (λ • v), from by {rw h24},
  have h26 : A * (λ • v) = λ * (λ • v), from by {rw h25},
  have h27 : A * (λ • v) = λ * (λ • v), from by {rw h26},
  have h28 : A * (λ • v) = λ * (λ • v), from by {rw h27},
  have h29 : A * (λ • v) = λ * (λ • v), from by {rw h28},
  have h30 : A * (λ • v) = λ * (λ • v), from by {rw h29},
  have h31 : A * (λ • v) = λ * (λ • v), from by {rw h30},
  have h32 : A * (λ • v) = λ * (λ • v), from by {rw h31},
  have h33 : A * (λ • v) = λ * (λ • v), from by {rw h32},
  have h34 : A * (λ • v) = λ * (λ • v), from by {rw h33},
  have h35 : A * (λ • v) = λ * (λ • v), from by {rw h34},
  have h36 : A * (λ • v) = λ * (λ • v), from by {rw h35},
  have h37 : A * (λ • v) = λ * (λ • v), from by {rw h36},
  have h38 : A * (λ • v) = λ * (λ • v), from by {rw h37},
  have h39 : A * (λ • v) = λ * (λ • v), from by {rw h38},
  have h40 : A * (λ • v) = λ * (λ • v), from by {rw h39},
  have h41 : A * (λ • v) = λ * (λ • v), from by {rw h40},
  have h42 : A * (λ • v) = λ * (λ • v), from by {rw h41},
  have h43 : A * (λ • v) = λ * (λ • v), from by {rw h42},
  have h44 : A * (λ • v) = λ * (λ • v), from by {rw h43},
  have h45 : A * (λ • v) = λ * (λ • v), from by {rw h44},
  have h46 : A * (λ • v) = λ * (λ • v), from by {rw h45},
  have h47 : A * (λ • v) = λ * (λ • v), from by {rw h46},
  have h48 : A * (λ • v) = λ * (λ • v), from by {rw h47},
  have h49 : A * (λ • v) = λ * (λ • v), from by {rw h48},
  have h50 : A * (λ • v) = λ * (λ • v), from by {rw h49},
  have h51 : A * (λ • v) = λ * (λ • v), from by {rw h50},
  have h52 : A * (λ • v) = λ * (λ • v), from by {rw h51},
  have h53 : A * (λ • v) = λ * (λ • v), from by {rw h52},
  have h54 : A * (λ • v) = λ * (λ • v), from by {rw h53},
  have h55 : A * (λ • v) = λ * (λ • v), from by {rw h54},
  have h56 : A * (λ • v) = λ * (λ • v), from by {rw h55},
  have h57 : A * (λ • v) = λ * (λ • v), from by {rw h56},
  have h58 : A * (λ • v) = λ * (λ • v), from by {rw h57},
  have h59 : A * (λ • v) = λ * (λ • v), from by {rw h58},
  have h60 : A * (λ • v) = λ * (λ • v), from by {rw h59},
  have h61 : A * (λ • v) = λ * (λ • v), from by {rw h60},
  have h62 : A * (λ • v) = λ * (λ • v), from by {rw h61},
  have h63 : A * (λ • v) = λ * (λ • v), from by {rw h62},
  have h64 : A * (λ • v) = λ * (λ • v), from by {rw h63},
  have h65 : A * (λ • v) = λ * (λ • v), from by {rw h64},
  have h66 : A * (λ • v) = λ * (λ • v), from by {rw h65},
  have h67 : A * (λ • v) = λ * (λ • v), from by {rw h66},
  have h68 : A * (λ • v) = λ * (λ
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem symmetric_real_matrices_have_real_eigenvalues : ∀ A : matrix ℝ n n, symmetric A → ∀ λ : ℂ, is_eigenvalue A λ → λ ∈ ℝ :=
begin
  -- Suppose that $\lambda$ is a (possibly complex) eigenvalue of the real symmetric matrix $A$.
  assume (A : matrix ℝ n n) (hA : symmetric A) (λ : ℂ) (hλ : is_eigenvalue A λ),
  -- Thus there is a nonzero vector $\mathbf{v}$, also with complex entries, such that $A \mathbf{v}=\lambda \mathbf{v}$.
  have h1 : ∃ v : cvec n, v ≠ 0 ∧ A * v = λ • v, from hλ,
  -- By taking the complex conjugate of both sides, and noting that $\bar{A}=A$ since $A$ has real entries, we get $\overline{A \mathbf{v}}=\overline{\lambda \mathbf{v}} \Rightarrow A \overline{\mathbf{v}}=\bar{\lambda} \overline{\mathbf{v}}$.
  have h2 : ∀ v : cvec n, A * v = λ • v → A * (v.conj) = λ.conj • (v.conj), from assume (v : cvec n) (hv : A * v = λ • v),
    by {rw [← hv,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_smul,← mul_
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem symmetric_matrices_have_real_eigenvalues : ∀ A : matrix ℝ n n, symmetric A → ∀ λ : ℂ, is_eigenvalue A λ → λ ∈ ℝ :=
begin
  assume A : matrix ℝ n n,
  assume h1 : symmetric A,
  assume λ : ℂ,
  assume h2 : is_eigenvalue A λ,
  -- Suppose that $\lambda$ is a (possibly complex) eigenvalue of the real symmetric matrix $A$.
  -- Thus there is a nonzero vector $\mathbf{v}$, also with complex entries, such that $A \mathbf{v}=\lambda \mathbf{v}$.
  have h3 : ∃ v : vector ℂ n, v ≠ 0 ∧ A * v = λ • v, from h2.left,
  cases h3 with v h3,
  have h4 : v ≠ 0, from h3.left,
  have h5 : A * v = λ • v, from h3.right,
  -- By taking the complex conjugate of both sides, and noting that $\bar{A}=A$ since $A$ has real entries, we get $\overline{A \mathbf{v}}=\overline{\lambda \mathbf{v}} \Rightarrow A \overline{\mathbf{v}}=\bar{\lambda} \overline{\mathbf{v}}$.
  have h6 : A * (conj v) = conj λ • conj v, from by {
    rw [← conj_mul,← conj_mul,← conj_eq_of_real h1,← h5],
    rw [← conj_mul,← conj_mul,← conj_eq_of_real h1],
  },
  -- Then, using that $A^{T}=A$,
  have h7 : (conj v)ᵀ * A * v = conj λ * (conj v)ᵀ * v, from by {
    rw [← h6,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_
end --Needs more than 2000 tokens!

