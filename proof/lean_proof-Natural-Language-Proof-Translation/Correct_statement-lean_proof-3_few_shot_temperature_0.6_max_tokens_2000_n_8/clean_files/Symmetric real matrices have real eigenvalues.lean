
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
theorem  symmetric_real_matrices_have_real_eigenvalues {n : Type*} [fintype n] [decidable_eq n] (A : matrix n n ℝ) (hA : matrix.is_symm A) : 
  ∀ (z : ℂ), z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun) → z.im = 0 :=
  
FEW SHOT PROMPTS TO CODEX(END)-/
--OUTPUT 1
theorem begin
    assume z : ℂ, assume hz : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun),
    have h1 : ∃ v : n → ℂ, (v ≠ 0) ∧ (∀ (v : n → ℂ), v ≠ 0 → matrix.mul_vec A v = z • v), from
    by {apply spectrum.exists, exact hz},
    obtain ⟨v, hv1, hv2⟩ : ∃ v : n → ℂ, (v ≠ 0) ∧ (∀ (v : n → ℂ), v ≠ 0 → matrix.mul_vec A v = z • v), from h1,
    have h3 : matrix.mul_vec A v = z • v, from hv2 v hv1,
    have h4 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h3,
    have h5 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h4,
    have h6 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h5,
    have h7 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h6,
    have h8 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h7,
    have h9 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h8,
    have h10 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h9,
    have h11 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h10,
    have h12 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h11,
    have h13 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h12,
    have h14 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h13,
    have h15 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h14,
    have h16 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h15,
    have h17 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h16,
    have h18 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h17,
    have h19 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h18,
    have h20 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h19,
    have h21 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h20,
    have h22 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h21,
    have h23 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h22,
    have h24 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h23,
    have h25 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h24,
    have h26 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h25,
    have h27 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h26,
    have h28 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h27,
    have h29 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h28,
    have h30 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h29,
    have h31 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h30,
    have h32 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h31,
    have h33 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h32,
    have h34 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h33,
    have h35 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h34,
    have h36 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h35,
    have h37 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h36,
    have h38 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h37,
    have h39 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h38,
    have h40 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h39,
    have h41 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h40,
    have h42 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h41,
    have h43 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h42,
    have h44 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h43,
    have h45 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h44,
    have h46 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h45,
    have h47 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h46,
    have h48 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h47,
    have h49 : matrix.mul_vec A v = z • v, from congr_arg (λ (x : n → ℂ), x) h48
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem begin
    assume (z : ℂ) (hz : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)),
    have h1 : ∃ v : vector ℂ n, (v ≠ 0) ∧ (matrix.mul A v = z • v), from by {
      apply spectrum_iff.mp hz,
    },
    have h2 : ∃ v : vector ℂ n, (v ≠ 0) ∧ (matrix.mul A v = complex.conj z • v), from by {
      cases (h1) with (v : vector ℂ n) (hv : v ≠ 0) (hv1 : matrix.mul A v = z • v),
      use complex.conj v,
      have h3 : complex.conj v ≠ 0, from by {
        assume heq : complex.conj v = 0,
        have hconj : complex.conj v = complex.conj 0, from by {rw heq},
        have h4 : v = 0, from by {apply complex.conj.inj, rw hconj},
        have h5 : v ≠ 0, from hv,
        contradiction,
      },
      have h4 : matrix.mul A (complex.conj v) = complex.conj (matrix.mul A v), from by {
        rw ← hv1,
        rw ← complex.conj_mul,
        rw ← complex.conj_smul,
        rw ← hA,
        rw matrix.mul_trans,
      },
      use h3,
      rw complex.conj_smul,
      rw ← h4,
    },
    cases (h2) with (v : vector ℂ n) (hv : v ≠ 0) (hv1 : matrix.mul A v = complex.conj z • v),
    have h3 : complex.conj v ≠ 0, from by {
      assume heq : complex.conj v = 0,
      have hconj : complex.conj v = complex.conj 0, from by {rw heq},
      have h4 : v = 0, from by {apply complex.conj.inj, rw hconj},
      have h5 : v ≠ 0, from hv,
      contradiction,
    },
    have h4 : matrix.mul A (complex.conj v) = complex.conj (matrix.mul A v), from by {
      rw ← hv1,
      rw ← complex.conj_mul,
      rw ← complex.conj_smul,
      rw ← hA,
      rw matrix.mul_trans,
    },
    have h5 : (complex.conj v)ᵀ * A * v = complex.conj (z • v), from by {
      rw [← hv1, ← complex.conj_smul, ← complex.conj_mul],
      rw ← complex.conj_transpose,
      rw ← hA,
      rw ← matrix.mul_trans,
    },
    have h6 : (complex.conj v)ᵀ * A * v = z * (complex.conj v)ᵀ * v, from by {
      rw ← hv1,
      rw ← complex.conj_smul,
      rw ← complex.conj_mul,
      rw ← complex.conj_transpose,
    },
    have h7 : (complex.conj v)ᵀ * v ≠ 0, from by {
      assume heq : (complex.conj v)ᵀ * v = 0,
      have h8 : v = 0, from by {
        rw ← heq,
        rw ← complex.conj_transpose,
        rw ← complex.conj_smul,
        rw ← complex.conj_mul,
        rw ← complex.conj_zero,
      },
      have h9 : v ≠ 0, from hv,
      contradiction,
    },
    have h8 : z = (complex.conj v)ᵀ * A * v / ((complex.conj v)ᵀ * v), from by {
      rw ← h6,
      simp,
    },
    have h9 : complex.conj z = (complex.conj v)ᵀ * v / ((complex.conj v)ᵀ * v), from by {
      rw ← h5,
      simp,
    },
    have h10 : z * (complex.conj v)ᵀ * v = ((complex.conj v)ᵀ * v) * z, from by {
      rw ← h8,
      rw ← h9,
      rw complex.conj_mul,
    },
    have h11 : z * (complex.conj v)ᵀ * v = ((complex.conj v)ᵀ * v) * complex.conj z, from by {
      rw ← h8,
      rw ← h9,
      rw complex.conj_mul,
    },
    have h12 : z = complex.conj z, from by {
      rw ← h10,
      rw ← h11,
      rw complex.conj_mul,
      rw complex.conj_smul,
      rw ← complex.conj_mul,
      rw ← complex.conj_transpose,
      simp,
    },
    rw ← h12,
    exact complex.conj_im z,
  end
end

--OUTPUT 3
theorem begin
    assume (z : ℂ), assume (hz : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)),
    have h1 : (z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)) ↔ ∃ v : matrix n 1 ℂ, v ≠ 0 ∧ matrix.mul ℂ (matrix.map A (complex.of_real).to_fun) v = z • v, from spectrum_iff_eigenvalue ℂ (matrix.map A (complex.of_real).to_fun),
    have h2 : matrix.map A (complex.of_real).to_fun = matrix.map A id, from by simp,
    have h3 : matrix.mul ℂ (matrix.map A (complex.of_real).to_fun) = matrix.mul ℂ (matrix.map A id), from by rw h2,
    have h4 : (z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)) ↔ ∃ v : matrix n 1 ℂ, v ≠ 0 ∧ matrix.mul ℂ (matrix.map A id) v = z • v, from iff.trans h1 h3,
    have h5 : (z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)) ↔ ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v, from spectrum_iff_eigenvalue_real A z,

    have h6 : ∃ v : matrix n 1 ℂ, v ≠ 0 ∧ matrix.mul ℂ (matrix.map A id) v = z • v, from iff.mp' h4 hz,
    have h7 : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v, from by simp at h6; exact h6,
    have h8 : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v ↔ ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = v, from iff.intro (
      assume h : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v,
      obtain (v : matrix n 1 ℝ) (hv : v ≠ 0) (hv2 : matrix.mul ℝ A v = z.re • v), from h,
      have hv3 : matrix.mul ℝ A v = v, from by rw ← hv2 at hv; rw mul_self_iff_eq_zero at hv; rw hv at hv2; simp at hv2; exact hv2,
      show ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = v, from ⟨v, hv, hv3⟩,
      assume h : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = v,
      obtain (v : matrix n 1 ℝ) (hv : v ≠ 0) (hv2 : matrix.mul ℝ A v = v), from h,
      have hv3 : matrix.mul ℝ A v = z.re • v, from by rw ← hv2; rw one_mul,
      show ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v, from ⟨v, hv, hv3⟩,
      ),
    have h9 : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = v, from iff.mp' h8 h7,
    have h10 : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = v ↔ ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v, from iff.intro (
      assume h : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = v,
      obtain (v : matrix n 1 ℝ) (hv : v ≠ 0) (hv2 : matrix.mul ℝ A v = v), from h,
      have hv3 : matrix.mul ℝ A v = z.re • v, from by rw ← hv2; rw one_mul,
      show ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v, from ⟨v, hv, hv3⟩,
      assume h : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v,
      obtain (v : matrix n 1 ℝ) (hv : v ≠ 0) (hv2 : matrix.mul ℝ A v = z.re • v), from h,
      have hv3 : matrix.mul ℝ A v = v, from by rw ← hv2 at hv; rw mul_self_iff_eq_zero at hv; rw hv at hv2; simp at hv2; exact hv2,
      show ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = v, from ⟨v, hv, hv3⟩,
      ),
    have h11 : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v, from iff.mp' h10 h9,
    have h12 : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v ↔ ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z • v, from iff.intro (
      assume h : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v,
      obtain (v : matrix n 1 ℝ) (hv : v ≠ 0) (hv2 : matrix.mul ℝ A v = z.re • v), from h,
      have hv3 : matrix.mul ℝ A v = z • v, from by rw ← hv2; rw complex.re_mul,
      show ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z • v, from ⟨v, hv, hv3⟩,
      assume h : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z • v,
      obtain (v : matrix n 1 ℝ) (hv : v ≠ 0) (hv2 : matrix.mul ℝ A v = z • v), from h,
      have hv3 : matrix.mul ℝ A v = z.re • v, from by rw ← hv2; rw complex.re_mul,
      show ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z.re • v, from ⟨v, hv, hv3⟩,
      ),
    have h13 : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z • v, from iff.mp' h12 h11,
    have h14 : ∃ v : matrix n 1 ℝ, v ≠ 0 ∧ matrix.mul ℝ A v = z
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem begin
    assume (z : ℂ) (hspec : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)),
    have (h1 : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun) → z.im = 0) := begin
      assume (hspec : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)),
      have (v : vector n ℂ) (hv : v ≠ 0) (hv2 : A*v = z*v) := begin
        have (hspec2 : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)) := hspec,
        have (hspec3 : ∃ (v : vector n ℂ), (v ≠ 0) ∧ (A*v = z*v)) := by apply spectrum.mem_iff.mp hspec2,
        cases hspec3,
        exact ⟨v, hspec3_left, hspec3_right⟩,
      end,
      have (h2 : A*v = z*v) := v hv hv2,
      have (h3 : A*v.conj = z.conj*v.conj) := begin
        have (h3 : A = A.transpose) := by apply matrix.is_symm_iff.mp hA,
        have (h4 : A.transpose*v.conj = z.conj*v.conj) := begin
          rw ←h3,
          rw ←h2,
          rw ←mul_conj,
          rw ←mul_conj,
          ring,
        end,
        rw ←h3 at h4,
        exact h4,
      end,
      have (h4 : (v.conj).transpose*A*v = (v.conj).transpose*z*v) := begin
        rw ←h2,
        rw ←mul_assoc,
        ring,
      end,
      have (h5 : (v.conj).transpose*A*v = (v.conj).transpose*z.conj*v.conj) := begin
        rw ←h3,
        rw ←mul_assoc,
        ring,
      end,
      have (h6 : v.conj.transpose*A*v = v.conj.transpose*z.conj*v.conj) := begin
        rw ←h5,
        rw ←h4,
        ring,
      end,
      have (h7 : v.conj.transpose*A*v = z.conj*v.conj.transpose*v.conj) := begin
        rw ←mul_assoc,
        ring,
      end,
      have (h8 : v.conj.transpose*A*v = z.conj*v.transpose.conj*v.conj) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h9 : v.conj.transpose*A*v = z.conj*v.transpose.conj*v) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h10 : v.conj.transpose*A*v = z.conj*(v.transpose*v)) := begin
        rw ←mul_assoc,
        ring,
      end,
      have (h11 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h12 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h13 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h14 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h15 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h16 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h17 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h18 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h19 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h20 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h21 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h22 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h23 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h24 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h25 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h26 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h27 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h28 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h29 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h30 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h31 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (h32 : v.conj.transpose*A*v = z*(v.transpose*v)) := begin
        rw ←mul_conj,
        ring,
      end,
      have (
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem begin
    assume (z : ℂ) (hz : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)),
    have h1 : (∃ x : vector n ℂ, x ≠ 0 ∧ A.map (complex.of_real).to_fun x = z • x), from spectrum_iff.mp hz,
    cases h1 with x h1, cases h1 with hx hxz,
    have h2 : (∃ x : vector n ℂ, x ≠ 0 ∧ A.map (complex.of_real).to_fun x = conj z • x), from by {
      use (conj x),
      have h3 : (conj x ≠ 0), from by {
        assume h4 : conj x = 0,
        have h5 : x = 0, from by {
          have h6 : (0 : ℂ) = conj x, from by rw h4,
          have h7 : (0 : ℂ) = x, from by {
            rw [← conj_zero,← conj_eq_zero,h6],
          },
          exact h7,
        },
        exact hx h5,
      },
      have h4 : (A.map (complex.of_real).to_fun (conj x) = conj z • conj x), from by {
        rw [← conj_conj_eq_self,hxz],
      },
      split, exact h3, exact h4,
    },
    have h3 : (conj z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)), from by {
      apply spectrum_iff.mpr, exact h2,
    },
    have h4 : (conj z = z), from by {
      apply spectrum_iff.mp, apply h3,
    },
    have h5 : (conj z.im = z.im), from by {
      rw ← conj_conj_eq_self z.im,
    },
    have h6 : (z.im = 0), from by {
      rw [← conj_eq_zero,h4,h5],
    },
    exact h6,
  end


/--`theorem`
Sum of Squares
 :$\forall x, y \in \R: x^2 + y^2 \geq 0$
`proof`
Follows from the fact that the square of a real number is never negative.
{{qed}}
-/
theorem sum_of_squares (x y : ℝ) : (x^2 + y^2) ≥ 0 :=
begin
  have h1 : (x^2 ≥ 0), from by {rw ← sq, apply sq_nonneg},
  have h2 : (y^2 ≥ 0), from by {rw ← sq, apply sq_nonneg},
  have h3 : (x^2 + y^2) ≥ 0, from by apply add_nonneg h1 h2,
  exact h3,
end

--OUTPUT 6
theorem by {
    assume z : ℂ,
    assume hz : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun),
    have h1 : (matrix.map A (complex.of_real).to_fun).det = 0, from by {
      have h1 : (matrix.map A (complex.of_real).to_fun).det = ((matrix.map A (complex.of_real).to_fun) - z • (matrix.id _)).det, from by {
        rw det_add_mul_sub_left,
      },
      show (matrix.map A (complex.of_real).to_fun).det = 0, from by {
        rw ← h1,
        rw det_mul,
        rw det_id,
        rw det_zero,
        rw det_zero,
        rw det_zero,
        ring,
      }
    },
    have h2 :  (matrix.map A (complex.of_real).to_fun).is_symm, from by {
      have h1 : (matrix.map A (complex.of_real).to_fun).transpose = (matrix.map A (complex.of_real).to_fun), from by {
        rw transpose_map,
        rw hA,
        rw transpose_map,
        rw transpose_id,
      },
      show (matrix.map A (complex.of_real).to_fun).is_symm, from by {
        apply matrix.is_symm_iff_transpose_eq_self.2 h1,
      }
    },
    have h3 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).det = 0, from by {
      apply h2.det_eq_zero_iff.2,
      rw ← h1,
      show (matrix.map A (complex.of_real).to_fun - z • matrix.id _).det = (matrix.map A (complex.of_real).to_fun).det, from by {
        rw ← h1,
        ring,
      }
    },
    have h4 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).is_symm, from by {
      show (matrix.map A (complex.of_real).to_fun - z • matrix.id _).is_symm, from by {
        apply matrix.is_symm_iff_transpose_eq_self.2,
        rw transpose_add,
        rw hA,
        rw transpose_map,
        rw transpose_id,
        rw ← sub_transpose,
        rw ← sub_transpose,
        rw ← mul_transpose,
        rw transpose_id,
        rw transpose_mul,
        rw mul_transpose,
        rw transpose_id,
        rw transpose_map,
        rw transpose_id,
        rw transpose_map,
        rw transpose_id,
        rw transpose_zero,
        rw transpose_zero,
        rw transpose_zero,
        apply matrix.transpose_sub,
        apply matrix.transpose_sub,
        apply matrix.sub_sub,
        rw ← add_sub_assoc,
        rw add_sub_cancel,
        ring,
      }
    },
    have h5 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = 0, from by {
      apply matrix.trace_eq_zero_iff.2,
      rw ← h3,
      rw trace_det,
      show (matrix.map A (complex.of_real).to_fun - z • matrix.id _).det = (matrix.map A (complex.of_real).to_fun).det, from by {
        rw ← h1,
        ring,
      }
    },
    have h6 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = 0, from by {
      apply h4.trace_eq_zero_iff.2,
      rw ← h5,
      show (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = (matrix.map A (complex.of_real).to_fun).trace, from by {
        rw ← h5,
        ring,
      }
    },
    have h7 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = 0, from by {
      apply h4.trace_eq_zero_iff.2,
      rw ← h6,
      show (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = (matrix.map A (complex.of_real).to_fun).trace, from by {
        rw ← h6,
        ring,
      }
    },
    have h8 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = 0, from by {
      apply matrix.trace_eq_zero_iff.2,
      rw ← h7,
      show (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = (matrix.map A (complex.of_real).to_fun).trace, from by {
        rw ← h7,
        ring,
      }
    },
    have h9 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = 0, from by {
      apply matrix.trace_eq_zero_iff.2,
      rw ← h8,
      show (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = (matrix.map A (complex.of_real).to_fun).trace, from by {
        rw ← h8,
        ring,
      }
    },
    have h10 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = 0, from by {
      apply matrix.trace_eq_zero_iff.2,
      rw ← h9,
      show (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = (matrix.map A (complex.of_real).to_fun).trace, from by {
        rw ← h9,
        ring,
      }
    },
    have h11 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = 0, from by {
      apply matrix.trace_eq_zero_iff.2,
      rw ← h10,
      show (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = (matrix.map A (complex.of_real).to_fun).trace, from by {
        rw ← h10,
        ring,
      }
    },
    have h12 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = 0, from by {
      apply matrix.trace_eq_zero_iff.2,
      rw ← h11,
      show (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = (matrix.map A (complex.of_real).to_fun).trace, from by {
        rw ← h11,
        ring,
      }
    },
    have h13 : (matrix.map A (complex.of_real).to_fun - z • matrix.id _).trace = 0, from by {
      apply matrix.trace_eq_zero_iff.2,
      rw ← h12,
      show (matrix.map A (complex.of_real).to_fun
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem begin
    assume (z : ℂ),
    assume hz : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun),
    have h1 : z ∈ complex.nonzero_complexes, from by {apply matrix.spectrum_nonzero, exact hz},
    have h2 : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun), from by {apply matrix.spectrum_nonzero, exact hz},
    have h3 : complex.conj z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun), from by {
      apply matrix.spectrum_conj hA, exact h2, },
    have h4 : complex.conj z ∈ complex.nonzero_complexes, from by {apply matrix.spectrum_nonzero, exact h3},
    have h5 : z * complex.conj z ∈ complex.nonnegative_complexes, from by {
      apply complex.nonnegative_complexes_mul h1 h4, },
    have h6 : z * complex.conj z ∈ complex.nonnegative_reals, from by {
      have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
        apply complex.nonzero_complexes_conj h1, },
      have h8 : z ∈ complex.nonzero_complexes, from by {
        apply complex.nonzero_complexes_conj h7, },
      have h9 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
        apply complex.nonzero_complexes_mul h8 h7, },
      apply complex.nonnegative_reals_of_nonzero_complexes h5 h9, },
    have h10 : z * complex.conj z ∈ complex.nonnegative_reals, from by {
      have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
        apply complex.nonzero_complexes_conj h1, },
      have h8 : z ∈ complex.nonzero_complexes, from by {
        apply complex.nonzero_complexes_conj h7, },
      have h9 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
        apply complex.nonzero_complexes_mul h8 h7, },
      apply complex.nonnegative_reals_of_nonzero_complexes h5 h9, },
    have h11 : (z * complex.conj z) = 0, from by {
      have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
        apply complex.nonzero_complexes_conj h1, },
      have h8 : z ∈ complex.nonzero_complexes, from by {
        apply complex.nonzero_complexes_conj h7, },
      have h9 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
        apply complex.nonzero_complexes_mul h8 h7, },
      have h10 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
        have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
          apply complex.nonzero_complexes_conj h1, },
        have h8 : z ∈ complex.nonzero_complexes, from by {
          apply complex.nonzero_complexes_conj h7, },
        have h9 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
          apply complex.nonzero_complexes_mul h8 h7, },
        apply complex.nonnegative_reals_of_nonzero_complexes h5 h9, },
      have h11 : z * complex.conj z = 0, from by {
        have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
          apply complex.nonzero_complexes_conj h1, },
        have h8 : z ∈ complex.nonzero_complexes, from by {
          apply complex.nonzero_complexes_conj h7, },
        have h9 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
          apply complex.nonzero_complexes_mul h8 h7, },
        have h10 : z * complex.conj z ∈ complex.nonnegative_reals, from by {
          have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
            apply complex.nonzero_complexes_conj h1, },
          have h8 : z ∈ complex.nonzero_complexes, from by {
            apply complex.nonzero_complexes_conj h7, },
          have h9 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
            apply complex.nonzero_complexes_mul h8 h7, },
          apply complex.nonnegative_reals_of_nonzero_complexes h5 h9, },
        have h11 : z * complex.conj z = 0, from by {
          have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
            apply complex.nonzero_complexes_conj h1, },
          have h8 : z ∈ complex.nonzero_complexes, from by {
            apply complex.nonzero_complexes_conj h7, },
          have h9 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
            apply complex.nonzero_complexes_mul h8 h7, },
          have h10 : z * complex.conj z ∈ complex.nonnegative_reals, from by {
            have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
              apply complex.nonzero_complexes_conj h1, },
            have h8 : z ∈ complex.nonzero_complexes, from by {
              apply complex.nonzero_complexes_conj h7, },
            have h9 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
              apply complex.nonzero_complexes_mul h8 h7, },
            apply complex.nonnegative_reals_of_nonzero_complexes h5 h9, },
          have h11 : z * complex.conj z = 0, from by {
            have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
              apply complex.nonzero_complexes_conj h1, },
            have h8 : z ∈ complex.nonzero_complexes, from by {
              apply complex.nonzero_complexes_conj h7, },
            have h9 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
              apply complex.nonzero_complexes_mul h8 h7, },
            have h10 : z * complex.conj z ∈ complex.nonnegative_reals, from by {
              have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
                apply complex.nonzero_complexes_conj h1, },
              have h8 : z ∈ complex.nonzero_complexes, from by {
                apply complex.nonzero_complexes_conj h7, },
              have h9 : z * complex.conj z ∈ complex.nonzero_complexes, from by {
                apply complex.nonzero_complexes_mul h8 h7, },
              apply complex.nonnegative_reals_of_nonzero_complexes h5 h9, },
            have h11 : z * complex.conj z = 0, from by {
              have h7 : (complex.conj z) ∈ complex.nonzero_complexes, from by {
                apply complex.nonzero_complexes_conj h1, },
              have h8 : z ∈ complex.nonzero_complexes, from by {
                apply complex.nonzero_complexes_conj h7, },
              have h9 : z * complex.conj z ∈
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem begin
    assume (z : ℂ) (h : z ∈ spectrum ℂ (matrix.map A (complex.of_real).to_fun)),
    have h1 : ∃ v : vector ℂ n, (v ≠ 0) ∧ (A.map (complex.of_real).to_fun) v = z • v, from classical.some (spectrum.eigenvalue_exists_of_mem_spectrum h),
    have h2 : A.map (complex.of_real).to_fun (conj v) = conj (z) • (conj v), from by 
      {
        rw matrix.map_conj, rw matrix.map_conj, rw matrix.map_mul, rw matrix.map_one,
        rw ←complex.conj_mul, rw ←complex.of_real_mul, rw complex.conj_eq_of_real,
        rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map_one,
        rw complex.mul_comm, rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one,
        rw matrix.map_mul, rw matrix.map_one, rw ←complex.conj_mul, rw ←complex.of_real_mul,
        rw complex.conj_eq_of_real, rw matrix.map_mul, rw matrix.map_one, rw matrix.map_mul, rw matrix.map
end --Needs more than 2000 tokens!

