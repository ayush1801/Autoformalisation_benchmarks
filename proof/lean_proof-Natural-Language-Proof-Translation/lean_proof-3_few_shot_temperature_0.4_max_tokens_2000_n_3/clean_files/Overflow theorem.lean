
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
/- FEW SHOT PROMPTS TO CODEX(START)/--`theorem`
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
Overflow theorem
Let $F$ be a set of first-order formulas which has finite models of arbitrarily large size.

Then $F$ has an infinite model.
`proof`
For each $n$, let $\mathbf A_n$ be the formula:

$\exists x_1 \exists x_2 \ldots \exists x_n: \{x_1 \ne x_2 \land x_1 \ne x_3 \land \ldots \land x_{n - 1} \ne x_n\}$

Then $\mathbf A_i$ is true in a structure $\AA$ iff $\AA$ has at least $n$ elements.

Take:
$$ \Gamma := F \cup \bigcup_{i \mathop = 1}^\infty A_i $$

Since $F$ has models of arbitrarily large size, every finite subset of $\Gamma$ is satisfiable.

From the Compactness Theorem, $\Gamma$ is satisfiable in some model $\mathbf{M}$.

But since $\mathbf{M} \models A_i$ for each $i$, $\mathbf{M}$ must be infinite.

So $F$ has an infinite model.

QED
-/
theorem 
FEW SHOT PROMPTS TO CODEX(END)-/
--OUTPUT 1
theorem overflow {F : Type*} [decidable_pred F] : (∃ n, finite n ∧ ∀ A ∈ F, A n) → (∃ n, infinite n ∧ ∀ A ∈ F, A n) :=
begin
  assume (hfinite : ∃ n, finite n ∧ ∀ A ∈ F, A n),
  have h1 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
    exists.intro (λ x, x = n) (by obviously),
  have h2 : ∀ n, ∃ A, A n ∧ ∀ x y, x ≠ y → ¬ (A x ∧ A y), from assume (n : ℕ),
    begin
      have h3 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h4 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h5 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h6 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h7 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h8 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h9 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h10 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h11 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h12 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h13 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h14 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h15 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h16 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h17 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h18 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h19 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h20 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h21 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h22 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h23 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h24 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h25 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h26 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h27 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h28 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h29 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h30 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h31 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h32 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n : ℕ),
        exists.intro (λ x, x = n) (by obviously),
      have h33 : ∀ n, ∃ A, A n ∧ ∀ x, x ≠ n → ¬ A x, from assume (n :
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem overflow (F : set (formula ℕ)) (hF : ∀ n : ℕ, ∃ A : structure ℕ, A ⊨ F ∧ A.card ≥ n) : ∃ A : structure ℕ, A ⊨ F ∧ A.card = ⊤ :=
begin
  let A := (λ n : ℕ, ∃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℕ, x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧ x₁ ≠ x₅ ∧ x₁ ≠ x₆ ∧ x₁ ≠ x₇ ∧ x₁ ≠ x₈ ∧ x₁ ≠ x₉ ∧ x₁ ≠ x₁₀),
  let Γ := F ∪ (∪ i : ℕ, {A i}),
  have h1 : ∀ n : ℕ, ∃ A : structure ℕ, A ⊨ Γ ∧ A.card ≥ n, from
    assume (n : ℕ),
    have h1 : ∀ n : ℕ, ∃ A : structure ℕ, A ⊨ F ∧ A.card ≥ n, from hF,
    have h2 : ∀ n : ℕ, ∃ A : structure ℕ, A ⊨ A n ∧ A.card ≥ n, from
      assume (n : ℕ),
      have h3 : ∃ A : structure ℕ, A ⊨ A n ∧ A.card ≥ n, from by {
        use ⟨ℕ, by obviously⟩,
        have h4 : ⟨ℕ, by obviously⟩.card ≥ n, from by obviously,
        show ⟨ℕ, by obviously⟩ ⊨ A n ∧ ⟨ℕ, by obviously⟩.card ≥ n, from ⟨by obviously, h4⟩,
      },
    have h5 : ∃ A : structure ℕ, A ⊨ F ∧ A ⊨ A n ∧ A.card ≥ n, from
      exists.elim (h1 n) (assume (A : structure ℕ) (hA : A ⊨ F ∧ A.card ≥ n),
        exists.elim (h2 n) (assume (B : structure ℕ) (hB : B ⊨ A n ∧ B.card ≥ n),
          have h6 : A.card ≥ n ∧ B.card ≥ n, from ⟨hA.right, hB.right⟩,
          have h7 : A.card ≥ n ∧ A.card ≥ n, from ⟨hA.right, hA.right⟩,
          have h8 : A.card ≥ n, from le_trans h7.left h6.right,
          have h9 : A.card ≥ n ∧ A.card ≥ n, from ⟨hA.right, hA.right⟩,
          have h10 : A.card ≥ n, from le_trans h9.right h6.left,
          have h11 : A.card ≥ n, from le_trans h8 h10,
          have h12 : A ⊨ F ∧ A ⊨ A n ∧ A.card ≥ n, from ⟨hA.left, hB.left, h11⟩,
          exists.intro A h12,
        )
      ),
    have h13 : ∃ A : structure ℕ, A ⊨ Γ ∧ A.card ≥ n, from
      exists.elim (h5 n) (assume (A : structure ℕ) (hA : A ⊨ F ∧ A ⊨ A n ∧ A.card ≥ n),
        have h14 : A ⊨ Γ ∧ A.card ≥ n, from ⟨by obviously, hA.right⟩,
        exists.intro A h14,
      ),
    h13,
  have h2 : ∃ A : structure ℕ, A ⊨ Γ, from compactness Γ h1,
  have h3 : ∃ A : structure ℕ, A ⊨ F ∧ A ⊨ (∪ i : ℕ, {A i}) ∧ A.card = ⊤, from
    exists.elim h2 (assume (A : structure ℕ) (hA : A ⊨ Γ),
      have h4 : ∀ n : ℕ, A ⊨ A n, from
        assume (n : ℕ),
        have h5 : A ⊨ A n ∨ A ⊨ ¬ A n, from by {
          have h6 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
          show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
            have h7 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
            show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
              have h8 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
              show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                have h9 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                  have h10 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                  show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                    have h11 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                    show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                      have h12 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                      show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                        have h13 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                        show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                          have h14 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                          show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                            have h15 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                            show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                              have h16 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                              show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                                have h17 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                                show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                                  have h18 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                                  show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                                    have h19 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                                    show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                                      have h20 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                                      show A ⊨ A n ∨ A ⊨ ¬ A n, from by {
                                        have h21 : A ⊨ A n ∨ A ⊨ ¬ A n, from by obviously,
                                        show A ⊨ A n ∨ A ⊨
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem overflow_theorem (F : set (formula letter)) :
  (∀ n, ∃ (A : structure letter), A ⊨ F ∧ A.card ≥ n) → ∃ (A : structure letter), A ⊨ F ∧ A.card = ⊤ :=
begin
  assume h1 : ∀ n, ∃ (A : structure letter), A ⊨ F ∧ A.card ≥ n,
  let A_n := λ n, ∃ x₁, ∃ x₂, ∃ x₃, ∃ x₄, ∃ x₅, ∃ x₆, ∃ x₇, ∃ x₈, ∃ x₉, ∃ x₁₀, ∃ x₁₁, ∃ x₁₂, ∃ x₁₃, ∃ x₁₄, ∃ x₁₅, ∃ x₁₆, ∃ x₁₇, ∃ x₁₈, ∃ x₁₉, ∃ x₂₀, ∃ x₂₁, ∃ x₂₂, ∃ x₂₃, ∃ x₂₄, ∃ x₂₅, ∃ x₂₆, ∃ x₂₇, ∃ x₂₈, ∃ x₂₉, ∃ x₃₀, ∃ x₃₁, ∃ x₃₂, ∃ x₃₃, ∃ x₃₄, ∃ x₃₅, ∃ x₃₆, ∃ x₃₇, ∃ x₃₈, ∃ x₃₉, ∃ x₄₀, ∃ x₄₁, ∃ x₄₂, ∃ x₄₃, ∃ x₄₄, ∃ x₄₅, ∃ x₄₆, ∃ x₄₇, ∃ x₄₈, ∃ x₄₉, ∃ x₅₀, ∃ x₅₁, ∃ x₅₂, ∃ x₅₃, ∃ x₅₄, ∃ x₅₅, ∃ x₅₆, ∃ x₅₇, ∃ x₅₈, ∃ x₅₉, ∃ x₆₀, ∃ x₆₁, ∃ x₆₂, ∃ x₆₃, ∃ x₆₄, ∃ x₆₅, ∃ x₆₆, ∃ x₆₇, ∃ x₆₈, ∃ x₆₉, ∃ x₇₀, ∃ x₇₁, ∃ x₇₂, ∃ x₇₃, ∃ x₇₄, ∃ x₇₅, ∃ x₇₆, ∃ x₇₇, ∃ x₇₈, ∃ x₇₉, ∃ x₈₀, ∃ x₈₁, ∃ x₈₂, ∃ x₈₃, ∃ x₈₄, ∃ x₈₅, ∃ x₈₆, ∃ x₈₇, ∃ x₈₈, ∃ x₈₉, ∃ x₉₀, ∃ x₉₁, ∃ x₉₂, ∃ x₉₃, ∃ x₉₄, ∃ x₉₅, ∃ x₉₆, ∃ x₉₇, ∃ x₉₈, ∃ x₉₉, ∃ x₁₀₀, ∃ x₁₀₁, ∃ x₁₀₂, ∃ x₁₀₃, ∃ x₁₀₄, ∃ x₁₀₅, ∃ x₁₀₆, ∃ x₁₀₇, ∃ x₁₀₈, ∃ x₁₀₉, ∃ x₁₁₀, ∃ x₁₁₁, ∃ x₁₁₂, ∃ x₁₁₃, ∃ x₁₁₄, ∃ x₁₁₅, ∃ x₁₁₆, ∃ x₁₁₇, ∃ x₁₁₈, ∃ x₁₁₉, ∃ x₁₂₀, ∃ x₁₂₁, ∃ x₁₂₂, ∃ x₁₂₃, ∃ x₁₂₄, ∃ x₁₂₅, ∃ x₁₂₆, ∃ x₁₂₇, ∃ x₁₂₈, ∃ x₁₂₉, ∃ x₁₃₀, ∃ x₁₃₁, ∃ x₁₃₂, ∃ x₁₃₃, ∃ x₁₃₄, ∃ x₁₃₅, ∃ x₁₃₆, ∃ x₁₃₇, ∃ x₁₃₈, ∃ x₁₃₉, ∃ x₁₄₀, ∃ x₁₄₁, ∃ x₁₄₂, ∃ x₁₄₃, ∃ x₁₄₄, ∃ x₁₄₅, ∃ x₁₄₆, ∃ x₁₄₇, ∃ x₁₄₈, ∃ x₁₄₉, ∃ x₁₅₀, ∃ x₁₅₁, ∃ x₁₅₂, ∃ x₁₅₃, ∃ x₁₅₄, ∃ x₁₅₅, ∃ x₁₅₆, ∃ x₁₅₇, ∃ x₁₅₈, ∃ x₁₅₉, ∃ x₁₆₀, ∃ x₁₆₁, ∃ x₁₆₂, ∃ x₁₆₃, ∃ x₁₆₄, ∃ x₁₆₅, ∃ x₁₆₆, ∃ x₁₆₇, ∃ x₁₆₈, ∃ x₁₆₉, ∃ x₁₇₀, ∃ x
end --Needs more than 2000 tokens!

