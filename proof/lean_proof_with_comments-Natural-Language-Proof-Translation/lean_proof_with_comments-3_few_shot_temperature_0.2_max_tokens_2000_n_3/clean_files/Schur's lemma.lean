
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
Schur's lemma
Let $V$ and $W$ be vector spaces; and let $\rho_{V}$ and $\rho_{W}$ be irreducible representations of $G$ on $V$ and $W$ respectively. If $V$ and $W$ are not isomorphic, then there are no nontrivial representations of $G$ on $V$ and $W$ respectively.
`proof`
Suppose $f$ is a nonzero $G$-linear map from $V$ to $W$. We will prove that $V$ and $W$ are isomorphic. Let $V^{\prime}$ be the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$. (It is easy to check that this is a subspace.) By the assumption that $f$ is $G$-linear, for every $g$ in $G$ and choice of $x$ in $V^{\prime}, f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))=\left(\rho_W(g)\right)(0)=0$. But saying that $f\left(\rho_V(g)(x)\right)=0$ is the same as saying that $\rho_V(g)(x)$ is in the null space of $f: V \rightarrow W$. So $V^{\prime}$ is stable under the action of $G$; it is a subrepresentation. Since by assumption $V$ is irreducible, $V^{\prime}$ must be zero; so $f$ is injective.

By an identical argument we will show $f$ is also surjective; since $f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))$, we can conclude that for arbitrary choice of $f(x)$ in the image of $f, \rho_W(g)$ sends $f(x)$ somewhere else in the image of $f$; in particular it sends it to the image of $\rho_V(g) x$. So the image of $f(x)$ is a subspace $W^{\prime}$ of $W$ stable under the action of $G$, so it is a subrepresentation and $f$ must be zero or surjective. By assumption it is not zero, so it is surjective, in which case it is an isomorphism.

QED
-/
theorem 
FEW SHOT PROMPTS TO CODEX(END)-/
--OUTPUT 1
theorem schur_lemma {V W : Type*} [add_comm_group V] [add_comm_group W] [vector_space ℂ V] [vector_space ℂ W]
  (G : Type*) [group G] [decidable_eq G] [decidable_eq V] [decidable_eq W]
  (rhoV : G →* linear_map ℂ V V) (rhoW : G →* linear_map ℂ W W)
  (hirrV : irreducible rhoV) (hirrW : irreducible rhoW)
  (f : V →ₗ[ℂ] W) (hf : f ≠ 0) : V ≃ₗ[ℂ] W :=
begin
  -- Suppose $f$ is a nonzero $G$-linear map from $V$ to $W$.
  -- We will prove that $V$ and $W$ are isomorphic.
  have h1 : ∀ (f : V →ₗ[ℂ] W) (hf : f ≠ 0), V ≃ₗ[ℂ] W, from
    assume (f : V →ₗ[ℂ] W) (hf : f ≠ 0),
  begin
    -- Let $V^{\prime}$ be the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$.
    -- (It is easy to check that this is a subspace.)
    let V' := f.ker,
    have h2 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h3 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h4 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h5 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h6 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h7 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h8 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h9 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h10 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h11 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h12 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h13 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h14 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h15 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h16 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h17 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h18 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h19 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h20 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h21 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h22 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h23 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h24 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h25 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h26 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h27 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h28 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h29 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h30 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h31 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h32 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h33 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h34 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h35 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h36 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h37 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h38 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h39 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h40 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h41 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h42 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h43 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h44 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h45 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h46 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h47 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h48 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h49 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h50 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h51 : is_submodule ℂ V' V, from by apply is_submodule.ker_is_submodule,
    have h52 : is_submodule ℂ V' V, from by apply is_
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem schur_lemma {G : Type*} [group G] {V W : Type*} [add_comm_group V] [add_comm_group W] [vector_space ℂ V] [vector_space ℂ W]
  (hirrV : irreducible G V) (hirrW : irreducible G W) (hnotiso : ¬ isomorphic V W) :
  ∀ f : V →ₗ[ℂ] W, f = 0 :=
begin
  assume f : V →ₗ[ℂ] W,
  -- Suppose $f$ is a nonzero $G$-linear map from $V$ to $W$.
  assume hnonzero : f ≠ 0,
  -- We will prove that $V$ and $W$ are isomorphic.
  have hiso : isomorphic V W, from by {
    -- Let $V^{\prime}$ be the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$.
    let V' := f.ker,
    -- (It is easy to check that this is a subspace.)
    have hsubspace : is_subspace V' := by {
      apply is_submodule.is_subspace,
      apply is_submodule.of_le (submodule.span ℂ V),
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_submodule.subset_span,
      apply is_sub
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem schur_lemma {G : Type*} [group G] {V W : Type*} [add_comm_group V] [module G V] [add_comm_group W] [module G W] (hirrV : irreducible G V) (hirrW : irreducible G W) (hnotiso : ¬ isomorphic V W) : ∀ f : V →ₗ[G] W, f = 0 :=
begin
  -- Suppose $f$ is a nonzero $G$-linear map from $V$ to $W$.
  assume f : V →ₗ[G] W,
  assume hf : f ≠ 0,
  -- We will prove that $V$ and $W$ are isomorphic.
  have hiso : isomorphic V W, from by {
    -- Let $V^{\prime}$ be the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$.
    let V' : submodule G V := ker f,
    -- (It is easy to check that this is a subspace.)
    have hV' : is_submodule G V' := by apply_instance,
    -- By the assumption that $f$ is $G$-linear, for every $g$ in $G$ and choice of $x$ in $V^{\prime}, f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))=\left(\rho_W(g)\right)(0)=0$.
    have h1 : ∀ (g : G) (x : V'), f (g • x) = 0, from by {
      assume (g : G) (x : V'),
      have h2 : f (g • x) = g • (f x), from by {
        apply linear_map.map_smul,
      },
      have h3 : f x = 0, from by {
        apply submodule.mem_ker,
        exact hV',
        exact x,
      },
      rw h3 at h2,
      rw smul_zero at h2,
      exact h2,
    },
    -- But saying that $f\left(\rho_V(g)(x)\right)=0$ is the same as saying that $\rho_V(g)(x)$ is in the null space of $f: V \rightarrow W$.
    have h4 : ∀ (g : G) (x : V'), g • x ∈ V', from by {
      assume (g : G) (x : V'),
      have h5 : f (g • x) = 0, from by {
        apply h1,
      },
      show g • x ∈ V', from by {
        apply submodule.mem_ker,
        exact hV',
        exact h5,
      },
    },
    -- So $V^{\prime}$ is stable under the action of $G$; it is a subrepresentation.
    have h6 : is_submodule G V', from by {
      apply is_submodule.of_is_submodule_of_stable,
      exact hV',
      exact h4,
    },
    -- Since by assumption $V$ is irreducible, $V^{\prime}$ must be zero; so $f$ is injective.
    have h7 : V' = ⊥, from by {
      apply irreducible.irreducible_of_submodule_eq_bot,
      exact hirrV,
      exact h6,
    },
    have h8 : injective f, from by {
      apply linear_map.injective_of_ker_eq_bot,
      exact h7,
    },

    -- By an identical argument we will show $f$ is also surjective;
    have h9 : surjective f, from by {
      -- since $f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))$, we can conclude that for arbitrary choice of $f(x)$ in the image of $f, \rho_W(g)$ sends $f(x)$ somewhere else in the image of $f$;
      have h10 : ∀ (g : G) (x : V), f x ∈ range f → g • (f x) ∈ range f, from by {
        assume (g : G) (x : V) (h11 : f x ∈ range f),
        have h12 : f (g • x) = g • (f x), from by {
          apply linear_map.map_smul,
        },
        have h13 : f (g • x) ∈ range f, from by {
          apply range.mem_of_mem_range,
          exact h11,
        },
        show g • (f x) ∈ range f, from by {
          apply range.mem_of_mem_range,
          exact h13,
        },
      },
      -- in particular it sends it to the image of $\rho_V(g) x$.
      have h14 : ∀ (g : G) (x : V), f x ∈ range f → g • (f x) = f (g • x), from by {
        assume (g : G) (x : V) (h15 : f x ∈ range f),
        have h16 : f (g • x) ∈ range f, from by {
          apply h10,
          exact h15,
        },
        have h17 : f (g • x) = g • (f x), from by {
          apply linear_map.map_smul,
        },
        show g • (f x) = f (g • x), from by {
          apply eq_of_mem_range h16,
          exact h17,
        },
      },
      -- So the image of $f(x)$ is a subspace $W^{\prime}$ of $W$ stable under the action of $G$, so it is a subrepresentation and $f$ must be zero or surjective.
      let W' : submodule G W := range f,
      have h18 : is_submodule G W', from by {
        apply is_submodule.of_is_submodule_of_stable,
        apply range.is_submodule,
        exact h14,
      },
      -- By assumption it is not zero, so it is surjective, in which case it is an isomorphism.
      have h19 : W' = ⊤, from by {
        apply irreducible.irreducible_of_submodule_eq_top,
        exact hirrW,
        exact h18,
      },
      show surjective f, from by {
        apply linear_map.surjective_of_range_eq_top,
        exact h19,
      },
    },
    -- QED
    show isomorphic V W, from by {
      apply linear_equiv.is_iso,
      exact h8,
      exact h9,
    },
  },
  -- We will prove that $V$ and $W$ are isomorphic.
  show false, from by {
    apply hnotiso,
    exact hiso,
  },
end

