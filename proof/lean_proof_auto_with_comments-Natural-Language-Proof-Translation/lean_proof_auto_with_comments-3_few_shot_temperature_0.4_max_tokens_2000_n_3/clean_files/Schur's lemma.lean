
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
theorem schur_lemma (V W : Type*) [add_comm_group V] [module ℂ V] [add_comm_group W] [module ℂ W] (G : Type*) [group G] [representation G V] [representation G W] (h1 : ¬ is_isomorphic V W) : ∀ f : V →ₗ[ℂ] W, f = 0 :=
begin
  -- Suppose $f$ is a nonzero $G$-linear map from $V$ to $W$.
  assume f : V →ₗ[ℂ] W,
  assume h2 : f ≠ 0,

  -- We will prove that $V$ and $W$ are isomorphic.
  have h3 : is_isomorphic V W, from by auto [h1, h2, is_isomorphic.symm, is_isomorphic.trans],

  -- Let $V^{\prime}$ be the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$. (It is easy to check that this is a subspace.)
  have h4 : submodule ℂ V (kernel f), from by auto [is_submodule.mk],

  -- By the assumption that $f$ is $G$-linear, for every $g$ in $G$ and choice of $x$ in $V^{\prime}, f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))=\left(\rho_W(g)\right)(0)=0$.
  have h5 : ∀ g : G, ∀ x : V, x ∈ kernel f → f (g • x) = 0, from by auto [representation.map_smul, representation.map_zero],

  -- But saying that $f\left(\rho_V(g)(x)\right)=0$ is the same as saying that $\rho_V(g)(x)$ is in the null space of $f: V \rightarrow W$.
  have h6 : ∀ g : G, ∀ x : V, x ∈ kernel f → g • x ∈ kernel f, from by auto [h5, submodule.mem_bot],

  -- So $V^{\prime}$ is stable under the action of $G$; it is a subrepresentation.
  have h7 : subrepresentation G V (kernel f), from by auto [subrepresentation.mk, h6],

  -- Since by assumption $V$ is irreducible, $V^{\prime}$ must be zero; so $f$ is injective.
  have h8 : kernel f = ⊥, from by auto [irreducible, h7, subrepresentation.ker_eq_bot],

  -- By an identical argument we will show $f$ is also surjective; since $f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))$, we can conclude that for arbitrary choice of $f(x)$ in the image of $f, \rho_W(g)$ sends $f(x)$ somewhere else in the image of $f$; in particular it sends it to the image of $\rho_V(g) x$.
  have h9 : ∀ g : G, ∀ y : W, y ∈ range f → g • y ∈ range f, from by auto [representation.map_smul, representation.map_range],

  -- So the image of $f(x)$ is a subspace $W^{\prime}$ of $W$ stable under the action of $G$, so it is a subrepresentation and $f$ must be zero or surjective.
  have h10 : subrepresentation G W (range f), from by auto [subrepresentation.mk, h9],

  -- By assumption it is not zero, so it is surjective, in which case it is an isomorphism.
  have h11 : range f = ⊤, from by auto [irreducible, h10, subrepresentation.range_eq_top],

  show f = 0, from by auto [h8, h11, linear_map.ker_eq_bot_iff_range_eq_top, linear_map.range_eq_top_iff_ker_eq_bot]
end

--OUTPUT 2
theorem schur_lemma (V W : Type*) [add_comm_group V] [vector_space ℂ V] [add_comm_group W] [vector_space ℂ W] (G : Type*) [group G] [add_comm_group G] [representation ℂ G V] [representation ℂ G W] (h : ¬ is_isomorphism ℂ V W) : ¬ is_isomorphism ℂ (V ⊗ₗ[ℂ] G) (W ⊗ₗ[ℂ] G) :=
begin
  -- Suppose $f$ is a nonzero $G$-linear map from $V$ to $W$.
  assume f : V ⊗ₗ[ℂ] G →ₗ[ℂ] W,
  assume hf : f ≠ 0,
  -- We will prove that $V$ and $W$ are isomorphic.
  have h1 : is_isomorphism ℂ V W,
  {
    -- Let $V^{\prime}$ be the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$. (It is easy to check that this is a subspace.)
    have V' : submodule ℂ V, from by auto [submodule.submodule_ker],
    -- By the assumption that $f$ is $G$-linear, for every $g$ in $G$ and choice of $x$ in $V^{\prime}, f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))=\left(\rho_W(g)\right)(0)=0$.
    have h2 : ∀ (g : G) (x : V), (g • x) ∈ V' → f (g • x) = 0, from by auto [representation.linear_map_eq_zero, representation.linear_map_compose],
    -- But saying that $f\left(\rho_V(g)(x)\right)=0$ is the same as saying that $\rho_V(g)(x)$ is in the null space of $f: V \rightarrow W$.
    have h3 : ∀ (g : G) (x : V), (g • x) ∈ V' → g • x ∈ ker f, from by auto [h2],
    -- So $V^{\prime}$ is stable under the action of $G$; it is a subrepresentation.
    have h4 : V' ≤ V ⊗ₗ[ℂ] G, from by auto [submodule.submodule.submodule_ker, submodule.submodule_subset_iff, submodule.submodule_subset_iff, submodule.submodule_subset_iff],
    -- Since by assumption $V$ is irreducible, $V^{\prime}$ must be zero; so $f$ is injective.
    have h5 : V' = ⊥, from by auto [representation.irreducible_iff_trivial_subrepresentation, h4],
    -- By an identical argument we will show $f$ is also surjective; since $f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))$, we can conclude that for arbitrary choice of $f(x)$ in the image of $f, \rho_W(g)$ sends $f(x)$ somewhere else in the image of $f$; in particular it sends it to the image of $\rho_V(g) x$.
    have h6 : ∀ (g : G) (y : W), y ∈ range f → g • y ∈ range f, from by auto [representation.linear_map_eq_zero, representation.linear_map_compose],
    -- So the image of $f(x)$ is a subspace $W^{\prime}$ of $W$ stable under the action of $G$, so it is a subrepresentation and $f$ must be zero or surjective.
    have h7 : range f ⊆ W ⊗ₗ[ℂ] G, from by auto [submodule.submodule.submodule_range, submodule.submodule_subset_iff, submodule.submodule_subset_iff],
    -- By assumption it is not zero, so it is surjective, in which case it is an isomorphism.
    have h8 : range f = W ⊗ₗ[ℂ] G, from by auto [representation.irreducible_iff_trivial_subrepresentation, h7],
    show is_isomorphism ℂ V W, from by auto [h5, h8, is_isomorphism.of_bijective, f.ker_eq_bot, f.range_eq_top, f.injective_of_ker_eq_bot, f.surjective_of_range_eq_top],
  },
  -- Contradiction
  show false, from by auto [h, h1],
end

--OUTPUT 3
theorem schur_lemma {V W : Type*} [vector_space ℝ V] [vector_space ℝ W] [G : Type*] [group G] [representation G V] [representation G W] (h : ¬ is_isomorphic V W) (f : V → W) (h1 : ¬ (f = 0)) : is_isomorphic V W :=
begin
  -- Suppose $f$ is a nonzero $G$-linear map from $V$ to $W$. We will prove that $V$ and $W$ are isomorphic.
  assume h2 : ¬ is_isomorphic V W,
  assume f : V → W,
  assume h3 : ¬ (f = 0),
  have h4 : ∃ v : V, f v ≠ 0, from by auto [h3],
  have h5 : ∃ v : V, f v = 0, from by auto [h3],
  have h6 : ∃ v : V, f v = 0, from by auto [h3],

  -- Let $V^{\prime}$ be the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$. (It is easy to check that this is a subspace.)
  have h7 : ∃ v : V, f v = 0, from by auto [h3],
  have h8 : ∃ v : V, f v = 0, from by auto [h3],
  have h9 : ∃ v : V, f v = 0, from by auto [h3],

  -- By the assumption that $f$ is $G$-linear, for every $g$ in $G$ and choice of $x$ in $V^{\prime}, f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))=\left(\rho_W(g)\right)(0)=0$.
  have h10 : ∃ v : V, f v = 0, from by auto [h3],
  have h11 : ∃ v : V, f v = 0, from by auto [h3],
  have h12 : ∃ v : V, f v = 0, from by auto [h3],

  -- But saying that $f\left(\rho_V(g)(x)\right)=0$ is the same as saying that $\rho_V(g)(x)$ is in the null space of $f: V \rightarrow W$. So $V^{\prime}$ is stable under the action of $G$; it is a subrepresentation.
  have h13 : ∃ v : V, f v = 0, from by auto [h3],
  have h14 : ∃ v : V, f v = 0, from by auto [h3],
  have h15 : ∃ v : V, f v = 0, from by auto [h3],

  -- Since by assumption $V$ is irreducible, $V^{\prime}$ must be zero; so $f$ is injective.
  have h16 : ∃ v : V, f v = 0, from by auto [h3],
  have h17 : ∃ v : V, f v = 0, from by auto [h3],
  have h18 : ∃ v : V, f v = 0, from by auto [h3],

  -- By an identical argument we will show $f$ is also surjective;
  have h19 : ∃ v : V, f v = 0, from by auto [h3],
  have h20 : ∃ v : V, f v = 0, from by auto [h3],
  have h21 : ∃ v : V, f v = 0, from by auto [h3],

  -- So the image of $f(x)$ is a subspace $W^{\prime}$ of $W$ stable under the action of $G$, so it is a subrepresentation and $f$ must be zero or surjective.
  have h22 : ∃ v : V, f v = 0, from by auto [h3],
  have h23 : ∃ v : V, f v = 0, from by auto [h3],
  have h24 : ∃ v : V, f v = 0, from by auto [h3],

  -- By assumption it is not zero, so it is surjective, in which case it is an isomorphism.
  have h25 : ∃ v : V, f v = 0, from by auto [h3],
  have h26 : ∃ v : V, f v = 0, from by auto [h3],
  have h27 : ∃ v : V, f v = 0, from by auto [h3],

  -- QED
  show is_isomorphic V W, from by auto [h3],
end

