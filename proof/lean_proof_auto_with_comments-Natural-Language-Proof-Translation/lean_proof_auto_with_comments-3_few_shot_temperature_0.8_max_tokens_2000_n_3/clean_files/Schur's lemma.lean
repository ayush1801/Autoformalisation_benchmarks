
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
theorem schur_lemma {G α : Type} (V : representation G α) (W : representation G α) (f : V → W) :
  ∀ x ∈ V, f x ≠ 0 →
  ∃ W' ⊆ W, ∀ g ∈ G, (g.repr : V → W) f x ∈ W' :=
sorry


/--`theorem`
Consistent and Complete
A set of statements is consistent if and only if there is at least one true statement.
`proof`
Suppose there is a true statement. Then by definition of a true statement, the set of statements is consistent.

Suppose there is no true statement. Then by definition of a true statement, the set of statements is inconsistent.

Suppose the set is consistent. Then there is at least one true statement, or by definition of a true statement, there is no true statement. The set is complete if and only if there is at least one true statement.
{{qed}}
-/
theorem consistent_complete {α : Type} (S : set (statement α)) (consistency : consistent S) : ∃ s ∈ S, s.s_truth = tt :=
begin
  -- Set is consistent
  assume (S : set (statement α)) (consistency : consistent S),
  -- Then there is at least one true statement, by definition of a true statement
  have h1 : ∃ s ∈ S, s.s_truth = tt, from by auto [consistency],
  -- The set is complete if and only if there is at least one true statement.
  show ∃ s ∈ S, s.s_truth = tt, from h1,
end

--OUTPUT 2
theorem schur_lemma (V W : Type*) [vector_space ℂ V] [vector_space ℂ W] (ρ₁ : G →* lin ℂ V) (ρ₂ : G →* lin ℂ W) : irreducible ρ₁ → irreducible ρ₂ → (nonzero (V → W)) → V ≃* W :=
begin
  assume h1 : irreducible ρ₁,
  assume h2 : irreducible ρ₂,
  assume (h3 : V → W) (h4 : nonzero (V → W)),

  sorry,
end

--OUTPUT 3
theorem schurs_lemma {G : Type*} {V W : Type*} [group G] [add_comm_group V] [add_comm_group W] [vector_space ℂ V] [vector_space ℂ W] [module ℂ G V] [module ℂ G W] [irreducible G V] [irreducible G W] (f : V →ₗ[ℂ] W) : f ≠ 0 → V ≃ W :=
begin
  -- Suppose $f$ is a nonzero $G$-linear map from $V$ to $W$. We will prove that $V$ and $W$ are isomorphic.
  assume h1 : f ≠ 0,
  have h1a : f ≠ 0, from show f ≠ 0, from by auto [h1, zero_smul] using [linear_map.map_zero],
  have h1b : f ≠ 0, from show f ≠ 0, from by auto [h1, smul_zero] using [linear_map.map_zero],

  -- Let $V^{\prime}$ be the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$. (It is easy to check that this is a subspace.)
  let V' : set V := ker f,
  have h2 : V' ⊆ V, from by auto [linear_map.ker_subset],

  -- By the assumption that $f$ is $G$-linear, for every $g$ in $G$ and choice of $x$ in $V^{\prime}, f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))=\left(\rho_W(g)\right)(0)=0$.
  have h3 : ∀ g : G, ∀ x : V, x ∈ V' → f (g • x) = 0, from by auto [linear_map.mem_ker] using [linear_map.map_smul],
  have h4 : ∀ g : G, ∀ x : V, x ∈ V' → f (g • x) = 0, from by auto [h3] using [linear_map.map_smul],

  -- But saying that $f\left(\rho_V(g)(x)\right)=0$ is the same as saying that $\rho_V(g)(x)$ is in the null space of $f: V \rightarrow W$.
  have h5 : ∀ g : G, ∀ x : V, x ∈ V' → g • x ∈ V', from by auto [h3, mem_ker] using [linear_map.map_smul, linear_map.map_zero],

  -- So $V^{\prime}$ is stable under the action of $G$; it is a subrepresentation.
  have h6 : subrepresentation G V V', from subrepresentation.mk' (h5 : _),
  have h7 : is_submodule G V' V, from is_submodule.mk (h5 : _),

  -- Since by assumption $V$ is irreducible, $V^{\prime}$ must be zero; so $f$ is injective.
  have h8 : irreducible G V' → V' = (linear_map.ker f), from by auto [irreducible.irr_ker_eq, h1a, h1b] using [linear_map.map_zero],
  have h9 : irreducible G (V') → (V') = (0), from by auto [irreducible.irr_eq_zero, h1a, h1b, h8, linear_map.ker_eq_zero] using [linear_map.map_zero],
  have h10 : irreducible G (V') → (V') = (0), from by auto [h9, h6, irreducible_subrepresentation],
  have h11 : irreducible G (V') → (V') = (0), from by auto [h10, irreducible_subrepresentation],
  have h12 : V' = 0, from by auto [h11],

  -- By an identical argument we will show $f$ is also surjective;
  have h13 : linear_map.range f ⊆ W, from by auto [linear_map.range_subset_iff],
  have h14 : linear_map.range f ⊆ W, from by auto [h13, linear_map.range_subset_iff],
  have h15 : ∀ g : G, ∀ x : V, x ∈ linear_map.range f → g • x ∈ linear_map.range f, from by auto [linear_map.mem_range, linear_map.map_smul] using [linear_map.map_smul],
  have h16 : subrepresentation G W (linear_map.range f), from subrepresentation.mk' (h15 : _),
  have h17 : is_submodule G (linear_map.range f) W, from is_submodule.mk (h15 : _),

  -- since $f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))$, we can conclude that for arbitrary choice of $f(x)$ in the image of $f, \rho_W(g)$ sends $f(x)$ somewhere else in the image of $f; in particular it sends it to the image of $\rho_V(g) x$.
  have h18 : ∀ g : G, ∀ v : V, v ∈ linear_map.range f → g • v ∈ linear_map.range f, from by auto [linear_map.mem_range, linear_map.map_smul] using [linear_map.map_smul],
  have h19 : subrepresentation G W (linear_map.range f), from subrepresentation.mk' (h18 : _),
  have h20 : is_submodule G (linear_map.range f) W, from is_submodule.mk (h18 : _),

  -- So the image of $f(x)$ is a subspace $W^{\prime}$ of $W$ stable under the action of $G$, so it is a subrepresentation and $f$ must be zero or surjective.
  have h21 : is_submodule G (linear_map.range f) W → linear_map.range f = W → f ≠ 0, from by auto [linear_map.range_eq_top],
  have h22 : is_submodule G (linear_map.range f) W → linear_map.range f = W → f ≠ 0, from by auto [h21, h20] using [linear_map.injective],
  have h23 : is_submodule G (linear_map.range f) W → linear_map.range f = W → f ≠ 0, from by auto [h22, linear_map.injective_eq_range_eq_top] using [linear_map.injective],
  have h24 : is_submodule G (linear_map.range f) W → linear_map.range f = W → f ≠ 0, from by auto [h23, h16] using [irreducible_subrepresentation],

  -- By assumption it is not zero, so it is surjective, in which case it is an isomorphism.
  have h25 : f ≠ 0 → linear_map.range f = W, from by auto [h24, h1b] using [linear_map.range_eq_top],
  have h26 : f ≠ 0 → linear_map.range f = W, from by auto [h25, h12] using [linear_map.range_eq_top],

  -- QED
  show f ≠ 0 → V ≃ W, from by auto [linear_map.is_linear_equiv, h26] using [linear_map.is_linear_equiv]
end

