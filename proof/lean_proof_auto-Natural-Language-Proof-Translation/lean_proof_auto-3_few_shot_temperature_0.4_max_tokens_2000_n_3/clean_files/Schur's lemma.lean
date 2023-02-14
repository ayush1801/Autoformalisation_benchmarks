
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
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by auto [set.subset_of_mem_powerset, set.subset_of_mem_powerset],
  have h2 : (A ∩ B) ⊆ A, from by auto [set.inter_subset_left],
  have h3 : (A ∩ B) ⊆ S, from by auto [set.subset.trans],
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
  calc (x + y)^2 = (x+y)*(x+y) : by auto [sq]
  ... = x*(x+y) + y*(x+y) : by auto [add_mul]
  ... = x*x + x*y + y*x + y*y : by auto [mul_comm, add_mul] using [ring]
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
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by auto using [use (a⁻¹ * b)],
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by auto using [use b * a⁻¹], 

  have h3 : ∀ a : G, ∃! x : G, a * x = a, from by auto [h1],
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from by auto [h2],

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
theorem schur_lemma {V W : Type*} [add_comm_group V] [add_comm_group W] [vector_space ℝ V] [vector_space ℝ W] (f : V → W) [is_linear_map ℝ f] (h : ∀ v : V, f v ≠ 0) : V ≃ W :=
begin
  have h1 : ∀ v : V, f v = 0 → v = 0, from by auto [linear_map.ker_eq_bot],
  have h2 : ∀ w : W, ∃ v : V, f v = w, from by auto [linear_map.range_eq_top],
  have h3 : ∀ w : W, ∃! v : V, f v = w, from by auto [linear_map.range_eq_top],
  have h4 : ∀ v : V, f v = 0 → v = 0, from by auto [linear_map.ker_eq_bot],
  have h5 : ∀ w : W, ∃ v : V, f v = w, from by auto [linear_map.range_eq_top],
  have h6 : ∀ w : W, ∃! v : V, f v = w, from by auto [linear_map.range_eq_top],
  show V ≃ W, from by auto [linear_map.is_linear_map_iff, linear_map.ker_eq_bot, linear_map.range_eq_top, linear_map.is_linear_map_iff] using [use f],
end

--OUTPUT 2
theorem schur_lemma {G : Type*} [group G] {V W : Type*} [add_comm_group V] [add_comm_group W] [vector_space ℂ V] [vector_space ℂ W] [irreducible_representation G V] [irreducible_representation G W] (h : V ≃ₗ[G] W) : V ≃ₗ[ℂ] W :=
begin
  have h1 : V ≃ₗ[G] W, from h,
  have h2 : V ≃ₗ[ℂ] W, from h1.to_linear_equiv,
  show V ≃ₗ[ℂ] W, from h2,
end

--OUTPUT 3
theorem schur_lemma {V W : Type*} [add_comm_group V] [add_comm_group W] [vector_space ℝ V] [vector_space ℝ W] {G : Type*} [group G] [finite_dimensional ℝ V] [finite_dimensional ℝ W] {ρ₁ : G →* (V →ₗ[ℝ] V)} {ρ₂ : G →* (W →ₗ[ℝ] W)}
  (h_irr_1 : irreducible ρ₁) (h_irr_2 : irreducible ρ₂)
  (h_not_iso : ¬ is_linear_equiv V W)
  (f : V →ₗ[ℝ] W) (h_nonzero : f ≠ 0) : false :=
begin
  have h_inj : injective f, from
  begin
    have h_ker : submodule ℝ f.ker, from
    begin
      rw submodule.mk_eq_bot,
      have h_ker_sub : f.ker ⊆ ⊥, from
      begin
        assume x h_x,
        have h_fx : f x = 0, from by auto [h_x],
        show x ∈ ⊥, from by auto [h_fx, linear_map.mem_bot],
      end,
      show f.ker = ⊥, from by auto [h_ker_sub, set.subset.antisymm],
    end,
    have h_ker_irr : irreducible (ρ₁.comp f.ker), from by auto [h_irr_1, h_ker, irreducible.comp_bot],
    have h_ker_zero : f.ker = ⊥, from by auto [h_ker_irr, irreducible.ker_eq_bot],
    show injective f, from by auto [h_ker_zero, linear_map.injective_of_ker_eq_bot],
  end,
  have h_surj : surjective f, from
  begin
    have h_im : submodule ℝ f.range, from
    begin
      rw submodule.mk_eq_top,
      have h_im_sub : f.range ⊆ ⊤, from
      begin
        assume x h_x,
        have h_x_range : x ∈ f.range, from by auto [h_x],
        have h_x_mem : ∃ y, x = f y, from by auto [h_x_range, linear_map.mem_range],
        have h_x_mem_spec : x = f (classical.some h_x_mem), from by auto [h_x_mem, classical.some_spec],
        show x ∈ ⊤, from by auto [h_x_mem_spec, linear_map.mem_top],
      end,
      show f.range = ⊤, from by auto [h_im_sub, set.subset.antisymm],
    end,
    have h_im_irr : irreducible (ρ₂.comp f.range), from by auto [h_irr_2, h_im, irreducible.comp_top],
    have h_im_one : f.range = ⊤, from by auto [h_im_irr, irreducible.range_eq_top],
    show surjective f, from by auto [h_im_one, linear_map.surjective_of_range_eq_top],
  end,
  show false, from by auto [h_not_iso, h_inj, h_surj, linear_map.is_linear_equiv_iff_bijective],
end

