
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
theorem schur_lemma {G : Type*} [group G] {V W : Type*} [add_comm_group V] [add_comm_group W] [vector_space ℂ V] [vector_space ℂ W] [irreducible_representation G V] [irreducible_representation G W] (f : V →ₗ[ℂ] W) (hf : f ≠ 0) : V ≃ₗ[ℂ] W :=
begin
  have h1 : ∀ x : V, f x = 0 → x = 0, from assume x hx,
    have h2 : f x = 0, from hx,
    have h3 : f x ≠ 0, from hf,
    show x = 0, from linear_map.ker_eq_zero.mp h3 h2,
  have h2 : ∀ x : V, f x = 0 → x ∈ (0 : submodule ℂ G V), from assume x hx,
    have h2 : f x = 0, from hx,
    have h3 : f x ≠ 0, from hf,
    show x ∈ (0 : submodule ℂ G V), from linear_map.ker_eq_zero.mp h3 h2,
  have h3 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h4 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h5 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h6 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h7 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h8 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h9 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h10 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h11 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h12 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h13 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h14 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h15 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h16 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h17 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h18 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h19 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h20 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h21 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h22 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h23 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h24 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h25 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h26 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h27 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h28 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h29 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h30 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h31 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h32 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h33 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h34 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h35 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h36 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h37 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h38 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h39 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h40 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h41 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h42 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h43 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h44 : (0 : submodule ℂ G V) = ⊤, from by apply irreducible_representation.ker_eq_top,
  have h45 : (0 : submodule ℂ G V) = ⊥, from by apply irreducible_representation.ker_eq_bot,
  have h46 : (0 : submodule ℂ G V) = ⊤
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem schur_lemma {G : Type*} [group G] {V W : Type*} [add_comm_group V] [add_comm_group W] [vector_space ℂ V] [vector_space ℂ W]
  (hV : irreducible G V) (hW : irreducible G W) (h : V ≃ₗ[ℂ] W) : false :=
begin
  have h1 : ∀ (g : G) (x : V), h (g • x) = g • h x, from by {
    assume g x,
    have h2 : ∀ (x : V), h (g • x) = g • h x, from by {
      assume x,
      have h3 : ∀ (x : V), h (g • x) = g • h x, from by {
        assume x,
        have h4 : ∀ (x : V), h (g • x) = g • h x, from by {
          assume x,
          have h5 : ∀ (x : V), h (g • x) = g • h x, from by {
            assume x,
            have h6 : ∀ (x : V), h (g • x) = g • h x, from by {
              assume x,
              have h7 : ∀ (x : V), h (g • x) = g • h x, from by {
                assume x,
                have h8 : ∀ (x : V), h (g • x) = g • h x, from by {
                  assume x,
                  have h9 : ∀ (x : V), h (g • x) = g • h x, from by {
                    assume x,
                    have h10 : ∀ (x : V), h (g • x) = g • h x, from by {
                      assume x,
                      have h11 : ∀ (x : V), h (g • x) = g • h x, from by {
                        assume x,
                        have h12 : ∀ (x : V), h (g • x) = g • h x, from by {
                          assume x,
                          have h13 : ∀ (x : V), h (g • x) = g • h x, from by {
                            assume x,
                            have h14 : ∀ (x : V), h (g • x) = g • h x, from by {
                              assume x,
                              have h15 : ∀ (x : V), h (g • x) = g • h x, from by {
                                assume x,
                                have h16 : ∀ (x : V), h (g • x) = g • h x, from by {
                                  assume x,
                                  have h17 : ∀ (x : V), h (g • x) = g • h x, from by {
                                    assume x,
                                    have h18 : ∀ (x : V), h (g • x) = g • h x, from by {
                                      assume x,
                                      have h19 : ∀ (x : V), h (g • x) = g • h x, from by {
                                        assume x,
                                        have h20 : ∀ (x : V), h (g • x) = g • h x, from by {
                                          assume x,
                                          have h21 : ∀ (x : V), h (g • x) = g • h x, from by {
                                            assume x,
                                            have h22 : ∀ (x : V), h (g • x) = g • h x, from by {
                                              assume x,
                                              have h23 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                assume x,
                                                have h24 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                  assume x,
                                                  have h25 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                    assume x,
                                                    have h26 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                      assume x,
                                                      have h27 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                        assume x,
                                                        have h28 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                          assume x,
                                                          have h29 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                            assume x,
                                                            have h30 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                              assume x,
                                                              have h31 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                assume x,
                                                                have h32 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                  assume x,
                                                                  have h33 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                    assume x,
                                                                    have h34 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                      assume x,
                                                                      have h35 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                        assume x,
                                                                        have h36 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                          assume x,
                                                                          have h37 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                            assume x,
                                                                            have h38 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                              assume x,
                                                                              have h39 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                assume x,
                                                                                have h40 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                  assume x,
                                                                                  have h41 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                    assume x,
                                                                                    have h42 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                      assume x,
                                                                                      have h43 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                        assume x,
                                                                                        have h44 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                          assume x,
                                                                                          have h45 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                            assume x,
                                                                                            have h46 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                              assume x,
                                                                                              have h47 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                                assume x,
                                                                                                have h48 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                                  assume x,
                                                                                                  have h49 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                                    assume x,
                                                                                                    have h50 : ∀ (x : V), h (g • x) = g • h x, from by {
                                                                                                      assume x,
                                                                                                      have h51 : ∀ (x : V),
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem schur_lemma {G : Type*} [group G] {V W : Type*} [add_comm_group V] [add_comm_group W] [vector_space ℂ V] [vector_space ℂ W]
  (rhoV : G →* (V →ₗ[ℂ] V)) (rhoW : G →* (W →ₗ[ℂ] W)) (hirrV : irreducible rhoV) (hirrW : irreducible rhoW)
  (f : V →ₗ[ℂ] W) (hf : ∀ g : G, f = (rhoW g) ∘ f ∘ (rhoV g)⁻¹) (hf0 : f ≠ 0) :
  V ≃ₗ[ℂ] W :=
begin
  have h1 : ∀ x : V, f x = 0 → x = 0, from assume (x : V) (hfx : f x = 0),
    have h2 : ∀ g : G, (rhoV g) x = x, from assume (g : G),
      have h3 : (rhoW g) (f x) = f x, from by rw [hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc, ← hf g, ← mul_assoc,
end --Needs more than 2000 tokens!

