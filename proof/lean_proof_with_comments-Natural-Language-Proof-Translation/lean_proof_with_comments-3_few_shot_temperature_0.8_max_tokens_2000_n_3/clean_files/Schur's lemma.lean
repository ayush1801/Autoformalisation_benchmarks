
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
theorem schur_s_lemma : sorry

/--`theorem`
Theorem:
Let $V$ be a vector space over a field $F$, and let $U$ and $W$ be subspaces of $V$. If $U$ and $W$ are nonzero, then there exists a nonzero vector $x$ in $U$ such that $W + x$ is a subspace of $V$.
Proof
Let $U$ and $W$ be subspaces of $V$. Either $U \cap W=V$ or $U \cap W=\emptyset$. If $U \cap W=V$, then $W + x=V$ for some $x \in U$ (if we can't find $x$ outside $W$, then $U \subseteq W$, and $U \cap W$ is a proper subspace of $V$, which contradicts $U \cap W=V$). Therefore, either $W+x=V$ or $U \cap W=\emptyset$.

In the case $U \cap W \neq \emptyset$, let $f:U \cap W \rightarrow \mathbb{Z}_2$ be the map $f(a)=1$ for all $a \in U \cap W$. This is clearly a linear map, and $V=U + W$. $f$ is also non-zero since $V \neq \emptyset$. Therefore, $f$ is a surjective map from $U \cap W$ to $\mathbb{Z}_2$. By the rank-nullity theorem, $\dim (U \cap W)=\dim\mathbb{Z}_2$. By the dimension theorem, $U \cap W$ and $\mathbb{Z}_2$ are isomorphic, so there exists a linear map $g:U \cap W \rightarrow \mathbb{Z}_2$ such that $g(a)=1$ for all $a \in U \cap W$.

Let $f:U \cap W \rightarrow \mathbb{Z}_2$ be the linear map $f(a)=0$ for all $a \in U \cap W$. $f$ is clearly a linear map, and it is also a non-zero map since $V \neq \emptyset$. Therefore, since $\dim (U \cap W)=\dim\mathbb{Z}_2$, by the rank-nullity theorem, there exists a non-zero linear map $h:U \cap W$ to $\mathbb{Z}_2$. The map $h$ is non-zero since $V \neq \emptyset$. Therefore, $g-h$ is a non-zero linear map from $U \cap W$ to $\mathbb{Z}_2$. Therefore, since $V \neq \emptyset$ and $\dim (U \cap W)=\dim\mathbb{Z}_2$, so by the rank-nullity theorem, $g-h$ must be surjective. Therefore, there exists a vector $x \in U \cap W$ such that $(g-h)(a)=1$.

$g(a)=0$ implies that $a \in W$. Therefore, $x \in U \cap W$ implies that $x \in W$, but $g(a)=1$ implies that $x \notin W$. Therefore, $x$ is the required non-zero vector in $U$ such that $W + x$ is a subspace of $V$. 
QED
-/
theorem subspaces : sorry

/--`theorem`
Let $V$ be a vector space over a field $F$, and let $T:V \rightarrow V$ be a linear map. Then $\dim (\operatorname{Im}(T))$ is the largest positive integer $n$ for which there exists a chain of subspaces
$$0=V_0 \subseteq V_1 \subseteq V_2 \subseteq \cdots \subseteq V_n=V$$
such that $V_{i+1}=V_i+T(V_i)$ for all $i=0,1,2,\ldots,n-1$.

Proof
Let $T(V)$ denote the image of $T$. Let $0=V_0 \subseteq V_1 \subseteq V_2 \subseteq \cdots \subseteq V_n=V$ be a maximal chain of subspaces of $V$ with the additional property that $V_{i+1}=V_i+T(V_i)$ for all $i=0,1,2,\ldots,n-1$. Let $V_{n+1} := V_n+T(V_n)$. Since $V_{n+1}=V_n+T(V_n)$, $V_{n+1}$ is a subspace of $V$. Moreover, $V_n \subset V_{n+1}$. To see this, let $v$ be in $V_n$. Then $v=w+T(w)$ for some $w$ in $V_n$. Then $v=w+T(w) \in V_{n+1}$ since $V_{n+1}=V_n+T(V_n)$. It follows that $V=V_n \subseteq V_{n+1}$.

Let $x \in V_{n+1} \setminus V_n$. We will show that $V_n+x=V_{n+1}$. Indeed, let $y$ be in $V_{n+1}$. Then $y=w+T(w)$ for some $w$ in $V_n$. Then $y=w+T(w)+0 \cdot x \in V_n+x$ since $V_n+x=V_n+x$. Thus, $V_{n+1} \subseteq V_n+x$, and so $V_{n+1}=V_n+x$.

Let $V_{n+2} := V_{n+1}+T(V_{n+1})$. We will show that $V_{n+2}=V$. Let $v$ be in $V$. In order to show that $v \in V_{n+2}$, then it would be sufficient to show that $v=x+T(x)$ for some $x$ in $V_{n+1}$. Let $x=v-T(v) \in V_{n+1}$. Then $v=x+T(x) \in V_{n+2}$. Thus, $V_{n+2}=V$ and so we have a chain
$$0=V_0 \subseteq V_1 \subseteq V_2 \subseteq \cdots \subseteq V_n \subseteq V_n+x \subseteq V_{n+1}=V_{n+2}=V$$
such that $V_{i+1}=V_i+T(V_i)$ for all $i=0,1,2,\ldots,n-1$, which contradicts the maximality of $n$. Thus, if $V=V_n \subset V_{n+1}$, then $T(V_n)$ is the full space $V$. This implies that $T$ is surjective, and therefore $\dim T(V)=\dim V$.
QED
-/
theorem dimension_of_image : sorry

/--`theorem`
THEOREM
Let $V, W$ be vector spaces over a field $F$. Let $T:V \rightarrow W$ and $S:W \rightarrow V$ be linear maps. Then $S \circ T$ is surjective if and only if $T$ is surjective and $\dim V=\dim W$.

Proof
First, let $S \circ T$ be surjective. Let $w$ be in $W$. Then $w=(S \circ T)(x)$ for some $x \in V$. Thus $w=S(T(x))$ for some $x \in V$, and so $T$ is surjective. Also, $\dim V \leq \dim W$ since $S \circ T$ is surjective. 

Now let $T$ be surjective. Let $w$ be in $W$. Then $w=T(x)$ for some $x \in V$. Then $S(w)=S(T(x)=T(T(x))=T(x)$ for all $x \in V$. Thus, $S(w)=w$ for all $w \in W$, so $
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem schur_lemma {G : Type*} {V W : Type*} [group G] [add_comm_group V] [module ℂ V] [add_comm_group W] [module ℂ W] (ρV ρW : G → units ℂ →* V →* V) (f : V →* W) (h1 : irreducible ρV) (h2 : irreducible ρW) (h3 : (f ≠ 0) ∧ (∀ g : G, ∀ x : V, (f (ρV g x)) = ρW g (f x))): V ≅ W :=
begin
  -- f is a nonzero G-linear map from V to W.
    -- show that V and W are isomorphic.
  -- $V^{\prime}$ is the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$.
  let V' := {x : V | f x = 0},
  -- $V^{\prime}$ is a subspace.
  have h4 : is_submodule V' := is_submodule_le (le_of_not_gt h3.left),
  -- Let $g$ in $G$ and choice of $x$ in $V^{\prime}, f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))=\left(\rho_W(g)\right)(0)=0$.
  have h5 : ∀ (g : G) (x : V'), f (ρV g x) = 0 := assume g : G, assume x : V',
    eq.symm (eq_of_sub_eq_zero (sub_self (f (ρV g x)))),
  -- But saying that $f\left(\rho_V(g)(x)\right)=0$ is the same as saying that $\rho_V(g)(x)$ is in the null space of $f: V \rightarrow W$.
  have h6 : (∀ g : G, ∀ x : V', ρV g x ∈ V') := assume g : G, assume x : V',
    by {apply h5 g x,},
  -- So $V^{\prime}$ is stable under the action of $G$; it is a subrepresentation.
  have h7 : subrepresentation ρV V' := subrepresentation_of_submodule ρV V' h4 h6,
  -- Since by assumption $V$ is irreducible, $V^{\prime}$ must be zero; so $f$ is injective.
  have h8 : V' = univ := h1 V' h4 h7,
  --
  have h9 : function.injective f := 
  begin
    --
    show function.injective f, from by 
    {
      apply function.injective_iff_has_left_inverse.mp,
      use f.left_inverse,
      obviously,
      rw ← h8,
    },
  end,
  -- By an identical argument we will show $f$ is also surjective;
  have h10 : function.surjective f := 
  begin
    --
    show function.surjective f, from by 
    {
      apply function.surjective_iff_has_right_inverse.mp,
      use f.right_inverse,
      obviously,
    },
  end,
  -- since $f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))$,
  have h11 : ∀ g : G, ∀ y : W, ∃ x : V, f x = y := assume g : G, assume y : W,
    by {use f.right_inverse y,obviously},
  -- we can conclude that for arbitrary choice of $f(x)$ in the image of $f, \rho_W(g)$ sends $f(x)$ somewhere else in the image of $f$
  have h12 : ∀ g : G, ∀ y : W, (f (ρV g (f.right_inverse y))) = (ρW g y) := assume g : G, assume y : W,
    by rw h3,
  -- So the image of $f(x)$ is a subspace $W^{\prime}$ of $W$ stable under the action of $G$, 
  let (W' : submodule ℂ W) := span ℂ V' f,
  have h13 : (∀ g : G, ∀ y : W', ρW g y ∈ W') := assume g : G, assume y : W',
    by {
      -- choice of y in the span of V' using the definition of span,
      cases y,
      -- f z = y, z ∈ V'
      cases h_property,
      rw [h_property_right,←h3.right],
      -- z is in V'
      change f z = ρW g (f (ρV g (f.right_inverse _))), rw h_property_left,
      -- z ∈ V'
      rw h8,
    },
  -- so it is a subrepresentation and $f$ must be zero or surjective.
  have h14 : subrepresentation ρW W' := subrepresentation_of_submodule ρW W' h10.left h13,
  -- By assumption it is not zero, so it is surjective, in which case it is an isomorphism.
  have h15 : W ≅ W' := h2.is_eq_span W' h10.left h14,
  -- W' ≅ V'
  show V ≅ W, from
  begin
    -- V ≅ V'
    have h16 : V ≅ V' := h15.symm.trans h8.symm,
    -- V' ≅ W'
    have h17 : V' ≅ W' := 
    begin
      unfold is_isomorphism,
      show function.bijective f, from h10.left,
    end,
    -- V ≅ W'
    have h18 : V ≅ W' := h16.trans h17,
    -- W' ≅ W
    have h19 : W' ≅ W := h15,
    -- V ≅ W
    show V ≅ W, from h18.trans h19,
  end
end

--OUTPUT 3
theorem schurs_lemma {G V W : Type*} [group G] [add_comm_group V] [add_comm_group W] [module G V] [module G W]
  {a} (f : V →ₗ[G] W) (hf : a ≠ 0 → f a ≠ 0) (hirred : begin
    have h1 : la.irreducible (G →ₗ[add_monoid] V), 
    have h2 : la.irreducible (G →ₗ[add_monoid] W), 
    have h3 : irreducible (G →ₗ[add_monoid] V ⊗ₗ[add_monoid] W),
    have h4 : irreducible (G →ₗ[add_monoid] V ⊗ₗ[add_monoid] V),
    have h5 : irreducible (G →ₗ[add_monoid] W ⊗ₗ[add_monoid] W),
end

