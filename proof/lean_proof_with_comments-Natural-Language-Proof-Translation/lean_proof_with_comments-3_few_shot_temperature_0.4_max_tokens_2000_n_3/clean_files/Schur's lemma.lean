
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
theorem schur_lemma (G : Type*) [group G] (V W : Type*) [add_comm_group V] [add_comm_group W] [vector_space ℂ V] [vector_space ℂ W] [rep G V] [rep G W] (hirr : irreducible G V) (hirr' : irreducible G W) (h : V ≃ₗ[ℂ] W) : V ≅ₗ[ℂ] W :=
begin
  -- Suppose $f$ is a nonzero $G$-linear map from $V$ to $W$.
  assume f : V →ₗ[ℂ] W,
  assume hf : f ≠ 0,
  have h1 : f ≠ 0, from by {assume h2 : f = 0, have h3 : V ≅ₗ[ℂ] W, from by {rw h2, exact zero_equiv}, exact hirr (hirr' h3)},
  -- We will prove that $V$ and $W$ are isomorphic.
  have h2 : V ≅ₗ[ℂ] W, from by {
    -- Let $V^{\prime}$ be the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$. (It is easy to check that this is a subspace.)
    let V' : set V := {x : V | f x = 0},
    have hV' : is_submodule ℂ V' := by {apply is_submodule.of_subset, apply set.subset_range_iff.mpr, exact λ x hx, hx.symm},
    have hV'1 : V' ⊆ V := by {apply set.subset_range_iff.mpr, exact λ x hx, hx.symm},
    have hV'2 : V' ⊆ V' := by {apply set.subset_range_iff.mpr, exact λ x hx, hx.symm},
    -- By the assumption that $f$ is $G$-linear, for every $g$ in $G$ and choice of $x$ in $V^{\prime}, f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))=\left(\rho_W(g)\right)(0)=0$.
    have h3 : ∀ g : G, ∀ x : V', f (g • x) = 0, from by {
      assume g : G,
      assume x : V',
      have h4 : f (g • x) = f (g • x), from by obviously,
      have h5 : f (g • x) = g • (f x), from by {rw ← rep.map_smul g, rw ← rep.map_smul g, rw ← h, rw ← rep.map_smul g, rw ← rep.map_smul g, rw ← h, obviously,},
      have h6 : g • (f x) = 0, from by {rw ← h5, rw ← set.mem_range_iff.mpr x, obviously,},
      have h7 : g • (f x) = g • 0, from by {rw ← h6, obviously,},
      have h8 : g • 0 = 0, from by {rw ← rep.map_smul g, rw ← h, rw ← rep.map_smul g, rw ← h, obviously,},
      have h9 : g • (f x) = 0, from by {rw ← h7, rw h8, obviously,},
      rw ← h9,
      obviously,
    },
    -- But saying that $f\left(\rho_V(g)(x)\right)=0$ is the same as saying that $\rho_V(g)(x)$ is in the null space of $f: V \rightarrow W$. So $V^{\prime}$ is stable under the action of $G$; it is a subrepresentation.
    have h4 : ∀ g : G, ∀ x : V', g • x ∈ V', from by {
      assume g : G,
      assume x : V',
      have h5 : g • x ∈ V', from by {rw ← set.mem_range_iff.mpr x, rw ← set.mem_range_iff.mpr x, rw ← h3, obviously,},
      rw ← set.mem_range_iff.mpr x,
      rw ← set.mem_range_iff.mpr x,
      rw ← h3,
      obviously,
    },
    -- Since by assumption $V$ is irreducible, $V^{\prime}$ must be zero; so $f$ is injective.
    have h5 : V' = {0}, from by {
      have h6 : V' ≠ (0 : set V), from by {
        assume h7 : V' = (0 : set V),
        have h8 : V' = 0, from by {rw ← h7, obviously,},
        have h9 : V' = {0}, from by {rw ← h8, obviously,},
        have h10 : V' ≅ₗ[ℂ] ℂ, from by {rw ← h9, rw zero_equiv, obviously,},
        have h11 : V' ≅ₗ[ℂ] V, from by {rw ← h9, rw zero_equiv, obviously,},
        have h12 : V ≅ₗ[ℂ] V', from by {rw ← h9, rw zero_equiv, obviously,},
        have h13 : V ≅ₗ[ℂ] ℂ, from by {rw ← h9, rw zero_equiv, obviously,},
        have h14 : V ≅ₗ[ℂ] V, from by {exact hirr (hirr' h13),},
        have h15 : V ≅ₗ[ℂ] V', from by {exact hirr (hirr' h12),},
        have h16 : V ≅ₗ[ℂ] ℂ, from by {exact hirr (hirr' h11),},
        have h17 : V ≅ₗ[ℂ] V, from by {exact hirr (hirr' h10),},
        have h18 : V ≅ₗ[ℂ] V', from by {exact hirr (hirr' h14),},
        have h19 : V ≅ₗ[ℂ] ℂ, from by {exact hirr (hirr' h17),},
        have h20 : V ≅ₗ[ℂ] V, from by {exact hirr (hirr' h16),},
        have h21 : V ≅ₗ[ℂ] V', from by {exact hirr (hirr' h15),},
        have h22 : V ≅ₗ[ℂ] ℂ, from by {exact hirr (hirr' h18),},
        have h23 : V ≅ₗ[ℂ] V, from by {exact hirr (hirr' h20),},
        have h24 : V ≅ₗ[ℂ] V', from by {exact hirr (hirr' h21),},
        have h25 : V ≅ₗ[ℂ] ℂ, from by {exact hirr (hirr' h24),},
        have h26 : V ≅ₗ[ℂ] V, from by {exact hirr (hirr' h23),},
        have h27 : V ≅ₗ[ℂ] V', from by {exact hirr (hirr' h26),},
        have h28 : V ≅ₗ[ℂ] ℂ, from by {exact hirr (hirr' h25),},
        have h29 : V ≅ₗ[
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem schurs_lemma {G : Type*} {V W : Type*} [group G] [add_comm_group V] [add_comm_group W]
  [vector_space ℂ V] [vector_space ℂ W] [irreducible G V] [irreducible G W] : 
  (V ≃ₗ[ℂ] W) → (∃ g : G →* V →* W, g ≠ 0) :=
begin
  assume (h1 : V ≃ₗ[ℂ] W),
  have h2 : ∃ g : G →* V →* W, g ≠ 0, from by {
    use linear_map.to_add_group_hom (h1.to_linear_equiv.to_fun).to_add_group_hom,
    have h3 : linear_map.to_add_group_hom (h1.to_linear_equiv.to_fun).to_add_group_hom ≠ 0, from by {
      assume h4 : linear_map.to_add_group_hom (h1.to_linear_equiv.to_fun).to_add_group_hom = 0,
      have h5 : linear_map.to_add_group_hom (h1.to_linear_equiv.to_fun).to_add_group_hom = 0, from by {
        rw ← h4,
        exact (h1.to_linear_equiv.to_fun).to_add_group_hom,
      },
      have h6 : h1.to_linear_equiv.to_fun = 0, from by {
        rw ← h5,
        exact linear_map.to_add_group_hom_eq_zero,
      },
      have h7 : h1.to_linear_equiv.to_fun ≠ 0, from by {
        assume h8 : h1.to_linear_equiv.to_fun = 0,
        have h9 : h1.to_linear_equiv = 0, from by {
          rw ← h8,
          exact linear_equiv.to_fun_eq_zero,
        },
        have h10 : h1 = 0, from by {
          rw ← h9,
          exact linear_equiv.to_linear_map_eq_zero,
        },
        have h11 : h1 ≠ 0, from by {
          assume h12 : h1 = 0,
          have h13 : h1.to_linear_equiv.to_fun = 0, from by {
            rw ← h12,
            exact linear_equiv.to_linear_map_eq_zero,
          },
          have h14 : h1.to_linear_equiv.to_fun ≠ 0, from by {
            assume h15 : h1.to_linear_equiv.to_fun = 0,
            have h16 : h1.to_linear_equiv = 0, from by {
              rw ← h15,
              exact linear_equiv.to_fun_eq_zero,
            },
            have h17 : h1 = 0, from by {
              rw ← h16,
              exact linear_equiv.to_linear_map_eq_zero,
            },
            exact h11 h17,
          },
          exact h14,
        },
        exact h11 h10,
      },
      exact h7 h6,
    },
    exact h3,
  },
  exact h2,
end

--OUTPUT 3
theorem schurs_lemma {V W : Type*} [add_comm_group V] [add_comm_group W] [vector_space ℂ V] [vector_space ℂ W] [finite_dimensional ℂ V] [finite_dimensional ℂ W] (G : Type*) [group G] (ρV : G → linear_map V V) (ρW : G → linear_map W W) (hirrV : irreducible ρV) (hirrW : irreducible ρW) (hnotiso : ¬(V ≃ₗ[ℂ] W)) : ∀ f : V →ₗ[ℂ] W, f = 0 :=
begin
  assume f : V →ₗ[ℂ] W,
  -- Suppose $f$ is a nonzero $G$-linear map from $V$ to $W$.
  have hf : f ≠ 0, from by {assume h, apply hnotiso, exact linear_equiv.of_linear h},

  -- We will prove that $V$ and $W$ are isomorphic.
  have hiso : V ≃ₗ[ℂ] W, from by {
    -- Let $V^{\prime}$ be the kernel, or null space, of $f$ in $V$, the subspace of all $x$ in $V$ for which $f x=0$. (It is easy to check that this is a subspace.)
    let V' := f.ker,
    have hsubV' : is_submodule V' ⊆ V, from by {
      assume v : V', assume hv : v ∈ V',
      have hv' : v ∈ f.ker, from by {apply hv},
      have hv'' : f v = 0, from by {apply hv'},
      show v ∈ V, from by {rw ← hv'', apply f.map_zero},
    },
    have hsubV'2 : is_submodule V' ⊆ V, from by {
      assume v : V', assume hv : v ∈ V',
      have hv' : v ∈ f.ker, from by {apply hv},
      have hv'' : f v = 0, from by {apply hv'},
      show v ∈ V, from by {rw ← hv'', apply f.map_zero},
    },
    have hsubV'3 : add_subgroup V' ⊆ V, from by {
      assume v₁ v₂ : V',
      assume hv₁ : v₁ ∈ V',
      assume hv₂ : v₂ ∈ V',
      have hv₁' : v₁ ∈ f.ker, from by {apply hv₁},
      have hv₂' : v₂ ∈ f.ker, from by {apply hv₂},
      have hv₁'' : f v₁ = 0, from by {apply hv₁'},
      have hv₂'' : f v₂ = 0, from by {apply hv₂'},
      have hv₁''' : f (v₁ + v₂) = 0, from by {rw [← hv₁'', ← hv₂''], rw [← f.map_add], apply f.map_zero},
      have hv₁'''' : v₁ + v₂ ∈ f.ker, from by {rw hv₁''', apply f.ker_zero},
      show v₁ + v₂ ∈ V, from by {rw ← hv₁''', apply f.map_zero},
    },
    have hsubV'4 : smul_subgroup ℂ V' ⊆ V, from by {
      assume (c : ℂ) (v : V'),
      assume hv : v ∈ V',
      have hv' : v ∈ f.ker, from by {apply hv},
      have hv'' : f v = 0, from by {apply hv'},
      have hv''' : f (c • v) = 0, from by {rw [← hv'', ← f.map_smul], apply f.map_zero},
      have hv'''' : c • v ∈ f.ker, from by {rw hv''', apply f.ker_zero},
      show c • v ∈ V, from by {rw ← hv''', apply f.map_zero},
    },
    have hV' : add_subgroup V' ⊆ V, from by {
      assume v₁ v₂ : V',
      assume hv₁ : v₁ ∈ V',
      assume hv₂ : v₂ ∈ V',
      have hv₁' : v₁ ∈ f.ker, from by {apply hv₁},
      have hv₂' : v₂ ∈ f.ker, from by {apply hv₂},
      have hv₁'' : f v₁ = 0, from by {apply hv₁'},
      have hv₂'' : f v₂ = 0, from by {apply hv₂'},
      have hv₁''' : f (v₁ + v₂) = 0, from by {rw [← hv₁'', ← hv₂''], rw [← f.map_add], apply f.map_zero},
      have hv₁'''' : v₁ + v₂ ∈ f.ker, from by {rw hv₁''', apply f.ker_zero},
      show v₁ + v₂ ∈ V, from by {rw ← hv₁''', apply f.map_zero},
    },
    have hV'2 : smul_subgroup ℂ V' ⊆ V, from by {
      assume (c : ℂ) (v : V'),
      assume hv : v ∈ V',
      have hv' : v ∈ f.ker, from by {apply hv},
      have hv'' : f v = 0, from by {apply hv'},
      have hv''' : f (c • v) = 0, from by {rw [← hv'', ← f.map_smul], apply f.map_zero},
      have hv'''' : c • v ∈ f.ker, from by {rw hv''', apply f.ker_zero},
      show c • v ∈ V, from by {rw ← hv''', apply f.map_zero},
    },

    -- By the assumption that $f$ is $G$-linear, for every $g$ in $G$ and choice of $x$ in $V^{\prime}, f\left(\left(\rho_V(g)\right)(x)\right)=\left(\rho_W(g)\right)(f(x))=\left(\rho_W(g)\right)(0)=0$.
    have hGlin : ∀ g : G, ∀ v : V', f (ρV g v) = ρW g (f v), from by {
      assume g : G,
      assume v : V',
      have hv : v ∈ V', from by {apply v},
      have hv' : v ∈ f.ker, from by {apply hv},
      have hv'' : f v = 0, from by {apply hv'},
      show f (ρV g v) = ρW g (f v), from by {rw [← hv'', ← f.map_zero], rw [← f.map_smul], rw [← f.map_zero], rw [← f.map_add], rw [← f.map_zero], rw [← f.map_smul], rw [← f.map_zero], rw [← f.map_add], rw [← f.map_zero], rw [← f.map_smul], rw [← f.map_zero], rw [←
end --Needs more than 2000 tokens!

