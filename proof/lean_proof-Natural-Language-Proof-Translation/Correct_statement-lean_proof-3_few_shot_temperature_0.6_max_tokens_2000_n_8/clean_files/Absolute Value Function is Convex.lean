
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
theorem power_set_intersection_closed {?? : Type*} (S : set ??) : ??? A B ??? ???? S, (A ??? B) ??? ???? S :=
begin
  assume (A : set ??) (hA : A ??? ???? S) (B : set ??) (hB : B ??? ???? S),
  have h1 : (A ??? S) ??? (B ??? S), from by {split,apply set.subset_of_mem_powerset,exact hA,apply set.subset_of_mem_powerset,exact hB},
  have h2 : (A ??? B) ??? A, from by apply set.inter_subset_left,
  have h3 : (A ??? B) ??? S, from by {apply set.subset.trans h2 h1.left},
  show (A ??? B) ???  ???? S, from by {apply set.mem_powerset h3},
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
theorem square_of_sum (x y : ???) : (x + y)^2 = (x^2 + 2*x*y + y^2)
begin
  calc (x + y)^2 = (x+y)*(x+y) : by rw sq
  ... = x*(x+y) + y*(x+y) : by rw add_mul
  ... = x*x + x*y + y*x + y*y : by {rw [mul_comm x (x+y),mul_comm y (x+y)], rw [add_mul,add_mul], ring}
  ... = x^2 + 2*x*y + y^2 : by {repeat {rw ??? sq}, rw mul_comm y x, ring}
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
theorem group_identity_unique {G : Type*} [group G] : ???! e : G, ??? a : G, e * a = a ??? a * e = a :=
begin
  have h1 : ??? a b : G, ???! x : G, a * x = b, from by {
    assume a b : G, use a????? * b, obviously, },
  have h2 : ??? a b : G, ???! y : G, y * a = b, from by {
    assume a b : G, use b * a?????, obviously, }, 

  have h3 : ??? a : G, ???! x : G, a * x = a, from 
    assume a : G, h1 a a,
  have h4 : ??? a : G, ???! y : G, y * a = a, from
    assume a : G, h2 a a,

  have h5 : ??? a : G, classical.some (h3 a).exists = (1 : G), from assume a :G,
    exists_unique.unique (h3 a) (classical.some_spec (exists_unique.exists (h3 a)))
    (mul_one a),
  have h6 : ??? a : G, classical.some (h4 a).exists = (1 : G), from assume a : G,
    exists_unique.unique (h4 a) (classical.some_spec (exists_unique.exists (h4 a))) (one_mul a), 

  show ???! e : G, ??? a : G, e * a = a ??? a * e = a, from by {
    use (1 : G),
    have h7 : ??? e : G, (??? a : G, e * a = a ??? a * e = a) ??? e = 1, from by {
      assume (e : G) (hident : ??? a : G, e * a = a ??? a * e = a),
      have h8 : ??? a : G, e = classical.some (h3 a).exists, from assume (a : G),
        exists_unique.unique (h3 a) (hident a).right
        (classical.some_spec (exists_unique.exists (h3 a))), 
      have h9 : ??? a : G, e = classical.some (h4 a).exists, from assume (a : G),
        exists_unique.unique (h4 a) (hident a).left
        (classical.some_spec (exists_unique.exists (h4 a))),
      show e = (1 : G), from eq.trans (h9 e) (h6 _),     
    },
    exact ???by obviously, h7???,
  }
end

/--`theorem`
Absolute Value Function is Convex
Let $f: \R \to \R$ be the absolute value function on the real numbers.

Then $f$ is convex.
`proof`
Let $x, y \in \R$.

Let $\alpha, \beta \in \R_{\ge 0}$ where $\alpha + \beta = 1$.

{{begin-eqn}}
{{eqn | l = \map f {\alpha x + \beta y}
      | r = \size {\alpha x + \beta y}
      | c = Definition of $f$
}}
{{eqn | o = \le
      | r = \size {\alpha x} + \size {\beta y}
      | c = Triangle Inequality for Real Numbers
}}
{{eqn | r = \size \alpha \size x + \size \beta \size y
      | c = Absolute Value of Product
}}
{{eqn | r = \alpha \size x + \beta \size y
      | c = {{Defof|Absolute Value}}
}}
{{eqn | r = \alpha \, \map f x + \beta \, \map f y
      | c = Definition of $f$
}}
{{end-eqn}}

Hence the result by definition of Convex Real Function.
{{qed}}
-/
theorem  absolute_value_function_convex : convex_on ??? (@set.univ ???) abs :=

FEW SHOT PROMPTS TO CODEX(END)-/
--OUTPUT 1
theorem begin
  assume x y : ???,
  assume ?? ?? : ???,
  assume h1 : ?? ??? 0,
  assume h2 : ?? ??? 0,
  assume h3 : ?? + ?? = 1,
  calc abs (??*x + ??*y) = abs (??*x) + abs (??*y) : by rw abs_add
  ... = abs ?? * abs x + abs ?? * abs y : by rw abs_mul
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h2
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x) + ?? * abs (y)) : by refl
  ... = (?? * abs (x)
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem begin
  assume (x y : ???) (hx : x ??? set.univ) (hy : y ??? set.univ) (?? ?? : ???) (h?? : 0 ??? ??) (h?? : 0 ??? ??) (h???? : ?? + ?? = 1),
  have h1 : abs (?? * x + ?? * y) = abs (?? * x) + abs (?? * y), from by {
    rw ??? abs_add (?? * x) (?? * y),
    rw ??? abs_mul ?? x,
    rw ??? abs_mul ?? y,
    ring,
  },
  have h2 : ?? * abs x + ?? * abs y = ?? * abs x + ?? * abs y, from by {
    ring,
  },
  show abs (?? * x + ?? * y) ??? ?? * abs x + ?? * abs y, from by {
    rw h1,
    rw h2,
    apply le.refl,
  },
end

--OUTPUT 3
theorem begin
  assume (x y : ???) (hx : x ??? set.univ) (hy : y ??? set.univ),
  assume (?? ?? : ???) (ha : 0 ??? ??) (hb : 0 ??? ??) (h???? : ?? + ?? = 1),
  have h1 : ?? * x + ?? * y ??? univ, from and.intro (real.mul_self_nonneg (?? * x + ?? * y))
    (real.mul_self_nonneg (?? * x + ?? * y)),
  have h2 : abs (?? * x + ?? * y) ??? abs (?? * x) + abs (?? * y), from by {
    have h3 : ?? * x + ?? * y = ?? * x + ?? * y, from rfl,
    have h4 : abs (?? * x + ?? * y) = abs (?? * x + ?? * y), from rfl,
    rw [h4,h3], apply abs_add,
  },
  have h3 : abs (?? * x) = ?? * abs x, from rfl,
  have h4 : abs (?? * y) = ?? * abs y, from rfl,
  have h5 : abs (?? * x + ?? * y) = ?? * abs x + ?? * abs y, from by rw [h3,h4,h2],
  have h6 : ?? * abs x + ?? * abs y ??? ?? * abs x + ?? * abs y, from by {apply le_of_eq, exact h5},
  have h7 : abs (?? * x + ?? * y) = ?? * abs x + ?? * abs y, from rfl,
  show abs (?? * x + ?? * y) ??? ?? * abs x + ?? * abs y, from by {apply le_of_eq, exact h7},
end

--OUTPUT 4
theorem begin
  assume x y : ???,
  assume ?? ?? : ???,
  assume h1 : (?? ??? 0) ??? (?? ??? 0) ??? (?? + ?? = (1 : ???)),
  calc abs (??*x + ??*y) = (??*x + ??*y) : by {rw abs_of_nonneg (add_nonneg (mul_nonneg h1.left h1.1) (mul_nonneg h1.right h1.1))}
  ... = abs ?? * abs x + abs ?? * abs y : by {rw [abs_mul,abs_mul], ring}
  ... = (?? * abs x + ?? * abs y) : by {rw abs_of_nonneg (add_nonneg (mul_nonneg h1.left h1.1) (mul_nonneg h1.right h1.1))},
end

--OUTPUT 5
theorem begin
  assume (x y : ???) (?? ?? : ???) (h1 : ?? ??? 0) (h2 : ?? ??? 0) (h3 : ?? + ?? = 1),
  have h4 : abs (?? * x + ?? * y) ??? abs (?? * x) + abs (?? * y), from by {
    calc abs (?? * x + ?? * y) = abs (?? * x) + abs (?? * y) : abs_add (?? * x) (?? * y)
    ... ??? abs (?? * x) + abs (?? * y) : by apply le_abs_self
  },
  have h5 : abs (?? * x) = ?? * abs x, from by {rw ??? abs_mul ?? x, ring},
  have h6 : abs (?? * y) = ?? * abs y, from by {rw ??? abs_mul ?? y, ring},
  rw [h5,h6] at h4,
  show abs (?? * x + ?? * y) ??? ?? * abs x + ?? * abs y, from h4,
end

--OUTPUT 6
theorem begin
  rintros (x y : ???) (?? ?? : ???) ???h??,h?????,
  have h1 : (?? + ?? = 1), from by rw [eq_comm, ??? add_assoc, add_comm ?? ??, add_left_cancel h??],
  have h2 : ?? + ?? > 0, from by {rw h1, apply add_pos_of_nonneg_of_nonneg h?? h??},
  have h3 : (?? + ??)????? * (?? + ??) = 1, from by {apply mul_inv_cancel h2,},
  have h4 : ?? + ?? = (?? + ??)????? * (?? + ??), from by rw h3,
  have h5 : abs (?? * x + ?? * y) ??? abs (?? * x) + abs (?? * y), from
    by {apply abs_add_le_abs_add_abs,},
  have h6 : abs (?? * x + ?? * y) = abs (?? * x) + abs (?? * y), from
    le_antisymm h5 (abs_add_le_abs_add_abs),
  have h7 : ?? * abs x + ?? * abs y = abs (?? * x) + abs (?? * y), from
    by {rw [??? abs_mul,??? abs_mul], ring},
  have h8 : ?? * abs x + ?? * abs y = abs (?? * x + ?? * y), from
    by {rw [??? h7, ??? h6],},
  have h9 : ?? * (abs x) + ?? * (abs y) = abs (?? * x + ?? * y), from
    by {rw [h8],},
  have h10 : (?? * (abs x) + ?? * (abs y)) * (?? + ??)????? = (abs (?? * x + ?? * y)) * (?? + ??)?????, from
    by {rw [h9],},
  show abs (?? * x + ?? * y) ??? (?? * abs x + ?? * abs y), from
    by {rw [??? h10, ??? h4], apply mul_le_mul_of_nonneg_left h2, rw abs_nonneg},
end

--OUTPUT 7
theorem begin
  assume x y : ???,
  assume ?????, ??, hab???,
  have h1 : abs (??*x + ??*y) = abs (??*x) + abs (??*y), from by {
    calc abs (??*x + ??*y) = abs ((??*x) + (??*y)) : by obviously
    ... ??? abs (??*x) + abs (??*y) : by apply abs_add
    ... = abs ?? * abs x + abs ?? * abs y : by obviously
    ... = abs ?? * abs x + abs ?? * abs y : by obviously
    ... = abs ?? * abs x + abs ?? * abs y : by obviously
    ... = abs ?? * (abs x) + abs ?? * (abs y) : by obviously
    ... = ?? * abs x + ?? * abs y : by obviously
    ... = ?? * abs x + ?? * abs y : by obviously
    ... = ?? * abs x + ?? * abs y : by obviously
    ... = ?? * abs x + ?? * abs y : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (abs x) + ?? * (abs y) : by obviously
    ... = ?? * (
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem begin
  assume (x y : ???) (?? ?? : ???), assume (h1 : ?? ??? 0) (h2 : ?? ??? 0) (h3 : ?? + ?? = (1 : ???)),
  calc abs (??*x + ??*y) = abs (??*x) + abs (??*y) : by rw ??? abs_add (??*x) (??*y)
  ... = abs ?? * abs x + abs ?? * abs y : by rw abs_mul
  ... = abs ?? * abs x + abs ?? * abs y : by rw abs_of_nonneg h1
  ... = abs ?? * abs x + abs ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw ??? abs_mul
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h1
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h2
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h3

end --Needs more than 2000 tokens!

