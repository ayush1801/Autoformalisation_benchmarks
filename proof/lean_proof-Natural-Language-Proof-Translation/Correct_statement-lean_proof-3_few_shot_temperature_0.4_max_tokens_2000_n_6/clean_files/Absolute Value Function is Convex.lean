
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
  have h4 : ?? * x + ?? * y = ?? * x + ?? * y, from by {ring},
  have h5 : abs (?? * x + ?? * y) ??? abs (?? * x) + abs (?? * y), from by {rw h4, apply abs_add},
  have h6 : abs (?? * x) + abs (?? * y) = ?? * abs x + ?? * abs y, from by {rw ??? abs_mul, rw ??? abs_mul, ring},
  show abs (?? * x + ?? * y) ??? ?? * abs x + ?? * abs y, from by {rw h6 at h5, exact h5},
end

--OUTPUT 2
theorem begin
  assume x y : ???,
  assume (?? : ???) (h?? : 0 ??? ??) (?? : ???) (h?? : 0 ??? ??) (h1 : ?? + ?? = 1),
  calc abs (??*x + ??*y) = abs (??*x) + abs (??*y) : by rw abs_add
  ... = abs ?? * abs x + abs ?? * abs y : by rw [abs_mul, abs_mul]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]
  ... = ?? * abs x + ?? * abs y : by rw [??? abs_of_nonneg h??, ??? abs_of_nonneg h??]

end --Needs more than 2000 tokens!

--OUTPUT 3
theorem begin
  assume (x y : ???) (?? ?? : ???) (h???? : 0 ??? ?? ??? 0 ??? ?? ??? ?? + ?? = 1),
  have h1 : abs (??*x + ??*y) = abs (??*x) + abs (??*y), from by {
    rw ??? abs_add (??*x) (??*y),
    rw ??? abs_mul ?? x,
    rw ??? abs_mul ?? y,
    rw ??? add_mul,
    rw ??? add_mul,
    rw ??? mul_one,
    rw ??? mul_one,
    rw ??? h????.right,
    ring,
  },
  have h2 : abs (??*x + ??*y) ??? abs (??*x) + abs (??*y), from by {
    apply abs_add_le (??*x) (??*y),
  },
  have h3 : abs (??*x + ??*y) ??? ??*abs x + ??*abs y, from by {
    rw ??? h1,
    apply h2,
  },
  show abs (??*x + ??*y) ??? ??*abs x + ??*abs y, from h3,
end

--OUTPUT 4
theorem begin
  assume (x y : ???) (?? ?? : ???) (h???? : ?? ??? 0) (h???? : ?? ??? 0) (h????1 : ?? + ?? = 1),
  calc abs (?? * x + ?? * y) = abs (?? * x) + abs (?? * y) : by rw abs_add
  ... = abs ?? * abs x + abs ?? * abs y : by rw abs_mul
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h????
  ... = ?? * abs x + ?? * abs y : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x) + ?? * abs (y) : by rw abs_of_nonneg h????
  ... = ?? * abs (x)
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem begin
  assume x y : ???,
  assume (?? : ???) (h?? : 0 ??? ??) (?? : ???) (h?? : 0 ??? ??) (h1 : ?? + ?? = 1),
  calc abs (?? * x + ?? * y) = abs (?? * x + ?? * y) : by refl
  ... = abs ((?? * x) + (?? * y)) : by refl
  ... ??? abs (?? * x) + abs (?? * y) : by apply abs_add
  ... = abs ?? * abs x + abs ?? * abs y : by apply abs_mul
  ... = ?? * abs x + ?? * abs y : by {rw abs_of_nonneg h??, rw abs_of_nonneg h??}
  ... = ?? * abs x + ?? * abs y : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? * abs (y) : by refl
  ... = ?? * abs (x) + ?? *
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem begin
  assume x y : ???, assume ?? ?? : ???, assume h???? : ?? + ?? = 1,
  have h1 : (?? * x + ?? * y) ??? ???, from by {
    have h2 : (?? * x + ?? * y) ??? set.Icc (-???) ???, from by {
      have h3 : (?? * x + ?? * y) ??? set.Icc (-???) (?? * x + ?? * y), from by {
        have h4 : (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) ???, from by {
          have h5 : (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) (?? * x + ?? * y), from by {
            have h6 : (?? * x + ?? * y) = (?? * x + ?? * y), from rfl,
            show (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) (?? * x + ?? * y), from by {
              apply set.mem_Icc.mpr, split,
              exact h6, exact h6,
            },
          },
          show (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) ???, from by {
            apply set.mem_Icc.mpr, split,
            exact h5, apply set.mem_Icc.mpr,
            split, apply set.mem_univ,
            apply set.mem_univ,
          },
        },
        show (?? * x + ?? * y) ??? set.Icc (-???) (?? * x + ?? * y), from by {
          apply set.mem_Icc.mpr, split,
          apply set.mem_Icc.mpr, split,
          apply set.mem_univ, exact h4,
        },
      },
      show (?? * x + ?? * y) ??? set.Icc (-???) ???, from by {
        apply set.mem_Icc.mpr, split,
        exact h3, apply set.mem_Icc.mpr,
        split, apply set.mem_univ,
        apply set.mem_univ,
      },
    },
    show (?? * x + ?? * y) ??? ???, from by {
      apply set.mem_univ, exact h2,
    },
  },
  have h2 : (?? * x + ?? * y) ??? set.Icc (-???) ???, from by {
    have h3 : (?? * x + ?? * y) ??? set.Icc (-???) (?? * x + ?? * y), from by {
      have h4 : (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) ???, from by {
        have h5 : (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) (?? * x + ?? * y), from by {
          have h6 : (?? * x + ?? * y) = (?? * x + ?? * y), from rfl,
          show (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) (?? * x + ?? * y), from by {
            apply set.mem_Icc.mpr, split,
            exact h6, exact h6,
          },
        },
        show (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) ???, from by {
          apply set.mem_Icc.mpr, split,
          exact h5, apply set.mem_Icc.mpr,
          split, apply set.mem_univ,
          apply set.mem_univ,
        },
      },
      show (?? * x + ?? * y) ??? set.Icc (-???) (?? * x + ?? * y), from by {
        apply set.mem_Icc.mpr, split,
        apply set.mem_Icc.mpr, split,
        apply set.mem_univ, exact h4,
      },
    },
    show (?? * x + ?? * y) ??? set.Icc (-???) ???, from by {
      apply set.mem_Icc.mpr, split,
      exact h3, apply set.mem_Icc.mpr,
      split, apply set.mem_univ,
      apply set.mem_univ,
    },
  },
  have h3 : (?? * x + ?? * y) ??? ???, from by {
    apply set.mem_univ, exact h2,
  },
  have h4 : (?? * x + ?? * y) ??? set.Icc (-???) ???, from by {
    have h5 : (?? * x + ?? * y) ??? set.Icc (-???) (?? * x + ?? * y), from by {
      have h6 : (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) ???, from by {
        have h7 : (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) (?? * x + ?? * y), from by {
          have h8 : (?? * x + ?? * y) = (?? * x + ?? * y), from rfl,
          show (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) (?? * x + ?? * y), from by {
            apply set.mem_Icc.mpr, split,
            exact h8, exact h8,
          },
        },
        show (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) ???, from by {
          apply set.mem_Icc.mpr, split,
          exact h7, apply set.mem_Icc.mpr,
          split, apply set.mem_univ,
          apply set.mem_univ,
        },
      },
      show (?? * x + ?? * y) ??? set.Icc (-???) (?? * x + ?? * y), from by {
        apply set.mem_Icc.mpr, split,
        apply set.mem_Icc.mpr, split,
        apply set.mem_univ, exact h6,
      },
    },
    show (?? * x + ?? * y) ??? set.Icc (-???) ???, from by {
      apply set.mem_Icc.mpr, split,
      exact h5, apply set.mem_Icc.mpr,
      split, apply set.mem_univ,
      apply set.mem_univ,
    },
  },
  have h5 : (?? * x + ?? * y) ??? ???, from by {
    apply set.mem_univ, exact h4,
  },
  have h6 : (?? * x + ?? * y) ??? set.Icc (-???) ???, from by {
    have h7 : (?? * x + ?? * y) ??? set.Icc (-???) (?? * x + ?? * y), from by {
      have h8 : (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) ???, from by {
        have h9 : (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) (?? * x + ?? * y), from by {
          have h10 : (?? * x + ?? * y) = (?? * x + ?? * y), from rfl,
          show (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) (?? * x + ?? * y), from by {
            apply set.mem_Icc.mpr, split,
            exact h10, exact h10,
          },
        },
        show (?? * x + ?? * y) ??? set.Icc (?? * x + ?? * y) ???, from by {
          apply set.mem_Icc.mpr, split
end --Needs more than 2000 tokens!

