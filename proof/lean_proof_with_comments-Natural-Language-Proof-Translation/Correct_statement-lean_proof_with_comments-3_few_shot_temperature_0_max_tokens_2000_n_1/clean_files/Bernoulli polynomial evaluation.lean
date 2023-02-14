import number_theory.bernoulli


--OUTPUT 1
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- We apply strong induction on $n$. So, for all $m < d$, we have $B_{m} (1 + x) = B_{m} (x) + m x^{m - 1}$ and we want to show that $$B_{d} (1 + x) = B_{d} (x) + d x^{d - 1}$$
  induction n with d hd,
  { -- base case
    show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from by {
      rw polynomial.bernoulli,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      rw polynomial.
end --Needs more than 2000 tokens!

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
theorem square_of_sum (x y : ℝ) : (x + y)^2 = (x^2 + 2*x*y + y^2) := 
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
Bernoulli polynomial evaluation
Given a natural number $n$ and a rational $x$, let $B_n (x)$ denote the $n$-th Bernoulli polynomial evaluated at $x$. Then, $$B_n (1 + x) = B_n (x) + n x^{n - 1}$$
`proof`
We apply strong induction on $n$. So, for all $m < d$, we have $B_{m} (1 + x) = B_{m} (x) + m x^{m - 1}$ and we want to show that $$B_{d} (1 + x) = B_{d} (x) + d x^{d - 1}$$
Multiplying both sides by $d + 1$, and using the fact that, for all $l \in \mathbb{N}$, $\sum_{k = 0}^{l} {l + 1 \choose k} B_k = (l + 1) X^l$ (where $B_k$ is the $k$-th Bernoulli number), we get that 
$$ (d + 1) (1 + x)^d - (d + 1) x^d = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
The conclusion then follows easily.

QED

-/
theorem  bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
FEW SHOT PROMPTS TO CODEX(END)-/
