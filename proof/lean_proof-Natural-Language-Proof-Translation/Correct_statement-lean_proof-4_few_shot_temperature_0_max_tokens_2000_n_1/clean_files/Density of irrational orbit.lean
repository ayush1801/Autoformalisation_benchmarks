import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j h,
    assume h2 : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h3 : α * ↑i - ↑(int.floor (α * ↑i)) = α * ↑j - ↑(int.floor (α * ↑j)), from by {
      rw h2,
    },
    have h4 : α = (int.floor (α * ↑i) - int.floor (α * ↑j)) / (i - j), from by {
      rw [← int.cast_add, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast_sub, ← int.cast_mul, ← int.cast
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
theorem square_of_sum (x y : ℝ) : (x + y)^2 = (x^2 + 2*x*y + y^2) := 
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
Squeeze Theorem for Real Numbers
Let $\sequence {x_n}$, $\sequence {y_n}$ and $\sequence {z_n}$ be sequences in $\R$.

Let $\sequence {y_n}$ and $\sequence {z_n}$ both be convergent to the following limit:
:$\ds \lim_{n \mathop \to \infty} y_n = l, \lim_{n \mathop \to \infty} z_n = l$

Suppose that:
:$\forall n \in \N: y_n \le x_n \le z_n$


Then:
:$x_n \to l$ as $n \to \infty$
that is:
:$\ds \lim_{n \mathop \to \infty} x_n = l$

`proof`
From Negative of Absolute Value:
:$\size {x - l} < \epsilon \iff l - \epsilon < x < l + \epsilon$

Let $\epsilon > 0$.

We need to prove that:
:$\exists N: \forall n > N: \size {x_n - l} < \epsilon$

As $\ds \lim_{n \mathop \to \infty} y_n = l$ we know that:
:$\exists N_1: \forall n > N_1: \size {y_n - l} < \epsilon$

As $\ds \lim_{n \mathop \to \infty} z_n = l$ we know that:
:$\exists N_2: \forall n > N_2: \size {z_n - l} < \epsilon$


Let $N = \max \set {N_1, N_2}$.

Then if $n > N$, it follows that $n > N_1$ and $n > N_2$.

So:
:$\forall n > N: l - \epsilon < y_n < l + \epsilon$
:$\forall n > N: l - \epsilon < z_n < l + \epsilon$

But:
:$\forall n \in \N: y_n \le x_n \le z_n$

So:
:$\forall n > N: l - \epsilon < y_n \le x_n \le z_n < l + \epsilon$

and so:
:$\forall n > N: l - \epsilon < x_n < l + \epsilon$

So:
:$\forall n > N: \size {x_n - l} < \epsilon$

Hence the result.
{{qed}}

-/
theorem squeeze_theorem_real_numbers (x y z : ℕ → ℝ) (l : ℝ) : 
let seq_limit : (ℕ → ℝ) → ℝ → Prop :=  λ (u : ℕ → ℝ) (l : ℝ), ∀ ε > 0, ∃ N, ∀ n > N, |u n - l| < ε in
 seq_limit y l → seq_limit z l →  (∀ n : ℕ, (y n) ≤ (x n) ∧ (x n) ≤ (z n)) → seq_limit x l :=
begin
  assume seq_limit (h2 : seq_limit y l) (h3 : seq_limit z l) (h4 : ∀ (n : ℕ), y n ≤ x n ∧ x n ≤ z n) (ε), 

  have h5 : ∀ x, |x - l| < ε ↔ (((l - ε) < x) ∧ (x < (l + ε))), 
  from by 
  {
    intro x0,
    have h6 : |x0 - l| < ε ↔ ((x0 - l) < ε) ∧ ((l - x0) < ε), 
    from abs_sub_lt_iff, rw h6,
    split, 
    rintro ⟨ S_1, S_2 ⟩, 
    split; linarith, 
    rintro ⟨ S_3, S_4 ⟩, 
    split; linarith,
    },
  
  assume (h7 : ε > 0),
  cases h2 ε h7 with N1 h8,
  cases h3 ε h7 with N2 h9,

  let N := max N1 N2,
  use N,

  have h10 : ∀ n > N, n > N1 ∧ n > N2 := by {
    assume n h,
    split,
    exact lt_of_le_of_lt (le_max_left N1 N2) h, 
    exact lt_of_le_of_lt (le_max_right N1 N2) h,
  },
  
  have h11 : ∀ n > N, (((l - ε) < (y n)) ∧ ((y n) ≤ (x n))) ∧ (((x n) ≤ (z n)) ∧ ((z n) < l+ε)), 
  from by {
    intros n h12,
    split,
    {

      have h13 := (h8 n (h10 n h12).left), rw h5 (y n) at h13,
      split,
      exact h13.left,
      exact (h4 n).left,
    },
    {        
      have h14 := (h9 n (h10 n h12).right),rw h5 (z n) at h14,
      split,
      exact (h4 n).right,
      exact h14.right,
    },
    
  },

  have h15 : ∀ n > N, ((l - ε) < (x n)) ∧ ((x n) < (l+ε)), 
  from by {
    intros n1 h16, cases (h11 n1 h16);
    split; linarith,
  },

  show  ∀ (n : ℕ), n > N → |x n - l| < ε, 
  from by {
    intros n h17,
    cases h5 (x n) with h18 h19,
    apply h19, exact h15 n h17,
  },
end


/--`theorem`
Density of irrational orbit
The fractional parts of the integer multiples of an irrational number form a dense subset of the unit interval
`proof`
Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
$$
i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,
$$
which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$. Hence,
$$
S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}
$$
is an infinite subset of $\left[0,1\right]$.

By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$. One can thus find pairs of elements of $S$ that are arbitrarily close. Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.

To show that $S$ is dense in $[0, 1]$, consider $y \in[0,1]$, and $\epsilon>0$. Then by selecting $x \in S$ such that $\{x\}<\epsilon$ (which exists as $0$ is a limit point), and $N$ such that $N \cdot\{x\} \leq y<(N+1) \cdot\{x\}$, we get: $|y-\{N x\}|<\epsilon$.

QED
-/
theorem  irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
FEW SHOT PROMPTS TO CODEX(END)-/
