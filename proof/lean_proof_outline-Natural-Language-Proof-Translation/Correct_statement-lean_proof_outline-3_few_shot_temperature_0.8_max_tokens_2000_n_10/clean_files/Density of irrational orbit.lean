import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ m₁ m₂ : ℤ, m₁ ≠ m₂ → int.fract (α * (m₁ : ℝ)) ≠ int.fract (α * (m₂ : ℝ)), from sorry,

  have h2 : (λ (m : ℤ), int.fract (α * ↑m)) '' @set.univ ℤ = _ := sorry,

  have h3 : set.finite ((λ (m : ℤ), int.fract (α * ↑m)) '' @set.univ ℤ) = false, from sorry,

  have h4 : ∃ (l : ℝ), is_limit ((λ (m : ℤ), int.fract (α * ↑m)) '' @set.univ ℤ) l, from sorry,

  have h5 : ∃ (l : ℝ), is_limit ((λ (m : ℤ), int.fract (α * ↑m)) '' @set.univ ℤ) l ∧ l = 0, from sorry,

  have h6 : ∀ (y : ℝ), 0 < y → ∃ (m : ℤ), abs y < abs (int.fract (α * ↑m)), from sorry,

  have h7 : ∀ (y : ℝ) (h : 0 < y), ∃ (m : ℤ), (abs y < abs (int.fract (α * ↑m))) ∧ (y < (m + 1) * (int.fract (α * ↑m))) ∧ ((m : ℝ) * (int.fract (α * ↑m)) ≤ y), from sorry,

  have h8 : ∀ (y : ℝ) (h : 0 < y), ∃ (m : ℤ), abs y - abs (int.fract (α * ↑m)) < y, from sorry,

  show closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from sorry,
end

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := 
begin
    sorry,
end

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  assume y : ℝ,
  assume h_neq_zero : y ≠ 0,
  assume h_neq_one : y ≠ 1,

  have h1 : (λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' (set.Ico y 1) ≠ ∅, from sorry,
  have h2 : (λ (m : ℤ), int.fract (α * ↑m)) '' (set.univ) = set.Icc 0 1, from sorry,
  have h3 : (λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' (set.Ico y 1) ∈ (λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' (set.Icc 0 1), from sorry,
  have h4: (λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' (set.Ico y 1) ⊆ (λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' (set.Icc 0 1), from sorry,

  have h5 : (λ (m : ℤ), int.fract (α * ↑m)) '' (set.univ) ⊆ closure ((λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' (set.Icc 0 1)), from sorry,

  show (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ closure ((λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' (set.Icc 0 1)), from sorry,
end

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := sorry

/--`theorem`
Density of rational orbit
The fractional parts of the integer multiples of an irrational number form a dense subset of the unit interval
`proof`
Let $\alpha$ be a rational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
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
theorem  rational_orbit_dense {α : ℝ} (hα_rat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := sorry

/--`theorem`
Union of Intervals
Let $I, J$ be open intervals.
Then $I \cup J$ is an interval.
`proof`
Let $I = (a, b), J = (c, d) \mathop{\in} \mathcal{I}$.

The cases fall into two separate cases.

In the first case, $I$, $J$ do not overlap.

In the second case, $I$, $J$ overlap.

TODO: Finish
{{qed}}
-/
theorem union_interval {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
  is_interval (set.Ioo a b) (set.Ioo c d) → is_interval (set.Ioo a b) (set.Ioo c d)
| ⟨h1, h2, h3⟩ := 
  begin
    by_cases hc1 : (a ≤ c),
    { have hac2 : c ≤ a ∨ a < c, from le_or_lt a c,
      have hac3 : a ≤ c ∨ a < c, from le_or_lt a c,
      have hac4 : a < c ∨ a ≤ c, from lt_or_le c a,
      have hac5 : a < c ∨ a < c, from lt_or_lt c a,
      have hac6 : c < a ∨ c < a, from lt_or_lt c a,
      have hac7 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac8 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac9 : c ≤ a ∨ c ≤ a, from le_or_le a c,
      have hac10 : c ≤ a ∨ c < a, from le_or_lt a c,
      have hac11 : c ≤ a ∨ c ≤ a, from le_or_le a c,

      have hb : b > a, from hab.lt_of_le hac1,
      have h1 : b > c, from hb.lt_of_le hac1,
      have h2 : b > c, from hab.lt_of_le hc1,
      have h3 : b > c, from h2,
      have h5 : b < b, from h3,

      show is_interval (set.Ioo a b) (set.Ioo c d), from sorry,
      --{
      --cases hcd {
      --  assume h4 : c < d,
      --  assume h6 : a < b,
      --  show is_interval (set.Ioo a b) (set.Ioo c d), from sorry,
      --  },
      --cases hcd {
      --  assume h4 : c ≤ d,
      --  assume h6 : a < b,
      --  show is_interval (set.Ioo a b) (set.Ioo c d), from sorry,
      --  },
      --},
    },
    { cases hc1,
      have hac2 : c ≤ a ∨ a < c, from le_or_lt a c,
      have hac3 : a ≤ c ∨ a < c, from le_or_lt a c,
      have hac4 : a < c ∨ a ≤ c, from lt_or_le c a,
      have hac5 : a < c ∨ a < c, from lt_or_lt c a,
      have hac6 : c < a ∨ c < a, from lt_or_lt c a,
      have hac7 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac8 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac9 : c ≤ a ∨ c ≤ a, from le_or_le a c,
      have hac10 : c ≤ a ∨ c < a, from le_or_lt a c,
      have hac11 : c ≤ a ∨ c ≤ a, from le_or_le a c,
      have hac12 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac13 : c < a ∨ c < a, from lt_or_lt a c,
      have hac14 : c ≤ a ∨ c < a, from le_or_lt a c,
      have hac15 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac16 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac17 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac18 : c < a ∨ c < a, from lt_or_lt a c,
      have hac19 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac20 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac21 : c < a ∨ c ≤ a, from lt_or_le a c,
      have hac22 : c ∈ set.Ioo a b, from sorry,
      have hac23 : c ∈ set.Ioo a b, from sorry,
      have hac24 : c < a ∨ c < a, from lt_or_lt a c,
      have hac25 : c < a ∨ c < a, from lt_or_lt a c,
      have hac26 : c < a ∨ c < a, from lt_or_lt a c,
      have hac27 : c < a ∨ c < a, from lt_or_lt a c,
      have hac28 : c < a ∨ c < a, from lt_or_lt a c,
      have hac29 : c < a ∨ c < a, from lt_or_lt a c,
      have hac30
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let hm_eq : ∀ m n : ℤ, m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n, from sorry,

  have h1 : ∀ a b ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), (abs (a - b)) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from sorry,

  have h2 : ∀ a : ℝ, 0 <= a → a ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∨ a ∈ set.Icc 0 1 - (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from sorry,

  have h3 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from sorry,

  have h4 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from sorry,

  have h5 : ∀ a : ℝ, 0 <= a → a ∈ set.Icc 0 1 - (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) → closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ {a}, from sorry,

  have h6 : ∀ a : ℝ, 0 <= a → closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ {a} ∨ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1 - {a}, from sorry,

  have h7 : is_open {a} ∧ is_open (set.Icc 0 1 - {a}) → is_open (set.Icc 0 1), from sorry,

  have h8 : is_open {a}, from sorry,

  have h9 : is_open (set.Icc 0 1 - {a}), from sorry,

  have h10 : is_open (set.Icc 0 1), from sorry,

  have h11 : is_connected (set.Icc 0 1), from sorry,

  have h12 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from sorry,

  sorry,
end

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  show closure ((λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // true}) = set.Icc 0 1, from sorry,
end

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j hij,
    assume h1 : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h2 : α = ↑(int.nat_abs (1/(α * ↑i - α * ↑j)) / ↑(i - j)), from by sorry,
    have h3 : α ∈ ℚ, from by sorry,
    show false, from int.irrational_of_not_rat h3 h2,
  },
  have h2 : ∀ i j k : ℤ, i ≠ j →  (k : ℝ) * (int.fract (α * ↑i) - int.fract (α * ↑j)) = int.fract (α * ↑k *(int.fract (α * ↑i) - int.fract (α * ↑j))), from by {
    assume i j k hij,
    rw int.fract_mul,
    rw int.fract_mul,
    rw int.fract_add,
    rw sub_add_cancel' (int.floor_le _),
    rw sub_add_cancel' (int.floor_le _),
    rw int.nat_abs_mul,
    rw int.fract_eq_self_of_irrational at h1,
    sorry,
  },
  have h3 : ∀ i j : ℤ,  (int.nat_abs (1/(α * ↑i - α * ↑j)) : ℝ) * (int.fract (α * ↑i) - int.fract (α * ↑j)) = int.fract (α * ↑(int.nat_abs (1/(α * ↑i - α * ↑j))) *(int.fract (α * ↑i) - int.fract (α * ↑j))), from sorry,
  have h4 : ∀ i j : ℤ,  int.nat_abs (1/(α * ↑i - α * ↑j)) ≠ 0, from sorry,
  have h5 : ∀ i j : ℤ, i ≠ j → int.nat_abs (1/(α * ↑i - α * ↑j)) = ↑ (int.nat_abs (1/(α * ↑i - α * ↑j))), from sorry,
  sorry,
end

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  sorry
end

--OUTPUT 9
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j ∈ @set.univ ℤ, ∀ (h : i ≠ j), α * ↑i - floor (α * ↑i) ≠ α * ↑j - floor (α * ↑j), from sorry,
  have h2 : ∀ i j ∈ @set.univ ℤ, ∀ (h : i ≠ j), α * ↑i - floor (α * ↑i) ≠ α * ↑j - floor (α * ↑j), from sorry,
  have h3 : ∀ i j ∈ @set.univ ℤ, ∀ (h : i ≠ j), int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h4 : ∀ i j ∈ @set.univ ℤ, ∀ (h : i ≠ j), int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h5 : ∀ i : ℝ, i ≠ 0 → ∃ (j : ℝ), j ∈ (λ i : ℕ, α * ↑i) '' ({n : ℕ | n ≤ abs i}),
    from sorry,
  have h6 : ∀ i j : ℤ, i < j → ∃(k : ℤ), k ∈ (λ (m : ℤ), ↑m * int.fract (α * ↑m)) '' ({n : ℤ | n < j}) ∧ k < i,
    from sorry,
-- Now we prove that the set of fractional parts of integer multiples of an irrational number is closed.
  have h7 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from sorry,
-- Now we prove that the set of fractional parts of integer multiples of an irrational number contains zero.
  have h8 : ∃ (k : ℤ), k ∈ (@set.univ ℤ), from sorry,
  have h9 : 0 ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from sorry,
-- Now we prove that the set of fractional parts of integer multiples of an irrational number is bounded above by 1.
  have h10 : ∃ (k : ℤ), k ∈ (@set.univ ℤ), from sorry,
  have h11 : 1 ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from sorry,
  show closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from sorry,
end

--OUTPUT 10
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := set.eq_univ_iff_forall.2 $ λ y, ⟨⟨y, le_refl 0, by linarith⟩, λ ε hε, ⟨⟨1, int.fract_lt_one 1⟩, λ m hm, show abs (y - int.fract (↑m * α)) < ε, by rw [show m = ↑m, from rfl]; exact int.fract_lt_of_ne_zero_of_ne_zero hα_irrat.ne_zero⟩, λ ⟨m, hm⟩, begin
  have := int.fract_lt_of_ne_zero_of_ne_zero hα_irrat.ne_zero,
  rw show m = ↑m, from rfl at this,
  exact this hm
end

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
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from sorry,
  have h2 : (A ∩ B) ⊆ A, from sorry,
  have h3 : (A ∩ B) ⊆ S, from sorry,
  show (A ∩ B) ∈  𝒫 S, from sorry,
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
  calc (x + y)^2 = (x+y)*(x+y) : by sorry
  ... = x*(x+y) + y*(x+y) : by sorry
  ... = x*x + x*y + y*x + y*y : by sorry
  ... = x^2 + 2*x*y + y^2 : by sorry,
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
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from sorry,
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from sorry,

  have h3 : ∀ a : G, ∃! x : G, a * x = a, from sorry,
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from sorry,

  have h5 : ∀ a : G, classical.some (h3 a) = (1 : G), from sorry,
  have h6 : ∀ a : G, classical.some (h4 a) = (1 : G), from sorry,

  show ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a, from by {
    use (1 : G),
    have h7 : ∀ e : G, (∀ a : G, e * a = a ∧ a * e = a) → e = 1, from by {
      assume (e : G) (h7 : ∀ a : G, e * a = a ∧ a * e = a),
      have h8 : ∀ a : G, e = classical.some (h3 a), from sorry,
      have h9 : ∀ a : G, e = classical.some (h4 a), from sorry,
      show e = (1 : G), from sorry,     
    },
    sorry,
  }
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
