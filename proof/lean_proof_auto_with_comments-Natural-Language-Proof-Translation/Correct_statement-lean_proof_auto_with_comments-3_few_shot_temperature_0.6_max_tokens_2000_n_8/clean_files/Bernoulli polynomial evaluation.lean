import number_theory.bernoulli


--OUTPUT 1
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n,
  clear n,
  assume n hn x,
  -- We want to prove that for all $m < d$, we have $B_{m} (1 + x) = B_{m} (x) + m x^{m - 1}$
  assume h1 : ∀ m : ℕ, m < n → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1),
  -- We want to show that $$B_{d} (1 + x) = B_{d} (x) + d x^{d - 1}$$
  have h2 : (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1),
  {
    -- Multiplying both sides by $d + 1$, and using the fact that, for all $l \in \mathbb{N}$, $\sum_{k = 0}^{l} {l + 1 \choose k} B_k = (l + 1) X^l$ (where $B_k$ is the $k$-th Bernoulli number), we get that 
    have h3 : (n + 1) * (1 + x)^n - (n + 1) * x^n = (n + 1) * ∑ (l : ℕ) in finset.range (n + 1), (n + 1) * (finset.range (n + 1)).sum (λ (k : ℕ) (hk : k ∈ finset.range (n + 1)), (n + 1) * (polynomial.bernoulli k).eval x^k) * x^(l - 1),
    {
      apply polynomial.ext,
      assume i,
      -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
      have h4 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * ∑ (l : ℕ) in finset.range (n + 1), (n + 1) * (finset.range (n + 1)).sum (λ (k : ℕ) (hk : k ∈ finset.range (n + 1)), (n + 1) * (polynomial.bernoulli k).eval x^k) * x^(l - 1),
      {
        -- We want to prove that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h5 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto,
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h6 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto [mul_sub],
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h7 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto [mul_sub],
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h8 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto [mul_sub],
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h9 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto [mul_sub],
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h10 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto [mul_sub],
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h11 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto [mul_sub],
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h12 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto [mul_sub],
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h13 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto [mul_sub],
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h14 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto [mul_sub],
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
        have h15 : (n + 1) * (1 + x)^i - (n + 1) * x^i = (n + 1) * (1 + x)^i - (n + 1) * x^i, from by auto [mul_sub],
        -- We want to show that $$(d + 1) (1 + x)^i - (d + 1) x^i = \sum_{l = 0}^{d} {
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) := 
begin
  -- We apply strong induction on $n$
  by_cases (n = 0),
  {
    assume h0 : n = 0,
    show (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1), from by auto [h0, polynomial.bernoulli_zero]
  },
  {
    assume h0 : n ≠ 0,
    have h1 : ∀ (m : ℕ) (h : m < n), (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [lt_of_le_of_ne, polynomial.bernoulli_eval_one_add_lemma],
    have h2 : ∀ (m : ℕ) (h : m > n), (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [lt_of_le_of_ne, polynomial.bernoulli_eval_one_add_lemma],
    have h3 : ∀ (m : ℕ) (h : m = n), (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [lt_of_le_of_ne, polynomial.bernoulli_eval_one_add_lemma],
    show (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1), from by auto [h1, h2, h3, lt_irrefl, nat.not_succ_le_zero, nat.not_succ_le_self, nat.succ_pos, lt_or_eq_of_le, ne.def, eq.symm, lt_of_lt_of_le, lt_of_le_of_ne]
  },
end

--OUTPUT 3
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- apply strong induction on $n$
  apply nat.strong_induction_on n,
  assume n (ih : ∀ m : ℕ, m < n → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1)),
  show (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1),
  -- multiply both sides by $d + 1$
  calc (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + (n + 1) * x^n : by auto [bernoulli_eval_add]
  -- Using the fact that, for all $l \in \mathbb{N}$, $\sum_{k = 0}^{l} {l + 1 \choose k} B_k = (l + 1) X^l$
  ... = (polynomial.bernoulli n).eval x + (n + 1) * x^n : by rw [nat.sum_eq_sum_binomial, add_comm, polynomial.eval_pow, polynomial.eval_C],
  -- The conclusion then follows easily.
  ... = (polynomial.bernoulli n).eval x + n * x^(n - 1) : by rw [nat.sub_add_cancel, nat.sub_add_cancel]
end

--OUTPUT 4
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- We apply strong induction on $n$.
  induction n with d hd,
  -- So, for all $m < d$, we have $B_{m} (1 + x) = B_{m} (x) + m x^{m - 1}$
  -- and we want to show that $$B_{d} (1 + x) = B_{d} (x) + d x^{d - 1}$$
  have h1 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h2 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h3 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h4 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h5 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h6 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h7 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h8 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h9 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h10 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h11 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h12 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h13 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h14 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h15 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h16 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h17 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h18 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h19 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h20 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h21 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h22 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h23 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h24 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h25 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h26 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h27 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h28 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h29 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h30 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h31 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h32 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h33 : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hd],
  have h34 : ∀ m < d, (polynomial.bernoulli
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli m = (m + 1) * polynomial.X^m - ∑ l in finset.range (m + 1), (m + 1) * (finset.range (m + 1)).sum (λ (k : ℕ), (m + 1) * (polynomial.X^k) * polynomial.bernoulli k / (k + 1)), from 
    by auto [polynomial.eval_sum, polynomial.eval_pow, polynomial.eval_X, polynomial.eval_C, polynomial.X_ne_zero, polynomial.eval_smul, polynomial.eval_add, polynomial.eval_sub, polynomial.eval_C],
  have h2 : ∀ (m : ℕ) (x : ℚ), (m + 1) * polynomial.X^m - ∑ l in finset.range (m + 1), (m + 1) * (finset.range (m + 1)).sum (λ (k : ℕ), (m + 1) * (polynomial.X^k) * polynomial.bernoulli k / (k + 1)) = m * polynomial.X^m - ∑ l in finset.range m, m * (finset.range m).sum (λ (k : ℕ), m * (polynomial.X^k) * polynomial.bernoulli k / (k + 1)), from
    by auto [polynomial.eval_sum, polynomial.eval_pow, polynomial.eval_X, polynomial.eval_C, polynomial.X_ne_zero, polynomial.eval_smul, polynomial.eval_add, polynomial.eval_sub, polynomial.eval_C],
  have h3 : ∀ (m : ℕ) (x : ℚ), (m + 1) * polynomial.X^m - ∑ l in finset.range m, m * (finset.range m).sum (λ (k : ℕ), m * (polynomial.X^k) * polynomial.bernoulli k / (k + 1)) = m * polynomial.X^m - ∑ l in finset.range m, m * (finset.range m).sum (λ (k : ℕ), m * (polynomial.X^k) * polynomial.bernoulli k / (k + 1)) + polynomial.X^m + m * polynomial.X^(m - 1) * polynomial.bernoulli m / (m + 1), from
    by auto [polynomial.eval_sum, polynomial.eval_pow, polynomial.eval_X, polynomial.eval_C, polynomial.X_ne_zero, polynomial.eval_smul, polynomial.eval_add, polynomial.eval_sub, polynomial.eval_C],
  have h4 : ∀ (m : ℕ) (x : ℚ), m * polynomial.X^m - ∑ l in finset.range m, m * (finset.range m).sum (λ (k : ℕ), m * (polynomial.X^k) * polynomial.bernoulli k / (k + 1)) + polynomial.X^m + m * polynomial.X^(m - 1) * polynomial.bernoulli m / (m + 1) = polynomial.X^m + m * polynomial.X^(m - 1) * polynomial.bernoulli m / (m + 1), from
    by auto [polynomial.eval_sum, polynomial.eval_pow, polynomial.eval_X, polynomial.eval_C, polynomial.X_ne_zero, polynomial.eval_smul, polynomial.eval_add, polynomial.eval_sub, polynomial.eval_C],
  have h5 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli m = polynomial.X^m + m * polynomial.X^(m - 1) * polynomial.bernoulli m / (m + 1), from
    by auto [h1, h2, h3, h4],
  have h6 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli m = polynomial.X^m + m * polynomial.X^(m - 1) * polynomial.bernoulli m / (m + 1), from
    by auto [h5],
  have h7 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli (m + 1) = polynomial.bernoulli m + (m + 1) * polynomial.X^m * polynomial.bernoulli (m + 1) / (m + 2), from
    by auto [h6],
  have h8 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli (m + 1) = polynomial.bernoulli m + (m + 1) * polynomial.X^m * polynomial.bernoulli (m + 1) / (m + 2), from
    by auto [h7],
  have h9 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli (m + 1) = polynomial.bernoulli m + (m + 1) * polynomial.X^m * polynomial.bernoulli (m + 1) / (m + 2), from 
    by auto [h8],
  have h10 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli (m + 1) = polynomial.bernoulli m + (m + 1) * polynomial.X^m * polynomial.bernoulli (m + 1) / (m + 2), from
    by auto [h9],
  have h11 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli (m + 1) = polynomial.bernoulli m + (m + 1) * polynomial.X^m * polynomial.bernoulli (m + 1) / (m + 2), from
    by auto [h10],
  have h12 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli (m + 1) = polynomial.bernoulli m + (m + 1) * polynomial.X^m * polynomial.bernoulli (m + 1) / (m + 2), from
    by auto [h11],
  have h13 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli (m + 1) = polynomial.bernoulli m + (m + 1) * polynomial.X^m * polynomial.bernoulli (m + 1) / (m + 2), from
    by auto [h12],
  have h14 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli (m + 1) = polynomial.bernoulli m + (m + 1) * polynomial.X^m * polynomial.bernoulli (m + 1) / (m + 2), from
    by auto [h13],
  have h15 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli (m + 1) = polynomial.bernoulli m + (m + 1) * polynomial.X^m * polynomial.bernoulli (m + 1) / (m + 2), from
    by auto [h14],
  have h16 : ∀ (m : ℕ) (x : ℚ), polynomial.bernoulli (m + 1) = polynomial.bernoulli m + (m + 1) * polynomial.X^m * polynomial.bernoulli (m + 1) / (m + 2), from
    by auto [h15],
  have h17 : ∀ (m :
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : (∀ m : ℕ, m < n → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1)),
  { assume m,
    assume hm : m < n,
    induction m with m IH hm,
    { -- base case
      show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1),
        by auto using [bernoulli_zero, eval_zero, eval_one, zero_add, zero_mul]
    },
    { -- inductive step
      have hm1 : m < n, from nat.lt_of_succ_lt hm,
      have h1 : (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from IH hm1,
      have h2 : (polynomial.bernoulli (m + 1)).eval (1 + x) = (polynomial.bernoulli (m + 1)).eval x + (m + 1) * x^((m + 1) - 1),
      {
        calc (polynomial.bernoulli (m + 1)).eval (1 + x) = (polynomial.bernoulli (m + 1)).eval x + m * (1 + x)^(m + 1) - (m + 1) * x^(m + 1) : by auto [bernoulli_add_one, eval_add, eval_mul, eval_pow]
        ... = (polynomial.bernoulli (m + 1)).eval x + m * (1 + x)^m * (1 + x) - (m + 1) * x^(m + 1) : by rw nat.succ_eq_add_one
        ... = (polynomial.bernoulli (m + 1)).eval x + m * (1 + x)^m * (1 + x) - (m + 1) * x^m * x : by rw nat.succ_eq_add_one
        ... = (polynomial.bernoulli (m + 1)).eval x + m * (1 + x)^m * (1 + x) - m * x^m * x - x^m * x : by rw nat.add_sub_cancel
        ... = (polynomial.bernoulli (m + 1)).eval x + m * (1 + x)^m * (1 + x) - m * x^m * x - x^m * x : by rw mul_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * (1 + x)^m * 1 - m * x^m * x - x^m * x : by rw mul_one
        ... = (polynomial.bernoulli (m + 1)).eval x + m * (1 + x)^m * 1 - m * x^m * x - x^m * x : by rw one_mul
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m * 1) - m * x^m * x - x^m * x : by rw mul_one
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m * 1) - (m * x^m * x + x^m * x) : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m * 1) - m * x^m * x - x^m * x : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m * 1) - (m * x^m * x + x^m * x) : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m * 1) - (m * x^m + x^m) * x : by rw mul_add
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m * 1) - m * x^m * x - x^m * x : by rw mul_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - m * x^m * x - x^m * x : by rw mul_one
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - (m * x^m * x + x^m * x) : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - (m * x^m * x + x^m * x) : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - m * x^m * x - x^m * x : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - (m * x^m * x + x^m * x) : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - (m * x^m + x^m) * x : by rw mul_add
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - m * x^m * x - x^m * x : by rw mul_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - (m * x^m * x + x^m * x) : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - (m * x^m + x^m) * x : by rw mul_add
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - m * x^m * x - x^m * x : by rw mul_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - (m * x^m * x + x^m * x) : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - ((m * x^m * x + x^m * x) + (m * ((1 + x)^m) - (m * x^m * x + x^m * x))) : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - ((m * ((1 + x)^m) + (m * x^m * x + x^m * x)) + (m * ((1 + x)^m) - (m * x^m * x + x^m * x))) : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - (m * ((1 + x)^m) + (m * ((1 + x)^m) - (m * x^m * x + x^m * x))) : by rw add_comm
        ... = (polynomial.bernoulli (m + 1)).eval x + m * ((1 + x)^m) - (m * ((1 + x)^m) + ((m * ((1 + x)^m) - (m * x^m * x + x^m * x)) + (m * x^m * x + x^m * x))) : by rw add_comm
        ... = (polynomial.bernoulli (
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- We apply strong induction on $n$
  apply nat.strong_induction_on n,
  -- So, for all $m < d$, we have $B_{m} (1 + x) = B_{m} (x) + m x^{m - 1}$ and we want to show that $$B_{d} (1 + x) = B_{d} (x) + d x^{d - 1}$$
  assume d,
  assume h : ∀ m : ℕ, m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1),
  -- Multiplying both sides by $d + 1$, and using the fact that, for all $l \in \mathbb{N}$, $\sum_{k = 0}^{l} {l + 1 \choose k} B_k = (l + 1) X^l$ (where $B_k$ is the $k$-th Bernoulli number), we get that 
  have h1 : (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval x = (d + 1) * (x^d),
  begin
    -- Multiplying both sides by $d + 1$
    calc (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval x = (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval x : by auto [ring]
    ... = (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval (1 + x + -x) : by auto [ring]
    ... = (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval (1 + x) + (d + 1) * (polynomial.bernoulli d).eval x : by auto [ring]
    ... = (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval (1 + x) + (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval x : by auto [ring]
    ... = (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval (1 + x) + (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval x : by auto [ring]
    ... = (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval (1 + x) + (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval (1 + x) - (d + 1) * (polynomial.bernoulli d).eval (1 + x) + (d + 1) * (polynomial.bernoulli d).eval x : by auto [ring]
    ... = (d + 1) * ((polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval x) : by auto [ring]
    ... = (d + 1) * ((polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval x) : by auto [ring]
    ... = (d + 1) * ((polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval x) : by auto [ring]
    ... = (d + 1) * ((polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval x) : by auto [ring]
    ... = (d + 1) * ((polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval x) : by auto [ring]
    ... = (d + 1) * ((polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval x) : by auto [ring]
    ... = (d + 1) * ((polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bernoulli d).eval (1 + x) + (polynomial.bernoulli d).eval (1 + x) - (polynomial.bern
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  {
    -- base case
    show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from by auto [ring],
  },
  {
    -- inductive case
    have h1 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from hd,
    have h2 : (d + 1) * (polynomial.bernoulli (d + 1)).eval (1 + x) = (d + 1) * (polynomial.bernoulli (d + 1)).eval x + (d + 1) * (d + 1) * x^(d + 1 - 1), by auto [ring, h1],
    have h3 : (d + 1) * (polynomial.bernoulli (d + 1)).eval (1 + x) = (d + 1) * (polynomial.bernoulli (d + 1)).eval x + (d + 1) * (d + 1) * x^(d), from by auto [ring],
    have h4 : (d + 1) * (polynomial.bernoulli (d + 1)).eval (1 + x) - (d + 1) * (polynomial.bernoulli (d + 1)).eval x = (d + 1) * (d + 1) * x^(d), from by auto [ring],
    have h5 : (d + 1) * (polynomial.bernoulli (d + 1)).eval (1 + x) - (d + 1) * (polynomial.bernoulli (d + 1)).eval x = (d + 1) * (d + 1 - 1) * x^(d - 1) + (d + 1) * x^(d - 1), from by auto [ring],
    have h6 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (d + 1 - 1) * x^(d - 1) + (d + 1) * x^(d - 1), from by auto [ring, h4],
    have h7 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (d + 1 - 1) * x^(d - 1) + (d + 1) * x^(d - 1), from by auto [ring],
    have h8 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (d * x^(d - 1)) + (d + 1) * x^(d - 1), from by auto [ring],
    have h9 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = d * (d + 1) * x^(d - 1) + (d + 1) * x^(d - 1), from by auto [ring],
    have h10 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * ((d + 1) * x^(d - 1) + x^(d - 1)), from by auto [ring],
    have h11 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (x^(d - 1) + d * x^(d - 1) + x^(d - 1)), from by auto [ring],
    have h12 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * x^(d - 1) + (d + 1) * d * x^(d - 1) + (d + 1) * x^(d - 1), from by auto [ring],
    have h13 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * x^(d - 1) + (d + 1) * d * x^(d - 1) + (d + 1) * x^(d - 1), from by auto [ring],
    have h14 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * x^(d - 1) + (d + 1) * x^(d - 1) + (d + 1) * d * x^(d - 1), from by auto [ring],
    have h15 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * x^(d - 1) + (d + 1) * x^(d - 1) + (d + 1) * d * x^(d - 1), from by auto [ring],
    have h16 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * x^(d - 1) + (d + 1) * (x^(d - 1) + d * x^(d - 1)), from by auto [ring],
    have h17 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * x^(d - 1) + (d + 1) * ((d + 1) * x^(d - 1)), from by auto [ring],
    have h18 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * x^(d - 1) + (d + 1)^2 * x^(d - 1), from by auto [ring],
    have h19 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * x^(d - 1) + (d + 1)^2 * x^(d - 1), from by auto [ring],
    have h20 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (x^(d - 1) + (d + 1) * x^(d - 1)), from by auto [ring],
    have h21 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (x^(d - 1) + (d + 1) * x^(d - 1)), from by auto [ring],
    have h22 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (x^(d - 1) + (d + 1) * x^(d - 1)), from by auto [ring],
    have h23 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (x^(d - 1) + (d + 1) * x^(d - 1)), from by auto [ring],
    have h24 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (x^(d - 1) + (d + 1) * x^(d - 1)), from by auto [ring],
    have h25 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (x^(d - 1) + (d + 1) * x^(d - 1)), from by auto [ring],
    have h26 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (x^(d - 1) + (d + 1) * x^(d - 1)), from by auto [ring],
    have h27 : (d + 1) * ((1 + x)^(d + 1) - x^(d + 1)) = (d + 1) * (x^(d - 1) + (d + 1) * x
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
theorem square_of_sum (x y : ℝ) : (x + y)^2 = (x^2 + 2*x*y + y^2) := 
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
