import number_theory.bernoulli


--OUTPUT 1
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n,
  assume d hd,
  have h1 : (d + 1) * (1 + x)^d - (d + 1) * x^d = 
            (d + 1) * (1 + x)^d - (d + 1) * x^d,
  {
    rw add_comm,
    ring,
  },
  have h2 : (d + 1) * (1 + x)^d - (d + 1) * x^d = 
            (d + 1) * ((1 + x)^d - x^d),
  {
    ring,
  },
  rw h2,
  clear h2,
  have h3 : (1 + x)^d = x^d + d * x^(d - 1) + (↑d : ℚ) * x^d,
  {
    rw hd,
    ring,
  },
  rw h3,
  have h4 : (d + 1) * ((1 + x)^d - x^d) = (d + 1) * (x^d + d * x^(d - 1) + (↑d : ℚ) * x^d - x^d),
  {
    ring,
  },
  rw h4,
  clear h4,
  rw ←polynomial.eval_sum,
  {
    have h5 : (d + 1) * (x^d + d * x^(d - 1) + (↑d : ℚ) * x^d - x^d) =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h5,
    clear h5,
    have h6 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h6,
    clear h6,
    have h7 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h7,
    clear h7,
    have h8 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h8,
    clear h8,
    have h9 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h9,
    clear h9,
    have h10 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h10,
    clear h10,
    have h11 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h11,
    clear h11,
    have h12 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h12,
    clear h12,
    have h13 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h13,
    clear h13,
    have h14 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h14,
    clear h14,
    have h15 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h15,
    clear h15,
    have h16 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d,
    {
      ring,
    },
    rw h16,
    clear h16,
    have h17 : (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d + 1) * x^d =
              (d + 1) * (x^d + d * x^(d - 1)) + (d + 1) * (↑d : ℚ) * x^d - (d
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : ∀ m : ℕ, m < n → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from 
    assume (m : ℕ) (hm : m < n),
    begin
      induction m with hm hih,
      { rw [polynomial.bernoulli,eval_C,add_zero,add_zero], },
      { rw [polynomial.bernoulli,eval_C,add_zero,add_zero],
        exact hih hm,
      }
    end,
  have h2 : ∀ l : ℕ, (polynomial.bernoulli l).eval 1 = l, from 
    assume (l : ℕ), (polynomial.bernoulli l).eval 1,
  have h3 : ∀ l : ℕ, (polynomial.bernoulli l).eval x = 0, from 
    assume (l : ℕ), (polynomial.bernoulli l).eval x,
  have h4 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval 1 + (polynomial.bernoulli l).eval x, from 
    assume (l : ℕ), (polynomial.bernoulli l).eval (1 + x),
  have h5 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval 1, from 
    assume (l : ℕ), eq.trans (h4 l) (add_zero (polynomial.bernoulli l).eval 1),
  have h6 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = l, from
    assume (l : ℕ), eq.trans (h5 l) (h2 l),
  have h7 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x, from 
    assume (l : ℕ), eq.trans (h4 l) (add_zero (polynomial.bernoulli l).eval x),
  have h8 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = 0, from 
    assume (l : ℕ), eq.trans (h7 l) (h3 l),
  have h9 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1), from 
    assume (l : ℕ), eq.trans (h4 l) (add_mul  (polynomial.bernoulli l).eval 1 x (l - 1)),
  have h10 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = l * x^(l - 1), from 
    assume (l : ℕ), eq.trans (h9 l) (add_right_cancel (polynomial.bernoulli l).eval x),
  have h11 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = l * x^(l - 1), from 
    assume (l : ℕ), by {rw [← h6 l,← h8 l], ring},

  have h12 : (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1), from 
    by {rw [← h11 n, ← mul_one (polynomial.bernoulli n).eval (1 + x), ← add_mul (polynomial.bernoulli n).eval 1 x (n - 1)], ring},
  show (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1), from 
    by {rw [← h4 n, ← add_mul (polynomial.bernoulli n).eval 1 x (n - 1)], ring},
end

--OUTPUT 3
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- use strong induction
  apply nat.strong_induction_on n,
  assume (d : ℕ) (ih : ∀ m : ℕ, m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1)),
  have h1 : ∀ l : ℕ, (d + 1) * (1 + x)^l - (d + 1) * x^l = ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k d) * x^k, from assume (l : ℕ),
    calc
    (d + 1) * (1 + x)^l - (d + 1) * x^l = (d + 1) * ∑ k in finset.range (l + 1), (finset.nat_fintype.choose k l) * x^k : by rw polynomial.eval_sum (1 + x) l
    ... = ∑ k in finset.range (l + 1), (d + 1) * (finset.nat_fintype.choose k l) * x^k : by rw ← finset.sum_mul_distrib
    ... = ∑ k in finset.range (l + 1), (finset.nat_fintype.choose k l) * ((d + 1) * x^k) : by rw finset.sum_mul_distrib
    ... = ∑ k in finset.range (l + 1), (finset.nat_fintype.choose k d) * ((d + 1) * x^k) : by {rw finset.nat_fintype.choose_succ, rw finset.nat_fintype.choose_zero},
  have h2 : ∀ l : ℕ, ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k d) * x^k = ∑ k in finset.range (l + 1), (l + 1) * k * (finset.nat_fintype.choose k (d - 1)) * x^(k - 1), from assume (l : ℕ),
    calc
    ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k d) * x^k = ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k d) * x^(k - 1 + 1) : by rw finset.sum_mul_distrib
    ... = ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k d) * x^(k - 1) * x : by rw finset.sum_mul_distrib
    ... = ∑ k in finset.range (l + 1), (l + 1) * x^(k - 1) * (finset.nat_fintype.choose k d) * x : by rw finset.sum_mul_distrib
    ... = ∑ k in finset.range (l + 1), (l + 1) * x^(k - 1) * (finset.nat_fintype.choose (k - 1) d) * x : by rw finset.nat_fintype.choose_succ
    ... = ∑ k in finset.range (l + 1), (l + 1) * x^(k - 1) * (finset.nat_fintype.choose (k - 1) (d - 1)) * x : by rw finset.nat_fintype.choose_succ
    ... = ∑ k in finset.range (l + 1), (l + 1) * k * (finset.nat_fintype.choose (k - 1) (d - 1)) * x^(k - 1) : by rw finset.nat_fintype.choose_zero,
  have h3 : ∀ l : ℕ, ∑ k in finset.range (l + 1), (l + 1) * k * (finset.nat_fintype.choose k (d - 1)) * x^(k - 1) = ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * (k * x^(k - 1)), from assume (l : ℕ),
    calc
    ∑ k in finset.range (l + 1), (l + 1) * k * (finset.nat_fintype.choose k (d - 1)) * x^(k - 1) = ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * (k * x^(k - 1)) : by rw finset.sum_mul_distrib,
  have h4 : ∀ l : ℕ, ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * (k * x^(k - 1)) = ∑ k in finset.range (l + 1), (l + 1) * k * (finset.nat_fintype.choose k (d - 1)) * x^(k - 1), from assume (l : ℕ),
    calc
    ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * (k * x^(k - 1)) = ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * x^(k - 1) * k : by rw finset.sum_mul_distrib
    ... = ∑ k in finset.range (l + 1), (l + 1) * k * (finset.nat_fintype.choose k (d - 1)) * x^(k - 1) : by rw finset.sum_mul_distrib,
  have h5 : ∀ l : ℕ, ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * (k * x^(k - 1)) = ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * ((k - 1 + 1) * x^(k - 1)), from assume (l : ℕ),
    calc
    ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * (k * x^(k - 1)) = ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * ((k - 1) * x^(k - 1)) + (l + 1) * (finset.nat_fintype.choose k (d - 1)) * x^(k - 1) : by rw finset.sum_distrib
    ... = ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * ((k - 1) * x^(k - 1)) + (l + 1) * (finset.nat_fintype.choose (k - 1) (d - 1)) * x^(k - 1) : by rw finset.nat_fintype.choose_succ
    ... = ∑ k in finset.range (l + 1), (l + 1) * (finset.nat_fintype.choose k (d - 1)) * ((k - 1) * x^(
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- strong induction
  have h : ∀ n : ℕ, ∀ x : ℚ, n < (polynomial.bernoulli n).nat_degree →
    (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1), from
      assume (n : ℕ) (x : ℚ) (h : n < (polynomial.bernoulli n).nat_degree),
      have h1 : ∀ m < n, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
          assume (m : ℕ) (h : m < n), show (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
          begin
            induction m with m hm,
            show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from rfl,
            show (polynomial.bernoulli (nat.succ m)).eval (1 + x) = (polynomial.bernoulli (nat.succ m)).eval x + (nat.succ m) * x^(nat.succ m - 1), from
            begin
              rw [polynomial.bernoulli, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add],
              rw [polynomial.eval_C, polynomial.eval_C, polynomial.eval_C, polynomial.eval_C, polynomial.eval_C, polynomial.eval_C, polynomial.eval_C, polynomial.eval_C, polynomial.eval_C, polynomial.eval_C, polynomial.eval_C, polynomial.eval_C, polynomial.eval_C],
              rw [polynomial.eval_X, polynomial.eval_X, polynomial.eval_X, polynomial.eval_X, polynomial.eval_X, polynomial.eval_X, polynomial.eval_X, polynomial.eval_X, polynomial.eval_X, polynomial.eval_X, polynomial.eval_X, polynomial.eval_X, polynomial.eval_X],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul],
              rw [polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_add],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_mul],
              rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) := 
begin
  -- We apply strong induction on $n$. So, for all $m < d$, we have $B_{m} (1 + x) = B_{m} (x) + m x^{m - 1}$ and we want to show that $$B_{d} (1 + x) = B_{d} (x) + d x^{d - 1}$$
  induction n with d hd,
  { -- base case
    assume x : ℚ,
    calc (polynomial.bernoulli 0).eval (1 + x) = ((polynomial.bernoulli 0).eval 1) + x : by {
      have h1 : ∀ x : ℚ, (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval 1 + x, from by {
        assume x : ℚ,
        rw [polynomial.bernoulli,eval_add,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_C,eval_X,eval_
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- We apply strong induction on $n$.
  induction n with d hd,
  -- So, for all $m < d$, we have `B_{m} (1 + x) = B_{m} (x) + m * x^(m - 1)`
  assume h1 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1),
  -- and we want to show that `B_{d} (1 + x) = B_{d} (x) + d * x^(d - 1)`
  have h2 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1),
  -- Multiplying both sides by `d + 1`, and using the fact that, for all `l` in `ℕ`, `∑_{k = 0}^{l} {l + 1 choose k} * (polynomial.bernoulli k) = (l + 1) * X^l` (where `B_k` is the $k$-th Bernoulli number),
  begin
    -- we get that 
    calc (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1) :
    -- $$ (d + 1) (1 + x)^d - (d + 1) x^d = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
    begin
      -- we get that 
      have h3 : (d + 1) * (1 + x)^d - (d + 1) * x^d = ∑ (k : ℕ) in finset.range (d + 1), (d + 1) * (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k).eval x, from
        begin
          -- we get that 
          have h31 : (d + 1) * (1 + x)^d - (d + 1) * x^d = (d + 1) * (((1 + x)^d - x^d) : polynomial ℚ), from
            by { rw [← polynomial.coeff_mul_X_pow, polynomial.coeff_sub (d + 1)], ring },
          -- we get that 
          have h32 : (1 + x)^d - x^d = polynomial.coeff_mul_X_pow (d + 1) (∑ (k : ℕ) in finset.range (d + 1), (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k) : polynomial ℚ), from
            begin
              -- we get that 
              have h321 : (1 + x)^d - x^d = polynomial.coeff_mul_X_pow (d + 1) (∑ (k : ℕ) in finset.range (d + 1), (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k : polynomial ℚ)), from
                by { apply polynomial.coeff_sub (d + 1), simp [polynomial.coeff_mul_X_pow],
                rw [← polynomial.coeff_mul_X_pow, polynomial.coeff_sub (d + 1)], ring },
              -- we get that 
              have h322 : (1 + x)^d - x^d = polynomial.coeff_mul_X_pow (d + 1) (∑ (k : ℕ) in finset.range (d + 1), (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k) : polynomial ℚ), from
                begin
                  -- we get that 
                  have h3221 : (1 + x)^d - x^d = polynomial.coeff_mul_X_pow (d + 1) (∑ (k : ℕ) in finset.range (d + 1), (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k : polynomial ℚ)), from
                    by { apply polynomial.coeff_sub (d + 1), simp [polynomial.coeff_mul_X_pow],
                    rw [← polynomial.coeff_mul_X_pow, polynomial.coeff_sub (d + 1)], ring },
                  -- we get that 
                  have h3222 : (1 + x)^d - x^d = polynomial.coeff_mul_X_pow (d + 1) (∑ (k : ℕ) in finset.range (d + 1), (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k) : polynomial ℚ), from
                    begin
                      -- we get that 
                      have h32221 : (1 + x)^d - x^d = polynomial.coeff_mul_X_pow (d + 1) (∑ (k : ℕ) in finset.range (d + 1), (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k) : polynomial ℚ), from
                        by { apply polynomial.coeff_sub (d + 1), simp [polynomial.coeff_mul_X_pow],
                        rw [← polynomial.coeff_mul_X_pow, polynomial.coeff_sub (d + 1)], ring },
                      -- we get that 
                      have h32222 : (1 + x)^d - x^d = polynomial.coeff_mul_X_pow (d + 1) (∑ (k : ℕ) in finset.range (d + 1), (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k) : polynomial ℚ), from
                        begin
                          -- we get that 
                          have h322221 : (1 + x)^d - x^d = polynomial.coeff_mul_X_pow (d + 1) (∑ (k : ℕ) in finset.range (d + 1), (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k) : polynomial ℚ), from
                            by { apply polynomial.coeff_sub (d + 1), simp [polynomial.coeff_mul_X_pow],
                            rw [← polynomial.coeff_mul_X_pow, polynomial.coeff_sub (d + 1)], ring },
                          -- we get that 
                          have h322222 : (1 + x)^d - x^d = polynomial.coeff_mul_X_pow (d + 1) (∑ (k : ℕ) in finset.range (d + 1), (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k) : polynomial ℚ), from
                            begin
                              -- we get that 
                              have h3222221 : (1 + x)^d - x^d = polynomial.coeff_mul_X_pow (d + 1) (∑ (k : ℕ) in finset.range (d + 1), (polynomial.choose_nat (d + 1) k) * (polynomial.bernoulli k) : polynomial ℚ), from
                                by { apply polynomial.coeff_sub (d + 1), simp [polynomial.coeff_mul_X_pow],
                                rw [← polynomial.coeff_mul_X_pow, po
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- Applying strong induction on $n$
  induction n with d hd,
  -- For $n = 0$, the conclusion is trivial.
  show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1),
  from by obviously,

  -- So, for all $m < d$, we have $B_{m} (1 + x) = B_{m} (x) + m x^{m - 1}$ and we want to show that $$B_{d} (1 + x) = B_{d} (x) + d x^{d - 1}$$
  assume d hd : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1),
  have h1 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from by {
    -- Multiplying both sides by $d + 1$,
    rw [show (d+1)*(polynomial.bernoulli d).eval (1 + x) = (d+1)*((polynomial.bernoulli d).eval x + d * x^(d - 1)),
    from eq.trans (mul_right_inj (d+1)).mp (mul_add ((polynomial.bernoulli d).eval x) (d * x^(d - 1)) (d+1)),
    show (d+1)*(polynomial.bernoulli d).eval (1 + x) = (d+1)*(polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)),
    from by ring,],
    -- and using the fact that, for all $l \in \mathbb{N}$, $\sum_{k = 0}^{l} {l + 1 \choose k} B_k = (l + 1) X^l$ (where $B_k$ is the $k$-th Bernoulli number), we get that 
    rw [show (d+1)*(polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) =
    (d+1)*((polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (d+1)*(polynomial.bernoulli d).eval x),
    from by simp [add_mul],
    show (d+1)*((polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (d+1)*(polynomial.bernoulli d).eval x) =
    (d+1)*(polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (d+1)*(polynomial.bernoulli d).eval x,
    from by ring,],
    rw [show (d+1)*((polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (polynomial.bernoulli d).eval x) =
    (d+1)*((polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (polynomial.bernoulli d).eval x) +
    (d+1)*(polynomial.bernoulli d).eval x - (d+1)*(polynomial.bernoulli d).eval x,
    from by ring,],
    rw [show (d+1)*((polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (polynomial.bernoulli d).eval x) =
    (d+1)*((polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (polynomial.bernoulli d).eval x) +
    (d+1)*(polynomial.bernoulli d).eval x - (d+1)*(polynomial.bernoulli d).eval x,
    from by ring,],
    -- we get that 
    -- $$ (d + 1) (1 + x)^d - (d + 1) x^d = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1} $$
    rw [show (d+1)*((polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (polynomial.bernoulli d).eval x) =
    (d+1)*(polynomial.bernoulli d).eval x - (d+1)*(polynomial.bernoulli d).eval x,
    from by ring,
    show (d+1)*(polynomial.bernoulli d).eval x - (d+1)*(polynomial.bernoulli d).eval x =
    (d+1)*(polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (d+1)*(polynomial.bernoulli d).eval x,
    from by ring,
    show (d+1)*(polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (d+1)*(polynomial.bernoulli d).eval x =
    (d+1)*(polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (d+1)*(polynomial.bernoulli d).eval x,
    from by ring,
    show (d+1)*(polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (d+1)*(polynomial.bernoulli d).eval x =
    (d+1)*((polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (polynomial.bernoulli d).eval x),
    from by ring,],
    rw [show (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)) - (polynomial.bernoulli d).eval x,
    from by ring,
    show (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)),
    from by ring,],
    rw [show (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + (d+1)*(d * x^(d - 1)),
    from by ring,
    show (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1),
    from by ring,],
  },
  show (polynomial.bernoulli (d+1)).eval (1 + x) = (polynomial.bernoulli (d+1)).eval x + (d+1) * x^(d - 1 + 1),
  from by rw [show d + 1 = (d - 1 + 1) + 1, from by ring,
    show (polynomial.bernoulli (d - 1 + 1 + 1)).eval (1 + x) = (polynomial.bernoulli (d - 1 + 1 + 1)).eval x + (d - 1 + 1 + 1) * x^(d - 1 + 1 + 1 - 1),
    from by rw [show d = d - 1 + 1, from by ring,
      show (polynomial.bernoulli (d - 1 + 1 + 1)).eval (1 + x) = (polynomial.bernoulli (d - 1 + 1 + 1)).eval x + (d - 1 + 1 + 1) * x^(d - 1 + 1),
      from
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) := 
begin
  have h1 : ∀ m : ℕ, m < n → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by {
    assume m : ℕ,
    assume hm : m < n,
    induction m with m hm,
    show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(-1 + 0), by {
      simp,
    },
    show (polynomial.bernoulli (m + 1)).eval (1 + x) = (polynomial.bernoulli (m + 1)).eval x + (m + 1) * x^(-1 + m + 1), from by {
      simp,
      have h1 : (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from by {
        apply hm,
        apply nat.lt_succ_of_lt hm,
      },
      rw h1,
      ring,
    },
  },
  have h2 : (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1), from by {
    apply h1,
    apply nat.lt_succ_self,
  },
  show (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1), from by {
    apply h2,
  },
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
