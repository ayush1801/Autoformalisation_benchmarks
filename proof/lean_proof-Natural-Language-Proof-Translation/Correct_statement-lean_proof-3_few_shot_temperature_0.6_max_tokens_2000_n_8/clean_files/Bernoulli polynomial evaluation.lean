import number_theory.bernoulli


--OUTPUT 1
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
    norm_num,
    by_cases hd_eq_zero : d = 0,
      rw hd_eq_zero,
      norm_num,
    rw polynomial.pow_add,
    have h1 : (1 + x) ^ d = x ^ d + d * x ^ (d - 1), from by {
      rw [← polynomial.pow_add, polynomial.pow_one, mul_one, add_comm],
    },
    rw [← polynomial.pow_add, add_comm, polynomial.pow_one, mul_one, ← hd d hd_eq_zero, ← h1],
    rw polynomial.eval_add,
    rw polynomial.eval_sum,
    rw polynomial.eval_mul,
    rw polynomial.eval_C,
    rw polynomial.eval_pow,
    rw polynomial.eval_pow,
    rw polynomial.eval_C,
    norm_num,
    rw [add_assoc, ← mul_assoc, ← mul_assoc],
    rw ← C_mul_X,
    rw polynomial.eval_add,
    rw polynomial.eval_mul,
    rw polynomial.eval_C,
    rw polynomial.eval_X,
    rw polynomial.eval_mul,
    rw polynomial.eval_C,
    rw polynomial.eval_pow,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_pow,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_pow,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_add,
    rw polynomial.eval_mul,
    rw polynomial.eval_C,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_mul,
    rw polynomial.eval_C,
    rw polynomial.eval_pow,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_pow,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_pow,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    by ring,
end

--OUTPUT 2
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n,
  assume (d : ℕ) (h : ∀ m : ℕ, m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1)),
  have h1 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from begin
    have h2 : (d + 1) * (1 + x)^d - (d + 1) * x^d = ∑ k in finset.range (d + 1), (d + 1) * (finset.range d).sum (λ i, ((d + 1 - i) * (1 + x)^(i - 1) * x^(d - i)) / (i : ℚ)), from begin
      rw finset.sum_mul_distrib,
      rw finset.sum_range_succ,
      rw finset.sum_range_succ,
      rw finset.sum_range_succ,
      rw [← mul_one ((d + 1) : ℚ), ← mul_one ((d + 1) : ℚ), ← mul_one ((d + 1) : ℚ)],
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum,
      rw finset.mul_sum
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  {
    show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1),
    calc (polynomial.bernoulli 0).eval (1 + x) = 1 : by apply polynomial.bernoulli_zero_eval
    ... = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1) : by rw [polynomial.bernoulli_zero_eval, mul_zero, add_zero, pow_zero],
  },
  {
    have h1 : (d + 1) * (1 + x)^d = (d + 1) * x^d + (d + 1) * x^(d - 1), from by {
      rw mul_comm (d + 1) ((1 + x)^d), rw pow_add, rw [mul_comm (d + 1) (1 + x), mul_one],
    },
    have h2 : (d + 1) * x^(d - 1) = (d + 1) * x^(d - 1) + (d + 1) * x^(d - 1), from by {
      rw add_zero,
    },
    rw ← add_assoc,
    have h3 : (d + 1) * x^(d - 1) = ∑ (k : ℕ) in finset.range (d + 1), (d + 1) * (d choose k) * x^(k - 1), from by {
      rw ← polynomial.eval_sum,
      rw ← polynomial.eval_mul,
      rw ← polynomial.eval_pow,
      rw ← polynomial.eval_mul,
      rw polynomial.eval_C,
      rw polynomial.eval_X,
      rw polynomial.eval_C,
      rw polynomial.eval_X,
      rw mul_comm,
      rw mul_comm (d + 1),
      rw polynomial.eval_X,
      rw polynomial.eval_C,
      rw finset.sum_const_mul,
      rw mul_comm (d + 1),
      rw ← polynomial.eval_mul,
      rw ← polynomial.eval_sum,
      rw polynomial.eval_bernoulli,
      rw finset.sum_const_mul,
    },
    rw h3,
    have h4 : (polynomial.bernoulli d).eval (1 + x) = (d + 1) * (1 + x)^d + ∑ (k : ℕ) in finset.range d, (d + 1) * (d choose k) * x^(k - 1), from by {
      rw ← polynomial.eval_sum,
      rw ← polynomial.eval_mul,
      rw ← polynomial.eval_pow,
      rw ← polynomial.eval_mul,
      rw polynomial.eval_C,
      rw polynomial.eval_X,
      rw polynomial.eval_C,
      rw polynomial.eval_X,
      rw mul_comm,
      rw mul_comm (d + 1),
      rw polynomial.eval_X,
      rw polynomial.eval_C,
      rw finset.sum_const_mul,
      rw mul_comm (d + 1),
      rw ← polynomial.eval_mul,
      rw ← polynomial.eval_sum,
      rw polynomial.eval_bernoulli,
      rw finset.sum_const_mul,
    },
    have h5 : (polynomial.bernoulli d).eval (1 + x) = (d + 1) * x^d + ∑ (k : ℕ) in finset.range d, (d + 1) * (d choose k) * x^(k - 1), from by {
      rw h4,
      rw h1,
      rw add_assoc,
      rw h2,
    },
    have h6 : (polynomial.bernoulli d).eval x + d * x^(d - 1) = (d + 1) * x^d + ∑ (k : ℕ) in finset.range d, (d + 1) * (d choose k) * x^(k - 1), from by {
      rw ← polynomial.eval_sum,
      rw ← polynomial.eval_mul,
      rw ← polynomial.eval_pow,
      rw ← polynomial.eval_mul,
      rw polynomial.eval_C,
      rw polynomial.eval_X,
      rw polynomial.eval_C,
      rw polynomial.eval_X,
      rw mul_comm,
      rw mul_comm (d + 1),
      rw polynomial.eval_X,
      rw polynomial.eval_C,
      rw finset.sum_const_mul,
      rw mul_comm (d + 1),
      rw ← polynomial.eval_mul,
      rw ← polynomial.eval_sum,
      rw polynomial.eval_bernoulli,
      rw finset.sum_const_mul,
    },
    have h7 : (polynomial.bernoulli d).eval x + d * x^(d - 1) = (polynomial.bernoulli d).eval (1 + x), from
    by {rw h5, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw add_right_neg, rw add_zero, rw add_zero, rw add_zero, rw add_zero, rw add_zero},
    have h8 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from by {rw ← h7, assumption},
    have h9 : ∀ (k : ℕ), k < d → (polynomial.bernoulli k).eval (1 + x) = (polynomial.bernoulli k).eval x + k * x^(k - 1), from assume (k : ℕ) (hk : k < d), by {rw ← hd k hk,},
    have h10 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from by {
      rw ← h8,
      apply h9,
      assumption,
    },
    have h11 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from by {
      rw ← h10,
      assumption,
    },
    show (polynomial.bernoulli (d + 1)).eval (1 + x) = (polynomial.bernoulli (d + 1)).eval x + (d + 1) * x^(d), from by {
      rw ← h11,
      rw ← pow_add,
      rw ← mul_comm,
      rw ← mul_comm,
      rw ← pow_add,
      rw ← mul_comm,
      rw ← mul_comm,
    },
  },
end

--OUTPUT 4
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  {
    unfold polynomial.bernoulli,
    rw [polynomial.eval_C],
    rw [zero_add],
    rw [one_pow],
    rw [one_mul],
    exact (eq.symm (polynomial.eval_C _ _)),
  },
  {
    have h1 : (d + 1) * (1 + x)^d - (d + 1) * x^d = (polynomial.sum (λ (k : ℕ), (polynomial.C (d + 1) * polynomial.X ^ k) * (polynomial.C (k) * polynomial.X ^ (k - 1))) (d + 1)).eval x,
    {
      rw [polynomial.eval_sum],
      rw [polynomial.eval_add],
      rw [polynomial.eval_mul],
      rw [polynomial.eval_C],
      rw [polynomial.eval_mul],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],
      rw [polynomial.eval_C],
      rw [polynomial.eval_X],

end --Needs more than 2000 tokens!

--OUTPUT 5
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  { calc (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval 1 + 0 * x ^ (0 - 1) : by simp
    ... = (polynomial.bernoulli 0).eval 1 + 0 : by simp
    ... = 1 : by simp
    ... = (polynomial.bernoulli 0).eval x + 0 : by simp
    ... = (polynomial.bernoulli 0).eval x + 0 * x ^ (0 - 1) : by simp
    ... = (polynomial.bernoulli 0).eval x + d * x ^ (0 - 1) : by simp
    ... = (polynomial.bernoulli 0).eval x + d * x ^ (d - 1) : by simp, },
  { calc (polynomial.bernoulli (d + 1)).eval (1 + x) = (polynomial.bernoulli (d + 1)).eval 1 + (d + 1) * x ^ (d + 1 - 1) : by simp
    ... = (polynomial.bernoulli (d + 1)).eval 1 + (d + 1) * x ^ d : by simp
    ... = (polynomial.bernoulli (d + 1)).eval x + (d + 1) * x ^ d : by simp
    ... = (polynomial.bernoulli (d + 1)).eval x + d * x ^ d + x ^ d : by simp
    ... = (polynomial.bernoulli (d + 1)).eval x + d * x ^ d + (polynomial.bernoulli 1).eval x : by simp
    ... = (polynomial.bernoulli (d + 1)).eval x + d * x ^ d + x : by simp
    ... = (polynomial.bernoulli (d + 1)).eval x + (d * x ^ d + x) : by simp
    ... = (polynomial.bernoulli (d + 1)).eval x + (d * x ^ (d - 1) + x ^ (d - 1)) : by simp
    ... = (polynomial.bernoulli (d + 1)).eval x + (d + 1) * x ^ (d - 1) : by simp
    ... = (polynomial.bernoulli (d + 1)).eval x + (d + 1) * x ^ (d + 1 - 1) : by simp
    ... = (polynomial.bernoulli (d + 1)).eval x + (d + 1) * x ^ (d + 1 - 1) : by simp
    ... = (polynomial.bernoulli (d + 1)).eval x + (d + 1) * x ^ (d + 1 - 1) : by simp, }
end

--OUTPUT 6
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  {
    show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1),
    {
      rw [polynomial.bernoulli,eval_zero,eval_zero,zero_mul],
      ring,
    }
  },
  {
    show (polynomial.bernoulli (d + 1)).eval (1 + x) = (polynomial.bernoulli (d + 1)).eval x + (d + 1) * x^((d + 1) - 1),
    {
      rw [polynomial.bernoulli,eval_add,eval_mul,eval_C,eval_X,eval_add,eval_mul,eval_C,eval_X],
      rw [eval_add,eval_mul,eval_C,eval_X,eval_add,eval_mul,eval_C,eval_X],
      have h1 : (d + 1) * (1 + x)^d = (d + 1) * (1 + x)^d + (d + 1) * x^d - (d + 1) * x^d,
      {
        ring,
      },
      rw [← h1,← hd,add_sub_cancel,sub_add_cancel],
      rw [mul_one,mul_one,add_comm,mul_comm,mul_comm],
      ring,
    }
  }
end

--OUTPUT 7
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  {
    have h1 : (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(-1), from 
      by {rw [(polynomial.bernoulli 0).eval_zero], rw [zero_mul], rw [nat.sub_zero], rw [(polynomial.bernoulli 0).eval_zero], },
    exact h1,
  },
  {
    have h1 : (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(-1), from 
      by {rw [(polynomial.bernoulli 0).eval_zero], rw [zero_mul], rw [nat.sub_zero], rw [(polynomial.bernoulli 0).eval_zero], },
    have h2 : (polynomial.bernoulli (d+1)).eval (1 + x) = (polynomial.bernoulli (d+1)).eval x + (d+1) * x^(d), from
    begin
      rw [(polynomial.bernoulli (d+1)).eval_add],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [one_add_one],
      rw [(polynomial.bernoulli (d+1)).eval_mul],
      rw [(polynomial.bernoulli (d+1)).eval_X],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [one_add_one],
      rw [(polynomial.bernoulli (d+1)).eval_X],
      rw [(polynomial.bernoulli d).eval_add],
      rw [hd],
      rw [(polynomial.bernoulli d).eval_zero],
      rw [mul_zero],
      rw [(polynomial.bernoulli d).eval_zero],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [add_mul],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [mul_add],
      rw [add_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      rw [one_mul],
      rw [mul_one],
      rw [mul_one],
      rw [mul_one],
      r
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) := 
begin
  have h1 : ∀ n : ℕ, ∀ x : ℚ, (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1), from assume (n : ℕ) (x : ℚ), 
    by {induction n with d hd, obviously, assume d : ℕ, assume hd : ∀ n : ℕ, ∀ x : ℚ, (polynomial.bernoulli n).eval (1+x) = (polynomial.bernoulli n).eval x + n*x^(n - 1),
      calc (polynomial.bernoulli (d + 1)).eval (1 + x)
           = (polynomial.bernoulli (d + 1)).eval (1 + x) : by refl
      ... = (polynomial.bernoulli (d + 1)).eval (1 + x) : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by rw polynomial.eval_of_degree_eq_zero
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : by refl
      ... = (d + 1) * (1 + x)
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
