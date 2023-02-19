import number_theory.bernoulli


--OUTPUT 1
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  {
    unfold polynomial.bernoulli polynomial.eval,
    by_cases (x = 0),
    {
      replace h : x = 0, from h,
      clear h,
      rw h,
      auto [mul_zero, zero_add],
    },
    {
      have h2 : x ≠ 0, from h,
      have h3 : (1 : ℚ) ≠ 0, from by auto [ne.symm h2],
      have h4 : 1 / x ≠ 0, from by auto [div_ne_zero h3],
      have h5 : x ≠ 0, from ne.symm h,
      have h6 : (1 + x) ≠ 0, from by auto [add_ne_zero],
      have h7 : (1 + x) ≠ 0, from h6,
      have h8 : (1 + x) ≠ 0, from by auto [add_ne_zero],
      have h9 : 1 + x ≠ 0, from h8,
      have h10 : (1 + x) ≠ 0, from by auto [add_ne_zero],
      have h11 : (1 + x) ≠ 0, from by auto [add_ne_zero],
      have h12 : ↑(1 + x) ≠ 0, from h11,
      have h13 : (1 : ℚ) ≠ 0, from by auto [ne.symm h2],
      have h14 : 1 ≠ 0, from h13,
      have h15 : (1 : ℚ) ≠ 0, from by auto [ne.symm h2],
      have h16 : (1 : ℚ) ≠ 0, from by auto [ne.symm h2],
      have h17 : (1 : ℚ) ≠ 0, from by auto [ne.symm h2],
      have h18 : (1 : ℚ) ≠ 0, from by auto [ne.symm h2],
      have h19 : (1 : ℚ) ≠ 0, from by auto [ne.symm h2],
      have h20 : (1 : ℚ) ≠ 0, from by auto [ne.symm h2],
      have h21 : 1 + x ≠ 0, from mul_ne_zero (cast h19) (cast h20),
      have h22 : (1 + x) ≠ 0, from h21,
      have h23 : (1 + x) ≠ 0, from h22,
      have h24 : 1 ≠ 0, from ne.symm h2,
      have h25 : 1 + x ≠ 0, from mul_ne_zero (cast h23) (cast h24),
      have h26 : (1 + x) ≠ 0, from h25,
      have h27 : (1 + x) ≠ 0, from by auto [add_ne_zero],
      have h28 : (1 + x) ≠ 0, from h27,
      rw show (1 : ℚ) = 1, from rfl,
      rw show (1 : ℚ) = 1, from rfl,
      rw show (1 : ℚ) = 1, from rfl,
      rw show (1 : ℚ) = 1, from rfl,
      rw show 1 + x = ↑(1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show x = (↑x : ℚ), from rfl,
      rw show ↑(x : ℚ) = (↑x : ℚ), from rfl,
      rw show x = (↑x : ℚ), from rfl,
      rw show ↑(x : ℚ) = (↑x : ℚ), from rfl,
      rw show x = (↑x : ℚ), from rfl,
      rw show ↑(x : ℚ) = (↑x : ℚ), from rfl,
      rw show x = (↑x : ℚ), from rfl,
      rw show ↑(x : ℚ) = (↑x : ℚ), from rfl,
      rw show ↑(x : ℚ) = (↑x : ℚ), from rfl,
      have h29 : (1 + x) ≠ 0, from by auto [add_ne_zero],
      have h30 : (1 + x) ≠ 0, from by auto [add_ne_zero],
      rw show (1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (1 + x), from rfl,
      rw show (1 + x) = (1 + x), from rfl,
      rw show ↑(1 + x) = (
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n,
  assume d h,
  have h1 : (d + 1) * (1 + x)^d - (d + 1) * x^d = (polynomial.sum (λ (k : ℕ), (polynomial.C (nat.choose (d + 1) k)) * polynomial.X^k)).eval x, from begin
    calc (d + 1) * (1 + x)^d - (d + 1) * x^d = 
      (polynomial.sum (λ (k : ℕ), (polynomial.C (nat.choose (d + 1) k)) * polynomial.X^k)).eval (1 + x) - (d + 1) * x^d : by auto [polynomial.eval_sum]
    ... = (polynomial.sum (λ (k : ℕ), (polynomial.C (nat.choose (d + 1) k)) * polynomial.X^k)).eval x : begin
        apply nat.induction_on d,
        repeat {rw ←add_zero},
        simp,
        assume d h,
        rw [nat.add_succ, polynomial.eval_sum],
        have h1 : ∀ k : ℕ, (polynomial.C (nat.choose (d + 1) k)) * polynomial.X^k * (1 + x) =
                            (polynomial.C (nat.choose (d + 1) k)) * (polynomial.X^k * (1 + x)), from by repeat {rw polynomial.mul_one},
        rw h1,
        rw polynomial.eval_mul,
        rw polynomial.eval_X,
        rw polynomial.eval_C,
        rw polynomial.eval_X,
        rw polynomial.eval_C,
        ring,
    end
    ... = (polynomial.sum (λ (k : ℕ), (polynomial.C (nat.choose (d + 1) k)) * polynomial.X^k)).eval x : rfl,
  end,
  have h2 : (polynomial.sum (λ (k : ℕ), (polynomial.C (nat.choose (d + 1) k)) * polynomial.X^k)).eval x = (polynomial.sum (λ (k : ℕ), k * polynomial.X^(k - 1))).eval x, from begin
    rw polynomial.eval_sum,
    apply nat.induction_on d,
    simp,
    assume d h,
    rw [nat.add_succ, polynomial.eval_sum],
    have h1 : ∀ k : ℕ, (polynomial.C (nat.choose (d + 1) k)) * polynomial.X^k = 
                            polynomial.C k * polynomial.X^(k - 1), from by auto [polynomial.C_one, nat.choose_one],
    rw h1,
    rw polynomial.eval_mul,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    ring,
  end,
  rw h1,
  rw h2,
  rw [nat.add_succ, polynomial.eval_sum],
  have h3 : ∀ k : ℕ, (polynomial.C k * polynomial.X^(k - 1)) * x = 
                          k * (polynomial.X^(k - 1) * x), from by auto [polynomial.mul_one],
  rw h3,
  rw polynomial.eval_mul,
  rw polynomial.eval_X,
  rw polynomial.eval_C,
  rw polynomial.eval_X,
  rw polynomial.eval_C,
  ring,
end

--OUTPUT 3
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
induction n with d hd,
{ simp [polynomial.bernoulli, polynomial.eval_add, polynomial.eval_C, polynomial.eval_mul,
  polynomial.eval_X, polynomial.eval_nat_cast, polynomial.eval_sub, polynomial.eval_X_sub_C,
  polynomial.eval_C_sub_X, polynomial.eval_sub_C_C, polynomial.eval_sub_X_C, polynomial.eval_sub_C_X,
  polynomial.eval_sub_X_X, polynomial.eval_pow, polynomial.eval_neg, polynomial.eval_one, 
  polynomial.eval_C_add, polynomial.eval_add_C_C],
},
{ simp [polynomial.bernoulli, polynomial.eval_add, polynomial.eval_C, polynomial.eval_mul,
  polynomial.eval_X, polynomial.eval_nat_cast, polynomial.eval_sub, polynomial.eval_X_sub_C,
  polynomial.eval_C_sub_X, polynomial.eval_sub_C_C, polynomial.eval_sub_X_C, polynomial.eval_sub_C_X,
  polynomial.eval_sub_X_X, polynomial.eval_pow, polynomial.eval_neg, polynomial.eval_one, 
  polynomial.eval_C_add, polynomial.eval_add_C_C],
}
end

--OUTPUT 4
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  rw[polynomial.eval_add, polynomial.eval_one, polynomial.eval_one],
  have h : ∀ m : ℕ, m ≤ n → (m : ℚ) ≤ n, from λ m hm, by linarith,
  induction n with d hd,
  { calc (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval (x + 1) :  by simp
                      ... = (polynomial.bernoulli 0).eval x + (0 : ℚ) * x^(0 - 1) : by simp [hd (by linarith)]
                      ... = (polynomial.bernoulli 0).eval x + (0 : ℚ) : by simp [polynomial.eval_zero]
                      ... = (polynomial.bernoulli 0).eval x : by simp [zero_add]},
  {calc (polynomial.bernoulli (d + 1)).eval (1 + x) = (polynomial.bernoulli (d + 1)).eval (x + 1) :  by simp
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d + 1 : ℚ) * x^(d + 1 - 1) : by rw[polynomial.eval_add, polynomial.eval_one, polynomial.eval_one, hd (by linarith)]
                     ... = (polynomial.bernoulli (d + 1)).eval x + d * x^d + x^d : by simp
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d * x^d + x^d) : by simp [polynomial.eval_add, polynomial.eval_one, polynomial.eval_one]
                     ... = (polynomial.bernoulli (d + 1)).eval x + d * x^d + x^d : by simp [polynomial.eval_add, polynomial.eval_one, polynomial.eval_one]
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d * x^d + x^d) : by simp [polynomial.eval_add, polynomial.eval_one, polynomial.eval_one]
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * (x^d + 1) : by simp [ring]
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * ((x + 1)^d) : by simp [polynomial.eval_add, polynomial.eval_one, polynomial.eval_one, polynomial.eval_one]
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * ((x + 1)^d - x^d) : by ring
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * (sum (λ (m : ℕ), (d : ℚ) choose m * x^m) (d - 1)) : by rw[polynomial.eval_one, polynomial.eval_one]
                     ... = (polynomial.bernoulli (d + 1)).eval x + sum (λ (m : ℕ), (d : ℚ) choose m * (d : ℚ) * x^m) (d - 1) : by simp [ring]
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * sum (λ (m : ℕ), m * x^m) (d - 1) : by simp
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * sum (λ (m : ℕ), m * x^m) (d - 1) : by simp
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * sum (λ (m : ℕ), ((m + 1) - 1 : ℚ) * x^m) (d - 1) : by simp
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m - (1 : ℚ) * x^m) (d - 1) : by refl
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m) (d - 1) - (d : ℚ) * sum (λ (m : ℕ), (1 : ℚ) * x^m) (d - 1) : by simp [sum_sub_sum]
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m) (d - 1) - (d : ℚ) * (sum (λ (m : ℕ), (1 : ℚ) * x^m) (d - 1)) : by simp
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m) (d - 1) - (d : ℚ) * (x^(d - 1) + sum (λ (m : ℕ), 1) (d - 2)) : by simp [sum_range_succ]
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m) (d - 2) - (d : ℚ) * x^(d - 1) : by simp [sum_range_succ]
                     ... = (polynomial.bernoulli (d + 1)).eval x + (d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m) (d - 2) - (d : ℚ) * x^(d - 1) : by simp [sum_range_succ]
                     ... = ((d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m) (d - 2) + (polynomial.bernoulli (d + 1)).eval x - (d : ℚ) * x^(d - 1)) : by simp
                     ... = ((d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m) (d - 2) + ((polynomial.bernoulli (d + 1)).eval x - (d : ℚ) * x^(d - 1))) : by refl
                     ... = ((d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m) (d - 2) + ((polynomial.bernoulli (d + 1)).eval x - (d : ℚ) * x^(d - 1))) : by refl
                     ... = (d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m) (d - 2) + (polynomial.bernoulli (d + 1)).eval x - (d : ℚ) * x^(d - 1) : by simp
                     ... = (d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ) * x^m) (d - 2) + (polynomial.bernoulli (d + 1)).eval x - (d : ℚ) * x^(d - 1) : by simp
                     ... = (d : ℚ) * sum (λ (m : ℕ), (m + 1 : ℚ)
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with h hd,
  { simp },
  { have h1 : polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * (polynomial.X : polynomial ℚ)^k) (λ (k : ℕ), k * (polynomial.X : polynomial ℚ)^(k - 1)) =
    (n + 1) * (polynomial.X : polynomial ℚ) ^ n, from by auto [polynomial.sum],
    have h2 : polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * ((polynomial.X : polynomial ℚ)^k)) (λ (k : ℕ), k * ((polynomial.X : polynomial ℚ)^(k - 1))) =
    polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * ((polynomial.X : polynomial ℚ)^k)) (λ (k : ℕ), k * x^(k - 1)), from by auto [polynomial.sum],
    have h3 : n * (1 + x) ^ n - n * x ^ n = polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * ((polynomial.X : polynomial ℚ)^k)) (λ (k : ℕ), k * ((polynomial.X : polynomial ℚ)^(k - 1))), from
      calc n * (1 + x) ^ n - n * x ^ n = polynomial.sum (λ (k : ℕ), n * ↑(choose (n + 1) k) * ((polynomial.X : polynomial ℚ)^k)) (λ (k : ℕ), (k + 1) * ((polynomial.X : polynomial ℚ)^k)) : by auto [polynomial.sum, polynomial.sum, polynomial.sum, polynomial.sum]
    ... = polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * ((polynomial.X : polynomial ℚ)^k)) (λ (k : ℕ), k * ((polynomial.X : polynomial ℚ)^k)) + (n + 1) * ((polynomial.X : polynomial ℚ)^n) : by auto [polynomial.sum]
    ... = (n + 1) * ((polynomial.X : polynomial ℚ)^n) : by auto [polynomial.sum, h1],
    have h4 : (polynomial.bernoulli (n + 1)).eval (1 + x) - (polynomial.bernoulli (n + 1)).eval x =
    polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * ((polynomial.X : polynomial ℚ)^k)) (λ (k : ℕ), k * ((polynomial.X : polynomial ℚ)^(k - 1))), from by auto [polynomial.sum],
    have h5 : (polynomial.bernoulli (n + 1)).eval (1 + x) - (polynomial.bernoulli (n + 1)).eval x =
    polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * ((polynomial.X : polynomial ℚ)^k)) (λ (k : ℕ), k * x^(k - 1)), from by auto [h2],
    have h6 : (polynomial.bernoulli (n + 1)).eval (1 + x) - (polynomial.bernoulli (n + 1)).eval x =
    n * (1 + x) ^ n - n * x ^ n, from by auto [h3, h4],
    have h7 : (polynomial.bernoulli (n + 1)).eval (1 + x) - (polynomial.bernoulli (n + 1)).eval x =
    polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * x^k) (λ (k : ℕ), k * x^(k - 1)), from by auto [h5],
    have h8 : (polynomial.bernoulli (n + 1)).eval (1 + x) - (polynomial.bernoulli (n + 1)).eval x + (n + 1) * x ^ n =
    polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * x^k) (λ (k : ℕ), (k + 1) * x^k), from by auto [polynomial.sum, polynomial.sum, polynomial.sum],
    have h9 : (polynomial.bernoulli (n + 1)).eval (1 + x) =
    polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * x^k) (λ (k : ℕ), (k + 1) * x^k), from by auto [h6, h7, h8],
    have h10 : polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * x^k) (λ (k : ℕ), (k + 1) * x^k) =
    polynomial.sum (λ (k : ℕ), (n + 1) * ↑(choose (n + 1) k) * x^k) (λ (k : ℕ), n * x^(n - 1)), from by auto [polynomial.sum],
    have h11 : (polynomial.bernoulli (n + 1)).eval (1 + x) =
    (n + 1) * x^n + n * x^n, from by auto [h9, h10, polynomial.sum, polynomial.sum],
    show (polynomial.bernoulli (n + 1)).eval (1 + x) = (polynomial.bernoulli (n + 1)).eval x + (n + 1) * x^(n + 1 - 1), from by auto [(n + 1) * x^(n + 1 - 1)],
  },
end

--OUTPUT 6
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
    induction n with l hl,
    rw polynomial.bernoulli,
    simp,
    rw add_zero,
    simp,

    rw polynomial.bernoulli at hl,
    simp [polynomial.eval_sum, polynomial.eval_C],
    rw polynomial.bernoulli,
    simp,
    rw add_comm,
    rw mul_comm (1 + x) x,
    rw add_assoc,
    rw hl,
    rw add_assoc (l * x ^ (l - 1)),
    rw mul_pow,
    rw mul_comm,
    rw add_comm,
    rw mul_comm ((1 + x) * x) x,
    rw ← mul_assoc,
    rw ← mul_comm x,
    rw ← pow_succ,
    rw mul_comm (l + 1) x,
end

--OUTPUT 7
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with n hn generalizing x,
  {
    show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x, from by simp [eval_C],
  },
  {
    have h1 : (polynomial.prod (λ (m : ℕ), C (m + 1) * (X^m + X^(m + 1))) n).eval (1 + x) =
              (polynomial.prod (λ (m : ℕ), C (m + 1) * (X^m + X^(m + 1))) n).eval x, from by auto [eval_prod],
    have h2 : (polynomial.prod (λ (m : ℕ), C (m + 1) * (X^m + X^(m + 1))) n).eval x =
              (polynomial.prod (λ (m : ℕ), C (m + 1) * X^m) n).eval x +
              (polynomial.prod (λ (m : ℕ), C (m + 1) * X^(m + 1)) n).eval x, from by auto [eval_prod, eval_add],
    have h3 : (polynomial.prod (λ (m : ℕ), C (m + 1) * X^m) n).eval x =
              (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x *
              (polynomial.prod (λ (m : ℕ), X^m) n).eval x, from by auto [eval_prod],
    have h4 : (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x =
              (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval 0, from by auto [eval_prod_const],
    have h5 : (polynomial.prod (λ (m : ℕ), X^m) n).eval x =
              polynomial.prod (λ (m : ℕ), X) n, from by auto [eval_prod],
    have h6 : (polynomial.prod (λ (m : ℕ), C (m + 1) * X^(m + 1)) n).eval x =
              (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x *
              (polynomial.prod (λ (m : ℕ), X) n) ^ (n + 1), from by auto [eval_prod],
    have h7 : (polynomial.prod (λ (m : ℕ), C (m + 1) * X^(m + 1)) n).eval x =
              (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x *
              (polynomial.prod (λ (m : ℕ), X) n) *
              (polynomial.prod (λ (m : ℕ), X) n) ^ n, from by auto [eval_prod],
    have h8 : (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x =
              (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval 0, from by auto [eval_prod_const],
    have h9 : (polynomial.prod (λ (m : ℕ), C (m + 1) * X^m) n).eval (1 + x) =
              (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval (1 + x) *
              (polynomial.prod (λ (m : ℕ), X^m) n).eval (1 + x), from by auto [eval_prod],
    have h10 : (polynomial.prod (λ (m : ℕ), C (m + 1) * X^(m + 1)) n).eval (1 + x) =
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval (1 + x) *
               (polynomial.prod (λ (m : ℕ), X) n) *
               (polynomial.prod (λ (m : ℕ), X) n) ^ n, from by auto [eval_prod],
    have h11 : (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval (1 + x) =
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x +
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n) *
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x, from by auto [eval_prod],
    have h12 : (polynomial.prod (λ (m : ℕ), X^m) n).eval (1 + x) =
               (polynomial.prod (λ (m : ℕ), X^m) n).eval x, from by auto [eval_prod],
    have h13 : (polynomial.prod (λ (m : ℕ), X) n) ^ (n + 1) =
               (polynomial.prod (λ (m : ℕ), X) n) * (polynomial.prod (λ (m : ℕ), X) n) ^ n, from by auto [eval_prod],
    have h14 : (polynomial.prod (λ (m : ℕ), C (m + 1)) n) *
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x =
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x *
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n), from by auto [eval_prod, mul_comm],
    have h15 : (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x =
               polynomial.prod (λ (m : ℕ), C (m + 1)) n, from by auto [eval_prod_const],
    have h16 : (polynomial.prod (λ (m : ℕ), C (m + 1)) n) *
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval 0 =
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval 0 *
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n), from by auto [eval_prod, mul_comm],
    have h17 : (polynomial.prod (λ (m : ℕ), C (m + 1)) n) *
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval x *
               (polynomial.prod (λ (m : ℕ), X^m) n).eval x =
               (polynomial.prod (λ (m : ℕ), C (m + 1) * X^m) n).eval x *
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n), from by auto [eval_prod, mul_comm],
    have h18 : (polynomial.prod (λ (m : ℕ), C (m + 1)) n) *
               (polynomial.prod (λ (m : ℕ), C (m + 1)) n).eval 0 *
               (polynomial.prod (λ (m : ℕ), X^m) n).eval x =
               (polynomial.prod (λ (m : ℕ), C (m + 1) * X^m) n).eval 0 *
               (polynomial.prod (λ (m :
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : ∀ (m : ℕ) (x : ℚ), m < n → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x ^ (m - 1),
  { assume m x h1,
    have h2 : ∀ k : ℕ, k ≤ m → (((C (1+x)) ^ (m - k))),
    { assume k h2,
      have h3 : (1 + x)^m = (C x)^m + m * (C x)^(m-1) * (C (1+x))^1, by simp [C, has_mul.one],
      rw has_pow.pow_eq_pow_of_nat_cast h2 at h3,
      have h4 : (1 + x) ^ (m - k) = (C x) ^ (m - k) + m * (C x) ^ (m - k - 1) * (C (1 + x)) ^ 1, from by simp [C, has_mul.one] at h3,
      exact h4,
    },
    have h3 : (polynomial.bernoulli m).eval (1 + x) = ∑ (k : ℕ) in finset.range m, (((C (1 + x)) ^ k) * C (mchoose k)), from by simp [C, has_mul.one],
    have h4 : (polynomial.bernoulli m).eval x = ∑ (k : ℕ) in finset.range m, ((C x ^ k) * C (mchoose k)), from by auto [C, has_mul.one] at h3,
    have h5 : (polynomial.bernoulli m).eval (1 + x) = ∑ (k : ℕ) in finset.range m, ((C x ^ k) * C (mchoose k) + m * C x ^ (k - 1) * C (mchoose k) * C (1 + x)), from by auto [C, has_mul.one] at h3 using [h2],
    have h6 : ∑ (k : ℕ) in finset.range m, (m * C x ^ (k - 1) * C (mchoose k) * C (1 + x)) = m * ∑ (k : ℕ) in finset.range m, (C x ^ (k - 1) * C (mchoose k) * C (1 + x)), from by auto [finset.sum_mul],
    have h7 : ∑ (k : ℕ) in finset.range m, (C x ^ (k - 1) * C (mchoose k) * C (1 + x)) = x ^ (m - 1), from by simp [C, has_mul.one] at h6,
    have h8 : m * (∑ (k : ℕ) in finset.range m, (C x ^ (k - 1) * C (mchoose k) * C (1 + x))) = m * x ^ (m - 1), from by auto at h7,
    have h9 : finset.sum finset.range m (λ (k : ℕ), C x ^ k * C (mchoose k) + m * C x ^ (k - 1) * C (mchoose k) * C (1 + x)) = finset.sum finset.range m (λ (k : ℕ), C x ^ k * C (mchoose k)) + m * x ^ (m - 1), from by rw finset.sum_add h4 h8,
    exact h9,
  },
  have h2 : ∀ (m : ℕ) (x : ℚ), m < n → (polynomial.bernoulli m).eval x = mchoose m, from by auto using [bernoulli_eval, nat.eq_zero_of_le_zero],
  have h3 : ∀ (m : ℕ) (x : ℚ), m < n →  mchoose m * x^(m - 1) = m * x^(m - 1), from by auto [mul_comm, nat.choose_eq_mul_succ_pred_div_succ, nat.one_mul],
  have h4 : ∀ (m : ℕ) (x : ℚ), m < n → (polynomial.bernoulli m).eval x + m * x ^ (m - 1) = mchoose m + m * x ^ (m - 1), from by auto [h2, h3],
  have h5 : ∀ (m : ℕ) (x : ℚ), m < n → (polynomial.bernoulli m).eval (1 + x) = mchoose m + m * x ^ (m - 1), from by auto [h1, h4],
  by_contradiction h6,
  have h7 : ∀ (m : ℕ) (x : ℚ), m < n → (polynomial.bernoulli m).eval (1 + x) + m * (1 + x) ^ (m - 1) = mchoose m + m * (1 + x) ^ (m - 1) + m * (1 + x) ^ (m - 1), from by auto [h5],
  have h8 : ∀ (m : ℕ) (x : ℚ), m < n → (polynomial.bernoulli m).eval (1 + x) + m * (1 + x) ^ (m - 1) = mchoose m + (1 + m) * (1 + x) ^ (m - 1), from by auto [mul_comm, one_mul, nat.add_comm] at h7,
  have h9 : ∀ (m : ℕ) (x : ℚ), m < n → ((polynomial.bernoulli m).eval (1 + x) + m * (1 + x) ^ (m - 1)) * ((C (1 + x)) ^ n) = (mchoose m + (1 + m) * (1 + x) ^ (m - 1)) * ((C (1 + x)) ^ n), from by auto at h8,
  have h10 : ∀ (m : ℕ) (x : ℚ), m < n → ∑ (k : ℕ) in finset.range m, (polynomial.bernoulli k).eval (1 + x) + k * (1 + x) ^ (k - 1) = (1 + x) ^ (m - 1) * ∑ (k : ℕ) in finset.range m, (1 + k) * (1 + x) ^ (k - 1), from by auto [C, has_mul.one] at h9,
  have h11 : ∀ (m : ℕ) (x : ℚ), m < n → ∑ (k : ℕ) in finset.range m, (polynomial.bernoulli k).eval (1 + x) + k * (1 + x) ^ (k - 1) * (C (1 + x)) ^ n = (1 + x) ^ (m - 1) * ∑ (k : ℕ) in finset.range m, (1 + k) * (1 + x) ^ (k - 1) * (C (1 + x)) ^ n, from by auto [nat.cast_one, one_mul, has_mul.one] at h10,
  have h12 : ∀ (m : ℕ) (x : ℚ), m < n → (1 + x)^m * ∑ (k : ℕ) in finset.range (m + 1), (((C (1 + x)) ^ k) * C (mchoose k)) = (1 + x) ^ (m - 1) * ∑ (k : ℕ) in finset.range m, (1 + k) * (1 + x) ^ (k - 1) * (C (1 + x)) ^ n, from by auto [C, has_mul.one] at h11,
  have h13 : ∀ (m : ℕ) (x : ℚ), m < n → (1 + x)^m * ∑ (k : ℕ) in finset.range (m + 1), ((
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n,
  intros,
  split_ifs with h,
  rw [h, nat.sub_self, pow_zero, add_zero],
  have h2 := polynomial.bernoulli_succ_eq_one_add_eval a x,
  rw [h, diff_pow, diff_pow, h2],
  ring,
  rw [h, pow_one, pow_zero],
  ring,
  rw [h, pow_one, pow_zero, mul_one, add_zero],
  rw polynomial.eval₂_zero,
  rw polynomial.eval₂_zero,
  ring,
  rw [h, pow_zero],
  ring,
  rw polynomial.eval₂_zero,
  ring,
end

--OUTPUT 10
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  rw [nat.zero_eq_zero, polynomial.bernoulli, polynomial.bernoulli, polynomial.eval_C],
  simp, 
  assume x rw [nat.one_eq_one, polynomial.bernoulli, polynomial.bernoulli, polynomial.eval_X, polynomial.eval_add, polynomial.eval_C, nat.one_eq_one],
  suffices h :
    polynomial.eval (of_nat (d + 1) * (X^d - X^d)) (1 + x) =
    polynomial.eval (of_nat (d + 1) * (X^d - X^d)) x + d * x ^ (d - 1),
  simp at h,
  exact h,
  rw [polynomial.eval_mul, polynomial.eval_add, polynomial.eval_neg, polynomial.eval_C, polynomial.eval_X],
  have h1 : (1 + x)^d - x^d = (1 - x) * ((1 + x) ^ (d - 1) + (1 + x) ^ (d - 2) * x + ... + x ^ (d - 1)),
  begin
    have h10 : (1 + x) ^ d - x ^ d = (1 + x) ^ (d - 1) * (1 + x - x),
    by simp [polynomial.add_mul, polynomial.mul_C, polynomial.mul_X_pow, polynomial.mul_one],
    have h11 : (1 + x - x) = (1 - x), 
    by simp,
    rw [h11] at h10,
    rw h10,
    rw [nat.mul_one, mul_comm, mul_assoc],
    induction d with d hd,
    by simp,
    assume x,
    simp,
    assume x d hd,
    have h11 : x ^ (d - 1) + (1 + x) ^ (d - 1) * x = (1 + x) ^ (d - 1) * (1 + x),
    by rw [← add_mul, polynomial.add_C, polynomial.add_X_pow],
    have h12 : (1 + x) ^ d - x ^ d = (1 + x - x) * ((1 + x) ^ (d - 1) + (1 + x) ^ (d - 2) * x + ... + x ^ (d - 1)),
    by simp; rw [← mul_assoc, mul_assoc, mul_comm, mul_assoc, mul_assoc, mul_comm, add_mul, add_mul, ↑_root_.add, nat.mul_one, polynomial.C_1, polynomial.C_0, hd],
    rw h12,
    rw [mul_comm, h11, mul_add, mul_assoc, mul_comm, mul_assoc, ← add_mul, add_mul, ← add_mul, h11, ← add_assoc, mul_comm, mul_assoc],
    rw [← mul_add],
  end,
  rw h1,
  rw mul_comm,
  rw [mul_add, mul_assoc],
  rw [← polynomial.eval_add],
  suffices h2 : polynomial.eval (of_nat (d + 1) * ((1 - x) * (X ^ (d - 1) + X ^ (d - 2) * X + ... + X ^ 0))) (1 + x) = polynomial.eval (of_nat (d + 1) * ((1 - x) * (X ^ (d - 1) + X ^ (d - 2) * X + ... + X ^ 0))) x + polynomial.eval (of_nat (d + 1) * (1 - x) * (X ^ (d - 1))) x,
  begin
    rw mul_comm,
    rw [mul_add, mul_comm],
    rw add_comm,
  end,
  rw [← h2],
  rw add_comm,
  induction d with d hd,
  rw [nat.add_one, nat.zero_eq_zero, zero_add, polynomial.eval_C, polynomial.eval_C],
  simp,
  have h20 : polynomial.eval (of_nat (d + 2) * (1 - x) * (X ^ (d + 1) + X ^ d * X + ... + X ^ 0)) (1 + x) = polynomial.eval ((of_nat (d + 2) * (1 - x) * (X ^ (d + 1) + X ^ d * X + ... + X ^ 0)) + (of_nat (d + 2) * (1 - x) * (X ^ (d + 1)))) (1 + x),
  by simp,
  rw h20,
  have h21 : polynomial.eval (of_nat (d + 2) * (1 - x) * (X ^ (d + 1) + X ^ d * X + ... + X ^ 0)) x + polynomial.eval (of_nat (d + 2) * (1 - x) * (X ^ (d + 1))) x = polynomial.eval ((of_nat (d + 2) * (1 - x) * (X ^ (d + 1) + X ^ d * X + ... + X ^ 0)) + (of_nat (d + 2) * (1 - x) * (X ^ (d + 1)))) x,
  by simp,
  rw h21,
  rw [← polynomial.eval_add],
  rw [polynomial.C_add, polynomial.eval_add, polynomial.eval_mul],
  rw [polynomial.eval_add],
  rw polynomial.eval_C,
  rw polynomial.eval_mul,
  rw polynomial.eval_C,
  rw polynomial.eval_X,
  rw [→ mul_comm, mul_comm (d + 2), ← mul_add],
  rw add_comm,
  rw mul_assoc,
  rw [← polynomial.eval_add],
  have h22 : polynomial.eval (of_nat (d + 2) * ((1 - x) * (X ^ (d + 1) + X ^ d * X + ... + X ^ 0))) (1 + x) + polynomial.eval (of_nat (d + 2) * ((1 - x) * (X ^ (d + 1) + X ^ d * X + ... + X ^ 0))) x + polynomial.eval (of_nat (d + 2) * (1 - x) * (X ^ (d + 1))) x =
    polynomial.eval ((of_nat (d + 2) * (1 - x) * (X ^ (d + 1)))) (1 + x) + polynomial.eval ((of_nat (d + 2) * (1 - x) * (X ^ (d + 1) + X ^ d * X + ... + X ^ 0))) (1 + x) + polynomial.eval ((of_nat (d + 2) * (1 - x) * (X ^ (d + 1) + X ^ d * X + ... + X ^ 0))) x + polynomial.eval (of_nat (d + 2) * (1 - x) * (X ^ (d + 1))) x,
  by simp,
  rw h22,
  rw [← polynomial.eval_add],
  have h23 :
    polynomial.eval ((of_nat (d + 2) * (1 - x) * (X ^ (d + 1)))) (1 + x) =
    polynomial.eval ((of_nat (d + 2) * (1 - x) * (X ^ (d + 1)))) x +
    polynomial.eval (of_nat (d + 2) * (1 - x) * X ^ (d + 1)) x,
  by rw [polynomial.eval_mul, po
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
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by auto [set.subset_of_mem_powerset, set.subset_of_mem_powerset],
  have h2 : (A ∩ B) ⊆ A, from by auto [set.inter_subset_left],
  have h3 : (A ∩ B) ⊆ S, from by auto [set.subset.trans],
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
  calc (x + y)^2 = (x+y)*(x+y) : by auto [sq]
  ... = x*(x+y) + y*(x+y) : by auto [add_mul]
  ... = x*x + x*y + y*x + y*y : by auto [mul_comm, add_mul] using [ring]
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
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by auto using [use (a⁻¹ * b)],
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by auto using [use b * a⁻¹], 

  have h3 : ∀ a : G, ∃! x : G, a * x = a, from by auto [h1],
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from by auto [h2],

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
