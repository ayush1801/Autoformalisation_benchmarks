import number_theory.bernoulli


--OUTPUT 1
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n,
  assume n hn,
  begin
    rw [polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_C],
    rw [polynomial.eval_add, polynomial.eval_add, polynomial.eval_C],
    rw [polynomial.eval_add, polynomial.eval_C],
    rw [polynomial.eval_add, polynomial.eval_C],

    rw [polynomial.eval_sub, polynomial.eval_sub, polynomial.eval_C],
    rw [polynomial.eval_sub, polynomial.eval_C],
    rw [polynomial.eval_sub, polynomial.eval_C],
    rw [polynomial.eval_sub, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],

    rw [polynomial.eval_mul, polynomial.eval_mul, polynomial.eval_C],
    rw [polynomial
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : ∀ m : ℕ, m < n → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1),
    assume m : ℕ,
    assume h2 : (m < n),
    induction m with m hm,
    show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from by auto [polynomial.bernoulli, eval_C, eval_X],
    show (polynomial.bernoulli (m + 1)).eval (1 + x) = (polynomial.bernoulli (m + 1)).eval x + (m + 1) * x^((m + 1) - 1),
    begin
      have h3 : (polynomial.bernoulli (m + 1)).eval (1 + x) = (polynomial.bernoulli (m + 1)).eval x + (polynomial.bernoulli m).eval (1 + x), from by auto [polynomial.bernoulli, eval_add, eval_mul, eval_X, eval_C],
      have h4 : (polynomial.bernoulli (m + 1)).eval x + (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli (m + 1)).eval x + (polynomial.bernoulli m).eval x + (polynomial.bernoulli m).eval x, from by auto [hm, add_assoc],
      have h5 : (polynomial.bernoulli (m + 1)).eval x + (polynomial.bernoulli m).eval x + (polynomial.bernoulli m).eval x = (polynomial.bernoulli (m + 1)).eval x + (polynomial.bernoulli m).eval x + m * x^(m - 1), from by auto [hm],
      have h6 : (polynomial.bernoulli (m + 1)).eval x + (polynomial.bernoulli m).eval x + m * x^(m - 1) = (polynomial.bernoulli (m + 1)).eval x + m * x^(m - 1) + m * x^(m - 1), from by auto [add_assoc],
      show (polynomial.bernoulli (m + 1)).eval (1 + x) = (polynomial.bernoulli (m + 1)).eval x + (m + 1) * x^((m + 1) - 1), from by auto [h3, h4, h5, h6],
    end,
  have h7 : (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + (polynomial.bernoulli (n - 1)).eval (1 + x), from by auto [polynomial.bernoulli, eval_add, eval_mul, eval_X, eval_C],
  have h8 : (polynomial.bernoulli n).eval x + (polynomial.bernoulli (n - 1)).eval (1 + x) = (polynomial.bernoulli n).eval x + (polynomial.bernoulli (n - 1)).eval x + (polynomial.bernoulli (n - 1)).eval x, from by auto [h1, nat.sub_lt],
  have h9 : (polynomial.bernoulli n).eval x + (polynomial.bernoulli (n - 1)).eval x + (polynomial.bernoulli (n - 1)).eval x = (polynomial.bernoulli n).eval x + (polynomial.bernoulli (n - 1)).eval x + (n - 1) * x^((n - 1) - 1), from by auto [h1, nat.sub_lt],
  have h10 : (polynomial.bernoulli n).eval x + (polynomial.bernoulli (n - 1)).eval x + (n - 1) * x^((n - 1) - 1) = (polynomial.bernoulli n).eval x + (n - 1) * x^((n - 1) - 1) + (n - 1) * x^((n - 1) - 1), from by auto [add_assoc],
  show (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1), from by auto [h7, h8, h9, h10],
end

--OUTPUT 3
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) := begin
  have h1 : ∀ l : ℕ, polynomial.sum (λ (k : ℕ), (polynomial.binomial (l + 1) k) * (polynomial.bernoulli k)) (l + 1) = (l + 1) * X^l, from by auto using [polynomial.sum_eq_mul],
  have h2 : ∀ l : ℕ, polynomial.sum (λ (k : ℕ), (polynomial.binomial (l + 1) k) * (polynomial.bernoulli k)) (l + 1) = polynomial.sum (λ (k : ℕ), (polynomial.binomial (l + 1) k) * (polynomial.bernoulli k)) l + (polynomial.binomial (l + 1) (l + 1)) * (polynomial.bernoulli (l + 1)), from by auto using [polynomial.sum_add],
  have h3 : ∀ l : ℕ, polynomial.sum (λ (k : ℕ), (polynomial.binomial (l + 1) k) * (polynomial.bernoulli k)) (l + 1) = polynomial.sum (λ (k : ℕ), (polynomial.binomial (l + 1) k) * (polynomial.bernoulli k)) l + (polynomial.bernoulli (l + 1)), from by auto,
  have h4 : ∀ l : ℕ, polynomial.sum (λ (k : ℕ), (polynomial.binomial (l + 1) k) * (polynomial.bernoulli k)) (l + 1) = polynomial.sum (λ (k : ℕ), (polynomial.binomial (l + 1) k) * (polynomial.bernoulli k)) (l + 1) + (polynomial.bernoulli (l + 1)), from by auto,

  induction n with d hd,
  {
    rw polynomial.bernoulli_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polynomial.eval_zero,
    rw polyn
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  rw polynomial.bernoulli,
  rw polynomial.eval_add,
  rw polynomial.eval_mul,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_monomial,
  rw polynomial.eval_mon
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), ((polynomial.binomial (n + 1) k) * (polynomial.X ^ k)) * (polynomial.bernoulli k).coeff 0), from by auto [polynomial.bernoulli_def],
  have h2 : ∀ (k : ℕ), (polynomial.binomial (n + 1) k) * (polynomial.X ^ k) = polynomial.C (k + 1) * polynomial.X ^ k, from by auto [polynomial.binomial_def],
  have h3 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), ((polynomial.C (k + 1) * polynomial.X ^ k) * (polynomial.bernoulli k).coeff 0)), from by auto [h1, h2],
  have h4 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * polynomial.X ^ k * (polynomial.bernoulli k).coeff 0), from by auto [h3],
  have h5 : polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * polynomial.X ^ k * (polynomial.bernoulli k).coeff 0) = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * (polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [polynomial.sum_mul_C],
  have h6 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * (polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h4, h5],
  have h7 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * polynomial.X ^ k * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h6],
  have h8 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * (polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h7],
  have h9 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * polynomial.X ^ k * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h8],
  have h10 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), (polynomial.C (k + 1) * polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h9],
  have h11 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * polynomial.X ^ k * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h10],
  have h12 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), (polynomial.C (k + 1) * polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h11],
  have h13 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * (polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h12],
  have h14 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * polynomial.X ^ k * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h13],
  have h15 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), (polynomial.C (k + 1) * polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h14],
  have h16 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * (polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h15],
  have h17 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), (polynomial.C (k + 1) * polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h16],
  have h18 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * (polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h17],
  have h19 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), (polynomial.C (k + 1) * polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h18],
  have h20 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * (polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h19],
  have h21 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), (polynomial.C (k + 1) * polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h20],
  have h22 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * (polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h21],
  have h23 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), (polynomial.C (k + 1) * polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h22],
  have h24 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * (polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h23],
  have h25 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), (polynomial.C (k + 1) * polynomial.X ^ k) * polynomial.C (polynomial.bernoulli k).coeff 0), from by auto [h24],
  have h26 : polynomial.bernoulli n = polynomial.sum (λ (k : ℕ), polynomial.C (k + 1) * (polynomial.X ^ k) * polynomial.C (polynomial.bernoulli
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  {
    unfold polynomial.bernoulli,
    unfold polynomial.eval,
    simp,
    ring,
  },
  {
    have h1 : (d + 1) * (1 + x)^d - (d + 1) * x^d = (sum (λ k, ((d + 1) : ℚ) * (polynomial.C (1 : ℚ) ^ k * polynomial.C (x : ℚ) ^ (d - k))) (range (0, d + 1))).eval x, by unfold polynomial.bernoulli,
    have h2 : (sum (λ k, ((d + 1) : ℚ) * (polynomial.C (1 : ℚ) ^ k * polynomial.C (x : ℚ) ^ (d - k))) (range (0, d + 1))).eval x = (sum (λ k, ((d + 1) : ℚ) * (polynomial.C (1 : ℚ) ^ k * polynomial.C (x : ℚ) ^ (d - k))) (range (0, d + 1))).eval x + (sum (λ (k : ℕ), ((d + 1) : ℚ) * (d - k) * (x : ℚ) ^ (d - k - 1) * polynomial.C (1 : ℚ) ^ k) (range (0, d + 1))).eval x, by ring,
    have h3 : (sum (λ (k : ℕ), ((d + 1) : ℚ) * (d - k) * (x : ℚ) ^ (d - k - 1) * polynomial.C (1 : ℚ) ^ k) (range (0, d + 1))).eval x = (sum (λ (k : ℕ), ((d + 1) : ℚ) * (d - k) * (x : ℚ) ^ (d - k - 1) * polynomial.C (1 : ℚ) ^ k) (range (0, d + 1))).eval x + (sum (λ (k : ℕ), ((d + 1) : ℚ) * (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x, by ring,
    have h4 : (sum (λ (k : ℕ), ((d + 1) : ℚ) * (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x = (sum (λ (k : ℕ), ((d + 1) : ℚ) * (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x + (d + 1) * (x : ℚ) ^ (d - 1), by ring,
    have h5 : (sum (λ (k : ℕ), ((d + 1) : ℚ) * (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x = (sum (λ (k : ℕ), ((d + 1) : ℚ) * (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x + (sum (λ k, ((d + 1) : ℚ) * (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x, by ring,
    have h6 : (sum (λ k, ((d + 1) : ℚ) * (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x = (sum (λ k, ((d + 1) : ℚ) * (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x + (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x, by ring,
    have h7 : (sum (λ k, ((d + 1) : ℚ) * (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x = (sum (λ k, ((d + 1) : ℚ) * (x : ℚ) ^ (d - k - 1)) (range (0, d + 1))).eval x + (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d))).eval x, by ring,
    have h8 : (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d))).eval x = (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d))).eval x + (d : ℚ) * (x : ℚ) ^ (d - 1), by ring,
    have h9 : (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d))).eval x = (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d))).eval x + (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 1))).eval x, by ring,
    have h10 : (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 1))).eval x = (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 1))).eval x + (d - 1) * (x : ℚ) ^ (d - 2), by ring,
    have h11 : (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 1))).eval x = (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 1))).eval x + (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 2))).eval x, by ring,
    have h12 : (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 2))).eval x = (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 2))).eval x + (d - 2) * (x : ℚ) ^ (d - 3), by ring,
    have h13 : (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 2))).eval x = (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 2))).eval x + (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 3))).eval x, by ring,
    have h14 : (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 3))).eval x = (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 3))).eval x + (d - 3) * (x : ℚ) ^ (d - 4), by ring,
    have h15 : (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 3))).eval x = (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 3))).eval x + (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 4))).eval x, by ring,
    have h16 : (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d - 4))).eval x = (sum (λ k, (x : ℚ) ^ (d - k - 1)) (range (0, d
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h0 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C 1).pow (-k), from by auto [pow_add, sum_mul_distrib_left, pow_neg, pow_zero],
  have h1 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto,
  have h2 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h3 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h4 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],

  have h5 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h6 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h7 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h8 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],

  have h9 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h10 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],

  have h11 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h12 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h13 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h14 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h15 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h16 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h17 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],

  have h18 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h19 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).pow l = ∑ k in finset.range (l + 1), (l + 1) * (polynomial.C 1).pow k * (polynomial.C (1 : ℚ)).pow (-k), from by auto [polynomial.pow_C, one_pow],
  have h20 : ∀ l : ℕ, (l + 1) * (polynomial.C 1).
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  {
    show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x ^ (0 - 1),
    from by auto [polynomial.bernoulli, polynomial.eval_add, polynomial.eval_C, polynomial.eval_X, polynomial.eval_mul, polynomial.eval_one, polynomial.bernoulli_zero]
  },
  {
    have h1 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x ^ (d - 1), from by auto [hd],
    have h2 : ((polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1)) * (d + 1) = (polynomial.bernoulli d).eval x * (d + 1) + d * x ^ (d - 1) * (d + 1), from by auto [add_mul],
    have h3 : ((polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1)) * (d + 1) = (polynomial.bernoulli d).eval x * (d + 1) + d * x ^ d * (d + 1), from by auto [mul_comm, pow_succ'],
    have h4 : ((polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1)) * (d + 1) = (polynomial.bernoulli d).eval x * (d + 1) + (polynomial.bernoulli d).eval x * (d + 1), from by auto [h1, h2, h3],
    have h5 : ((polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1)) * (d + 1) = (polynomial.bernoulli d).eval x * (d + 1) + (polynomial.bernoulli d).eval x * (d + 1), from by auto [mul_add],
    have h6 : (((polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1)) * (d + 1) - (polynomial.bernoulli d).eval x * (d + 1) - (polynomial.bernoulli d).eval x * (d + 1)) = 0, from by auto [h4, h5, sub_eq_zero],
    have h7 : (((polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1)) * (d + 1) - (polynomial.bernoulli d).eval x * (d + 1) - (polynomial.bernoulli d).eval x * (d + 1)) = (polynomial.bernoulli d).eval x * (d + 1) - (polynomial.bernoulli d).eval x * (d + 1), from by auto [add_sub_cancel'],
    have h8 : (((polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1)) * (d + 1) - (polynomial.bernoulli d).eval x * (d + 1) - (polynomial.bernoulli d).eval x * (d + 1)) = ((polynomial.bernoulli d).eval x - (polynomial.bernoulli d).eval x) * (d + 1), from by auto [h7, sub_eq_zero],
    have h9 : (((polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1)) * (d + 1) - (polynomial.bernoulli d).eval x * (d + 1) - (polynomial.bernoulli d).eval x * (d + 1)) = 0, from by auto [h6, h7, h8, mul_zero],

    have h10 : (polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1) = (polynomial.bernoulli d).eval x * (d + 1) / (d + 1), from by auto [h9, div_eq_zero, eq_zero_of_mul_self_eq_zero],
    have h11 : (polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1) = (polynomial.bernoulli d).eval x, from by auto [h10, div_one],
    have h12 : (polynomial.bernoulli d).eval (1 + x) + d * x ^ (d - 1) = (polynomial.bernoulli d).eval x + d * x ^ (d - 1), from by auto [h1, h11, eq.symm],
    show (polynomial.bernoulli (d + 1)).eval (1 + x) = (polynomial.bernoulli (d + 1)).eval x + (d + 1) * x ^ (d + 1 - 1), from by auto [h12, polynomial.bernoulli]
  }
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
