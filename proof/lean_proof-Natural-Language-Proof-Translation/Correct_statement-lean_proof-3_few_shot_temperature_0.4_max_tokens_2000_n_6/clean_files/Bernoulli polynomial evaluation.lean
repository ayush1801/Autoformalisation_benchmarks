import number_theory.bernoulli


--OUTPUT 1
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : ∀ m : ℕ, m < n → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1),
    from by {
      assume m : ℕ,
      assume hm : m < n,
      induction m with d hd,
      {show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from by ring},
      {have h1 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from by {
        have h2 : (d + 1) * (polynomial.bernoulli (d + 1)).eval (1 + x) - (d + 1) * (polynomial.bernoulli (d + 1)).eval x = 
          ∑ (k : ℕ) in finset.range (d + 1), (d + 1) * C (d + 1) k * (polynomial.bernoulli k).eval x * x^(k - 1),
          from by {
            rw ← polynomial.eval_add,
            rw ← polynomial.eval_mul,
            rw ← polynomial.eval_mul,
            rw ← polynomial.eval_mul,
            rw ← polynomial.eval_add,
            rw ← polynomial.eval_mul,
            rw ← polynomial.eval_mul,
            rw ← polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_add,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul,
            rw polynomial.eval_pow,
            rw polynomial.eval_one,
            rw polynomial.eval_mul,
            rw polynomial.eval_mul
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  {
    rw polynomial.bernoulli_zero,
    rw polynomial.eval_C,
    ring,
  },
  {
    rw polynomial.bernoulli_succ,
    rw polynomial.eval_add,
    rw polynomial.eval_mul,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_add,
    rw polynomial.eval_mul,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_sub,
    rw polynomial.eval_C,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_C,
    rw polynomial.eval_C,
    rw polynomial.eval_C,
    rw polynomial.eval_X,
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

end --Needs more than 2000 tokens!

--OUTPUT 3
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : ∀ m : ℕ, m < n → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
    assume (m : ℕ) (h : m < n),
    begin
      induction m with m hm,
      show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from
        by {rw [polynomial.bernoulli_zero,polynomial.bernoulli_zero,zero_pow],ring,},
      assume h1 : ∀ m : ℕ, m < m → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1),
      show (polynomial.bernoulli (m + 1)).eval (1 + x) = (polynomial.bernoulli (m + 1)).eval x + (m + 1) * x^((m + 1) - 1), from
        begin
          have h2 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1), from
            assume l : ℕ,
            begin
              induction l with l hl,
              show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from
                by {rw [polynomial.bernoulli_zero,polynomial.bernoulli_zero,zero_pow],ring,},
              assume h2 : (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1),
              show (polynomial.bernoulli (l + 1)).eval (1 + x) = (polynomial.bernoulli (l + 1)).eval x + (l + 1) * x^((l + 1) - 1), from
                by {rw [polynomial.bernoulli_succ,polynomial.bernoulli_succ],rw [h2,h2],ring,},
            end,
          have h3 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1), from
            assume l : ℕ,
            begin
              induction l with l hl,
              show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from
                by {rw [polynomial.bernoulli_zero,polynomial.bernoulli_zero,zero_pow],ring,},
              assume h3 : (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1),
              show (polynomial.bernoulli (l + 1)).eval (1 + x) = (polynomial.bernoulli (l + 1)).eval x + (l + 1) * x^((l + 1) - 1), from
                by {rw [polynomial.bernoulli_succ,polynomial.bernoulli_succ],rw [h3,h3],ring,},
            end,
          have h4 : (polynomial.bernoulli (m + 1)).eval (1 + x) = (polynomial.bernoulli (m + 1)).eval x + (m + 1) * x^((m + 1) - 1), from
            begin
              rw [polynomial.bernoulli_succ,polynomial.bernoulli_succ],
              have h5 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1), from
                assume l : ℕ,
                begin
                  induction l with l hl,
                  show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from
                    by {rw [polynomial.bernoulli_zero,polynomial.bernoulli_zero,zero_pow],ring,},
                  assume h5 : (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1),
                  show (polynomial.bernoulli (l + 1)).eval (1 + x) = (polynomial.bernoulli (l + 1)).eval x + (l + 1) * x^((l + 1) - 1), from
                    by {rw [polynomial.bernoulli_succ,polynomial.bernoulli_succ],rw [h5,h5],ring,},
                end,
              have h6 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1), from
                assume l : ℕ,
                begin
                  induction l with l hl,
                  show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from
                    by {rw [polynomial.bernoulli_zero,polynomial.bernoulli_zero,zero_pow],ring,},
                  assume h6 : (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1),
                  show (polynomial.bernoulli (l + 1)).eval (1 + x) = (polynomial.bernoulli (l + 1)).eval x + (l + 1) * x^((l + 1) - 1), from
                    by {rw [polynomial.bernoulli_succ,polynomial.bernoulli_succ],rw [h6,h6],ring,},
                end,
              have h7 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1), from
                assume l : ℕ,
                begin
                  induction l with l hl,
                  show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from
                    by {rw [polynomial.bernoulli_zero,polynomial.bernoulli_zero,zero_pow],ring,},
                  assume h7 : (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1),
                  show (polynomial.bernoulli (l + 1)).eval (1 + x) = (polynomial.bernoulli (l + 1)).eval x + (l + 1) * x^((l + 1) - 1), from
                    by {rw [polynomial.bernoulli_succ,polynomial.bernoulli_succ],rw [h7,h7],ring,},
                end,
              have h8 : ∀ l : ℕ, (polynomial.bernoulli l).eval (1 + x) = (polynomial.bernoulli l).eval x + l * x^(l - 1), from
                assume l : ℕ,
                begin
                  induction l with l hl,
                  show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from
                    by {rw [polynomial.bernoulli_zero,polynomial.bernoulli_zero,zero_pow],
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : ∀ m : ℕ, (m < n) → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from assume (m : ℕ) (h : m < n),
    begin
      induction m with d hd,
      {
        show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from by {
          rw [← polynomial.bernoulli_zero, ← polynomial.bernoulli_zero],
          ring,
        },
      },
      {
        have h1 : ∀ m : ℕ, (m < d) → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from assume (m : ℕ) (h : m < d), hd h,
        have h2 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from by {
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          have h3 : (d + 1) * (1 + x)^d - (d + 1) * x^d = (d + 1) * (1 + x)^d - (d + 1) * x^d, from by {
            rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
            rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
            ring,
          },
          rw [h3],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial.bernoulli_succ, ← polynomial.bernoulli_succ],
          rw [← polynomial
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  {
    show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from
    begin
      rw polynomial.bernoulli,
      rw polynomial.eval_C,
      rw polynomial.eval_C,
      ring,
    end,
  },
  {
    have h1 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h2 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h3 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,

    have h4 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h5 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h6 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h7 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h8 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h9 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h10 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h11 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h12 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h13 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h14 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h15 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h16 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h17 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h18 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h19 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h : m < d), hd m h,
    have h20 : ∀ (m : ℕ) (x : ℚ), m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from
      assume (m : ℕ) (x : ℚ) (h
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n,
  assume (d : ℕ) (h : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1)),
  have h1 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1),
  begin
    have h2 : (d + 1) * (1 + x)^d = (d + 1) * x^d + (d + 1) * (d - 1) * x^(d - 1),
    begin
      rw [pow_add,pow_one,mul_add,mul_one,← mul_assoc,← mul_assoc,← mul_assoc],
      rw [← pow_two,← pow_one,← pow_add,← pow_one,← pow_add,← pow_one],
      ring,
    end,
    have h3 : (polynomial.bernoulli d).eval (1 + x) = (d + 1) * (1 + x)^d - (d + 1) * x^d,
    begin
      rw [← polynomial.eval_C_mul,← polynomial.eval_C_mul,← polynomial.eval_C_add,polynomial.eval_C_mul,polynomial.eval_C_pow,polynomial.eval_C_mul,polynomial.eval_C_pow,polynomial.eval_C_add],
      ring,
    end,
    have h4 : (polynomial.bernoulli d).eval (1 + x) = (d + 1) * x^d + (d + 1) * (d - 1) * x^(d - 1), from by rw [h3,h2],
    have h5 : (polynomial.bernoulli d).eval (1 + x) = (d + 1) * x^d + (d + 1) * (d - 1) * x^(d - 1) + d * x^(d - 1), from by ring,
    have h6 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from by rw [h4,h5],
    show (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from h6,
  end,
  show (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1), from h1,
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
