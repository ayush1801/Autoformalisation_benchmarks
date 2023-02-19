import number_theory.bernoulli


--OUTPUT 1
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d generalizing x,
  { show (polynomial.bernoulli 0).eval (1 + x) = 
    (polynomial.bernoulli 0).eval x + 0 * x^(0 - 1), from rfl, },
  have h1 : (d + 1) * (1 + x)^d - (d + 1) * x^d = 
    (d + 1) * (1 + x)^d - d * x^d - x^d, from by rw ← nat.succ_eq_add_one d,
  have h2 : (d + 1) * (1 + x)^d - d * x^d - x^d =
    (d + 1) * (1 + x)^d - d * (x * (1 + x)^(d - 1)) - x^d, from by {rw ← pow_succ},
  have h3 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * (1 + x)^(d - 1) * ((1 + x) - x), from calc
    (d + 1) * (1 + x)^(d - 1) * ((1 + x)^1 - x^1) : by {rw [pow_one,pow_one]}
  ... = _ : by rw pow_add,
  have h4 : (d + 1) * ((1 + x)^d - x^d) =
    (d + 1) * (1 + x + x^2 + ... + x^(d - 1)) * ((1 + x) - x), from by rw pow_one,
  have h5 : (d + 1) * (1 + x)^(d - 1) * ((1 + x) - x) = 
    (d + 1) * (x + x^2 + ... + x^(d - 1)) + 
    d * x^d + (d + 1) * x^d - d * x^d - x^d, from by rw h4,
  have h6 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * (x + x^2 + ... + x^(d - 1)) + 
    d * x^d + (d + 1) * x^d - d * x^d - x^d, from by rw h5,
  have h7 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + (d + 1) * (x^2 + ... + x^(d - 1)) + 
    d * x^d + (d + 1) * x^d - d * x^d - x^d, from by rw pow_one,
  have h8 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + d * x^(d - 1) * x +
    d * x^d + (d + 1) * x^d - d * x^d - x^d, from by rw ← mul_add,
  have h9 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + d * x^(d - 1) * x +
    d * x^d + (d + 1) * x^d - d * x^d - x^d, from by rw h8,
  have h10 : d * x^(d - 1) * x = x * d * x^(d - 1), from by rw mul_comm,
  have h11 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    d * x^d + (d + 1) * x^d - d * x^d - x^d, from by rw h10,
  have h12 : (d + 1) * ((1 + x)^d - x^d) = 
    d * x^(d - 1) * (x + 1) + d * x^d + (d + 1) * x^d - d * x^d - x^d, from by rw h11,
  have h13 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + d * x^(d - 1) * x +
    d * x^d + (d + 1) * x^d - d * x^d - x^d, from by rw h10,
  have h14 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    d * x^d + (d + 1) * x^d - d * x^d - x^d, from by rw h13,
  have h15 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    (d + 1) * x^d - d * x^d - x^d, from by rw ← add_sub,
  have h16 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    (d + 1) * x^d - d * x^d - x^d, from by rw h15,
  have h17 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    (d + 1) * x^d - d * x^d - x^d, from by rw h16,
  have h18 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    x^d * (d + 1) - x^d * d - x^d, from by rw ← sub_add,
  have h19 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    x^d * (d + 1) - x^d * d - x^d, from by rw h18,
  have h20 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    x^d * (d + 1) - x^d * d - x^d, from by rw h19,
  have h21 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    d * x^d - x^d, from by rw ← sub_sub,
  have h22 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    d * x^d - x^d, from by rw h21,
  have h23 : (d + 1) * ((1 + x)^d - x^d) = 
    (d + 1) * x^(d - 1) + x * d * x^(d - 1) +
    d * x^d - x^d, from by rw h22,
  have h24 : (d + 1) * ((1 + x)^d - x^d) = 
    d *
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin 
  have h1 : ∀ (n k : ℕ), (polynomial.bernoulli n).eval x = n * x^(k - 1) →
    (polynomial.bernoulli (n + 1)).eval (1 + x) = (polynomial.bernoulli (n + 1)).eval x + (n + 1) * x^k, from 
  begin
    assume (n k : ℕ) (h : (polynomial.bernoulli n).eval x = n * x^(k - 1)),
    have h2 : (polynomial.bernoulli (n + 1)).eval (1 + x) = (polynomial.bernoulli (n + 1)).eval x + (n + 1) * x^k, from 
    begin
      have h1 : (n + 1) * (polynomial.bernoulli (n + 1)).eval (1 + x) = (n + 1) * (polynomial.bernoulli (n + 1)).eval x + (n + 1) * (k + 1) * x^k, from 
      begin
        have h_one : (polynomial.bernoulli (n + 1)).eval 1 = 1, from begin
          induction (n + 1) with e h_e,
          {rw polynomial.eval_C, refl,},
          {calc (polynomial.bernoulli (e + 1)).eval 1 = (polynomial.bernoulli e).eval (e + 1) + (e + 1) * (polynomial.bernoulli e).eval 0: begin
            rw polynomial.eval_add,
            rw polynomial.eval_mul,
            rw polynomial.eval_X,
            rw polynomial.eval_C,
            rw nat.sub_zero,
            rw polynomial.eval_nat_cast,
            rw polynomial.eval_C,
            rw polynomial.eval_X_nat,
            rw polynomial.eval_zero,
            rw polynomial.eval_one,
            ring,
          end
          ... = (polynomial.bernoulli e).eval (e + 1) + (e + 1) * 0 : begin
            rw polynomial.eval_zero,
            ring,
          end
          ... = (polynomial.bernoulli e).eval (e + 1) : by dcancel_factor (e + 1),
          },
        end,
        rw h_one,
        rw polynomial.eval_X,
        rw polynomial.eval_C,
        rw polynomial.eval_add,
        rw polynomial.eval_mul,
        rw polynomial.eval_X,
        rw polynomial.eval_C,
        rw nat.sub_zero,
        rw polynomial.eval_nat_cast,
        apply calc_line_5,
        calc (polynomial.bernoulli (n + 1)).eval x = (n + 1) * x^k : by rw [h,mul_comm],
        calc (polynomial.bernoulli (n + 1)).eval (1 + x) = (n + 1) * (1 + x)^k : by rw [h,mul_comm],
        calc (polynomial.bernoulli (n + 1)).eval (1 + x) = (n + 1) * (1 + k * x^k): begin
          rw polynomial.eval_X_nat,
          ring,
        end
        ... = (n + 1) * ((k + 1) * x^k) + (n + 1) * k * x^k : by ring,
        calc (polynomial.bernoulli (n + 1)).eval (1 + x) = (n + 1) * ((k + 1) * x^k) : by rw [h,mul_comm],
      end,
      calc (polynomial.bernoulli (n + 1)).eval (1 + x) = (1 / (n + 1)) * ((n + 1) * (polynomial.bernoulli (n + 1)).eval (1 + x)) : by rw [mul_comm,div_mul_cancel (ne.symm (nat.succ_ne_zero (n + 1)))]
      ... = (1 / (n + 1)) * ((n + 1) * (polynomial.bernoulli (n + 1)).eval x + (n + 1) * (k + 1) * x^k) : by rw h1
      ... = (1 / (n + 1)) * ((n + 1) * (polynomial.bernoulli (n + 1)).eval x) + (1 / (n + 1)) * ((n + 1) * (k + 1) * x^k) : by ring
      ... = (1 / (n + 1)) * ((n + 1) * (polynomial.bernoulli (n + 1)).eval x) + (k + 1) * x^k : by rw [mul_comm,div_mul_cancel (ne.symm (nat.succ_ne_zero (n + 1)))]
      ... = (polynomial.bernoulli (n + 1)).eval x + (k + 1) * x^k : by rw [mul_comm,div_mul_cancel (ne.symm (nat.succ_ne_zero (n + 1)))]
    end
    ,
    have h3 : (polynomial.bernoulli (n + 1)).eval x = (n + 1) * x^k, from begin
      have h_two : ∀ x : ℚ, (polynomial.bernoulli (n + 1)).eval (1 + x) = (n + 1) * x^k, from begin
        assume x : ℚ,
        rw ← h2,
        rw ← h,
        ring,
      end,
      have h_three : ∀ x : ℚ, (polynomial.bernoulli (n + 1)).eval x = (n + 1) * x^k, from begin
        assume x : ℚ,
        have h_four : (1 : ℚ) + (1 : ℚ) = 2, from by ring,
        rw h_four,
        rw [h_two ((1 : ℚ) + x),add_comm],
        rw ← mul_comm,
        rw ← mul_comm,
        ring,
      end,
      rw h_three x,
    end,
    calc (polynomial.bernoulli (n + 1)).eval x = (n + 1) * x^k : by rw h3
    ... = (n + 1) * x^(k - 1) : by ring,
  end,
  have h2 : ∀ (n k : ℕ), (polynomial.bernoulli (n + 1)).eval (1 + x) = (n + 1) * x^k → (n + 1) * x^(k - 1) = (polynomial.bernoulli (n + 1)).eval x + (n + 1) * x^(k - 1), from 
  begin
    assume n k (h : (polynomial.bernoulli (n + 1)).eval (1 + x) = (n + 1) * x^k),
    have h2 : (n + 1) * x^(k - 1) = (polynomial.bernoulli (n + 1)).eval x + (n + 1) * x^(k - 1), from 
    begin
      have h3 : (polynomial.bernoulli (n + 1)).eval (1 + x) = (polynomial.bernoulli (n + 1)).eval x + (n + 1) * x^k, from by rw h,
      have h4 : (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(k - 1), from begin
        have h5 : (polynomial.bernoulli n).eval x = n * x^(k - 1), from begin
          rw ← h,
          rw ← mul_comm,
          ring,
        end,
        rw h1 n (k -
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d hd,
  { show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x + 0 * x^(-1), from by
    {rw zero_sub, rw [pow_neg one_ne_zero, mul_zero], ring,},
  },
  { rw polynomial.bernoulli, rw eval_add, rw eval_mul,
    have hthm : d + 1 = (d : ℤ) + (1:ℤ), from by {ring},
    have hthm2 : polynomial.C (1 : ℤ) = 1, from by {refl},
    rw [hthm,hthm2,eval_pow],
    have hthm3 : (d : ℤ) + (1:ℤ) = (d + 1 : ℕ), from by {ring},
    rw [mul_add, mul_one, ← hthm3],
    rw ← polynomial.eval_apply_eq, rw ← polynomial.eval_apply_eq, rw ← polynomial.eval_apply_eq,
    rw ← map_pow,
    have hthm4 : (d : ℤ) = (d : ℕ), from by {refl},
    rw hthm4,
    have hthm5 : (1:ℤ) = (1 : ℕ), from by {refl},
    rw hthm5,
    rw eval_apply, ring,
    rw sub_zero, ring,
    rw hd,
    rw eval_apply, ring,
    rw sub_zero, ring,
    rw pow_one, ring,
    rw sub_zero, ring,
  },
end

--OUTPUT 4
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n using nat.strong_induction_on,
  case nat.zero {rw polynomial.eval_zero,rw polynomial.eval_zero, ring},
  case nat.succ : n hn {
    have h1 : (n : polynomial ℚ) * C x ^ n = n * C x ^ n, from by {unfold polynomial.C, ring,},
    have h2 : ((n : polynomial ℚ) + 1) * C x^n = (n + 1) * C x^n, from by {unfold polynomial.C, ring,},
    have h3 : (C 1 + C x)^n = C 1 ^ n + n * (C 1)^{n-1} * C x, from by {rw power_succ, unfold polynomial.C, ring,},
    have h4 : (C x)^n = C x ^ n, from by {unfold polynomial.C, ring},
    have h5 : (C x)^n * (n + 1) = (n + 1) * C x ^ n, from by {unfold polynomial.C, ring,},
    rw bernoulli,
    rw [← h1,← h2,← h3,← h4,← h5,← h1],
    rw polynomial.eval_add,
    rw polynomial.eval_pow,
    rw polynomial.eval_pow,
    rw polynomial.eval_C,
    rw polynomial.eval_C,
    rw polynomial.eval_C,
    rw polynomial.eval_pow,
    rw polynomial.eval_pow,
    rw polynomial.eval_C,
    conv {to_lhs, rw polynomial.eval_C},
    rw show n * x ^ n + n * x ^ n = n * (1 + x) ^ n, by ring,
    rw polynomial.eval_add,
    rw polynomial.eval_pow,
    rw polynomial.eval_pow,
    rw polynomial.eval_C,
    rw polynomial.eval_C,
    rw polynomial.eval_C,
    rw polynomial.eval_pow,
    rw polynomial.eval_pow,
    rw polynomial.eval_C,
    rw polynomial.eval_C,
    conv {to_lhs, rw polynomial.eval_C},
    ring,
  },
end

--OUTPUT 5
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with d ih,
  {simp only [polynomial.bernoulli_zero,polynomial.eval_zero], rw one_add, ring},
  {rw polynomial.bernoulli_succ,
  rw polynomial.eval_add,
  rw polynomial.eval_mul,
  rw polynomial.eval_mul,
  rw ← polynomial.eval_X_pow,
  rw ← polynomial.eval_X_pow,
  rw ih,
  rw polynomial.eval_X_pow,
  ring}
end

--OUTPUT 6
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n,
  { assume n,
    assume h1 : ∀ m : ℕ, m < n →
      (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1),
    assume h2 : (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1),
    show (polynomial.bernoulli (n + 1)).eval (1 + x) = (polynomial.bernoulli (n + 1)).eval x + (n + 1) * x ^ ((n + 1) - 1), from 
      by {
      have h3 : (n + 1) * (1 + x) ^ (n + 1) - (n + 1) * x ^ (n + 1) =
        ∑ k in range (n + 1), (n + 1) * (polynomial.bernoulli k).eval x*x^(n - k), from 
          by {
            have h4 : (n + 1) * (1 + x) ^ n * (1 + x) = (n + 1) * x ^ n * (1 + x) + 
              (n + 1) * (1 + x) ^ (n-1) * x, from by {
              rw [add_mul, pow_succ, mul_assoc],
              rw [add_mul, add_mul],
              rw ← add_assoc,
              apply add_comm},
            rw [pow_succ, h2],
            rw [add_mul, h4],
            rw add_assoc,
            ring,
          },
      have h5 : (n + 1) * (1 + x) ^ n * (1 + x) - (n + 1) * x ^ (n + 1) = 
        ∑ k in range n, (n + 1) * (polynomial.bernoulli k).eval x * x ^ (n - k) + n * x ^ n, from 
          by {
            rw [range_succ, h3],
            ring,
            },
      have h6 : (n + 1) * (1 + x) ^ n * (1 + x) - (n + 1) * x ^ (n + 1) =
        ∑ k in range (n + 1), (n + 1) * (polynomial.bernoulli k).eval x * x ^ (n - k), from 
          by {
            rw [range_succ, h5],
            rw [← range_succ],
            ring,
            },
      have h7 : (n + 1) * (1 + x) ^ n * (1 + x) - (n + 1) * x ^ (n + 1) =          
        ∑ k in range (n + 1), (n + 1) * (polynomial.bernoulli k).eval x * x ^ (n + 1 - k), from 
          by {
            congr,
            rw [range_succ],
          },
      have h8 : ∀ k : ℕ, k ≤ n → ∑ (i : ℕ) in range (n + 1), 
        (n + 1) * (polynomial.bernoulli i).eval x * x ^ (n + 1 - i) = 
        (n + 1) * (polynomial.bernoulli k).eval x * x ^ (n + 1 - k), from assume (k : ℕ) (hk : k ≤ n),
        begin
          rw [mem_range, mem_range],
          rw [nat.succ_le_iff', hk],
          rw [polynomial.bernoulli_zero_of_gt, polynomial.bernoulli_zero_of_gt],
          ring,
        end,
      have h9 : ∀ k : ℕ, k ≤ n → (n + 1) * (polynomial.bernoulli k).eval x * x ^ (n + 1 - k) = 
        n * (polynomial.bernoulli k).eval x * x ^ (n - k), from assume (k : ℕ) (hk : k ≤ n),
        begin
          rw [mul_comm, nat.mul_div_cancel_left],
          simp,
        end,
      have h10 : ∀ k : ℕ, k ≤ n → (n + 1) * (polynomial.bernoulli k).eval x * x ^ (n + 1 - k) = 
        n * (polynomial.bernoulli k).eval x * x ^ (n - k) + (polynomial.bernoulli k).eval x * x ^ (n - k), from assume (k : ℕ) (hk : k ≤ n),
        begin
          rw h9 k hk,
          ring,
        end,
      have h11 : ∀ k : ℕ, k ≤ n → (n + 1) * (polynomial.bernoulli k).eval x * x ^ (n + 1 - k) = 
        (n + 1) * (polynomial.bernoulli k).eval x * x ^ (n - k) + (polynomial.bernoulli k).eval x * x ^ (n - k), from assume (k : ℕ) (hk : k ≤ n),
        begin
          rw h8 k hk,
          ring,
        end,
      have h12 : ∀ k : ℕ, k ≤ n → (n + 1) * (polynomial.bernoulli k).eval x * x ^ (n + 1 - k) = 
        (n + 1) * (polynomial.bernoulli k).eval x * x ^ (n + 1 - k) + (polynomial.bernoulli k).eval x * x ^ (n - k), from assume (k : ℕ) (hk : k ≤ n),
        begin
          rw [← nat.sub_sub, nat.sub_sub],
          rw h11 k hk,
          simp,
        end,
      have h13 : (n + 1) * (1 + x) ^ n * (1 + x) - (n + 1) * x ^ (n + 1) = (n + 1) * (1 + x) ^ n * (1 + x) - 
        (n + 1) * (1 + x) ^ n * x, from by ring,
      have h14 : (n + 1) * (1 + x) ^ n * (1 + x) - (n + 1) * x ^ (n + 1) = (n + 1) * (1 + x) ^ n * (1 + x - x), from 
        by {
          rw h13,
          ring,
          },
      have h15 : (n + 1) * (1 + x) ^ n * (1 + x - x) = (n + 1) * (1 + x) ^ n * 0, from by {simp},
      have h16 : (n + 1) * (1 + x) ^ n * 0 = (n + 1) * (1 + x) ^ (n - 1) * x, from by rw pow_succ,
      have h17 : (n + 1) * (1 + x) ^ (n - 1) * x = (n + 1) * (polynomial.bernoulli n).eval x * x ^ (n - 1), from 
        by {
          rw ← polynomial.eval_hom_C n _,
          rw polynomial.eval_C,
          ring,
          },
      have h18 : (n + 1) * (polynomial.bernoulli n).eval x * x ^ (n - 1) = (polynomial.bernoulli n).eval x * x ^ (n - 1), from 
        by {
          rw mul_one,
          },
      have h19 : (n + 1) * (1 + x) ^ n * (1 + x) - (n + 1) * x ^ (n + 1) = (polynomial.bernoulli n).eval x * x ^ (n - 1), from 
        by {
          rw [h15, h
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  by_cases h : n = 0,
  {
    rw [h, polynomial.bernoulli, eval_C, eval_add],
    {
      rw eval_C,
      simp,
    },
    {
      simp,
    }
  },
  {
    sorry,
  },
end

--OUTPUT 8
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  revert n, apply nat.strong_induction_on,
  assume (d : ℕ) (hyp : ∀ (n : ℕ), n < d → (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1)),
  have h1 : ∀ (l : ℕ), (l + 1) * (1 + x)^l = ∑ k : ℕ, (l + 1) * ((l + 1) choose k) * x^k, from
    assume (l : ℕ), by rw [mul_one,←mul_one,←@binomial_expansion l (1 + x) ((l+1 : ℚ))],
  
  have h2 : ∀ (l : ℕ), (l + 1) * (1 + x)^l - (l + 1) * x^l = ∑ k : ℕ, (l + 1) * ((l + 1) choose k) * (x^k - x^(k-1)), from
    assume (l : ℕ), by {simp,rw ←@mul_sub ℚ l ((l+1:ℚ)) x x, ring,},
  
  have h3 : ∀ (l : ℕ), (l + 1) * (1 + x)^l - (l + 1) * x^l = ∑ k : ℕ, (l + 1) * ((l + 1) choose k) * (k * x^(k - 1)), from
    assume (l : ℕ), by {rw ←@eq_Sum_bij (ℕ) (λ k : ℕ, ↑k * x^(k - 1)) (λ k : ℕ, x^k - x^(k-1)) (λ k, k * (x^k - x^(k-1)))
    _ _ _ _ _, simp, simp,},
  
  have h4 : ∀ (l : ℕ), (l + 1) * (1 + x)^l - (l + 1) * x^l = ∑ k : ℕ, (l + 1) * ((l + 1) choose k) * (k * x^(k - 1)) - 0, from
    assume (l : ℕ), by simp [h3],
  
  have h5 : ∀ (l : ℕ), (l + 1) * (1 + x)^l - (l + 1) * x^l = ∑ k : ℕ, (l + 1) * (bernoulli k) * x^(k - 1), from
    assume (l : ℕ), by {rw ←@eq_Sum_bij (ℕ) (λ k : ℕ, (l + 1) * bernoulli k * x^(k - 1)) (λ k : ℕ, (l + 1) * ((l + 1) choose k) * (k * x^(k - 1)))
    (λ k, (l + 1) * k * (bernoulli k * x^(k-1))) _ _ _ _ _, simp, simp,},
  
  have h6 : (1 : ℚ) = ∑ k : ℕ, bernoulli k * x^(k - 1), from
    by {rw ←@eq_Sum_bij (ℕ) (λ k : ℕ, bernoulli k * x^(k - 1)) (λ k : ℕ, 1 * (k * x^(k - 1)))
    (λ k, 1 * k * (bernoulli k * x^(k-1))) _ _ _ _ _, simp, simp,},
  
  have h7 : (d + 1) * (1 + x)^d - (d + 1) * x^d = ∑ k : ℕ, (d + 1) * bernoulli k * x^(k - 1), from
    by {rw h5 d},
  
  have h8 : (d + 1) * (1 + x)^d - (d + 1) * x^d = ∑ k : ℕ, (d + 1) * d * bernoulli k * x^(k - 1), from
    by {rw ←@eq_Sum_bij (ℕ) (λ k : ℕ, (d + 1) * d * bernoulli k * x^(k - 1)) (λ k : ℕ, (d + 1) * bernoulli k * x^(k - 1))
    (λ k, (d + 1) * (d * bernoulli k * x^(k-1))) _ _ _ _ _, simp, simp,},
  
  have h9 : (d + 1) * x^d = ∑ k : ℕ, (d + 1) * k * bernoulli k * x^(k - 1), from
    by {rw ←@eq_Sum_bij (ℕ) (λ k : ℕ, (d + 1) * k * bernoulli k * x^(k - 1)) (λ k : ℕ, (d + 1) * d * bernoulli k * x^(k - 1))
    (λ k, (d + 1) * (k * bernoulli k * x^(k-1))) _ _ _ _ _, simp, simp,},
  
  have h10 : (d + 1) * x^d = (d + 1) * ∑ k : ℕ, k * bernoulli k * x^(k - 1), from
    by {rw ←@eq_Sum_bij (ℕ) ((λ k : ℕ, (d + 1) * k * bernoulli k * x^(k - 1))) (λ k : ℕ, k * bernoulli k * x^(k - 1))
    (λ k, (d + 1) * (k * bernoulli k * x^(k-1))) _ _ _ _ _, simp, simp,},
  
  have h11 : (d + 1) * (1 + x)^d - (d + 1) * x^d = (d + 1) * ∑ k : ℕ, (d - k) * bernoulli k * x^(k - 1), from
    by {rw h8 at h7, rw h9 at h7, rw h10 at h7, simp [h7],},
  
  have h12 : ∀ (k : ℕ), (d + 1) * (d - k) * bernoulli k * x^(k - 1) = (k + 1) * bernoulli(k + 1) * x^k, from
    by {intro k, calc
        (d + 1) * (d - k) * bernoulli k * x^(k - 1) = (d + 1) * (d - k) * ((bernoulli k) * x^(k - 1)) : by {rw mul_assoc,}
        ... = (d + 1) * ((d - k) * ((bernoulli k) * x^(k - 1))) : by {rw mul_assoc,}
        ... = (d + 1) * ((d - k) * ((bernoulli (k + 1)) * x^k)) : by {rw bernoulli_add_one_mul,}
        ... = (d + 1) * (d - k) * (bernoulli (k + 1)) * x^k : by {rw mul_assoc,}
        ... = (k + 1) * bernoulli(k + 1) * x^k : by {rw dif_pos (nat.succ_pos k),ring,},},
  
  have h13 : ((d + 1) * (1 + x)^d - (d + 1) * x^d) / (k + 1) = bernoulli(k + 1) * x^k, from
    by {rw ←@eq_Sum_bij (ℕ) (λ k : ℕ, ((d + 1) * (1 + x)^d - (d + 1) * x^d) / (k + 1)) (λ k
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : ∀ (x : ℝ), (polynomial.bernoulli n).eval x = 0, from
    assume r : ℝ, by {rw polynomial.bernoulli, rw ← polynomial.eval_sum, show (λ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (r : ℚ) ^ k) = 0,
      from funext (λ k : ℕ,  by {
        have h2 : (r : ℚ) ^ k = 0, from by {rw_mod_cast polynomial.eval_monomial,exact nat.mod_cast _},
        have h3 : polynomial.C (↑(ber n k)) = 0, from by rw polynomial.C_zero,
        rw [h2,h3], }),
      show ∑ k, (λ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (r : ℚ) ^ k) k = 0, from eq.trans (sum_const_zero (λ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (r : ℚ) ^ k))
        (eq.symm (by apply_fun (sum_zero_indexed ℕ) (λ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (r : ℚ) ^ k) ((polynomial.C (↑(ber n k)) : ℚ) * (r : ℚ) ^ k))),
     },
  have h2 : ∀ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (1 + x) ^ k = ((polynomial.C (↑(ber n k)) : ℚ) * (1 : ℚ)) + ((polynomial.C (↑(ber n k)) : ℚ) * x ^ k), from
    assume k : ℕ, by rw_mod_cast polynomial.eval_monomial,
  have h3 : ∀ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) = 0, from
    assume k : ℕ, by {rw polynomial.C_zero},
  have h4 : ∀ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (1 : ℚ) = 0, from
    assume k : ℕ, by {rw [h3 k],},
  have h5 : ∀ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * x ^ k = 0, from
    assume k : ℕ, by {rw [h3 k],},
  have h6 : ∀ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (1 + x) ^ k = 0, from
    assume k : ℕ, by {rw [h4 k,h5 k,zero_add],},
  have h7 : polynomial.bernoulli n = 0, from by {rw [← polynomial.eval_eq_zero h1,← polynomial.eval_sum],
    have h8 : ∑ k, (λ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (1 + x) ^ k) k = 0, from
      eq.trans (sum_const_zero (λ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (1 + x) ^ k)) (eq.symm (by apply_fun (sum_zero_indexed ℕ) (λ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (1 + x) ^ k) ((polynomial.C (↑(ber n k)) : ℚ) * (1 + x) ^ k))),
    show ∑ k, (λ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (1 + x) ^ k) k = 0, from eq.trans h8 (sum_zero_indexed_of_const_zero (λ (k : ℕ), (polynomial.C (↑(ber n k)) : ℚ) * (1 + x) ^ k) h6), },
  have h8 : (polynomial.bernoulli n).eval (1 + x) = 0, from by {rw h7,}, 
  induction n with d hd,
  {have h9 : (polynomial.bernoulli 0).eval (1 + x) = 1, from by {rw polynomial.bernoulli,rw_mod_cast polynomial.eval_monomial,rw polynomial.C_one,ring},
    rw h9, rw polynomial.bernoulli, rw_mod_cast polynomial.eval_monomial, rw polynomial.C_one, rw zero_mul, ring, },
  {have h10 : (polynomial.bernoulli d).eval (1 + x) = 0, from by {rw polynomial.bernoulli,rw_mod_cast polynomial.eval_sum,
    have h11 : ∑ k, (λ (k : ℕ), (polynomial.C (↑(ber d k)) : ℚ) * ((1 + x) : ℚ) ^ k) k = 0, from by {
      have h12 : ∑ k, (λ (k : ℕ), (polynomial.C (↑(ber d k)) : ℚ) * (1 : ℚ)) k = 0, from by {rw [polynomial.C_sum,polynomial.C_sum],rw_mod_cast polynomial.eval_monomial,
      rw_mod_cast polynomial.eval_monomial,rw_mod_cast polynomial.eval_sum,
      have h13 : ∑ k, (λ (k : ℕ), ((↑(ber d k) : ℚ) * (1 : ℚ)) : ℚ) k = (↑(1 : ℤ) : ℚ), from by {
        have h14 : ∑ k, (λ (k : ℕ), (↑(1 : ℤ) : ℚ)) k = (↑(1 : ℤ) : ℚ), from by {rw [sum_const_one ℕ (λ (k : ℕ), (↑(1 : ℤ) : ℚ))],},
        have h15 : ∑ k, (λ (k : ℕ), (↑(ber d k) : ℚ) * (1 : ℚ)) k = (↑(1 : ℤ) : ℚ), from by {rw_mod_cast polynomial.eval_monomial,rw nat.mod_cast,},
        have h16 : (↑(1 : ℤ) : ℚ) = (↑(1 : ℤ) : ℚ) * (1 : ℚ), from by {rw one_mul,},
        show ∑ k, (λ (k : ℕ), (↑(ber d k) : ℚ) * (1 : ℚ)) k = (↑(1 : ℤ) : ℚ), from eq.trans h15 (by rw h16), },
        show (polynomial.C 1 * x ^ d).eval 1 = 0, from by {rw_mod_cast polynomial.eval_monomial,rw_mod_cast polynomial.eval_monomial,
          have h15 : (1 : ℚ) ^ d = 1, from by {rw_mod_cast polynomial.eval_monomial,rw_mod_cast polynomial.eval_monomial},
        show (1 * 1) = 0, from by {rw [h15,one_mul],},},
      have h14 : ((d + 1) : ℚ) = (↑(d + 1) : ℚ), from by {rw_mod_cast
end --Needs more than 2000 tokens!

--OUTPUT 10
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h0 : ∀ d : ℕ, (∀ m : ℕ, m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1)) → (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d-1), from
    nat.strong_induction_on n (
      assume (d : ℕ) (hind : ∀ m : ℕ, m < d → (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1)),
      show (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d-1), from 
        begin
          show ((d + 1) * (1 + x)^d - (d + 1) * x^d) = (sum (λ (l : ℕ), ({d + 1} choose l) * l * x^l)) - {d + 1} * (1 + x)^d, from by ring,
          have h1 : (d + 1) * (1 + x)^d - (d + 1) * x^d = sum (λ (l : ℕ), ({d + 1} choose l) * (polynomial.bernoulli l).eval x), from by ring,
          have h2 : (sum (λ (l : ℕ), ({d + 1} choose l) * l * x^l)) - {d + 1} * (1 + x)^d = sum (λ (l : ℕ), ({d + 1} choose l) * (polynomial.bernoulli l).eval x), from by ring,
          have h3 : sum (λ (l : ℕ), ({d + 1} choose l) * l * x^l) = sum (λ (l : ℕ), ({d + 1} choose l) * (l * x^(l - 1))), from by ring,
          have h4 : ({d + 1} choose d) * d * x^(d - 1) = ({d + 1} choose d) * (d * x^(d - 1)), from by ring,
          rw [h2,h1] at hind,
          have h5 : ∀ l : ℕ, (({d + 1} choose l) * l * x^(l - 1)) = ({d + 1} choose l) * (polynomial.bernoulli l).eval x + (({d + 1} choose l) * l * x^(l - 1)) - ({d + 1} choose l) * (polynomial.bernoulli l).eval x, from by ring,
          have h6 : ∀ l : ℕ, l ≠ 0 → l < d → ({d + 1} choose l) * (polynomial.bernoulli l).eval x + (({d + 1} choose l) * l * x^(l - 1)) - ({d + 1} choose l) * (polynomial.bernoulli l).eval x = ({d + 1} choose l) * (polynomial.bernoulli l).eval x + (({d + 1} choose l) * l * x^(l - 1)) - ({d + 1} choose l) * (polynomial.bernoulli l).eval x, from
            by {
              assume (l : ℕ) (h6 : (l ≠ 0) → l < d) (h7 : l < d),
              have h8 : ({d + 1} choose l) * (polynomial.bernoulli l).eval x + (({d + 1} choose l) * l * x^(l - 1)) - ({d + 1} choose l) * (polynomial.bernoulli l).eval x = ({d + 1} choose l) * ((polynomial.bernoulli l).eval x + l * x^(l - 1)) - ({d + 1} choose l) * (polynomial.bernoulli l).eval x, from by ring,
              have h9 : ({d + 1} choose l) * (polynomial.bernoulli l).eval x + (({d + 1} choose l) * l * x^(l - 1)) - ({d + 1} choose l) * (polynomial.bernoulli l).eval x = ({d + 1} choose l) * (polynomial.bernoulli l).eval (1 + x) - ({d + 1} choose l) * (polynomial.bernoulli l).eval x, from by {rw [h8,←hind h7], ring},
              have h10 : ({d + 1} choose l) * (polynomial.bernoulli l).eval x + (({d + 1} choose l) * l * x^(l - 1)) - ({d + 1} choose l) * (polynomial.bernoulli l).eval x = ({d + 1} choose l) * (polynomial.bernoulli l).eval x, from by {rw h9, ring},
              rw h10,
              exact h6 l h7,
            },
          rw [←h3,h5,h4], 
          have h7 : {d + 1} choose (d + 1) = 1, from by ring,
          have h8 : ({d + 1} choose (d + 1)) * (polynomial.bernoulli (d + 1)).eval x + ({d + 1} choose (d + 1)) * (d + 1) * x^d - ({d + 1} choose (d + 1)) * (polynomial.bernoulli (d + 1)).eval x = ({d + 1} choose (d + 1)) * ((polynomial.bernoulli (d + 1)).eval x + (d + 1) * x^d), from by ring,
          have h9 : ({d + 1} choose (d + 1)) * (polynomial.bernoulli (d + 1)).eval x + ({d + 1} choose (d + 1)) * (d + 1) * x^d - ({d + 1} choose (d + 1)) * (polynomial.bernoulli (d + 1)).eval x = ((d + 1) * ((1 + x)^d + x^d)), from by {rw [h8,←h7], ring},
          have h10 : ({d + 1} choose (d + 1)) * (polynomial.bernoulli (d + 1)).eval x + ({d + 1} choose (d + 1)) * (d + 1) * x^d - ({d + 1} choose (d + 1)) * (polynomial.bernoulli (d + 1)).eval x = (d + 1) * ((1 + x)^d - x^d), from by {rw h9, ring},
          have h11 : ({d + 1} choose (d + 1)) * (polynomial.bernoulli (d + 1)).eval x + (({d + 1} choose (d + 1)) * (d + 1) * x^d) - ({d + 1} choose (d + 1)) * (polynomial.bernoulli (d + 1)).eval x = (d + 1) * x^(d - 1), from by {rw h10, ring},
          have h12 : {d + 1} choose (d + 1) = (d + 1), from by ring,
          rw [h12,h11],
        }
    ),

  have h1 : ∀ l : ℕ, (1 + x)^l = ((x + 1)^l), from by obviously,
  have h2 : (1+x)^(n-1) = x^(n-1) + (n-1)*x^(n-2) + (n-1) * (1+x)^(n-2), from by rw [sum_range,sum_range]; assumption, simp,
  have h3 : (polynomial.bernoulli n).eval (1+x) = n * (1 + x)^(n-1) + n * (1 + x)^(n-1), from by ring,
  have h5 : (polynomial.bernoulli n).eval (1+x) = (polynomial.bernoulli n).eval
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
