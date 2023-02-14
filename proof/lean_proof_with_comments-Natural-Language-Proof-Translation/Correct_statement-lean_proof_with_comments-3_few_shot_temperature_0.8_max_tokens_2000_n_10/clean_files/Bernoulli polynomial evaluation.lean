import number_theory.bernoulli


--OUTPUT 1
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- apply strong induction on $n$, so for all $m < d$,  $B_{m} (1 + x) = B_{m} (x) + m x^{m - 1}$
  induction n with d hd,
  from by ring,
  from by {
    -- and we want to show that $B_{d} (1 + x) = B_{d} (x) + d x^{d - 1}$
    have h1 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1),
      from by {
        have h2 : (d + 1) * (1 + x)^d = (d + 1) * x^d + ((d + 1) * ∑ (k : fin d), dchoose (d + 1) k * x^k), from by {
          rw pow_add, ring, },
        have h3 : ∀ k : fin d, (d + 1) * dchoose (d + 1) k * x^k = d * dchoose (d + 1) k * x^k + dchoose (d + 1) k * x^k, from 
          assume (k : fin d), (d + 1) * dchoose (d + 1) k * x^k = (d * dchoose (d + 1) k + dchoose (d + 1) k) * x^k, 
        have h4 : ∀ k : fin d, dchoose (d + 1) k * x^k = dchoose (d + 1) k * x^{k + 1} / x, from assume (k : fin d),
          dchoose (d + 1) k * x^k = dchoose (d + 1) k * x^{k + 1} / x,
        have h5 : (d + 1) * x^d = (d + 1) * ∑ (k : fin d), dchoose (d + 1) k * x^k, from by {
          congr, rw [← polynomial.bernoulli_eq_sum], ext, ring, },
        have h6 : (d + 1) * (1 + x)^d - (d + 1) * x^d = (d + 1) * ∑ (k : fin d), dchoose (d + 1) k * x^(k + 1) / x, from by {
          rw [h2,h5,add_comm], ring, },
        have h7 : (d + 1) * ∑ (k : fin d), dchoose (d + 1) k * x^(k + 1) = (d + 1) * ∑ (k : fin d), dchoose (d + 1) k * x^k * x, from by {
          congr, ext, ring, },
        have h8 : (d + 1) * ∑ (k : fin d), dchoose (d + 1) k * x^(k + 1) / x = (d + 1) * ∑ (k : fin d), dchoose (d + 1) k * x^k + (d + 1) * ∑ (k : fin d), dchoose (d + 1) k * x^k, from by {
          rw [h7,mul_div_cancel,one_mul], },
        have h9 : ∀ k : fin d, dchoose (d + 1) k * x^k = (polynomial.bernoulli k).eval x, from assume (k : fin d),
          dchoose (d + 1) k * x^k = (polynomial.bernoulli k).eval x,
        have h10 : ∀ k : fin d, dchoose (d + 1) k * x^k = (polynomial.bernoulli k).eval x, from assume (k : fin d),
          dchoose (d + 1) k * x^k = (polynomial.bernoulli k).eval x,
        have h11 : ∀ k : fin d, (d + 1) * dchoose (d + 1) k * x^k = (d + 1) * (polynomial.bernoulli k).eval x, from assume (k : fin d),
          (d + 1) * dchoose (d + 1) k * x^k = (d + 1) * (polynomial.bernoulli k).eval x,
        have h12 : ∀ k : fin d, dchoose (d + 1) k * x^k = dchoose (d + 1) k * x^{k + 1} / x, from assume (k : fin d),
          dchoose (d + 1) k * x^k = dchoose (d + 1) k * x^{k + 1} / x,
        have h13 : ∀ k : fin d, (d + 1) * dchoose (d + 1) k * x^(k + 1) = (d + 1) * (polynomial.bernoulli k).eval x * x, from assume (k : fin d),
          (d + 1) * dchoose (d + 1) k * x^(k + 1) = (d + 1) * (polynomial.bernoulli k).eval x * x,
        have h14 : ∀ k : fin d, (d + 1) * dchoose (d + 1) k * x^k + (d + 1) * dchoose (d + 1) k * x^k = (d + 1) * (polynomial.bernoulli k).eval x + (d + 1) * (polynomial.bernoulli k).eval x, from assume (k : fin d),
          (d + 1) * dchoose (d + 1) k * x^k + (d + 1) * dchoose (d + 1) k * x^k = (d + 1) * (polynomial.bernoulli k).eval x + (d + 1) * (polynomial.bernoulli k).eval x,
        have h15 : ∀ k : fin d, dchoose (d + 1) k * x^k + dchoose (d + 1) k * x^k = (polynomial.bernoulli k).eval x + (polynomial.bernoulli k).eval x, from assume (k : fin d),
          dchoose (d + 1) k * x^k + dchoose (d + 1) k * x^k = (polynomial.bernoulli k).eval x + (polynomial.bernoulli k).eval x,
        have h16 : ∀ k : fin d, d * (polynomial.bernoulli k).eval x + dchoose (d + 1) k * x^k = d * (polynomial.bernoulli k).eval x + (polynomial.bernoulli k).eval x, from assume (k : fin d),
          d * (polynomial.bernoulli k).eval x + dchoose (d + 1) k * x^k = d * (polynomial.bernoulli k).eval x + (polynomial.bernoulli k).eval x,
        have h17 : ∀ k : fin d, (d + 1) * (polynomial.bernoulli k).eval x + (d + 1) * (polynomial.bernoulli k).eval x = d * (polynomial.bernoulli k).eval x + (polynomial.bernoulli k).eval x, from assume (k : fin d),
          (d + 1) * (polynomial.bernoulli k).eval x + (d + 1) * (polynomial.bernoulli k).eval x = d * (polynomial.bernoulli k).eval x + (polynomial.bernoulli k).eval x,
        have h18 : (d + 1) * (1 + x)^d - (d + 1) * x^d = (d + 1) * ∑ (k : fin d), (polynomial.bernoulli k).eval x, from by {
          rw [h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17], ring, },
        have h19 : (d + 1) * (1 + x)^d - (d + 1) * x^
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) := 
begin
  induction n with d hd,
  {
    rw polynomial.bernoulli_zero,
    rw polynomial.eval_one,
    rw nat.sub_zero,
    ring,
  },
  {
    rw polynomial.bernoulli_succ,
    rw polynomial.eval_add,
    rw polynomial.eval_mul,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_one,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_add,
    rw nat.sub_succ,
    rw polynomial.eval_mul,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_one,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw polynomial.eval_add,
    rw polynomial.eval_mul,
    rw polynomial.eval_X,
    rw polynomial.eval_C,
    rw nat.cast_add,
    rw nat.cast_one,
    rw nat.add_comm,
    rw nat.add_one,
    rw nat.add_one,
    rw nat.add_one,
    rw nat.add_one,
    rw hd,
    ring,
  }
end

--OUTPUT 3
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
    -- we apply strong induction on $n$
  induction n with d hd,
    -- the base case with $n=0$ is trivial
  {
    show (polynomial.bernoulli 0).eval (1 + x) = (polynomial.bernoulli 0).eval x, from
    obviously,
  },
  -- in the inductive case, we have that $B_{m} (1 + x) = B_{m} (x) + m x^{m - 1}$ for all $m < d$
  {
    assume : ∀ m < d, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x ^ (m - 1),
    -- we want to show that $$B_{d} (1 + x) = B_{d} (x) + d x^{d - 1}$$
    have goal : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x ^ (d - 1), from
    begin
      --  multiplying both sides by $d + 1$, and using the fact that, for all $l \in \mathbb{N}$, $\sum_{k = 0}^{l} {l + 1 \choose k} B_k = (l + 1) X^l$ (where $B_k$ is the $k$-th Bernoulli number),
      have sum_eq : (d + 1) * ((1 + x) ^ d - x ^ d) = polynomial.sum (λ l, (d + 1) * ((d + 1) ^ l : ℚ) / (fact l) * x ^ (l - 1)), from
      begin
        { refine congr_arg (λ p : polynomial ℚ, (d + 1) * p) _, have h : ∀ n, ((d + 1) ^ n) / (fact n) = nth_bernoulli n * (d + 1), from
        begin
          assume n, rw [nat.otimes_pow, nat.div_pow_of_pow_le, nat.fact_eq_zero, zero_le, nat.div_eq_of_eq_mul, ←nat.div_eq_div_iff, ←nat.div_eq_div_iff],
          exact nat.pow_le_pow_of_le_right (d + 1) (succ n) (nat.le_add_right _ _),
        end, rw [h, nth_bernoulli_polynomial_eq], rw [polynomial.sum_C_mul], refl, },
        { assume l, rw [nat.div_eq_div_iff, nat.div_eq_div_iff], have h : (d + 1) ^ l * (fact d) * (d + 1) = (d + 1) ^ (l + 1), from
        calc (d + 1) ^ l * (fact d) * (d + 1) = (d + 1) ^ l * (fact d) * (1 + d + 1) : by rw add_comm
        ... = (d + 1) ^ l * (fact d) * (1 + (d + 1)) : by rw add_assoc
        ... = (d + 1) ^ l * (fact d) * (fact d + 1) : by rw [←fact_succ d, ←nat.fact_eq_zero d, add_zero]
        ... = (d + 1) ^ l * (fact (d + 1)) : by rw fact_succ
        ... = (d + 1) ^ (l + 1) : by rw [←nat.fact_eq_zero (d + 1), nat.pow_succ (d + 1) l], rw h, },
        { assume l hl, rw [fact_pos hl, nat.pow_succ (d + 1) l, nat.pow_succ (d + 1) (l - 1), nat.div_mul_cancel (nat.pos_of_ne_zero (ne_of_gt (nat.pos_of_ne_zero hl)))], rw ←nat.fact_eq_zero (d + 1), },
      end,
      -- The conclusion then follows easily
      cases nat.eq_or_lt_of_le (nat.succ_le_of_lt (by linarith)) with hdl hdl,
        -- If $d = l$ then we are done
      {
        rw hdl, rw [polynomial.sum_C_mul], rw [polynomial.sum_C_mul], rw ←sum_eq, refl,
      },
      {
        -- Otherwise, we use the fact that, for all $l \in \mathbb{N}$, $\sum_{k = 0}^{l} {l + 1 \choose k} B_k = (l + 1) X^l$ (where $B_k$ is the $k$-th Bernoulli number)
        have h7 : (d + 1) * ((1 + x) ^ d - x ^ d) = d * (d + 1) * x ^ (d - 1) + (d + 1) * ((1 + x) ^ (d - 1) - x ^ (d - 1)), from
        begin
          calc (d + 1) * ((1 + x) ^ d - x ^ d) = d * (d + 1) * x ^ (d - 1) + (d + 1) * ((1 + x) ^ d - x ^ d - x ^ (d - 1)) : by rw sub_sub
          ... = d * (d + 1) * x ^ (d - 1) + (d + 1) * ((1 + x) ^ d - x ^ d - (1 + x) * x ^ (d - 1)) : by rw nat.sub_sub
          ... = d * (d + 1) * x ^ (d - 1) + (d + 1) * ((1 + x) * ((1 + x) ^ (d - 1) - x ^ (d - 1))) : by rw sub_sub
          ... = d * (d + 1) * x ^ (d - 1) + (d + 1) * ((1 + x) * ((1 + x) ^ (d - 1) - (1 + x) * x ^ (d - 2))) : by rw nat.sub_sub
          ... = d * (d + 1) * x ^ (d - 1) + (d + 1) * ((1 + x) * (1 + x) ^ (d - 1) - (1 + x)^2 * x ^ (d - 2)) : by rw sub_sub
          ... = d * (d + 1) * x ^ (d - 1) + (d + 1) * (1 + x) * ((1 + x) ^ (d - 1) - x ^ (d - 1)) : by rw nat.sub_sub,
        end,
        -- and conclude by induction
        rw ←sum_eq at h7, rw polynomial.sum_add at h7, rw add_comm at h7, rw polynomial.sum_add at h7, rw ←nat.mul_sub_left_distrib at h7, rw pow_zero at h7, rw mul_one at h7, rw ←nat.mul_sub_left_distrib at h7, rw ←nat.mul_sub_left_distrib at h7, rw [polynomial.sum_C_mul], rw [polynomial.sum_C_mul], rw ←hd, rw pow_zero, rw mul_one, rw pow_zero, rw mul_one, rw ←hd, rw hdl, rw add_comm, rw add_comm, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←sum_eq, rw ←
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- ind./cases
  cases n,
  { -- base case
    have e1 : (polynomial.bernoulli (nat.succ 0)).eval (1 + x) = (polynomial.bernoulli (nat.succ 0)).eval x + (nat.succ 0) * x^(nat.succ 0 - 1), from by
    {
      -- rw
      rw nat.one_mul,
      rw nat.one_pow,
      rw polynomial.bernoulli,
      rw polynomial.eval_sum,
      -- calc
      calc (polynomial.X * (polynomial.bernoulli (nat.succ 0)).deriv).eval (1 + x) = polynomial.X.eval (1 + x) * (polynomial.bernoulli (nat.succ 0)).deriv.eval (1 + x) : by apply polynomial.eval_mul
      ... = (1 + x) * (polynomial.bernoulli (nat.succ 0)).deriv.eval (1 + x) : by {rw polynomial.X, rw polynomial.eval_C, ring}
      ... = (1 + x) * (polynomial.bernoulli (nat.succ (nat.succ 0))).deriv.eval x : by {rw polynomial.bernoulli, rw polynomial.deriv_sum, rw ← polynomial.deriv_C, rw polynomial.deriv_X, rw polynomial.deriv_const, rw polynomial.eval_pow, ac_refl, rw polynomial.deriv_const, rw polynomial.eval_C, rw nat.succ_ne_zero, rw polynomial.eval_const, ac_refl}
      ... = (1 + x) * 1 : by {rw polynomial.bernoulli, rw polynomial.deriv_sum, rw ← polynomial.deriv_C, rw polynomial.deriv_X, rw polynomial.deriv_const, rw polynomial.eval_pow, ac_refl, rw polynomial.deriv_const, rw polynomial.eval_C, rw nat.succ_ne_zero, rw polynomial.eval_C, ac_refl}
      ... = 1 + x : by ring
      ... = polynomial.X.eval x * (polynomial.bernoulli (nat.succ 0)).deriv.eval x : by {rw polynomial.X, rw polynomial.eval_C, ring,}
      ... = (polynomial.X * (polynomial.bernoulli (nat.succ 0)).deriv).eval x : by apply polynomial.eval_mul
      ... = (polynomial.bernoulli (nat.succ 0)).eval x : by rw polynomial.bernoulli,
      rw nat.one_mul,
      rw nat.one_pow,
    },
    rw e1,
    exact rfl,
  },
  { -- inductive case
    assume d : ℕ,
    assume ih : polynomial.bernoulli d = polynomial.bernoulli d.succ.succ,
    have e1 : (polynomial.bernoulli (nat.succ d)).eval (1 + x) = (polynomial.bernoulli (nat.succ d)).eval x + (nat.succ d) * x^(nat.succ d - 1), from by
    {
      -- rw
      rw polynomial.bernoulli,
      rw polynomial.eval_sum,
      -- calc
      calc (polynomial.X * (polynomial.bernoulli (nat.succ d)).deriv).eval (1 + x) = polynomial.X.eval (1 + x) * (polynomial.bernoulli (nat.succ d)).deriv.eval (1 + x) : by apply polynomial.eval_mul
      ... = (1 + x) * (polynomial.bernoulli (nat.succ d)).deriv.eval (1 + x) : by {rw polynomial.X, rw polynomial.eval_C, ring}
      ... = (1 + x) * (polynomial.bernoulli (nat.succ (nat.succ d))).deriv.eval x : by {rw polynomial.bernoulli, rw polynomial.deriv_sum, rw ← polynomial.deriv_C, rw polynomial.deriv_X, rw polynomial.deriv_const, rw polynomial.eval_pow, ac_refl, rw polynomial.deriv_const, rw polynomial.eval_C, rw nat.succ_ne_zero, rw polynomial.eval_const, ac_refl}
      ... = (1 + x) * (nat.succ d) * x^(d - 1) : by {rw polynomial.bernoulli, rw polynomial.deriv_sum, rw ← polynomial.deriv_C, rw polynomial.deriv_X, rw polynomial.deriv_const, rw polynomial.eval_pow, ac_refl, rw polynomial.deriv_const, rw polynomial.eval_C, rw nat.succ_ne_zero, rw polynomial.eval_C, ac_refl, rw polynomial.eval_mul, rw polynomial.eval_const, rw polynomial.eval_pow, ac_refl}
      ... = (1 + x) * (nat.succ d) * x^(d - 1) : by {rw nat.pow_succ_eq_mul_pow, rw nat.succ_pred_eq_of_pos, rw nat.zero_ne_one, ac_refl}
      ... = (nat.succ d) * (1 + x) * x^(d - 1) : by ring
      ... = (1 + x) * (nat.succ d) * x^(d - 1) : by ring
      ... = (1 + x) * (polynomial.bernoulli d).deriv.eval x : by {rw polynomial.bernoulli, rw polynomial.deriv_sum, rw ← polynomial.deriv_C, rw polynomial.deriv_X, rw polynomial.deriv_const, rw polynomial.eval_pow, ac_refl, rw polynomial.deriv_const, rw polynomial.eval_C, rw nat.succ_ne_zero, rw polynomial.eval_const, ac_refl}
      ... = (1 + x) * (polynomial.bernoulli (nat.succ d)).deriv.eval x : by rw ih
      ... = polynomial.X.eval x * (polynomial.bernoulli (nat.succ d)).deriv.eval x : by {rw polynomial.X, rw polynomial.eval_C, ring}
      ... = (polynomial.X * (polynomial.bernoulli (nat.succ d)).deriv).eval x : by apply polynomial.eval_mul
      ... = (polynomial.bernoulli (nat.succ d)).eval x : by rw polynomial.bernoulli
      ... = (polynomial.bernoulli d).eval x + (nat.succ d) * x^(nat.succ d - 1) : by rw ih
    },
    rw e1,
    exact rfl,
  }
end

--OUTPUT 5
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- We apply strong induction on $n$
  induction n with d hd,
  case nat.zero {
    -- Let $B_0 (x) = 1$
    use (1 : ℚ),
    -- Then $B_0 (1 + x) = 1$, as required.
    conv {to_lhs, rw ← hd }, ring
  },
  case nat.succ {
    -- Given $B_n (x)$ is correct, we want to deduce that $B_{n+1} (x)$ is correct.
    have h1 : polynomial.bernoulli n.succ = polynomial.bernoulli n + n.succ * X^n, from
        by obviously,

    have h2 : (n + 1) * (1 + x)^n = (n + 1) * x^n + (n + 1) * (n * x^(n - 1)), from by {
      have h2 : (1 + x)^n = x^n + n * x^(n - 1), from hd.symm,
      rw h2, ring,
    },  

    rw h2, 
    show (polynomial.bernoulli (n+1)).eval (1+x) = 
        (polynomial.bernoulli (n+1)).eval x + (n+1) * x^n, rw [h1, eval_add, h1, eval_add, h1], ring }
end

--OUTPUT 6
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  have h1 : (polynomial.bernoulli n).eval (1 + x) = n * x^(n - 1),
  {
    have h2 : (polynomial.bernoulli n).eval (1 + x) = (((polynomial.bernoulli n).eval 1) * (1 + x)^n - (polynomial.bernoulli n).eval x * (1 + x)^n), by ring,
    rw [h2, polynomial.bernoulli_eval_one], rw pow_one (1 + x), rw pow_one x, rw mul_one, rw mul_one, rw mul_one, ring,
  },

  have h3 : (polynomial.bernoulli n).eval x + n * x^(n - 1) = ((polynomial.bernoulli n).eval x + (polynomial.bernoulli n).eval x) + n * x^(n - 1), by ring,
  rw [h3, h1], ring,
end

--OUTPUT 7
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n with m hi,
  { -- Base case
    -- $n = 0$
    exact by {simp},
  },
  {
    -- Induction step
    have H2 : ∀ x : ℚ, (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1), from 
      assume x : ℚ, hi,
    have H3 : ∀ x : ℚ, (polynomial.bernoulli (m + 1)).eval (1 + x) = (polynomial.bernoulli (m + 1)).eval x + m * x^m * ((x + 1) - x), from 
      assume x : ℚ, polynomial.eval_mul_leading_coeff (polynomial.bernoulli (m + 1)) (1 + x),
    
    -- The conclusion follows easily
    exact by {rw [H2,H3], ring, done},
  }
end

--OUTPUT 8
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- We apply strong induction on $n$
  apply nat.strong_induction_on n,
  assume (d : ℕ) (H : ∀ m : ℕ, m < d →
    (polynomial.bernoulli m).eval (1 + x) = (polynomial.bernoulli m).eval x + m * x^(m - 1)),

  -- We want to show that $B_{d} (1 + x) = B_{d} (x) + d x^{d - 1}$
  have h1 : (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1),
  
  -- Multiplying both sides by $(d+1)$, and using the fact that, for all $l \in \mathbb{N}$, $\sum_{k = 0}^{l} {l + 1 \choose k} B_k = (l + 1) X^l$ 
  calc (polynomial.bernoulli d).eval (1 + x) = (polynomial.bernoulli d).eval x + d * x^(d - 1) : H d (nat.succ_lt_succ (nat.zero_lt_succ d))
  ... = (d + 1) * (1 + x)^d - (d + 1) * x^d : 
    -- (where $B_k$ is the $k$-th Bernoulli number)
    begin
      assume (d : ℕ),
      have h0 : ∀ l : ℕ, (polynomial.bernoulli l).eval 0 = l / (l + 1), from assume l,
        begin
          -- Let us first prove that $B_l (x) = B_{l - 1} (x) + 1$
          have h1 : (polynomial.bernoulli l).eval x = (polynomial.bernoulli (l - 1)).eval x + 1, from by {
            induction l with l hl,
            have h2 : polynomial.bernoulli 0 = polynomial.C 1, from by {
              apply polynomial.C_1,
            },
            rw [h2,polynomial.C_add],
            rw [hl],
            apply polynomial.one_mul,
          },
          
          -- Now, using the fact that $B_l (0) = 0$ for all $l \in \mathbb{N}$, we conclude that $B_{l - 1} (0) = -\frac{1}{l}$
          rw [h1,ring.sub_zero],
        end,
      
      -- We now need to apply the formula $\sum_{k = 0}^{l} {l + 1 \choose k} B_k = (l + 1) X^l$
      have h2 : ∀ l : ℕ, (∑ k in finset.range (l + 1), (l + 1)!/((k+1)! * (l - k)!) * l / (l + 1)) = l + 1, from assume l,
        begin
          induction l with l hl,
          simp,
          show (∑ (k : fin n), n! / k! / ((n - k + 1)!) * (n - 1) / (n + 1)) = n + 1, from by simp,
          
          show (∑ (k : fin (l+2)), (l+2)! / k! / (l+2 - k)! * l / (l+2)) = l + 1 + 1, from by {
            rw [finset.sum_range_succ],
            rw [hl],
            have h3 : (l + 1) * (l + 2) / (l + 2) = l + 1, from begin
              rw [mul_comm (l + 1) (l + 2),mul_one_div_cancel l.succ_pos],
              exact dec_trivial,
            end,
            ring,
          }
        end,
      
      -- Now, let us apply the formula
      induction d with d hd,
      rw [zero_add,finset.sum_range_zero],
      simp,

      rw [ring.add_assoc,ring.one_add,finset.sum_range_succ],
      rw [ring.add_assoc,ring.one_add,finset.sum_range_succ],
      have h3 : (d + 1) * (1 + x)^d - (d + 1) * x^d =
        (∑ k in finset.range (d + 1), (d + 1)!/((k+1)! * (d - k + 1)!) * (d + 1)) * x^d - (d + 1) * x^d, from by {
        rw [polynomial.pow_coe_add_one,polynomial.pow_coe_add_one],
        rw [polynomial.coe_C],
        rw [polynomial.coe_C],
        have h3 : ∑ k in finset.range (1 + 1), d! / ((1 + k)! * (1 - k + 1)!) = d + 1, from 
          by {rw [one_add,finset.sum_range_succ], rw [finset.sum_range_zero], simp, },
        rw [h3],
        rw [nat.fact_succ_eq_succ_mul,nat.fact_succ_eq_succ_mul],
        rw [field.div_mul_cancel ((nat.succ d).pos)],
        rw [field.div_mul_cancel ((nat.succ d).pos)],
        rw [nat.cast_one,nat.cast_one,field.mul_one],
        rw [← fpow_add_one,fpow_succ],
        have h4 : (d! / ((1 + 1)! * (1 - 1 + 1)!)) = d, from by {
          have h5 : (d! / ((1 + 1)! * (1 - 1 + 1)!)) = (d! / (1! * (1 - 1 + 1)!)), from by simp,
          have h6 : (d! / (1! * (2)!) = d), from by {
            rw [nat.fact_succ_eq_succ_mul,nat.fact_eq_one,nat.cast_one,field.one_mul],
            rw [field.mul_inv_cancel ((nat.succ d).pos),field.inv_eq_one_div],
            rw [nat.fact_eq_one,nat.cast_one,field.one_div],
            ring,
          },
          exact eq.trans h5 h6,
        },
        rw [h4],
      },
      have h4 : (∑ k in finset.range (d + 1), (d + 1)!/((k+1)! * (d - k + 1)!) * (d + 1)) * x^d - (d + 1) * x^d =
        (d + 1) * x^d * (∑ k in finset.range (d + 1), (d + 1)!/((k+1)! * (d - k + 1)!) - 1), from by {
          rw [mul_sub,mul_sub,mul_assoc,mul_comm x^d (d + 1)],
          ring,
        },
      have h5 : (d + 1) * x^d * (∑ k in finset.range (d + 1), (d + 1)!/((k+1)! * (d - k + 1)!) - 1) = (d + 1) * x^d * (d + 1 - 1), from by {
        have h6 : ∑ k in finset.range (d + 1), (d + 1)!/((k+1)! * (d - k + 1)!) - 1 = d, from
          by {rw [h2,nat.sub_eq_zero_iff_eq,one_add],},
        rw [h6],
      },
      have h6 : (d + 1) * x^d
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  induction n using nat.strong_induction_on,
  rw polynomial.bernoulli_zero, rw polynomial.eval_zero, rw polynomial.eval_zero, rw one_add_one, ring,
  rw polynomial.bernoulli_succ, rw polynomial.eval_add, rw polynomial.eval_C, rw add_one, 
  rw polynomial.eval_mul, rw polynomial.eval_X, rw polynomial.eval_pow, rw polynomial.eval_X,
  rw polynomial.eval_mul, rw polynomial.eval_X, rw polynomial.eval_pow, rw pow_succ, rw mul_one,
  have h : polynomial.bernoulli (n + 1) = (n + 1 : ℚ) * X^n + polynomial.bernoulli n, from
    polynomial.bernoulli_eq_add_mul_X n,
  rw polynomial.eval_add, rw polynomial.eval_mul, rw polynomial.eval_C, rw polynomial.eval_X,
  rw polynomial.eval_pow, rw pow_succ, rw pow_zero, ring, rw ←h, rw ←n_ih, ring, 
end

--OUTPUT 10
theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (polynomial.bernoulli n).eval (1 + x) = (polynomial.bernoulli n).eval x + n * x^(n - 1) :=
begin
  -- We apply strong induction on $n$
  have h1 : ∀ (d : ℕ), ∀ (m : ℕ), m < d → (bernoulli m).eval (1 + x) = (bernoulli m).eval x + m * x^(m - 1),
  begin
    intro d,
    induction d with d hd, -- d = 0
    {
      assume m hm,
      rw [zero_lt_iff_ne_zero] at hm,
      cases m,
      {
        rw [one_eq_succ_zero],
        simp,
      },
      {
        rw [succ_eq_add_one],
        rw [add_one_ne_zero] at hm,
        rw [add_lt_iff_pos_right] at hm,
        rw [pos_iff_ne_zero] at hm,
        rw [succ_eq_add_one],
        rw [hm],
        ring,
      }
    }, -- d = succ d, use strong induction
    {
      assume (m : ℕ) (hm : m < succ d),
      cases hm with hm_lt hm_eq,
      rw [succ_lt_succ_iff] at hm_lt,
      rw [hm_eq],
      rw [succ_eq_add_one],
      have h1 : (bernoulli d).eval (1+x) = (bernoulli d).eval x + d * x^(d - 1), from hd _ hm_lt,
      ring,
      rw [succ_eq_add_one],
      have h2 : (bernoulli m).eval (1+x) = (bernoulli m).eval x + m * x^(m - 1), from hd _ hm_lt,
      exact h2,
    }
  end,
  -- Hence, $(d + 1) (1 + x)^d - (d + 1) x^d = \sum_{l = 0}^{d} {d + 1 \choose l} l x^{l - 1}$
  have h2 : (n + 1) * (1 + x)^n - (n + 1) * x^n = (polynomial.eval (bernoulli n) x) + sum (range n) (λ l : ℕ, (n + 1) * (l+1) * x^l / ↑(n+1)),
  begin
    have h1_1 : ∀ (l : ℕ), l < n + 1 → (n+1) * (l+1) * x^l  = ((n+1) * x^l) * (l+1), from
      assume (l : ℕ) (h : l < n + 1), by ring,
    rw [←polynomial.eval_add (polynomial.bernoulli n) ((n+1) * x^n),
        polynomial.eval_add, polynomial.eval_smul, polynomial.eval_C, polynomial.eval_zero,
        polynomial.sum_range_succ_zero n (λ l : ℕ, (n + 1) * (l + 1) * x^l / ↑(n + 1)),
        ←polynomial.eval_add (polynomial.sum_range_succ_zero n (λ l : ℕ, (n + 1) * (l + 1) * x^l / ↑(n + 1)))
        (((n+1) * x^n) * (1+x)),
        polynomial.eval_add, polynomial.eval_add (polynomial.sum_range_succ_zero n (λ l : ℕ, (n + 1) * (l + 1) * x^l / ↑(n + 1))),
        polynomial.eval_smul, polynomial.eval_C],
    simp,
    rw [polynomial.sum_mul_distrib],
    have h1_2 : (1+x) * (n+1) - (n+1) * x^n = (n+1) * x^(n - 1), by ring,
    rw [h1_2],
    have h1_3 : ∀ (l : ℕ), l < n + 1 → (1+x)^l = (x^l * (l+1)) + (bernoulli l).eval (1+x), from 
      assume (l : ℕ) (h : l < n + 1), 
      begin
        induction l with l hl,
        {
          rw [zero_lt_iff_ne_zero] at h,
          rw [one_eq_succ_zero],
          rw [one_eq_succ_zero] at h,
          have h1 : ¬ l < 0, from 
            (not_lt_of_ge (nat.zero_le l)) 
              (by {rw [lt_iff_le_and_ne],
                    split,
                    rwa nat.zero_le,
                    rw [one_ne_zero],
                    intro h2,
                    rw [succ_inj] at h2,
                    rw [h2],
                    exact h})
          rw [zero_lt_iff_ne_zero] at h1,
          rw [h1],
          simp,
        }, -- l = succ l, use strong induction
        {
          rw [succ_lt_succ_iff] at h,
          rw [succ_eq_add_one, ←add_zero (polynomial.bernoulli l)],
          rw [polynomial.mul_add],
          rw [polynomial.mul_C_mul_X, polynomial.mul_X_mul_X],
          rw [←polynomial.eval_add (polynomial.bernoulli l) x^l],
          rw [polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_C],
          have h1 : l < n + 1, from h.left,
          have h2 : (bernoulli l).eval (1+x) = (bernoulli l).eval x + l * x^(l - 1), from h1_3 l h1,
          rw [h2, ←hl h.left],
          ring,
        },
      end,
    simp,
    have h1_4 := (h1_3 n (le_refl n)),
    rw [←polynomial.eval_add (polynomial.bernoulli n) x^n] at h1_4,
    rw [←polynomial.eval_smul (bernoulli n) (n+1) x^n],
    rw [←polynomial.eval_add (polynomial.bernoulli n) n * x^n] at h1_4,
    rw [polynomial.eval_add, polynomial.eval_add, polynomial.eval_add, polynomial.eval_C],
    ring,
    {
      assume i hi,
      have h1_5 : (1 + x)^i = (x^i * (i + 1)) + (bernoulli i).eval (1 + x), from h1_3 _ hi,
      rw [h1_5],
      rw [polynomial.eval_add, polynomial.eval_smul, polynomial.eval_C],
      ring,
    }
  end,
  -- The conclusion then follows easily
  rw [←add_assoc, ←h2],
  ring,
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
