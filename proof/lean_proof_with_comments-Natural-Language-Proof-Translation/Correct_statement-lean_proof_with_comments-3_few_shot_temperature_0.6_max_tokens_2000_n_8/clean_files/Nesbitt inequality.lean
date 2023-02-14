import data.real.basic


--OUTPUT 1
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  -- $\frac a {b + c} + \frac b {a + c} + \frac c {a + b}$ is the arithmetic mean
  have h1 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a + b + c) / 3, from
    by {norm_num,ring},
  -- $\frac 1 {b + c} + \frac 1 {a + c} + \frac 1 {a + b}$ is the harmonic mean
  have h2 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) = 3 / ((b + c) + (a + c) + (a + b)), from
    by {norm_num,ring},
  -- $\frac 1 {b + c} + \frac 1 {a + c} + \frac 1 {a + b}$ is the harmonic mean
  have h3 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) = 3 / ((b + c) + (a + c) + (a + b)), from
    by {norm_num,ring},
  -- $\frac a {b + c} + \frac b {a + c} + \frac c {a + b}$ is the arithmetic mean
  have h4 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a + b + c) / 3, from
    by {norm_num,ring},
  -- $\frac {a + b + c} {\paren {b + c} + \paren {a + c} + \paren {a + b} } = \dfrac 1 2$
  have h5 : (a + b + c) / ((b + c) + (a + c) + (a + b)) = 1 / 2, from
    by {norm_num,ring},
  -- $\frac {9 \paren {a + b + c} } {\paren {b + c} + \paren {a + c} + \paren {a + b} }$
  have h6 : 9 * (a + b + c) / ((b + c) + (a + c) + (a + b)) = 9 / 2, from
    by {norm_num,ring},
  -- $\frac {\frac 1 {b + c} + \frac 1 {a + c} + \frac 1 {a + b} } 3$
  have h7 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) / 3 = 3 / ((b + c) + (a + c) + (a + b)), from
    by {norm_num,ring},
  -- $\frac {a + b + c} {b + c} + \frac {a + b + c} {a + c} + \frac {a + b + c} {a + b}$
  have h8 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) = 9 / 2, from
    by {norm_num,ring},
  -- $\frac a {b + c} + \frac b {a + c} + \frac c {a + b} \ge \dfrac 3 2$
  show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ 3 / 2, from
    by {rw [← h1, ← h8], apply arithmetic_mean_is_never_less_than_harmonic_mean, norm_num, ring, exact hb, exact hc},
end

--OUTPUT 2
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  -- adding a $3$
  have h1 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = ((a + b + c) / (b + c)) + ((a + b + c) / (a + c)) + ((a + b + c) / (a + b)), from
    by rw add_three,
  -- as $\dfrac {a + b + c} {\paren {b + c} + \paren {a + c} + \paren {a + b} } = \dfrac 1 2$
  have h2 : ((a + b + c) / (b + c)) + ((a + b + c) / (a + c)) + ((a + b + c) / (a + b)) ≥ ((9 * (a + b + c)) / ((b + c) + (a + c) + (a + b))), from
    by rw [div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same,div_add_div_same],
  -- dividing by $3 \paren {a + b + c}$
  have h3 : ((a + b + c) / (b + c)) + ((a + b + c) / (a + c)) + ((a + b + c) / (a + b)) ≥ (3 / ((b + c) + (a + c) + (a + b))), from
    by rw div_mul_div_same h1,
  -- These are the arithmetic mean and the harmonic mean of $\dfrac 1 {b + c}$, $\dfrac 1 {a + c}$ and $\dfrac 1 {a + b}$.
  show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from
    by {rw ← h1, apply arithmetic_mean_is_never_less_than_harmonic_mean, exact h3}
end

--OUTPUT 3
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  -- $a$, $b$ and $c$ are positive real numbers
  assume (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),

  -- Then:
  -- :$\dfrac a {b + c} + \dfrac b {a + c} + \dfrac c {a + b} \ge \dfrac 3 2$
  show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from
  begin
    -- $\leadstoandfrom$
    have h1 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (9 / 2) * (a + b + c) / ((b + c) + (a + c) + (a + b)), from
    begin
      -- as $\dfrac {a + b + c} {\paren {b + c} + \paren {a + c} + \paren {a + b} } = \dfrac 1 2$
      have h1 : (a + b + c) / ((b + c) + (a + c) + (a + b)) = (1 / 2), from by {
        have h1 : ((b + c) + (a + c) + (a + b)) * (a + b + c) = (b + c) * (a + b + c) + (a + c) * (a + b + c) + (a + b) * (a + b + c), from by ring,
        have h2 : ((b + c) + (a + c) + (a + b)) * (a + b + c) = (b + c) * (a + b + c) + (a + c) * (a + b + c) + (a + b) * (a + b + c), from by ring,
        show ((a + b + c) / ((b + c) + (a + c) + (a + b))) = (1 / 2), from by {
          have h3 : ((a + b + c) * ((b + c) + (a + c) + (a + b))) = ((a + b + c) * (a + b + c)) + ((a + b + c) * (a + c)) + ((a + b + c) * (b + c)), from by ring,
          have h4 : ((a + b + c) * ((b + c) + (a + c) + (a + b))) = ((a + b + c) * (a + b + c)) + ((a + b + c) * (a + c)) + ((a + b + c) * (b + c)), from by ring,
          have h5 : ((a + b + c) * ((b + c) + (a + c) + (a + b))) = ((a + b + c) * (a + b + c)) + ((a + b + c) * (a + c)) + ((a + b + c) * (b + c)), from by ring,
          have h6 : ((a + b + c) * ((b + c) + (a + c) + (a + b))) = ((a + b + c) * (a + b + c)) + ((a + b + c) * (a + c)) + ((a + b + c) * (b + c)), from by ring,
          have h7 : ((a + b + c) * ((b + c) + (a + c) + (a + b))) = ((a + b + c) * (a + b + c)) + ((a + b + c) * (a + c)) + ((a + b + c) * (b + c)), from by ring,
          have h8 : ((a + b + c) * ((b + c) + (a + c) + (a + b))) = ((a + b + c) * (a + b + c)) + ((a + b + c) * (a + c)) + ((a + b + c) * (b + c)), from by ring,
          rw [h3,h7,h8,div_mul_cancel _ (ne.symm (ne_of_lt ha))],
          rw [h4,h6,h8,div_mul_cancel _ (ne.symm (ne_of_lt hb))],
          rw [h5,h6,h7,div_mul_cancel _ (ne.symm (ne_of_lt hc))],
          ring,
        },
      },
      -- $\leadstoandfrom$
      have h2 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (9 / 2) * (a + b + c) / ((b + c) + (a + c) + (a + b)), from by {
        rw h1,
        have h3 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (9 / 2) * (1 / 2), from by linarith,
        rw mul_comm (9 / 2) (1 / 2),
        exact h3,
      },
      -- $\leadstoandfrom$
      have h3 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (9 / 2) * (1 / 2), from by linarith,
      rw mul_comm (9 / 2) (1 / 2),
      exact h3,
    },

    -- These are the arithmetic mean and the harmonic mean of $\dfrac 1 {b + c}$, $\dfrac 1 {a + c}$ and $\dfrac 1 {a + b}$.

    -- From Arithmetic Mean is Never Less than Harmonic Mean the last inequality is true.

    -- Thus Nesbitt's Inequality holds.
    have h2 : (9 / 2) * (a + b + c) / ((b + c) + (a + c) + (a + b)) ≥ (9 / 2) * (3 / ((b + c) + (a + c) + (a + b))), from by {
      have h3 : ((b + c) + (a + c) + (a + b)) * (a + b + c) = (b + c) * (a + b + c) + (a + c) * (a + b + c) + (a + b) * (a + b + c), from by ring,
      have h4 : ((b + c) + (a + c) + (a + b)) * (a + b + c) = (b + c) * (a + b + c) + (a + c) * (a + b + c) + (a + b) * (a + b + c), from by ring,
      have h5 : ((b + c) + (a + c) + (a + b)) * (a + b + c) = (b + c) * (a + b + c) + (a + c) * (a + b + c) + (a + b) * (a + b + c), from by ring,
      have h6 : ((b + c) + (a + c) + (a + b)) * (a + b + c) = (b + c) * (a + b + c) + (a + c) * (a + b + c) + (a + b) * (a + b + c), from by ring,
      have h7 : ((b + c) + (a + c) + (a + b)) * (a + b + c) = (b + c) * (a + b + c) + (a + c) * (a + b + c) + (a + b) * (a + b + c), from by ring,
      have h8 : ((b + c) + (a + c) + (a + b)) * (a + b + c) = (b + c) * (a + b + c) + (a + c) * (a + b + c) + (a + b) * (a + b + c), from by ring,
      have h9 : ((b + c) + (a + c) + (a + b)) * (a + b + c) = (b + c) * (a + b + c) + (a + c) * (a + b + c) + (a + b) * (a
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  -- Rearranging and adding $3$ gives:
  have h1 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from by {
    rw [add_div,add_div,add_div,add_div,add_div,add_div,add_div],
    have h2 : a + b + c > 0, from by {rw ← add_assoc, rw add_comm b c, rw add_assoc, rw add_comm a (b + c), rw add_assoc, rw add_comm c a, rw add_assoc, rw add_comm b c, rw add_assoc, rw add_comm a (b + c), rw add_assoc, rw add_comm c a, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, ring},
    rw ← div_div_eq_div_mul,
    rw div_self h2,
    rw mul_one,
    rw mul_comm,
    rw mul_one,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw add_mul,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ← add_assoc,
    rw ←
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  -- adding $3$ gives:
  have h1 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (9 / 2), from by {
    have h2 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + 3, from by {
      rw ← add_assoc (c / (a + b)) (b / (a + c)) (a / (b + c)),
      rw add_comm 3 (c / (a + b)), rw ← add_assoc (b / (a + c)) (a / (b + c)) 3,
      rw ← add_assoc (a / (b + c)) 3 (b / (a + c)), rw ← add_assoc 3 (b / (a + c)) (a / (b + c)),
      repeat {rw ← add_assoc},
    },
    have h3 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + 3 = (a / (b + c)) + 3 + (b / (a + c)) + (c / (a + b)), from by {
      rw ← add_assoc (c / (a + b)) (b / (a + c)) (a / (b + c)),
      rw add_comm 3 (c / (a + b)), rw ← add_assoc (b / (a + c)) (a / (b + c)) 3,
      rw ← add_assoc (a / (b + c)) 3 (b / (a + c)), rw ← add_assoc 3 (b / (a + c)) (a / (b + c)),
      repeat {rw ← add_assoc},
    },
    have h4 : (a / (b + c)) + 3 + (b / (a + c)) + (c / (a + b)) = 3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b)), from by {
      rw ← add_assoc 3 (c / (a + b)) ((a / (b + c)) + (b / (a + c))),
      rw ← add_assoc 3 ((a / (b + c)) + (b / (a + c))) (c / (a + b)),
      repeat {rw ← add_assoc},
    },
    have h5 : 3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = 3 + ((a / (b + c)) + (b / (a + c)) + (c / (a + b))), from by {
      rw ← add_assoc 3 (c / (a + b)) ((a / (b + c)) + (b / (a + c))),
      rw ← add_assoc 3 ((a / (b + c)) + (b / (a + c))) (c / (a + b)),
      repeat {rw ← add_assoc},
    },
    have h6 : 3 + ((a / (b + c)) + (b / (a + c)) + (c / (a + b))) = (3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b))), from by {
      rw ← add_assoc 3 (c / (a + b)) ((a / (b + c)) + (b / (a + c))),
      rw ← add_assoc 3 ((a / (b + c)) + (b / (a + c))) (c / (a + b)),
      repeat {rw ← add_assoc},
    },
    have h7 : 3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b))) + 0, from by {
      rw ← add_assoc (c / (a + b)) (b / (a + c)) (a / (b + c)),
      rw add_comm 3 (c / (a + b)), rw ← add_assoc (b / (a + c)) (a / (b + c)) 3,
      rw ← add_assoc (a / (b + c)) 3 (b / (a + c)), rw ← add_assoc 3 (b / (a + c)) (a / (b + c)),
      repeat {rw ← add_assoc},
    },
    have h8 : (3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b))) + 0 = (3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b))) + 3*0, from by {
      rw ← add_assoc (c / (a + b)) (b / (a + c)) (a / (b + c)),
      rw add_comm 3 (c / (a + b)), rw ← add_assoc (b / (a + c)) (a / (b + c)) 3,
      rw ← add_assoc (a / (b + c)) 3 (b / (a + c)), rw ← add_assoc 3 (b / (a + c)) (a / (b + c)),
      repeat {rw ← add_assoc},
    },
    have h9 : (3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b))) + 3*0 = (3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b))) + 3*1, from by {
      rw ← add_assoc (c / (a + b)) (b / (a + c)) (a / (b + c)),
      rw add_comm 3 (c / (a + b)), rw ← add_assoc (b / (a + c)) (a / (b + c)) 3,
      rw ← add_assoc (a / (b + c)) 3 (b / (a + c)), rw ← add_assoc 3 (b / (a + c)) (a / (b + c)),
      repeat {rw ← add_assoc},
    },
    have h10 : (3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b))) + 3*1 = 3 + (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + 3, from by {
      rw ← add_assoc (c / (a + b)) (b / (a + c)) (a / (b + c)),
      rw add_comm 3 (c / (a + b)), rw ← add_assoc (b / (a + c)) (a / (b + c)) 3,
      rw ← add_assoc (a / (b + c)) 3 (b / (a + c)), rw ← add_assoc 3 (b / (a + c)) (a / (b + c)),
      repeat {rw ← add_assoc},
    },
    show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (9 / 2), from eq.trans h2 (eq.trans h3 (eq.trans h4 (eq.trans h5 (eq.trans h6 (eq.trans h7 (eq.trans h8 h9))))))
  },

  -- as $\dfrac {a + b + c} {\paren {b + c} + \paren {a + c} + \paren {a + b} } = \dfrac 1 2$
  have h2 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (9 / ((b + c) + (a + c) + (a + b))), from by {
    have h3 : (a + b + c
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  -- By adding $3$
  have h1 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ ((a + b + c) / (b + c)) + ((a + b + c) / (a + c)) + ((a + b + c) / (a + b)),
    from by {rw [add_halves,add_halves,add_halves, add_halves,add_halves,add_halves], ring,},
  -- as $\dfrac {a + b + c} {\paren {b + c} + \paren {a + c} + \paren {a + b} } = \dfrac 1 2$
  have h2 : ((a + b + c) / (b + c)) + ((a + b + c) / (a + c)) + ((a + b + c) / (a + b)) ≥ (9 * (a + b + c)) / ((b + c) + (a + c) + (a + b)),
    from by {rw add_halves, ring,},
  -- dividing by $3 \paren {a + b + c}$
  have h3 : (9 * (a + b + c)) / ((b + c) + (a + c) + (a + b)) ≥ ((1 / (b + c)) + (1 / (a + c)) + (1 / (a + b))) / 3,
    from by {rw mul_assoc, apply div_le_div_of_le_of_pos h2, ring,},
  -- These are the arithmetic mean and the harmonic mean of $\dfrac 1 {b + c}$, $\dfrac 1 {a + c}$ and $\dfrac 1 {a + b}$.
  have h4 : ((1 / (b + c)) + (1 / (a + c)) + (1 / (a + b))) / 3 ≥ (3 / ((b + c) + (a + c) + (a + b))),
    from by {apply arithmetic_mean_ge_harmonic_mean,},
  have h5 : ((3 : ℝ) / ((b + c) + (a + c) + (a + b))) ≥ (3 / 2),
    from by {apply div_le_div_of_le_of_pos,ring,},
  show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from by {
    apply le_trans,
    apply h1,
    apply le_trans,
    apply h3,
    apply le_trans,
    apply h4,
    apply h5,
  }
end

--OUTPUT 7
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  -- $\dfrac a {b + c} + \dfrac b {a + c} + \dfrac c {a + b} \ge \dfrac 3 2$
  have h1 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from
    by {
      -- by adding $3$
      have h2 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)),
        from by {rw [div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv], exact add_le_add (le_div_iff_mul_le'.mp hb) (le_div_iff_mul_le'.mp hc) (le_div_iff_mul_le'.mp hc) (le_div_iff_mul_le'.mp ha) (le_div_iff_mul_le'.mp ha) (le_div_iff_mul_le'.mp hb), },
      -- as $\dfrac {a + b + c} {\paren {b + c} + \paren {a + c} + \paren {a + b} } = \dfrac 1 2$
      have h3 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) ≥ (3 / (2 * (b + c + a))),
        from by {rw [div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv], rw [← mul_assoc,← mul_assoc,← mul_assoc], rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, ring, },
      -- dividing by $3 \paren {a + b + c}$
      have h4 : (3 / (2 * (b + c + a))) ≥ (3 / ((b + c) + (a + c) + (a + b))),
        from by {rw [← div_eq_mul_inv,← div_eq_mul_inv,← div_eq_mul_inv,← div_eq_mul_inv], rw [← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc], rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, ring, exact mul_le_mul_left ha (le_div_iff_mul_le'.mp hb) (le_div_iff_mul_le'.mp hc) (le_div_iff_mul_le'.mp ha) (le_div_iff_mul_le'.mp hb) (le_div_iff_mul_le'.mp hc), },
      -- These are the arithmetic mean and the harmonic mean of $\dfrac 1 {b + c}$, $\dfrac 1 {a + c}$ and $\dfrac 1 {a + b}$.
      -- From Arithmetic Mean is Never Less than Harmonic Mean the last inequality is true.
      -- Thus Nesbitt's Inequality holds.
      exact arithmetic_mean_never_less_harmonic_mean h2 h4,
    },
  -- $\dfrac a {b + c} + \dfrac b {a + c} + \dfrac c {a + b} \ge \dfrac 3 2$
  show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from h1,
end

--OUTPUT 8
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have habc : 0 < a + b + c, from by {apply add_pos ha, apply add_pos hb, apply add_pos hc},
  calc (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) :
  begin
    rw [← add_div_right ha, ← add_div_right hb, ← add_div_right hc],
    ring
  end
  ... ≥ (9 * (a + b + c)) / (2 * (b + c) + 2 * (a + c) + 2 * (a + b)) :
  begin
    apply div_le_div_of_le_of_pos (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (le_of_lt habc) (le_of_lt (add_pos hb hc)))
      (mul_le_mul_of_nonneg_left (le_of_lt habc) (le_of_lt (add_pos ha hc))))
      (mul_le_mul_of_nonneg_left (le_of_lt habc) (le_of_lt (add_pos ha hb)))),
    show (2 * (b + c) + 2 * (a + c) + 2 * (a + b)) > 0, from by {apply add_pos, apply add_pos, apply add_pos},
    rw [← mul_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc],
    rw [← mul_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc],
    apply add_le_add (add_le_add (mul_le_mul_of_nonneg_left (le_of_lt habc) (le_of_lt (add_pos hb hc)))
      (mul_le_mul_of_nonneg_left (le_of_lt habc) (le_of_lt (add_pos ha hc))))
      (mul_le_mul_of_nonneg_left (le_of_lt habc) (le_of_lt (add_pos ha hb))),
  end
  ... ≥ (3 * ((1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)))) / (b + c + a + c + a + b) :
  begin
    apply div_le_div_of_le_of_pos (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (le_of_lt (add_pos hb hc)) (le_of_lt (add_pos ha hc)))
      (mul_le_mul_of_nonneg_left (le_of_lt (add_pos ha hc)) (le_of_lt (add_pos ha hb))))
      (mul_le_mul_of_nonneg_left (le_of_lt (add_pos ha hb)) (le_of_lt (add_pos hb hc)))),
    show (b + c + a + c + a + b) > 0, from by {apply add_pos, apply add_pos, apply add_pos},
    rw [← mul_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc],
    rw [← mul_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc],
    apply add_le_add (add_le_add (mul_le_mul_of_nonneg_left (le_of_lt (add_pos hb hc)) (le_of_lt (add_pos ha hc)))
      (mul_le_mul_of_nonneg_left (le_of_lt (add_pos ha hc)) (le_of_lt (add_pos ha hb))))
      (mul_le_mul_of_nonneg_left (le_of_lt (add_pos ha hb)) (le_of_lt (add_pos hb hc))),
  end
  ... = 3 * ((1 / (b + c)) + (1 / (a + c)) + (1 / (a + b))) : by rw [← add_div_right ha, ← add_div_right hb, ← add_div_right hc]
  ... ≥ 3 * (2 / 3) : by apply arithmetic_mean_is_never_less_than_harmonic_mean
  ... = 3 : by rw [← mul_assoc, mul_comm 3 2, ← mul_assoc, mul_comm 3 2, mul_assoc],
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
Nesbitt's inequality
Let $a$, $b$ and $c$ be positive real numbers.

Then:
:$\dfrac a {b + c} + \dfrac b {a + c} + \dfrac c {a + b} \ge \dfrac 3 2$

`proof`
{{begin-eqn}}
{{eqn | l = \frac a {b + c} + \frac b {a + c} + \frac c {a + b}
      | o = \ge
      | r = \dfrac 3 2
}}
{{eqn | ll= \leadstoandfrom
      | l = \frac {a + b + c} {b + c} + \frac {a + b + c} {a + c} + \frac {a + b + c} {a + b}
      | o = \ge
      | r = \frac 9 2
      | c = by adding $3$
}}
{{eqn | ll= \leadstoandfrom
      | l = \frac {a + b + c} {b + c} + \frac {a + b + c} {a + c} + \frac {a + b + c} {a + b}
      | o = \ge
      | r = \frac {9 \paren {a + b + c} } {\paren {b + c} + \paren {a + c} + \paren {a + b} }
      | c = as $\dfrac {a + b + c} {\paren {b + c} + \paren {a + c} + \paren {a + b} } = \dfrac 1 2$
}}
{{eqn | ll= \leadstoandfrom
      | l = \frac {\frac 1 {b + c} + \frac 1 {a + c} + \frac 1 {a + b} } 3
      | o = \ge
      | r = \frac 3 {\paren {b + c} + \paren {a + c} + \paren {a + b} }
      | c = dividing by $3 \paren {a + b + c}$
}}
{{end-eqn}}
These are the arithmetic mean and the harmonic mean of $\dfrac 1 {b + c}$, $\dfrac 1 {a + c}$ and $\dfrac 1 {a + b}$.

From Arithmetic Mean is Never Less than Harmonic Mean the last inequality is true.

Thus Nesbitt's Inequality holds.
{{qed}}

-/
theorem  nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
FEW SHOT PROMPTS TO CODEX(END)-/
