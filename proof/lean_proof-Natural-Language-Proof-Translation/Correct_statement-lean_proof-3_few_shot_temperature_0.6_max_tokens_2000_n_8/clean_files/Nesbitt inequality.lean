import data.real.basic


--OUTPUT 1
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ (9 / 2), from
    by {rw [add_mul,add_mul,add_mul], rw ← add_assoc, rw mul_assoc, rw mul_comm _ 3, ring, },
  have h2 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ (9 / (2 * (a + b + c))), from
    by {rw mul_assoc, rw div_mul_cancel, rw add_left_cancel, rw add_left_cancel, rw add_left_cancel, rw mul_comm _ 2, ring,},
  have h3 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) ≥ (3 / ((b + c) + (a + c) + (a + b))), from
    by {rw [div_mul,div_mul,div_mul], rw mul_comm _ 3, rw mul_assoc, rw div_mul_cancel, rw add_left_cancel, rw mul_comm _ 2, ring,},
  have h4 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) ≥ (3 / (2 * (a + b + c))), from
    by {rw mul_assoc, rw div_mul_cancel, rw add_left_cancel, rw add_left_cancel, rw add_left_cancel, rw mul_comm _ 2, ring,},
  have h5 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) ≥ (3 / 2), from
    by {rw mul_comm _ 2, rw mul_assoc, rw div_mul_cancel, rw add_left_cancel, rw add_left_cancel, rw add_left_cancel, ring,},
  have h6 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from
    by {rw [div_mul,div_mul,div_mul], rw add_mul, rw add_mul, rw add_mul, rw mul_comm _ 2, rw mul_comm _ 3, ring,},
  show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from
    by {rw [div_mul,div_mul,div_mul], rw add_mul, rw add_mul, rw add_mul, rw mul_comm _ 2, rw mul_comm _ 3, ring,},
end

--OUTPUT 2
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) ≥ (3 / (a + b + c)), from by {
    rw [one_mul,mul_comm 3 (a+b+c),mul_assoc,mul_comm (3/2) (a+b+c),div_eq_mul_inv,add_mul],
    apply arithmetic_mean_never_less_than_harmonic_mean (a + b + c) (b + c) (a + c) (a + b),
    simp,
    have h2 : 0 < a + b + c, from add_pos ha (add_pos hb hc),
    have h3 : 0 < b + c, from add_pos hb hc,
    have h4 : 0 < a + c, from add_pos ha hc,
    have h5 : 0 < a + b, from add_pos ha hb,
    exact ⟨h2,h3,h4,h5⟩,
  },
  rw [mul_comm 3 (a + b + c),mul_assoc,mul_comm (3 / 2) (a + b + c),div_eq_mul_inv,add_mul],
  exact h1,
end

--OUTPUT 3
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ (9 / 2), from by {
    rw [div_add_div_same,div_add_div_same,div_add_div_same],
    have h1 : (b + c) + (a + c) + (a + b) > 0, from by {repeat {rw lt_add_iff_pos_right},exact ⟨hb,hc⟩},
    have h2 : (b + c) * (a + c) * (a + b) > 0, from by {rw mul_pos h1,apply lt_add_iff_pos_right.mpr,exact ⟨hb,hc⟩},
    have h3 : (a + b + c)^2 > 0, from by {rw ← sq,exact sq_pos (a + b + c)},
    have h4 : (a + b + c)^2 * (b + c) * (a + c) * (a + b) > 0, from by {apply mul_pos h3,exact h2},
    have h5 : (a + b + c)^2 * (b + c) * (a + c) * (a + b) = (a + b + c) * ((a + b + c) * (b + c) * (a + c) * (a + b)), from by rw mul_left_comm (a + b + c),
    have h6 : (a + b + c) * ((a + b + c) * (b + c) * (a + c) * (a + b)) > 0, from by {rw ← h5,exact h4},
    have h7 : ((a + b + c) * (b + c) * (a + c) * (a + b)) > 0, from by {rw mul_left_comm (a + b + c),exact h6},
    have h8 : (b + c) * (a + c) * (a + b) > 0, from by {rw ← mul_left_comm (a + b + c),exact h7},
    have h9 : (b + c) * (a + c) * (a + b) = (b + c) * (a + c) * (a + b) * 1, from by rw mul_one,
    have h10 : (b + c) * (a + c) * (a + b) * 1 > 0, from by {rw ← h9,exact h8},
    have h11 : (b + c) * (a + c) * (a + b) * 1 = ((b + c) * (a + c) * (a + b)) * 1, from by rw mul_left_comm ((b + c) * (a + c) * (a + b)),
    have h12 : ((b + c) * (a + c) * (a + b)) * 1 > 0, from by {rw ← h11,exact h10},
    have h13 : ((b + c) * (a + c) * (a + b)) * 1 = ((b + c) * (a + c) * (a + b)) * (1 * 1), from by rw mul_left_comm ((b + c) * (a + c) * (a + b)),
    have h14 : ((b + c) * (a + c) * (a + b)) * (1 * 1) > 0, from by {rw ← h13,exact h12},
    have h15 : ((b + c) * (a + c) * (a + b)) * (1 * 1) = (((b + c) * (a + c) * (a + b)) * 1) * 1, from by rw mul_left_comm (((b + c) * (a + c) * (a + b)) * 1),
    have h16 : (((b + c) * (a + c) * (a + b)) * 1) * 1 > 0, from by {rw ← h15,exact h14},
    have h17 : (((b + c) * (a + c) * (a + b)) * 1) * 1 = (((b + c) * (a + c) * (a + b)) * 1) * (1 * 1), from by rw mul_left_comm (((b + c) * (a + c) * (a + b)) * 1),
    have h18 : (((b + c) * (a + c) * (a + b)) * 1) * (1 * 1) > 0, from by {rw ← h17,exact h16},
    have h19 : (((b + c) * (a + c) * (a + b)) * 1) * (1 * 1) = (((b + c) * (a + c) * (a + b)) * 1) * ((1 * 1) * 1), from by rw mul_left_comm (((b + c) * (a + c) * (a + b)) * 1),
    have h20 : (((b + c) * (a + c) * (a + b)) * 1) * ((1 * 1) * 1) > 0, from by {rw ← h19,exact h18},
    have h21 : (((b + c) * (a + c) * (a + b)) * 1) * ((1 * 1) * 1) = ((((b + c) * (a + c) * (a + b)) * 1) * (1 * 1)) * 1, from by rw mul_left_comm ((((b + c) * (a + c) * (a + b)) * 1) * (1 * 1)),
    have h22 : ((((b + c) * (a + c) * (a + b)) * 1) * (1 * 1)) * 1 > 0, from by {rw ← h21,exact h20},
    have h23 : ((((b + c) * (a + c) * (a + b)) * 1) * (1 * 1)) * 1 = (((b + c) * (a + c) * (a + b) * 1) * 1) * 1, from by rw mul_left_comm (((b + c) * (a + c) * (a + b) * 1) * 1),
    have h24 : (((b + c) * (a + c) * (a + b) * 1) * 1) * 1 > 0, from by {rw ← h23,exact h22},
    have h25 : (((b + c) * (a + c) * (a + b) * 1) * 1) * 1 = ((b + c) * (a + c) * (a + b) * 1) * (1 * 1), from by rw mul_left_comm ((b + c) * (a + c) * (a + b) * 1),
    have h26 : ((b + c) * (a + c) * (a + b) * 1) * (1 * 1) > 0, from by {rw ← h25,exact h24},
    have h27 : ((b + c) * (a + c) * (a + b) * 1) * (1 * 1) = ((b + c) * (a + c) * (a + b) * 1) * ((1 * 1) * 1), from by rw mul_left_comm ((b + c) * (a + c) * (a + b) * 1),
    have h28 : ((b + c) * (a + c) * (a + b) * 1) * ((1 * 1) * 1) > 0, from by {rw ← h27,exact h26},
    have h29 : ((b + c) * (a + c) * (a + b) * 1) * ((1 * 1) * 1) = (((b + c) * (a + c) * (a + b)) * 1) * ((1 * 1) * 1), from by rw mul_left_comm (((b + c) * (a + c) * (a + b)) * 1),
    have h30 : (((b + c) * (a + c) * (a + b)) * 1) * ((1 * 1) * 1) > 0,
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : a + b + c > 0, from by {apply add_pos,exact ha,exact hb,exact hc,},
  have h2 : (a + b + c) / 3 = 1 / 2, from by {
    have h3 : 3 * ((a + b + c) / 3) = a + b + c, from by {rw div_mul,ring},
    have h4 : ((a + b + c) / 3) * 3 = a + b + c, from by {rw mul_comm,apply h3},
    have h5 : ((a + b + c) / 3) * 6 = 2 * (a + b + c), from by {rw h4,rw mul_comm,rw mul_assoc,ring},
    have h6 : 6 * ((a + b + c) / 3) = 2 * (a + b + c), from by {rw mul_comm,apply h5},
    have h7 : ((a + b + c) / 3) * 2 = (a + b + c) * 2, from by {rw ← h6,rw div_mul,ring},
    have h8 : 2 * ((a + b + c) / 3) = (a + b + c) * 2, from by {rw mul_comm,apply h7},
    have h9 : ((a + b + c) / 3) * 2 = (a + b + c) * 2, from by {rw ← h8,rw mul_assoc,ring},
    have h10 : ((a + b + c) / 3) * 2 = 2 * (a + b + c), from by {rw ← h9,rw mul_comm,rw mul_assoc,ring},
    have h11 : 2 * ((a + b + c) / 3) = 2 * (a + b + c), from by {rw ← h10,rw mul_comm,rw mul_assoc,ring},
    have h12 : ((a + b + c) / 3) = (a + b + c) / 2, from by {rw ← h11,rw div_mul,ring},
    have h13 : ((a + b + c) / 3) = (a + b + c) / 2, from by {rw mul_comm,apply h12},
    have h14 : ((a + b + c) / 3) = (a + b + c) / 2, from by {rw mul_assoc,apply h13},
    have h15 : ((a + b + c) / 3) = (a + b + c) / 2, from by {rw mul_comm,apply h14},
    have h16 : ((a + b + c) / 3) = (a + b + c) / 2, from by {rw mul_assoc,apply h15},
    have h17 : ((a + b + c) / 3) = (a + b + c) / 2, from by {rw mul_comm,apply h16},
    have h18 : ((a + b + c) / 3) = (a + b + c) / 2, from by {rw mul_assoc,apply h17},
    have h19 : ((a + b + c) / 3) = (a + b + c) / 2, from by {rw mul_comm,apply h18},
    have h20 : ((a + b + c) / 3) = (a + b + c) / 2, from by {rw mul_assoc,apply h19},
    rw ← h20,rw mul_comm,rw mul_assoc,ring,
  },
  have h3 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ 9 / 2, from by {
    rw ← add_assoc,rw ← add_assoc,rw ← add_assoc,
    have h4 : (b + c) * (a / (b + c)) = a, from by {rw mul_comm,rw div_mul,ring},
    have h5 : (a + c) * (b / (a + c)) = b, from by {rw mul_comm,rw div_mul,ring},
    have h6 : (a + b) * (c / (a + b)) = c, from by {rw mul_comm,rw div_mul,ring},
    have h7 : (b + c) + (a + c) + (a + b) = 3 * (a + b + c), from by {ring},
    have h8 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) =
      ((a + b + c) / (b + c)) + ((a + b + c) / (a + c)) + ((a + b + c) / (a + b)), from by {
        rw h4,rw h5,rw h6,ring,
      },
    rw h8,rw h2,rw mul_comm,rw mul_assoc,ring,
  },
  have h4 : 9 / 2 ≥ 3 / 2, from by {rw mul_comm,rw mul_assoc,ring},
  show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ 3 / 2, from by {apply le_of_lt h3,exact h4},
end

--OUTPUT 5
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) / ((b + c) + (a + c) + (a + b)) = (1 / 2), from (add_div_add_div_add_div a b c).symm,
  have h2 : (3 * (a + b + c)) / (3 * ((b + c) + (a + c) + (a + b))) = (1 / 2), from by rw [← mul_div_assoc, ← h1, mul_comm 3 (a + b + c), mul_comm 3 ((b + c) + (a + c) + (a + b))],
  have h3 : (3 * (a + b + c)) / (3 * ((b + c) + (a + c) + (a + b))) ≥ (3 / ((b + c) + (a + c) + (a + b))), from
    mul_div_ge_div_mul_of_nonneg (le_of_lt (add_three_pos ha hb hc)) h2 (add_three_pos ha hb hc) (by norm_num),
  have h4 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 * (a + b + c)) / (3 * ((b + c) + (a + c) + (a + b))), from
    add_div_add_div_add_div a b c,
  have h5 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / ((b + c) + (a + c) + (a + b))), from
    le_trans h4 h3,
  show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from le_trans h5 (by norm_num),
end

--OUTPUT 6
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have habc : 0 < (a + b + c), from by {apply lt_add_of_pos_of_pos ha hb, apply lt_add_of_pos_of_pos ha hc, apply lt_add_of_pos_of_pos hb hc,},
  have hab : 0 < (a + b), from by {apply lt_add_of_pos_of_pos ha hb,},
  have hac : 0 < (a + c), from by {apply lt_add_of_pos_of_pos ha hc,},
  have hbc : 0 < (b + c), from by {apply lt_add_of_pos_of_pos hb hc,},

  calc (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + 3 : by rw add_zero
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (a + b + c) / (a + b + c) : by rw div_self habc
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (1 / (a + b + c)) * (a + b + c) : by rw div_mul_cancel habc
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + ((1 / (b + c)) * (b + c) + (1 / (a + c)) * (a + c) + (1 / (a + b)) * (a + b)) : by rw mul_assoc
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + ((1 / (b + c)) * b + (1 / (b + c)) * c + (1 / (a + c)) * a + (1 / (a + c)) * c + (1 / (a + b)) * a + (1 / (a + b)) * b) : by ring
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (b / (b + c) + c / (b + c) + a / (a + c) + c / (a + c) + a / (a + b) + b / (a + b)) : by rw [div_mul_cancel hbc,div_mul_cancel hac,div_mul_cancel hab]
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (b / (b + c) + c / (b + c) + a / (a + c) + c / (a + c) + a / (a + b) + b / (a + b)) + 1 : by rw add_zero
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (b / (b + c) + c / (b + c) + a / (a + c) + c / (a + c) + a / (a + b) + b / (a + b)) + (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) : by rw add_comm
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (b / (b + c) + c / (b + c) + a / (a + c) + c / (a + c) + a / (a + b) + b / (a + b)) + ((1 / (b + c)) * (b + c) + (1 / (a + c)) * (a + c) + (1 / (a + b)) * (a + b)) : by rw [div_mul_cancel hbc,div_mul_cancel hac,div_mul_cancel hab]
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (b / (b + c) + c / (b + c) + a / (a + c) + c / (a + c) + a / (a + b) + b / (a + b)) + ((1 / (b + c)) * b + (1 / (b + c)) * c + (1 / (a + c)) * a + (1 / (a + c)) * c + (1 / (a + b)) * a + (1 / (a + b)) * b) : by ring
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (b / (b + c) + c / (b + c) + a / (a + c) + c / (a + c) + a / (a + b) + b / (a + b)) + (b / (b + c) + c / (b + c) + a / (a + c) + c / (a + c) + a / (a + b) + b / (a + b)) : by ring
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (a / (a + c) + b / (a + c) + c / (a + c) + a / (a + b) + b / (a + b) + c / (a + b)) : by {rw add_comm, rw add_assoc,}
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (a / (a + c) + b / (a + c) + a / (a + b) + b / (a + b) + c / (a + c) + c / (a + b)) : by rw add_comm
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (a / (a + c) + a / (a + b) + b / (a + c) + b / (a + b) + c / (a + c) + c / (a + b)) : by rw add_comm
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (a / (a + b) + b / (a + b) + a / (a + c) + b / (a + c) + c / (a + b) + c / (a + c)) : by rw add_comm
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (a / (a + b) + b / (a + b) + c / (a + b) + a / (a + c) + b / (a + c) + c / (a + c)) : by rw add_comm
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (a / (a + b) + b / (a + b) + c / (a + b)) + (a / (a + c) + b / (a + c) + c / (a + c)) : by rw add_assoc
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (a / (a + c) + b / (a + c) + c / (a + c)) + (a / (a + b) + b / (a + b) + c / (a + b)) : by rw add_comm
  ... = (a / (b + c)) + (b / (a + c)) + (c / (a + b)) + (a / (a + c) + b / (a + c) + c / (a + c)) + (a / (a + b)) + (b / (a + b)) + (c / (a + b)) : by rw add_assoc
  ...
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) > 0, from by {linarith,},
  have h2 : (a + b + c) / 2 = (3/2) * (a + b + c), from by {repeat {rw ← mul_one}, rw mul_comm, ring},
  have h3 : (a + b + c) / (b + c) = (a + b + c) * (2 / (b + c)), from by {rw ← mul_one, rw mul_comm, ring},
  have h4 : (a + b + c) / (a + c) = (a + b + c) * (2 / (a + c)), from by {rw ← mul_one, rw mul_comm, ring},
  have h5 : (a + b + c) / (a + b) = (a + b + c) * (2 / (a + b)), from by {rw ← mul_one, rw mul_comm, ring},
  have h6 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) / 3, from by {
    rw [← add_mul,← add_mul,← add_mul,← add_mul,← add_mul,← add_mul,← add_mul], ring,
  },
  have h7 : (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) / 3 = (a + b + c) * (2 / (b + c) + 2 / (a + c) + 2 / (a + b)) / 6, from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← mul_add}, ring,
  },
  have h8 : (a + b + c) * (2 / (b + c) + 2 / (a + c) + 2 / (a + b)) / 6 = (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) / 2, from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← mul_add}, ring,
  },
  have h9 : (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) / 2 = (a + b + c) / 2 * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)), from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← div_mul}, ring,
  },
  have h10 : (a + b + c) / 2 * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) = (3 / 2) * (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)), from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← mul_add}, ring,
  },
  have h11 : (3 / 2) * (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) = (3 / 2) * ((a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b)), from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← mul_add}, ring,
  },
  have h12 : (3 / 2) * ((a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b)) = (3 / 2) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)), from by {
    rw ← mul_one, rw ← mul_one, rw ← div_mul, rw ← div_mul, rw ← div_mul, rw ← div_mul, rw ← div_mul, rw ← div_mul, rw ← div_mul, repeat {rw ← mul_add}, ring,
  },
  have h13 : (3 / 2) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) = (3 / 2) * (2 / (b + c) + 2 / (a + c) + 2 / (a + b)) / 6, from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← mul_add}, ring,
  },
  have h14 : (3 / 2) * (2 / (b + c) + 2 / (a + c) + 2 / (a + b)) / 6 = (3 / 2) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) / 3, from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← mul_add}, ring,
  },
  have h15 : (3 / 2) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) / 3 = (3 / 2) / ((b + c) + (a + c) + (a + b)), from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← div_mul}, ring,
  },
  have h16 : (3 / 2) / ((b + c) + (a + c) + (a + b)) = (a + b + c) / ((b + c) + (a + c) + (a + b)) * (3 / 2), from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← div_mul, rw ← div_mul, ring,
  },
  have h17 : (a + b + c) / ((b + c) + (a + c) + (a + b)) * (3 / 2) = (a + b + c) / 2 * (3 / 2), from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← div_mul}, ring,
  },
  have h18 : (a + b + c) / 2 * (3 / 2) = (3 / 2) * (a + b + c) / 2, from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← mul_add}, ring,
  },
  have h19 : (3 / 2) * (a + b + c) / 2 = (3 / 2) * (a + b + c), from by {
    rw ← mul_one, rw ← mul_one, rw ← mul_one, rw ← mul_one, repeat {rw ← mul_add}, ring,
  },
  have h20 : (3 / 2) * (a
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) > 0, from by linarith,
  have h2 : (a + b + c) / 2 = 1 / 2 * (a + b + c), from by rw div_mul_cancel h1,
  have h3 : (a + b + c) / 2 = 1 / 2 * ((a + b + c) + (a + b + c)), from by ring,
  have h4 : (a + b + c) / 2 = ((a + b + c) / 2) + ((a + b + c) / 2), from by rw ← h3,
  have h5 : (a + b + c) / 2 = ((a + b + c) / 2) + (1 / 2 * (a + b + c)), from by rw h2,
  have h6 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + ((a + b + c) / 2), from by rw add_comm ((a + b + c) / 2) (1 / 2 * (a + b + c)),
  have h7 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)), from by rw ← h3,
  have h8 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + ((a + b + c) / 2), from by rw ← h4,
  have h9 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)), from by rw h2,
  have h10 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + ((a + b + c) / 2), from by rw ← h5,
  have h11 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)), from by rw h2,
  have h12 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + ((a + b + c) / 2), from by rw ← h7,
  have h13 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)), from by rw h2,
  have h14 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + ((a + b + c) / 2), from by rw ← h9,
  have h15 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)), from by rw h2,
  have h16 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + ((a + b + c) / 2), from by rw ← h11,
  have h17 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)), from by rw h2,
  have h18 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + ((a + b + c) / 2), from by rw ← h13,
  have h19 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)), from by rw h2,
  have h20 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + ((a + b + c) / 2), from by rw ← h15,
  have h21 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)), from by rw h2,
  have h22 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + ((a + b + c) / 2), from by rw ← h17,
  have h23 : (a + b + c) / 2 = (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (1 / 2 * (a + b + c)) + (
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
