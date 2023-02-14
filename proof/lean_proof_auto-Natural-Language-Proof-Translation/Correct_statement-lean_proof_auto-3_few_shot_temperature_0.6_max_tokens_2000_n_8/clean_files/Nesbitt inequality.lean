import data.real.basic


--OUTPUT 1
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ 9 / 2, from by auto [div_eq_mul_inv, add_div],
  have h2 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ (9 / 2) * ((a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b)), from by auto [div_le_div_of_mul_le, lt_of_lt_of_le (ha + hb + hc) (by auto [add_pos]), mul_le_mul_of_nonneg_right (by auto [add_nonneg, add_nonneg, add_nonneg, add_nonneg, add_nonneg, add_nonneg, add_nonneg]), mul_self_nonneg, mul_self_nonneg, mul_self_nonneg, mul_self_nonneg, mul_self_nonneg, mul_self_nonneg, mul_self_nonneg, mul_self_nonneg, mul_self_nonneg],
  have h3 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ (1 / 2) * ((a + b + c) / (b + c) + (a + b + c) + (a + b + c) / (a + b)), from by auto [mul_le_mul_of_nonneg_left (by auto [half_pos]), h2],
  have h4 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ (1 / 2) * ((a + b + c) + (a + b + c) + (a + b + c)), from by auto [mul_le_mul_of_nonneg_right (by auto [add_pos]), h3],
  have h5 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ ((1 / 2) * (a + b + c) + (1 / 2) * (a + b + c) + (1 / 2) * (a + b + c)), from by auto [mul_le_mul_of_nonneg_left (by auto [half_pos]), h4],
  have h6 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ ((1 / 2) * (a + b + c) + (1 / 2) * (a + b + c) + (1 / 2) * (a + b + c)) / (b + c + a + b), from by auto [mul_le_mul_of_nonneg_right, add_pos, add_pos, add_pos, h5],
  have h7 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ ((1 / 2) * (a + b + c) + (1 / 2) * (a + b + c) + (1 / 2) * (a + b + c)) / (b + c + a + b), from by auto [add_le_add_iff_left, add_le_add_iff_left, h6],
  have h8 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ ((1 / 2) * (a + b + c) + (1 / 2) * (a + b + c) + (1 / 2) * (a + b + c)) / (b + c + a + b), from by auto [add_le_add_iff_right, h7],
  show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from by auto [div_eq_mul_inv, add_div, h8],
end

--OUTPUT 2
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : 0 < (b + c) + (a + c) + (a + b), from by auto [add_pos],
  have h2 : 0 < (b + c) + (a + c) + (a + b) / 3, from by auto [add_pos, div_pos],
  have h3 : (a + b + c) / ((b + c) + (a + c) + (a + b) / 3) = 1 / 2, from by auto [div_eq_iff],

  calc (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (a + b + c) / ((b + c) + (a + c) + (a + b)) : by auto [mul_div_mul_left, div_add_div_left, div_add_div_left, div_add_div_left, add_pos, add_pos, add_pos, h1, h2, h3]
  ... ≥ (a + b + c) / ((b + c) + (a + c) + (a + b) / 3) : by auto [div_le_div_right, h1, h2, add_pos, add_pos, add_pos]
  ... = 1 / 2 : by auto [h3]
  ... = 3 / 6 : by auto [div_eq_iff, mul_comm]
  ... = 3 / 2 : by auto [div_eq_iff, mul_comm]
end

--OUTPUT 3
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ (9 / 2), from by auto [div_add_div_same, div_add_div_same, add_mul_div_left, add_mul_div_left, add_mul_div_left, mul_self_inj, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add_halves, add
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : a + b + c > 0, from by auto [add_pos, ha, hb, hc],
  have h2 : (a + b + c) / 3 = (1 / 2) * (a + b + c), from by auto [mul_div_cancel, three],
  have h3 : (a + b + c) / (b + c) = (1 / 2) * (a + b + c), from by auto [mul_div_cancel, two],
  have h4 : (a + b + c) / (a + c) = (1 / 2) * (a + b + c), from by auto [mul_div_cancel, two],
  have h5 : (a + b + c) / (a + b) = (1 / 2) * (a + b + c), from by auto [mul_div_cancel, two],
  have h6 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) > 0, from by auto [add_pos, one_div_pos, ha, hb, hc],
  have h7 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) = (b + c) + (a + c) + (a + b) / ((b + c) * (a + c) * (a + b)), from by auto [one_div_mul, mul_comm, mul_add],
  have h8 : (3 / 2) * (b + c) * (a + c) * (a + b) = (3 / 2) * ((b + c) + (a + c) + (a + b)), from by auto [mul_div_cancel, two, mul_comm, mul_add],
  have h9 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) ≥ (3 / 2) / ((b + c) + (a + c) + (a + b)), from by auto [arithmetic_mean_never_less_than_harmonic_mean, h6],
  calc (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) : by auto [h3, h4, h5]
  ... = 1 / 2 * (a + b + c) + 1 / 2 * (a + b + c) + 1 / 2 * (a + b + c) : by auto [add_mul, h3, h4, h5]
  ... = (1 / 2) * (3 * (a + b + c)) : by auto [mul_add, three, mul_comm, mul_assoc]
  ... = (1 / 2) * (3 / 3) * (a + b + c) : by auto [mul_div_cancel, three]
  ... = (1 / 2) * (1 / 2) * (a + b + c) : by auto [mul_div_cancel, two]
  ... = (1 / 2) * (a + b + c) / 2 : by auto [mul_div_cancel, two]
  ... = (1 / 2) * ((a + b + c) / 3) : by auto [mul_div_cancel, two]
  ... = (1 / 2) * (1 / 2) * (a + b + c) : by auto [h2]
  ... = (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) : by auto [one_div_mul, mul_comm, mul_add]
  ... ≥ (3 / 2) / ((b + c) + (a + c) + (a + b)) : by auto [h9]
  ... = (3 / 2) * ((b + c) + (a + c) + (a + b)) / ((b + c) * (a + c) * (a + b)) : by auto [div_mul_cancel, h6]
  ... = (3 / 2) * (b + c) * (a + c) * (a + b) / ((b + c) * (a + c) * (a + b)) : by auto [mul_comm, mul_add]
  ... = (3 / 2) : by auto [h8],
end

--OUTPUT 5
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : 0 < b + c, from by exact add_pos hb hc,
  have h2 : 0 < a + c, from by exact add_pos ha hc,
  have h3 : 0 < a + b, from by exact add_pos ha hb,
  have h4 : 0 < (b + c) + (a + c) + (a + b), from by exact add_pos h1 h2 h3,
  have h5 : 0 < 3, from by exact is_pos_three,
  have h6 : 0 < (b + c) + (a + c) + (a + b), from by exact add_pos h1 h2 h3,
  have h7 : 0 < (a + b + c), from by exact add_pos ha hb hc,

  have h8 : (a + b + c) / (b + c) = (a + b + c) * ((b + c)⁻¹), from by auto [div],
  have h9 : (a + b + c) / (a + c) = (a + b + c) * ((a + c)⁻¹), from by auto [div],
  have h10 : (a + b + c) / (a + b) = (a + b + c) * ((a + b)⁻¹), from by auto [div],

  have h11 : (a + b + c) / (b + c) = (a + b + c) * (1 / (b + c)), from by auto [one_div],
  have h12 : (a + b + c) / (a + c) = (a + b + c) * (1 / (a + c)), from by auto [one_div],
  have h13 : (a + b + c) / (a + b) = (a + b + c) * (1 / (a + b)), from by auto [one_div],

  have h14 : (a + b + c) / (b + c) = a + b + c - (a / (b + c)) + (b / (b + c)), from by auto [add_div, add_comm, add_mul, add_comm (a + b + c) (a / (b + c))],
  have h15 : (a + b + c) / (a + c) = a + b + c - (a / (a + c)) + (c / (a + c)), from by auto [add_div, add_comm, add_mul, add_comm (a + b + c) (a / (a + c))],
  have h16 : (a + b + c) / (a + b) = a + b + c - (c / (a + b)) + (b / (a + b)), from by auto [add_div, add_comm, add_mul, add_comm (a + b + c) (c / (a + b))],

  have h17 : (a + b + c) / (b + c) = a + b + c + (-a / (b + c)) + (b / (b + c)), from by auto [neg_div, add_mul, add_comm (a + b + c) (-a / (b + c))],
  have h18 : (a + b + c) / (a + c) = a + b + c + (-a / (a + c)) + (c / (a + c)), from by auto [neg_div, add_mul, add_comm (a + b + c) (-a / (a + c))],
  have h19 : (a + b + c) / (a + b) = a + b + c + (-c / (a + b)) + (b / (a + b)), from by auto [neg_div, add_mul, add_comm (a + b + c) (-c / (a + b))],

  have h20 : (a + b + c) / (b + c) = a + b + c + (-a / (b + c)) + b * (1 / (b + c)), from by auto [h17, h11],
  have h21 : (a + b + c) / (a + c) = a + b + c + (-a / (a + c)) + c * (1 / (a + c)), from by auto [h18, h12],
  have h22 : (a + b + c) / (a + b) = a + b + c + (-c / (a + b)) + b * (1 / (a + b)), from by auto [h19, h13],

  have h23 : (a + b + c) / (b + c) = a + b + c + (1 / (b + c)) + b * (1 / (b + c)), from by auto [h20, neg_div, add_mul],
  have h24 : (a + b + c) / (a + c) = a + b + c + (1 / (a + c)) + c * (1 / (a + c)), from by auto [h21, neg_div, add_mul],
  have h25 : (a + b + c) / (a + b) = a + b + c + (1 / (a + b)) + b * (1 / (a + b)), from by auto [h22, neg_div, add_mul],

  have h26 : (a + b + c) / (b + c) = a + b + c + (1 / (b + c)) + (b / (b + c)), from by auto [h23, mul_one],
  have h27 : (a + b + c) / (a + c) = a + b + c + (1 / (a + c)) + (c / (a + c)), from by auto [h24, mul_one],
  have h28 : (a + b + c) / (a + b) = a + b + c + (1 / (a + b)) + (b / (a + b)), from by auto [h25, mul_one],

  have h29 : (a + b + c) / (b + c) = a + b + c + (1 / (b + c)) + (b / (b + c)) + (-a / (b + c)), from by auto [h26, add_comm],
  have h30 : (a + b + c) / (a + c) = a + b + c + (1 / (a + c)) + (c / (a + c)) + (-a / (a + c)), from by auto [h27, add_comm],
  have h31 : (a + b + c) / (a + b) = a + b + c + (1 / (a + b)) + (b / (a + b)) + (-c / (a + b)), from by auto [h28, add_comm],

  have h32 : (a + b + c) / (b + c) = a + b + c + (1 / (b + c)) - (a / (b + c)) + (b / (b + c)), from by auto [h29, add_comm (-a / (b + c))],
  have h33 : (a + b + c) / (a + c) = a + b + c + (1 / (a + c)) - (a / (a + c)) + (c / (a + c)), from by auto [h30, add_comm (-a / (a + c))],
  have h34 : (a + b + c) / (a + b) = a + b + c + (1 / (a + b)) - (c / (a + b)) + (b / (a + b)), from by auto [h31, add_comm (-c / (a + b))],

  have h35 : (a + b + c) / (b + c) = a + b + c + (1 / (b + c)) - (a / (b + c)) + (b / (b + c)) + c, from by auto [h32, add_right_inj],
  have h36 : (a + b + c) / (a + c) = a + b + c + (1 / (a + c)) - (a / (a + c)) + (c / (a + c)) + b, from by auto [h33, add_right_inj],
  have h37 : (a + b + c) / (a + b) = a + b + c + (1 / (a + b
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) := 
begin
  have h1 : a + b + c > 0, from by auto [ha, hb, hc, add_pos],
  calc (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) : by simp
  ... = (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) : by auto [add_div_cancel_left] using [h1]
  ... ≥ (9 * (a + b + c)) / ((b + c) + (a + c) + (a + b)) : by auto [div_le_div_of_le_of_pos, add_pos, div_le_div_of_le_of_pos, add_pos, div_le_div_of_le_of_pos, add_pos, le_div_iff, mul_pos] using [h1, ha, hb, hc, arithmetic_mean_is_never_less_than_harmonic_mean]
  ... = 3 / 2 : by auto [div_eq_iff_mul_eq, mul_comm, mul_assoc, mul_left_cancel, mul_div_cancel, mul_one] using [h1],
end

--OUTPUT 7
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : 0 < a + b + c, from by auto [add_pos],
  have h2 : 0 < b + c, from by auto [add_pos],
  have h3 : 0 < a + c, from by auto [add_pos],
  have h4 : 0 < a + b, from by auto [add_pos],

  calc (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) : by auto [div_add_div_same, add_assoc, add_assoc, add_assoc, add_assoc] using [field]
  ... ≥ 9 / 2 : by auto [add_pos, div_le_div_iff_le_of_pos, mul_pos] using [arithmetic_mean_harmonic_mean]
  ... ≥ 3 / 2 : by auto [div_le_div_iff_le_of_pos, div_pos] using [field]
end

--OUTPUT 8
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) / ((b + c) + (a + c) + (a + b)) = (1 / 2), from by auto [div_eq_mul_inv, add_mul, mul_comm, mul_assoc],
  have h2 : (9 / 2) * ((a + b + c) / ((b + c) + (a + c) + (a + b))) = (9 / 2) * (1 / 2), from by auto [mul_assoc, h1],
  have h3 : ((a + b + c) / (b + c)) + ((a + b + c) / (a + c)) + ((a + b + c) / (a + b)) = (9 / 2) * (1 / 2), from by auto [mul_one, add_mul, add_mul, add_mul, add_assoc, add_assoc, add_comm, add_assoc, add_comm, add_comm, add_assoc, add_comm, add_assoc, add_assoc, add_comm, add_assoc, add_assoc, mul_assoc, mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm, mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, h2, !mul_one],
  have h4 : (1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)) = (9 / 2) * (1 / 2), from by auto [h3, div_eq_mul_inv, mul_one, mul_one, mul_one, add_mul, add_mul, add_mul, add_assoc, add_assoc, add_comm, add_assoc, add_comm, add_comm, add_assoc, add_comm, add_assoc, add_assoc, add_comm, add_assoc, add_assoc, mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm, mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, !mul_one],
  have h5 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / (b + c) + (a + c) + (a + b)), from by auto [arithmetic_mean_harmonic_mean, h4],
  show (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2), from by auto [h5, div_eq_mul_inv, mul_one, mul_one, mul_one, mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm, mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, mul_comm, !mul_one],
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
