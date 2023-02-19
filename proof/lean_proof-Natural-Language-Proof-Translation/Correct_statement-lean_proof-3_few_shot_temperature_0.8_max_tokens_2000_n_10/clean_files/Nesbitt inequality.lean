import data.real.basic


--OUTPUT 1
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) := 
begin
  have h1 : a + b + c ≠ 0, from by {rw add_zero at hb,rw add_zero at hc, exfalso, exact lt_irrefl 0 (begin linarith, end)},
  have h2 : a + b ≠ 0 ∧ a + c ≠ 0 ∧ b + c ≠ 0, from by {
    have h3 : ¬ (a + b + c = 0), from h1,
    have h4 : ¬ (a + b = 0 ∧ a + c = 0 ∧ b + c = 0), from decidable.finset.le_zero_iff_eq_zero.mp h3,
    have h5 : ¬ (a + b = 0), from h4.imp (λ h6, h6.left),
    have h6 : ¬ (a + c = 0), from h4.imp (λ h7, h7.right.left),
    have h7 : ¬ (b + c = 0), from h4.imp (λ h8, h8.right.right),
    have h8 : ¬ (a + b = 0 ∧ a + c = 0), from and.rec_on h4 (λ h9 h10, h9.symm ▸ h10.symm ▸ h6),
    have h9 : ¬ (a + b = 0), from h8.imp h5,
    have h10 : ¬ (a + c = 0), from h8.imp h6,
    have h11 : ¬ (a + b = 0 ∧ b + c = 0), from and.rec_on h8 (λ h12 h13, h12.symm ▸ h13.symm ▸ h7),
    have h12 : ¬ (a + b = 0), from h11.imp h9,
    have h13 : ¬ (b + c = 0), from h11.imp h7,
    have h14 : ¬ (a + c = 0 ∧ b + c = 0), from and.rec_on h11 (λ h15 h16, h15.symm ▸ h16.symm ▸ h10),
    have h15 : ¬ (a + c = 0), from h14.imp h13,
    have h16 : ¬ (b + c = 0), from h14.imp h7,
    have h17 : ¬ (a + b = 0 ∧ a + c = 0 ∧ b + c = 0), from (λ h18, h18.symm ▸ h12),  
    show ¬ (a + b = 0), from by {assume h18, exact h17 ⟨h18,h15,h16⟩},
    show ¬ (a + c = 0), from by {assume h18, exact h17 ⟨h9,h18,h16⟩},
    show ¬ (b + c = 0), from by {assume h18, exact h17 ⟨h9,h15,h18⟩},
  },
  have h3 : (3 / 2) * (a + b + c) = (3 / 2) * a + (3 / 2) * b + (3 / 2) * c, from by rw ← mul_assoc,
  have h4 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = 
      (a / (b + c)) + (((b + c) / (a + c)) * (b / (b + c))) + 
      (c / (a + b)) + (((a + b) / (a + c)) * (c / (c + b))) + 
      (((b + c) / (a + c)) * (c / (c + b))) + (((a + c) / (a + b)) * (a / (a + c))) + 
      (((a + c) / (a + b)) * (a / (a + c))) + (((a + b) / (a + c)) * (b / (b + c))) + 
      (((a + b) / (a + c)) * (c / (c + b))) + (((a + c) / (a + b)) * (b / (b + c))) := by ring,
  have h5: 0 < a + b ∧ 0 < a + c ∧ 0 < b + c, from 
    by {split, apply lt_add_of_pos_left ha, apply lt_add_of_pos_right hb, apply lt_add_of_pos_right hc},
  have h6 : (a + b) / (b + c) = 1, from by rw [add_comm (a + b) c, sub_self, div_zero],
  have h7 : (a + c) / (b + c) = ((a + c) * (b + c)) / ((b + c) * (b + c)),
    from by rw [mul_comm (a + c) (b + c)],
  have h8 : 0 < (a + c) * (b + c), from by {rw ← (mul_two_pos h5.left h5.right), linarith},
  have h9 : ((a + c) * (b + c)) / ((b + c) * (b + c)) = 1, from by rw div_mul_cancel h8,
  have h10 : (a + b) / (a + c) = 1, from by rw [add_comm a b, sub_self, div_zero],
  have h11 : (b + c) / (a + c) = ((b + c) * (a + c)) / ((a + c) * (a + c)),
    from by rw mul_comm (b + c) (a + c),
  have h12 : 0 < (b + c) * (a + c), from by {rw ← (mul_two_pos h5.right h5.left), linarith},
  have h13 : ((b + c) * (a + c)) / ((a + c) * (a + c)) = 1, from by rw div_mul_cancel h12,
  have h14 : (a + c) / (a + b) = 1, from by rw [add_comm a c, sub_self, div_zero],
  have h15 : (b + c) / (a + b) = ((b + c) * (a + b)) / ((a + b) * (a + b)),
    from by rw mul_comm (b + c) (a + b),
  have h16 : 0 < (b + c) * (a + b), from by {rw ← (mul_two_pos h5.right h5.left), linarith},
  have h17 : ((b + c) * (a + b)) / ((a + b) * (a + b)) = 1, from by rw div_mul_cancel h16,
  have h18 : a / (a + c) = 1, from by rw [add_comm a c, sub_self, div_zero],
  have h19 : (b + c) / (a + c) = ((b + c) * (a + c)) / ((a + c) * (a + c)),
    from by rw mul_comm (b + c) (a + c),
  have h20 : 0 < (b + c) * (a + c), from by {rw ← (mul_two_pos h5.right h5.left), linarith},
  have h21 : ((b + c) * (a + c)) / ((a + c) * (a + c)) = 1, from by rw div_mul_cancel h20,
  have h22 : (a + b) / (a + c) = 1, from by rw [add_comm a b, sub_self, div_zero],
  have h23 : (b + c) / (a + c) = ((b + c) * (a + c)) / ((a + c) * (a + c)),
    from by rw mul_comm (b + c) (a + c),
  have h24 : 0 < (b + c) * (a + c), from by {rw ← (mul_two_pos h5.right h5.left), linarith
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  rw ← add_three,
  rw ← add_mul, rw ← add_mul, rw ← add_mul,
  rw ← add_halves, rw add_halves, rw add_halves,
  show (a/ (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ 3 / 2,
  apply arithmetic_harmonic_mean,
  simp,
end

--OUTPUT 3
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  calc (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) : by ring
  ... = 9 * ((a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b)) : by rw [← mul_three, mul_comm]
  ... ≥ 9 * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) / 3 : by rw [← mul_three, mul_comm, div_mul_eq_mul_div, div_self ha]
  ... = 3 / ((b + c) + (a + c) + (a + b)) : by {rw add_mul, rw div_mul_eq_mul_div, ring}
  ... ≥ 3 / (2 * (a + b + c)) : by apply harmonic_mean_le_arithmetic_mean
  ... = 3 / (2 * (a + b)) : by rw add_assoc a b c 
  ... = 3 / (2 * a) : by rw add_comm a b
  ... ≥ 3 / (2 * (a + c)) : by apply real.lt_of_add_lt_add_right hc
  ... ≥ 3 / (2 * (b + c)) : by apply real.lt_of_add_lt_add_right ha
  ... = 3 / (2 * b) : by rw add_comm b c
  ... ≥ 3 / (2 * (b + c)) : by apply real.lt_of_add_lt_add_right hc
  ... ≥ 3 / (2 * (a + c)) : by apply real.lt_of_add_lt_add_right hb
  ... = 3 / (2 * a) : by rw add_comm a c
  ... ≥ 3 / (2 * a) : by apply real.lt_of_add_lt_add_right ha
  ... = (3 / 2) : rfl,
end

--OUTPUT 4
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  calc 
  (a / (b + c)) +  (b / (a + c)) + (c / (a + b)) ≥ 
  (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) : by linarith
  ... ≥ (9 * (a + b + c)) / ((b + c) + (a + c) + (a + b)) : by linarith
  ... ≥ (3 / ((1 / (b + c)) + (1 / (a + c)) + (1 / (a + b)))) : by {
    rw [mul_comm (3:ℝ),mul_comm (a + b + c),mul_assoc,mul_assoc,mul_inv_cancel (a + b + c),mul_one],
    rw [mul_comm a,mul_assoc,mul_inv_cancel (a:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (a:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (a:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (a:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (b:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (b:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (b:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (b:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (c:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (c:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (c:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (c:ℝ),mul_one,←add_mul,←add_mul,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_add,←mul_add,←mul_add,←mul_add,←mul_add,←mul_add],
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel (9:ℝ),mul_one],
    have h1 : ((c + a) + b)⁻¹ = (c + a)⁻¹ + b⁻¹, from calc 
                ((c + a) + b)⁻¹ = ((c + a)⁻¹ + b⁻¹) : by {rw add_mul, rw ←mul_assoc, rw ←mul_assoc, rw ←mul_assoc, rw mul_inv_cancel, rw one_mul, rw [mul_comm,add_mul,mul_assoc,mul_assoc,mul_comm b,mul_assoc,mul_assoc,mul_comm]},
          rw h1,
          have h2 : b⁻¹ * (c + a)⁻¹ = (c + a)⁻¹ * b⁻¹, from mul_comm _ _,
          rw h2,
          rw add_mul,
          have h3 : (c + a) + b = a + (b + c), from calc (c + a) + b = (c * 1 + a * 1) + b : by repeat {rw mul_one}
          ... = (c + a) + b : by repeat {rw add_mul},
          rw h3,
          ring,
    rw mul_comm 3,
    have h4 : (3 : ℝ)⁻¹ = (1 : ℝ) / 3, from calc (3 : ℝ)⁻¹ = (1 : ℝ) / (1 * 3) : by rw one_mul
    ... = (1 : ℝ) / 3 : by rw mul_comm,
    rw h4,
    rw ←mul_inv_cancel,
    rw ←mul_assoc,
    rw ←mul_assoc,
    rw ←mul_assoc,
    rw mul_inv_cancel,
    rw mul_one,
    rw mul_comm 3,
    rw ←mul_assoc,
    rw ←mul_assoc,
    rw ←mul_assoc,
    rw ←mul_assoc
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ 9 / 2, from arithmetic_mean_harmonic_mean (b + c) (a + c) (a + b) 3 ha hb hc,
  have h2 :  (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ 3 / (2 * (a + b + c)), from by {rw mul_comm, show _ ≥ _, from by linarith},
  have h3 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ 3 / (2 * (a + b + c)), from by {rw [ha,hb,hc], linarith},
  have h4 : (a + b + c) > 0, from by {linarith},
  show _ ≥ _, from by {rw [mul_comm (3 / 2) (a + b + c),div_mul_cancel _ h4], exact h3},
end

--OUTPUT 6
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (3 : ℝ) / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b), from by {
    have h2 : (a : ℝ) / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b), from by {
      have h3 : ((a + b + c) : ℝ) / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b), from by {
        have h4 : ((a + b + c) : ℝ) / 2 ≥ (a : ℝ) / ((b + c) + (a + c) + (a + b)), from by {
          have h5 : 1/(b + c) + 1/(a + c) + 1/(a + b) ≥ 3 * (1/(b + c) + 1/(a + c) + 1/(a + b)) / ((b + c) + (a + c) + (a + b)),
            from by {exact harmonic_mean_arithmetic_mean_inequality (1 / (b + c)) (1 / (a + c)) (1 / (a + b))},
          rw ← mul_assoc,
          rw ← ← one_div_mul_cancel (a + b + c),
          rw one_div_eq_inv,
          rw mul_comm,
          rw mul_assoc,
          rw ← div_eq_mul_one_div,
          rw ← mul_assoc,
          rw ← div_eq_mul_one_div,
          apply mul_le_mul h5 ha,
          apply add_pos,
          rw mul_comm (a + b + c),
          exact zero_add _,
          intros x hx,
          exact hc,
          intros x hx,
          exact hb,
        },
        rw ← add_assoc,
        rw ← add_assoc,
        rw ← add_assoc,
        rw add_comm (a + b),
        rw add_comm (a + c),
        rw add_comm (b + c),
        rw add_assoc,
        rw add_assoc,
        rw ← add_assoc (a + b),
        rw ← add_assoc,
        apply add_le_add_right (b / (a + c)),
        apply add_le_add_left (c / (a + b)),
        exact h4,
        apply lt_of_le_of_lt h3,
        rw ← add_assoc,
        rw ← add_assoc,
        rw ← add_assoc,
        rw ← add_assoc,
        rw ← add_assoc,
        rw ← div_eq_mul_one_div,
        rw ← div_eq_mul_one_div,
        rw ← div_eq_mul_one_div,
        rw ← mul_assoc,
        rw ← mul_assoc,
        rw ← mul_assoc,
        rw mul_comm (3 : ℝ),
        rw ← mul_assoc,
        rw ← mul_assoc,
        apply mul_lt_mul ha,
        exact add_pos hc hb,
        exact add_pos hc ha,
        exact add_pos hb ha,
        intros x hx,
        exact hc,
        intros x hx,
        exact hb,
        intros x hx,
        exact ha,
      },
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
      rw add_comm (b + c),
      rw add_comm (a + c),
      rw add_comm (a + b),
      rw ← add_assoc,
      rw ← add_assoc,
      rw ← add_assoc,
      rw ← add_assoc,
      rw ← add_assoc,
      rw ← add_assoc,
      rw add_assoc (a + b),
      rw add_assoc,
      rw add_comm (a + b),
      rw add_assoc,
      rw ← add_assoc (a + b + c),
      rw add_comm (a + b + c),
      apply add_le_add_right (c / (a + b)),
      apply add_le_add_right (b / (a + c)),
      apply add_le_add_left (a / (b + c)),
      exact h3,
      apply lt_of_le_of_lt h2,
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
      rw add_comm (b + c),
      rw add_comm (a + c),
      rw add_comm (a + b),
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
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← div_eq_mul_one_div,
      rw ← div_eq_mul_one_div,
      rw ← div_eq_mul_one_div,
      rw ← div_eq_mul_one_div,
      rw ← div_eq_mul_one_div,
      rw ← div_eq_mul_one_div,
      rw ← div_eq_mul_one_div,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw ← mul_assoc,
      rw mul_comm (3 : ℝ),
      rw mul_assoc,
      rw mul_assoc,
      rw mul_assoc,
      rw mul_assoc,
      rw mul_comm (3 : ℝ),
      apply mul_lt_mul ha,
      exact add_pos hb hc,
      exact add_pos
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) ≥ 9 / 2, from 
    arith_mean_never_less_than_harmonic_mean _ _ _,
  calc
     (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = 3 * ((a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b)) / (a + b + c) : by ring
  ... = (9 / 2) / (a + b + c) : by rw [mul_comm 3,mul_assoc, mul_div_cancel _ (by apply add_pos ha hb; linarith), ←mul_div_cancel' _ (by linarith),h1]
  ... = (3 / 2) * ((a + b + c) / (a + b + c) : by rw [mul_div_cancel _ (by linarith), ←div_div_cancel, mul_comm 3,←mul_div_cancel' _ (by linarith)])
  ... = (3 / 2) * (1 : ℝ) : by rw [div_self ha, one_mul]
  ... = (3 / 2) : rfl,
end

--OUTPUT 8
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  have h1 : (a + b + c) / (b+c) ≥ (9 * (a + b + c)) / ((b + c) + (a + c) + (a + b)), from by {
    rw ← inv_inv' (hb + hc),
    have h1 : b + c ≠ 0, from assume h, by { rw h at hb, simp at hb },
    have h2 : a + c ≠ 0, from assume h, by { rw h at hc, simp at hc },
    have h3 : a + b ≠ 0, from assume h, by { have h4 : b ≠ 0, from assume h5, by { rw h5 at hb, simp at hb },
    have h5 : a ≠ 0, from assume h6, by { rw h6 at ha, simp at ha },
    have h6 : b = 0, from eq_zero_of_add_eq_zero (h h4 h5) ,
    rw h6 at hb, simp at hb },
    have h4 : b + c + (a + c) + (a + b) ≠ 0, from assume h5, by { 
      rw h5 at h1 h2 h3, simp at h1 h2 h3, },
    have h5 : (3 : ℝ) ≠ 0, from assume h6, by { rw h6, simp, },
    have h6 : (a + b + c) ≠ 0, from assume h7, by { rw h7 at ha hb hc, simp at ha hb hc },
    calc 9 * (a + b + c) / ((b + c) + (a + c) + (a + b)) = (3 * 3) * (a + b + c) / ((b + c) + (a + c) + (a + b))
      : by rw mul_comm (3 : ℝ) (3 : ℝ)
    ... = 3 * 3 * (a + b + c) / ((b + c) + (a + c) + (a + b)) : by rw mul_comm (3 : ℝ) (a + b + c)
    ... = 3 * (3 * (a + b + c)) / ((b + c) + (a + c) + (a + b)) : by simp
    ... = 3 * ((a + b + c) / (b + c) + (a + c) + (a + b)) : by rw add_mul
    ... = 3 * ((a + b + c) / (b + c)) + 3 * ((a + c) + (a + b)) : by rw add_mul
    ... = 3 * ((a + b + c) / (b + c) + (a + c)) + 3 * (a + b) : by rw add_assoc
    ... = 3 * ((a + b + c) / (b + c) + (a + c)) + 3 * a + 3 * b : by rw add_mul
    ... = (a + b + c) * ((a + b + c) / (b + c)) + 3 * ((a + c) + a + b) : by rw mul_comm (a + b + c) 3
    ... = (a + b + c) * ((a + b + c) / (b + c)) + 3 * ((a + c) + (b + a)) : by rw add_comm a b
    ... = (a + b + c) * ((a + b + c) / (b + c)) + 3 * ((a + c) + b + a) : by rw add_assoc
    ... = (a + b + c) * ((a + b + c) / (b + c)) + 3 * (b + a + (a + c)) : by rw add_comm b a
    ... = (a + b + c) * ((a + b + c) / (b + c)) + 3 * (b + (a + a + c)) : by rw add_assoc
    ... = (a + b + c) * ((a + b + c) / (b + c)) + 3 * (b + a + a + c) : by rw add_assoc a a c
    ... = (a + b + c) * ((a + b + c) / (b + c)) + 3 * (a + a + b + c) : by rw add_comm b a
    ... = (a + b + c) * ((a + b + c) / (b + c)) + 3 * (a + (a + b) + c) : by rw add_assoc
    ... = (a + b + c) * (a + b + c) / (b + c) + 3 * ((a + b) + c) : by rw add_mul
    ... = (a + b + c) * a / (b + c) + (a + b + c) * b / (b + c) + (a + b + c) * c / (b + c) + 3 * ((a + b) + c) : by rw add_mul
    ... = (a * (a + b + c)) / (b + c) + (b * (a + b + c)) / (b + c) + (c * (a + b + c)) / (b + c) + 3 * ((a + b) + c) : by rw mul_comm (a + b + c)
    ... = a * a / (b + c) + b * a / (b + c) + c * a / (b + c) + a * b / (b + c) + b * b / (b + c) + c * b / (b + c) + a * c / (b + c) + b * c / (b + c) + c * c / (b + c) + 3 * ((a + b) + c) : by rw add_mul
    ... = a * a / (b + c) + b * a / (b + c) + c * a / (b + c) + b * a / (b + c) + a * b / (b + c) + c * b / (b + c) + b * c / (b + c) + a * c / (b + c) + c * c / (b + c) + 3 * ((a + b) + c) : by rw add_mul
    ... = a * a / (b + c) + b * a / (b + c) + c * a / (b + c) + a * b / (b + c) + b * b / (b + c) + c * b / (b + c) + a * c / (b + c) + b * c / (b + c) + c * c / (b + c) + 3 * ((a + b) + c) : by rw add_mul
    ... = a / (b + c) * a + b / (b + c) * a + c / (b + c) * a + a / (b + c) * b + b / (b + c) * b + c / (b + c) * b + a / (b + c) * c + b / (b + c) * c + c / (b + c) * c + 3 * (a + b + c) : by rw mul_comm
    ... = a / (b + c) * a + a / (b + c) * b + a / (b + c) * c + b / (b + c) * a + b / (b + c) * b + b / (b + c) * c + c / (b + c) * a + c / (b + c) * b + c / (b + c) * c + 3 * (a + b + c) : by rw add_mul
    ... = a / (b + c) * a + a / (b + c) * b + a / (b + c) * c + a / (b + c) * b + b / (b + c) * b + b / (b + c) * c + a / (b + c) * c + b / (b + c) * c + c / (b + c) * c + 3 * (a + b + c) : by rw add_mul
    ... = a / (b + c) * a + b / (b + c) * b + a
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  calc (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = 3 * (a / (b + c)) + 3 * (b / (a + c)) + 3 * (c / (a + b)) : by ring
  ... = 3 * ((a / (b + c)) + (b / (a + c)) + (c / (a + b))) : by {simp only [mul_add], rw [← add_assoc], simp only [three_mul],}
  ... ≥ 3 * (3 / (b + c) + (a + c) + (a + b))⁻¹ : by {apply mul_le_mul_of_nonneg_right (by norm_num), apply arithmetic_ge_harmonic,}
  ... = 3 / (3 * (3 / (b + c) + (a + c) + (a + b))) : by {rw div_mul_div_assoc, rw div_self (by norm_num), simp [three_mul],}
  ... = 3 / ((b + c) + (a + c) + (a + b)) : by ring
  ... ≥ 2.5 : by {apply div_le_of_le_mul, norm_num, rw [← add_assoc,add_comm (a + b) c,add_assoc],simp [add_assoc], exact add_nonneg (add_nonneg ha hb) hc,}
  ... = 3 / 2 : by norm_num,
end

--OUTPUT 10
theorem nesbitt_inequality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) ≥ (3 / 2) :=
begin
  apply le_of_eq,
  have h1 : (a / (b + c)) + (b / (a + c)) + (c / (a + b)) = (a + b + c) / (b + c) +
    (a + b + c) / (a + c) + (a + b + c) / (a + b), from by ring,
  have h2 : (a + b + c) / (b + c) + (a + b + c) / (a + c) + (a + b + c) / (a + b) =
    (9 / 2) * (a + b + c), from by {rw ← div_mul_cancel, simp, ring},
  rw [h1,h2],
  have h3 : (9 / 2) * (a + b + c) ≥ (3 / 2) * (1 / ((b + c) + (a + c) + (a + b))), from
    mul_le_mul (arithmetic_mean_ge_harmonic_mean (1 / (b + c)) (1 / (a + c)) (1 / (a + b))) 
    (zero_lt_one) (zero_lt_one),
  have h4 : (a + b + c) ≠ 0, from lt_of_le_of_lt (by apply le_of_lt; apply add_three_nonneg; apply ha;apply hb;apply hc) one_add_one,
  have h5 : (3 / 2) * (1 / ((b + c) + (a + c) + (a + b))) = ((3 / 2) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b))) / ((b + c) + (a + c) + (a + b)), from by ring,
  rw [div_mul_cancel h4, h5] at h3,
  convert h3,
  have h6 : (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) ≠ 0, from 
    by {apply add_ne_zero, apply inv_pos, apply add_pos, 
    apply hb, apply hc, apply ha, apply hc, apply hb, apply ha},
  have h7 : (3 / 2) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) = 
    (a / (b + c)) + (b / (a + c)) + (c / (a + b)), from by ring,
  rw [div_mul_cancel h6, h7],
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
