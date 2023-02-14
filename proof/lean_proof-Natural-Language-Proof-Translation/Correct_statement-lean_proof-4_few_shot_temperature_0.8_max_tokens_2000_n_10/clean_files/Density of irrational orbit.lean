import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  rw closure_eq,
  split; rintros ⟨x, h₁, h₂⟩; split,
  rwa [← coe_nat_cast_on_nat_cast (nat.succ_pos _), ← coe_nat_cast_add, coe_int_nat, nat.cast_add, nat.add_one,
        nat_cast_lt_coe_nat, int.coe_nat_succ, int.add_mul_div_left_fract, int.fract_coe_nat, int.add_zero,
        ← int.to_rat_mul],
  {
    assume h,
    have h' : ↑(x - α) ∈ (@set.univ ℤ),
    {
      rw [← int.to_rat_mul, ← rat.cast_coe_int, @rat.cast_lt _ _ _ x,
          rat.cast_lt_rat, rat.fract_lt_iff, rat.mul_eq_one, int.coe_nat_one] at h,
      rwa [← rat.cast_coe_int, ← int.to_rat_mul],
    },
    rw ← h₂ at h',
    cases h',
  },
  {
    assume h,
    cases (classical.em (x = 1)),
    {
      rw h_1,
    },
    {
      let N : ℕ := ⌊x⌋,
      have h' : x - int.nat_abs (x * rat.cast α - int.nat_abs (N * rat.cast α)) < 1,
      {
        rw [← rat.cast_coe_int, rat.cast_lt_rat, int.fract_eq_of_nonneg_of_lt, int.nat_abs_of_nonneg, int.coe_nat_nonneg,
            ← rat.cast_coe_int, int.coe_nat_lt_coe_nat_of_lt, int.lt_nat_abs, rat.cast_lt_rat] at h,
        rw [← int.nat_abs_of_nonneg (int.coe_nat_nonneg _), ← int.coe_nat_lt_coe_nat_of_lt, int.lt_nat_abs] at h,
        exact h,
      },
      have h' : x - rat.cast (int.nat_abs (x * rat.cast α - int.nat_abs (N * rat.cast α))) < 1,
      {
        rw rat.cast_lt_rat,
        exact h',
      },
      have h'' : 0 < x * rat.cast α - int.nat_abs (N * rat.cast α),
      {
        have h'' : 0 < x - ((1 : ℝ) - rat.cast (int.nat_abs (x * rat.cast α))) := by linarith,
        rw [← int.to_rat_mul, ← rat.cast_coe_int, ← int.to_rat_mul],
        simpa only [rat.cast_sub, int.coe_nat_add, rat.cast_le, rat.cast_coe_nat, rat.sub_eq_add_neg],
      },
      have h''' : 0 < (x * rat.cast α - int.nat_abs (N * rat.cast α)) * int.nat_abs (x * rat.cast α - int.nat_abs (N * rat.cast α)),
      {
        exact rat.mul_pos h'' (int.nat_abs_pos _),
      },
      have h''' : 0 < (x * rat.cast α - int.nat_abs (N * rat.cast α)) * rat.cast (int.nat_abs (x * rat.cast α - int.nat_abs (N * rat.cast α))),
      {
        rw rat.cast_lt_rat,
        exact h''',
      },
      have h'''' : x * rat.cast α - int.nat_abs (N * rat.cast α) < rat.cast (int.nat_abs (x * rat.cast α - int.nat_abs (N * rat.cast α))),
      {
        rw [int.nat_abs_of_nonneg (int.le_of_lt h''), ← sub_eq_add_neg],
        exact rat.sub_lt_sub_right h''' _,
      },
      have h'''' : x * rat.cast α - int.nat_abs (N * rat.cast α) - rat.cast (int.nat_abs (x * rat.cast α - int.nat_abs (N * rat.cast α))) < 0,
      {
        rw [← rat.cast_sub, ← rat.cast_sub],
        exact rat.sub_lt_sub_left h'''' _,
      },
      have h''''' : 0 < x * rat.cast α - int.nat_abs (N * rat.cast α) - (x * rat.cast α - int.nat_abs (N * rat.cast α)),
      {
        rw [← int.coe_nat_zero, ← int.coe_nat_sub, ← rat.cast_sub],
        exact rat.sub_pos.2 h'''',
      },
      have h''''' : (x * rat.cast α - int.nat_abs (N * rat.cast α)) * 0 < 0,
      {
        exact rat.mul_lt_mul_of_pos_left h''''' (int.coe_nat_pos _),
      },
      have h''''' : 0 < 0,
      {
        rw [int.nat_abs_zero, rat.cast_zero, rat.cast_sub, rat.sub_eq_zero_iff_eq] at h''''',
        exact h''''',
      },
      exact int.lt_irrefl _ h''''',
    },
    
    {
      rw [← int.to_rat_mul, ← rat.cast_coe_int, ← int.to_rat_mul] at h,
      apply int.lt_of_add_one_le_iff.2,
      apply int.le_of_lt_add_one,
      intros a ha,
      have h' : a * rat.cast α < 0,
      {
        have : a * rat.cast α ≤ x * rat.cast α := rat.mul_le_mul_of_nonneg_left (le_of_lt ha) (rat.cast_nonneg _),
        linarith,
      },
      have h'' : int.nat_abs (a * rat.cast α) = 0,
      {
        have h''' : 0 < int.nat_abs (a * rat.cast α),
        {
          rw int.nat_abs_of_nonneg (le_of_lt h'),
          exact h',
        },
        linarith,
      },
      rw [int.nat_abs_of_nonneg (le_of_lt ha), sub_eq_zero, ← int.to_rat_mul, ← rat.cast_coe_int, ← int.to_rat_mul] at h'',
      rw [← int.to_rat_mul, ← rat.cast_coe_int, ← int.to_rat_mul] at h'',

      have h''' := int.lt_of_add_one_le_iff.1 (int.coe_nat_le_coe_nat.2 ha),
      rw [← int.coe_nat_add, sub_eq_zero, int.coe_nat_sub, sub_eq_zero, ← int.to_rat_mul, ← rat.cast_coe_int,
          ← int.to_rat_mul] at h''',
      rw [← int.to_rat_mul, ← rat.cast_coe_int, ← int.to_rat_mul, rat.cast_lt_rat] at h''',
      linarith,
    },
  },
end

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h_nonempty : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
    begin
      assume (i j : ℤ) h_neq,
      have h_1 : (α * ↑i - (int.fract (α * ↑i))) = int.fract (α * ↑i),
      {
        have h_2 := int.fract_val (α * ↑i),
        rw h_2,
        rw int.fract_val,
        ring,
      },
      have h_3 : (α * ↑j - (int.fract (α * ↑j))) = int.fract (α * ↑j),
      {
        have h_4 := int.fract_val (α * ↑j),
        rw h_4,
        rw int.fract_val,
        ring,
      },
      have h_5 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from rat.eq_iff_mul_eq_mul_left_iff.mp (int.eq_iff_modeq_nat_int.mp h_neq),
      have h_6 : (i - j) ≠ (0 : ℤ), from assume h_absurd, h_neq (one_mul i - one_mul j),
      have h_7 : (i - j) ≠ (0 : ℕ), from int.coe_nat_ne_zero_iff_ne_zero.mp h_6,
      have h_8 : (i - j) ≠ (0 : ℚ), from 
        begin 
          have h_9 : (0 : ℤ) ≠ (i - j), from assume h_absurd, h_neq (i - j),
          rw int.eq_zero_iff_nat_abs_eq_zero, 
          rw nat.eq_zero_iff_zero at h_9,
          rw nat.eq_zero_iff_zero at h_9,
          exact h_9,
        end,
      rw rat.div_eq_iff_mul_eq h_8 at h_5,
      rw ← h_1 at h_5,
      rw ← h_3 at h_5,
      rw ← rat.cast_val at h_5,
      have h_10 : (int.fract (α * ↑i) - int.fract (α * ↑j)) ≠ (0 : ℤ), from assume h_absurd, h_neq (int.fract (α * ↑i) - int.fract (α * ↑j)),
      have h_11 :
        (int.fract (α * ↑i) - int.fract (α * ↑j)) ≠ (0 : ℤ),
        from nat.cast_ne_zero.mp h_10,
      have h_12 : (int.fract (α * ↑i) - int.fract (α * ↑j)) ≠ (0 : ℚ), from 
        begin 
          have h_13 : (0 : ℤ) ≠ (int.fract (α * ↑i) - int.fract (α * ↑j)), from assume h_absurd, h_neq (int.fract (α * ↑i) - int.fract (α * ↑j)),
          rw int.eq_zero_iff_nat_abs_eq_zero, 
          rw nat.eq_zero_iff_zero at h_13,
          rw nat.eq_zero_iff_zero at h_13,
          exact h_13,
        end,
      rw rat.cast_ne_zero_iff at h_12,
      exact h_12 h_5,
    end,

  have h_seq_limit : ∀ (i : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑(i + n))) 0, from
    begin
      assume i,
      assume ε : ℝ,
      assume h1 : (ε > 0),
      have h2 : (2 * ε) > 0, from 
        begin 
          have h3 := rat.coe_lt_coe,
          have h4 := h3 ℝ ℚ ε (2 : ℝ) (rat.cast_lt.mp h1),
          rw rat.cast_one at h4,
          linarith,
        end,
      have h5 : ∃ (N : ℤ), (∀ (n : ℕ), (int.fract (α * ↑(i + n))) ≤ ((-1 : ℤ) + (1 + (2 * ε))) ∧ ((-1 : ℤ) + (1 + (2 * ε))) ≤ (int.fract (α * ↑(i + n)))), from 
        begin
          use int.nat_abs ((1 + ε) / (2 * α)),
          assume n h_absurd,
          have h6 : (int.fract (α * ↑(i + n)) - (int.fract (α * ↑i))) = (int.fract (α * ↑n)), from
            begin 
              rw nat.add_comm (i : ℕ),
              rw int.fract_add,
              rw int.fract_val,
              ring,
            end,
          have h7 : (α * ↑n - (int.fract (α * ↑n))) = int.fract (α * ↑n), from 
            begin 
              rw int.fract_val,
              ring,
            end,
          have h8 : α = (α * ↑n - (int.fract (α * ↑n))) / (n : ℕ) ,from 
            begin
              have h9 : (n : ℤ) ≠ (0 : ℤ), by {linarith,},
              have h10 : (n : ℤ) ≠ (0 : ℝ), by {rw rat.cast_ne_zero_iff, exact h9,},
              rw rat.div_eq_iff_mul_eq h10,
              ring,
            end,
          have h11 : ((n : ℝ) : ℚ) ≠ (0 : ℚ), from 
            begin
              have h12 : (n : ℤ) ≠ (0 : ℤ), by {linarith},
              rw rat.cast_ne_zero_iff,
              exact h12,
            end,
          rw rat.div_eq_iff_mul_eq h11 at h8,
          rw h7 at h8,
          rw ← h6 at h8,
          have h13 : (α * ↑(i + n) - (int.fract (α * ↑i))) = (int.fract (α * ↑n)), from
            begin 
              rw nat.add_comm (i : ℕ),
              rw int.fract_add,
              rw int.fract_val,
              ring,
            end,
          rw h7 at h13,
          rw ← h13 at h8,
          have h14 : (int.fract (α * ↑n) < ((1 + (2 * ε)) : ℝ)), from 
            begin 
              have h15 : (int.fract (α * ↑n) - (1 + (2 * ε))) < (0 : ℝ), from by {linarith},
              have h16 : (0 : ℝ) - (0 : ℝ) < (int.fract (α * ↑n) - (1 + (2 * ε))), from by {linarith},
              rw zero_sub at h16,
              exact h16,
            end,
          have h17 : ((-1) : ℤ) ≤ (int.fract (α * ↑n)), from by {linarith},
          have h18 : (int.fract (α * ↑n)) ≤ ((1 + (2 * ε)) : ℝ), from by {linarith,},
          split, exact h17, exact h
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  split,

  {
    show closure ((λ (m : ℤ), int.fract (α * ↑m)) '' set.univ) ⊆ Icc 0 1,
    by {
      assume y (h1 : (λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' {y} ∈ closure (λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' {y}),
      have h2_exists : ∃ m : ℤ, (λ (m : ℤ), int.fract (α * ↑m)) m = y, from
        exists_mem_of_ne_empty h1,
      cases h2_exists with m h2, rw h2,
      rw int.fract_mul,
      rw int.fract_eq_iff_mod_one,
      simp, exacts [and.intro (by rw int.div_lt_iff;exacts[lt_iff_le_and_ne,zero_lt_one,hα_irrat]) (by rw int.mod_lt;exact one_pos)],
    },
  },

  {
    show Icc 0 1 ⊆ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' set.univ),
    by {
      assume y (h : y ∈ Icc 0 1),
      cases h with h1 h2,
      have h1_pos : (0 : ℤ) < 1, from zero_lt_one,

      have h2_dense : ∀ ε : ℝ, 0 < ε → ∃ (m : ℤ), ((int.fract (α * ↑m)) - y)^2 < ε,
      from begin
        assume ε h2,
        have h3 : 0 < ε^2, from by {rw pow, linarith},
        have h4 : (ε^2) / 2 = ε / 2 * ε, from by {rw ← pow, linarith},
        have h4_pos : 0 < ε / 2, from by {rw ← h4, linarith},
        have h5 : 2 < ε^2, from by {rw pow, linarith},

        have h6 : 0 < y, from by {contradiction, linarith},
        have h7 : 0 < 1 - y, from by {rw sub_pos_iff, linarith},
        have h8 : 0 < min y (1 - y), from by {apply min_pos, exacts [h6,h7]},

        have h9 : ∃ a : ℤ, 1 - y < (α * ↑a - y)^2 ∧ (α * ↑a - y)^2 < ε,
        from begin
          have h10 : ∃ a : ℤ, (α * ↑a - y)^2 < ε, by {
            apply limit_theorem_irrational_squared_distance,
            exact hα_irrat,
            exact h5,
          },
          cases h10 with a h10,
          have h10_pos : 0 < (α * ↑a - y)^2, from by {rw pow, linarith},
          have h11 : ∃ a : ℤ, 1 - y < (α * ↑a - y)^2, from by {
            apply limit_theorem_irrational_squared_distance,
            exact hα_irrat,
            exact h3,
          },
          cases h11 with a1 h11,

          existsi max a a1,
          split,
          {
            apply lt_of_le_of_lt,
            apply lt_of_lt_of_le,
            apply int.cast_lt,
            exact le_max_left _ _,
            exact h11,
          },
          {
            apply lt_of_lt_of_le,
            apply lt_of_lt_of_le,
            apply int.cast_lt,
            exact le_max_right _ _,
            exact h10,
          },
        end,

        cases h9 with a h9,

        existsi a,
        rw pow_two,
        rw pow_two,
        rw sub_sub,
        rw ← subsingleton.elim (int.cast_inj.mp (le_antisymm (int.cast_lt.mp (by linarith)) (int.cast_lt.mp (le_max_left _ _)))),
        rw ← subsingleton.elim (int.cast_inj.mp (le_antisymm (int.cast_lt.mp (by linarith)) (int.cast_lt.mp (le_max_right _ _)))),
        rw int.fract_mul,
        rw int.fract_eq_iff_mod_one,
        rw int.mod_lt,
        rw pow_two,
        rw pow_two,
        rw sub_sub,
        linarith,
        linarith,
        exact one_pos,
        exact one_pos,
        exact hα_irrat,
        exact hα_irrat,
        rw pow,
        linarith,
      end,

      have h3 : ∃ (m : ℤ), ((int.fract (α * ↑m)) - y)^2 < (ε / 2)^2, from 
        @squeeze_theorem_real_numbers ℤ ((λ (m : ℤ), int.fract (α * ↑m)) - y) 0 ((ε / 2)^2)
        (by rw sub_zero),
      cases h3 with m h3,
      have h4 : 0 < (ε / 2)^2, from by {rw pow, linarith},
      have h5 : ((int.fract (α * ↑m)) - y)^2 < ε / 2, from by {rw ← pow, linarith},
      have h6 : y < int.fract (α * ↑m) + ε / 2, by {linarith},
      existsi m,
      split,
      {
        have h7 : int.fract (α * ↑m) - ε / 2 ≤ int.fract (α * ↑m), from by {linarith},
        rw ← sub_sub,
        rw ← sub_sub,
        rw ← sub_sub,
        rw sub_sub_self,
        apply lt_of_le_of_lt,
        exact h7,
        exact h6,
      },
      {
        have h7 : int.fract (α * ↑m) + ε / 2 < 1, from int.fract_lt_one_of_ne_zero (by linarith),
        rw ← sub_sub,
        apply lt_of_lt_of_le,
        exact h6,
        exact h7,
      },
    },
  },
end

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
    by {
      intros i j hi,
      rw int.fract_eq_iff.1,
      intro h2,
      have h2_rat := @rat.cast_inj ℤ _ _ _ _,
      rw [int.cast_inj, int.cast_inj] at h2_rat,
      have h3 := h2_rat
        ((int.cast α)/(int.cast i))
        ((int.cast α)/(int.cast j)),
      rw [h2,h2] at h3,
      have h4 := h1,
      apply hi h4,
    },

  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
    by {
      intros i j hi,
      rw int.fract_eq_iff.1,
      intro h2,
      have h2_rat := @rat.cast_inj ℤ _ _ _ _,
      rw [int.cast_inj, int.cast_inj] at h2_rat,
      have h3 := h2_rat
        ((int.cast α)/(int.cast i))
        ((int.cast α)/(int.cast j)),
      rw [h2,h2] at h3,
      have h4 := h3.trans (by {ring at h3, exact h3}),
      have h5 : int.cast i = 0, from h4.right.right,
      have h6 : int.cast j = 0, from h4.left.right,
      have h7 : i = 0, from congr_arg int.fract h5,
      have h8 : j = 0, from congr_arg int.fract h6,
      have h9 : i = j, by {rw [h7,h8]},
      apply hi h9,
    },

  have h2 : ∀ m n : ℤ, m ≠ n → (int.fract (α * ↑m)) * (int.fract (α * ↑n)) ≠ 0, from
    by {
      intros m n h,
      rw int.fract_eq_iff.1,
      intro h2,
      have h3 := int.cast_inj α,
      rw h3,
      have h4 := int.cast_inj m,
      have h5 := int.cast_inj n,
      have h6 := int.cast_mul m n,
      have h7 := int.cast_mul α α,
      rw [h4,h5,h6,h7,mul_assoc,h2] at h3,
      have h8 := @rat.cast_inj ℤ _ _ _ _,
      have h9 := h8 _ _ h3,
      have h10 := rat.mul_self_inj (int.cast α),
      rw [←rat.mul_div_assoc,h2,rat.one_mul,rat.div_one,rat.one_mul,rat.div_one,rat.mul_one] at h10,
      apply h10 h9,
    }, 


  have h2 : ∀ m n : ℤ, m ≠ n → (int.fract (α * ↑m)) * (int.fract (α * ↑n)) ≠ 0, from
    by {
      intros m n hn,
      rw int.fract_eq_iff.1,
      intro h,
      have h1 := int.cast_inj α, 
      have h2 := int.cast_inj m,
      have h3 := int.cast_inj n,
      have h4 := int.cast_mul m n,
      have h5 := int.cast_mul α α,
      rw [h2,h3,h4,h5,mul_assoc,h,mul_assoc] at h1,
      have h6 : (int.cast α) * ((int.cast m) * (int.cast n)) = ((int.cast α) * (int.cast α)) * (int.cast m), from by {
        rw h1, ring,
      },
      have h7 := @rat.cast_inj ℤ _ _ _ _,
      have h8 := h7 _ _ h6,
      have h9 := rat.mul_self_inj (int.cast α),
      rw [←rat.mul_div_assoc,h,rat.one_mul,rat.div_one,rat.one_mul,rat.div_one,rat.mul_one] at h9,
      apply h9 h8,
    },


  have h3 : ∀ n : ℤ, n ≠ 0 → rat.mk n 1 ≠ (int.cast α) * ((int.cast n) * (int.cast n)), 
  begin
    assume (n : ℤ) (hn : n ≠ 0),
    rw rat.mk_eq_div,
    rw int.cast_inj,
    have h1 := int.cast_inj α, 
    have h2 := int.cast_inj n,
    have h3 := int.cast_mul n n,
    have h4 := int.cast_mul α n,
    rw [h2,h3,h4,mul_assoc,mul_assoc,mul_assoc,h1] at hn,
    rw [mul_comm,mul_comm] at hn,
    intro h,
    cases h with h1 h2,
    rw [h1,h2,rat.mul_div_cancel] at hn,
    have h5 : int.cast n = 0, from hn,
    rw h5 at h1,
    have h6 : n = 0, from congr_arg int.fract h1,
    have h7 : n ≠ n, from h6.symm ▸ hn,
    apply h7, 
    end,

  have h3 : ∀ n : ℤ, n ≠ 0 → rat.mk n 1 ≠ (int.cast α) * ((int.cast n) * (int.cast n)), from 
    by {
      assume (n : ℤ) (hn : n ≠ 0),
      rw rat.mk_eq_div,
      rw int.cast_inj,
      have h1 := int.cast_inj α, 
      have h2 := int.cast_inj n,
      have h3 := int.cast_mul n n,
      have h4 := int.cast_mul α n,
      rw [h2,h3,h4,mul_assoc,mul_assoc,mul_assoc,h1] at hn,
      rw [mul_comm,mul_comm] at hn,
      intro h,
      cases h with h1 h2,
      rw [h1,h2,rat.mul_div_cancel] at hn,
      have h5 : int.cast n = 0, from hn,
      rw h5 at h1,
      have h6 : n = 0, from congr_arg int.fract h1,
      have h7 : n ≠ n, from h6.symm ▸ hn,
      apply h7, 
    },

  have h4 : ∀ m n : ℤ, m ≠ n → (int.fract (α * ↑m)) * (int.fract (α * ↑n)) ≠ 0, from 
    by {
      assume (m n : ℤ) (hm : m ≠ n),
      cases m with m,
      exfalso,
      apply hm (int.coe_nat_zero),
      cases n with n, 
      exfalso, rw eq_comm at hm, apply hm (int.coe_nat_zero).symm,

end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := 
begin
  unfold irrational at hα_irrat, 
  assume ε : ℝ,
  assume (h1 : 0 ≤ ε) (h2 : ε < 1),
  have εpos : ε > 0, from lt_of_lt_of_le h2 h1,

  have h3 : ∃ q ∈ ℚ, ε < q, from
  begin
    apply exists_lt_rat,
    exact ε,
  end,
  rcases h3 with ⟨q1, h4, h5⟩,
  note h6 := hα_irrat q1 h4,
  let q2 := min q1 1,
  have h7 : q1 ≥ q2, from min_le_left,
  let N := ceil ((q2 - ε) / α),
  have h7 : N ∈ ℕ, from nat.mem_coe.2 (le_ceil ((q2 - ε) / α)),
  let m : ℤ := N,
  have h8 : α * ↑m = α * (↑N : ℝ), from by rw mul_comm,
  have h9 : 0 ≤ α * ↑N, from zero_le_mul (nat.cast_nonneg.2 h7) (irrational.nonneg hα_irrat),
  have h10 : α * ↑N ≤ (q1 - ε), from le_of_lt (sub_lt_iff_lt_add'.2 h5),
  let αNε : ℝ := (α * ↑N) + ε,
  have h11 : (αNε : ℝ) ∈ set.univ, from
  begin
    change ((αNε : ℝ) ∈ set.univ),
    suffices h12 : αNε ∈ ℝ,
      from ⟨h12, rfl⟩,
    split,
    exact h9,
    exact h10,
  end,
  have h12 : (αNε : ℝ) = α * ↑N + ε, from rfl,
  have h13 : (0 : ℝ) ≤ α * ↑N + ε, from calc
    0 ≤ α * ↑N : add_nonneg h9 (by {linarith; from trivial})
    ... ≤ α * ↑N + ε : add_le_add_left h10 (by {linarith; from trivial}),
  have h14 : α * ↑N + ε ≤ 1, from calc
    α * ↑N + ε ≤ q2 : add_le_add_right h10 (by {linarith; from trivial})
    ... ≤ 1 : add_le_add_right (by {linarith; from trivial}) (by {linarith; from trivial}),
  have h15 : (αNε : ℝ) ∈ set.Icc 0 1, from ⟨h13, h14⟩,
  have h16 : (αNε : ℝ) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), 
    from set.mem_closure_of_mem (set.mem_image_of_mem αNε h11) (by {linarith; from trivial}),
  have h17 : ∃ x ∈ set.Icc 0 1, ∀ y : ℝ, y ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) → ∃ b : ℝ, (b > 0 ∧ b < ε) ∧ abs (x - y) < b,
  from set.mem_of_closure_of_mem h16 (by {linarith; from trivial}),
  have h18 : ∃ x : ℝ, x ∈ set.Icc 0 1 ∧ ∀ y : ℝ, y ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) → ∃ b : ℝ, (b > 0 ∧ b < ε) ∧ abs (x - y) < b, from exists_prop h17,
  have h19 : ∃ x : ℝ, x ∈ set.Icc 0 1 ∧ 
    ∀ y : ℝ, ∃ b : ℝ, (y ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ (b > 0 ∧ b < ε) ∧ abs (x - y) < b, from exists_prop h18,
  have h20 : ∃ x : ℝ, x ∈ set.Icc 0 1 ∧ 
    ∀ y : ℝ, ∃ b : ℝ, (y ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ (b > 0 ∧ b < ε) ∧ abs (x - y) < b, from exists_prop h19,
  have h21 : (αNε : ℝ) ∈ ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from
  begin
    change ((αNε : ℝ) ∈ ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ))),
    apply exists.intro m,
    split,
    exact h11,
    rw ← h12,
    rw ← h8,
    exact rfl,
  end,
  have h22 : ∃ b : ℝ, ((αNε : ℝ) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ (b > 0 ∧ b < ε) ∧ abs (αNε - αNε) < b, from h20 αNε h15 h21,
  have h23 : ∃ b : ℝ, (b > 0 ∧ b < ε) ∧ abs (αNε - αNε) < b, from exists_prop h22,
  have h24 : ∃ b : ℝ, (b > 0 ∧ b < ε) ∧ (abs (αNε - αNε) < b), from exists_prop h23,
  have h25 : ∃ b : ℝ, (b > 0 ∧ b < ε) ∧ (abs (αNε - αNε) < b), from exists_prop h24,
  have h26 : ∃ b : ℝ, (b > 0 ∧ b < ε) ∧ (abs (αNε - αNε) < b), from exists_prop h25,
  have h27 : αNε - αNε = 0, from calc
    αNε - αNε = α* ↑N + ε - α* ↑N - ε : by rw [h12, h12]
    ... = 0 : by ring,
  have h28 : abs (0 : ℝ) = 0, from dec_trivial,
  have h29 : ∃ b : ℝ, (b > 0 ∧ b < ε) ∧ (abs (αNε - αNε) < b), 
    from eq.symm (h28 (αNε - αNε)) ▸ h26,
  have h30 : ∃ b : ℝ, b > 0 ∧ b < ε, from exists_prop h29,
  have h31 : ∃ b : ℝ, b > 0 ∧ b < ε, from exists_prop h30,
  have h32 : ∃ b : ℝ, b > 0 ∧ b < ε, from exists_prop h31,
  have h33 : ∃ b : ℝ, b > 0 ∧ b < ε, from exists_prop h32,
  have h34 : ∃ b : ℝ, b > 0 ∧ b < ε, from exists_prop h33,
  have h35 : ∃ b : ℝ, b > 0 ∧ b < ε, from exists_prop h34,
  have h36 :
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (m n : ℤ), m ≠ n → (α * ↑ m) % 1 ≠ (α * ↑ n) % 1 := by
  {
    assume (m n : ℤ) (hne : m ≠ n),
    have h2 : (α * ↑ m) % 1 = (α * ↑ n) % 1 ↔ (α * ↑ m - (α * ↑ m) % 1) = (α * ↑ n - (α * ↑ n) % 1), from
    by {
      rw [←int.fract_eq_iff_eq_or_lt α, ←int.fract_eq_iff_eq_or_lt (α * ↑ m), ←int.fract_eq_iff_eq_or_lt (α * ↑ n),
      int.fract_add_int_eq_add_int_fract (α * ↑ m) (α * ↑ n)] },

    have h3 : (α * ↑ m) % 1 = (α * ↑ n) % 1 ↔ (α * ↑ m) = (α * ↑ n), from
    by {
      rw [h2, int.fract_eq_iff_eq_or_lt (α * ↑ m), int.fract_eq_iff_eq_or_lt (α * ↑ n)],
      rw [←int.fract_add_int_eq_add_int_fract (α * ↑ m) (α * ↑ n), int.fract_add_int_eq_add_int_fract (α * ↑ m) (α * ↑ n)],
      split,
      rintro ⟨rfl,rfl⟩,
      rintro rfl,
      split; linarith,
    },
    have hn : (α * ↑ m) = (α * ↑ n) → m = n, from
    by {
      assume h4 : (α * ↑ m) = (α * ↑ n) ,
      rw [(left_distrib α ↑ m ↑ n), (left_distrib α ↑ m ↑ n)] at h4,
      rw (zero_add α) at h4,
      rw (zero_add α) at h4, linarith,
    },

    exact or.resolve_left (hne) (hn (h3.mp (h2.mp h4))),
  },

  have h2 : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1 :=
  by {
    rintro x (mx : x ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))),
    have h3 : x ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) := mx,
    rw[set.mem_image] at h3,
    cases h3 with m h4,
    cases h4 with h4 h4,
    rw h4, 
    exact int.fract_lt_one (α * ↑m),
  },

  have h3 : ∀ x : ℝ, x ∈ set.Icc 0 1 → ∃ (N : ℕ) (y : ℤ), (N : ℝ) * x ≤ (y : ℝ) ∧ (y + 1) * x ≥ 1 := by
  {
    assume (x : ℝ) (hx : x ∈ set.Icc 0 1),
    have h4 : ∃ (N : ℕ), (N : ℝ) * x > 1 :=
    begin
      have h5 : (1 : ℝ) > ((1 : ℕ) : ℝ) * x ∨ (1 : ℝ) = ((1 : ℕ) : ℝ) * x, from classical.em (((1 : ℕ) : ℝ) * x < (1 : ℝ)),
      cases h5 with h6 h7,
      {
        use 1,
        linarith,
      },
      {
        have h8 : ((1 : ℕ) : ℝ) * x < 1 ∨ ((1 : ℕ) : ℝ) * x = 1, from (not_lt.mp h6),
        cases h8 with h9 h10,
        have h11 : (1 : ℕ) + 1 > (1 : ℝ) * x, from nat.cast_add (1 : ℕ) ▸ h9,
        use 2, linarith,
      },
    end,

    cases h4 with N h5,
    use N,

    cases x with x hx_spec,
    rw set.mem_Icc at hx, cases hx with hx1 hx2,
    have h6 : 0 ≤ x ∧ x < 1 := hx,
    have h7 : x ≤ 1 := le_of_lt h6.right,
    have h8 : ((N : ℕ) : ℝ) * x > 1, from h5,
    have h9 : ((N : ℕ) : ℝ) * x ≤ 1, from le_of_not_gt h8,
    have h10 : ((N : ℕ) : ℝ) * x < 1 + 1, from lt_of_lt_of_le h8 h7,
    have h11 : (N : ℝ) * x < ↑(nat.succ N), from lt_of_lt_of_le h10 (le_refl (1 + 1)),
    have h12 : (N : ℝ) * x ≤ ↑N := le_of_lt_succ h11,
    have h13 : (N : ℝ) * x ≤ nat.succ ↑N := nat.succ_le_succ (le_of_lt_succ h11),
    have h14 : ((N : ℕ) : ℝ) * x < ↑(nat.succ ↑N), from h13,
    have h15 : (N : ℝ) * x ≤ ↑(↑N + 1), from h13,
    have h16 : (N : ℝ) * x < ↑(↑N + 1) := lt_of_le_of_lt h15 h14,
    have h17 : (N : ℝ) * x < ↑(↑N + 1), from h16,
    have h18 : (N : ℝ) * x ≤ ↑N := le_of_not_gt h5,

    have h19 : (↑N + 1 : ℝ) > 0, from nat.cast_add (1 : ℕ) ▸ h6.left,
    have h20 : (↑N + 1 : ℝ) ≥ 0, from zero_le (↑N + 1),

    have h21 : nat.succ N > 0, from nat.cast_lt.mp h19,
    have h22 : nat.succ N ≥ 0, from zero_le (nat.succ N),

    have h23 : (↑N : ℝ) + 1 > ↑N, from nat.cast_add 1 ▸ h21,

    have h24 : (↑N : ℝ) ≤ ↑N + 1, from le_of_not_gt (not_lt_of_ge h22 (nat.succ_pos N)),

    have h25 : (N : ℝ) * x < ↑N + 1, from lt_of_le_of_lt h18 h23,
    have h26 : (N : ℝ) * x < ↑(↑N + 1), from h25,
    have h27 : (N : ℝ) * x < ↑(nat.succ ↑N), from h26,
    have h28 : (N : ℕ) * x < nat.succ ↑N, from nat.cast_lt.mpr h27,
    have h29 : (N : ℕ) * x < nat.succ ↑N, from h28,
    have h30 : (N : ℕ) * x ≤ nat.succ ↑N, from le_of_not_gt (not_lt_of_ge h22 (nat.succ_pos N)),
    have h31 :
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, (int.fract ((α * ↑i))) ≠ (int.fract ((α * ↑j))), from begin
    assume i j : ℤ,
    have h2 := hα_irrat,
    have h3 : irrational (α * ↑i), from by {rintro rfl,exact h2},
    have h4 : irrational (α * ↑j), from by {rintro rfl,exact h2},
    have h5 : (α * ↑i) = (α * ↑j) → ¬ irrational α, 
    from by {
      assume h6 : (α * ↑i) = (α * ↑j), 
      have h7 := eq_of_mul_eq_mul_left (α * ↑i),
      have h8 := eq_of_mul_eq_mul_left (α * ↑j),
      have h9 := @add_left_cancel ℝ (α * ↑i) (↑i) α,
      have h10 := @add_left_cancel ℝ (α * ↑j) (↑j) α,
      have h11 := calc 
                    ↑i = (α * ↑i) - α : by rw [sub_eq_add_neg,sub_eq_add_neg,sub_self]
                   ... = (α * ↑j) - α : by rw [h6,sub_self]
                   ... = ↑j : by simp,

      have h12 := calc 
                    ↑i - ↑j = (α * ↑i) - (α * ↑j) : by simp
                   ... = ↥α * (↑i - ↑j) : by ring,

      rw ↥α at h12,
      rw ↥α at h11,
      have h13 := eq_rat_of_mul_eq_mul_of_ne_zero h12 hα_irrat,
      rwa ↥α at h13,
    },
    have h11 := 
      calc 
      (int.fract ((α * ↑i))) = (int.fract ((α * ↑i) - ↑i))
      : by rw [sub_eq_add_neg,sub_eq_add_neg,sub_self]
      ... = (int.fract ((α * ↑j) - ↑j)) : by rw [add_right_cancel (↑i) (α * ↑i) (α * ↑j),h5 h11],
    exact h11,
  end,

  have h2 : ∀ i : ℤ, (int.fract (α * ↑i)) ∈ set.Icc 0 1, from begin
    assume i : ℤ,
    have h3 := int.fract_within_Icc _ _,
    rw int.fract at h3,
    exact h3,
  end,

  have h3 : ∀ x ∈ (int.fract '' (@set.univ ℤ)), x ∈ (set.Icc 0 1), from by {
    assume (x : ℝ) (h : x ∈ (int.fract '' (@set.univ ℤ))),
    apply h2,
    exact (h.right),
  },

  have h4 : ∀ x : ℝ,  x ∈ (set.Icc 0 1) → x ∈ (int.fract '' (@set.univ ℤ)), from begin
    assume (x : ℝ) (h : x ∈ (set.Icc 0 1)),
    cases (hx : ∃ i : ℤ, x ∈ (int.fract '' (@set.range i))) with (i : ℤ) h0,
    have h1 := h0.left,
    have h2 := set.mem_range.mp h1,
    have h3 : int.fract ↑i ∈ (int.fract '' (@set.range i)), from by {exact set.mem_range.mpr ⟨i,rfl⟩,},
    have h4 := @add_left_cancel ℝ ↑i x (int.fract ↑i),
    have h5 : x = int.fract ((↑i + x) - ↑i), from by {rw [h4,sub_eq_add_neg,sub_eq_add_neg,sub_self],},
    rw ↥ℤ at h2,
    have h6 := int.fract_nonneg (↑i + x),
    have h7 := int.lt_add_one_of_fract_lt_one (↑x),
    have h8 := int.fract_lt_one (↑i + x),
    have h9 := @add_left_cancel ℝ (↑i + x) ↑i (int.fract (↑i + x)),
    have h10 := calc 
                   ↑i + x = ↥(↑i + x) : by rw ↥ℤ
                  ... = ↥(↑i) + x : by simp
                  ... = (int.fract (↑i + x)) + x : by rw [↥ℤ,h9,↥ℤ,int.fract_add_int,int.fract_neg_int,int.fract_zero]
                  ... = int.fract (↑i + x) : by simp,
    cases (eq_or_lt_of_le h8) with h10 h11,
    cases h10 with h12 h13,
    have h11 : x < (1 : ℝ), from by {linarith,},
    cases h11 with h12 h13,
    have h14 : int.fract (↑i + x) = (1 : ℝ), from by {rw [↥ℤ,add_comm,h5,↥ℤ] at h10,exact h10,},
    have h15 := int.fract_add_int (↑i + x),
    have h16 := calc
                  int.fract (↑i + x) = int.fract (↑i + (int.fract (↑i + x) + x - int.fract (↑i + x))) : by rw [↥ℤ,int.fract_add_int,int.fract_add_int,h14,int.fract_int,int.fract_neg_int,int.fract_zero]
                 ... = int.fract (↑i + (1 + x - 1)) : by rw ↥ℤ

    have h17 := int.fract_lt_one (↑i + 1 + x - 1),
    have h18 := calc
                  (1 : ℝ) = int.fract (↑i + 1 + x - 1) - (0 : ℝ)  : by rw [↥ℤ,add_comm,int.fract_add_int,int.fract_add_int,h14,int.fract_int,int.fract_neg_int,int.fract_zero]
                 ... < int.fract (↑i + 1 + x - 1) : by linarith,
    have h19 := int.fract_nonneg (↑i + 1 + x - 1),
    cases (eq_or_lt_of_le h19) with h20 h21,
    cases h20 with h22 h23,
    have h24 := @add_left_cancel ℝ ↑i (1 + x - 1) 
    have h25 : int.fract (↑i + 1 + x - 1) = (1 : ℝ), from by {rw [↥ℤ,add_comm,int.fract_add_int,int.fract_add_int,h14,int.fract_int,int.fract_neg_int,int.fract_zero] at h14,exact h14,},
    exact (1 : ℝ),
    have h20 : int.fract (↑i + 1 + x - 1) < (1 : ℝ), from by {rw [↥ℤ,int.fract_add_int,int.fract_neg_int,int.fract_zero] at h18, exact h18,},
    exact (1 : ℝ),
    have h20 : (1 : ℝ
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let S : set ℝ := {x | ∃ m : ℤ, x = int.fract (α * ↑m)},

  obtain ⟨δ, hδ⟩ : ∃ δ > 0, ∀ x ∈ S.Ico 0 1, ∃ y ∈ S.Ico 0 1, |x - y| < δ := 
  begin
    have hS_infinite : infinite S, from 
    begin
      intros h1,
      obtain ⟨m, hm⟩ := nat.find_min h1,

      have h1 : ∀ m : ℤ, ∃ n : ℤ, α * ↑m = n, from 
        by {intros m, use (m * α), simp [mul_comm],},
      obtain ⟨n, hn⟩ := h1 m,
      have h3 : (α * ↑m) = (α * ↑n), from hn,
      rw [h3, mul_left_inj hα_irrat] at hm,
      rw [hm, nat.find_min_eq_zero] at hm, simp at hm,
      exact absurd hm dec_trivial
    end,
    have hS_closed : is_closed S, from is_closed_finite_inter_Ico ⊤,
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ¬ is_open (finite_inter_Ico ⊤ (insert 0 ((int.fract (α * ↑N)) : finset ℝ))), 
    from mt (is_open_finite_inter_Ico ⊤) hS_infinite,
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ¬ is_open (Ico 0 1 ∩ S), from (hN ⊤).elim,
    let S' : finset ℝ := insert 0 ((int.fract (α * ↑N)) : finset ℝ),
    have hS' : S ∩ Ico 0 1 ⊆ ↑S', from 
    begin
      assume x hx,
      have h1 : x ∈ Ico 0 1 ∧ x ∈ S, from hx,
      have h2 : x ∈ Ico 0 1, from (h1.left),
      have h3 : x ∈ S, from (h1.right),
      have h3 : x = int.fract (α * ↑N), from (h3.elim N),
      have h4 : x = 0 ∨ x = int.fract (α * ↑N), from (eq_or_mem_insert_of_mem h3),
      simp at h4,
      exact (or.elim h4 (λ h5, (or.inl h5)) (λ h6, (or.inr h6))),
    end,
    have hS'_set : ↑S' = {x : ℝ | ∃ (t : ℤ), x = int.fract (α * ↑t) ∧ (x = 0 ∨ x = int.fract (α * ↑N))}, from
    begin
      rw [finset.coe_insert, finset.coe_singleton, finset.coe_union],
      simp,
    end,

    have hS': S' ⊆ S, from 
    begin
      assume x hx,
      obtain ⟨t, ht⟩ := hx,
      have h2 : ∃ (s : ℤ), x = int.fract (α * ↑s), {
        cases ht with h3 ht,
        obtain ⟨s, hs⟩ := h3,
        use s,
        assume h, simp [h] at hs,
        exact absurd hs dec_trivial,
      },
      obtain ⟨s, hs⟩ := h2,
      use s,
      simp [hs, ht],
    end,
    obtain ⟨y, hy⟩ : ∃ y ∈ S, y ∈ (Icc 0 1), from exists_mem_of_ne_empty (ne_empty_of_mem (mem_Icc.2 ⟨zero_lt_one, dec_trivial⟩) S') (mt (is_open_Icc 0 1) hS'),
    obtain ⟨δ, hδ⟩ : ∃ δ > 0, ∀ x ∈ (Icc (y - δ) (y + δ)), x ∈ (Icc 0 1), from exists_is_open_of_mem_nhds (mem_nhds_Icc (y - δ) (y + δ)) (y - δ) (y + δ) (mem_Icc_self 0 1) (hy.right),
    use δ,
    split, exact δ,
    assume x hx, cases (hδ x), split, exact hδ_left, exact hδ_right,
  end,

  have h1 : closure S ⊆ S, from by {

    assume x h1,
    have h2 : ∀ ε > 0, ∃ y ∈ S, |x - y| < ε, from h1,
    show x ∈ S, from
    begin
      assume h3,
      have h4 : ∀ ε > 0, ∃ y ∈ S, |x - y| < ε, from h2,
      have h5 : ∃ y ∈ S, |x - y| < δ, from h4 δ,
      obtain ⟨y, hy⟩ := h5,
      have h6 : δ > 0, exact (hδ).left,
      have h6 : |x - y| < δ, from h6,
      obtain ⟨z, hz⟩ := hδ y hx,
      have h7 : (y - δ) < y, from sub_lt_self y δ,
      have h8 : (y + δ) > y, from add_lt_self y δ,
      have h9 : (y - δ) < z, from lt_of_le_of_lt (hz.left) h7,
      have h10 : z < (y + δ), from lt_of_lt_of_le h8 (hz.right),
      have h11 : z ∈ Icc (y - δ) (y + δ), from mem_Icc.2 ⟨h9, h10⟩,
      have h12 : x = z, simp [h6, h11] at hz, exact hz,
      have h13 : (x - δ) < x, from sub_lt_self x δ,
      have h14 : (x + δ) > x, from add_lt_self x δ,

      have h15 : (x - δ) < y, from lt_of_lt_of_le h13 ((mem_Ico.1 hy).left),
      have h16 : y < (x + δ), from lt_of_le_of_lt ((mem_Ico.1 hy).right) h14,
      have h17 : y ∈ Icc (x - δ) (x + δ), from mem_Icc.2 ⟨h15, h16⟩,
      have h18 := hδ x (h1 h17),
      have h19 : (x - δ) < z, from lt_of_lt_of_le (h18.left) h13,
      have h20 : z < (x + δ), from lt_of_le_of_lt h14 (h18.right),
      have h21 : z ∈ Icc (x - δ) (x + δ), from mem_Icc.2 ⟨h19, h20⟩,
      have h22 : x = z, simp [h6, h21] at hz, exact hz,
      rw h12 at h13, rw h22 at h13,
      exact absurd h13 dec_trivial,
    end
  },

  have h2 : ∀ n : ℤ, 0 ≤
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  sorry,
end

--OUTPUT 10
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := 
begin
    rw closure_univ_eq,
    show (λ (i : ℤ), int.fract (α * i)) '' set.univ ⊆ set.Icc 0 1, 
    from by {
      assume z hz,
      cases hz with x hx,
      rw ← hx,
      show int.fract (α * x) ∈ set.Icc 0 1,
      from by 
      {
        have h1 : int.fract (α * x) < 1, rw [← @add_zero_dt ℤ _ _ _,mul_add,int.fract_eq_int_add_fract,add_assoc],
        exact lt_of_lt_of_le zero_lt_one h1,
        have h2 : 0 ≤ int.fract (α * x), rw [← @zero_add_dt ℤ _ _ _,add_mul,int.fract_eq_int_add_fract,add_assoc],
        exact le_of_lt h2 zero_lt_one,
      },
    },
    show set.Icc 0 1 ⊆ (λ (i : ℤ), int.fract (α * i)) '' set.univ,
    from by {
      assume z hz,
      rw ← @set.mem_univ_iff ℤ _ z,
      use z,
      split,
      swap,
      show int.fract (α * z) = z,
      rw int.fract_eq_int_add_fract, ring,
      cases hz,
      exact hz.left,
    },
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
Squeeze Theorem for Real Numbers
Let $\sequence {x_n}$, $\sequence {y_n}$ and $\sequence {z_n}$ be sequences in $\R$.

Let $\sequence {y_n}$ and $\sequence {z_n}$ both be convergent to the following limit:
:$\ds \lim_{n \mathop \to \infty} y_n = l, \lim_{n \mathop \to \infty} z_n = l$

Suppose that:
:$\forall n \in \N: y_n \le x_n \le z_n$


Then:
:$x_n \to l$ as $n \to \infty$
that is:
:$\ds \lim_{n \mathop \to \infty} x_n = l$

`proof`
From Negative of Absolute Value:
:$\size {x - l} < \epsilon \iff l - \epsilon < x < l + \epsilon$

Let $\epsilon > 0$.

We need to prove that:
:$\exists N: \forall n > N: \size {x_n - l} < \epsilon$

As $\ds \lim_{n \mathop \to \infty} y_n = l$ we know that:
:$\exists N_1: \forall n > N_1: \size {y_n - l} < \epsilon$

As $\ds \lim_{n \mathop \to \infty} z_n = l$ we know that:
:$\exists N_2: \forall n > N_2: \size {z_n - l} < \epsilon$


Let $N = \max \set {N_1, N_2}$.

Then if $n > N$, it follows that $n > N_1$ and $n > N_2$.

So:
:$\forall n > N: l - \epsilon < y_n < l + \epsilon$
:$\forall n > N: l - \epsilon < z_n < l + \epsilon$

But:
:$\forall n \in \N: y_n \le x_n \le z_n$

So:
:$\forall n > N: l - \epsilon < y_n \le x_n \le z_n < l + \epsilon$

and so:
:$\forall n > N: l - \epsilon < x_n < l + \epsilon$

So:
:$\forall n > N: \size {x_n - l} < \epsilon$

Hence the result.
{{qed}}

-/
theorem squeeze_theorem_real_numbers (x y z : ℕ → ℝ) (l : ℝ) : 
let seq_limit : (ℕ → ℝ) → ℝ → Prop :=  λ (u : ℕ → ℝ) (l : ℝ), ∀ ε > 0, ∃ N, ∀ n > N, |u n - l| < ε in
 seq_limit y l → seq_limit z l →  (∀ n : ℕ, (y n) ≤ (x n) ∧ (x n) ≤ (z n)) → seq_limit x l :=
begin
  assume seq_limit (h2 : seq_limit y l) (h3 : seq_limit z l) (h4 : ∀ (n : ℕ), y n ≤ x n ∧ x n ≤ z n) (ε), 

  have h5 : ∀ x, |x - l| < ε ↔ (((l - ε) < x) ∧ (x < (l + ε))), 
  from by 
  {
    intro x0,
    have h6 : |x0 - l| < ε ↔ ((x0 - l) < ε) ∧ ((l - x0) < ε), 
    from abs_sub_lt_iff, rw h6,
    split, 
    rintro ⟨ S_1, S_2 ⟩, 
    split; linarith, 
    rintro ⟨ S_3, S_4 ⟩, 
    split; linarith,
    },
  
  assume (h7 : ε > 0),
  cases h2 ε h7 with N1 h8,
  cases h3 ε h7 with N2 h9,

  let N := max N1 N2,
  use N,

  have h10 : ∀ n > N, n > N1 ∧ n > N2 := by {
    assume n h,
    split,
    exact lt_of_le_of_lt (le_max_left N1 N2) h, 
    exact lt_of_le_of_lt (le_max_right N1 N2) h,
  },
  
  have h11 : ∀ n > N, (((l - ε) < (y n)) ∧ ((y n) ≤ (x n))) ∧ (((x n) ≤ (z n)) ∧ ((z n) < l+ε)), 
  from by {
    intros n h12,
    split,
    {

      have h13 := (h8 n (h10 n h12).left), rw h5 (y n) at h13,
      split,
      exact h13.left,
      exact (h4 n).left,
    },
    {        
      have h14 := (h9 n (h10 n h12).right),rw h5 (z n) at h14,
      split,
      exact (h4 n).right,
      exact h14.right,
    },
    
  },

  have h15 : ∀ n > N, ((l - ε) < (x n)) ∧ ((x n) < (l+ε)), 
  from by {
    intros n1 h16, cases (h11 n1 h16);
    split; linarith,
  },

  show  ∀ (n : ℕ), n > N → |x n - l| < ε, 
  from by {
    intros n h17,
    cases h5 (x n) with h18 h19,
    apply h19, exact h15 n h17,
  },
end


/--`theorem`
Density of irrational orbit
The fractional parts of the integer multiples of an irrational number form a dense subset of the unit interval
`proof`
Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
$$
i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,
$$
which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$. Hence,
$$
S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}
$$
is an infinite subset of $\left[0,1\right]$.

By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$. One can thus find pairs of elements of $S$ that are arbitrarily close. Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.

To show that $S$ is dense in $[0, 1]$, consider $y \in[0,1]$, and $\epsilon>0$. Then by selecting $x \in S$ such that $\{x\}<\epsilon$ (which exists as $0$ is a limit point), and $N$ such that $N \cdot\{x\} \leq y<(N+1) \cdot\{x\}$, we get: $|y-\{N x\}|<\epsilon$.

QED
-/
theorem  irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
FEW SHOT PROMPTS TO CODEX(END)-/
