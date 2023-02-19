import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let f : ℤ → ℝ := λ m : ℤ, int.fract (α * ↑m),
  let S : set ℝ := {x : ℝ | ∃ m : ℤ, x = int.fract (α * ↑m)},
  let T : set ℝ := f '' (@set.univ ℤ),

  have h1 : ∀ i j : ℤ, i ≠ j → f i ≠ f j, from by {
    assume i j : ℤ,
    have h2 : ∀ m n : ℤ, m ≠ n → α ≠ ↑m / ↑n, from by {
        assume m n : ℤ,
        assume h3 : m ≠ n,
        assume h4 : α = ↑m / ↑n,
        have h5 := eq_rat α (↑m / ↑n),
        have h6 := h5 h4,
        cases h6 with h7 h8,
        rw h7 at h3,
        exact h3 rfl,
      },
    assume h3 : i ≠ j,
    assume h4 : f i = f j,
    have h5 : α = ↑i / ↑j, from by {
      rw h4,
      rw mul_comm,
      apply mul_fract,
    },
    have h6 := h2 i j h3,
    exact h6 h5,
  },
  
  have h2 : ∀ i j : ℤ, i ≠ j → S i ≠ S j, from by {
    assume i j : ℤ,
    assume h1 : i ≠ j,
    assume h2 : S i = S j,
    cases h2 with h3 h4,
    have h5 := h1 h3,
    exact h5 rfl,
  },

  have h3 : ∀ i : ℤ, S i ∈ set.Icc 0 1, from by {
    assume i : ℤ,
    have h1 : α * ↑i - floor (α * ↑i) = int.fract (α * ↑i), from by {
      rw mul_comm,
      apply mul_fract,
    },
    have h2 : 0 ≤ α * ↑i - floor (α * ↑i), from by {
      rw h1,
      apply int.fract_nonneg,
    },
    have h3 : α * ↑i - floor (α * ↑i) < 1, from by {
      rw h1,
      apply int.fract_lt_one,
    },
    use h2, use h3,
  },

  have h4 : ∀ x ∈ S, ∃ y ∈ S, 0 < ↑x - ↑y ∧ ↑x - ↑y < 1, from by {
    assume x : ℝ,
    assume h1 : x ∈ S,
    cases h1 with i h2,
    have h3 : 0 < ↑i + 1 - ↑i, from by {
      rw h2,
      have h4 : 0 ≤ ↑i + 1 - ↑i, from by {
        apply sub_nonneg,
        apply nat.cast_le.mpr,
        apply le_succ,
      },
      have h5 : ↑i + 1 - ↑i < 1, from by {
        apply sub_lt_one,
        apply nat.cast_le.mpr,
        apply le_succ,
      },
      split, exact h4, exact h5,
    },
    use i + 1,
    use h3,
    have h4 : int.fract (α * ↑(i + 1)) = int.fract (α * ↑i + α), from by apply mul_fract,
    have h5 : int.fract (α * ↑i + α) = int.fract (α * ↑i) + α - floor (α * ↑i + α), from by apply add_fract,
    have h6 : int.fract (α * ↑(i + 1)) = int.fract (α * ↑i) + α - floor (α * ↑i + α), from by rw ← h4 at h5,
    have h7 : int.fract (α * ↑(i + 1)) = int.fract (α * ↑i) + (α - floor (α * ↑i + α)), from by rw add_comm at h6,
    have h8 : int.fract (α * ↑(i + 1)) = int.fract (α * ↑i) + (α - floor (α * ↑i)), from by rw ← mul_add (1 : ℝ) α ↑i at h7,
    have h9 : int.fract (α * ↑(i + 1)) = x + (α - floor (α * ↑i)), from by rw h2 at h8,
    have h10 : int.fract (α * ↑(i + 1)) = x + (α - floor (α * ↑i)), from by rw ← h2 at h9,
    have h11 : x + (α - floor (α * ↑i)) = ↑(i + 1) - floor (α * ↑(i + 1)), from by rw h2 at h10,
    have h12 : x + (α - floor (α * ↑i)) = ↑i + 1 - floor (α * ↑(i + 1)), from by rw add_comm at h11,
    have h13 : x + (α - floor (α * ↑i)) = ↑i + 1 - floor (α * ↑i + α), from by rw mul_add (1 : ℝ) α ↑i at h12,
    have h14 : x + (α - floor (α * ↑i)) = ↑i + 1 - floor (α * ↑i) - α, from by rw add_comm at h13,
    have h15 : x + (α - floor (α * ↑i)) = ↑i + 1 - (floor (α * ↑i) + α), from by rw sub_add_eq_sub_sub at h14,
    have h16 : x + (α - floor (α * ↑i)) = ↑i + 1 - ↑i, from by rw floor_add at h15,
    have h17 : x + (α - floor (α * ↑i)) = 1, from by rw add_sub_cancel at h16,
    have h18 : x = 1 - (α - floor (α * ↑i)), from by rw h17,
    have h19 : x = 1 - (α - floor (α * ↑i)), from by rw ← add_sub_assoc at h18,
    have h20 : x = 1 - ↑i + floor (α * ↑i), from by rw ← sub_sub at h19,
    have h21 : x = 1 - ↑i + int.fract (α * ↑i), from by rw h2 at h20,
    have h22 : x = 1 - ↑i + x, from by rw h2 at h21,
    have h23 : ↑i + x = 1 + x, from by rw ← h22,
    have h24 : ↑i = 1, from by rw sub_add_cancel at h23,
    have h25 : i = 1, from by rw int.cast_eq_coe at h24,
    have h26 : i ≠ 1, from by {
      assume h27 : i = 1,
      have h28 := h1 h27,
      exact h28 rfl,
    },
    exact h26 rfl,
  },

  have h5 : ∀ x ∈ T, ∃ y ∈ T, 0 < ↑x - ↑y ∧ ↑x - ↑y < 1, from by {
    assume x : ℝ,
    assume h1 : x ∈ T,
    cases h1 with i h2,
    have h3 : f i ∈ S, from by {
      use i,
      exact h2,
    },
    cases h4 (f i) h3 with j h4,
    use j,
    use h4,
  },

  have h6 : ∀ x ∈ set.Icc 0 1, ∃ y ∈ T, 0 < x - y ∧ x - y < 1, from by {
    assume x : ℝ,
    assume h1 : x ∈ set.
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * i) ≠ int.fract (α * j), from 
  begin 
    assume i j h,
    assume h_eq : int.fract (α * i) = int.fract (α * j),
    have h2 : α = (int.fract (α * i) + int.floor (α * i)) / (i - j), from 
      by {rw [mul_comm i α, mul_comm j α, int.fract_add_floor (α * i), int.fract_add_floor (α * j), h_eq], ring},
    have h3 : (int.fract (α * i) + int.floor (α * i)) / (i - j) ∈ ℚ, from sorry,
    rw ← h3 at h2, contradiction,
  end,

  have h2 : ∀ i j : ℤ, i ≠ j → int.fract (α * i) - int.fract (α * j) ≠ 0, from
  begin
    assume i j h,
    assume h_eq : int.fract (α * i) - int.fract (α * j) = 0,
    have h_eq2 : int.fract (α * i) = int.fract (α * j), from by {rw h_eq, ring},
    have h_eq3 : i ≠ j, from by rw ← h_eq2 at h; assumption,
    have h_eq4 : int.fract (α * i) ≠ int.fract (α * j), from h h_eq3,
    have h_eq5 : int.fract (α * i) - int.fract (α * j) ≠ 0, from by rw h_eq4; linarith,
    show int.fract (α * i) - int.fract (α * j) ≠ 0, from h_eq5,
  end,

  have h3 : ∀ i : ℤ, int.fract (α * i) ∈ set.Icc 0 1, from 
  begin
    assume i,
    have h4 : 0 ≤ int.fract (α * i) ∧ int.fract (α * i) ≤ 1, from 
    begin
      split,
      apply int.fract_nonneg,
      apply int.fract_le_one,
    end,
    show int.fract (α * i) ∈ set.Icc 0 1, from set.mem_Icc.2 h4,
  end,

  have h4 : ∀ i : ℤ, int.fract (α * i) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from 
  begin
    assume i,
    have h5 : ∀ n : ℕ, ∃ j : ℤ, int.fract (α * i) = int.fract (α * ↑j) ∧ (j - i) / ↑n ∈ ℤ, from 
    begin
      assume n,
      have h6 : int.fract (α * i) = int.fract (α * ↑(i + (n * ↑(int.floor (α * ↑(i + 1)) - int.floor (α * ↑i))))), 
      from by simp [int.fract_add_floor],
      use (i + (n * ↑(int.floor (α * ↑(i + 1)) - int.floor (α * ↑i)))),
      split,
      exact h6,
      rw int.cast_add,
      rw int.cast_mul, 
      exact int.coe_nat_dvd (int.floor (α * ↑(i + 1)) - int.floor (α * ↑i)) n,
    end,
    have h7 : ∀ n : ℕ, ∃ j : ℤ, int.fract (α * i) = int.fract (α * ↑j) ∧ (j - i) / ↑n ∈ ℤ ∧ j ≠ i, from 
    begin
      assume n,
      cases h5 n with j hj,
      use j,
      split,
      exact hj.1,
      split,
      exact hj.2,
      rw ← hj.1 at h2,
      have h8 : (j - i) / ↑n ≠ 0, from 
      begin
        assume h8,
        have h9 : j - i = 0, from by rw [int.cast_coe_nat, int.cast_coe_nat] at h8; exact h8,
        have h10 : j ≠ i, from by rw h9; linarith,
        show j ≠ i, from h10,
      end,
      exact h8,
    end,
    have h8 : ∀ m : ℕ, ∃ j : ℤ, int.fract (α * i) = int.fract (α * ↑j) ∧ (j - i) / ↑m ∈ ℤ ∧ j ≠ i, from 
    begin
      assume m,
      induction m with m' hm',
      cases h7 1 with j hj,
      use j,
      split,
      exact hj.1,
      split,
      exact hj.2,
      exact hj.3,
      cases hj.3 with hj1 hj2,
      cases hm' hj2 with j' hj',
      use j',
      split,
      exact hj'.1,
      split,
      exact hj'.2,
      exact hj'.3,
    end,
    have h9 : ∀ m : ℕ, ∃ j : ℤ, int.fract (α * i) = int.fract (α * ↑j) ∧ (j - i) / ↑m ∈ ℤ ∧ j ≠ i ∧ j ≠ 0, from 
    begin
      assume m,
      cases h8 m with j hj,
      cases hj.3 with hj1 hj2,
      cases hj2 with hj3 hj4,
      use j,
      split,
      exact hj.1,
      split,
      exact hj.2,
      split,
      exact hj.3,
      exact hj.4,
    end,
    have h10 : ∀ m : ℕ, ∃ j : ℤ, int.fract (α * i) = int.fract (α * ↑j) ∧ (j - i) / ↑m ∈ ℤ ∧ j ≠ i ∧ j ≠ 0 ∧ j < m, from 
    begin
      assume m,
      cases h9 m with j hj,
      use j,
      split,
      exact hj.1,
      split,
      exact hj.2,
      split,
      exact hj.3,
      split,
      exact hj.4,
      split,
      exact hj.5,
      rw [int.cast_coe_nat, int.cast_coe_nat] at hj.5,
      have h11 : (j - i) / ↑m > 0, from by {exact int.coe_nat_pos.2 hj.5},
      have h12 : int.fract (α * i) - int.fract (α * ↑j) < 1, from by {rw hj.1, exact int.fract_lt_one},
      have h13 : int.fract (α * i) - int.fract (α * ↑j) > -1, from by {rw hj.1, simp [int.fract_add_floor]},
      have h14 : int.fract (α * i) - int.fract (α * ↑j) = int.fract (α * ↑j) - int.fract (α * i), from by rw hj.1; ring,
      have h15 : int.fract (α * ↑j) - int.fract (α * i) < 1, from by rw h14; exact h12,
      have h16 : int.fract (α
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (m : ℤ) (n : ℤ), (m ≠ n) → (int.fract (α * ↑m) ≠ int.fract (α * ↑n)), from 
  begin
    assume m n h2,
    assume h3 : (int.fract (α * ↑m)) = (int.fract (α * ↑n)),
    have h4 : α = (int.fract (α * ↑m)) + (int.floor (α * ↑m)), from by {rw int.fract_def, rw int.floor_add_one, ring},
    have h5 : α = (int.fract (α * ↑n)) + (int.floor (α * ↑n)), from by {rw int.fract_def, rw int.floor_add_one, ring},
    have h6 : α = (int.floor (α * ↑m)) - (int.floor (α * ↑n)), from by {rw [h3, h5, h4], ring},
    have h7 : (int.floor (α * ↑m)) - (int.floor (α * ↑n)) = (α * ↑m) - (α * ↑n), from by {rw int.floor_mul, rw int.floor_mul, ring},
    have h8 : α = (α * ↑m) - (α * ↑n), from by {rw h6, ring},
    have h9 : α = α * (↑m - ↑n), from by {rw h8, ring},
    have h10 : ((α ≠ 0) ∧ (↑m - ↑n ≠ 0)), from by {split, exact hα_irrat, rw int.coe_nat_eq_coe_int_iff at h2, exact h2},
    have h11 : (↑m - ↑n) ∈ @set.univ ℤ, from by {apply set.mem_univ _,},
    have h12 : (↑m - ↑n) ∈ (@set.univ ℤ), from by {exact h11,},
    have h13 : (↑m - ↑n) ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by 
    {
      use (↑m - ↑n),
      split,
      {exact h12,},
      {
        have h14 : (int.fract (α * ↑m)) - (int.fract (α * ↑n)) = (int.fract (α * ↑(m - n))), from by {
          have h15 : (int.fract (α * ↑m)) - (int.fract (α * ↑n)) = (int.fract ((α * ↑m) - (α * ↑n))), from by {rw [← int.fract_sub, h3, int.fract_zero],},
          have h16 : (int.fract ((α * ↑m) - (α * ↑n))) = (int.fract (α * ↑(m - n))), from by {rw h8, ring,},
          exact h16,
        },
        have h17 : (int.fract (α * ↑(m - n))) = (int.fract (α * ↑(↑m - ↑n))), from by {rw int.coe_nat_eq_coe_int_iff,},
        rw [h17, h14, int.fract_zero],
      },
    },
    have h14 : 0 ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by {exact set.mem_closure h13},
    have h15 : (0 : ℝ) ∈ (set.Icc 0 1), from by {apply set.mem_Icc, linarith,},
    have h16 : (0 : ℝ) ∈ set.Icc 0 1, from by {exact h15,},
    have h17 : set.Icc 0 1 = (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by {
      apply set.subset.antisymm,
      {
        apply set.subset_Icc,
      },
    {
      apply set.subset_closure,
    },
  },
  have h18 : set.Icc 0 1 = closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {exact h17,},
  exact absurd h16 h18,
  },
  },
  have h2 : ∀ (n : ℤ), (int.fract (α * ↑n)) ∈ set.Icc 0 1, from by {
    assume n,
    have h3 : (int.fract (α * ↑n)) ∈ set.Icc 0 1, from by {
      apply set.mem_Icc,
      linarith,
    },
    exact h3,
  },
  have h3 : ∀ (n : ℤ), (int.fract (α * ↑n)) ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by {
    assume n,
    have h4 : (int.fract (α * ↑n)) ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by {
      have h5 : (int.fract (α * ↑n)) ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
        use n,
        split,
        {
          apply set.mem_univ _,
        },
        {
          rw int.fract_mul,
          ring,
        },
      },
      apply set.mem_closure,
      exact h5,
    },
    exact h4,
  },
  have h4 : set.Icc 0 1 ⊆ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by {
    apply set.subset.antisymm,
    {
      intros x h5,
      cases h5 with h6 h7,
      rw h6 at h7,
      cases (classical.em (∃ n : ℤ, x = int.fract (α * ↑n))),
      {
        cases a with n h8,
        rw h8,
        apply h3,
      },
      {
        have h9 : x = 0, from by {
          have h10 : x ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by {apply set.mem_closure, exact h7,},
          have h11 : x ∈ set.Icc 0 1, from by {apply set.mem_Icc, linarith,},
          have h12 : set.Icc 0 1 = (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by {exact h17,},
          rw h12 at h10,
          exact absurd h10 h11,
        },
        rw h9,
        apply h3,
      },
    },
    {
      apply set.subset_closure,
    },
  },
  exact h4,
end

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h : ∀ m n : ℤ, (int.fract (α * ↑m)) ≠ (int.fract (α * ↑n)) := by {
    assume (m n : ℤ), assume hmn : (int.fract (α * ↑m)) = (int.fract (α * ↑n)),
    have h1 : (α * ↑m) - ↑(int.floor (α * ↑m)) = (α * ↑n) - ↑(int.floor (α * ↑n)), from by {rw hmn},
    have h2 : α = (int.floor (α * ↑m) - int.floor (α * ↑n))/(m - n), from by {rw h1, ring},
    have h3 : (m - n) ≠ 0, from by {intro h4, have h5 := eq_zero_of_mul_self_right h4, contradiction},
    have h6 : (int.floor (α * ↑m) - int.floor (α * ↑n))/(m - n) ∈ ℚ, from by {apply quotient.mk_div_mk, exact h3},
    have h7 := hα_irrat.ne_of_mem h6, exact h7 h2,
  },
  have h_inj : ∀ m n : ℤ, int.fract (α * ↑m) = int.fract (α * ↑n) → m = n, from by {
    assume (m n : ℤ) (hmn : int.fract (α * ↑m) = int.fract (α * ↑n)),
    have h1 := exists_eq_mul_right_of_dvd (dvd_sub _ _) (int.fract_nonneg (α * ↑m)),
    have h2 := exists_eq_mul_right_of_dvd (dvd_sub _ _) (int.fract_nonneg (α * ↑n)),
    rw hmn at h1, rw hmn at h2,
    cases h1 with k1 h3, cases h2 with k2 h4,
    have h5 : α * ↑m = (α * ↑m - ↑k1) + ↑k1, from by {rw h3, ring},
    have h6 : α * ↑n = (α * ↑n - ↑k2) + ↑k2, from by {rw h4, ring},
    have h7 : α * ↑m = α * ↑n, from by {rw h5, rw h6, ring},
    have h8 := mul_left_inj hα_irrat h7, exact h8 rfl,
  },
  have h_fract : ∀ m : ℤ, int.fract (α * ↑m) ∈ set.Icc 0 1, from by {
    assume m,
    have h1 : (α * ↑m) - ↑(int.floor (α * ↑m)) < 1, from by {rw ← int.fract_lt_one (α * ↑m), refl},
    have h2 : 0 ≤ (α * ↑m) - ↑(int.floor (α * ↑m)), from by {rw ← int.fract_nonneg (α * ↑m), refl},
    exact ⟨h2,h1⟩,
  },
  have h_fract_conv : ∀ m : ℤ, is_closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    assume m,
    have h1 : ∀ m n : ℤ, (int.fract (α * ↑m) = int.fract (α * ↑n)) ↔ (m = n), from by {
      assume (m n : ℤ), split, exact h_inj m n,
      assume hmn, rw hmn,
    },
    have h2 : ∀ m n : ℤ, (int.fract (α * ↑m) = int.fract (α * ↑n)) → is_open ((λ m : ℤ, int.fract (α * ↑m)) '' (set.Ico m n)), from by {
      assume (m n : ℤ) (hmn : int.fract (α * ↑m) = int.fract (α * ↑n)),
      have h3 : (int.fract (α * ↑m)) ∈ set.Icc 0 1, from h_fract m,
      have h4 : ∀ m n : ℤ, int.fract (α * ↑m) ∈ set.Icc 0 1 ∧ m < n → is_open ((λ m : ℤ, int.fract (α * ↑m)) '' (set.Ico m n)), from by {
        assume (m n : ℤ), assume hmn,
        have h5 := set.Ico_subset_Ico_iff.mp hmn.right, 
        have h6 : ∀ k : ℤ, k ∈ set.Ico (m + 1) n → int.fract (α * ↑m) ≠ int.fract (α * ↑k), from by {
          assume k (hk : k ∈ set.Ico (m + 1) n),
          have h7 : k > m, from by {apply lt_of_le_of_lt, exact h5.left, exact hk},
          have h8 : (α * ↑m) = (α * ↑k), from by {rw ← hmn.left, ring},
          have h9 := h_inj m k h8,
          have h10 : k = m, from by {apply h9.symm,},
          have h11 : k > m, from by {rw h10, exact h7,},
          have h12 : k ≥ m + 1, from by {apply le_of_lt, exact h11},
          have h13 : k < m + 1, from by {apply lt_of_le_of_lt, exact h12, exact h7},
          contradiction,
        },
        have h7 : ∀ k : ℤ, k ∈ set.Ico (m + 1) n → ∃ ϵ > 0, ∀ j : ℤ, j ∈ set.Ico (k - ϵ) (k + ϵ) → int.fract (α * ↑m) ≠ int.fract (α * ↑j), from by {
          assume k (hk : k ∈ set.Ico (m + 1) n),
          have h8 : ∀ j : ℤ, j ∈ set.Ico (k - 1) (k + 1) → int.fract (α * ↑m) ≠ int.fract (α * ↑j), from by {
            assume j (hj : j ∈ set.Ico (k - 1) (k + 1)),
            have h9 : int.fract (α * ↑m) ≠ int.fract (α * ↑k), from by {apply h6 k hk,},
            have h10 : int.fract (α * ↑k) ≠ int.fract (α * ↑j), from by {apply h6 k hj,},
            have h11 : int.fract (α * ↑m) ≠ int.fract (α * ↑j), from by {apply ne.trans h9 h10,},
            exact h11,
          },
          have h9 : ∃ ϵ > 0, ∀ j : ℤ, j ∈ set.Ico (k - ϵ) (k + ϵ) → int.fract (α * ↑m) ≠ int.fract (α * ↑j), from by {
            use (1 : ℝ), split, exact dec_trivial, exact h8,
          },
          exact h9,
        },
        have h8 : ∀ k : ℤ, k ∈ set.Ico (m + 1) n → ∃ ϵ > 0, ∀ j : ℤ, ∃ k : ℤ, j ∈ set.Ico (k - ϵ) (k + ϵ) → int.fract (α * ↑m) ≠ int.fract (α * ↑j), from by {
          assume k (hk : k ∈ set.Ico (m + 1) n),
          cases h7 k hk with ϵ
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j),
  from begin
    assume i j hij,
    have h2 : α * ↑i - int.floor (α * ↑i) = int.fract (α * ↑i), from rfl,
    have h3 : α * ↑j - int.floor (α * ↑j) = int.fract (α * ↑j), from rfl,
    have h4 : int.fract (α * ↑i) = int.fract (α * ↑j), from eq.trans h2.symm (eq.trans h3 h2),
    have h5 : α = ((int.floor (α * ↑i) - int.floor (α * ↑j)) / (i - j)), from by linarith,
    have h6 : i - j ≠ 0, from by linarith,
    have h7 : (int.floor (α * ↑i) - int.floor (α * ↑j)) / (i - j) ∈ ℚ, from by linarith,
    have h8 : α ∈ ℚ, from eq.trans h5 h7,
    have h9 : irrational α, from hα_irrat,
    have h10 : ¬(α ∈ ℚ), from h9.irrat,
    exact absurd h8 h10,
  end,
  have h2 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod set.univ set.univ,
  from begin
    assume i j hij,
    have h3 : (i,j) ∉ set.prod set.univ set.univ, from by linarith,
    have h4 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (int.fract (α * ↑i),α * ↑i - int.floor (α * ↑i)), from by linarith,
    have h5 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (int.fract (α * ↑j),α * ↑j - int.floor (α * ↑j)), from by linarith,
    have h6 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (α * ↑i - int.floor (α * ↑i),int.fract (α * ↑j)), from by linarith,
    have h7 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (α * ↑j - int.floor (α * ↑j),int.fract (α * ↑i)), from by linarith,
    have h8 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (int.fract (α * ↑j),α * ↑j - int.floor (α * ↑j)), from by linarith,
    have h9 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (α * ↑j - int.floor (α * ↑j),int.fract (α * ↑i)), from by linarith,
    have h10 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (α * ↑i - int.floor (α * ↑i),int.fract (α * ↑j)), from by linarith,
    have h11 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (int.fract (α * ↑i),α * ↑i - int.floor (α * ↑i)), from by linarith,
    have h12 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (α * ↑i - int.floor (α * ↑i),α * ↑j - int.floor (α * ↑j)), from by linarith,
    have h13 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (α * ↑j - int.floor (α * ↑j),α * ↑i - int.floor (α * ↑i)), from by linarith,
    have h14 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (α * ↑j - int.floor (α * ↑j),α * ↑j - int.floor (α * ↑j)), from by linarith,
    have h15 : (int.fract (α * ↑i),int.fract (α * ↑j)) = (α * ↑i - int.floor (α * ↑i),α * ↑i - int.floor (α * ↑i)), from by linarith,
    have h16 : (int.fract (α * ↑i),int.fract (α * ↑j)) ∈ set.prod set.univ set.univ, from by linarith,
    have h17 : (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod set.univ set.univ, from absurd h16 h3,
    exact h17,
  end,
  have h3 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod (int.fract (α * ↑i)) (int.fract (α * ↑j)),
  from begin
    assume i j hij,
    have h4 : (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod (int.fract (α * ↑i)) (int.fract (α * ↑j)), from by linarith,
    exact h4,
  end,
  have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod (α * ↑i - int.floor (α * ↑i)) (α * ↑j - int.floor (α * ↑j)),
  from begin
    assume i j hij,
    have h5 : (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod (α * ↑i - int.floor (α * ↑i)) (α * ↑j - int.floor (α * ↑j)), from by linarith,
    exact h5,
  end,
  have h5 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod (α * ↑j - int.floor (α * ↑j)) (α * ↑i - int.floor (α * ↑i)),
  from begin
    assume i j hij,
    have h6 : (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod (α * ↑j - int.floor (α * ↑j)) (α * ↑i - int.floor (α * ↑i)), from by linarith,
    exact h6,
  end,
  have h6 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod (α * ↑j - int.floor (α * ↑j)) (α * ↑j - int.floor (α * ↑j)),
  from begin
    assume i j hij,
    have h7 : (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod (α * ↑j - int.floor (α * ↑j)) (α * ↑j - int.floor (α * ↑j)), from by linarith,
    exact h7,
  end,
  have h7 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i),int.fract (α * ↑j)) ∉ set.prod (α * ↑i - int.floor (α * ↑i)) (α *
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i ∈ @set.univ ℤ, ∃ (n : ℤ), (α * ↑i) - ↑n ∈ set.Ioi 0, from 
    assume i hij,
    have h2 : (α * ↑i) - ↑(int.floor (α * ↑i)) ∈ set.Ioi 0, from int.fract_lt_one (α * ↑i),
    use int.floor (α * ↑i),
    exact h2,
  have h3 : ∀ i j ∈ @set.univ ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
    assume i j hij hijj hneq,
    have h4 : (α * ↑i) - (α * ↑j) ≠ 0, from by {rw [int.sub_eq_zero_of_eq,mul_comm] at hneq, exact hneq},
    have h5 : (α * ↑i) - (α * ↑j) = α * (↑i - ↑j), from by ring, rw h5 at h4,
    have h6 : (α : ℝ) ≠ 0, from by {rw [← int.cast_inj,int.sub_eq_zero_of_eq,int.cast_zero] at h4, exact h4},
    have h7 : (↑i - ↑j) ≠ 0, from mul_ne_zero hα_irrat h6,
    have h8 : (α * ↑i) ≠ (α * ↑j), from by {rw [mul_sub,sub_eq_zero] at h7, exact h7},
    have h9 : (α * ↑i) - ↑(int.floor ((α * ↑i))) ≠ (α * ↑j) - ↑(int.floor ((α * ↑j))), from by {linarith},
    show int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {rw [← int.sub_eq_zero_of_eq,← int.sub_eq_zero_of_eq] at h9, exact h9},
  have h10 : int.fract (α * ↑i) ∈ set.Icc 0 1, from by {rw ← int.fract_lt_one, exact int.fract_nonneg (α * ↑i)},
  have h11 : (λ (i : ℤ), int.fract (α * ↑i)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by {rw ← set.image_subset_iff, exact h10},
  have h12 : ∀ n : ℤ, n ∈ (λ (i : ℤ), int.fract (α * ↑i)) '' (@set.univ ℤ) → n ∈ set.Icc 0 1, from 
    assume n hn, rw h11, exact hn,
  have h13 : ∀ n : ℤ, n ∈ set.Icc 0 1 → ∃ (i : ℤ), i ∈ (@set.univ ℤ) ∧ int.fract (α * ↑i) = n, from 
    assume n hn,
    have h14 : n ∈ set.Ioi 0, from by {rw ← set.mem_Icc at hn, exact hn},
    have h15 : n ∈ set.Ioi 0 → ∃ (i : ℤ), (α * ↑i) - ↑(int.floor (α * ↑i)) = n, from 
      assume h16,
      have h17 : ∃ (i : ℤ), (α * ↑i) - ↑(int.floor (α * ↑i)) = n, from 
        begin
          rw [← set.mem_Ioi at h16,int.sub_eq_zero_iff] at h16,
          have h18 : ∃ (i : ℤ), (α * ↑i) = ↑(int.floor (α * ↑i)) + n, from 
            begin
              rw h16, use int.floor (α * ↑i), ring,
            end,
          cases h18 with i h18,
          have h19 : (α * ↑i) - ↑(int.floor (α * ↑i)) = n, from by {rw h18, ring},
          use i, exact h19,
        end,
      use int.floor (α * ↑i),
      have h17 : (α * ↑i) - ↑(int.floor (α * ↑i)) = n, from h17,
      rw [int.sub_eq_zero_iff] at h17,
      have h18 : (α * ↑i) = ↑(int.floor (α * ↑i)) + n, from by {rw h17, ring},
      have h19 : (α * ↑i) = ↑(int.floor (α * ↑i)) + n → ∃ (i : ℤ), (α * ↑i) = ↑(int.floor (α * ↑i)) + n, from 
        assume h20, use int.floor (α * ↑i), exact h20,
      have h20 : ∃ (i : ℤ), (α * ↑i) = ↑(int.floor (α * ↑i)) + n, from h19 h18,
      cases h20 with i h20,
      have h21 : (α * ↑i) = ↑(int.floor (α * ↑i)) + n, from h20,
      have h22 : (α * ↑i) - ↑(int.floor (α * ↑i)) = n, from by {rw h21, ring},
      use i, exact h22,
    have h18 : ∃ (i : ℤ), (α * ↑i) - ↑(int.floor (α * ↑i)) ∈ set.Ioi 0, from h15 h14,
    cases h18 with i h18,
    have h19 : (α * ↑i) - ↑(int.floor (α * ↑i)) ∈ set.Ioi 0, from h18,
    have h20 : (α * ↑i) - ↑(int.floor (α * ↑i)) ∈ set.Ioi 0 → ∃ (i : ℤ), (α * ↑i) - ↑(int.floor (α * ↑i)) ∈ set.Ioi 0, from 
      assume h21, use int.floor (α * ↑i), exact h21,
    have h21 : ∃ (i : ℤ), (α * ↑i) - ↑(int.floor (α * ↑i)) ∈ set.Ioi 0, from h20 h19,
    cases h21 with i h21,
    have h22 : (α * ↑i) - ↑(int.floor (α * ↑i)) ∈ set.Ioi 0, from h21,
    have h23 : (α * ↑i) - ↑(int.floor (α * ↑i)) = n, from by {rw [← set.mem_Ioi at h22,int.sub_eq_zero_iff] at h22,rw h22, ring},
    have h24 : int.fract (α * ↑i) = n, from by {rw [← int.sub_eq_zero_of_eq,← int.sub_eq_zero_of_eq] at h23, rw h23, ring},
    have h25 : i ∈ set.univ, from set.mem_univ i,
    use i,
    exact ⟨h25, h24⟩,
  have h14 : (λ (i : ℤ), int.fract (α * ↑i)) '' (@set.univ ℤ) = set.Icc 0 1, from 
    set.image_eq_preimage h13 h12,
  have h15 : (λ (i : ℤ), int.fract (α * ↑i)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from 
    by {rw ← h14, rw ← set.image_subset_iff, exact h10},
  have h16 : closure ((λ (i : ℤ), int.fract (α * ↑i)) '' (@set.univ ℤ)) ⊆ set.
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (m n : ℤ), m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n), 
  from assume (m n : ℤ) (h2 : m ≠ n), 
  by {
    assume h3 : int.fract (α * ↑m) = int.fract (α * ↑n),
    have h4 : α = (int.floor (α * ↑n) - int.floor (α * ↑m)) / (n - m), 
    from by {
      rw ← int.fract_eq_sub_floor at h3,
      rw ← int.fract_eq_sub_floor at h3,
      rw h3,
      ring,
    },
    have h5 : α ∈ int.rat, by {apply int.rat_eq_of_int h4,},
    have h6 : irrational α, from hα_irrat,
    have h7 : irrational α ∧ irrational α, by {split,exact h6,exact h6,},
    show false, from h7.elim h5,
  },
  
  have h8 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), by {
    have h10 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from h1 m n h9,
    have h11 : int.fract (α * ↑m) = (λ m : ℤ, int.fract (α * ↑m)) m, obviously,
    have h12 : int.fract (α * ↑n) = (λ m : ℤ, int.fract (α * ↑m)) n, obviously,
    rw h11 at h10, rw h12 at h10, exact h10,
  },
  
  have h13 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), h8 m n h9,
  have h14 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), h8 n m (ne.symm h9),
  have h15 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), (or.elim (decidable.em (m < n))
    (assume h10 : m < n, h14 m n h10)
    (assume h10 : ¬ m < n, h13 m n (ne.symm h10))),

  have h16 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), or.resolve_right (decidable.em (n < m)) h9
    (assume (h10 : ¬ n < m), h15 m n (ne.symm h10)),
  have h17 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), or.resolve_left (decidable.em (n < m)) h9
    (assume (h10 : ¬ n < m), h13 m n h10),
  have h18 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), (or.elim (decidable.em (m < n))
    (assume h10 : m < n, h16 m n h10)
    (assume h10 : ¬ m < n, h17 m n (ne.symm h10))),
  
  have h19 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), or.resolve_right (decidable.em (n < m)) h9
    (assume (h10 : ¬ n < m), h18 m n (ne.symm h10)),
  have h20 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), or.resolve_left (decidable.em (n < m)) h9
    (assume (h10 : ¬ n < m), h16 m n h10),
  have h21 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), (or.elim (decidable.em (m < n))
    (assume h10 : m < n, h20 m n h10)
    (assume h10 : ¬ m < n, h19 m n (ne.symm h10))),
  
  have h22 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), or.resolve_right (decidable.em (n < m)) h9
    (assume (h10 : ¬ n < m), h21 m n (ne.symm h10)),
  have h23 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), or.resolve_left (decidable.em (n < m)) h9
    (assume (h10 : ¬ n < m), h20 m n h10),
  have h24 : ∀ (m n : ℤ), m ≠ n → (λ m : ℤ, int.fract (α * ↑m)) m ≠ (λ m : ℤ, int.fract (α * ↑m)) n,
  from assume (m n : ℤ) (h9 : m ≠ n), (or.elim (decidable.em (m < n))
    (assume h10 : m < n, h23 m n h
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by {
    assume x hx, 
    show x ∈ set.Icc 0 1, from by {
      cases hx with i hi,
      rw hi,
      show int.fract (α * ↑i) ∈ set.Icc 0 1, from by {
        have h2 : (0 : ℝ) ≤ int.fract (α * ↑i), from by {apply int.fract_nonneg,},
        have h3 : int.fract (α * ↑i) < 1, from by {apply int.fract_lt_one,},
        split, exact h2, exact h3,
      },
    },
  },
  
  have h2 : ∀ (x : ℤ), (int.fract (α * ↑x)) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    assume x,
    show int.fract (α * ↑x) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
      show int.fract (α * ↑x) ∈ closure ((int.fract ∘ (λ (m : ℤ), α * ↑m)) '' (@set.univ ℤ)), from by {
        show int.fract (α * ↑x) ∈ closure ((int.fract ∘ (λ (m : ℤ), α * ↑m)) '' (@set.univ ℤ)), from by {
          show int.fract (α * ↑x) ∈ closure (int.fract '' ((λ (m : ℤ), α * ↑m) '' (@set.univ ℤ))), from by {
            have h3 : ((λ (m : ℤ), α * ↑m) '' (@set.univ ℤ)) = ((λ (m : ℤ), (@int.cast ℝ ℤ) (α * ↑m)) '' (@set.univ ℤ)), from by {
              show (λ (m : ℤ), α * ↑m) '' (@set.univ ℤ) = (λ (m : ℤ), (@int.cast ℝ ℤ) (α * ↑m)) '' (@set.univ ℤ), from by {
                apply set.ext,
                assume y,
                split;
                rintro ⟨ z, hz ⟩,
                {
                  rw hz,
                  show (α * ↑z) ∈ (λ (m : ℤ), (@int.cast ℝ ℤ) (α * ↑m)) '' (@set.univ ℤ), from by {
                    use z,
                    show α * ↑z = (@int.cast ℝ ℤ) (α * ↑z), from by {
                      rw ← int.cast_coe,
                      rw ← int.coe_nat_mul,
                      rw int.coe_nat_one,
                      ring,
                    },
                  },
                },
                {
                  rw hz,
                  show (α * ↑z) ∈ (λ (m : ℤ), (α * ↑m)) '' (@set.univ ℤ), from by {
                    use z,
                    show α * ↑z = (α * ↑z), from by {
                      rw ← int.coe_nat_mul,
                      rw int.coe_nat_one,
                      ring,
                    },
                  },
                },
              },
            },
            rw h3,
            show int.fract (α * ↑x) ∈ closure (int.fract '' (λ (m : ℤ), (@int.cast ℝ ℤ) (α * ↑m)) '' (@set.univ ℤ)), from by {
              show int.fract (α * ↑x) ∈ closure (int.fract '' (λ (m : ℤ), (@int.cast ℝ ℤ) (α * ↑m)) '' (@set.univ ℤ)), from by {
                show int.fract (α * ↑x) ∈ closure (int.fract '' (λ (m : ℤ), (@int.cast ℝ ℤ) (α * ↑m)) '' ((@set.univ ℤ))), from by {
                  show int.fract (α * ↑x) ∈ closure (int.fract '' (λ (m : ℤ), (@int.cast ℝ ℤ) (α * ↑m)) '' set.univ), from by {
                    show int.fract (α * ↑x) ∈ closure ((int.fract ∘ (λ (m : ℤ), (@int.cast ℝ ℤ) (α * ↑m))) '' (@set.univ ℤ)), from by {
                      show int.fract (α * ↑x) ∈ closure ((int.fract ∘ (λ (m : ℤ), (@int.cast ℝ ℤ) (α * ↑m))) '' (@set.univ ℤ)), from by {
                        show int.fract (α * ↑x) ∈ closure (int.fract '' (λ (m : ℤ), (@int.cast ℝ ℤ) (α * ↑m)) '' (@set.univ ℤ)), from by {
                          show int.fract (α * ↑x) ∈ closure (int.fract '' (@set.univ ℝ)), from by {
                            show int.fract (α * ↑x) ∈ closure (int.fract '' set.univ), from by {
                              have h4 : int.fract (α * ↑x) ∈ set.univ, from by {
                                show int.fract (α * ↑x) ∈ set.univ, from by {
                                  apply set.mem_univ,
                                },
                              },
                              exact set.mem_closure_of_mem h4,
                            },
                          },
                        },
                      },
                    },
                  },
                },
              },
            },
          },
        },
      },
    },
  },
  
  have h3 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from by {
    apply set.closure_mono,
    apply h1,
  },
  
  show closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from by {
    apply set.subset.antisymm,
    show closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from by {
      apply set.closure_mono,
      apply h1,
    },
    show set.Icc 0 1 ⊆ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
      rw ← set.univ_Icc,
      apply set.closure_mono,
      apply set.univ_subset_iff.mpr,
      apply h2,
    },
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
