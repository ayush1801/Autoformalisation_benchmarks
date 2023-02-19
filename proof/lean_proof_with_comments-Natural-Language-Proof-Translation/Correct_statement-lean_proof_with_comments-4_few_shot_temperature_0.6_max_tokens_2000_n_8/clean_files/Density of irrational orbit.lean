import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by {
    assume i j h,
    assume heq : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h2 : (α * ↑i) - ↑(int.nat_abs (α * ↑i)) = (α * ↑j) - ↑(int.nat_abs (α * ↑j)), from by {
      rw heq,
    },
    have h3 : (α * ↑i) - ↑(int.nat_abs (α * ↑i)) = ↑i * α - ↑i * α + (↑(int.nat_abs (α * ↑i)) - ↑i * α), from by {
      rw int.fract_eq_of_nat_abs_add_sub_nat_abs_le (α * ↑i),
    },
    have h4 : (α * ↑j) - ↑(int.nat_abs (α * ↑j)) = ↑j * α - ↑j * α + (↑(int.nat_abs (α * ↑j)) - ↑j * α), from by {
      rw int.fract_eq_of_nat_abs_add_sub_nat_abs_le (α * ↑j),
    },
    have h5 : ↑i * α - ↑i * α + (↑(int.nat_abs (α * ↑i)) - ↑i * α) = ↑j * α - ↑j * α + (↑(int.nat_abs (α * ↑j)) - ↑j * α), from by {
      rw h2,
    },
    have h6 : ↑i * α - ↑i * α = ↑j * α - ↑j * α, from by {
      rw h5,
    },
    have h7 : ↑i * α = ↑j * α, from by {
      rw h6,
    },
    have h8 : i * α = j * α, from by {
      rw h7,
    },
    let h9 : (α = (i/j : ℤ)) ∨ (α = -(i/j : ℤ)), from by {
      apply exists_rat_btwn, exact hα_irrat,
    },
    rw h8 at h9,
    cases h9,
    {
    have h10 : α = i/j, from by {
      rw h9,
    },
    have h11 : α = (j/i : ℤ), from by {
      rw h10,
      rw mul_comm,
      rw int.mul_inv_cancel i,
    },
    have h12 : α = -(i/j : ℤ), from by {
      rw h11,
      rw int.mul_neg_self_iff,
    },
    rw h12 at hα_irrat,
    exact absurd hα_irrat (irrational_of_int_div_int h),
    },
    {
    have h10 : α = -(i/j : ℤ), from by {
      rw h9,
    },
    have h11 : α = (j/i : ℤ), from by {
      rw h10,
      rw mul_comm,
      rw int.mul_inv_cancel i,
    },
    have h12 : α = -(i/j : ℤ), from by {
      rw h11,
      rw int.mul_neg_self_iff,
    },
    rw h12 at hα_irrat,
    exact absurd hα_irrat (irrational_of_int_div_int h),
    },
  },
  have h2 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ∉ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    assume i j h3,
    assume h4 : int.fract (α * ↑i) ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)),
    cases h4 with j h5,
    cases h5 with h6 h7,
    have h8 : int.fract (α * ↑i) = int.fract (α * ↑j), from by {
      rw h7,
    },
    have h9 : i ≠ j, from by {
      exact h1 i j h3 h8,
    },
    exact absurd h3 h9,
  },
  have h3 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from by {
    apply closure_eq_of_is_closed,
    apply is_closed_Icc,
  },
  have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ∈ (set.Icc 0 1), from by {
    assume i j h,
    have h5 : 0 ≤ int.fract (α * ↑i), from by {
      rw int.fract_eq_of_nat_abs_add_sub_nat_abs_le (α * ↑i),
    },
    have h6 : int.fract (α * ↑i) < 1, from by {
      rw int.fract_eq_of_nat_abs_add_sub_nat_abs_le (α * ↑i),
    },
    split,
    exact h5,
    exact h6,
  },
  have h5 : ∀ i : ℤ, (int.fract (α * ↑i)) ∈ (set.Icc 0 1), from by {
    assume i,
    apply h4 i i,
    exact int.ne_of_nat_ne_nat (nat.succ_ne_zero 0),
  },
  have h6 : set.Icc 0 1 = ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    apply set.ext,
    split,
    {
      assume x h7,
      use 0,
      split,
      exact set.mem_univ 0,
      have h8 : int.fract (α * ↑0) = int.fract (α * ↑0), from rfl,
      rw h8,
    },
    {
      assume x h7,
      cases h7 with i h8,
      cases h8 with h9 h10,
      have h11 : int.fract (α * ↑i) = x, from by {
        rw h10,
      },
      rw h11,
      exact h5 i,
    },
  },
  rw h6,
  apply set.ext,
  split,
  {
    assume x h7,
    cases h7 with i h8,
    cases h8 with h9 h10,
    have h11 : int.fract (α * ↑i) = x, from by {
      rw h10,
    },
    rw h11,
    exact h5 i,
  },
  {
    assume x h7,
    use 0,
    split,
    exact set.mem_univ 0,
    have h8 : int.fract (α * ↑0) = int.fract (α * ↑0), from rfl,
    rw h8,
  },
end

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  --$\alpha$ is an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * i) ≠ int.fract (α * j),
  from by {
    assume (i j : ℤ) (hneq : i ≠ j),
    have h2 : int.fract (α * i) = α * i - ⌊α * i⌋, from by {rw int.fract},
    have h3 : int.fract (α * j) = α * j - ⌊α * j⌋, from by {rw int.fract},
    have h4 : i ≠ j → α ≠ (⌊α * i⌋ - ⌊α * j⌋) / (i-j), from by {
      assume hneq1 : i ≠ j,
      assume h5 : α = (⌊α * i⌋ - ⌊α * j⌋) / (i-j),
      have h6 : (⌊α * i⌋ - ⌊α * j⌋) = (i-j) * α, from by {rw h5, ring},
      have h7 : ⌊α * i⌋ = ⌊(i-j) * α⌋, from by {rw ← h6, ring},
      have h8 : ⌊α * j⌋ = ⌊(i-j) * α⌋, from by {rw ← h6, ring},
      have h9 : ⌊(i-j) * α⌋ ∈ ℤ, from by {rw int.cast_coe_int, apply int.cast_le.mp, apply int.floor_nonneg},
      have h10 : ⌊α * i⌋ = ⌊α * j⌋, from by {rw h7, rw h8},
      have h11 : α * i = ⌊α * i⌋, from by {rw int.cast_coe_int, apply int.cast_le.mp, apply int.floor_nonneg},
      have h12 : α * j = ⌊α * j⌋, from by {rw int.cast_coe_int, apply int.cast_le.mp, apply int.floor_nonneg},
      have h13 : α * i = α * j, from by {rw h10, rw h11, rw h12},
      have h14 : i = j, from by {linarith, linarith},
      exact h14 hneq1,
    },
    have h15 : i - j ≠ 0, from by {intro h16, exact hneq (eq_of_sub_eq_zero h16)},
    have h16 : rational ((⌊α * i⌋ - ⌊α * j⌋) / (i-j)), from by {rw ← h2, rw ← h3, apply rational.add_sub_div, apply rational.mul_self_floor, apply rational.mul_self_floor, apply rational.mul_self_floor, apply rational.mul_self_floor, apply irrational.floor_div_irrational, exact hα_irrat, exact h15, exact h15},
    exact hα_irrat h4 h16,
  },

  --If this were not true, then
  --$$
  --i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,
  --$$
  --which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
  --Hence,
  --$$
  --S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}
  --$$
  --is an infinite subset of $\left[0,1\right]$.
  have h2 : ∀ i j : ℤ, i ≠ j → (λ m : ℤ, int.fract (α * m)) i ≠ (λ m : ℤ, int.fract (α * m)) j,
  from by {
    assume (i j : ℤ) (hneq : i ≠ j),
    have h3 : (λ m : ℤ, int.fract (α * m)) i = int.fract (α * i), from by {rw (λ m : ℤ, int.fract (α * m))},
    have h4 : (λ m : ℤ, int.fract (α * m)) j = int.fract (α * j), from by {rw (λ m : ℤ, int.fract (α * m))},
    rw h3, rw h4, exact h1 i j hneq,
  },
  have h3 : (λ m : ℤ, int.fract (α * m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1,
  from by {
    assume x,
    assume h4 : x ∈ (λ m : ℤ, int.fract (α * m)) '' (@set.univ ℤ),
    cases h4 with y h5,
    cases h5 with h6 h7,
    have h8 : (λ m : ℤ, int.fract (α * m)) y = x, from by {rw h7, apply h6},
    have h9 : y ∈ @set.univ ℤ, from by {exact h7},
    rw h8,
    have h10 : 0 ≤ int.fract (α * y), from by {rw h8, apply int.fract_nonneg},
    have h11 : int.fract (α * y) < 1, from by {rw h8, apply int.fract_lt_one},
    split,
    exact h10,
    exact h11,
  },
  have h4 : set.Icc 0 1 ⊆ (λ m : ℤ, int.fract (α * m)) '' (@set.univ ℤ),
  from by {
    assume x,
    assume h5 : x ∈ set.Icc 0 1,
    cases h5 with h6 h7,
    have h8 : ∃ i : ℤ, int.fract (α * i) = x, from by {
      have h9 : ∃ i : ℤ, int.fract (α * i) ≤ x, from by {
        have h10 : ∃ i : ℤ, 0 ≤ int.fract (α * i), from by {
          existsi (0 : ℤ),
          have h11 : (α * (0 : ℤ)) = 0, from by {rw mul_zero},
          rw h11,
          apply int.fract_nonneg,
        },
        existsi (⌈x⌉ : ℤ),
        have h12 : x < int.fract (α * ⌈x⌉), from by {rw int.fract, linarith},
        have h13 : x < α * ⌈x⌉ - ⌊α * ⌈x⌉⌋, from by {rw int.fract, linarith},
        have h14 : x < α * ⌈x⌉, from by {exact lt_of_lt_of_le h13 (int.floor_le _)},
        have h15 : x ≤ ⌈x⌉, from by {apply le_of_lt, exact h14},
        have h16 : x ≤ α * ⌈x⌉, from by {linarith, linarith},
        have h17 : x ≤ int.fract (α * ⌈x⌉), from by {rw int.fract, linarith, linarith},
        exact le_trans h17 (int.fract_le _),
      },
      cases
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * i) ≠ int.fract (α * j),
  from by {
    assume i j,
    assume h2 : i ≠ j,
    assume h3 : int.fract (α * i) = int.fract (α * j),
    have h4 : α * i - (int.fract (α * i)) = int.fract (α * i), from by rw [h3,int.fract_eq_of_lt (by linarith)],
    have h5 : α * j - (int.fract (α * j)) = int.fract (α * j), from by rw [h3,int.fract_eq_of_lt (by linarith)],
    have h6 : α = (int.fract (α * i) - int.fract (α * j)) / (i - j), from by rw [←h4,←h5],
    have h7 : (int.fract (α * i) - int.fract (α * j)) / (i - j) ∈ ℚ, from by apply quotient.exact h6,
    have h8 : α ∈ ℚ, from by apply rational_iff_exists_rat.mp h7,
    have h9 : irrational α, from by assumption,
    contradiction,
  },

  -- Hence, $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$ is an infinite subset of $\left[0,1\right]$.
  have h10 : ∀ i : ℤ, int.fract (α * i) ∈ set.Icc 0 1, from by {
    assume i : ℤ,
    have h11 : ↑i * α - ↑(int.fract (α * i)) = int.fract (α * i), from by apply int.fract_eq_of_lt (by linarith),
    have h12 : ↑i * α - int.fract (α * i) < ↑i * α, from by linarith,
    have h13 : 0 < int.fract (α * i), from by linarith,
    have h14 : 0 ≤ int.fract (α * i) ∧ int.fract (α * i) < 1, from by rw [←h11,int.fract_lt_one],
    exact set.mem_Icc.mpr h14,
  },
  have h15 : set.finite (∅ : set ℤ), from by apply set.finite_empty,
  have h16 : set.finite {z : ℤ | z = 0}, from by apply set.finite_singleton,
  have h17 : set.finite {z : ℤ | z = -1}, from by apply set.finite_singleton,
  have h18 : set.finite {z : ℤ | z = 1}, from by apply set.finite_singleton,
  have h19 : set.finite {z : ℤ | (0 < z) ∧ (z < 1)}, from by apply set.finite_Ico,
  have h20 : set.finite {z : ℤ | (z < 0) ∧ (-1 < z)}, from by apply set.finite_Icc,
  have h21 : set.finite {z : ℤ | (z < 0) ∧ (z < -1)}, from by apply set.finite_Icc,
  have h22 : set.finite {z : ℤ | (0 < z) ∧ (1 < z)}, from by apply set.finite_Ico,
  have h23 : set.finite {z : ℤ | z = -2}, from by apply set.finite_singleton,
  have h24 : set.finite {z : ℤ | z = 2}, from by apply set.finite_singleton,
  have h25 : set.finite {z : ℤ | (z < -2) ∧ (-3 < z)}, from by apply set.finite_Icc,
  have h26 : set.finite {z : ℤ | (z < -3) ∧ (-4 < z)}, from by apply set.finite_Icc,
  have h27 : set.finite {z : ℤ | (z < -4) ∧ (-5 < z)}, from by apply set.finite_Icc,
  have h28 : set.finite {z : ℤ | (z < -5) ∧ (-6 < z)}, from by apply set.finite_Icc,
  have h29 : set.finite {z : ℤ | (z < -6) ∧ (-7 < z)}, from by apply set.finite_Icc,
  have h30 : set.finite {z : ℤ | (z < -7) ∧ (-8 < z)}, from by apply set.finite_Icc,
  have h31 : set.finite {z : ℤ | (z < -8) ∧ (-9 < z)}, from by apply set.finite_Icc,
  have h32 : set.finite {z : ℤ | (z < -9) ∧ (-10 < z)}, from by apply set.finite_Icc,
  have h33 : set.finite {z : ℤ | (2 < z) ∧ (z < 3)}, from by apply set.finite_Ico,
  have h34 : set.finite {z : ℤ | (3 < z) ∧ (z < 4)}, from by apply set.finite_Ico,
  have h35 : set.finite {z : ℤ | (4 < z) ∧ (z < 5)}, from by apply set.finite_Ico,
  have h36 : set.finite {z : ℤ | (5 < z) ∧ (z < 6)}, from by apply set.finite_Ico,
  have h37 : set.finite {z : ℤ | (6 < z) ∧ (z < 7)}, from by apply set.finite_Ico,
  have h38 : set.finite {z : ℤ | (7 < z) ∧ (z < 8)}, from by apply set.finite_Ico,
  have h39 : set.finite {z : ℤ | (8 < z) ∧ (z < 9)}, from by apply set.finite_Ico,
  have h40 : set.finite {z : ℤ | (9 < z) ∧ (z < 10)}, from by apply set.finite_Ico,
  have h41 : set.finite {z : ℤ | (10 < z) ∧ (z < 11)}, from by apply set.finite_Ico,
  have h42 : set.finite {z : ℤ | (11 < z) ∧ (z < 12)}, from by apply set.finite_Ico,
  have h43 : set.finite {z : ℤ | (12 < z) ∧ (z < 13)}, from by apply set.finite_Ico,
  have h44 : set.finite {z : ℤ | (13 < z) ∧ (z < 14)}, from by apply set.finite_Ico,
  have h45 : set.finite {z : ℤ | (14 < z) ∧ (z < 15)}, from by apply set.finite_Ico,
  have h46 : set.finite {z : ℤ | (15 < z) ∧ (z < 16)}, from by apply set.finite_Ico,
  have h47 : set.finite {z : ℤ | (16 < z) ∧ (z < 17)}, from by apply set.finite_Ico,
  have h48 : set.finite {z : ℤ | (17 < z) ∧ (z < 18
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ m n : ℤ, ↑(m * n) = (↑m : ℝ) * n, from by {
    assume m n : ℤ,
    have h1 : (↑m : ℝ) * n = ↑m * n, from by {
      have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
        have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
          have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
            have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
              have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                  have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                    have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                      have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                        have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                          have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                            have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                              have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                  have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                    have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                      have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                        have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                          have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                            have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                              have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                  have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                    have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                      have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                        have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                          have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                            have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                              have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                  have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                    have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                      have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                        have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                          have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                            have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                              have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                  have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                    have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                      have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                        have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                          have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                            have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                              have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                  have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                    have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                      have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                        have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                          have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                            have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                              have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                  have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                    have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                      have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                        have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                          have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                            have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                              have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                                have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                                  have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                                    have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                                      have h1 : (↑m : ℝ) * n = ↑m * ↑n, from by {
                                                                                                                                        have h1 : (↑m : ℝ
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  --By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  let S : set ℝ := {int.fract (α * ↑m) | m : ℤ},
  have h1 : ∃ x : ℝ, x ∈ closure S, from by {
    have h2 : ∀ m n : ℤ, m ≠ n → (int.fract (α * ↑m)) ≠ int.fract (α * ↑n), from by {
      assume m n hmn,
      have h3 : m ≠ n, from by {
        cases hmn, exact hmn,
      },
      have h4 : α ≠ ↑n / ↑m, from by {
        rw hmn at hα_irrat, exact hα_irrat,
      },
      have h5 : (α * ↑m) ≠ (α * ↑n), from by {
        rw mul_comm (α * ↑m) (α * ↑n),
        rw mul_assoc α ↑m ↑n,
        rw mul_comm ↑m ↑n,
        rw mul_assoc ↑m α ↑n,
        rw mul_comm ↑m α,
        rw mul_assoc ↑m ↑n α,
        rw mul_comm ↑n α,
        rw mul_assoc ↑n ↑m α,
        rw hmn,
        rw mul_comm ↑m ↑n,
        rw ← mul_assoc,
        rw mul_comm α,
        rw mul_inv_cancel α,
        rw mul_one,
        rw mul_comm ↑n ↑m,
        rw h4,
        rw mul_comm ↑n ↑m,
        rw mul_one,
      },
      exact int.fract_ne_of_ne h5,
    },
    exact exists_mem_of_finite_image_ne_empty h2,
  },

  --One can thus find pairs of elements of $S$ that are arbitrarily close. 
  have h2 : ∀ ε > 0, ∃ x y ∈ S, ∀ z ∈ S, |z - x| < ε ∧ |z - y| < ε, from by {
    assume ε hε,
    cases h1 with x hx,
    cases (mem_closure_iff.1 hx ε hε) with h3 h4,
    cases h3 with y hy,
    use x, use y,
    intros z hz,
    rw [mem_image, exists_prop],
    use z,
    split,
    exact hz,
    have h5 : ∀ z' ∈ S, ∃ m : ℤ, z' = int.fract (α * ↑m), from by {
      assume z' hz',
      rw mem_image at hz',
      rcases hz' with ⟨m, rfl⟩,
      use m,
      exact rfl,
    },
    cases h4 z with h6 h7,
    rcases (h5 z h6) with ⟨m, rfl⟩,
    rcases (h5 y hy) with ⟨n, rfl⟩,
    have h8 : ∀ m n : ℤ, m ≠ n → (int.fract (α * ↑m)) ≠ int.fract (α * ↑n), from by {
      assume m n hmn,
      have h9 : m ≠ n, from by {
        cases hmn, exact hmn,
      },
      have h10 : α ≠ ↑n / ↑m, from by {
        rw hmn at hα_irrat, exact hα_irrat,
      },
      have h11 : (α * ↑m) ≠ (α * ↑n), from by {
        rw mul_comm (α * ↑m) (α * ↑n),
        rw mul_assoc α ↑m ↑n,
        rw mul_comm ↑m ↑n,
        rw mul_assoc ↑m α ↑n,
        rw mul_comm ↑m α,
        rw mul_assoc ↑m ↑n α,
        rw mul_comm ↑n α,
        rw mul_assoc ↑n ↑m α,
        rw hmn,
        rw mul_comm ↑m ↑n,
        rw ← mul_assoc,
        rw mul_comm α,
        rw mul_inv_cancel α,
        rw mul_one,
        rw mul_comm ↑n ↑m,
        rw h10,
        rw mul_comm ↑n ↑m,
        rw mul_one,
      },
      exact int.fract_ne_of_ne h11,
    },
    have h12 : (int.fract (α * ↑m)) ≠ int.fract (α * ↑n), from by {
      apply h8, exact h7,
    },
    have h13 : (α * ↑m) ≠ (α * ↑n), from by {
      exact int.fract_ne_of_ne h12,
    },
    have h14 : ↑m ≠ ↑n, from by {
      intro h,
      rw [← mul_assoc, mul_comm ↑m ↑n, h] at h13,
      have h15 : (α * ↑n) = (α * ↑m), from h13,
      have h16 : ↑n = ↑m, from by {
        rw ← mul_assoc,
        rw mul_comm ↑n α,
        rw mul_inv_cancel α,
        rw mul_one,
      },
      contradiction,
    },
    have h17 : (int.fract (α * ↑n)) = z, from by {
      rw int.fract_mul,
      rw int.fract_mul,
      rw mul_comm ↑n α,
      rw mul_assoc ↑n ↑m α,
      rw ← mul_assoc,
      rw mul_comm ↑n ↑m,
      rw h16,
      rw mul_assoc ↑m α ↑n,
      rw mul_comm ↑m α,
      rw ← mul_assoc,
      rw mul_comm α ↑m,
      rw mul_inv_cancel α,
      rw mul_one,
    },
    have h18 : (int.fract (α * ↑m)) = y, from by {
      rw int.fract_mul,
      rw int.fract_mul,
      rw mul_comm ↑m α,
      rw mul_assoc ↑m ↑n α,
      rw ← mul_assoc,
      rw mul_comm ↑m ↑n,
      rw h16,
      rw mul_assoc ↑n α ↑m,
      rw mul_comm ↑n α,
      rw ← mul_assoc,
      rw mul_comm α ↑n,
      rw mul_inv_cancel α,
      rw mul_one,
    },
    have h19 : (int.fract (α * ↑m)) - (int.fract (α * ↑n)) = y - z, from by {
      rw h17,
      rw h18,
    },
    have h20 : ↑m - ↑n = (y - z) / α, from by {
      rw [← mul_assoc, mul_comm α ↑n, mul_assoc α ↑n ↑m, ← mul_assoc] at h19,
      rw mul_comm α ↑m at h19,
      rw ← mul_assoc at h19,
      rw mul_comm ↑m α at h19,
      rw mul_inv_cancel α at h19,
      rw mul_one at h19,
      rw h19,
      rw mul_sub,
      rw mul_comm ↑m ↑n,
      rw mul_sub,
      rw mul_comm ↑m ↑n,
    },
    have h21 : ↑m - ↑n ≠ 0, from by {
      linarith,
    },
    have h
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin 
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j),
  from by {
    assume i j : ℤ,
    assume h2 : i ≠ j,
    assume h3 : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h4 : α = (int.fract (α * ↑i)) / (i-j), from by {
      rw h3,
      have h5 : (int.fract (α * ↑i)) / (i-j) = ((α * ↑i) - int.nat_abs (α * ↑i)) / (i-j), from by {
        rw int.fract_def, 
        have h6 : int.nat_abs (α * ↑i) = int.nat_abs ((α * ↑i) - ((α * ↑i) - int.nat_abs (α * ↑i))), from by {
          apply int.nat_abs_of_nonneg,
          rw int.nat_abs_of_nonneg,
          linarith,
        },
        rw h6, ring,
      },
      rw h5, ring,
    },
    have h5 : α ∈ ℚ, from by {
      have h6 := (set.mem_rat.mpr (⟨α, h4⟩ : ℚ × ℚ)),
      apply set.mem_rat_iff.mp h6,
      },
    apply irrational.not_mem_of_mem_rat hα_irrat h5,
  },

  --$S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$
  --$S$ is an infinite subset of $\left[0,1\right]$.
  have h2 : infinite ((λ m : ℤ, int.fract (α * ↑m)) '' set.univ), from by {
    have h3 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h4 : i ≠ j,
      have h5 : int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
        rw set.not_mem_singleton,
        apply h1 i j h4,
      },
      exact h5,
    },
    have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by {
      assume i j : ℤ,
      assume h5 : i ≠ j,
      apply h3 i j h5,
    },
    have h5 : ∀ i j : ℤ, i ≠ j → ↑i ≠ ↑j, from by {
      assume i j : ℤ,
      assume h6 : i ≠ j,
      apply int.cast_ne_int.mpr h6,
    },
    have h6 : ∀ i j : ℤ, i ≠ j → ↑i ≠ ↑j, from by {
      assume i j : ℤ,
      assume h7 : i ≠ j,
      apply h5 i j h7,
    },
    have h7 : ∀ i j : ℤ, i ≠ j → (α * ↑i) ≠ (α * ↑j), from by {
      assume i j : ℤ,
      assume h8 : i ≠ j,
      apply int.cast_ne_int.mpr h8,
    },
    have h8 : ∀ i j : ℤ, i ≠ j → (α * ↑i) ≠ (α * ↑j), from by {
      assume i j : ℤ,
      assume h9 : i ≠ j,
      apply h7 i j h9,
    },
    have h9 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h10 : i ≠ j,
      apply h4 i j h10,
    },
    have h10 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h11 : i ≠ j,
      apply h9 i j h11,
    },
    have h11 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h12 : i ≠ j,
      apply h10 i j h12,
    },
    have h12 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h13 : i ≠ j,
      apply h11 i j h13,
    },
    have h13 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h14 : i ≠ j,
      apply h12 i j h14,
    },
    have h14 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h15 : i ≠ j,
      apply h13 i j h15,
    },
    have h15 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h16 : i ≠ j,
      apply h14 i j h16,
    },
    have h16 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h17 : i ≠ j,
      apply h15 i j h17,
    },
    have h17 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h18 : i ≠ j,
      apply h16 i j h18,
    },
    have h18 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h19 : i ≠ j,
      apply h17 i j h19,
    },
    have h19 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h20 : i ≠ j,
      apply h18 i j h20,
    },
    have h20 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h21 : i ≠ j,
      apply h19 i j h21,
    },
    have h21 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume i j : ℤ,
      assume h22 : i ≠ j,
     
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  --Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (i * α) ≠ int.fract (j * α), from assume (i j : ℤ) (h2 : i ≠ j), 
  by {
    rw [int.fract_eq, int.fract_eq] at h2,
    have h3 : α = (int.nat_abs (i - j))⁻¹ * (i * α - j * α), from by {
      rw mul_comm,
      rw sub_mul,
      rw h2,
      ring,
    },
    rw [int.nat_abs_of_nonneg (le_of_lt (int.coe_nat_pos.2 hα_irrat))] at h3,
    have h4 : α ∈ ℚ, from by {
      rw int.coe_nat_dvd,
      use (i - j),
      simp [h3],
    },
    have h5 : irrational α, from hα_irrat,
    have h6 : ¬(α ∈ ℚ), from h5,
    contradiction,
  },
  --If this were not true, then
  --$$
  --i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,
  --$$
  --which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
  --Hence,
  --$$
  --S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}
  --$$
  --is an infinite subset of $\left[0,1\right]$.
  have h7 : set.infinite ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    have h8 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume (i j : ℤ) (h9 : i ≠ j),
      rw [mul_comm α i, mul_comm α j] at h9,
      exact h1 i j h9,
    },
    have h9 : ∀ (i j : ℤ), i ≠ j → (λ m : ℤ, int.fract (α * ↑m)) i ≠ (λ m : ℤ, int.fract (α * ↑m)) j, from by {
      assume (i j : ℤ) (h10 : i ≠ j),
      rw [eq_comm, ← function.funext_iff],
      exact h8 i j h10,
    },
    show set.infinite ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from
    by {
      apply set.infinite_of_injective_of_univ,
      exact h9,
      exact set.univ_mem_univ,
    },
  },
  --By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  have h10 : set.has_limit_point ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) (Icc 0 1), from by {
    apply set.has_limit_point_of_infinite_of_compact_of_nonempty,
    exact h7,
    exact is_compact_Icc,
    simp,
  },
  --One can thus find pairs of elements of $S$ that are arbitrarily close.
  have h11 : ∀ (ε : ℝ), ε > 0 → ∃ (x y : ℤ), x ≠ y ∧ (λ m : ℤ, int.fract (α * ↑m)) x ≠ (λ m : ℤ, int.fract (α * ↑m)) y ∧ int.fract (α * ↑y) - int.fract (α * ↑x) < ε, from by {
    assume (ε : ℝ) (h12 : ε > 0),
    apply set.has_limit_point.has_limit_point_of_finite_cover,
    exact h10,
    exact h12,
    exact set.univ_mem_univ,
    use (set.Icc 0 1),
    use (set.Ioo (ε / 2) (1 - (ε / 2))),
    split,
    {
      rw [← set.image_univ],
      rw [← set.image_univ],
      apply set.finite_inter_finite,
      apply set.finite_Icc,
      apply set.finite_Ioo,
    },
    {
      rw [← set.image_univ],
      rw [← set.image_univ],
      apply set.finite_inter_finite,
      apply set.finite_Icc,
      apply set.finite_Ioo,
    },
    {
      rw [← set.image_univ],
      rw [← set.image_univ],
      rw [← set.image_univ],
      rw [← set.image_univ],
      apply set.finite_inter_finite,
      apply set.finite_Icc,
      apply set.finite_Ioo,
    },
    {
      rw [← set.image_inter],
      rw [← set.image_inter],
      rw [← set.image_inter],
      rw [← set.image_inter],
      intros x h13,
      cases h13 with x1 h14,
      cases h14 with x2 h15,
      cases h15 with h16 h17,
      cases h17 with h18 h19,
      cases h19 with h20 h21,
      cases h21 with h22 h23,
      cases h23 with h24 h25,
      cases h25 with h26 h27,
      cases h27 with h28 h29,
      cases h29 with h30 h31,
      cases h31 with h32 h33,
      cases h33 with h34 h35,
      cases h35 with h36 h37,
      cases h37 with h38 h39,
      cases h39 with h40 h41,
      cases h41 with h42 h43,
      cases h43 with h44 h45,
      cases h45 with h46 h47,
      cases h47 with h48 h49,
      cases h49 with h50 h51,
      cases h51 with h52 h53,
      cases h53 with h54 h55,
      cases h55 with h56 h57,
      cases h57 with h58 h59,
      cases h59 with h60 h61,
      cases h61 with h62 h63,
      cases h63 with h64 h65,
      cases h65 with h66 h67,
      cases h67 with h68 h69,
      cases h69 with h70 h71,
      cases h71 with h72 h73,
      cases h73 with h74 h75,
      cases h75 with h76 h77,
      cases h77 with h78 h79,
      cases h79 with h80 h81,
      cases h81 with h82 h83,
      cases h83 with h84 h85,
      cases h85 with h86 h87,
      cases h87 with h88 h89,
      cases h89 with h90 h91,
      cases h91 with h92 h93,
      cases h93 with h94 h95,
      cases h95 with h96 h97,
      cases h97 with h98 h99,
     
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- let S := $\{\{i \alpha\} \mid i \in \mathbb{Z}\}$
  have h1 : ∀ m : ℤ, int.fract (α * ↑m) ∈ set.Icc 0 1, by {
    assume m,
    have h1_1 : 0 ≤ int.fract (α * ↑m), by linarith,
    have h1_2 : int.fract (α * ↑m) ≤ 1, by linarith,
    show int.fract (α * ↑m) ∈ set.Icc 0 1, from ⟨h1_1,h1_2⟩,
  },
  have h2 : ∀ m : ℤ, int.fract (α * ↑m) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), by {
    assume m,
    have h2_1 : (m : ℤ) ∈ set.univ, from set.mem_univ m,
    show int.fract (α * ↑m) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from ⟨m, h2_1⟩,
  },
  let S := (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ),

  -- then S is infinite set
  have h3 : infinite S, from by {
    have h3_1 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
      begin
        assume i j,
        assume h3_1_1,
        have h3_1_2 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) * (i - j)⁻¹, from by {
          rw ← int.fract_add_int,
          rw ← mul_int_fract,
          rw ← mul_int_fract,
          ring,
        },
        have h3_1_3 : ((i - j) : ℤ) ≠ 0, from by {
          assume h3_1_3_1,
          have h3_1_3_2 := int.eq_iff_exists_int.mpr h3_1_3_1,
          cases h3_1_3_2,
          have h3_1_3_3 := int.cast_inj.mp h3_1_3_2_h,
          rw h3_1_3_3 at h3_1_2,
          have h3_1_3_4 : α ∈ ℚ, from by {
            exact h3_1_2.symm,
          },
          have h3_1_3_5 : α ∉ ℚ, from by {
            apply hα_irrat,
          },
          exact h3_1_3_5 h3_1_3_4,
        },
        have h3_1_4 : (i - j)⁻¹ ∈ ℚ, from by {
          exact inv_in_rational (int.cast_ne_zero.mp h3_1_3),
        },
        have h3_1_5 : (i - j)⁻¹ ∉ ℚ, from by {
          apply hα_irrat,
        },
        exact h3_1_5 h3_1_4,
      end,
    have h3_1_1 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from 
      begin
        assume i j,
        assume h3_1_1_1,
        have h3_1_1_2 := h3_1 i j h3_1_1_1,
        show int.fract (α * ↑i) ≠ int.fract (α * ↑j),
        from h3_1_1_2,
      end,
    have h3_1_2 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ⁻¹ ≠ (int.fract (α * ↑j)) ⁻¹, from 
      begin
        assume i j,
        assume h3_1_2_1,
        have h3_1_2_2 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
          by {exact h3_1_1_1 i j h3_1_2_1},
        rw int.fract_eq_of_ne at h3_1_2_2,
        show (int.fract (α * ↑i)) ⁻¹ ≠ (int.fract (α * ↑j)) ⁻¹,
        from by {
          exact inv_ne_of_ne_of_ne h3_1_2_2 h3_1_2_2,
        },
      end,
    have h3_1_3 : ∀ (i j : ℤ), (int.fract (α * ↑i)) ⁻¹ ≠ (int.fract (α * ↑j)) ⁻¹ → i ≠ j, from 
      begin
        assume i j,
        assume h3_1_3_1,
        have h3_1_3_2 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
          by {exact inv_ne_of_ne_of_ne h3_1_3_1 h3_1_3_1},
        rw int.fract_eq_of_ne at h3_1_3_2,
        show i ≠ j, from h3_1_1_1 i j h3_1_3_2,
      end,
    have h3_1_4 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ⁻¹ ≠ (int.fract (α * ↑j)) ⁻¹, from 
      begin
        assume i j,
        assume h3_1_4_1,
        have h3_1_4_2 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
          by {exact h3_1_1_1 i j h3_1_4_1},
        rw int.fract_eq_of_ne at h3_1_4_2,
        show (int.fract (α * ↑i)) ⁻¹ ≠ (int.fract (α * ↑j)) ⁻¹, from
          by {exact inv_ne_of_ne_of_ne h3_1_4_2 h3_1_4_2},
      end,
    have h3_1_5 : ∀ (i j : ℤ), (int.fract (α * ↑i)) ⁻¹ = (int.fract (α * ↑j)) ⁻¹ → i = j, from 
      begin
        assume i j,
        assume h3_1_5_1,
        have h3_1_5_2 : int.fract (α * ↑i) = int.fract (α * ↑j), from
          by {exact inv_inj h3_1_5_1},
        show i = j, from int.fract_eq_of_eq h3_1_5_2,
      end,
    have h3_1_6 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ⁻¹ ≠ (int.fract (α * ↑j)) ⁻¹, from 
      begin
        assume i j,
        assume h3_1_6_1,
        have h3_1_6_2 : int.fract (α * ↑i) ≠ int.fract (α * ↑j
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

  --From Negative of Absolute Value: $\size {x - l} < \epsilon \iff l - \epsilon < x < l + \epsilon$
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
  
  --Let $\epsilon > 0$.
  assume (h7 : ε > 0),

  --As $\ds \lim_{n \mathop \to \infty} y_n = l$ we know that $\exists N_1: \forall n > N_1: \size {y_n - l} < \epsilon$
  cases h2 ε h7 with N1 h8,

  --As $\ds \lim_{n \mathop \to \infty} z_n = l$ we know that $\exists N_2: \forall n > N_2: \size {z_n - l} < \epsilon$
  cases h3 ε h7 with N2 h9,
  
  --Let $N = \max \set {N_1, N_2}$.
  let N := max N1 N2,
  use N,

  --Then if $n > N$, it follows that $n > N_1$ and $n > N_2$.
  have h10 : ∀ n > N, n > N1 ∧ n > N2 := by {
    assume n h,
    split,
    exact lt_of_le_of_lt (le_max_left N1 N2) h, 
    exact lt_of_le_of_lt (le_max_right N1 N2) h,
  },
  
  --$\forall n > N: l - \epsilon < y_n < l + \epsilon$
  --$\forall n > N: l - \epsilon < z_n < l + \epsilon$
  --$\forall n \in \N: y_n \le x_n \le z_n$
  --So $\forall n > N: l - \epsilon < y_n \le x_n \le z_n < l + \epsilon$
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

  --$\forall n > N: l - \epsilon < x_n < l + \epsilon$
  have h15 : ∀ n > N, ((l - ε) < (x n)) ∧ ((x n) < (l+ε)), 
  from by {
    intros n1 h16, cases (h11 n1 h16);
    split; linarith,
  },

  --So $\forall n > N: \size {x_n - l} < \epsilon$
  --Hence the result
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
