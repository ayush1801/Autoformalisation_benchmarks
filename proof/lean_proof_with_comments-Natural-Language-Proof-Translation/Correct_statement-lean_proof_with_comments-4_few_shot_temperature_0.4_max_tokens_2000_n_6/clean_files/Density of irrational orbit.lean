import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from assume i j h,
  begin
    assume h2,
    have h3 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
      rw [← int.fract_add_int (α * ↑i), ← int.fract_add_int (α * ↑j), ← int.fract_mul α i, ← int.fract_mul α j, ← int.fract_add_int (α * ↑i), ← int.fract_add_int (α * ↑j), int.fract_eq_of_eq h2],
      ring,
    },
    have h4 : (i - j) ≠ 0, from by {
      assume h5,
      rw [h5, sub_self] at h3,
      have h6 : α = 0, from by {
        rw [← int.fract_eq_of_eq h3, int.fract_zero],
      },
      exact absurd h6 hα_irrat,
    },
    have h7 : (i - j) ∈ @set.univ ℤ, from by {
      rw [set.mem_univ],
    },
    have h8 : (i - j) ∈ set.range (λ (m : ℤ), int.fract (α * ↑m)), from by {
      rw [set.mem_range],
      use (int.fract (α * ↑(i - j))),
      rw [← int.fract_mul α (i - j), ← int.fract_add_int (α * ↑i), ← int.fract_add_int (α * ↑j), int.fract_eq_of_eq h3, int.fract_zero],
      ring,
    },
    have h9 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h10 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h11 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h12 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h13 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h14 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h15 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h16 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h17 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h18 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h19 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h20 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h21 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h22 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h23 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h24 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h25 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h26 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h27 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h28 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h29 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h30 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h31 : (i - j) ∈ (set.range (λ (m : ℤ), int.fract (α * ↑m))) ∩ set.univ, from by {
      split,
      exact h8,
      exact h7,
    },
    have h32 : (i -
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  --Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by {
    assume i j : ℤ,
    assume h2 : i ≠ j,
    assume h3 : (int.fract (α * ↑i)) = (int.fract (α * ↑j)),
    have h4 : α = (α * ↑i - int.floor (α * ↑i)) / ↑(i - j), from by {
      rw [← h3, int.fract_eq_iff_eq_or_eq_add_one],
      rw [← int.fract_eq_iff_eq_or_eq_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract_add_one, int.fract_add_one],
      rw [int.fract
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
  begin
    assume i j h,
    assume h2 : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h3 : α = (int.fract (α * ↑i) + int.nat_abs (α * ↑i)) / (i - j), from by {
      rw [h2, int.fract_add_nat_abs, int.nat_abs_of_nonneg (le_of_lt (mul_pos hα_irrat (int.coe_nat_pos.2 (nat.zero_lt_succ 0)))), int.coe_nat_mul, int.coe_nat_mul],
      rw [int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add],
      rw [int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add],
      rw [int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add, int.coe_nat_add],
    },
    have h4 : α ∈ ℚ, from by {
      apply int.coe_nat_ne_zero_iff_pos.1,
      assume h5 : i - j = 0,
      have h6 : i = j, from by {rw h5, ring},
      contradiction,
    },
    exact hα_irrat h4,
  end,

  -- If this were not true, then
  -- $$
  -- i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,
  -- $$
  -- which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$. 
  have h2 : ∀ i j : ℤ, i ≠ j → α ≠ (int.nat_abs (α * ↑i) - int.nat_abs (α * ↑j)) / (i - j), from
  begin
    assume i j h,
    assume h3 : α = (int.nat_abs (α * ↑i) - int.nat_abs (α * ↑j)) / (i - j),
    have h4 : α ∈ ℚ, from by {
      apply int.coe_nat_ne_zero_iff_pos.1,
      assume h5 : i - j = 0,
      have h6 : i = j, from by {rw h5, ring},
      contradiction,
    },
    exact hα_irrat h4,
  end,

  -- Hence,
  -- $$
  -- S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}
  -- $$
  -- is an infinite subset of $\left[0,1\right]$.
  have h3 : set.finite (set.range (λ m : ℤ, int.fract (α * ↑m))) = ff, from
  begin
    apply set.finite_iff_fintype.2,
    apply set.fintype_range_int_fract,
  end,
  have h4 : set.finite (set.range (λ m : ℤ, int.fract (α * ↑m))), from by {
    rw h3,
  },
  have h5 : set.finite (set.range (λ m : ℤ, int.fract (α * ↑m))) = tt, from by {
    apply set.finite_iff_fintype.1,
    apply set.fintype_range_int_fract,
  },
  have h6 : set.finite (set.range (λ m : ℤ, int.fract (α * ↑m))), from by {
    rw h5,
  },
  have h7 : set.finite (set.range (λ m : ℤ, int.fract (α * ↑m))), from by {
    rw h4,
  },
  have h8 : (set.range (λ m : ℤ, int.fract (α * ↑m))) ≠ ∅, from by {
    apply set.nonempty_range_int_fract,
    exact hα_irrat,
  },
  have h9 : set.finite (set.range (λ m : ℤ, int.fract (α * ↑m))), from by {
    rw h4,
  },

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  have h10 : ∃ x : ℝ, x ∈ set.range (λ (m : ℤ), int.fract (α * ↑m)) ∧ x ∈ closure (set.range (λ (m : ℤ), int.fract (α * ↑m))), from by {
    apply set.exists_mem_of_ne_empty,
    apply h8,
    have h11 : set.range (λ (m : ℤ), int.fract (α * ↑m)) ⊆ set.Icc 0 1, from by {
      rintros x h12,
      rcases h12 with ⟨m, h13⟩,
      rw h13,
      rw int.fract_lt_one,
    },
    apply set.subset_closure,
    exact h11,
  },
  cases h10 with x h11,
  cases h11 with h12 h13,

  -- One can thus find pairs of elements of $S$ that are arbitrarily close. 
  have h14 : ∀ ε > 0, ∃ (x y : ℤ), x ≠ y ∧ int.fract (α * ↑x) ∈ set.range (λ (m : ℤ), int.fract (α * ↑m)) ∧ int.fract (α * ↑y) ∈ set.range (λ (m : ℤ), int.fract (α * ↑m)) ∧ abs (int.fract (α * ↑x) - int.fract (α * ↑y)) < ε, from
  begin
    assume ε h15,
    cases h13 ε h15 with N h16,
    use (N+1),
    use N,
    split,
    exact nat.succ_ne_self N,
    split,
    exact h16 (nat.succ_le_of_lt (nat.lt_succ_self N)),
    split,
    exact h16 (nat.le_refl N),
    have h17 : int.fract (α * ↑(N+1)) - int.fract (α * ↑N) = α * ↑(N+1) - (α * ↑N - int.nat_abs (α * ↑N)), from by {
      rw int.fract_add_nat_abs,
      rw int.nat_abs_of_nonneg (le_of_lt (mul_pos hα_irrat (int.coe_nat_pos.2 (nat.zero_lt_succ 0)))),
      ring,
    },
    have h18 : int.fract (α * ↑(N+1)) - int.fract (α * ↑N) = α - int.nat_abs (α * ↑N), from
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  --Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j : ℤ, assume h1 : i ≠ j,
    assume h2 : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h3 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
      rw h2, rw sub_eq_zero, rw div_eq_mul_inv, rw mul_comm, rw mul_one, rw sub_self,
      rw inv_zero, rw mul_zero, },
    have h4 : (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j) ∈ ℚ, from by {
      apply quotient.exact h3, },
    exact hα_irrat h4,
  },

  --If this were not true, then
  --$i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,$
  --which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
  --Hence,
  --$S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$
  --is an infinite subset of $\left[0,1\right]$.
  have h2 : ∀ (i : ℤ), int.fract (α * ↑i) ∈ set.Icc 0 1, from by {
    assume i : ℤ,
    have h3 : int.fract (α * ↑i) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
      use i, rw set.mem_univ,
    },
    show int.fract (α * ↑i) ∈ set.Icc 0 1, from by {
      apply set.mem_Icc.2,
      split; linarith,
    },
  },

  have h3 : ∀ (i : ℤ), int.fract (α * ↑i) ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    assume i : ℤ,
    rw closure_eq_nhds,
    use i,
    use (int.fract (α * ↑i)),
    split,
    exact h2 i,
    use 1,
    split,
    linarith,
    linarith,
  },

  --By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  have h4 : ∃ (x : ℝ), x ∈ set.Icc 0 1 ∧ x ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    apply set.compact_Icc.exists_mem_of_finite_subcover,
    have h5 : ∀ (i : ℤ), ∃ (ε : ℝ), ε > 0 ∧ ∀ (x : ℝ), x ∈ set.Icc 0 1 ∧ |x - int.fract (α * ↑i)| < ε → x ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
      assume i : ℤ,
      use 1,
      split,
      linarith,
      assume x : ℝ,
      assume h6 : x ∈ set.Icc 0 1 ∧ |x - int.fract (α * ↑i)| < 1,
      have h7 : x ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
        use i,
        split,
        rw set.mem_univ,
        rw h6.right,
      },
      show x ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
        rw closure_eq_nhds,
        use i,
        use x,
        split,
        exact h7,
        use 1,
        split,
        linarith,
        linarith,
      },
    },
    have h8 : ∀ (i : ℤ), ∃ (ε : ℝ), ε > 0 ∧ ∀ (x : ℝ), x ∈ set.Icc 0 1 ∧ |x - int.fract (α * ↑i)| < ε → x ∈ set.Icc 0 1, from by {
      assume i : ℤ,
      use 1,
      split,
      linarith,
      assume x : ℝ,
      assume h9 : x ∈ set.Icc 0 1 ∧ |x - int.fract (α * ↑i)| < 1,
      show x ∈ set.Icc 0 1, from by {
        exact h9.left,
      },
    },
    use h8,
    intros i h10,
    cases h5 i with ε h11,
    use ε,
    split,
    exact h11.left,
    exact h11.right,
  },

  cases h4 with x h5,

  --One can thus find pairs of elements of $S$ that are arbitrarily close.
  have h6 : ∀ (ε : ℝ), ε > 0 → ∃ (y : ℝ), y ∈ set.Icc 0 1 ∧ y ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ |x - y| < ε, from by {
    assume ε : ℝ,
    assume h6 : ε > 0,
    cases h5.right ε h6 with y h7,
    use y,
    split,
    exact h7.left,
    split,
    exact h7.right,
    exact h7.right_1,
  },

  --Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
  have h8 : 0 ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    rw closure_eq_nhds,
    use x,
    use 0,
    split,
    exact h5.left,
    use 1,
    split,
    linarith,
    linarith,
  },

  --To show that $S$ is dense in $[0, 1]$, consider $y \in[0,1]$, and $\epsilon>0$.
  have h9 : ∀ (y : ℝ), y ∈ set.Icc 0 1 → ∀ (ε : ℝ), ε > 0 → ∃ (x : ℝ), x ∈ set.Icc 0 1 ∧ x ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ |y - x| < ε, from by {
    assume (y : ℝ) (h10 : y ∈ set.Icc 0 1),
    assume (ε : ℝ) (h11 : ε > 0),
    cases h6 ε h11 with x h12,
    use x,

end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  --Let $\alpha$ be an irrational number.
  assume α,
  --Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j h,
    have h2 : (α * ↑i) - (int.floor (α * ↑i)) = int.fract (α * ↑i), from by {
      rw int.fract_eq_sub_floor,
    },
    have h3 : (α * ↑j) - (int.floor (α * ↑j)) = int.fract (α * ↑j), from by {
      rw int.fract_eq_sub_floor,
    },
    have h4 : (α * ↑i) - (int.floor (α * ↑i)) = (α * ↑j) - (int.floor (α * ↑j)), from by {
      rw [h2,h3],
    },
    have h5 : α = (int.floor (α * ↑i) - int.floor (α * ↑j)) / (i - j), from by {
      rw [←int.cast_div,←int.cast_sub,←int.cast_mul,←int.cast_mul,←int.cast_mul,←int.cast_mul,←int.cast_mul,←int.cast_mul],
      rw [mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub,mul_sub
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number.
  assume α : ℝ,
  assume hα_irrat : irrational α,

  -- Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
  begin
    assume i j h,
    assume h2 : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h3 : α = (int.fract (α * ↑i) + int.nat_abs (α * ↑i)) / (i - j), from by {
      rw [int.fract_add_nat_abs_of_nonneg, h2, int.fract_add_nat_abs_of_nonneg],
      rw [int.mul_sub, int.mul_sub, int.mul_sub],
      rw [mul_comm α i, mul_comm α j],
      ring,
    },
    have h4 : (int.fract (α * ↑i) + int.nat_abs (α * ↑i)) / (i - j) ∈ ℚ, from by {
      rw h3,
    },
    have h5 : irrational α, from hα_irrat,
    have h6 : ¬(α ∈ ℚ), from h5,
    show false, from h6 h4,
  end,

  -- If this were not true, then
  -- $i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor$,
  -- which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
  have h7 : ∀ i j : ℤ, i ≠ j → α ≠ (int.floor (α * ↑i) - int.floor (α * ↑j)) / (i - j), from 
  begin
    assume i j h,
    assume h2 : α = (int.floor (α * ↑i) - int.floor (α * ↑j)) / (i - j),
    have h3 : int.fract (α * ↑i) = int.fract (α * ↑j), from by {
      rw [int.fract_add_nat_abs_of_nonneg, int.fract_add_nat_abs_of_nonneg],
      rw [int.mul_sub, int.mul_sub, int.mul_sub],
      rw [mul_comm α i, mul_comm α j],
      rw h2,
      ring,
    },
    have h4 : i ≠ j, from h,
    have h5 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h1 i j h4,
    show false, from h5 h3,
  end,

  -- Hence,
  -- $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$
  -- is an infinite subset of $\left[0,1\right]$.
  have h8 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by {
    assume x h,
    cases h with m hm,
    rw ←hm,
    rw int.fract_mul,
    rw int.fract_lt_one,
    rw int.fract_lt_one,
  },
  have h9 : infinite ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    have h10 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h1,
    have h11 : ∀ i j : ℤ, i ≠ j → (λ m : ℤ, int.fract (α * ↑m)) i ≠ (λ m : ℤ, int.fract (α * ↑m)) j, from by {
      assume i j h,
      rw [←int.fract_mul, ←int.fract_mul],
      exact h10 i j h,
    },
    have h12 : ∀ i j : ℤ, i ≠ j → (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
      assume i j h,
      use i,
      refl,
    },
    have h13 : ∀ i j : ℤ, i ≠ j → (λ m : ℤ, int.fract (α * ↑m)) j ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
      assume i j h,
      use j,
      refl,
    },
    have h14 : ∀ i j : ℤ, i ≠ j → (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∧ (λ m : ℤ, int.fract (α * ↑m)) j ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
      assume i j h,
      split,
      exact h12 i j h,
      exact h13 i j h,
    },
    have h15 : ∀ i j : ℤ, i ≠ j → (λ m : ℤ, int.fract (α * ↑m)) i ≠ (λ m : ℤ, int.fract (α * ↑m)) j, from by {
      assume i j h,
      exact h11 i j h,
    },
    exact set.infinite_of_injective_of_ne_of_ne (λ m : ℤ, int.fract (α * ↑m)) h15 h14,
  },

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  have h16 : ∃ x : ℝ, x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    exact set.bounded_has_sup_of_ne_empty h8,
  },

  -- One can thus find pairs of elements of $S$ that are arbitrarily close.
  have h17 : ∀ ε > 0, ∃ x y : ℝ, x ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∧ y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∧ abs (x - y) < ε, from by {
    assume ε h,
    cases h16 with x hx,
    have h18 : ∃ y : ℝ, y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∧ abs (x - y) < ε, from by {
      have h19 : ∃ y : ℝ, y ∈ set.Icc 0 1 ∧ abs (x - y) < ε, from by {
        have h20 : ∃ y : ℝ, y ∈ set.Icc 0 1 ∧ abs (x - y) < ε, from by {
          have h21 : ∃ y : ℝ, y ∈
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
