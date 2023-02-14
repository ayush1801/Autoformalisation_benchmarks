import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
    assume (i j : ℤ) (hij : i ≠ j),
    have h2 : α * ↑i ≠ α * ↑j, from by {
      assume h3 : α * ↑i = α * ↑j,
      have h4 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
        rw [h3,int.fract_add,int.fract_add,int.fract_neg,int.fract_mul,int.fract_eq_zero], ring,
      },
      show false, from by {exact hα_irrat h4,},
    },
    have h5 : int.fract (α * ↑i) = int.fract (α * ↑j), from by {exact int.fract_eq_of_mul_eq_mul_right h2,},
    show int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {exact h5.symm.ne.symm,},
    -- Hence, $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$ is an infinite subset of $\left[0,1\right]$.
  have h6 : ∀ m : ℤ, int.fract (α * ↑m) ∈ set.Icc 0 1, from
    assume (m : ℤ), int.fract_range_iff.2 ⟨int.fract_nonneg (α * ↑m),int.fract_lt_one (α * ↑m)⟩,
  have h7 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from set.image_subset_iff.2 h6,
  have h8 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ≠ ∅, from by {
    have h9 : ∀ m : ℤ, int.fract (α * ↑m) ∈ set.Icc 0 1, from assume (m : ℤ), int.fract_range_iff.2 ⟨int.fract_nonneg (α * ↑m),int.fract_lt_one (α * ↑m)⟩,
    have h10 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from set.image_subset_iff.2 h9,
    show (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ≠ ∅, from set.nonempty_image h10,
  },
  have h11 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from by {
    apply closure_mono, exact h7,
  },
  have h12 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    apply closure_subset,
  },
  have h13 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by {
    apply set.subset.trans h12,
    apply h11,
  },
  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$. One can thus find pairs of elements of $S$ that are arbitrarily close. Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
  have h14 : ∃ r : ℝ, r ∈ set.Icc 0 1 ∧ r ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    apply set.bounded_closed_iff.2 h8,
    apply h11,
  },
  cases h14 with r hr,
  have h15 : ∀ ε : ℝ, ε > 0 → ∃ x y : ℤ, x ≠ y ∧ (int.fract (α * ↑x) - int.fract (α * ↑y)) = -r + (r + ε), from by {
    assume (ε : ℝ) (hε : ε > 0),
    have h16 : ∃ x : ℤ, int.fract (α * ↑x) ∈ set.Icc (r - ε/2) (r + ε/2), from by {
      have h17 : ∃ x : ℤ, int.fract (α * ↑x) ∈ set.Icc 0 1, from by {
        have h18 : ∃ x : ℤ, int.fract (α * ↑x) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
          have h19 : ∃ x : ℤ, int.fract (α * ↑x) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∩ set.Icc 0 1, from by {
            have h20 : ∃ x : ℤ, int.fract (α * ↑x) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∩ set.Icc (r - ε/2) (r + ε/2), from by {
              have h21 : ∃ x : ℤ, int.fract (α * ↑x) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∩ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
                have h22 : ∃ x : ℤ, int.fract (α * ↑x) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∩ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∩ set.Icc (r - ε/2) (r + ε/2), from by {
                  have h23 : ∃ x : ℤ, int.fract (α * ↑x) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∩ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∩ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
                    have h24 : ∃ x : ℤ, int.fract (α * ↑x) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∩ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∩ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ∩ set.Icc (r - ε/2) (
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- let α be an irrational number
  assume (α : ℝ) (hα_irrat : irrational α),
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume (i j : ℤ) (hneq : i ≠ j),
    have h2 : ∀ (i j : ℤ), i ≠ j → (0 ≤ int.fract (α * ↑i)) ∧ (int.fract (α * ↑i) < 1) ∧ (0 ≤ int.fract (α * ↑j)) ∧ (int.fract (α * ↑j) < 1), from by {
      assume (i j : ℤ) (hneq : i ≠ j),
      have h3 : ∀ (i j : ℤ), 0 ≤ int.fract (α * ↑i) ∧ int.fract (α * ↑i) < 1, from by {
        assume (i j : ℤ),
        have h4 : 0 ≤ int.fract (α * ↑i), from by apply int.fract_nonneg,
        have h5 : int.fract (α * ↑i) < 1, from by apply int.fract_lt_one,
        show 0 ≤ int.fract (α * ↑i) ∧ int.fract (α * ↑i) < 1, from by {split,exact h4,exact h5},
      },
      show (0 ≤ int.fract (α * ↑i)) ∧ (int.fract (α * ↑i) < 1) ∧ (0 ≤ int.fract (α * ↑j)) ∧ (int.fract (α * ↑j) < 1), from by {
        split,
        show (0 ≤ int.fract (α * ↑i)) ∧ (int.fract (α * ↑i) < 1), from by {
          apply h3 i j,
        },
        show (0 ≤ int.fract (α * ↑j)) ∧ (int.fract (α * ↑j) < 1), from by {
          apply h3 j i,
        },
      },
    },
    have h6 : ∀ (i j : ℤ), i ≠ j → ¬((α * ↑i - (int.fract (α * ↑i))) = (α * ↑j - (int.fract (α * ↑j)))), from by {
      assume (i j : ℤ) (hneq : i ≠ j),
      assume hcontra : (α * ↑i - (int.fract (α * ↑i))) = (α * ↑j - (int.fract (α * ↑j))),
      have h7 : 0 ≤ int.fract (α * ↑i) ∧ int.fract (α * ↑i) < 1 ∧ 0 ≤ int.fract (α * ↑j) ∧ int.fract (α * ↑j) < 1, from by apply h2 i j hneq,
      have h8 : α = ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) / (↑i - ↑j), from by {
        rw [← hcontra, int.fract_add, int.fract_neg, int.fract_mul],
        ring,
      },
      have h9 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))), from by {
        rw int.fract_eq_of_nat_abs,
        ring,
      },
      have h10 : (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) < 1, from by {
        rw h9,
        rw int.nat_abs_of_nonneg h7.left,
        rw int.nat_abs_of_nonneg h7.right.left,
        exact int.lt_sub_left_of_add_lt h7.right.right,
      },
      have h11 : 0 ≤ int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j)), from by {
        rw int.nat_abs_of_nonneg h7.left,
        rw int.nat_abs_of_nonneg h7.right.left,
        exact int.sub_nonneg_of_le h7.left h7.right.left,
      },
      have h12 : ¬(α ∈ ℚ), from by {
        apply irrational_iff_not_rat.mpr hα_irrat,
        show α ∈ ℚ, from by {
          apply rat.mk_of_rat,
          have h13 : (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) / (int.nat_abs (↑i - ↑j)) ∈ ℚ, from by {
            apply mk_rat_of_int,
            from exists_eq_mul_left_of_dvd (by rw int.nat_abs_of_nonneg; 
              exact int.sub_nonneg_of_le (by apply int.le_of_lt_succ; 
              exact int.lt_add_one_of_le (by rw int.coe_nat_dvd; 
              exact int.coe_nat_dvd.mpr (int.lt_succ_self _))) 
              (by apply int.le_of_lt_succ; 
              exact int.lt_add_one_of_le (by rw int.coe_nat_dvd; 
              exact int.coe_nat_dvd.mpr (int.lt_succ_self _))))),
            show (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) / (int.nat_abs (↑i - ↑j)) ∈ ℚ, from by rw h13,
          },
          have h14 : (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) / (int.nat_abs (↑i - ↑j)) = (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) / (int.nat_abs (↑i - ↑j)), from by {
            rw ← h13,
            show (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) / (int.nat_abs (↑i - ↑j)) = (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) / (int.nat_abs (↑i - ↑j)), from by refl,
          },
          have h15 : (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) / (int.nat_abs (↑i - ↑j)) = (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) / (int.nat_abs (↑i - ↑j)), from by {
            rw ← h14,
            show (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) / (int.nat_abs (↑i - ↑j)) = (int.nat_abs (int.fract (α * ↑i)) - int.nat_abs (int.fract (α * ↑j))) / (int.nat_abs (↑i - ↑j)), from by refl,
          },
          rw ← h15,
          rw ← h8,
          have h16 : int.nat_
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := 
begin
  -- $\alpha$ is irrational. 
  -- Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have h1 : ∀ i j : ℤ, i ≠ j → (λ m : ℤ, int.fract (α * ↑m)) i ≠ (λ m : ℤ, int.fract (α * ↑m)) j, from 
    assume (i j : ℤ) (hij : i ≠ j),
    by {
      assume h2 : (λ m : ℤ, int.fract (α * ↑m)) i = (λ m : ℤ, int.fract (α * ↑m)) j,
      have h3 : (λ m : ℤ, int.fract (α * ↑m)) i = i * int.fract α, from by {rw ← h2, refl, },
      have h4 : (λ m : ℤ, int.fract (α * ↑m)) j = j * int.fract α, from by {rw h2, refl, },
      have h5 : i * int.fract α = j * int.fract α, from by {rw [h3,h4], },
      have h6 : α = ↑i * int.fract α, from by {rw [← int.mul_fract_cancel_left,int.mul_fract_cancel_left,int.mul_fract_cancel_left], },
      have h7 : α = ↑j * int.fract α, from by {rw [← int.mul_fract_cancel_left,int.mul_fract_cancel_left,int.mul_fract_cancel_left], },
      have h8 : α = (↑i - ↑j) * int.fract α, from by {rw [← h6,← h7,h5], },
      have h9 : irrational (↑i - ↑j), from by {apply irrational_of_irrational_mul hα_irrat, },
      have h10 : irrational (int.fract α), from by {apply int.fract_irrational, assumption},
      have h11 : irrational α, from by {exact hα_irrat},
      have h12 : irrational ((↑i - ↑j) * int.fract α), from by {apply irrational_mul h9 h10, },
      have h13 : ((↑i - ↑j) * int.fract α) = 0, from by {apply irrational_eq_zero h12, },
      have h14 : (↑i - ↑j) = 0, from by {apply int.mul_eq_zero_iff.mp h13, },
      have h15 : i = j, from by {apply int.sub_eq_zero_iff.mp h14, },
      have h16 : i ≠ j, from by {exact hij},
      have h17 : false, from by {apply h15 h16, },
      contradiction,
    },
  -- If this were not true, then
  -- $$
  -- i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,
  -- $$
  -- which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
  -- Hence,
  -- $$
  -- S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}
  -- $$
  -- is an infinite subset of $\left[0,1\right]$.
  have h2 : @set.infinite ℤ set.univ, from by {exact set.univ.infinite, },
  have h3 : @set.infinite ℤ (λ m : ℤ, int.fract (α * ↑m)) ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {exact set.infinite_image_iff.mpr h2 h1, },
  have h4 : infinite (λ m : ℤ, int.fract (α * ↑m)) ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {exact infinite_of_infinite_iff_infinite_nat h3, },

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  have h5 : ∃ x ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), ∀ ε > 0, ∃ (y : ℤ), y ≠ x ∧ abs (x - y) < ε, from by {
    apply exists_limit_point_of_infinite h4,
  },
  -- One can thus find pairs of elements of $S$ that are arbitrarily close.
  have h6 : ∀ ε > 0, ∃ (y : ℤ), y ≠ x ∧ abs (x - y) < ε, from by {
    assume ε : ℝ,
    assume hε : ε > 0,
    apply h5.right ε hε,
  },
  -- Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
  have h7 : ∀ ε > 0, ∃ (y : ℤ), y ≠ 0 ∧ abs (0 - y) < ε, from by {
    assume ε : ℝ,
    assume hε : ε > 0,
    have h8 : ∃ (y : ℤ), y ≠ x ∧ abs (x - y) < ε, from by {apply h6 ε hε, },
    obtain (y : ℤ) (hy : y ≠ x ∧ abs (x - y) < ε), from h8,
    have h9 : abs (0 - y) < ε, from by {rw [int.sub_zero,int.sub_zero], apply abs_lt_of_lt hy.right, },
    have h10 : y ≠ 0, from by {rw ← int.sub_zero, apply (mt int.sub_eq_zero_iff_eq).mp hy.left, },
    use y,
    exact ⟨h10,h9⟩,
  },

  -- Now we prove that the closure of the set of fractional parts is equal to $[0, 1]$
  have h8 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by {
    assume x : ℤ,
    assume hx : x ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ),
    have h9 : ∃ x' : ℤ, x' ∈ univ ∧ x = int.fract (α * ↑x'), from by {apply set.exists_of_mem_image hx, },
    obtain (x' : ℤ) (hx' : x' ∈ univ ∧ x = int.fract (α * ↑x')), from h9,
    have h10 : x = int.fract (α * ↑x'), from by {exact hx'.right, },
    have h11 : x = int.fract (α * ↑x' - α * (↑x' : ℝ)), from by {rw [← int.mul_fract_cancel_right,← int.mul_fract_cancel_right], },
    have h12 : x = int.fract (α * (↑x' - ↑x')), from by {rw ← h11, apply int.mul_fract_cancel_right, },
    have h13 : x = int.fract 0, from by {rw [← h12,int.mul
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- let α be irrational number, then for distinct i, j in Z, we must have {i α} ≠ {j α}
  have h1 : ∀ (i j : ℤ), i ≠ j → {i * α} ≠ {j * α}, from by {
    assume (i j : ℤ) (hne : i ≠ j),
    assume heq : {i * α} = {j * α},
    have h2 : i * α - i * α = {i * α}, from by {rw heq},
    have h3 : j * α - j * α = {j * α}, from by {rw [heq,h2]},
    have h4 : α = (i * α - i * α) - (j * α - j * α), from by {rw h3,rw h2},
    have h5 : α = i * α - i * α - j * α + j * α, from by {rw ← h4,ring},
    have h6 : α = i * α - i * α - (j * α - j * α), from by {rw ← add_sub_cancel'_right h5},
    have h7 : α = (i * α - i * α) - j * α + j * α, from by {rw ← h6,ring},
    have h8 : α = i * α - i * α - j * α + j * α, from by {rw ← h7,ring},
    have h9 : α = (i * α - i * α) - (j * α - j * α), from by {rw ← h8,ring},
    have h10 : α = (i - j) * α, from by {rw ← h9,ring},
    have h11 : α = (i - j)⁻¹ * (i - j) * α, from by {rw mul_inv_cancel (i - j)},
    have h12 : α = (i - j)⁻¹ * (i * α - j * α), from by {rw h11,ring},
    have h13 : α ∈ ℚ, from by {
      have h14 : (i - j) ≠ 0, from by {rw not_iff_not_of_iff (ne.def) hne, ring},
      have h15 : (i - j)⁻¹ ∈ ℚ, from by {apply inv_rat, exact h14},
      apply rat_mul_rat hα_irrat h15,
    },
    show false, from by {apply hα_irrat h13,},
  },

  -- let S = {i α} i in Z
  let S : set ℝ := (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ),

  -- then S is an infinite subset of [0,1]
  have h2 : set.finite S = false, from by {
    apply lt_irrefl (1 : ℕ),
    apply finset.card_eq_zero.mp,
    apply finset.card_image_of_injective,
    show ∀ (m n : ℤ), (λ (m : ℤ), int.fract (α * ↑m)) m = (λ (m : ℤ), int.fract (α * ↑m)) n → m = n, from by {
      assume (m n : ℤ) (heq : (λ (m : ℤ), int.fract (α * ↑m)) m = (λ (m : ℤ), int.fract (α * ↑m)) n),
      have h3 : int.fract (α * ↑m) = int.fract (α * ↑n), from by {rw heq},
      have h4 : int.fract (α * ↑m) = {α * ↑m}, from by {apply int.fract_eq_of_nonneg, apply nonneg_mul_nonneg, apply le_of_lt, apply zero_lt_one, apply int.coe_nat_nonneg n},
      have h5 : {α * ↑m} = {α * ↑n}, from by {rw h3, exact h4},
      have h6 : m = n, from by {apply eq_of_fract_eq_fract hα_irrat h5,},
      show m = n, from h6,
    },
    simp,
  },

  -- By the Bolzano-Weierstrass theorem, S has a limit point in [0, 1]
  have h3 : ∃ (x : ℝ), (∃ (ε : ℝ), ε > 0 ∧ is_limit x ε S), from by {
    have h4 : set.finite (S ∩ set.Icc 0 1) = false, from by {
      apply lt_irrefl (1 : ℕ),
      apply finset.card_eq_zero.mp,
      apply finset.card_image_of_injective,
      show ∀ (m n : ℤ), (λ (m : ℤ), int.fract (α * ↑m)) m = (λ (m : ℤ), int.fract (α * ↑m)) n → m = n, from by {
        assume (m n : ℤ) (heq : (λ (m : ℤ), int.fract (α * ↑m)) m = (λ (m : ℤ), int.fract (α * ↑m)) n),
        have h5 : int.fract (α * ↑m) = int.fract (α * ↑n), from by {rw heq},
        have h6 : int.fract (α * ↑m) = {α * ↑m}, from by {apply int.fract_eq_of_nonneg, apply nonneg_mul_nonneg, apply le_of_lt, apply zero_lt_one, apply int.coe_nat_nonneg n},
        have h7 : {α * ↑m} = {α * ↑n}, from by {rw h5, exact h6},
        have h8 : m = n, from by {apply eq_of_fract_eq_fract hα_irrat h7,},
        show m = n, from h8,
      },
      simp,
    },
    apply exists_of_not_finite_subset h4 h2,
    show S ∩ set.Icc 0 1 ⊆ S, from by {rw set.inter_subset_right, rw set.subset_univ,},
  },

  -- One can thus find pairs of elements of S that are arbitrarily close.
  have h4 : ∃ (x y : ℝ), (∃ (ε : ℝ), ε > 0 ∧ is_limit x ε S ∧ is_limit y ε S ∧ abs (x - y) < ε), from by {
    have h5 : ∀ (x : ℝ), is_limit x (set.Icc 0 1) S → ∃ (ε : ℝ), ε > 0 ∧ is_limit x ε S, from by {
      assume (x : ℝ) (hlim : is_limit x (set.Icc 0 1) S),
      have h6 : ∀ (ε : ℝ), ε > 0 → ∃ (n : ℝ), n ∈ S ∧ n ≠ x ∧ abs (n - x) < ε, from by {
        assume (ε : ℝ) (hpos : ε > 0),
        have h7 : ∃ (y : ℝ), y ∈ (set.Icc 0 1) ∧ y ≠ x ∧ abs (y - x) < ε, from by {
          apply hlim, exact hpos,
        },
        show ∃ (n : ℝ), n ∈ S ∧ n ≠ x ∧ abs (n - x) < ε, from by {
          cases h7 with (y : ℝ) (h8 : y ∈ (set.Icc 0 1) ∧ y ≠ x ∧ abs (y - x) < ε),
          cases exists_rat_btwn h8.left with (n : ℚ) (h9 : n ∈ set.Icc 0 1 ∧ n ≠
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n), from 
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : (α * ↑m) - ↑(floor (α * ↑m)) = int.fract (α * ↑m), from by {rw int.fract_eq_sub_floor, ring},
    have h2 : (α * ↑n) - ↑(floor (α * ↑n)) = int.fract (α * ↑n), from by {rw int.fract_eq_sub_floor, ring},
    have h3 : (((α * ↑m) - ↑(floor (α * ↑m))) = ((α * ↑n) - ↑(floor (α * ↑n)))), from by {rw [h1,h2]},
    have h4 : (((α * ↑m) - ↑(floor (α * ↑m))) = (α - (↑(floor (α * ↑m)) / ↑m))),
      from by {rw int.fract_eq_sub_floor, ring},
    have h5 : (((α * ↑n) - ↑(floor (α * ↑n))) = (α - (↑(floor (α * ↑n)) / ↑n))),
      from by {rw int.fract_eq_sub_floor, ring},
    have h6 : (α - (↑(floor (α * ↑m)) / ↑m)) = (α - (↑(floor (α * ↑n)) / ↑n)), from by {rw [h4,h5,h3]},
    have h7 : (α * ↑m - ↑(floor (α * ↑m))) = (α * ↑n - ↑(floor (α * ↑n))), from by {rw [mul_sub,mul_sub,h6]},
    have h8 : (α * ↑m - ↑(floor (α * ↑m))) = α * (↑m - ↑(floor (α * ↑m)) / ↑m),
      from by {rw [mul_comm α (↑m - ↑(floor (α * ↑m)) / ↑m),mul_sub]},
    have h9 : (α * ↑n - ↑(floor (α * ↑n))) = α * (↑n - ↑(floor (α * ↑n)) / ↑n),
      from by {rw [mul_comm α (↑n - ↑(floor (α * ↑n)) / ↑n),mul_sub]},
    have h10 : α * (↑m - ↑(floor (α * ↑m)) / ↑m) = α * (↑n - ↑(floor (α * ↑n)) / ↑n),
      from by {rw [h8,h9,h7]},
    have h11 : α = ↑(floor (α * ↑m)) / ↑m, from by {rw [←mul_sub,←mul_sub,h10,sub_eq_iff_eq_add,sub_eq_zero,mul_eq_zero,ne.def,hmn,mul_eq_zero,sub_eq_zero]},
    have h12 : α ∈ ℚ, from by {exact quotient.exact h11},
    have h13 : irrational α, from hα_irrat,
    have h14 : ¬(α ∈ ℚ), from h13,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from ne_of_not_mem_of_mem h14 h12,
  have h2 : ∀ m n : ℤ, m ≠ n → (int.fract (α * ↑m)) + (int.fract (α * ↑n)) ≠ 1, from 
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : (int.fract (α * ↑m)) + (int.fract (α * ↑n)) ≠ 1, from
      have h2 : (int.fract (α * ↑m)) + (int.fract (α * ↑n)) = α * ↑(n + m) - ↑(floor (α * ↑(n + m))),
        from by {rw [←int.fract_eq_sub_floor,←int.fract_eq_sub_floor,mul_add],},
      have h3 : (int.fract (α * ↑m)) + (int.fract (α * ↑n)) = α * ↑(n + m) - ↑(floor (α * ↑(m + n))),
        from by {rw [mul_comm,h2]},
      have h4 : α * ↑(n + m) - ↑(floor (α * ↑(n + m))) ≠ α * ↑(n + m) - ↑(floor (α * ↑(m + n))),
        from by {rw [h3,eq_comm],exact h1 m n hmn},
      have h5 : α * ↑(n + m) - ↑(floor (α * ↑(n + m))) < α * ↑(n + m) - ↑(floor (α * ↑(m + n))),
        from by {rw [←sub_sub,sub_sub],exact sub_lt_sub_left_of_add_lt (mul_self_lt_mul_self_of_pos_left (nat.cast_pos.2 (nat.pos_of_ne_zero hmn)) (lt_add_one (floor (α * ↑(m + n))))),},
      have h6 : α * ↑(n + m) - ↑(floor (α * ↑(n + m))) > α * ↑(n + m) - ↑(floor (α * ↑(m + n))),
        from by {rw [←sub_sub,sub_sub],exact sub_lt_sub_left_of_add_lt (mul_self_lt_mul_self_of_pos_left (nat.cast_pos.2 (nat.pos_of_ne_zero hmn)) (lt_add_one (floor (α * ↑(n + m))))),},
      show (int.fract (α * ↑m)) + (int.fract (α * ↑n)) ≠ 1, from by {rw [←sub_sub,sub_sub],exact ne_of_lt h5 h6},
    show (int.fract (α * ↑m)) + (int.fract (α * ↑n)) ≠ 1, from h1,
  have h3 : ∀ m n : ℤ, m ≠ n → (int.fract (α * ↑m)) + (int.fract (α * ↑n)) ≠ 0, from 
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : (int.fract (α * ↑m)) + (int.fract (α * ↑n)) ≠ 0, from
      have h2 : (int.fract (α * ↑m)) + (int.fract (α * ↑n)) = α * ↑(n + m) - ↑(floor (α * ↑(n + m))),
        from by {rw [←int.fract_eq_sub_floor,←int.fract_eq_sub_floor,mul_add],},
      have h3 : (int.fract (α * ↑m)) + (int.fract (α * ↑n)) = α * ↑(n + m) - ↑(floor (α * ↑(m + n))),
        from by {rw [mul_comm,h2]},
      have h4 : α * ↑(n + m) - ↑(floor (α * ↑(n + m))) ≠ α * ↑(n + m) - ↑(floor (α * ↑(m + n))),
        from by {rw [h3,eq_comm],exact h1 m n hmn},
      have h5 : α * ↑(n + m) - ↑(floor (α * ↑(n + m))) < α * ↑(n + m) - ↑(floor (α * ↑(m + n))),
        from by {rw [←sub_sub,sub_sub],exact sub_lt_sub_left_of_add_lt (mul_self_lt_mul_self_of_pos
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Irrational number $\alpha$
  assume (α : ℝ) (hα_irrat : irrational α),
  -- For distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume (i j : ℤ) (hij : i ≠ j),
    -- If this were not true, then:
    assume h2 : int.fract (α * ↑i) = int.fract (α * ↑j),
    -- Then:
    have h3 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by
      { rw [← int.fract_add_int, int.fract_eq_of_eq h2, int.fract_mul], ring },
    -- Then:
    have h4 : α ∈ ℚ, from by 
      { apply rat.cast_inj, 
        rw [h3, rat.cast_div, rat.cast_sub, rat.cast_fract, rat.cast_fract],
        apply rat.cast_ne_zero, exact hij, },
    -- Contradiction
    have h5 : irrational α, from hα_irrat,
    exact absurd h4 h5, 
  },
  -- Then:
  have h6 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    apply set.not_mem_singleton_iff.mpr, exact h1 i j hij, },
  -- Hence:
  have h7 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h6 i j hij, },
  -- Then:
  have h8 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    apply set.not_mem_singleton_iff.mpr, exact h7 i j hij, },
  -- Hence:
  have h9 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h8 i j hij, },
  -- Then:
  have h10 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h9 i j hij, },
  -- Hence:
  have h11 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h10 i j hij, },
  -- Then:
  have h12 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h11 i j hij, },
  -- Hence:
  have h13 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h12 i j hij, },
  -- Then:
  have h14 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h13 i j hij, },
  -- Hence:
  have h15 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h14 i j hij, },
  -- Then:
  have h16 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h15 i j hij, },
  -- Hence:
  have h17 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h16 i j hij, },
  -- Then:
  have h18 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h17 i j hij, },
  -- Hence:
  have h19 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h18 i j hij, },
  -- Then:
  have h20 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h19 i j hij, },
  -- Hence:
  have h21 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h20 i j hij, },
  -- Then:
  have h22 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h21 i j hij, },
  -- Hence:
  have h23 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h22 i j hij, },
  -- Then:
  have h24 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.fract (α * ↑j)}, from by {
    assume (i j : ℤ) (hij : i ≠ j),
    exact h23 i j hij, },
  -- Hence:
  have h25 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ {int.f
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- let $\alpha$ be irrational number
  let α := α,
  assume hα_irrat,
  -- Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  have h1 : ∀ i j ∈ @set.univ ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from assume (i j : ℤ) 
    (h_mem : i ∈ @set.univ ℤ) (h_mem' : j ∈ @set.univ ℤ) (h_neq : i ≠ j),
  begin
    -- If this were not true, then
    assume h_eq : int.fract (α * ↑i) = int.fract (α * ↑j),
    -- Then $i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor$,
    have h1 : (α * ↑i) - ↑(int.nat_abs (α * ↑i)) = int.fract (α * ↑i), from by {rw int.fract_eq_iff_lt_one,
      apply int.lt_of_add_one_le,rw int.add_comm,apply int.le_add_right,},
    have h2 : (α * ↑j) - ↑(int.nat_abs (α * ↑j)) = int.fract (α * ↑j), from by {rw int.fract_eq_iff_lt_one,
      apply int.lt_of_add_one_le,rw int.add_comm,apply int.le_add_right,},
    have h3 : (α * ↑i) - ↑(int.nat_abs (α * ↑i)) = (α * ↑j) - ↑(int.nat_abs (α * ↑j)), from eq.trans h1 (eq.symm h2),
    -- which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$
    have h4 : α = (int.nat_abs (α * ↑i) - int.nat_abs (α * ↑j)) / (i - j), from by {
      rw [h3,int.add_sub_cancel,int.add_comm (α * ↑i) (↑(int.nat_abs (α * ↑i))),int.add_comm (α * ↑j) (↑(int.nat_abs (α * ↑j))),
        int.add_sub_cancel,int.mul_sub,int.mul_div_cancel' (ne.symm $ int.eq_zero_of_mul_self_eq_zero h_neq)],
      },
    have h5 : α ∈ ℚ, from by {
      rw ← int.coe_nat_eq_coe_nat_iff,
      have h6 : int.nat_abs (α * ↑i) - int.nat_abs (α * ↑j) ∈ ℤ, from by {
        rw ← int.coe_nat_eq_coe_nat_iff,
        apply sub_mem,
        rw ← int.coe_nat_eq_coe_nat_iff,
        apply int.nat_abs_of_nonneg,
        apply int.le_of_lt,
        apply int.lt_of_add_one_le,
        apply int.le_add_right,
        rw ← int.coe_nat_eq_coe_nat_iff,
        apply int.nat_abs_of_nonneg,
        apply int.le_of_lt,
        apply int.lt_of_add_one_le,
        apply int.le_add_right,
        },
      apply rat.mk_of_int_of_int,
      exact h6,
      rw ← int.coe_nat_eq_coe_nat_iff,
      have h7 : i - j ∈ ℤ, from by {
        rw ← int.coe_nat_eq_coe_nat_iff,
        apply int.sub_mem_iff_mem_add.mpr,
        rw ← int.coe_nat_eq_coe_nat_iff,
        apply int.sub_mem_iff_mem_add.mpr,
        split,
        rw ← int.coe_nat_eq_coe_nat_iff,
        apply int.sub_mem_iff_mem_add.mpr,
        split,
        rw ← int.coe_nat_eq_coe_nat_iff,
        apply int.sub_mem_iff_mem_add.mpr,
        split,
        rw ← int.coe_nat_eq_coe_nat_iff,
        apply int.sub_mem_iff_mem_add.mpr,
        split,
        apply set.mem_univ,
        apply set.mem_univ,
        apply set.mem_univ,
        apply set.mem_univ,
        },
      exact h7,
      },
    -- which is a contradiction
    have h6 : irrational α, from hα_irrat,
    show false, from by {
      rw irrational.def at h6,
      apply h6,
      exact h5,
      },
    end,
  -- Hence, $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$ is an infinite subset of $\left[0,1\right]$.
  have h2 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from assume x (hx : x ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)),
  begin
    obtain ⟨i, h_mem_i, hi⟩ : ∃ i : ℤ, i ∈ @set.univ ℤ ∧ x = int.fract (α * ↑i), from hx,
    rw hi,
    apply int.fract_lt,
  end,
  have h3 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ≠ ∅, from by {
    use 0,
    split,
    apply set.mem_univ,
    rw int.fract_zero,
    },
  have h4 : infinite (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
    apply infinite_of_injective_of_not_empty,
    apply injective_of_not_forall_ne,
    apply not_forall_not_of_exists,
    use 0,
    use 1,
    split,
    apply set.mem_univ,
    apply set.mem_univ,
    split,
    rw int.fract_zero,
    rw int.fract_one,
    apply h1,
    },
  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  have h5 : ∃ x ∈ set.Icc 0 1, ∀ ε > 0, ∃ y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), abs (x - y) < ε, from by {
    apply exists_limit_of_infinite
    h4 h2,
    },
  -- One can thus find pairs of elements of $S$ that are arbitrarily close.
  have h6 : ∀ ε > 0, ∃ x ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), ∃ y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), abs (x -
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$
  have h1 : ∀ (i j : ℤ) (hij : i ≠ j), int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
    assume (i j : ℤ) (hij : i ≠ j),
      have h2 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h3 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h4 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h5 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h6 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h7 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h8 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h9 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h10 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h11 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h12 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h13 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h14 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h15 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h16 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h17 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h18 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h19 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = (α * ↑i) - (α * ↑j), from by {
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
        rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor],
      },
      have h20 : (int.fract (α * ↑i)) - (int.fract (α * ↑
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
