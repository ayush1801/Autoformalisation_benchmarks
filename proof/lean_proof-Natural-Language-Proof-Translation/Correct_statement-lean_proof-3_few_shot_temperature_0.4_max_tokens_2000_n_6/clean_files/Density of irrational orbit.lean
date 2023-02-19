import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume (i j : ℤ) (hij : i ≠ j),
    have h2 : ∀ (i j : ℤ), i ≠ j → ¬ (int.fract (α * ↑i) = int.fract (α * ↑j)), from by {
      assume (i j : ℤ) (hij : i ≠ j),
      assume h3 : int.fract (α * ↑i) = int.fract (α * ↑j),
      have h4 : α = (↑i)⁻¹ * ↑(int.nat_abs (α * ↑i)) / (↑j)⁻¹ * ↑(int.nat_abs (α * ↑j)), from by {
        rw h3,
        rw int.fract_eq_div_nat_abs,
        rw int.fract_eq_div_nat_abs,
        ring,
      },
      have h5 : α * ↑j = ↑i * ↑(int.nat_abs (α * ↑i)), from by {
        rw h4,
        rw mul_assoc,
        rw mul_assoc,
        rw mul_comm (↑i) (↑j)⁻¹,
        rw mul_assoc,
        rw mul_inv_cancel,
        rw mul_one,
        ring,
      },
      have h6 : α * ↑j = ↑(int.nat_abs (α * ↑i)) * ↑i, from by {
        rw h5,
        rw mul_comm (↑i) (int.nat_abs (α * ↑i)),
      },
      have h7 : α * ↑j = ↑(int.nat_abs (α * ↑i) * i), from by {
        rw h6,
        rw int.coe_nat_mul,
      },
      have h8 : α * ↑j = ↑(int.nat_abs (α * ↑j * j)), from by {
        rw mul_comm (α * ↑j) j,
        rw int.nat_abs_mul,
        rw int.coe_nat_mul,
      },
      have h9 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i) * i, from by {
        rw h7,
        rw h8,
      },
      have h10 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h11 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h10,
      },
      have h12 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h13 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h12,
      },
      have h14 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h15 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h14,
      },
      have h16 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h17 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h16,
      },
      have h18 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h19 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h18,
      },
      have h20 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h21 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h20,
      },
      have h22 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h23 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h22,
      },
      have h24 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h25 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h24,
      },
      have h26 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h27 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h26,
      },
      have h28 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h29 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h28,
      },
      have h30 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_abs_mul,
      },
      have h31 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw h9,
        rw h30,
      },
      have h32 : int.nat_abs (α * ↑j * j) = int.nat_abs (α * ↑i * i), from by {
        rw mul_comm (α * ↑i) i,
        rw int.nat_
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j : ℤ, assume h1 : i ≠ j,
    have h2 : α ≠ (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
      assume h2 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j),
      have h3 : (i - j) * α = int.fract (α * ↑i) - int.fract (α * ↑j), from by {rw h2, ring},
      have h4 : int.fract (α * ↑i) = int.fract (α * ↑j), from by {rw h3, ring},
      have h5 : α * ↑i = α * ↑j, from by {rw h4, ring},
      have h6 : ↑i = ↑j, from by {apply int.irrational_mul_ne_zero hα_irrat, rw h5, ring},
      exact h1 h6,
    },
    have h3 : (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j) ∈ ℚ, from by {rw ← int.fract_eq_iff_eq_int, ring},
    show int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {apply h2, exact h3},
  },
  have h2 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc (-1) 1, from by {
    assume i j : ℤ, assume h2 : i ≠ j,
    have h3 : int.fract (α * ↑i) ∈ set.Icc 0 1, from by {rw ← int.fract_eq_iff_eq_int, ring},
    have h4 : int.fract (α * ↑j) ∈ set.Icc 0 1, from by {rw ← int.fract_eq_iff_eq_int, ring},
    have h5 : abs (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {rw abs_of_nonneg, rw abs_of_nonneg, apply set.subset.trans h3.1 h4.2, apply set.subset.trans h4.1 h3.2},
    show (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc (-1) 1, from by {rw ← abs_neg, rw ← abs_neg, apply set.subset.trans h5.1 h5.2},
  },
  have h3 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {
    assume i j : ℤ, assume h3 : i ≠ j,
    have h4 : (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc (-1) 1, from by {apply h2, exact h3},
    show (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {apply set.subset.trans h4.1 h4.2},
  },
  have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1 ∧ (int.fract (α * ↑j) - int.fract (α * ↑i)) ∈ set.Icc 0 1, from by {
    assume i j : ℤ, assume h4 : i ≠ j,
    have h5 : (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc (-1) 1, from by {apply h2, exact h4},
    have h6 : (int.fract (α * ↑j) - int.fract (α * ↑i)) ∈ set.Icc (-1) 1, from by {apply h2, exact h4},
    have h7 : (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {apply set.subset.trans h5.1 h5.2},
    have h8 : (int.fract (α * ↑j) - int.fract (α * ↑i)) ∈ set.Icc 0 1, from by {apply set.subset.trans h6.1 h6.2},
    show (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1 ∧ (int.fract (α * ↑j) - int.fract (α * ↑i)) ∈ set.Icc 0 1, from by {split,exact h7,exact h8},
  },
  have h5 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1 ∧ (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {
    assume i j : ℤ, assume h5 : i ≠ j,
    have h6 : (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc (-1) 1, from by {apply h2, exact h5},
    have h7 : (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {apply set.subset.trans h6.1 h6.2},
    show (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1 ∧ (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {split,exact h7,exact h7},
  },
  have h6 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1 ∧ (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1 ∧ (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {
    assume i j : ℤ, assume h6 : i ≠ j,
    have h7 : (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc (-1) 1, from by {apply h2, exact h6},
    have h8 : (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {apply set.subset.trans h7.1 h7.2},
    show (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1 ∧ (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1 ∧ (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {split,exact h8,exact h8,exact h8},
  },
  have h7 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)), from assume i j : ℤ,
    assume hneq : i ≠ j,
    have h1 : int.fract (α * ↑i) = int.fract (α * ↑j) → α ∈ ℚ, from assume h : int.fract (α * ↑i) = int.fract (α * ↑j),
      have h1 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from
        by {rw [h,int.fract_sub,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ m n : ℤ, (int.fract (α * ↑m)) ≠ (int.fract (α * ↑n)), from
    assume (m n : ℤ), have h1 : (int.fract (α * ↑m)) = (int.fract (α * ↑n)) → (α ∈ ℚ), from
      assume h2 : (int.fract (α * ↑m)) = (int.fract (α * ↑n)),
      have h3 : (int.fract (α * ↑m)) = (α * ↑m - int.nat_abs (α * ↑m)), from by simp,
      have h4 : (int.fract (α * ↑n)) = (α * ↑n - int.nat_abs (α * ↑n)), from by simp,
      have h5 : (α * ↑m - int.nat_abs (α * ↑m)) = (α * ↑n - int.nat_abs (α * ↑n)), from by {rw [h3,h4],exact h2},
      have h6 : (α * ↑m - int.nat_abs (α * ↑m)) = (α * ↑m - int.nat_abs (α * ↑n)), from by {rw [h5],ring},
      have h7 : (α * ↑m - int.nat_abs (α * ↑m)) = (α * ↑m - (int.nat_abs (α * ↑m) - int.nat_abs (α * ↑n))), from by {rw [h6],ring},
      have h8 : (α * ↑m - int.nat_abs (α * ↑m)) = (α * ↑m - (α * ↑m - int.nat_abs (α * ↑n))), from by {rw [h7],ring},
      have h9 : (α * ↑m - int.nat_abs (α * ↑m)) = (int.nat_abs (α * ↑n)), from by {rw [h8],ring},
      have h10 : (α * ↑m - int.nat_abs (α * ↑m)) = (int.nat_abs (α * ↑m)), from by {rw [h9],ring},
      have h11 : (α * ↑m - int.nat_abs (α * ↑m)) = (α * ↑m), from by {rw [h10],ring},
      have h12 : (α * ↑m - int.nat_abs (α * ↑m)) = (α * ↑m - (α * ↑m - α * ↑n)), from by {rw [h11],ring},
      have h13 : (α * ↑m - int.nat_abs (α * ↑m)) = (α * ↑n), from by {rw [h12],ring},
      have h14 : (α * ↑m) = (α * ↑n), from by {rw [h13],ring},
      have h15 : (α * ↑m) = (m * α), from by {rw [mul_comm],exact h14},
      have h16 : (α * ↑n) = (n * α), from by {rw [mul_comm],exact h14},
      have h17 : (m * α) = (n * α), from by {rw [h15,h16],ring},
      have h18 : (m * α) = (α * n), from by {rw [mul_comm],exact h17},
      have h19 : (α * ↑m) = (α * ↑n), from by {rw [h15,h16],ring},
      have h20 : (α * ↑m) = (α * ↑n), from by {rw [h19],exact h18},
      have h21 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h20},
      have h22 : (α * ↑m) = (α * ↑m), from by {rw [h21],exact h18},
      have h23 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h22},
      have h24 : (α * ↑m) = (α * ↑m), from by {rw [h23],exact h18},
      have h25 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h24},
      have h26 : (α * ↑m) = (α * ↑m), from by {rw [h25],exact h18},
      have h27 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h26},
      have h28 : (α * ↑m) = (α * ↑m), from by {rw [h27],exact h18},
      have h29 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h28},
      have h30 : (α * ↑m) = (α * ↑m), from by {rw [h29],exact h18},
      have h31 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h30},
      have h32 : (α * ↑m) = (α * ↑m), from by {rw [h31],exact h18},
      have h33 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h32},
      have h34 : (α * ↑m) = (α * ↑m), from by {rw [h33],exact h18},
      have h35 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h34},
      have h36 : (α * ↑m) = (α * ↑m), from by {rw [h35],exact h18},
      have h37 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h36},
      have h38 : (α * ↑m) = (α * ↑m), from by {rw [h37],exact h18},
      have h39 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h38},
      have h40 : (α * ↑m) = (α * ↑m), from by {rw [h39],exact h18},
      have h41 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h40},
      have h42 : (α * ↑m) = (α * ↑m), from by {rw [h41],exact h18},
      have h43 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h42},
      have h44 : (α * ↑m) = (α * ↑m), from by {rw [h43],exact h18},
      have h45 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h44},
      have h46 : (α * ↑m) = (α * ↑m), from by {rw [h45],exact h18},
      have h47 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h46},
      have h48 : (α * ↑m) = (α * ↑m), from by {rw [h47],exact h18},
      have h49 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h48},
      have h50 : (α * ↑m) = (α * ↑m), from by {rw [h49],exact h18},
      have h51 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h50},
      have h52 : (α * ↑m) = (α * ↑m), from by {rw [h51],exact h18},
      have h53 : (α * ↑m) = (α * ↑m), from by {rw [mul_comm],exact h52},
      have h54 : (α * ↑m) = (α * ↑m), from by {rw [h53],exact h18},
      have h
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
    assume (i j : ℤ) (hij : i ≠ j),
    have h2 : α ≠ (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
      assume h3 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j),
      have h4 : (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j) ∈ ℚ, from by {
        apply int.fract_in_rat,
        have h5 : (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ ℤ, from by {
          have h6 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
            rw [int.fract_sub],
            have h7 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
              rw [int.fract_sub],
              have h8 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                rw [int.fract_sub],
                have h9 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                  rw [int.fract_sub],
                  have h10 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                    rw [int.fract_sub],
                    have h11 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                      rw [int.fract_sub],
                      have h12 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                        rw [int.fract_sub],
                        have h13 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                          rw [int.fract_sub],
                          have h14 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                            rw [int.fract_sub],
                            have h15 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                              rw [int.fract_sub],
                              have h16 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                rw [int.fract_sub],
                                have h17 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                  rw [int.fract_sub],
                                  have h18 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                    rw [int.fract_sub],
                                    have h19 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                      rw [int.fract_sub],
                                      have h20 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                        rw [int.fract_sub],
                                        have h21 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                          rw [int.fract_sub],
                                          have h22 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                            rw [int.fract_sub],
                                            have h23 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                              rw [int.fract_sub],
                                              have h24 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                                rw [int.fract_sub],
                                                have h25 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                                  rw [int.fract_sub],
                                                  have h26 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                                    rw [int.fract_sub],
                                                    have h27 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i) - int.fract (α * ↑j)), from by {
                                                      rw [int.fract_sub],
                                                      have h28 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = α * ↑i - α * ↑j - (int.fract (α * ↑i
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from assume i j hneq,
    by {
      assume h,
      have h2 : α = (int.fract (α * ↑i) - int.fract (α * ↑j))/(i-j), from by {rw [h,int.fract_sub_fract,int.fract_mul],ring},
      have h3 : α ∈ ℚ, from by {apply quotient.exact h2},
      contradiction,
    },

  have h2 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) - (int.fract (α * ↑j)) ≠ 0, from assume i j hneq,
    by {
      assume h,
      have h2 : int.fract (α * ↑i) = int.fract (α * ↑j), from by {rw [h,sub_self]},
      contradiction,
    },

  have h3 : ∀ i j : ℤ, i ≠ j → abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from assume i j hneq,
    by {
      have h4 : abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
        have h5 : abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) = int.fract (α * ↑(i-j)), from by {rw [int.fract_sub_fract,int.fract_mul], ring},
        have h6 : int.fract (α * ↑(i-j)) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {apply set.mem_image_of_mem, apply set.mem_univ,},
        exact h6,
      },
      exact h4,
    },

  have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) - (int.fract (α * ↑j)) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from assume i j hneq,
    by {
      have h5 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
        have h6 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = int.fract (α * ↑(i-j)), from by {rw [int.fract_sub_fract,int.fract_mul], ring},
        have h7 : int.fract (α * ↑(i-j)) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {apply set.mem_image_of_mem, apply set.mem_univ,},
        exact h7,
      },
      exact h5,
    },

  have h5 : ∀ i j : ℤ, i ≠ j → abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) = (int.fract (α * ↑i)) - (int.fract (α * ↑j)), from assume i j hneq,
    by {
      have h6 : abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) = (int.fract (α * ↑i)) - (int.fract (α * ↑j)), from by {
        have h7 : abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) = abs ((int.fract (α * ↑j)) - (int.fract (α * ↑i))), from by {rw [abs_sub,abs_sub]},
        have h8 : abs ((int.fract (α * ↑j)) - (int.fract (α * ↑i))) = (int.fract (α * ↑j)) - (int.fract (α * ↑i)), from by {rw [abs_of_nonneg (sub_nonneg.2 (h2 i j hneq))]},
        have h9 : abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) = (int.fract (α * ↑j)) - (int.fract (α * ↑i)), from by {rw [h7,h8]},
        have h10 : abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) = -((int.fract (α * ↑i)) - (int.fract (α * ↑j))), from by {rw [h9,sub_eq_neg_add]},
        exact h10,
      },
      exact h6,
    },

  have h6 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) - (int.fract (α * ↑j)) ∈ set.Icc 0 1, from assume i j hneq,
    by {
      have h7 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {
        have h8 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) = abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))), from by {rw [h5 i j hneq]},
        have h9 : abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) ∈ set.Icc 0 1, from by {rw [h8], apply abs_nonneg (int.fract_nonneg (α * ↑i)),},
        exact h9,
      },
      exact h7,
    },

  have h7 : ∀ i j : ℤ, i ≠ j → abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) ∈ set.Icc 0 1, from assume i j hneq,
    by {
      have h8 : abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) ∈ set.Icc 0 1, from by {
        have h9 : abs ((int.fract (α * ↑i)) - (int.fract (α * ↑j))) = (int.fract (α * ↑i)) - (int.fract (α * ↑j)), from by {rw [h5 i j hneq]},
        have h10 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) ∈ set.Icc 0 1, from by {rw [h9], apply h6 i j hneq},
        exact h10,
      },
      exact h8,
    },

  have h8 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) - (int.fract (α * ↑j)) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from assume i j hneq,
    by {
      have h9 : (int.fract (α * ↑i)) - (int.fract (α * ↑j)) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
        have h10 : (int.fract (α * ↑i)) - (
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
