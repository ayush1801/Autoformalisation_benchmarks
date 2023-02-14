import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $α$ be an irrational number
  assume α : ℝ,
  assume hα_irrat : irrational α,
  -- show the fractional parts of the integer multiples of $α$ form a dense subset of the unit interval
  have Icc_subset : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from --assume m : ℤ, by {rw int.fract_eq,
    assume m : ℤ, by {rw int.fract_eq, simp [int.fract_bound_eq], },
  have closure_subset_eq : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from by {rw ← Icc_subset, exact closure_subset _ _},
  have h1 : ∀ x, x ∈ set.Icc 0 1 → x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from begin
    assume (x : ℝ),
    assume : x ∈ set.Icc 0 1,
    have h2 : ∀ n : ℤ, ∃ (m : ℤ), ∃ (M : ℤ), (M ≥ 0 ∧ M ≤ n) ∧ 
      (int.fract (α * ↑m) - int.fract (α * ↑n)) < x ∧ int.fract (α * ↑m) ∈ set.Icc 0 1, from begin
      assume n : ℤ,
      have h3 : ∃ m : ℤ, int.fract (α * ↑m) < x, from begin
        have exists_nat : ∃ n : ℕ, (n : ℝ) ≥ x, from exists_nat_ge x,
        show ∃ m : ℤ, int.fract (α * ↑m) < x, from exists.elim exists_nat 
          (assume n, assume h4 : n ∈ ℕ, assume h5 : (↑n : ℝ) ≥ x,
          exists.elim h5 (assume h6 : ↑n = x,
            obtain (m : ℕ) (h7 : ↑n = ↑m * α) 
                     (h8 : ↑n > (↑m : ℝ) * α → abs (↑n - ↑m * α) ≤ 1), from hα_irrat x,
            have h9 : m ∈ ℤ, from exists.elim h8 (assume m : ℤ, assume h10 : ↑n = ↑m * α,
              have h11 : ↑m ∈ ℕ, from (nat.of_int_eq_coe.mp h10).symm ▸ h4,
              show m ∈ ℤ, from int.coe_nat_of_nat h11),
            have h10 : ↑(nat.fract m) = x, from nat.fract_eq_of_eq h7,
            have h11 : 1 ≥ 0, from trivial,
            have h12 : int.fract ↑m = int.fract (α * ↑m), from begin
              show int.fract ↑m = int.fract ↑m * α - int.fract ↑m + int.fract (α * ↑m), by ring,
            end,
            have h13 : int.fract ↑m = int.fract (α * ↑m), from by {rw nat.fract_eq (by {have h14 : ↑m ∈ ℤ, from exists.elim h8 (assume m : ℤ, 
              assume h15 : ↑n = ↑m * α, show ↑m ∈ ℤ, from int.coe_nat_of_nat h4), rw nat.fract_eq}), rw nat.fract_eq at h12,
            rw h10 at h12, rw ← h12, simp [int.fract_bound_eq], assumption,}, 
            have h14 : int.fract ↑m < x, from by {rw ← h10, rw int.fract_eq,
            simp [int.fract_bound_eq], assumption,},
            have h15 : int.fract (α * ↑m) = int.fract ↑m, from by rw [h13, mul_comm],
            have h16 : int.fract (α * ↑m) < x, from by rw ← h15 at h14,
            show _, from ⟨↑m, h9, h16⟩)),
        have h7 : ∃ (m : ℤ), int.fract (α * ↑m) < x, from exists.elim h3 (assume m : ℤ,
          assume h8 : int.fract (α * ↑m) < x, show _, from ⟨m, h8⟩),
        show ∃ (m : ℤ), ∃ (M : ℤ), (M ≥ 0 ∧ M ≤ n) ∧ 
          (int.fract (α * ↑m) - int.fract (α * ↑n)) < x ∧ int.fract (α * ↑m) ∈ set.Icc 0 1, from exists.elim h7 (assume m : ℤ, 
          assume h9 : int.fract (α * ↑m) < x, exists.elim h9 (assume h10 : int.fract (α * ↑m) < x,
          exists.elim (le_iff_exists_add.mp (le_of_lt h10)) (assume M : ℤ, assume h11 : int.fract (α * ↑m) + (↑M : ℝ) = x,
          exists.elim h11 (assume h12 : int.fract (α * ↑m) + ↑M = x,
          exists.elim h12 (assume h13 : int.fract (α * ↑m) + ↑M = x,
          show _, from ⟨int.of_nat (nat.fract m), by {have h14 : ↑m = ↑m * α, from mul_one_eq_of_irrational hα_irrat,
          rw h14 at h13, rw mul_comm at h13, rw nat.fract_eq at h13, rw ← nat.fract_eq at h13, rw ← h13, rw mul_comm, 
          rw int.of_nat_eq_coe, simp}, h13 ▸ le_refl _, by {rw int.fract_eq at h13, rw mul_comm at h13, simp at h13, rw [← h13,int.fract_add], ring,}, 
          by {have m_bound : ↑m ∈ ℤ, from nat.le.dest (nat.fract_le_nat h10) ▸ h9.1, 
          show int.fract (α * ↑m) ∈ set.Icc 0 1, from by {rw int.fract_eq, simp [int.fract_bound_eq], 
          have h14 : ↑m < ↑m + 1, from exists.elim h10 (assume h15 : α > 0, by linarith [h15]) ,
          have h15 : (↑m : ℝ) ≥ 0, from nat.succ_le_iff.mp h14, rw [int.fract_eq, mul_comm] at h10, 
          have h16 : (α * ↑m) - ↑m < α, from 
            begin 
              have h17 : (α * ↑m) - ↑m < ↑m + 1 - ↑m, from ← h10,
              have h18 : (α * ↑m) - ↑m < ↑m, from h17 ▸ nat.cast_succ_le_self h14,
              have h19 : (α * ↑m) - ↑m + ↑m = ↑m * α, from by ring, rw ← h19 at h18,
              have h20 : (α * ↑m) - ↑m + ↑m < ↑m * α, from h18, have h21 : (α * ↑m) - ↑
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  --Let $\alpha$ be an irrational number
  assume hα_irrat : irrational α,

  --Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$
  have h1 : ∀ (i j : ℤ) (h_ij_distinct : i ≠ j), int.fract (α * ↑i) ≠ int.fract (α * ↑j), from assume (i j : ℤ) (h_ij_distinct : i ≠ j), by
  {
    have h1_1 : α * ↑i - (α * ↑i) ≠ α * ↑j - (α * ↑j), from 
    begin  
      rw int.fract,
      rw int.fract,
      assume h : α * ↑i - (α * ↑i) = α * ↑j - (α * ↑j),
      rw [h,← int.cast_mul,← int.cast_mul i,← int.cast_mul j,← int.cast_mul (i-j),← int.cast_mul i] at h,
      have h1_1_1 : rational (α * ↑j - (α * ↑j)), from by {rw ← h, apply rat_of_real_fract_of_real,},
      have h1_1_2 : rational (α * ↑i - (α * ↑i)), by {apply rat_of_real_fract_of_real,},
      have h1_1_3 : rational ((↑i-j) * (α * ↑i - (α * ↑i))), from rat.mul_self h1_1_2,
      have h1_1_4 : (↑i-j) * (α * ↑i - (α * ↑i)) = (1 : ℝ), from by {rw ← int.cast_mul (i-j),rw ← h,rw ← int.cast_one,ring,},
      have h1_1_5 : rational ((1 : ℝ)), from h1_1_3,
      have h1_1_6 : ((1 : ℝ)) = (1 : ℚ), by {apply rat.eq_of_mul_self_eq_one h1_1_5,}, 
      have h1_1_7 : ((1 : ℝ)) = rat.cast ((1 : ℚ)), by {rw h1_1_6,rw rat.cast_one,},
      have h1_1_8 : ((1 : ℝ)) = 1, by {rw ← h1_1_7,apply rat.cast_injective,},
      have h1_1_9 : 1 ≠ 0, from by {unfold has_zero.zero,rw h1_1_8,refl,},
      have h1_1_10 : ↑i - j ≠ 0, from by {contradiction,},
      rw [h1_1_4,← int.cast_mul (↑i-j),← int.cast_mul (↑i-j),← int.cast_mul (↑i-j),int.cast_one] at h1_1_1,
      rw [← int.cast_mul (↑i-j)] at h1_1_3,
      have h1_1_11 : (1 : ℚ) * ((↑i-j) * α) = (1 : ℚ), from by {rw ← int.cast_mul (↑i-j),rw ← rat.cast_one,rw ← h,rw ← rat.cast_mul,rw ← rat.cast_mul,ring,},
      have h1_1_12 : (1 : ℚ) * ((↑i-j) * α) = (1 : ℚ), from by {rw ← rat.cast_one,rw ← h1_1_1,rw rat.cast_mul,rw rat.cast_mul,},
      have h1_1_13 : (1 : ℚ) = rat.cast ((↑i-j) * α), from by {rw h1_1_12,rw h1_1_11,},
      have h1_1_14 : (1 : ℝ) = (↑i-j) * α, from by {rw ← rat.cast_one,rw ← h1_1_13,apply rat.cast_injective,},
      have h1_1_15 : (1 : ℝ) = ((↑i-j) : ℚ) * α, from by {rw ← int.cast_mul (i-j),rw h1_1_14,},
      have h1_1_16 : (1 : ℝ) = ((↑i-j) : ℚ) * α, from by {rw ← rat.cast_one,rw ← h1_1_15,apply rat.cast_injective,},
      have h1_1_17 : (1 : ℚ) = ((↑i-j) : ℚ) * α, from by ring at h1_1_16,
      exact hα_irrat h1_1_17,
    end,
    exact ne_of_lt (abs_int_fract_lt_one (α * ↑i)) (abs_int_fract_lt_one (α * ↑j)) h1_1,
  },

  --If this were not true, then
  --$$
  --i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,
  --$$
  --which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
  have h2 : ∀ (i j : ℤ) (h_ij_distinct : i ≠ j), rat.cast (α) ≠ (((rat.cast (α * ↑i)) - (rat.cast (α * ↑j))) / (↑i - ↑j)), from 
  assume (i j : ℤ) (h_ij_distinct : i ≠ j),
  begin
    assume h : rat.cast (α) = (((rat.cast (α * ↑i)) - (rat.cast (α * ↑j))) / (↑i - ↑j)),
    rw [rat.cast_mul,rat.cast_mul] at h,
    have h1 : (rat.cast (α * ↑i)) - (rat.cast (α * ↑j)) = (rat.cast (α)) * (↑i - ↑j), from by {rw ← h,ring,},
    have h2 : rat.cast (α * ↑i) - rat.cast (α * ↑j) = rat.cast (α) * (↑i - ↑j), from by rw [rat.cast_mul] at h1,
    have h3 : rat.cast (α * ↑i) = rat.cast (α) * ↑i, from by {apply rat.mul_self,},
    have h4 : rat.cast (α * ↑j) = rat.cast (α) * ↑j, from by {apply rat.mul_self,},
    have h5 : rat.cast (α) = rat.cast (α) * ↑i, from by {apply rat.cast_injective,},
    have h6 : rat.cast (α) = rat.cast (((↑i) : ℚ) * α), from by rw [← h5,← rat.cast_one,← rat.cast_mul,← rat.cast_mul],
    have h7 : rat.cast (α) = rat.cast (((↑i) : ℚ) * α), from by ring at h3,
    have h8 : rational (rat.cast (α)), from by {apply rat.cast_ne_zero,},
    have h9 : rat.cast (((↑i) : ℚ) * α) ≠ rat.cast 0, from by {contradiction,},
    have h10 : rat.cast (α) ≠ 0,
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number. Then
  assume hα_irrat : irrational α,
  -- for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. 
  have h2 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from 
  assume (i j : ℤ) (hne : i ≠ j),
  -- If this were not true, then $i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor$,
  have h2a : (α * ↑i) - (int.to_nat (α * ↑i)) = (int.fract (α * ↑i)) := by {rw fract_eq_sub_floor,ring},
  have h2b : (α * ↑j) - (int.to_nat (α * ↑j)) = (int.fract (α * ↑j)) := by {rw fract_eq_sub_floor,ring},
  assume h2c : (int.fract (α * ↑i)) = (int.fract (α * ↑j)),
  rw h2c at h2a h2b,
  -- which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$. 
  have h2d : (α - int.fract α) + (int.fract α) = α := by ring,
  have h2e : (int.fract α) = α - (α - int.fract α) := by ring,
  have h2f : (α - int.fract α) = (α * ↑i) - (int.to_nat (α * ↑i)) := by rw h2a,
  have h2g : (int.fract α) = (α * ↑j) - (int.to_nat (α * ↑j)) := by rw h2b,
  have h2h : (α - int.fract α) = (α * ↑j) - (int.to_nat (α * ↑j)) := by rw h2e h2g,
  have h2i : (α - int.fract α) - ((α * ↑j) - (int.to_nat (α * ↑j))) = 0 := by rw h2f h2h,
  have h2j : (α * ↑i) - (int.to_nat (α * ↑i)) - ((α * ↑j) - (int.to_nat (α * ↑j))) = 0 := by rw ← nat.cast_sub h2i,
  have h2k : (int.to_nat (α * ↑i)) - (int.to_nat (α * ↑j)) = 0 := by rw ← int.coe_nat_sub h2j,
  have h2l : (int.to_nat (α * ↑i)) = (int.to_nat (α * ↑j)) := by rw nat.eq_zero_iff_zero_eq h2k,
  have h2m : (α * ↑i) = (α * ↑j) := by {rw ← int.cast_mul,repeat {rw ← int.coe_nat_eq_coe_nat_iff},exact h2l},
  have h2n : (α * (↑i - ↑j)) = 0 := by rw h2m,
  have h2o : α = 0 := by rw int.cast_mul h2n,
  have h2p : (α - int.fract α) + (int.fract α) = α := by ring,
  have h2q : (int.fract α) = α - (α - int.fract α) := by ring,
  have h2r : (α - int.fract α) = (α * ↑i) - (int.to_nat (α * ↑i)) := by rw h2a,
  have h2s : (int.fract α) = (α * ↑j) - (int.to_nat (α * ↑j)) := by rw h2b,
  have h2t : (α - int.fract α) = (α * ↑j) - (int.to_nat (α * ↑j)) := by rw h2q h2s,
  have h2u : (α - int.fract α) - ((α * ↑j) - (int.to_nat (α * ↑j))) = 0 := by rw h2r h2t,
  have h2v : (α * ↑i) - (int.to_nat (α * ↑i)) - ((α * ↑j) - (int.to_nat (α * ↑j))) = 0 := by rw ← nat.cast_sub h2u,
  have h2w : (int.to_nat (α * ↑i)) - (int.to_nat (α * ↑j)) = 0 := by rw ← int.coe_nat_sub h2v,
  have h2x : (int.to_nat (α * ↑i)) = (int.to_nat (α * ↑j)) := by rw nat.eq_zero_iff_zero_eq h2w,
  have h2y : (α * ↑i) = (α * ↑j) := by {rw ← int.cast_mul,repeat {rw ← int.coe_nat_eq_coe_nat_iff},exact h2x},
  have h2z : (α * (↑i - ↑j)) = 0 := by rw h2y,
  have h2aa : α = 0 := by rw int.cast_mul h2z,
  have h2ab : false := by {apply hα_irrat h2aa,},
  exact absurd h2ab (show (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from h2ab),

  -- Hence, $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$
  have h3 : univ ⊆ (Π (m : ℤ), (int.fract (α * ↑m))), from by {
    assume (n : ℤ),
    existsi n, simp, },

  -- is an infinite subset of $\left[0,1\right]$
  have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from 
    assume (i j : ℤ) (hne : i ≠ j), h2 i j hne,
  have h5 : ((λ m : ℤ, (int.fract (α * ↑m))) '' univ) = univ, from by rw set.eq_univ_of_forall h4,

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$. One can thus find pairs of elements of $S$ that are arbitrarily close. Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
  have h6 : closure ((λ m : ℤ, (int.fract (α * ↑m))) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from 
    by rw ← h5.symm; apply closure_subset,

  -- To show that $S$ is dense in $[0, 1]$,
  have h7 : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → ∃ z : ℤ, 0 < (int.fract (α * ↑z)) ∧ (int.fract (α * ↑z)) ≤ y, from 
    by {
      -- consider $y \in[0,1]$, and $\epsilon>0$. 
      assume (y : ℝ) (hy_pos : 0 ≤ y) (hy_le_one : y ≤ 1),
      --
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  --let S := {x : ℝ | ∃ m : ℤ, x = α * (↑m)},

  -- let $S := \{\{x\} \mid x \in \R \}$
  let S : set ℝ := {int.fract x | x : ℝ},
  -- S is an infinite subset of $[0,1]$, by the comment above
  have hS_infinite : infinite S, from by
    { -- (the fractional parts of) the integer multiples of an irrational number form an infinite set
    -- hence S is an infinite set, as required
    exact @set.infinite_of_injective_to_univ ℝ _ ℤ (λ (x : ℝ), int.fract x)
      (λ x y, int.fract_eq_fract) (λ (m : ℤ), int.fract (α * ↑m))
      (mt (int.fract_eq_of_irrational_of_eq hα_irrat))
      (λ m x, begin
        { assume hx : x = α * ↑m,
        have h1 : (int.fract (α * ↑m)) = int.fract x, from by {rw hx, refl,},
        apply @exists_of_mem ℝ _ _ _ _ _ h1, },
        end)
      (λ x, int.fract_ne_zero),
  },
  -- The set of integers is bounded
  let Z : set ℤ := set.Icc (int.of_nat 0) (int.of_nat 0),
  have hZ_bounded : is_bounded_above Z, from by {exact set.bounded_univ,},

  -- The fractional parts of the integer multiples of an irrational number is a subset of the unit interval
  have h1 : ((λ (m : ℤ), int.fract (α * ↑m) ) '' (@set.univ ℤ)) ⊆ S, from @set.subset.trans ((λ (m : ℤ), int.fract (α * ↑m)) '' Z) _ _ (set.image_subset_iff.mpr ⟨by obviously, by obviously⟩),
  -- The fractional parts of the integer multiples of an irrational number is dense in the unit interval
  have h2 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from
    begin
    have h3 : ∀ (x : ℝ) (hx : x ∈ closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), ∃ (n : ℤ), n * (((int.fract (α * ↑n) : ℝ)) - x) > 0, from
      begin
        assume (x : ℝ) (hx : x ∈ closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)),
        show ∃ (n : ℤ), n * (((int.fract (α * ↑n) : ℝ)) - x) > 0, from by
        { -- There exists a limit point of $S$ in $[0,1]$, by the Bolzano-Weierstrass theorem
        -- Hence there exists an $x$ such that $(int.fract (α * ↑(int.of_nat 0)) : ℝ) < x < (int.fract (α * ↑(int.of_nat 1)) : ℝ)$
        -- Hence there exists an $n$ such that $n * (((int.fract (α * ↑n) : ℝ)) - x) > 0$
        have h4 : ∃ (n : ℤ), n * (((int.fract (α * ↑n) : ℝ)) - x) > 0, from by
          {
          have h5 : interval.is_open (set.Icc (int.fract (α * ↑(int.of_nat 0))) (int.fract (α * ↑(int.of_nat 1)))) :=
            interval.is_open_Ioo (int.fract (α * ↑(int.of_nat 0))) (int.fract (α * ↑(int.of_nat 1))),
          have h6 : x ∈ closure (λ (m : ℤ), int.fract (α * ↑m) ) '' (@set.univ ℤ), from hx,
          have h7 : ∃ (n : ℤ), n * (((int.fract (α * ↑n) : ℝ)) - x) > 0, from @exists_nat_gt _ _
            (λ (n : ℤ), (int.fract (α * ↑n) : ℝ) - x) 0
            (mt (by {exact int.fract_lt_one (α * ↑(int.of_nat 1)),}) x) h4,
          exact h7, },
        exact h4, },
      end,
      show closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from
      begin
      have h5 : ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from
        begin
        have h6 : (int.fract (α * ↑(int.of_nat 0)) : ℝ) = 0, from by
          {
          have h7 : (int.fract (α * ↑(int.of_nat 0)) : ℝ) = int.fract (int.of_nat 0), from by
            {
            have h8 : (int.fract (α * ↑(int.of_nat 0)) : ℝ) = int.fract (int.of_nat 0), from by
              {
              have h9 : ∀ (m : ℤ), int.fract (α * ↑m) = int.fract (int.of_nat (int.nat_abs m)), from
                begin
                have h10 : ∀ (m : ℤ), int.fract (α * ↑m) = int.fract (int.of_nat (int.nat_abs m)), from begin
                    assume (m : ℤ),
                    have h11 : int.fract (α * ↑m) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from
                    by apply @set.mem_image _ _ ℤ _ _ _ _ (int.fract (α * ↑m)) m,
                    have h12 : (int.fract (α * ↑m)) ∈ closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from h11,
                    have h13 : (int.fract (α * ↑m)) ∈ set.Icc 0 ((int.fract (α * ↑(int.of_nat 1))) : ℝ), from @mem_of_mem_closure ℝ _ _ (λ (m : ℤ), int.fract (α * ↑m)) h5
                    (int.fract (α * ↑m)) h12,
                    show int.fract (α * ↑m) = int.fract (int.of_nat (int.nat_abs m)), from begin
                      show int.fract (α * ↑m) = int.fract (int.of_nat (int.nat_abs m)), from by
                      {
                      have h14 : (int.fract (α * ↑m) : ℝ) < ((int.fract (α * ↑(int.of_nat 1)) : ℝ)), from by
                        {
                        exact @show (int.fract (α * ↑(int.of_nat 0))) < (int.fract (α * ↑(int.of_nat 1))), from
                        begin
                        have h15 : int.fract (int.of_nat (int.nat_abs (int.of_nat 1))) = int.fract (α * ↑(int.
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- don't know how to prove this yet, but it's true
  obviously,
end

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Lebesgue measure theory, one can show that the set (irrationals) has measure $1$.
  have h1 : measure_theory.measure (set.Icc 0 1) = 1, from by {
    rw [measure_theory.measure_Icc, measure_theory.measure_Icc_self],
    norm_num, },
  have h2 : measure_theory.is_measurable (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by {
    rw ← (measure_set_closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))),
    rw ← measure_theory.measure_univ, exact measure_theory.is_measurable_univ,
  },
  -- Then one can show that the closure of rationals has measure $1$.
  have h3 : measure_theory.measure (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))) = 1, from by {
    rw measure_set_closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)),
    -- By the Axiom of Choice, the set of rationals is countable.
    have h4 : fintype.card ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ≤ ℕ, from by {
      apply fintype.card_image_le,
      have h5 : fintype.card (set.univ) ≤ ℕ, { exact fintype.card_le_nat (fintype.card_univ : fintype.card (set.univ) ≤ ℕ) },
      rw ← fintype.card_fintype at h5, show fintype.card (λ (m : ℤ), int.fract (α * ↑m)) ≤ ℕ, from by {exact h5, },
    },
    rw ← ← card_set_closed_fract,
    show fintype.card ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ≤ fintype.card (set.univ), from by {
      rw ← fintype.card_fintype, exact h4, },
    norm_num, },
  have h6 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = set.Icc 0 1, from by {
    show (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) = set.Icc (0 : ℝ) 1, from 
    eq.symm (eq_of_measure_eq_of_measurable h1 h2 h3), },
  exact h6,
end

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  /-
    The fractional parts of the integer multiples of an irrational number form a dense subset of the unit interval
  -/
  sorry
end

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let α_set := (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ),
  have h1 : (α_set : set ℝ) = (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {obviously},
  -- Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
  have h2 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)), from assume (i j : ℤ) (hij : i ≠ j), by {
    -- Then $i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor$,
    have hij2 : int.fract (α * ↑i) = int.fract (α * ↑j), from int.fract_mul_cancel_left hij,
    -- which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
    have hα_rat : ℚ/1 = (α * ↑i - ↑i * int.fract (α * ↑i) - α * ↑j + ↑j * int.fract (α * ↑j)) / (↑i - ↑j), from by {rw [hij2, add_sub_cancel'],norm_cast, ring,},
    have hα_rat2 : ℚ/1 = (α * ↑i - α * ↑j - ↑i * int.fract (α * ↑i) + ↑j * int.fract (α * ↑j)) / (↑i - ↑j), from by {ring,},
    -- Then $i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor$, which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
    have hα_rat3 : ℚ/1 = (α * ↑i - α * ↑j) / (↑i - ↑j), from by {ring,},
    have hα_rat4 : ℚ/1 = α * (↑i - ↑j) / (↑i - ↑j), from by {ring,},
    -- hence, we must have $\{i \alpha\} \neq\{j \alpha\}$
    have hα_rat5 : α ≠ ℚ/1, from by {apply hα_irrat, rw ←hα_rat4,},
    have hα_rat6 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {ring at hα_rat5,exact hα_rat5,},
    show int.fract (α * ↑i) ≠ int.fract (α * ↑j) end,

  -- Hence, $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$ is an infinite subset of $\left[0,1\right]$.
  have h3 : α_set.finite = ff, from by {
    have h3 : ∀ i : ℤ, (i : ℝ) ≠ 0, from assume i : ℤ, by {
      assume h : (i : ℝ) = 0,
      from show i ≠ 0, from dec_trivial,},
    have h4 : ∀ i : ℤ, int.fract (α * ↑i) ≠ 0, from assume i : ℤ, by {
      assume h : int.fract (α * ↑i) = 0,
      have h5 : int.fract (α * ↑i) = int.fract (↑i * (α : ℤ)), from by {
        rw ← int.fract_mul_cancel_left,norm_cast,ring,},
      -- have h5 : int.fract (α * i) = 0, from by {rw ← int.fract_mul_cancel_left,norm_cast,ring,},
      show int.fract (α * i) ≠ 0, from by {rw h5 at h, exact h3 i h,},},
    have h5 : ∀ i : ℤ, (int.fract (α * ↑i) : ℝ) ≠ 0, from assume i : ℤ, by {
      assume h : (int.fract (α * ↑i) : ℝ) = 0,
      from show int.fract (α * ↑i) ≠ 0, from by { rw ← show (int.fract (α * ↑i) : ℝ) = ((int.fract (α * ↑i) : ℝ) * (1 : ℝ)) / (1 : ℝ), from by { norm_cast, ring }, },}, 

    show α_set.finite = ff, from by {
      unfold α_set,
      rw ← set.finite_univ,
      apply infinite.infinite_iff_fintype_nonempty,
      apply by { existsi ℤ, split,apply fintype.of_injective_of_not_mem_empty (λ x y, by {
        assume h : x ≠ y, exact h2 x y h}) h5, apply nonempty.intro (0 : ℤ),}
      },},
  have h4 : ∀ (j : ℤ), ∃! (i : ℤ), i ≠ j ∧ int.fract (α * ↑i) = int.fract (α * ↑j), from by {
    assume j : ℤ,
    -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
    have h4 : ∃! (i : ℤ), (int.fract (α * ↑i) : ℝ) = 0, from by {
      have h4 : ∀ (i : ℤ), (int.fract (α * ↑i) : ℝ) = 0 → i = 0, from by {
        assume i : ℤ, assume h : (int.fract (α * ↑i) : ℝ) = 0,
        have h5 : int.fract (α * ↑i) = 0, from by {
          have h5 : (int.fract (α * ↑i) : ℝ) = 0, from by {rw ← show ((int.fract (α * ↑i) : ℝ) : ℤ) = (int.fract (α * ↑i) : ℤ), from by {norm_cast,},},
          show int.fract (α * ↑i) = 0, from by {rw h5 at h, exact h,},},
        show i = 0, from by {rw h5, ring,},},
      have h5 : ∃ i : ℤ, (int.fract (α * ↑i) : ℝ) = 0, from by {
        have h5 : ∀ i : ℤ, (i : ℤ) ≠ 0 → (int.fract (α * ↑i) : ℝ) ≠ 0, from by {
          assume i : ℤ, assume hi : (i : ℤ) ≠ 0,
          have hi2 : (int.fract (α * ↑i) : ℝ) ≠ 0, from by {
            have hi2 : int.fract (α * ↑i) ≠ 0, from by {
              have hi2 : int.fract (α * ↑i) ≠ 0, from by {
                have hi2 : (i : ℝ) ≠ 0, from by {rw ← show (i : ℤ) ≠ (0 : ℤ), from hi,},
                show
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
    -- Consider $S$
    let S : set ℝ := λ i : ℤ, has_fract.fract i α,
    
    -- $S$ is an infinite subset of $\left[0,1\right]$
    have h1 : S ⊆ Icc 0 1 ∧ infinite S, from by {
      split,
      have h2 : ∀ i : ℤ, (0 ≤ has_fract.fract i α) ∧ (has_fract.fract i α < 1), from by {
        assume i : ℤ,
        have l : 0 ≤ has_fract.fract i α, from by {
              rw ← int.coe_nat_add, rw int.coe_nat_zero, rw int.fract_eq, ring,
              from int.fract_nonneg},
        have r : has_fract.fract i α < 1, from by {
              rw int.fract_eq, ring, rw int.coe_nat_zero, rw int.coe_nat_one,ring,
              from int.fract_lt_one},
        show (0 ≤ has_fract.fract i α) ∧ (has_fract.fract i α < 1), from ⟨l, r⟩,
      },
      from set.subset.antisymm (λ i : ℤ, (h2 i).left) (λ i : ℤ, (h2 i).right),
      have h3 : ∀ i j : ℤ, i ≠ j → has_fract.fract i α ≠ has_fract.fract j α, from by {
        assume i j : ℤ, assume h : i ≠ j,
        have h1 : i * α ≠ j * α, from by {
          assume h2 : i * α = j * α,
          have h3 : α = (i-j)*⁻¹*(i*α - j*α), from by {
            rw [h2, int.neg_mul_eq_neg_mul_symm, sub_eq_neg_add], rw add_comm, rw add_mul, ring,
          },
          have h4 : (i-j)*⁻¹*(i*α - j*α) ∈ ℤ, from by {
            rw h3, apply int.coe_nat_div_int, intros h4, exact h4.elim (λ h5 : j = 0, by {
              calc
                i = i*1 : by {rw mul_one}
                ... = i * (j+j) : by {rw h5, rw zero_add}
                ... = j* (i+i) : by {rw mul_comm, ring}
                ... = 0 : zero_mul,
              apply h.symm,
            }), intros h5, have h6 := h5.symm, have h7 : i - j ≠ 0, from h.symm,
            apply int.ne_of_nat_ne_nat (int.coe_nat_ne_coe_nat_of_ne h7),
          },
          have h5 : irrational α, from hα_irrat,
          show false, from h5 h4,
        },
        have h2 : i * α - j * α ≠ 0, from (int.ne_of_mul_ne_zero h1),
        have h3 : (i-j)*⁻¹ ≠ 0, from by {
          intros h4, exact absurd h4 ((int.coe_nat_ne_coe_nat_of_ne h).symm),
        },
        have h4 : (i * α - j * α) * (i-j)⁻¹ ≠ 0, from 
          by {rw ← inv_eq_iff_mul_eq_one, apply mul_ne_zero, exact h2, exact h3},
        have h5 : i*α-j*α ≠ 0, from 
          by {rw ← mul_inv_cancel h4, rw mul_one},
        have h6 : i * α - j * α ∈ ℤ, from by {
          rw ← int.fract_eq, ring, exact int.fract_nonneg, exact int.fract_lt_one,
        },
        have h7 : int.fract (i * α) ≠ int.fract (j * α), from by {
          rw int.fract_eq, ring, rw int.coe_nat_zero, rw int.coe_nat_zero, ring,
          from h5,
        },
        show has_fract.fract i α ≠ has_fract.fract j α, from h7,
      },
      from ⟨infinite_int, h3⟩,
    },

    -- So, $S$ has a limit point in $[0, 1]$
    have h2 : limit_point S (Icc 0 1), from by {
      have h3 : limit_point S (closure (Icc 0 1)), from by {
        rw ← closure_Icc, 
        rw ← closure_eq_of_is_closed (is_closed_Icc 0 1),
        apply h1.right.limit_point,
      },
      show limit_point S (Icc 0 1), from by {
        apply limit_point_of_limit_point_of_closed h3, from is_closed_Icc 0 1,
      },
    },
    -- Show that $S$ is dense in $[0, 1]$
    have h3 : dense S (Icc 0 1), from by {
      assume y : ℝ, assume hi : y ∈ Icc 0 1, assume ε : ℝ, assume hε : 0 < ε,
      have h4 : ∃ x : ℝ, x ∈ S ∧ x < ε, from h2.mem_of_lt_ne hi hε,
      obtain (x : ℝ) (hx : x ∈ S ∧ x < ε), from h4,
      have h5 : y - x ∈ set.Icc (-ε) ε, from by {
        calc
          y - x ∈ set.Icc 0 1 : by {
            rw ← hi, rw ← sub_zero,
            from set.sub_mem_iff.mp hx.right,
          }
          ... = set.Icc (-ε) ε : by {
            rw ← sub_eq_add_neg, rw ← Icc_eq_Ico,
            rw ← sub_eq_add_neg, rw ← Icc_eq_Ico,
            rw ← sub_zero, rw ← add_neg_cancel'_left ε,
            rw ← add_comm, rw ← add_zero, rw ← Ico_neg_Ico,
            rw ← one_add_one, rw ← Ico_eq_Ioo,
            rw ← sub_neg_eq_add, ring,
          },
      have h6 : abs (y - x) ∈ set.Icc 0 ε, from set.mem_Icc_of_mem_Icc h5 (hε),
      from set.Icc_mem_Icc.mp (h2.exists_of_mem_of_ne_of_lt h6 hε (λ h, by {
        show false, from begin
          rw ← hi, rw ← sub_zero,
          from or.elim (lt_or_gt 0 x) (λ h1, by {
            have h2 : 0 < ε - x, from sub_pos_of_lt hε,
            have h3 : y < ε - x, from by {
              have h4 : y < ε, from by {
                apply set.mem_Icc.mp h6, simp,
              },
              rw ← hi, rw ← sub_zero,
              from lt_of_lt_of_le h4 hx.right,
            },
            show false, from absurd h3 ((lt_irrefl ε) h2),
          }) (λ h1, by {
            have
end --Needs more than 2000 tokens!

--OUTPUT 10
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  apply le_antisymm,
  {
    intros x hx hxstd,
    rcases set.mem_closure_iff.1 hx with ⟨d, hd⟩ | ⟨n, hn, hnstd⟩,
    {
      use [d, hd],
      rw ← sub_nonneg,
      unfold set.mem,
      split,
      {
        exact lt_of_le_of_lt (int.fract_nonneg d) (hnstd),
      },
      {
        rw le_iff_not_lt,
        intro hlt,
        apply hlt,
        rw ← lt_sub_iff_add_lt,
        apply trans_rel_left,
        apply le_of_lt,
        apply int.lt_add_one_of_fract_lt,
        assumption,
      },
    },
    {
      use [n, hn],
      exact hnstd,
    },
  },
  {
    intros x hx,
    cases exists_lt_of_lt_one hx with y hy,
    cases exists_lt_of_lt_one hy with z hz,
    by_contradiction hzstd,
    rw <- hzstd at hz,
    apply lt_irrefl _ hz,
    rw [← int.fract_eq_iff_lt_one, ← lt_sub_iff_add_lt, ← int.lt_add_one_iff_fract_lt],
    apply le_of_lt,
    rw ← set.mem_image_iff,
    apply hx,
    use [z, hz],
    intro hnz,
    apply hnzstd,
    rw ← hnz,
    assumption,
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
