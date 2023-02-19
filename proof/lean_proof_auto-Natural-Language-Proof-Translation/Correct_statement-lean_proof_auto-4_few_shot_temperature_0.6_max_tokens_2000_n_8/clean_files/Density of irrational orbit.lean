import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), 
  from by auto [int.fract_eq_iff, int.coe_nat_ne_zero, hα_irrat, int.coe_nat_inj, subtype.ext, int.coe_nat_inj],

  have h2 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' univ) ⊆ Icc (0 : ℝ) (1 : ℝ), 
  from by auto [closure_subset_iff, int.fract_nonneg, int.fract_lt_one],

  have h3 : ∀ (m : ℤ), (int.fract (α * ↑m)) ∈ Icc (0 : ℝ) (1 : ℝ), 
  from by auto [int.fract_nonneg, int.fract_lt_one],

  have h4 : ∀ (m : ℤ), (int.fract (α * ↑m)) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' univ), 
  from by auto [closure_iff, h3, h2],

  have h5 : ∀ (m : ℤ), (int.fract (α * ↑m)) ∈ set.Icc 0 1, 
  from by auto [h4, h2],

  have h6 : Icc (0 : ℝ) (1 : ℝ) ⊆ closure ((λ m : ℤ, int.fract (α * ↑m)) '' univ), 
  from by auto [closure_iff, h5],

  show Icc 0 1 = closure ((λ m : ℤ, int.fract (α * ↑m)) '' univ), 
  from by auto [closure_subset_iff, h6]

end

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := 
begin
  let S : set ℝ := {x : ℝ | ∃ m : ℤ, x = int.fract (α * ↑m)},
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j),
  from begin
    assume i j h1 h2,
    have h3 : (α = (int.fract (α * ↑i) - int.fract (α * ↑j))/(i-j)),
    from by auto [int.fract_add, int.fract_mul, int.fract_eq_of_eq, h2],
    have h4 : (α ∈ ℚ), from by auto [h3],
    exact absurd h4 hα_irrat,
  end,
  have h2 : S.nonempty, from by auto [h1, exists_int],
  have h3 : ∃ x : ℝ, x ∈ S, from by auto using [exists_int],
  have h4 : S ⊆ set.Icc 0 1, from by auto [int.fract_lt_one, int.fract_nonneg],
  have h5 : ∀ x : ℝ, x ∈ S → x ∈ closure S, from by auto [mem_closure_iff_nhds],
  have h6 : ∀ x : ℝ, x ∈ S → x ∈ closure S, from by auto [mem_closure_iff_nhds],
  have h7 : ∀ (x : ℝ) (hx : x ∈ S), closure S ⊆ closure (set.Icc 0 1), from by auto [closure_mono],
  have h8 : closure S ⊆ closure (set.Icc 0 1), from by auto [h7],
  have h9 : closure (set.Icc 0 1) ⊆ closure S, from by auto [closure_mono],
  have h10 : closure S = closure (set.Icc 0 1), from by auto [set.eq_of_subset_of_subset_of_empty h8 h9],
  have h11 : ∀ (x : ℝ) (hx : x ∈ S), closure S ⊆ closure (set.Icc 0 1), from by auto [closure_mono],
  have h12 : closure S ⊆ closure (set.Icc 0 1), from by auto [h11],
  have h13 : closure (set.Icc 0 1) ⊆ closure S, from by auto [closure_mono],
  have h14 : closure S = closure (set.Icc 0 1), from by auto [set.eq_of_subset_of_subset_of_empty h12 h13],
  have h15 : closure S = closure (set.Icc 0 1), from by auto [h14],
  show closure S = set.Icc 0 1, from by auto [h15],
end

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ n m : ℤ, (n ≠ m) → (int.fract (α * ↑n) ≠ int.fract (α * ↑m)),
  begin
    assume (n m : ℤ) (h1 : n ≠ m),
    assume h2 : (int.fract (α * ↑n)) = (int.fract (α * ↑m)),
    have h3 : (α * ↑n) = (α * ↑m), from by auto [int.fract_eq_iff] using [h1, h2],
    have h4 : α = (↑m * α * ↑n⁻¹) ∈ ℚ, from by auto [mul_comm, mul_assoc, mul_comm, ←mul_assoc, mul_inv_cancel] using [h1, h3, int.coe_nat_ne_zero],
    show false, from by auto [hα_irrat] using [h4],
  end,

  let seq_limit : (ℕ → ℝ) → ℤ → ℝ → Prop := 
  λ (u : ℕ → ℝ) (l : ℤ) (l' : ℝ), ∀ ε > 0, ∃ N, ∀ n > N, |u n - l'| < ε,

  have h2 : ∀ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0,
  begin
    assume (l : ℤ),
    assume (ε),
    assume (h3 : ε > 0),
    use (l + 1),
    assume (n),
    assume (h4 : n > l + 1),
    have h5 : (int.fract (α * ↑(n - 1))) = (int.fract (α * ↑l)), from by auto [int.fract_eq_iff] using [h1],
    have h6 : (int.fract (α * ↑n)) = (int.fract (α * ↑(n - 1))), from by auto [mul_sub_left_distrib, int.fract_add],
    have h7 : (int.fract (α * ↑n)) = (int.fract (α * ↑l)), from by auto [h5, h6],
    have h8 : |(int.fract (α * ↑n))| < ε, from by auto [int.fract_int_lt, h4, h7],
    show |(int.fract (α * ↑n)) - 0| < ε, from by auto [h8],
  end,

  have h3 : ∀ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [h2] using [h2],

  have h4 : ∀ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [h3] using [h3],

  have h5 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h6 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h7 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h8 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h9 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h10 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h11 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h12 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h13 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h14 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h15 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h16 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h17 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h18 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h19 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h20 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h21 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h22 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h23 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h24 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h25 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h26 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto [exists.intro] using [h2],

  have h27 : ∃ (l : ℤ), seq_limit (λ (n : ℕ), int.fract (α * ↑n)) l 0, from by auto
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let S := (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ),
  let S_nonempty : ¬ S = ∅ := set.ne_empty_iff_exists_mem.2 ⟨0, ⟨0, by simp⟩⟩,
  let S_clos_S : closure S = S := set.closure_eq_of_is_closed (show is_closed S, from set.is_closed_Icc_iff.2 ⟨S_nonempty, S_nonempty⟩),
  have h1 : ∀ (i : ℤ) (j : ℤ), i ≠ j → ⟨int.fract (α * ↑i), 0, 1⟩ ≠ ⟨int.fract (α * ↑j), 0, 1⟩,
  begin
    assume i j h,
    have h1 : int.fract (α * ↑i) = int.fract (α * ↑j), from by simp [h],
    have h2 : (int.fract (α * ↑i) : ℝ) = (int.fract (α * ↑j) : ℝ), from by simp [h1],
    have h3 : (α * ↑i - int.fract (α * ↑i) : ℝ) = (α * ↑j - int.fract (α * ↑j) : ℝ), from by simp [h2, int.fract_eq_of_lt],
    have h4 : (α : ℝ) = ((int.fract (α * ↑i) - int.fract (α * ↑j)) : ℝ) / ((i - j) : ℝ), from by simp [h3],
    have h5 : (α : ℝ) * ((i - j) : ℝ) = (int.fract (α * ↑i) - int.fract (α * ↑j)) : ℝ, from by simp [h4],
    have h6 : (α : ℝ) * ((i - j) : ℝ) = (α * ↑i - int.fract (α * ↑i) : ℝ) - (α * ↑j - int.fract (α * ↑j) : ℝ), from by simp [h5, mul_sub],
    have h7 : (α : ℝ) * ((i - j) : ℝ) = α * (↑i - ↑j), from by simp [h6],
    have h8 : (α : ℝ) * ((i - j) : ℝ) = α * ((i - j) : ℝ), from by simp [h7],
    have h9 : (α : ℝ) * ((i - j) : ℝ) = 0, from by simp [h8],
    have h10 : (α : ℝ) ≠ 0, from by simp [hα_irrat],
    have h11 : (i - j) = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero h10 h9).elim (λ h, absurd h h),
    show false, from by simp [h11, h],
  end,
  have h2 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) : ℝ) ≠ (int.fract (α * ↑j) : ℝ), from by auto [h1],
  have h3 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) : ℝ) ∉ {(int.fract (α * ↑j) : ℝ)}, from by auto [h2],
  have S_inj : function.injective (λ (m : ℤ), int.fract (α * ↑m)) := set.injective_iff_ne_iff_image_ne_empty.2 h3,
  have h4 : (S : set ℝ) = range (λ (m : ℤ), int.fract (α * ↑m)), from by auto [S_inj, S],
  have S_dense : closure S = set.Icc 0 1 := set.closure_range (λ m hm, by simp [hm, int.fract_nonneg, int.fract_lt_one]),
  show closure S = set.Icc 0 1, from by simp [S_dense, S_clos_S, h4],
end

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
  begin 
    assume i j h1,
    assume h2 : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h3 : α = (int.nat_abs α * ↑i + int.fract (α * ↑i)) / ↑i, from by auto [int.fract_add_nat_abs, mul_comm],
    have h4 : α = (int.nat_abs α * ↑j + int.fract (α * ↑j)) / ↑j, from by auto [int.fract_add_nat_abs, mul_comm, h2],
    have h5 : α = (int.nat_abs α * ↑i - int.nat_abs α * ↑j) / (↑i - ↑j), from by auto [h3, h4, int.fract_add_nat_abs, mul_comm, mul_add, mul_neg_eq_neg_mul_symm, add_mul, nat_abs_mul_self, nat_abs_of_nonneg, le_of_lt, int.coe_nat_lt, int.coe_nat_le_coe_nat_iff, nat.cast_lt, nat.cast_le, int.cast_le, int.cast_lt], 
    have h6 : (int.nat_abs α * ↑i - int.nat_abs α * ↑j) / (↑i - ↑j) ∈ ℚ, from by auto [h5, rationals.of_int],
    have h7 : (int.nat_abs α * ↑i - int.nat_abs α * ↑j) = 0, from by auto [int.cast_inj, int.nat_abs_eq_nat_abs],
    have h8 : ↑i = ↑j, from by auto [nat.mul_right_inj, int.coe_nat_eq_coe_nat_iff, h7, int.coe_nat_zero, nat.cast_inj],
    have h9 : i = j, from by auto [h8],
    show false, from by auto [h1, h9],
  end,
  have h2 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by auto [h1],
  have h3 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by auto [h1],
  have h4 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.mem_closure_iff],
  have h5 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.not_mem_closure_iff],
  have h6 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h4], 
  have h7 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h5], 
  have h8 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h1],
  have h9 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h6], 
  have h10 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h7], 
  have h11 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h9], 
  have h12 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h10],
  have h13 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h11], 
  have h14 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h12],
  have h15 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h13], 
  have h16 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h14],
  have h17 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h15], 
  have h18 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h16],
  have h19 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h17], 
  have h20 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h18],
  have h21 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∈ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))), from by auto [h19], 
  have h22 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ∉ (closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j ∈ ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), 
  from by auto [int.fract_eq_iff] using [hα_irrat, classical],

  have h2 : ∀ i ∈ ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, 
  from by auto [int.fract_range],

  have h3 : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, 
  from by auto [mem_image, h2],

  have h4 : ∀ i j ∈ ℤ, i ≠ j → λ (x : ℝ), abs (int.fract (α * ↑i) - int.fract (α * ↑j)) ≠ x, 
  from by auto [abs_of_pos (int.fract_pos), h1],

  have h5 : ∀ i ∈ ℤ, λ (x : ℝ), abs (int.fract (α * ↑i) - int.fract (α * ↑i)) ≠ x, 
  from by auto [abs_of_nonneg (int.fract_nonneg), h1],

  have h6 : ∀ i ∈ ℤ, int.fract (α * ↑i) ≠ 0, 
  from by auto [int.fract_pos, zero_lt_one],

  have h7 : ∀ i ∈ ℤ, int.fract (α * ↑i) ≠ 1, 
  from by auto [int.fract_lt_one, one_lt_two],

  have h8 : ∀ i ∈ ℤ, λ (x : ℝ), abs (int.fract (α * ↑i)) ≠ x, 
  from by auto [abs_of_nonneg (int.fract_nonneg), h6, h7],

  have h9 : ∀ i ∈ ℤ, λ (x : ℝ), abs (int.fract (α * ↑i)) ≠ x, 
  from by auto [abs_of_nonneg (int.fract_nonneg), h6, h7],

  have h10 : ∀ i ∈ ℤ, λ (x : ℝ), abs (int.fract (α * ↑i) - 1) ≠ x, 
  from by auto [abs_of_nonneg (int.fract_nonneg), h6, h7],

  have h11 : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h8],

  have h12 : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x - 1)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h10],

  have h13 : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x - x)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h9],

  have h14 : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x - y)) '' set.Icc 0 1) ∪ ((λ (x : ℝ), abs (x - z)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h4, h5],

  have h15 : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x - y)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h4, h5],

  have h16 : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x - z)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h4, h5],

  have h17 : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), 
  from by auto [mem_image, mem_Icc, h6, h7, h4, h5],

  have h18 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x - y)) '' set.Icc 0 1) ∪ ((λ (x : ℝ), abs (x - z)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h4, h5],

  have h19 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x - y)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h4, h5],

  have h20 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x - z)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h4, h5],

  have h21 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h8],

  have h22 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x - 1)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h10],

  have h23 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ ((λ (x : ℝ), abs (x - x)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h9],

  have h24 : ((λ (x : ℝ), abs (x - y)) '' set.Icc 0 1) ⊆ ((λ (x : ℝ), abs (x - z)) '' set.Icc 0 1) ∪ ((λ (x : ℝ), abs (x - z)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_Icc, h6, h7, h4, h5],

  have h25 : ((λ (x : ℝ), abs (x - y)) '' set.Icc 0 1) ⊆ ((λ (x : ℝ), abs (x - z)) '' set.Icc 0 1), 
  from by auto [mem_image, mem_
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ∈ 𝒫 (set.univ : set ℤ), from by auto [int.fract_between_zero_one],

  have h2 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), 
  from begin
    assume (i j : ℤ) (h2 : i ≠ j),
    have h3 : (α * ↑i) - (↑i * α) < 1 ∧ (α * ↑i) - (↑i * α) ≥ 0, 
    from by auto [int.fract_lt_one, int.fract_nonneg],
    have h4 : (α * ↑j) - (↑j * α) < 1 ∧ (α * ↑j) - (↑j * α) ≥ 0, 
    from by auto [int.fract_lt_one, int.fract_nonneg],
    have h5 : ((α * ↑i) - (↑i * α)) = ((α * ↑j) - (↑j * α)) ↔ (α * ↑i - α * ↑j) = (↑i - ↑j) * α ↔ (α * (↑i - ↑j)) = (↑i - ↑j) * α ↔ α = (↑i - ↑j) / (↑i - ↑j), 
    from by auto [sub_eq_iff_eq_add, mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, mul_sub, sub_mul],
    have h6 : i - j ≠ 0, from by auto [sub_ne_zero],
    have h7 : α = (↑i - ↑j) / (↑i - ↑j), from by auto [h5, h3, h4],
    have h8 : α ∈ (rat.fract (↑i - ↑j) (↑i - ↑j)) :: set.univ, from by auto [rat.mk_eq_div, rat.mk_eq_div, rat.mk_eq_div, rat.mk_eq_div, h7],
    have h9 : α ∈ set.univ, from by auto [h8, set.mem_univ],
    show int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h2, h9, hα_irrat, irrational_iff_not_in_fracts],
  end,

  have h3 : ∀ i j : ℤ, i ≠ j → (λ (m : ℤ), int.fract (α * ↑m)) i ≠ (λ (m : ℤ), int.fract (α * ↑m)) j, 
  from by auto [h2],

  have h4 : ∀ i j : ℤ, i ≠ j → ¬(int.fract (α * ↑i) = int.fract (α * ↑j)), from by auto [h3],
  have h5 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) = int.fract (α * ↑j)) → false, from by auto [h4],
  have h6 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h5] using [classical],
  have h7 : ∀ i j : ℤ, i ≠ j → (λ (m : ℤ), int.fract (α * ↑m)) i ≠ (λ (m : ℤ), int.fract (α * ↑m)) j, from by auto [h6],
  have h8 : ∀ i j : ℤ, i ≠ j → ¬(int.fract (α * ↑i) = int.fract (α * ↑j)), from by auto [h7],
  have h9 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) = int.fract (α * ↑j)) → false, from by auto [h8],
  have h10 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h9] using [classical],
  have h11 : ∀ i j : ℤ, i ≠ j → (λ (m : ℤ), int.fract (α * ↑m)) i ≠ (λ (m : ℤ), int.fract (α * ↑m)) j, from by auto [h10],
  have h12 : ∀ i j : ℤ, i ≠ j → ¬(int.fract (α * ↑i) = int.fract (α * ↑j)), from by auto [h11],
  have h13 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) = int.fract (α * ↑j)) → false, from by auto [h12],
  have h14 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h13] using [classical],
  have h15 : ∀ i j : ℤ, i ≠ j → (λ (m : ℤ), int.fract (α * ↑m)) i ≠ (λ (m : ℤ), int.fract (α * ↑m)) j, from by auto [h14],
  have h16 : ∀ i j : ℤ, i ≠ j → ¬(int.fract (α * ↑i) = int.fract (α * ↑j)), from by auto [h15],
  have h17 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) = int.fract (α * ↑j)) → false, from by auto [h16],
  have h18 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h17] using [classical],
  have h19 : ∀ i j : ℤ, i ≠ j → (λ (m : ℤ), int.fract (α * ↑m)) i ≠ (λ (m : ℤ), int.fract (α * ↑m)) j, from by auto [h18],
  have h20 : ∀ i j : ℤ, i ≠ j → ¬(int.fract (α * ↑i) = int.fract (α * ↑j)), from by auto [h19],
  have h21 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) = int.fract (α * ↑j)) → false, from by auto [h20],
  have h22 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h21] using [classical],
  have h23 : ∀ i j : ℤ, i ≠ j → (λ (m : ℤ), int.fract (α * ↑m)) i ≠ (λ (m : ℤ), int.fract (α * ↑m)) j, from by auto [h22],
  have h24 : ∀ i j : ℤ, i ≠ j → ¬(int.fract (α * ↑i) = int.fract (α * ↑j)), from by auto [h23],
  have h25 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) = int.fract (α * ↑j)) → false, from by auto [h24],
  have h26 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h25] using [classical],
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, (i ≠ j) → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
  begin
    assume i j,
    assume h2 : (i ≠ j),
    assume h3 : (int.fract (α * ↑i) = int.fract (α * ↑j)),
    have h4 : ↑i * α - ↑(int.floor (↑i * α)) = int.fract (α * ↑i), from by auto [int.fract_def],
    have h5 : ↑j * α - ↑(int.floor (↑j * α)) = int.fract (α * ↑j), from by auto [int.fract_def],
    have h6 : ↑i * α - ↑(int.floor (↑i * α)) = ↑j * α - ↑(int.floor (↑j * α)), from by auto [h3, h4, h5],
    have h7 : ↑i * α - ↑(int.floor (↑i * α)) = (↑j - ↑i) * α, from by auto [sub_eq_iff_eq_add, nat.cast_sub, ← int.coe_nat_eq_coe_nat_iff, int.coe_nat_sub, int.coe_nat_add],
    have h8 : (↑j - ↑i) * α = ↑(int.floor (↑j * α)) - ↑(int.floor (↑i * α)), from by auto [h6, h7],
    have h9 : (↑j - ↑i) * α = ↑(int.floor (↑j * α)) - ↑(int.floor (↑i * α)), from by auto [h7, h6],
    have h10 : int.floor (↑j * α) - int.floor (↑i * α) = 0, from by auto [int.coe_nat_sub, int.coe_nat_eq_coe_nat_iff],
    have h11 : ↑(int.floor (↑j * α)) - ↑(int.floor (↑i * α)) = 0, from by auto [nat.cast_sub, ← int.coe_nat_eq_coe_nat_iff, int.coe_nat_sub, int.coe_nat_eq_coe_nat_iff, h10],
    have h12 : (↑j - ↑i) * α = 0, from by auto [h11, h9],
    have h13 : (↑j - ↑i) = 0, from by auto [int.coe_nat_sub, int.coe_nat_eq_coe_nat_iff, int.coe_nat_zero, int.coe_nat_mul, int.coe_nat_eq_coe_nat_iff, h12, int.coe_nat_zero],
    have h14 : (j - i) = 0, from by auto [nat.sub_eq_zero_iff_eq, h13],
    have h15 : (j = i), from by auto [nat.sub_eq_zero_iff_eq, h14],
    have h16 : (j = i), from by auto [h15, h2],
    show false, from by auto [h16],
  end,
  have h2 : ∀ i j : ℤ, (int.fract (α * ↑i) = int.fract (α * ↑j)) → (i = j), from
  begin
    assume i j,
    assume h3 : (int.fract (α * ↑i) = int.fract (α * ↑j)),
    have h4 : (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)), from by auto [h1],
    have h5 : ¬(i ≠ j), from by auto [h4, h3],
    have h6 : i = j, from by auto [h5],
    show (i = j), from by auto [h6],
  end,
  have h3 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)), from by auto [h1],
  have h4 : ∀ i j : ℤ, (int.fract (α * ↑i) = int.fract (α * ↑j)) → (i = j), from by auto [h2],
  have h5 : ∀ x : ℤ, (int.fract (α * ↑x) ∈ set.Icc 0 1), from by auto [int.fract_range],
  have h6 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by auto [h5],
  have h7 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ (closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.subset.refl],
  have h8 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ (closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.subset.trans, h6, h7],
  have h9 : (closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ (closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.subset.refl],
  have h10 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ (closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) → (closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ (closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) → closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by auto [set.eq_of_subset_of_subset],
  have h11 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by auto [h10, h8, h9],
  have h12 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) → closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by auto [set.eq_of_subset_of_subset],
  have h13 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by auto [h12, h11],
  have h14 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = closure (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) → closure ((λ (m : ℤ), int.
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
  from by auto [abs_sub_lt_iff] using [linarith],
  
  assume (h7 : ε > 0),

  cases h2 ε h7 with N1 h8,
  cases h3 ε h7 with N2 h9,
  let N := max N1 N2,
  use N,

  have h10 : ∀ n > N, n > N1 ∧ n > N2 := by auto [lt_of_le_of_lt, le_max_left, le_max_right],
  
  have h11 : ∀ n > N, (((l - ε) < (y n)) ∧ ((y n) ≤ (x n))) ∧ (((x n) ≤ (z n)) ∧ ((z n) < l+ε)), 
  from by auto [h8, h10, h5, h9],

  have h15 : ∀ n > N, ((l - ε) < (x n)) ∧ ((x n) < (l+ε)), 
  from by auto [h11] using [linarith],

  show  ∀ (n : ℕ), n > N → |x n - l| < ε, 
  from by auto [h5, h15], 

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
