import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)), from by auto [int.fract_eq_iff],
  have h2 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff, int.fract_add_int, int.fract_mul, int.fract_eq_zero_iff, hα_irrat, int.fract_add_int],
  have h3 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff, int.fract_add_int, int.fract_mul, int.fract_eq_zero_iff, hα_irrat, int.fract_add_int],
  have h4 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [h1, h2, h3],
  have h5 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [h1, h2, h3],
  have h6 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [h1, h2, h3],
  have h7 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [h1, h2, h3],
  have h8 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [h1, h2, h3],
  have h9 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [h1, h2, h3],
  have h10 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [h1, h2, h3],
  have h11 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [h1, h2, h3],
  have h12 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [h1, h2, h3],
  have h13 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0) → (int.fract (
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let S := (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ),
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
    begin
      assume (i j : ℤ) (hij : i ≠ j),
      have h1 : i * α - (i * α).floor ≠ j * α - (j * α).floor, from
        begin
          assume h2 : i * α - (i * α).floor = j * α - (j * α).floor,
          have h3 : α = ((i * α).floor - (j * α).floor) / (i - j), from by auto [mul_div_cancel, mul_eq_iff_eq_one_mul, one_mul],
          have h4 : α ∈ ℚ, from by auto [h3],
          have h5 : irrational α, from hα_irrat,
          have h6 : false, from by auto [h4, h5],
          show false, from h6,
        end,
      have h2 : int.fract (α * ↑i) = i * α - (i * α).floor, from by auto [int.fract_def, int.fract_lt_one],
      have h3 : int.fract (α * ↑j) = j * α - (j * α).floor, from by auto [int.fract_def, int.fract_lt_one],
      have h4 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h1, h2, h3],
      show int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h4,
    end,
  have h2 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h1,
  have h3 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from h2,
  have h4 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h3,
  have h5 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h4,
  have h6 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h5,
  have h7 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h6,
  have h8 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h7,
  have h9 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h8,
  have h10 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h9,
  have h11 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h10,
  have h12 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h11,
  have h13 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h12,
  have h14 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h13,
  have h15 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h14,
  have h16 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h15,
  have h17 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h16,
  have h18 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h17,
  have h19 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h18,
  have h20 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h19,
  have h21 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h20,
  have h22 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h21,
  have h23 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h22,
  have h24 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h23,
  have h25 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h24,
  have h26 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h25,
  have h27 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h26,
  have h28 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h27,
  have h29 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h28,
  have h30 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h29,
  have h31 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h30,
  have h32 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h31,
  have h33 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h32,
  have h34 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h33,
  have h35 : ∀ i j : ℤ, i ≠ j → int.f
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from
  begin
    assume i j h1,
    assume h2 : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h3 : (α * ↑i) - (int.floor (α * ↑i)) = int.fract (α * ↑i), from by auto [int.fract_def],
    have h4 : (α * ↑j) - (int.floor (α * ↑j)) = int.fract (α * ↑j), from by auto [int.fract_def],
    have h5 : (α * ↑i) - (int.floor (α * ↑i)) = (α * ↑j) - (int.floor (α * ↑j)), from by auto [h2, h3, h4],
    have h6 : (α * ↑i) - (int.floor (α * ↑i)) = (α * ↑j) - (int.floor (α * ↑j)), from by auto [h2, h3, h4],
    have h7 : α = (int.floor (α * ↑i) - int.floor (α * ↑j)) / (i - j), from by auto [int.sub_eq_iff_eq_add, h5, mul_sub, mul_add, mul_comm, mul_assoc, mul_left_comm, mul_sub, add_sub_cancel, int.sub_eq_iff_eq_add, h6, mul_sub, mul_add, mul_comm, mul_assoc, mul_left_comm, mul_sub, add_sub_cancel] using [field],
    have h8 : α ∈ ℚ, from by auto [h7],
    have h9 : irrational α, from by auto [hα_irrat],
    show false, from by auto [h8, h9],
  end,
  have h2 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h1],
  have h3 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [int.fract_range],
  have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h2],
  have h5 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h3],
  have h6 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h4],
  have h7 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h5],
  have h8 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h6],
  have h9 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h7],
  have h10 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h8],
  have h11 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h9],
  have h12 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h10],
  have h13 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h11],
  have h14 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h12],
  have h15 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h13],
  have h16 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h14],
  have h17 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h15],
  have h18 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h16],
  have h19 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h17],
  have h20 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h18],
  have h21 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h19],
  have h22 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h20],
  have h23 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h21],
  have h24 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h22],
  have h25 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h23],
  have h26 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h24],
  have h27 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h25],
  have h28 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h26],
  have h29 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h27],
  have h30 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h28],
  have h31 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h29],
  have h32 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h30],
  have h33 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [h31],
  have h34 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h32],
  have h35 : ∀
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := 
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h2 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h3 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h4 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h5 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h6 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h7 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h8 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h9 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h10 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h11 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h12 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h13 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h14 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h15 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h16 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h17 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h18 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h19 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h20 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h21 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h22 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h23 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h24 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h25 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h26 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h27 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h28 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h29 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h30 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h31 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h32 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_eq_iff, hα_irrat],
  have h33 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
  begin
    assume i j hi_ne_j,
    assume h2 : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h3 : int.fract (α * ↑i) = α * ↑i - int.nat_abs (α * ↑i), from by auto [int.fract],
    have h4 : int.fract (α * ↑j) = α * ↑j - int.nat_abs (α * ↑j), from by auto [int.fract],
    have h5 : α * ↑i - int.nat_abs (α * ↑i) = α * ↑j - int.nat_abs (α * ↑j), from by auto [h2],
    have h6 : α = (int.nat_abs (α * ↑i) - int.nat_abs (α * ↑j)) / (i - j), from by auto [int.nat_abs, int.coe_nat_sub, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)), from by auto [hα_irrat, int.fract_eq_iff_eq_int_mul_sub_int_mul],
  have h2 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h3 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h5 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h6 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h7 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h8 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h9 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h10 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h11 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h12 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h13 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h14 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h15 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h16 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h17 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h18 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h19 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h20 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h21 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h22 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h23 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h24 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from by auto [int.fract_eq_iff_eq_int_mul_sub_int_mul, sub_eq_zero_iff_eq],
  have h25 : ∀ i j :
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
