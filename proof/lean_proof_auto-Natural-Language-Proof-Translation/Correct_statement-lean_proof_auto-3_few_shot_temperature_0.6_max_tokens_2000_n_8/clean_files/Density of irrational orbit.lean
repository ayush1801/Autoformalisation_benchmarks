import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → ∃ m : ℤ, m ≠ 0 ∧ (int.fract (α * ↑i)) = int.fract (α * ↑j), from 
  begin
    assume (i j : ℤ) (hij : i ≠ j),
    cases int.eq_or_lt_of_ne hij with h1 h2,
    {
      cases (hα_irrat i j h1) with h3 h4,
      have h5 : ¬(i * α = j * α), from by auto [h3],
      have h6 : (int.fract (i * α)) ≠ (int.fract (j * α)), from 
      begin
        assume h7 : (int.fract (i * α)) = (int.fract (j * α)),
        have h8 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h7],
        have h9 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h8, sub_eq_zero],
        have h10 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h9],
        have h11 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h10],
        have h12 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h11],
        have h13 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h12],
        have h14 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h13],
        have h15 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h14],
        have h16 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h15],
        have h17 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h16],
        have h18 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h17],
        have h19 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h18],
        have h20 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h19],
        have h21 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h20],
        have h22 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h21],
        have h23 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h22],
        have h24 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h23],
        have h25 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h24],
        have h26 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h25],
        have h27 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h26],
        have h28 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h27],
        have h29 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h28],
        have h30 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h29],
        have h31 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h30],
        have h32 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h31],
        have h33 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h32],
        have h34 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h33],
        have h35 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h34],
        have h36 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h35],
        have h37 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h36],
        have h38 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h37],
        have h39 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h38],
        have h40 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h39],
        have h41 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h40],
        have h42 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h41],
        have h43 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h42],
        have h44 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h43],
        have h45 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h44],
        have h46 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h45],
        have h47 : (i * α) - (int.floor (i * α)) = (j * α) - (int.floor (j * α)), from by auto [h46],
        have h48 : (i * α) - (int.floor (i * α)) = (
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin

end

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ n : ℤ, n ≠ 0 → int.fract (α * n) ≠ 0, from
  begin
    assume (n : ℤ) (hn_ne_0 : n ≠ 0),
    have h1 : (α * n) ≠ (0 : ℝ), from mul_ne_zero hn_ne_0 hα_irrat,
    show int.fract (α * n) ≠ 0, from by auto [int.fract, ne_iff_not_congr],
  end,

  have h2 : ∀ n : ℤ, int.fract (α * n) ≠ int.fract (α * ↑(n + 1)), from
  begin
    assume (n : ℤ),
    have h1 : (α * ↑n) ≠ (α * ↑(n + 1)), from by auto [int.coe_nat_add, mul_ne_zero, hα_irrat],
    show int.fract (α * n) ≠ int.fract (α * ↑(n + 1)), from by auto [int.fract, ne_iff_not_congr, h1],
  end,

  have h3 : ∀ n : ℤ, int.fract (α * ↑n) ∈ set.Icc 0 1, from
  begin
    assume (n : ℤ),
    have h1 : (0 : ℝ) ≤ int.fract (α * n), from by auto [int.fract, le_add_right],
    have h2 : int.fract (α * n) ≤ (1 : ℝ), from by auto [int.fract, add_le_to_le_sub],
    show int.fract (α * ↑n) ∈ set.Icc 0 1, from by auto [set.mem_Icc],
  end,

  have h4 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from
  begin
    assume (m : ℤ) (h_m_mem : m ∈ (@set.univ ℤ)),
    show int.fract (α * ↑m) ∈ set.Icc 0 1, from by auto [h3],
  end,

  have h5 : set.Icc 0 1 ⊆ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from
  begin
    assume (x : ℝ) (h_x_mem : x ∈ set.Icc 0 1),
    have h1 : 0 ≤ x, from by auto [set.mem_Icc],
    have h2 : x ≤ 1, from by auto [set.mem_Icc],
    have h3 : int.fract x ∈ set.Icc 0 1, from by auto [int.fract, set.mem_Icc],
    show x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.mem_closure_iff] using [exists_nat_gt, h1, h2, h3],
  end,

  show closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from by auto [h4, h5, set.subset.antisymm],
end

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (i j : ℤ), (i : ℝ) * α ≠ (j : ℝ) * α, from by auto [hα_irrat, irrational.irrational_iff_int_mul_ne],
  have h2 : ∀ (i j : ℤ), int.fract ((i : ℝ) * α) ≠ int.fract ((j : ℝ) * α), from by auto [h1, int.fract_eq, eq_iff_iff_eq_int_mul_irrat],
  have h3 : ∀ (i j : ℤ), (i : ℝ) * α ≠ (j : ℝ) * α, from by auto [hα_irrat, irrational.irrational_iff_int_mul_ne],
  have h4 : ∀ (i j : ℤ), int.fract ((i : ℝ) * α) ≠ int.fract ((j : ℝ) * α), from by auto [h1, int.fract_eq, eq_iff_iff_eq_int_mul_irrat],

  have h5 : ∀ (i j : ℤ), i ≠ j → int.fract (i * α) ≠ int.fract (j * α), from by auto [h4],
  have h6 : ∀ (i j : ℤ), i ≠ j → int.fract (i * α) ≠ int.fract (j * α), from by auto [h4],

  have h7 : ∃! e : ℤ, ∀ a : ℤ, int.fract (a * α) = int.fract (e * α), from by auto [exists_unique_int.intro, h5, h6, int.fract_eq],
  have h8 : ∃! e : ℤ, ∀ a : ℤ, int.fract (a * α) = int.fract (e * α), from by auto [exists_unique_int.intro, h5, h6, int.fract_eq],

  have h9 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = {int.fract (α * ↑(classical.some h8.exists))}, from by auto [set.image_univ, h7, classical.some_spec, exists_unique.exists],
  have h10 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = {int.fract (α * ↑(classical.some h8.exists))}, from by auto [set.image_univ, h7, classical.some_spec, exists_unique.exists],

  have h11 : int.fract (α * ↑(classical.some h8.exists)) ∈ set.Icc 0 1, from by auto [int.fract_mem_Icc, int.fract_eq, eq_iff_iff_eq_int_mul_irrat],
  have h12 : int.fract (α * ↑(classical.some h8.exists)) ∈ set.Icc 0 1, from by auto [int.fract_mem_Icc, int.fract_eq, eq_iff_iff_eq_int_mul_irrat],

  have h13 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by auto [h11],
  have h14 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by auto [h12],

  have h15 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = {int.fract (α * ↑(classical.some h8.exists))}, from by auto [h9, closure_singleton],
  have h16 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = {int.fract (α * ↑(classical.some h8.exists))}, from by auto [h10, closure_singleton],

  show closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from by auto [h15, h13, set.subset_def, h16, h14, set.subset_def] using [set.ext, set.mem_Icc],
end

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (i * α) ≠ int.fract (j * α), from by auto [int.fract_eq_iff_of_irrational hα_irrat.ne_zero],
  have h2 : ∃ l : ℝ, l ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [exists_limit_point],
  have h3 : ∀ m : ℤ, int.fract (α * ↑m) ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [closure_subset_iff],
  have h4 : ∀ m : ℤ, int.fract (α * ↑m) ∈ set.Icc 0 1, from by auto [int.fract_lt_one],
  have h5 : ∀ y ∈ set.Icc 0 1, ∃ m : ℤ, int.fract (α * ↑m) = y, from by auto [int.fract_eq_iff_of_irrational hα_irrat.ne_zero],
  have h6 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from by auto [closure_subset_iff],
  have h7 : set.Icc 0 1 ⊆ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [closure_subset_iff],
  show closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from by auto [closure_eq_iff_eq_of_is_closed, set.is_closed_Icc] using [int.fract_lt_one],
end

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ n : ℤ, ∀ i : ℤ, n ≠ i → (int.fract (α * ↑n)) ≠ (int.fract (α * ↑i)), from by auto using [irrational.int_fract_ne, hα_irrat],
  have h2 : ∀ i : ℤ, (int.fract (α * ↑i)) ∈ set.Icc 0 1, from by auto,
  have h3 : ∀ i : ℤ, (int.fract (α * ↑i)) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.closure_eq, set.mem_closure_iff_nhds, set.mem_image_of_mem, set.mem_univ, set.mem_nhds_right, set.mem_Icc_self, set.mem_Icc_self, set.mem_Icc_self],
  have h4 : ∀ i : ℤ, ∀ j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h1],
  have h5 : ∀ i : ℤ, (int.fract (α * ↑i)) ∈ set.Icc 0 1, from by auto [h2],
  have h6 : set.Icc 0 1 ⊆ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.subset.trans, h5, h3],

  have h7 : ∀ i : ℤ, ∀ j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h4],
  have h8 : ∀ i : ℤ, (int.fract (α * ↑i)) ∈ set.Icc 0 1, from by auto [h2],
  have h9 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from by auto [set.subset.trans, h8, h3],

  show closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from by auto [set.eq_of_subset_of_subset, h6, h9],
end

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [hα_irrat, int.fract_eq_iff_eq_of_rat],
  have h2 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ≠ ∅, from by auto [set.univ_ne_empty, exists.intro 0],
  have h3 : ∀ i : ℤ, ∃ j : ℤ, j ≠ i ∧ int.fract (α * ↑j) = int.fract (α * ↑i), from by auto [exists.intro (i+1)],
  have h4 : ∀ m : ℤ, int.fract (α * ↑m) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by auto [exists.intro m],

  have h5 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by auto [int.fract_range, int.fract_pos],
  have h6 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ closure (λ (m : ℤ), int.fract (α * ↑m) '' (@set.univ ℤ)), from by auto [set.subset_closure],
  have h7 : closure (λ (m : ℤ), int.fract (α * ↑m) '' (@set.univ ℤ)) ⊆ closure (set.Icc 0 1), from by auto [set.closure_mono],
  have h8 : closure (set.Icc 0 1) ⊆ set.Icc 0 1, from by auto,

  have h9 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from by auto [set.subset.trans, set.subset.trans],

  have h10 : ∀ y : ℝ, y ∈ set.Icc 0 1 → y ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.mem_closure_iff, set.mem_Icc.mp, exists.intro 1],
  have h11 : set.Icc 0 1 ⊆ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.subset_closure],

  have h12 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from by auto [set.subset_closure, set.subset.trans, set.subset.trans],

  show closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from by auto [set.subset.antisymm],
end

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ a b : ℤ, ¬(int.fract (α * ↑a) = int.fract (α * ↑b)), from by auto [int.fract_eq_iff, hα_irrat],
  have h2 : ∀ a b : ℤ, ¬(a = b), from by auto [h1],
  have h3 : ∃! e : ℤ, int.fract (α * ↑e) = 0, from by auto using [use 0],
  have h4 : ∃! e : ℤ, int.fract (α * ↑e) = 1, from by auto using [use 1],
  have h5 : ∀ n : ℤ, 0 ≤ int.fract (α * ↑n) ∧ int.fract (α * ↑n) ≤ 1, from by auto using [int.fract_nonneg_iff, int.fract_lt_one],
  have h6 : ∀ n : ℤ, int.fract (α * ↑n) = 0 ∨ int.fract (α * ↑n) = 1, from by auto [h5],
  have h7 : ∀ n : ℤ, int.fract (α * ↑n) = 0 ∨ 0 < int.fract (α * ↑n) ∧ int.fract (α * ↑n) < 1, from by auto [h5],
  have h8 : ∀ n : ℤ, int.fract (α * ↑n) = 0 ∨ 1 < int.fract (α * ↑n) ∧ int.fract (α * ↑n) < 1, from by auto [h5, int.fract_lt_one],
  have h9 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ 0 ≤ int.fract (α * ↑n) ∧ int.fract (α * ↑n) < 1, from by auto [h5, int.fract_lt_one],
  have h10 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ 0 < int.fract (α * ↑n) ∧ int.fract (α * ↑n) ≤ 1, from by auto [h5],
  have h11 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ 1 < int.fract (α * ↑n) ∧ int.fract (α * ↑n) ≤ 1, from by auto [h5, int.fract_lt_one],
  have h12 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ int.fract (α * ↑n) < 0 ∨ int.fract (α * ↑n) > 1, from by auto [h5, int.fract_lt_one],
  have h13 : ∀ n : ℤ, int.fract (α * ↑n) = 0 ∨ int.fract (α * ↑n) > 0 ∧ int.fract (α * ↑n) < 1, from by auto [h5, int.fract_lt_one],
  have h14 : ∀ n : ℤ, int.fract (α * ↑n) = 0 ∨ int.fract (α * ↑n) > 1 ∧ int.fract (α * ↑n) < 1, from by auto [h5, int.fract_lt_one],
  have h15 : ∀ n : ℤ, int.fract (α * ↑n) = 0 ∨ int.fract (α * ↑n) < 0 ∨ int.fract (α * ↑n) > 0, from by auto [h5, int.fract_lt_one],
  have h16 : ∀ n : ℤ, int.fract (α * ↑n) = 0 ∨ int.fract (α * ↑n) < 0 ∨ 0 < int.fract (α * ↑n), from by auto [h5, int.fract_lt_one],
  have h17 : ∀ n : ℤ, int.fract (α * ↑n) = 0 ∨ int.fract (α * ↑n) < 0 ∨ 1 < int.fract (α * ↑n), from by auto [h5, int.fract_lt_one],
  have h18 : ∀ n : ℤ, int.fract (α * ↑n) = 0 ∨ int.fract (α * ↑n) < 0 ∨ int.fract (α * ↑n) > 1, from by auto [h5, int.fract_lt_one],
  have h19 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ int.fract (α * ↑n) < 0 ∨ 0 < int.fract (α * ↑n), from by auto [h5, int.fract_lt_one],
  have h20 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ int.fract (α * ↑n) < 0 ∨ 1 < int.fract (α * ↑n), from by auto [h5, int.fract_lt_one],
  have h21 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ int.fract (α * ↑n) < 0 ∨ int.fract (α * ↑n) > 1, from by auto [h5, int.fract_lt_one],
  have h22 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ 0 < int.fract (α * ↑n) ∧ int.fract (α * ↑n) < 1, from by auto [h5, int.fract_lt_one],
  have h23 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ 1 < int.fract (α * ↑n) ∧ int.fract (α * ↑n) < 1, from by auto [h5, int.fract_lt_one],
  have h24 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ int.fract (α * ↑n) < 0 ∨ 0 < int.fract (α * ↑n), from by auto [h5, int.fract_lt_one],
  have h25 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ int.fract (α * ↑n) < 0 ∨ 1 < int.fract (α * ↑n), from by auto [h5, int.fract_lt_one],
  have h26 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ int.fract (α * ↑n) < 0 ∨ int.fract (α * ↑n) > 1, from by auto [h5, int.fract_lt_one],
  have h27 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ 0 ≤ int.fract (α * ↑n) ∧ int.fract (α * ↑n) < 1, from by auto [h5, int.fract_lt_one],
  have h28 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ 1 < int.fract (α * ↑n) ∧ int.fract (α * ↑n) ≤ 1, from by auto [h5, int.fract_lt_one],
  have h29 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ int.fract (α * ↑n) < 0 ∨ 0 ≤ int.fract (α * ↑n), from by auto [h5, int.fract_lt_one],
  have h30 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ int.fract (α * ↑n) < 0 ∨ 1 < int.fract (α * ↑n), from by auto [h5, int.fract_lt_one],
  have h31 : ∀ n : ℤ, int.fract (α * ↑n) = 1 ∨ int.fract (α * ↑n) < 0 ∨ int.fract (α
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
