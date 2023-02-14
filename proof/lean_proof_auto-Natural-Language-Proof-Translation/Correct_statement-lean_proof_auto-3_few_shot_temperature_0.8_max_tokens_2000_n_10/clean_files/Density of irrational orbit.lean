import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  /- step 0 -/
  obtain ⟨a, b, a_le_b, hab_irrat, hb_nonzero⟩ : ∃ a b : ℝ, a ≤ b ∧ ∀ c ∈ set.Icc a b, irrational c ∧ b ≠ 0, from by auto using [set.Icc_subset_Iio, set.Ioo_subset_Ico, set.Ioc_subset_Icc],
  obtain ⟨c, d, c_lt_d, Icc_subset_Ioo, ho⟩ : ∃ c d : ℝ, c < d ∧ set.Icc c d ⊆ set.Ioo a b ∧ set.Ioo a b ⊆ set.Ico c d, from by auto using [set.Icc_subset_Iio, set.Iio_subset_Iic, set.Iic_subset_Icc],

  /- step 1 -/
  obtain hα : ∃! m : ℤ, α = ↑m, from irrational_iff_int_equiv.elim_left hα_irrat,
  obtain ⟨α_int_equiv, H⟩ : ∃ α_int_equiv : α = int.fract α, by auto using exists_eq_mul_right,
  rw H,
  intros y hy,
  /- step 2 -/
  obtain ⟨n, hn⟩ : ∃ n : ℤ, int.fract α * ↑n = y, from by auto using exists_eq_mul_left,
  have hn2 : y = int.fract (↑n * α), from by auto [hn, int.mul_fract],
  have hn3 : y = int.fract (↑n * α), from by auto [hn2],
  have hn4 : int.fract (↑n * α) ∈ set.Icc 0 1, from by auto,
  have hn5 : ↑n * α ∈ set.Icc 0 1, using hn4, from by auto using [set.mem_Icc],
  have hn6 : ↑n * α = ↑n * a, from by auto [int.mul_left_cancel, set.mem_Icc, set.mem_Ioo],
  have hn7 : ↑n * a ∈ set.Ioi 0, from by auto using [set.Ioi_pos, int.lt_of_mul_pos_left, set.mem_Ioo, set.mem_Ico],
  have hn8 : ↑n * a ≠ 0, from by auto [ne.symm],
  have hn9 : n ≠ 0, from by auto [int.coe_nat_ne_zero],

  have hn10 : n * a * ↑(int.nat_abs n) = n * a, from by auto [int.nat_abs_mul_self, ne.symm],
  have hn11 : n * a * ↑(int.nat_abs n) ∈ set.Ioi 0, from by auto [hn7, int.nat_abs_pos, mul_nonneg],
  have hn12 : n * a * ↑(int.nat_abs n) ≠ 0, from by auto using [hn8],
  have hn13 : n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) = n * a * ↑(int.nat_abs n), from by auto [mul_one],
  have hn14 : n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) ∈ set.Ioi 0, from by auto [hn11, mul_nonneg, int.coe_nat_nonneg],
  have hn15 : n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) ≠ 0, from by auto using [hn12, int.coe_nat_ne_zero],
  have hn16 : by exact_mod_cast (n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n)), from by auto [hn13],
  have hn17 : by exact_mod_cast (n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n)) ∈ set.Ioi 0, from by auto [hn14, (by exact_mod_cast)],
  have hn18 : by exact_mod_cast (n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n)) ≠ 0, from by auto [hn15, (by exact_mod_cast)],

  have hn19 : ↑n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) = ↑(n * a * int.nat_abs n * int.nat_abs n), from by auto,
  have hn20 : by exact_mod_cast (↑n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n)) = by exact_mod_cast (↑(n * a * int.nat_abs n * int.nat_abs n)), from by auto [hn19],
  have hn21 : ↑n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) ≠ 0, from by auto [hn18, hn20],
  have hn22 : ↑(n * a * int.nat_abs n * int.nat_abs n) ≠ 0, from by auto using [hn21, (by exact_mod_cast)],
  have hn23 : (↑(n * a * int.nat_abs n * int.nat_abs n)) ≠ 0, from by auto [hn22],

  have hn24 : n * a * int.nat_abs n * int.nat_abs n = n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n), from by auto,
  have hn25 : n * a * int.nat_abs n * int.nat_abs n ≠ 0, from by auto [hn24, hn23],
  have hn26 : n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) ≠ 0, from by auto [hn25],
  have hn27 : ↑(n * a * int.nat_abs n * int.nat_abs n) = n * a * int.nat_abs n * int.nat_abs n, from by auto using ↑_eq_coe,
  have hn28 : by exact_mod_cast (↑(n * a * int.nat_abs n * int.nat_abs n)) = by exact_mod_cast (n * a * int.nat_abs n * int.nat_abs n), from by auto [hn27],
  have hn29 : n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) ≠ 0, from by auto [hn26, hn28],
  have hn30 : n * a * int.nat_abs n * int.nat_abs n ≠ 0, from by auto [hn29, (by exact_mod_cast)],
  have hn31 : n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) ≠ 0, from by auto [hn30],
  have hn32 : ↑(n * a * int.nat_abs n * int.nat_abs n) = n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n), from by auto using ↑_eq_coe,
  have hn33 : n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) ≠ 0, from by auto [hn31, hn32],
  have hn34 : n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) ≠ 0, from by auto [hn33, hn32],
  have hn35 : n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n) = n * a * ↑(int.nat_abs n) * ↑(int.nat_abs n), from by auto [mul_one],
  have hn36 : n * a * ↑(int.nat_abs
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin 
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
    begin
      assume i j hi_not_eq_j,
      have h1 : (α * ↑i - int.floor (α * ↑i)) = int.fract (α * ↑i), from by auto [int.fract_add_floor],
      have h2 : (α * ↑j - int.floor (α * ↑j)) = int.fract (α * ↑j), from by auto [int.fract_add_floor],
      have h3: (α * ↑i - int.floor (α * ↑i)) = (α * ↑j - int.floor (α * ↑j)), from by auto [h1, h2],
      have h4 : α = ((int.floor (α * ↑i) - int.floor (α * ↑j))) / (i - j), from by auto [div_eq_iff_mul_eq, h3],
      have h5 : ¬ rational α, from by auto [hα_irrat],
      show int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h4, h5],
    end,
  have h2: ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) * ↑i) ≠ (int.fract (α * ↑j) * ↑j), from 
    begin
      assume i j hi_not_eq_j,
      have h1 : (α * ↑i - int.floor (α * ↑i)) * ↑i = (int.fract (α * ↑i) * ↑i), from by auto [int.fract_add_floor],
      have h2 : (α * ↑j - int.floor (α * ↑j)) * ↑j = (int.fract (α * ↑j) * ↑j), from by auto [int.fract_add_floor],
      have h3: (α * ↑i - int.floor (α * ↑i)) = (α * ↑j - int.floor (α * ↑j)), from by auto [h1, h2],
      have h4 : α = ((int.floor (α * ↑i) - int.floor (α * ↑j))) / (i - j), from by auto [div_eq_iff_mul_eq, h3],
      have h5 : ¬ rational α, from by auto [hα_irrat],
      show int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [h4, h5],
    end,
  have h3 : (λ m : ℤ, int.fract (α * ↑m)) '' (set.univ) = ((λ j : ℤ, (int.fract (α * ↑(j + 1)) * ↑(j + 1)) - (int.fract (α * ↑j) * ↑j)) '' (set.univ)), from by auto using [λ m : ℤ, int.fract_mul, mul_one],
  have h4: ∀ j : ℤ, ((int.fract (α * ↑(j + 1))) * (j + 1) - (int.fract (α * ↑j)) * j) < 1, from
    begin
      assume j,
      calc ((int.fract (α * ↑(j + 1))) * (j + 1) - (int.fract (α * ↑j)) * j) 
      = ((int.fract (α * ↑(j + 1))) * (j + 1) - (int.fract (α * ↑j)) * j) + 0 : by auto [add_zero]
      ... = ((int.fract (α * ↑(j + 1))) * (j + 1) - (int.fract (α * ↑j)) * j) + ((j + 1) * (int.fract (α * ↑(j + 1))) - (j + 1) * (int.fract (α * ↑(j + 1)))) : by auto [add_neg_cancel_right]
      ... = ((int.fract (α * ↑(j + 1))) * (j + 1) - (int.fract (α * ↑j)) * j) + ((j + 1) * (int.fract (α * ↑(j + 1))) - (j + 1) * (int.fract (α * ↑j)) + (int.fract (α * ↑j) * j - int.fract (α * ↑j) * j)) : by auto [add_comm, mul_comm, add_sub_cancel j (int.fract (α * ↑j)), sub_self]
      ... = ((int.fract (α * ↑(j + 1))) - (int.fract (α * ↑j))) + (j * (int.fract (α * ↑(j + 1)) - int.fract (α * ↑j))) + (int.fract (α * ↑j) * j - int.fract (α * ↑j) * j) : by auto [add_mul, add_comm, mul_one, mul_comm, add_sub_cancel]
      ... = ((int.fract (α * ↑(j + 1))) - (int.fract (α * ↑j))) + (j * (int.fract (α * ↑(j + 1)) - int.fract (α * ↑j))) + 0 : by auto [add_zero, sub_self]
      ... = ((int.fract (α * ↑(j + 1))) - (int.fract (α * ↑j))) + (j * (int.fract (α * ↑(j + 1)) - int.fract (α * ↑j))) : by auto [add_zero]
      ... = (int.fract (α * ↑(j + 1))) - (int.fract (α * ↑j)) + (j * (int.fract (α * ↑(j + 1)) - int.fract (α * ↑j))) : by auto [add_comm]
      ... = (int.fract (α * ↑(j + 1))) + (j * (int.fract (α * ↑(j + 1)) - int.fract (α * ↑j))) - (int.fract (α * ↑j)) : by auto [add_sub_assoc]
      ... = (j + 1) * (int.fract (α * ↑(j + 1))) - int.fract (α * ↑j) : by auto [mul_comm, add_mul, add_comm, mul_one, add_comm]
      ... = (j + 1) * (int.fract (α * ↑(j + 1))) : by auto [neg_neg]
      ... < (j + 1) * 1 : by auto [mul_lt_mul_of_pos_left, int.fract_lt_one],
    end,
  have h5 : (λ j : ℤ, (int.fract (α * ↑(j + 1)) * ↑(j + 1)) - (int.fract (α * ↑j) * ↑j)) '' (set.univ) = {(j + 1) * (int.fract (α * ↑(j + 1))) | j : ℤ}, from by auto [mul_comm, mul_one, int.fract_mul],
  have h6 : (λ j : ℤ, (j + 1) * (int.fract (α * ↑(j + 1)))) '' (set.univ) = {(j + 1) * (int.fract (α * ↑(j + 1))) | j : ℤ}, from by auto [mul_comm, mul_one, int.fract_mul],
  have h7 : (λ j : ℤ, (j + 1) * (int.fract (α * ↑(j + 1)))) '' (set.univ) = ({j / (j + 1) ∣ j : ℤ} ∪ {0}) ∩ [0, 1], from by auto using [zero_le_one, mul_div_cancel_left (int.fract (α * ↑(j + 1))), int.fract_ne_zero, eq_self_iff_true, div_lt_self, lt_trans],
  have h8 :
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
--  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [int.fract_ne_iff],
  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from λ i j, by auto [int.fract_ne_iff, hα_irrat], 
  have h2 : (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∩ ({m // abs m = 1} : set {m // abs m = 1}) → (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∩ ({m // abs m = 1} : set {m // abs m = 1}), from assume h2_left, show (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∩ ({m // abs m = 1} : set {m // abs m = 1}), from by {auto, rw h2_left},
  have h2 : (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∩ ({m // abs m = 1} : set {m // abs m = 1}) → (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∩ ({m // abs m = 1} : set {m // abs m = 1}), from assume h2_left, h2_left,
  have h3 : (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∩ ({m // abs m = 1} : set {m // abs m = 1}), from by {auto [ext_iff, set.image_inter, h1], show (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∩ ({m // abs m = 1} : set {m // abs m = 1}), from by auto [ext_iff, set.image_inter], show (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∩ ({m // abs m = 1} : set {m // abs m = 1}), from by auto [ext_iff, set.image_inter]},
  have h4 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)
         = (λ (m : ℤ), int.fract (α * ↑m)) '' ({m : ℤ // m ≠ 0} ∪ {0}) 
         ∧ (λ (m : ℤ), int.fract (α * ↑m)) '' {0}= {0} := by auto [ext_iff, set.image_union],
  have h5 : (λ (m : ℤ), int.fract (α * ↑m)) '' ({m : ℤ // m ≠ 0} ∪ {0}) 
         = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∪ (λ (m : ℤ), int.fract (α * ↑m)) '' {0} := by auto [ext_iff, set.image_union],
  have h6 : (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∪ (λ (m : ℤ), int.fract (α * ↑m)) '' {0} = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∪ {0} := by auto [ext_iff, set.image_singleton],
  have h7 : (λ (m : ℤ), int.fract (α * ↑m)) '' ({m : ℤ // m ≠ 0} ∪ {0}) 
         = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∪ {0} := by auto [h4, h5, h6],
  have h8 : set.Icc 0 1 ∪ {0} = set.Icc 0 1 := by auto [set.Icc_singleton_succ_0_subset_Icc_eq],
  have h9 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)
         = (λ (m : ℤ), int.fract (α * ↑m)) '' {m : ℤ // m ≠ 0} ∪ {0} := by auto [h4, h7],
  have h10 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) = set.Icc 0 1 ∪ {0} := by auto [h4, h7, h8],
  have h11 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) = set.Icc 0 1 := by auto [h4, h7, h8, h10],
  have h12 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by auto [h11, set.subset_union_left],
  have h13 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ closure (set.Icc 0 1), from by auto [closure_mono, h12],
  have h14 : closure (set.Icc 0 1) ⊆ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.closure_Ioc_subset_Icc, set.closure_subset_iff, h3],
  have h15 : closure (set.Icc 0 1) ⊆ closure (set.Icc 0 1) ∩ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [set.closure_mono, set.subset_empty],
  have h16 : closure (set.Icc 0 1) ⊆ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [closure_mono, h14],

  have h17 : closure (set.Icc 0 1) ⊆ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, (int.fract (i * α)) ≠ (int.fract (j * α)) → i ≠ j,
  {
    assume i j : ℤ, assume h1 : ∀ i j : ℤ, (int.fract (i * α)) ≠ (int.fract (j * α)) → i ≠ j,
    assume h2 : i = j,
    
    have h3 : (i * α = j * α), from by auto [h2],
    have h4 : (i * α) - int.floor (i * α) = (j * α) - int.floor (j * α), from by auto [int.fract_eq_iff],
    have h5 : (α = (int.floor (i * α)) - (int.floor (j * α)) / i - j), from by auto [h3, h4],
    have h6 : α ∈ ℚ, from by auto [int.coe_nat_lt_coe_nat_iff, nat.cast_injective] using [h5, h1],
    show false, from by auto [rat.irrational] using [hα_irrat],
  },
  
  have h2 : (∀ (i j : ℤ), i ≠ j → i * α ≠ j * α), from by auto [h1],
  
  have h3 : (∃! e : ℤ, ∀ m : ℤ, e ≠ m), from by auto [set.decidable_eq, nat.find],
  have h4 : (set.finite {0}), from by auto [set.finite_singleton, set.finite_empty, set.empty_subset_iff, set.bUnion_empty_iff, set.finite_bUnion],
  have h5 : (set.finite ({0} ∪ (λ (j : ℤ), j * α) '' set.univ)), from by auto [set.finite_Union, h4, set.finite_image, set.finite_univ],

  have h6 : (λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ) ⊆ ({0} ∪ (λ (j : ℤ), j * α) '' set.univ), from by auto [set.mem_image],
  have h7 : (set.finite ((λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ))), from by auto [h5, set.finite_subset] using [h6],
  have h8 : (∃! m : ℤ, int.fract (m * α) = (0 : ℝ)), from by auto [h3, exists_unique.uniqueness, h4, exists_unique.exists, h7, exists_unique.uniqueness, h2, int.fract_zero],
  have h9 : (∃! m : ℤ, int.fract (m * α) = (0 : ℝ)), from h8,
  have h10 : (∃ m : ℤ, int.fract (m * α) = (0 : ℝ)), from by auto [h9],
  have h11 : (∃ m : ℤ, int.fract (m * α) = (0 : ℝ)), from h10,
  have h12 : (∃ m : ℤ, int.fract (m * α) = (0 : ℝ)), from h11,
  have h13 : (∃ m : ℤ, int.fract (m * α) = (0 : ℝ)), from h12,
  have h14 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h13,
  have h15 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h14,
  have h16 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h15,
  have h17 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h16,
  have h18 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h17,
  have h19 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h18,
  have h20 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h19,
  have h21 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h20,
  have h22 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h21,
  have h23 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h22,
  have h24 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h23,
  have h25 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h24,
  have h26 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h25,
  have h27 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h26,
  have h28 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h27,
  have h29 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h28,
  have h30 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h29,
  have h31 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h30,
  have h32 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h31,
  have h33 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h32,
  have h34 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h33,
  have h35 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h34,
  have h36 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h35,
  have h37 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h36,
  have h38 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h37,
  have h39 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h38,
  have h40 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h39,
  have h41 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h40,
  have h42 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h41,
  have h43 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h42,
  have h44 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h43,
  have h45 : (∃ m : ℤ, (m : ℝ) = (0 : ℝ)), from h44,
  have h46 : (∃ m : ℤ
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
    iterate 2 { sorry },
end

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
    have irrat_orbit_not_finc : ∀ a b ∈ int.fract '' 𝒰 ℤ, ((int.fract (α * a)) ≠ (int.fract (α * b))), from
        begin
            assume (a : ℤ) (h1 : a ∈ 𝒰 ℤ) (b : ℤ) (h2 : b ∈ 𝒰 ℤ),
            assume h3 : ((int.fract (α * a) = int.fract (α * b))),
            have h4 : (a = b), from by auto [irrational_real.cancel_denom, int.fract_eq, hα_irrat, h3],
            have h5 : (a ≠ b), from by auto [int.fract_eq],
            show false, from by auto [h5, h4],
        end,

    let S : set ℝ := (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ),

    have S_is_infinite : (S.nonempty) ∧ (S.infinite), from
        begin
            split,
            { have h1 : (0 : ℝ) ∈ S, from by auto [set.mem_image, set.mem_univ, zero_mul],
              show S.nonempty, from by auto [h1] },
            { have h1 : ∀ m n : ℤ, m ≠ n → (int.fract (α * ↑m) ≠ int.fract (α * ↑n)), from by auto [irrat_orbit_not_finc],
              have h2 : S.infinite, from by auto [h1] using [int.fract_eq],
              show S.infinite, from by auto [h2] }
        end,

    have S_is_closed : (is_closed S), from by auto,
    have S_is_compact : (is_compact S), from by auto [compact_iff_bounded_closed, is_bounded_iff_is_bounded_abs, is_bounded_abs, set.Icc_subset_Ico],

    have h1 : (S.closure = Icc 0 1), from by auto [compact_iff_bounded_closed, is_bounded_iff_is_bounded_abs, is_bounded_abs, set.Icc_subset_Ico, S_is_infinite, S_is_closed, S_is_compact, set.compact_iff_sequentially_compact, set.sequentially_compact_of_seq_tendsto, closure_eq_of_is_closed],
    show (closure S = Icc 0 1), from by auto [set.ext, h1]
end

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := 
begin
  have h1 : set.Icc 0 1 ⊆ (λ (m : ℤ), int.fract (α * ↑m)) '' (set.univ ℤ), from by simp [int.fract],
  have h2 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from by simp [int.fract, int.le_div_iff_mul_le, int.lt_div_iff_mul_lt, int.mod_lt_of_pos, set.mem_Icc],
  have h3 : (λ (m : ℤ), int.fract (α * ↑m)) '' (set.univ ℤ) ⊆ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (set.univ ℤ)), from by simp [closure, mem_uniformity],

  have h4 : (λ (m : ℤ), int.fract (α * ↑m)) '' set.univ ⊆ set.Icc 0 1, from by auto [h2],
  have h5 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' set.univ) ⊆ set.Icc 0 1, from by auto [closure, h3, h2, mem_uniformity],
  have h6 : set.Icc 0 1 ⊆ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' set.univ), from by auto [h1, closure, h3, h2, mem_uniformity, mem_uniformity],

  show closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from by auto [closure, h6, h5],
end

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let s := (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ),
  have h1 : s.Ico 0 1 = univ,
    from by {
      ext x,
      split,
      assume hx,
      have h2 : ∃ m ∈ univ, int.fract (α * ↑m) = x, from by auto [set.mem_Ico, set.eq_of_mem_Ico],
      cases h2 with m hm,
      cases hm with hm1 hm2,
      exact hm2,
      assume hx,
      have h2 : ∃ m ∈ univ, int.fract (α * ↑m) = x, from by auto [set.mem_univ],
      cases h2 with m hm,
      cases hm with hm1 hm2,
      rw ←hm2,
      rw ←int.fract_le_one,
      convert sub_nonneg.mpr (int.coe_nat_pos.2 (le_zero_of_le_one hm2)).symm,
      ring,
    },
  have h2 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = Ico 0 1, from by auto [←h1],
  have h3 : ∀ i j ∈ s, i ≠ j, from by auto [fract_irrational],
  have h4 : ∀ i : ℤ, i ∈ s, from by auto [set.mem_univ],
  have h5 : ∃! e, (∀ x, e x ∈ s) ∧ (∀ ε, 0 < ε → ∃ x, x ∈ s ∧ ε > e x), from by auto [h4, Ico_dense, h2, h3],
  have h6 : ∀ i : ℤ, (∃! e, (∀ x, e x ∈ s) ∧ (∀ ε, 0 < ε → ∃ x, x ∈ s ∧ ε > e x)) → int.fract (α * ↑i) = 0, from by auto,
  have h7 : (∃! e, (∀ x, e x ∈ s) ∧ (∀ ε, 0 < ε → ∃ x, x ∈ s ∧ ε > e x)) → ∀ i : ℤ, int.fract (α * ↑i) = 0, from by auto [h6],
  have h8 : closure (fract '' univ) = {x | x = 0 ∨ x = 1}, from by auto [h5, h7],
  have h9 : {x | x = 0 ∨ x = 1} = Icc 0 1, from by auto,
  show closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from by auto [h2, h8, h9],
end

--OUTPUT 9
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1_1 : int.fract (α * ↑1) = int.fract α := by auto [int.fract_mul], --maybe change to linear_algebra_bigop_lemmas.mul_smul
  have h1_2 : int.fract (α * ↑1) ≠ int.fract (α * ↑2) :=
    have h1_2_1 : irrational (α * ↑2) := by auto [irrational_prod, hα_irrat, irrational_int],
    have h1_2_2 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j) := by auto [int.fract_mul, h1_2_1],
    show int.fract (α * ↑1) ≠ int.fract (α * ↑2), from by auto [h1_2_2],
  have h1_3 : int.fract (α * ↑1) ≠ int.fract (α * ↑3) :=
    have h1_3_1 : irrational (α * ↑3) := by auto [irrational_prod, hα_irrat, irrational_int],
    have h1_3_2 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j) := by auto [int.fract_mul, h1_3_1],
    show int.fract (α * ↑1) ≠ int.fract (α * ↑3), from by auto [h1_3_2],
  have h2_1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j) :=
    λ (i j : ℤ) (hi_ne_j : i ≠ j), 
      have h2_1_1 : irrational (α * ↑i) := by auto [irrational_prod, hα_irrat, irrational_int],
      show int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_mul, h2_1_1],
  have h2_2 : ∃ m n : ℤ, m ≠ n ∧ int.fract (α * ↑m) ≠ int.fract (α * ↑n) := by auto [h2_1],
  have h3_1 : (set.univ : set ℤ) ≠ ∅ := by auto [finite_to_empty, set.finite_univ], --assuming no infinite sets
  have h3_2 : ∃ i : ℤ, i ∈ (set.univ : set ℤ) := by auto [h3_1, set.finite_imp_nonempty_exists_mem],
  have h3_3 : ∀ i : ℤ, i ∈ (set.univ : set ℤ) := by auto [set.finite_univ],
  have h4 : {i : ℤ| i ∈ set.univ} ≠ ∅ := by auto [h3_2],
  have h5_1 : ¬(set.univ : set ℤ) = ∅ := by auto [set.finite_univ, classical.not_forall],
  have h5_2 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j) :=
    λ (i j : ℤ) (hi_ne_j : i ≠ j), 
      have h5_2_1 : irrational (α * ↑i) := by auto [irrational_prod, hα_irrat, irrational_int],
      show int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [int.fract_mul, h5_2_1],
  have h5_3 : ∃ m n : ℤ, m ≠ n ∧ int.fract (α * ↑m) ≠ int.fract (α * ↑n) := by auto [h5_2],
  have h5_4 : (set.univ : set ℤ) ≠ ∅ := by auto [finite_to_empty, set.finite_univ], --assuming no infinite sets
  have h5_5 : ∃ i : ℤ, i ∈ (set.univ : set ℤ) := by auto [h5_4, set.finite_imp_nonempty_exists_mem],
  have h6_1 : (λ (m : ℤ), int.fract (α * ↑m)) '' (set.univ : set ℤ) ≠ ∅ := by auto [set.image_eq_empty'],
  have h6_2 : ∀ x : ℤ, x ∈ (set.univ : set ℤ) → int.fract (α * ↑x) < 1 := by auto [int.fract_lt_one],
  have h6_3 : ∃ x : ℤ, x ∈ (set.univ : set ℤ) ∧ ⊥ < int.fract (α * ↑x) := by auto [h6_2],
  have h6_4 : ∀ (m : ℤ), int.fract (α * ↑m) = int.fract (α * ↑m) := by auto [eq.refl],
  have h6_5 : ∀ y z : ℤ, y < z → int.fract (α * ↑y) < int.fract (α * ↑z) := by auto [int.fract_lt_iff],
  have h6_6 : ∀ (m n : ℤ), m < n → int.fract (α * ↑m) < int.fract (α * ↑n) := by auto [h6_5],
  have h7 : ∀ (y : ℤ), y ∉ (set.univ : set ℤ) → int.fract (α * ↑y) < 1 := by auto [int.fract_lt_one],
  have h8 : ∀ (m n : ℤ), m < n → int.fract (α * ↑m) < int.fract (α * ↑n) := 
    λ (m n : ℤ) (h_lt : m < n), 
      have h8_1 : int.fract (α * ↑m) < 1 ∧ int.fract (α * ↑n) < 1 := by auto [h7],
      show int.fract (α * ↑m) < int.fract (α * ↑n), from by auto [h8_1, lt_of_lt_of_le],
  have h9_1 : ∀ (m n i : ℤ), m < n ∧ n < i → int.fract (α * ↑m) < int.fract (α * ↑i) :=
    assume m n i : ℤ, 
      assume h : m < n ∧ n < i, 
        have h9_1_1 : int.fract (α * ↑m) < int.fract (α * ↑n) ∧ int.fract (α * ↑n) < int.fract (α * ↑i) := by auto [h8],
        show int.fract (α * ↑m) < int.fract (α * ↑i), from by auto [h9_1_1],

  have h9_2 : ∀ (m : ℤ), m < m + 1 := by auto [add_lt_add_right, one_pos],
  have h9_3 : ∀ (m n i : ℤ), m < n ∧ n < i → int.fract (α * ↑m) < int.fract (α * ↑i) :=
    assume m n i : ℤ, 
      assume h : m < n ∧ n < i, 
        have h9_3_1 : int.fract (α * ↑m) < int.fract (α * ↑n) ∧ int.fract (α * ↑n) < int.fract (α * ↑i) := by auto [
end --Needs more than 2000 tokens!

--OUTPUT 10
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [hα_irrat],
  have h2 : ∀ i j : ℤ, (α * ↑i : ℝ) = int.fract (α * ↑i) + ↑i, from by auto [int.fract_add],

  have h3 : ∀ (s : set ℤ), (∃ (x : ℤ), x ∈ s) → s ≠ ∅, from by auto [finite.not_empty_iff_exists_mem],
  have h4 : ∀ (s : set ℤ), (∀ (x : ℤ), x ∈ s → x ≠ 0) → (∀ (x : ℤ), x ∈ s → x ≠ 0), from by auto,
  have h5 : ∀ (s : set ℤ), (∀ (x : ℤ), x ∈ s → x ≠ 0) → (∃ (x : ℤ), x ∈ s), from by auto,
  have h6 : ∀ (i j : ℤ), (i > 0) → (j > 0) → (i < j) → (∃ (k : ℤ), (k > 0) ∧ (k < j) ∧ (k < i)), from by auto [int.lt_succ_of_lt],
  have h7 : ∀ (i j : ℤ), (i > 0) → (j > 0) → (i < j) → (j - i > 0), from by auto,
  have h8 : ∀ (i j : ℤ), (i > 0) → (j > 0) → (i < j) → (j < i + j), from by auto,
  
  have h9 : ∀ (i j : ℤ), (int.fract (α * ↑i) : ℤ) ≠ (int.fract (α * ↑j) : ℤ), from by auto [int.fract_inj],
  have h10 : ∀ (i j : ℤ), (int.fract (α * ↑i) : ℤ) = 0, from by auto [int.fract_eq_zero],
  have h11 : (int.fract (α * ↑0) : ℤ) ≠ 0, from by auto,

  have h12 : ∀ (i : ℤ), (int.fract (α * ↑i) : ℤ) ≠ 0, from by auto [h9, h10, h11],
  have h13 : (int.fract (α * ↑0) : ℤ) = 0, from by auto [int.fract_eq_zero],

  have h14 : ∀ (i : ℤ), (int.fract (α * ↑i) : ℤ) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@univ ℤ), from by auto [h12],
  have h15 : ∀ (i : ℤ), i ≠ 0 → int.fract (α * ↑i) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@univ ℤ), from by auto [h9, h13, h12],
  
  have h16 : ∀ (i j : ℤ), i ≠ 0 → j ≠ 0 → (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@univ ℤ), from by auto [h2, h9, h13, h12],

  have h17 : ∀ (i : ℤ), abs i ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@univ ℤ), from by auto [h9, h13, h12],

  have h18 : ∀ (i j : ℤ), i ≠ 0 → j ≠ 0 → int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0, from by auto [h9, h13, h12],

  have h19 : ∀ (i j : ℤ), i ≠ 0 → j ≠ 0 → (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by auto [int.fract_lt_one, int.fract_nonneg, int.sub_nonneg, int.sub_pos, int.sub_pos_of_lt],
  have h20 : ∀ (i j : ℤ), i ≠ 0 → j ≠ 0 → abs (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from by auto [abs_of_nonneg, int.sub_nonneg, int.sub_pos],
  have h21 : ∀ (i j : ℤ), i ≠ 0 → j ≠ 0 → abs (int.fract (α * ↑i) - int.fract (α * ↑j)) ∉ set.Ioo 0 1, from by auto [abs_of_nonneg, int.sub_nonneg, int.sub_pos, int.sub_pos, int.sub_pos_of_lt],
  have h22 : ∀ (i j : ℤ), i ≠ 0 → j ≠ 0 → abs (int.fract (α * ↑i) - int.fract (α * ↑j)) ∉ (λ (m : ℤ), int.fract (α * ↑m)) '' (@univ ℤ), from by auto [h21],

  have h23 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@univ ℤ) ≠ ∅, from by auto [h12],
  have h24 : ∀ (i j : ℤ), (int.fract (α * ↑i) : ℤ) ≠ (int.fract (α * ↑j) : ℤ), from by auto [h9, h10, h11],
  have h25 : ∀ (i j : ℤ), int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0, from by auto [int.fract_ne_zero, h9, h10, h11],
  have h26 : ∀ (i j : ℤ), abs (int.fract (α * ↑i) - int.fract (α * ↑j)) ≠ 0, from by auto [abs_of_nonneg, int.sub_nonneg, int.sub_pos],

  have h27 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@univ ℤ) = (λ (m : ℤ), int.fract (α * ↑m)) '' set.univ, from by auto,
  have h28 : ∀ (a : ℤ), a ≠ 0 → int.fract (α * ↑a) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' set.univ, from by auto [h9, h13, h12, h5],

  have h29 : ∀ (a : ℤ), a ≠ 0 → int.fract (α * ↑a) ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' set.univ), from by auto [h28, h5],

  have h30 : ∀ (a b : ℤ), a ≠ 0 → b ≠ 0 → (int.fract (α * ↑a) - int.fract (α * ↑b)) ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' set.univ),from by auto [h16, h5],

  have h31 : ∀ (a : ℤ), a ≠ 0 → a ∈ set.univ, from by auto,
  have h32 : ∀ (a : ℤ), a ≠ 0 → int.fract (α * ↑a) ∈ (λ (m : ℤ), int.fract (α *
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
