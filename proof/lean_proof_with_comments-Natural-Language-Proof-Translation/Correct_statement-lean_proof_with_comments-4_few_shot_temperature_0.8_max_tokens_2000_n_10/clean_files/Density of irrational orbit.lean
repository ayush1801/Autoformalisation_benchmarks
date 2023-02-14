import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let α be an irrational number.
  -- Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$.
  -- If this were not true, then
  --$i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor,$
  have h1 : ∀ (i j : ℤ) (hij : i ≠ j), int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    intros i j hij,
    assume h2,
    have h4 : α * ↑i - int.floor (α * ↑i) = int.fract (α * ↑i), from by rw int.fract_eq_sub_floor,
    have h3 : (α * ↑i) - int.floor ((α * ↑i)) = (α * ↑j) - int.floor ((α * ↑j)), by {rw [h4,h2],},
    have h5 : α = ((int.floor ((α * ↑i)) - int.floor (α * ↑j))/(i - j)), from by {rw [div_eq_iff_mul_eq,mul_comm,h3],},
    have h6 : α ∈ ℚ, from by {rw h5,from hα_irrat.irrational_iff hij,},
    show false, from hα_irrat h6,
  },

  --Hence,
  --$$S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$$
  --is an infinite subset of $\left[0,1\right]$.
  have h2 : (λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from λ x h, begin
    --Assume (h : x ∈ (λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ)),
    have h : x ∈ (λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ), from h,
    --As (λ (m : ℤ), int.fract (m * α)) is a continuous function and (int.fract) maps into the unit interval,
    --we have $f(x) = int.fract(x) \in [0,1]$
    have h3 : x = int.fract(x) ∈ [0,1], from set.mem_image_of_mem h,
    --Hence the result.
    exact h3,
  end,
  have h3 : (λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ) ≠ ∅, from begin
    --As (λ (m : ℤ), int.fract (m * α)) is a continuous function and (int.fract) maps into the unit interval,
    --we have $f(x) = int.fract(x) \in [0,1]$
    have h4 : (λ (m : ℤ), int.fract (m * α)) 0 = 0 ∈ [0,1], from by {rw [set.univ_def],norm_num,},
    exact h4,
  end,

  --By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  have h4 : ∃ x, x ∈ closure ((λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ)), from by {
    apply closure_of_discrete_subset_of_univ h2 h3,
    assume (m : ℤ) (n : ℤ) (hmn : m ≠ n),
    suffices h5 : int.fract (m * α) ≠ int.fract (n * α), from h5,
    apply h1 m n hmn,
  },
  have h5 : ∃ x, x ∈ closure ((λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ)) ∧ x ∈ set.Icc 0 1, from by {
    cases h4 with x h4,
    have h6 : x ∈ {x : ℝ | ∃ m : ℤ, x = int.fract (m * α)}, from h4,
    have h7 : x ∈ {x : ℝ | ∃ m : ℤ, x = int.fract (m * α)} ∧ x ∈ set.Icc 0 1, from by {apply set.mem_inter_iff, split; exact h6, exact h2 h6,},
    exact h7,
  },

  -- One can thus find pairs of elements of $S$ that are arbitrarily close.
  have h6 : ∃ x y, x ∈ closure ((λ (m : ℤ), @int.fract ℝ _ (m * α)) '' (@set.univ ℤ)) ∧ y ∈ closure ((λ (m : ℤ), @int.fract ℝ _ (m * α)) '' (@set.univ ℤ)) ∧ x ≠ y ∧  |x - y| < (1: ℝ), from by {
    cases h5 with x hx,
    cases hx with hx,
    cases hx with hx hx,
    cases hx with hx hx,
    cases hx with hx hx,
    rcases hx with ⟨m, rfl⟩,    
    rw ← sub_eq_add_neg at hx,
    have h7 : |(m:ℝ)*α - (x:ℝ)| < 1, from by exact hx,
    rcases h7 with ⟨N, rfl⟩,
    have h8 : (N : ℝ) ≠ (m:ℝ), from by 
    {
      assume h8,
      have h9 : (m:ℝ) - (m:ℝ) = (N:ℝ) - (m:ℝ), by rw h8,
      rw zero_sub at h9,
      rw zero_sub at hx,
      rw h9 at hx,
      apply absurd hx,
      norm_num,
    }, 
    have h9 : (↑N : ℝ) - (m:ℝ) < 1, from by linarith,
    use int.fract(N * α),
    use int.fract(m * α),
    use N,
    use m,
    have h10 : int.fract(N * α) ∈ closure ((λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ)), from begin
      have h11 : int.fract(N * α) ∈ (λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ), from begin
        -- TODO
        have h12 : N ∈ univ, from set.mem_univ N,
        exact mem_image_of_mem (λ (m : ℤ), int.fract (m * α)) h12,
      end,
      exact subset_closure h11,
    end,
    split,
    exact h10,
    split,
    exact hx,
    split,
    exact h8,
    rw abs_of_pos (sub_pos_of_lt h9), 
  },

  --Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$,
  have h7 : ∀ x y, x ∈ closure ((λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ)) ∧ y ∈ closure ((λ (m : ℤ), int.fract (m * α)) '' (@set.univ ℤ)) → int.fract (y * α
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h_fract_zero : ∀ (a : ℤ), ∃ m : ℤ, int.fract (a * ↑α) < ↑m * (int.fract α), from
  begin
    assume a, 
    have h1 : (a * ↑α) - a * (int.floor (a * ↑α)) < a * (int.fract α), begin
      lin
end

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from by {
    apply closure_subset,
    intros m h2,
    rw set.mem_Icc_eq,
    split; linarith,
  },

  have h2 : ∀ x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), ∃ (m : ℤ), x = int.fract (α * ↑m), from by {
    assume (x : ℝ) (h2 : x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))),
    cases h2 with U h3,
    assume h4,
    cases h3 with a h5,
    use a,
    rw set.mem_image_eq at h5,
    cases h5 with b h6,
    rw h6,
    symmetry,
    apply int.fract_mul,
  },

  have h6 : ∀ (x : ℝ), x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ↔ ∃ (m : ℤ), x = int.fract (α * ↑m), from by {
    intros x,
    split;
    assume hx,
    {
      apply h2, assumption,
    },
    {
      assume h7,
      cases h7 with m hx,
      use {m},
      rw set.mem_singleton_iff,
      rw set.mem_image_eq,
      use m,
      rw set.mem_univ,
      exact hx,
    },
  },

  have h7 : ∀ y ∈ set.Icc 0 1, ∃ (m : ℤ), int.fract (α * ↑m) = y, from by {
    assume y,
    assume h7,
    rw set.mem_Icc_eq at h7,
    use ↑nat.floor (α * y),
    calc int.fract (α * ↑nat.floor (α * y)) = int.fract(α * y) : by rw [hz_nat_floor, mul_comm],
    show int.fract (α * y) = y, from by {rw hx_int_fract, linarith,},
  },

  have h8 : ∀ y ∈ set.Icc 0 1, ∃ x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), x = y, from by {
    assume (y : ℝ), 
    assume h7,
    have h8 : ∃ (m : ℤ), int.fract (α * ↑m) = y, from by {apply h7,},
    cases h8 with m hm,
    use int.fract (α * ↑m),
    rw h6,
    use m,
    exact hm,
  },

  have h9 : ∀ x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), ∃ y ∈ set.Icc 0 1, y = x, from by {
    assume x,
    assume hx,
    use x,
    have h8 : ∃ (m : ℤ), int.fract (α * ↑m) = x, from by {apply h6, assumption,},
    cases h8 with m hm,
    apply set.mem_Icc_eq,
    split,
    have h9 : 0 ≤ int.fract(α * ↑m), from by {rw hm, linarith},
    exact h9,
    have h10 : int.fract(α * ↑m) < 1, from by {rw hm, linarith,},
    exact h10,
  },

  exact subset.antisymm h1 set.subset_Icc,
end

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, (int.fract (α *↑i)) = (int.fract (α * ↑j)) → i = j, 
  from by {intros i j h, rw int.floor_eq_iff at h, rw int.floor_eq_iff at h,
          rw [int.coe_nat_eq_coe_int_iff, int.coe_nat_eq_coe_int_iff] at h,
          exact quotient.sound (by exact_mod_cast _ _) (by exact_mod_cast _ _) h,
          },

  have h2 : ∀ {i j : ℤ}, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j),
  from by {intros i j hi, rw int.fract_eq_iff, rw int.fract_eq_iff, rw int.fract_eq_iff, rw [int.coe_nat_eq_coe_int_iff, int.coe_nat_eq_coe_int_iff],
          rw int.nat_abs_of_nonneg (int.coe_nat_nonneg _), 
          rw int.nat_abs_of_nonneg (int.coe_nat_nonneg _), 
          rw int.nat_abs_of_nonneg (int.coe_nat_nonneg _), 
          rw mul_comm (int.nat_abs _) (int.nat_abs _),
          intro h, rw ← h at hi, rw [← int.coe_nat_eq_coe_int_iff, ← int.coe_nat_eq_coe_int_iff] at hi,
          have htemp := show ∀ (i : ℕ), (i : ℤ) * (1 : ℤ) = i * 1, from by {intros, ring},
          rw htemp at hi, rw htemp at hi, rw htemp at hi,
          have htemp2 := show ∀ (i : ℕ), (i : ℝ) = ↑i, from by {intros, rw ← int.coe_nat_eq_coe_int_iff},
          rw htemp2 at hi, rw htemp2 at hi, rw htemp2 at hi,
          exact hα_irrat (hi.symm),
          },

  -- $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$ is an infinite subset of $\left[0,1\right]$
  have h3 : ∀ {i j : ℤ}, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from h2, 
  have h3.r : nonempty.intro (int.fract (α * 1)) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' set.univ := 
  by {use (1 : ℤ),simp [h3],rw ← int.coe_nat_eq_coe_int_iff,},
  rw ← set.nonempty_iff_ne_empty at h3.r,

  have h4 : ∀ {i j : ℤ}, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j),
  from h3, 

  have h5 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ∉ {(int.fract (α * ↑j))},
  from by {intros i j hi, assume (h5 : int.fract (α * ↑i) = int.fract (α * ↑j)), contradiction},

  have h6 : ∀ i : ℤ, (int.fract (α * ↑i)) ∉ {(int.fract (α * ↑i))}, by {intros i, assume h1, assumption},
  have h7 : ∀ i : ℤ, (int.fract (α * ↑i)) ∉ {(int.fract (α * ↑i))}, from h6, 
  
  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$
  have hb : closure (λ m : ℤ, int.fract (α * ↑m)) ∩ set.Icc 0 1 ≠ ∅, 
  from by {rw ← h3.r, apply set.inter_nonempty_iff_ne_empty, apply set.is_closed_Icc, apply set.is_closed_closure,},

  have h8 : ∀ (S : set (ℤ → ℝ)) {l : ℝ}, (closure S) ∩ set.Icc 0 1 ≠ ∅ → l ∈ S → ∃ (ε : ℝ),  ε > 0, ∃ (x : ℤ → ℝ), x ∈ S ∧ |x - l| < ε, 
  from by {
           assume S l hb hl, cases hl with i hi, 
           let iα := (int.fract (α * ↑i)),
           let htemp := show iα ∈ closure S ∩ set.Icc 0 1, from by {apply set.mem_inter,
                                                                   apply set.mem_closure_iff.mp,
                                                                   use i,
                                                                   simp [hi, h7],
                                                                   apply set.mem_Icc,
                                                                   split, 
                                                                   rw ← int.fract_zero,
                                                                   apply int.fract_lt,
                                                                   rw ← int.fract_one,
                                                                   apply int.fract_lt,
                                                                  },
           have htemp2 : ∃ (ε : ℝ), ε > 0,  ∃ (x : ℤ → ℝ), x ∈ (λ m : ℤ, int.fract (α * ↑m)) '' set.univ ∧ |x - iα| < ε, 
           from by {
                     use (iα),
                     use (↑i),
                     split,
                     have htemp3 := show int.fract (α * ↑i) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' set.univ, from by {simp [hi],},
                     simp [htemp3, hi],
                     have htemp_2 := show  1⁻¹ ∈ set.Icc 0 (1 : ℝ), from by {split, exact zero_lt_one, exact le_refl 1},
                     have htemp_3 := show 1⁻¹ = iα, by {rw ← int.fract_one,rw ← int.fract_fract_of_nat,ring,},
                     have htemp_4 := show  1⁻¹ ∈ set.Icc 0 (1 : ℝ), from by {rw htemp_3, exact htemp_2},
                     have htemp_5 := show |iα - iα| < 1⁻¹, from by {rw abs_of_nonneg (sub_nonneg.mpr (by {apply int.fract_nonneg})),rw int.fract_fract_of_nat,ring,},
                     exact lt_trans (htemp_5) (inv_pos one_pos),
                    },
           exact htemp2,

           },

  cases h8 (λ m : ℤ, int.fract (α * ↑m)) hb h6.r with ε (h9 : ε > 0), 
  cases h9 with x (h9), 
  cases h9 with hx hxmini,
  cases hx with i hi,
  rw ← hi at hxmini,
  have h10 := hxmini,
  have h11 : ∀ (ε : ℝ), ε > 0 → ∃ (i : ℤ), |x - int.fract (α * ↑i)| < ε, 
  from by {
           assume (ε : ℝ) (h11 : ε > 0),
           have htemp : 0
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let α be an irrational number
  assume (α : ℝ) (hα_irrat : irrational α),
  -- Then for distinct $i,j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$
  have h1 : ∀ (i j : ℤ), i ≠ j → ∄ p q ∈ (@set.univ ℤ), p ≠ q ∧ int.fract (α * ↑p) = int.fract (α * ↑q), from assume (i : ℤ) (j : ℤ) (hint : i ≠ j), assume hpq : (∃ p q, p ∈ (@set.univ ℤ) ∧ q ∈ (set.univ) ∧ p ≠ q ∧ int.fract (α * ↑p) = int.fract (α * ↑q)),
  let ⟨p, q, h2, h3, h4, h5⟩ := hpq in by {
    have h6 : ∀ n : ℤ, n * α = n * int.fract α + n * int.nat_abs α, from int.fract_eq_of_nat_abs_mul_nat_abs,
    rw [h6 p, h6 q, ← int.fract_mul, ← int.fract_mul] at h5,
    have h7 : α = (int.fractα) / (int.nat_abs α), from eq.symm ((int.fract_eq_of_nat_abs_eq_one α hα_irrat).right.right),
    have h8 : p * α = p * int.fract α / (int.nat_abs α) + p * nat_abs α, from by rw h7 at h6 p,
    have h9 : q * α = q * int.fract α / (int.nat_abs α) + q * nat_abs α, from by rw h7 at h6 q,
    rw h8 at h5, rw h9 at h5,
    have h10 : ((p * int.fract α) / (int.nat_abs α)) + p * nat_abs α = ((q * int.fract α) / (int.nat_abs α)) + q * nat_abs α, from by rw h5,
    have h11 : (p * int.fract α) / (int.nat_abs α) = (q * int.fract α) / (int.nat_abs α), from by simp [h10],
    have h12 : (p * int.fract α) = ((q * int.fract α) / (int.nat_abs α)) * (int.nat_abs α), from by {rw ← h11, ring},
    have h13 : p * int.fract α = (q * int.fract α), from by {rw ← h12, apply int.nat_abs.eq_iff.2, linarith},
    have h14 : p * int.fract α = q * int.fract α, from by {rw h13, linarith}, 
    have h15 : int.fract (α * p) = int.fract (q * α), from by {rw [← int.fract_mul, ← int.fract_mul] at h14, exact h14},
    have h16 : α * p = q * α, from by {apply int.fract_eq_of_nat_abs_eq_one _ hα_irrat, split, linarith, exact h4, exact h15},
    have h17 : ((p : ℤ) : ℝ) = ((q : ℤ) : ℝ), from by rw h16,
    exact h4 (int.coe_nat_inj.2 (coe_int_inj h17)),
  },
  --If this were not true, then 
  --$i \alpha - \lfloor i \alpha\rfloor = \{i \alpha\} = \{j \alpha\} = j \alpha - \lfloor j \alpha\rfloor$,
  --which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor - \lfloor j \alpha\rfloor}{i - j} \in \mathbb{Q}$
  --Hence
  --$S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$ is an infinite subset of $\left[0,1\right]$
  rw eq_empty_iff_forall_not_mem,
  have h18 : ∀ (n : ℤ), (n : ℝ) ≠ 0, from by {intros n hn, linarith},
  have h19 : (set.univ : set ℤ) ≠ ∅, from by {rw set.univ_ne_empty_iff, apply h18},
  have h20 : set.finite (set.univ : set ℤ), from by {apply set.finite_univ},
  have h21 : set.finite ((λ (m : ℤ), int.fract (α * ↑m)) '' set.univ), from by {apply set.finite_image, exact h20},
  have h22 : ∃ (n : ℤ), n ∈ (set.univ : set ℤ), from by {rw set.univ_ne_empty_iff, exact h18 0},
  have h23 : ∀ (n : ℤ), int.fract (α * ↑n) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' set.univ, from by {intros n, use n, simp, linarith},
  have h23a : ∀ (n : ℤ), int.fract (α * ↑n) ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {intro n, use n, simp, linarith},
  have h24 : (λ (m : ℤ), int.fract (α * ↑m)) '' set.univ ≠ ∅, from by {rw eq_empty_iff_forall_not_mem, exact h23},

  --By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0,1]$.
  --One can thus find pairs of elements of $S$ that are arbitrarily close.
  have h26 : ∃ (p q : ℤ), p ∈ (set.univ : set ℤ) ∧ q ∈ (set.univ : set ℤ) ∧ p ≠ q ∧ int.fract (α * ↑p) = int.fract (α * ↑q), from by {apply exists_ne_of_infinite_of_finite_of_ne_empty h21 h24, },
  let ⟨p, q, h27, h28, h29, h30⟩ := h26 in by {

  --Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
  have h31 : (λ (m : ℤ), int.fract (α * ↑m)) '' set.univ ⊆ closure (λ (m : ℤ), int.fract (α * ↑m)) '' set.univ, from by {apply set.subset_univ, },
  have h32 : ∃ (n : ℤ), n ∈ closure (λ (m : ℤ), int.fract (α * ↑m)) '' (set.univ : set ℤ), from by {
    have h33 : ∃ (m : ℤ), m ∈ (λ (n : ℤ), int.fract (α * ↑n)) '' set.univ := h21,
    cases h33 with m h34,
    show ∃ (n : ℤ), n ∈ closure (λ (m : ℤ), int.fract (α * ↑m)) '' set.univ, from by {
      use m,
      apply set.mem_closure_iff.2,
      use
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin 
  sorry 
end

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
    -- We have shown that irrational number $\alpha$ and its integer multiples $i \alpha$ has fractional parts $[0,1]$
    have h_nonempty : (λ (m : ℤ), int.fract (α * ↑m)) '' set.univ ⊆ set.Icc 0 1, from by {
        assume (x : ℝ),
        by_contradiction h_false,
        apply x_mem_set_Icc_iff.1 h_false,
    },
    have h_dense_in_Icc : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' set.univ) ⊆ set.Icc 0 1, from by {
        assume x h,
        have h_non_empty : (λ (m : ℤ), int.fract (α * ↑m)) '' set.univ ≠ ∅, from by {
            exact set.nonempty_iff_exists_mem.2 ⟨int.fract α,set.mem_univ (int.fract α),rfl⟩,    
        },
        exact closure_eq_of_is_closed_idem h_non_empty h_nonempty h,
    },
    let seq_limit : (ℕ → ℝ) → ℝ → Prop :=  λ (u : ℕ → ℝ) (l : ℝ), ∀ ε > 0, ∃ N, ∀ n > N, |u n - l| < ε in

    -- Then, we need to show that the fractional parts $\{i \alpha\}$ must be dense in $[0,1]$
    have h1 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' set.univ) = set.Icc 0 1, from by {

        -- So we have to show that the set of fractional parts $\{i \alpha\}$ is both open and closed in $[0,1]$
        apply set.eq_of_is_open_eq_of_is_closed_eq,

        -- First, we have to show that the set of fractional parts $\{i \alpha\}$ is open in $[0,1]$
        -- So we need to show that $q \in [0,1] \implies \exists \epsilon > 0: \forall x \in [0,1] : x \in (q - \epsilon, q + \epsilon) \implies x \in \{i \alpha\}$
        rw set.is_open_iff,
        -- Let $q \in [0,1]$
        assume q hq,
        -- Let $\epsilon > 0$ be $q$
        use q,
        -- By Bolzano-Weiestrass theorem, the set of fractioal parts $\{i \alpha\}$ has a limit point in $[0,1]$
        -- So we can find a pair of elements of $\{i \alpha\}$ that are arbitrarily close. Since (the absolute value of) the difference of any two elements of $\{i \alpha\}$ is also an element of $\{i \alpha\}$, it follows that $0$ is a limit point of $\{i \alpha\}$
        -- The set of fractional parts is infinite as it contains $\alpha$, so it must have a limit point in $[0,1]$
        have h : ∃ x0, limit (λ (n : ℕ), int.fract (α * ↑n)) x0,
        from has_finite_limit.has_limit (λ (n : ℕ), α * ↑n) 0 α,
        cases h with limit_point h,
        cases h with ε h1,
        -- So we have that if $m x < y < (m + 1) x$, then $|y - \{m x\}| < \epsilon$
        have h2 : ∀ (nen : ℕ), ε > int.fract x → |int.fract (α * ↑nen) - limit_point| < ε, from
        by {
            assume n h3,
            have h4 : limit (λ (n : ℕ), int.fract (α * ↑n)) 0 → ∀ ε > 0, ∃ N, ∀ n > N, |(λ (n : ℕ), int.fract (α * ↑n)) n - 0| < ε, from h1,
            have h5 := (h4 ε h3),
            cases h5 with N h6,
            have h7 : ∀ n > N, |int.fract (α * ↑n) - limit_point| < ε, from h6,
            have h8 : |int.fract (α * ↑n) - limit_point| < ε, 
            from h7 n (by linarith),
            exact h8,
        },
        -- selected $x = \{i \alpha\}$ such that $\{x\}<\epsilon$
        let x := limit_point,
        have h3 : ∃ N, ∀ n > N, |int.fract (α * ↑n) - limit_point| < ε, from h2 x ε,
        cases h3 with N h4,
        -- So we have that if $m x < y < (m + 1) x$, then $|y - \{m x\}| < \epsilon$
        have h5 : ∀ (nen : ℕ), ε > int.fract x → |int.fract (α * ↑nen) - limit_point| < ε, from h2 x ε,
        have h6 : |int.fract (α * ↑N) - limit_point| < ε, from h5 N (by linarith),
        have h7 : ∃ N, ∀ n > N, |int.fract (α * ↑n) - limit_point| < ε, from ⟨N,h4⟩,
        -- selected $N$ such that $N \cdot\{x\} \leq y<(N+1) \cdot\{x\}$
        let N0 := N,
        have h8 : int.fract (α * ↑N0) ≤ q ∧ q < int.fract (α * ↑N0) + int.fract x := by 
        {
            split; linarith,
        },
        -- So $|y - \{N x\}|<\epsilon$
        have h9 : |q - int.fract (α * ↑N0)| < ε, from by
        {
            rw int.fract_eq_sub_floor_add_self at h8,
            have h10 : |int.fract (α * ↑N0) - limit_point| < ε, from h7 N0 (h8.left) h8.right,
            linarith,
        },
        have h10 : ∃ m : ℤ, int.fract (α * ↑m) = q, from 
        exists_int_neq_of_nat_neq_of_int_floor_eq
        (x * (int.floor (α * ↑N0) / x)) (x * (int.floor x)) N0
        (int.floor (α * ↑N0)) (int.floor (α * ↑N0)) (int.fract x) h8.2,
        have h11 : ∃ m : ℤ, int.fract (α * ↑m) = int.fract (α * ↑N0), from 
        exists_int_neq_of_nat_neq_of_int_floor_eq
        (x * (int.floor (α * ↑N0) / x)) (x * (int.floor x)) N0
        (int.floor (α * ↑N0)) (int.floor (α * ↑N0)) (int.fract x) h8.2,
        cases h10 with i h10,
        cases h11 with j h11,
        have h12 := int.fract_add α (α * ↑N0) j i,
        have h13 := int.fract_add α (α * ↑N0) N0 j,
        have h14 : int.fract (α * ↑j)
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α*i)) ≠ (int.fract (α*j)), from by {
    intros i j h, rw h,
    rw [rat.fract_eq_of_int, rat.fract_eq_of_int], ring,
  },
  have h2 : ∀ i j : ℤ, i ≠ j → (α * ↑i - int.nat_abs (↑i * α) : ℝ) ≠ (α * ↑j - int.nat_abs (↑j * α) : ℝ), from by {
    rintro i j h, rw [real.sub_eq_zero_iff_eq,real.sub_eq_zero_iff_eq], rw mul_comm, rw mul_comm, rw hα_irrat,
    linarith,
    linarith,
  }, 
  have h3 : ∀ i j : ℤ, i ≠ j → (α * ↑i - int.nat_abs (↑i * α) : ℝ) ≠ (α * ↑j - int.nat_abs (↑j * α) : ℝ), from by {
    intros i j h,
    apply h2, exact h,
  },
  have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i) : ℝ) ≠ (int.fract (α * ↑j) : ℝ), from by {
    rintro i j h, rw [rat.fract_eq_of_int,rat.fract_eq_of_int], exact h3 i j h,
  },
  have h5 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ∉ ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    rintro i j h, intro h_contra, apply h4 i j h, exact h_contra,
  },
  have h6 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ∉ ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    intros i j h, exact h5 i j h,
  },
  have h7 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by {
    intros i j h,
    apply h4 i j h,
  },
  have h8 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by {
    intros i j h,
    exact h7 i j h,
  },
  have h9 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ (@set.univ ℝ) ∧ ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by {
    split,
    {
      intros m hm,
      exact mem_univ _,
    },
    intros i j h, exact h7 i j h,
  },
  have h10 : (@set.univ ℤ) ⊆ ℕ, from by {
    intros i hi, rw ← int.coe_nat_lt, apply int.cast_lt.2, linarith,
  },
  have h11 : ∀ i : ℤ, ∃ j : ℤ, i ≠ j, from by {
    intros i,
    refine ⟨i + 1, _⟩,
    linarith,
  },
  have h12 : ∀ i : ℤ, (int.fract (α * ↑i)) ∉ ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    intros i,
    cases h11 i,
    rw mem_image,
    rw set.eq_empty_iff_forall_not_mem,
    rw set.compl_empty,
    rw set.univ_def,
    rw set.subset_univ,
    intros j h,
    exact h12 j h,
  },
  let S := (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ),
  have h13 : ∀ i ∈ S, ∃ j ∈ S, i ≠ j, from by {
    intros i hi,
    cases hi with j hj,
    rw hj at *,
    refine ⟨_, _, _⟩,
    rw mem_image,
    use j + 1,
    split,
    {
      exact set.mem_univ _,
    },
    {
      rw ← hj,
      rw ← int.coe_nat_add,
      rw ← mul_add,
      ring,
    },
  },
  have h14 : ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ (@set.univ ℝ), from by {
    intros m hm,
    exact mem_univ _,
  },
  have h15 : (λ (m : ℕ), int.fract (α * ↑m)) '' (@set.univ ℕ) ⊆ (@set.univ ℝ), from by {
    intros m hm,
    exact h14 m hm,
  },
  have h16 : ∀ n : ℕ, (int.fract (α * ↑n)) ∈ ((λ (m : ℕ), int.fract (α * ↑m)) '' (@set.univ ℕ)), from by {
    intros n,
    rw mem_image,
    use n,
    split,
    {
      exact set.univ_mem _,
    },
    {
      refl,
    },  
  },
  have h17 : ∀ i : ℤ, ∃ j : ℤ, i ≠ j, from by {
    intros i,
    refine ⟨i + 1, _⟩,
    linarith,
  },
  have h18 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by {
    intros i j h,
    rw h,
    rw [rat.fract_eq_of_int,rat.fract_eq_of_int], ring,
  },
  have h19 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ∈ S → (int.fract (α * ↑j)) ∈ S → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by {
    intros i j h h1 h2,
    exact h18 i j h,
  },
  have h20 : ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ (@set.univ ℝ), from by {
    intros m hm,
    exact mem_univ _,
  },
  have h21 : ∀ n : ℕ, (int.fract (α * ↑n)) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℕ), from by {
    intros n,
    rw mem_image,
    use n,
    split,
    {
      exact set.mem_univ _,
   
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
    have h : ∀ i j : ℤ, (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)) ↔ (i ≠ j),
    {
      intros i j,
      split,
      {
          assume h1,
          assume h2 : i = j,
          rw [h2] at h1,
          rw int.fract_mul at h1,
          rw int.fract_mul at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          have h3 : (α * ↑i) - (int.floor (α * ↑i)) = (α * ↑i) - (int.floor (α * ↑i)), 
          simp,
          rw h3 at h1,
          rw sub_eq_add_neg at h1,
          have h4 : (-(int.ceil (α * ↑i)) : ℤ) = (int.floor (α * ↑i)) - (α * ↑i),
          rw int.ceil_eq_int_floor_add_one,
          linarith,
          rw h4 at h1,
          have h5 : (1 : ℤ) = -(int.ceil (α * ↑i) - (α * ↑i)) + (α * ↑i - int.floor (α * ↑i)),
          linarith,
          rw h5 at h1,
          rw ← sub_eq_add_neg at h1,
          rw ← neg_add at h1,
          rw ← neg_neg at h1,
          rw ← int.fract_neg_add_one at h1,
          rw ← int.fract_neg_add_one at h1,
          have h6 : α = int.fract (α),
          rw int.fract_mk,
          linarith,
          rw h6 at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          rw add_zero int.fract at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          have h7 : (0 : ℤ) = int.floor (α) + int.fract (α),
          rw int.fract_mk,
          linarith,
          rw h7 at h1,
          have h8 : (0 : ℤ) = int.floor (α) + int.fract (α),
          rw int.fract_mk,
          linarith,
          rw h8 at h1,
          rw add_zero int.fract at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          have h9 : α = int.fract α,
          rw int.fract_mk,
          linarith,
          rw h9 at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          rw int.fract_mk at h1,
          have h10 : ((int.ceil (α * ↑i)) : ℤ) = int.ceil (α * ↑i),
          refl,
          have h11 : (((0 : ℕ)≥int.ceil (α * ↑i)-(α * ↑i)) : ℤ) = (0 ≥ int.ceil (α * ↑i)-(α * ↑i)),
          refl,
          rw h11 at h1,
          have h12 := α_irrational hα_irrat (int.ceil (α * ↑i)),
          rw add_zero int.fract at h12,
          rw add_assoc int.fract at h12,
          rw ← nat.add_sub_cancel (int.floor (α * ↑i)) int.fract at h12,
          rw add_zero at h12,
          rw int.ceil_eq_int_floor_add_one at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw int.fract_mk at h12,
          rw add_zero int.fract at h12,
          rw add_comm int.fract at h12,
          rw ← add_assoc int.fract at h12,
          rw ← add_assoc int.fract at h12,
          rw ← neg_add_rev at h12,
          rw ← add_assoc int.fract at h12,
          show (1 : ℝ) ≠ 0,
          rw [h1,h9,h8,h7,h6,h5,h4,h3,h2],
          linarith,
      },
      {
          intro h1,
          linarith,
      },
    },
    have h2 : ∀ i j : ℤ, (i ≠ j) ↔ (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)),
    {
      intros i j,
      split,
      {
          assume h3,
          assume h4 : i = j,
          rw h4 at h3,
          rw int.fract_mul at h3,
          rw int.fract_mul at h3,
          rw int.fract_mk at h3,
          rw int.fract_mk at h3,
          have h5 : (α * ↑i) - (int.floor (α * ↑i)) = (α * ↑i) - (int.floor (α * ↑i)), 
          simp,
          rw h5 at h3,
          rw sub_eq_add_neg at h3,
          have h6 : (-(int.ceil (α * ↑i)) : ℤ) = (int.floor (α * ↑i)) - (α * ↑i),
          rw int.ceil_eq_int_floor_add_one,
          linarith,
          rw h6 at h3,
          have h7 : (1 : ℤ) = -(int.ceil (α * ↑i) - (α * ↑i)) + (α * ↑i - int.floor (α * ↑i)),
          linarith,
          rw h7 at h3,
          rw ← sub_eq_add_neg at h3,
          rw ← neg_add at h3,
          rw ← neg_neg at h3,
          rw ← int.fract_neg_add_one at h3,
          rw ← int.fract_neg_add_one at h3,
          have h8 : α = int.fract (α),
         
end --Needs more than 2000 tokens!

--OUTPUT 10
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- "Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$."
  have h1 : ∀ (i j : ℤ) (h_distinct : i ≠ j), (int.fract (α * i) : ℝ) ≠ (int.fract (α * j)), from by {
    assume (i j : ℤ) (h_distinct : i ≠ j),
    -- "If this were not true, then"
    assume h2 : (int.fract (α * i)) = (int.fract (α * j)),
    -- then $i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor$
    have h3 : (α * ↑i - (α * ↑i).floor) = (int.fract (α * i)) ∧ (int.fract (α * j)) = (α * ↑j - (α * ↑j).floor), from by {
      split,
      rw h2,
      obviously,
    },
    -- then $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$
    have h4 :  α = ((α * ↑i).floor - (α * ↑j).floor) / (i - j), from by linarith,
    -- which is a contradiction of the irrationality of $\alpha$ 
    rw h4,
    have h5 : (irrational α) ↔ (∀ (x : ℚ), x ≠ α), from by {apply irrational_iff_eq_zero_of_mul_eq_zero},
    have h6 :  ∀ (x : ℚ), x ≠ α, from by {apply h5, assumption}, 
    have h7 :  (i - j) ≠ 0, from by {assumption},
    have h8 :  (i - j) ≠ 0, from by {assumption},
    rw h6,
    exact rat.denom_ne_zero _ h8,
  },

  -- Hence, $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$ is an infinite subset of $\left[0,1\right]$
  have h2 : is_infinite ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    -- "By the Bolzano-Weierstrass theorem"
    apply is_infinite_of_no_finite_limit_points,
    -- "Then"
    have h3 :  ∀ (f : ℤ → ℂ), ∀ (l : ℂ), tendsto f at_top (𝓝 l) ↔ 
      ∀ (ε > 0), ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |f (n : ℤ) - l| < ε, 
    from by {apply tendsto_at_top_iff_nat},
    
    -- $S$ has a limit point in $[0, 1]$
    apply not_forall.mpr,
    assume h4 : ∀ (l : ℝ), ¬ is_limit_point (λ m : ℤ, int.fract (α * ↑m)) l,

    -- "One can thus find pairs of elements of $S$ that are arbitrarily close"
    -- Hence for a given $\epsilon > 0$ there exists a finite set $F \subseteq S$ such that $|y - x| < \epsilon$
    -- for every $(x, y) \in F \times F$
    have h5 : ∀ (ε > 0), ∃ (F : set ℝ) (n : ℕ), finite F ∧ F ⊆ insert 0 1 ∧ ((λ m : ℤ, int.fract (α * ↑m)) '' (finset.range n)) ⊆ F ∧ 
      ∀ (x : ℝ), x ∈ F → ∃ (y : ℝ), y ∈ F ∧ |x - y| < ε,
    from by {
      assume h5 : ε > 0,
      have h6 : ∀ (l : ℝ), l ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (finset.range n)) → l ∈ 
        insert 0 1,
      from by {
        assume (l : ℝ),
        assume h6 : l ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)),
        obtain ⟨n, h7⟩ := h6,
        have h8 : ((λ m : ℤ, int.fract (α * ↑m)) '' (finset.range n)) ⊆ (@set.univ ℤ), from by 
          {apply set.image_subset_iff, apply finset.range_subset,},
        have h9 : l ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (finset.range n)) := by {exact set.mem_of_mem_closure h6,},
        have h10 : l ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
          rw h8 at h9, exact h9,
        },
        have h11 : ∀ (m : ℤ), m ∈ (@set.univ ℤ) → l ∈ (λ (m : ℤ), int.fract (α * m)) '' (@set.univ ℤ), from 
          by {assumption,},
        obtain ⟨m, h12, h13⟩ : ∃ (m : ℤ), m ∈ (@set.univ ℤ) ∧ l ∈ (λ (m : ℤ), int.fract (α * m)) '' (@set.univ ℤ), 
        from by {apply h11, exact h10},
        subst h13,
        -- We want to show that $\forall \epsilon > 0, \exists N : \mathbb{N}, |y - x| < \epsilon$
        -- But this follows from the fact that $x \in S$
        -- 
        have h14 : ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |int.fract (α * m) - int.fract (α * ↑n)| < ε, from by
          {apply h4, exact h3.right,},
        cases h14 with N h15,
        let F := (finset.range N).image (λ m : ℕ, int.fract (α * ↑m)),
        use F,
        use N,
        split,
        exact finset.finite_range N,
        split,
        apply set.image_subset,
        exact h7,
        intros m h,
        have h16 : m ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {exact set.mem_of_mem_closure h,},
        have h17 : m ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' finset.range N), from by {
          rw set.image_subset_iff at h7,
          obtain ⟨m0, h18, h19⟩ := h7 h16,
          use m0,
          split,
          exact h18, exact h19,
        },
        rw h7 at h17,
        have h20 : ∀ (m : ℤ), m ∈ finset.range N → 
          l ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' finset.range N, from by {assumption,},
        obtain
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
