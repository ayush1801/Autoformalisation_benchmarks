import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let S := (λ (m : ℤ), @int.fract ℝ _ (α * m)) '' (@set.univ ℤ),
  have h1 : ∀ m n : ℤ, (m ≠ n) → (int.fract (α * m) ≠ int.fract (α * n)), from assume m n, assume hmn,
    by {
      assume heq : (int.fract (α * m)) = int.fract (α * n),
      have h2 : ∃ (q : ℤ), ↑m*α = int.fract (m*α) + q, from by {
        apply int.of_rat_add_one,
      },
      have h3 : ∃ (q : ℤ), ↑n*α = int.fract (n*α) + q, from by {
        apply int.of_rat_add_one,
      },
      have h4 : ↑m*α = ↑n*α, from by {
        rw heq,
        rw int.fract_eq_of_lt,
        apply int.coe_nat_pos,
      },
      have h5 : ∃ a : ℤ, ↑m*α = a, from ⟨by exact int.fract (m*α),by exact h2.right⟩,
      have h6 : ∃ a : ℤ, ↑n*α = a, from ⟨by exact int.fract (n*α),by exact h3.right⟩,
      exact hα_irrat (int.eq_of_mul_eq_mul_right ((h5.left - h6.left)/(↑m-↑n)) zero_lt_one),
    },
  have hS_inf : ∃ m : ℤ, m ∈ S, from ⟨0, by exact set.mem_univ 0⟩,
  have hS_limpt : ∃ z : ℝ, z ∈ ↥S ∧ z ∈ S, from by {
    have h1 : set.Ico (0 : ℝ) 1 ⊆ ↥S, from by {apply set.inter_subset_right, apply set.image_subset_iff.2, apply set.mem_univ,},
    have h2 : ∃ z : ℝ, z ∈ set.Ico 0 1, from @is_compact_real.exists_mem_inter_Ico (0 : ℝ) 1,
    exact ⟨h2.w, by {split, apply set.mem_closure_iff.2, exact ⟨z, by {apply h1,exact h2.h}⟩, apply set.mem_univ, exact h2.h}⟩,
  },

  have hS_dense : ∀ y ∈ set.Ico 0 1, ∀ ε > 0, ∃ x ∈ S, abs(x-y) < ε, from assume y hy, assume ε hε,
    by {
      have h1 : ∃ z ∈ S, ∀ x ∈ S, abs(x-z) < ε, from by exact set.finite_complete (λ x, abs(x-y) < ε) hS_inf,
      exact ⟨h1.w, by exact h1.h.left, by {rcases h1.h.right m with ⟨_,_,h_abs⟩, have key := h_abs, show abs(m-y) < ε, from key, show m ∈ S, from set.mem_image_of_mem _ hS_limpt.h.right.left }}
  },
  show closure S = set.Icc 0 1, from le_antisymm
    (by exact ⟨set.inter_subset_left _ _, set.inter_subset_right _ _, hS_dense⟩)
    (by apply set.closure_minimal, from ⟨set.mem_set_of_eq (by {rw ← int.fract_zero, rw ← int.fract_one, rw ← int.fract_add, rw ← int.fract_mul, rw int.mul_assoc, rw int.coe_nat_mul, norm_num, rw ← int.fract_add, rw ← int.fract_add, rw ← int.fract_mul, rw ← int.fract_mul, rw int.mul_assoc, rw int.mul_assoc, rw int.coe_nat_mul, norm_num, rw int.mul_comm, rw int.fract_add, rw int.fract_of_nat_of_nonneg, simp, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw ← int.fract_add, rw ← int.fract_add, rw ← int.fract_mul, rw int.mul_assoc, rw int.mul_comm, rw int.coe_nat_mul, norm_num, rw int.mul_assoc, rw int.mul_assoc, rw int.coe_nat_mul, norm_num, rw int.mul_comm, rw int.fract_add, rw int.fract_of_nat_of_nonneg, simp, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw ← int.fract_add, rw ← int.fract_add, rw ← int.fract_mul, rw int.mul_assoc, rw int.mul_comm, rw int.coe_nat_mul, norm_num, rw int.mul_assoc, rw int.mul_comm, rw int.coe_nat_mul, norm_num, rw int.fract_mul, rw int.fract_of_nat_of_nonneg, simp, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw ← int.fract_add, rw ← int.fract_add, rw ← int.fract_mul, rw int.mul_assoc, rw int.mul_comm, rw int.coe_nat_mul, norm_num, rw int.mul_comm, rw int.fract_mul, rw int.fract_of_nat_of_nonneg, simp, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.mul_comm, rw int.mul_comm, rw ← int.fract_add, rw ← int.fract_add, rw ← int.fract_mul, rw int.mul_assoc, rw int.coe_nat_mul, norm_num, rw int.mul_comm, rw int.fract_mul, rw int.fract_of_nat_of_nonneg, simp, norm_num, rw int.mul_comm, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.coe_nat_add, norm_num, rw int.mul_comm, rw int.mul_comm, rw ← int.fract_add, rw ← int
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin

  have h0 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)), from 
    assume i j : ℤ, assume h : i ≠ j, assume h' : int.fract (α * ↑i) = int.fract (α * ↑j),
    have hirrat : irrational α, from hα_irrat,
    have hmul : i * α ≠ j * α, from by {rw ← int.fract_eq at h',assumption},
    have hit : ∃ intΦ : ℤ, i * α - intΦ ∈ ℤ, from by {use int.floor (i * α), apply int.fract_eq},
    have hjt : ∃ intΨ : ℤ, j * α - intΨ ∈ ℤ, from by {use int.floor (j * α), apply int.fract_eq},
    have h1 : int.fract (i * α) = int.fract (j * α), from by {rw [← int.fract_eq,h']},
    have hα : α = (int.floor (i * α) - int.floor (j * α))/(i - j), from by {rw [int.fract_eq,int.fract_eq,int.fract_eq,int.fract_eq,int.fract_eq,int.fract_eq,h1]},
    have hα_rat : α ∈ ℚ, from 
      by {have hα_ne : i - j ≠ 0, from mt int.eq_zero_of_mul_eq_mul_left hmul, 
        have hα_ne' : i - j ≠ 0, from mt int.eq_zero_of_mul_eq_mul_right (int.mul_right_inj hα_ne),
        have hα_div : (int.floor (i * α) - int.floor (j * α))/(i - j) ∈ ℚ, from int.div_in_rat _ hα_ne',
        assumption,
      },
    have hirrat_rat : irrational α → ¬α ∈ ℚ, from by {assume hirrat, assume hα_rat, assumption},
    show false, from hirrat_rat hirrat hα_rat,
  have h1 : ∀ i j : ℤ, (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (i ≠ j), from 
    assume i j : ℤ, assume h : (int.fract (α * ↑i) ≠ int.fract (α * ↑j)), 
    have hcontr : i = j → int.fract (α * ↑i) = int.fract (α * ↑j), from 
      (assume h' : i = j, by {rw [h',h']}),
    have hirrat : irrational α, from hα_irrat,
    have hmul : (α * ↑i) ≠ (α * ↑j), from mt int.eq_of_fract_eq_fract h, 
    have hit : ∃ intΦ : ℤ, i * α - intΦ ∈ ℤ, from by {use int.floor (i * α), apply int.fract_eq},
    have hjt : ∃ intΨ : ℤ, j * α - intΨ ∈ ℤ, from by {use int.floor (j * α), apply int.fract_eq},
    have h1 : int.fract ((α * ↑i) - (α * ↑j)) = 0, from by {rw [(hit).right], rw [(hjt).right], ring},
    show i ≠ j, from mt int.eq_of_mul_eq_mul_left h,
  have h2 : ∀ i j : ℤ, (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) ↔ (i ≠ j), from 
    assume i j : ℤ, ⟨h1 i j, h0 i j⟩,
  have h3 : ∀ i j : ℤ, (∃ i' j' : ℤ, (i ≠ j') ∧ (j ≠ i') ∧ abs (int.fract (α * ↑j') - int.fract (α * ↑i')) < abs (int.fract (α * ↑i) - int.fract (α * ↑j))), from 
    assume i j : ℤ, ⟨⟨i, j, by {simp [h2 i j]}⟩, ⟨i, j, by {simp [h2 i j]}⟩, 
      by {rw abs_of_pos,apply int.fract_pos}⟩,
  have h4 : ∀ y : ℝ, ∃ y' : ℝ, (((∃ i' j' : ℤ, (i' ≠ j') ∧ (int.fract (α * ↑i') ≠ int.fract (α * ↑j')) ∧ abs (int.fract (α * ↑j') - int.fract (α * ↑i')) < abs (int.fract (α * ↑i') - y))) ∧ (y < y') ∧ (y' < int.fract (α * ↑(i' + 1)))), from 
    assume y : ℝ,
    by {use int.fract (α * ↑(i + 1)),
      show (∃ (i' j' : ℤ), i' ≠ j' ∧ int.fract (α * ↑i') ≠ int.fract (α * ↑j') ∧ abs (int.fract (α * ↑j') - int.fract (α * ↑i')) < abs (int.fract (α * ↑i') - y)) ∧ y < int.fract (α * ↑(i + 1)) ∧ int.fract (α * ↑(i + 1)) < int.fract (α * ↑(i + 1)), from
      by {split, split,
        show ∃ (i' j' : ℤ), i' ≠ j' ∧ int.fract (α * ↑i') ≠ int.fract (α * ↑j') ∧ abs (int.fract (α * ↑j') - int.fract (α * ↑i')) < abs (int.fract (α * ↑i') - y), from
          by {use i, use i, split, simp, split, simp, 
          rw abs_of_pos, apply int.fract_pos},
        show y < int.fract (α * ↑(i + 1)), from by {rw ← int.fract_eq, apply int.add_fract_lt_one,},
        show int.fract (α * ↑(i + 1)) < int.fract (α * ↑(i + 1)), from by {rw ← int.fract_eq, apply int.add_fract_lt_one,},
       },
    },
  have h5 : ∀ x : ℝ, x ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) → x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from 
    assume x : ℝ, assume hx : x ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)),
    have hx' : ∃ n : ℤ, x = int.fract (α * ↑n), from hx,
    have hx'' : ∃ n : ℤ, ∃ i j : ℤ, (i ≠ j) ∧ (int.fract (α * ↑i) = x) ∧ (int.fract (α * ↑j) = int.fract (α * ↑n)), from 
      by {use (hx').fst, use (hx').fst, use (hx').fst
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let S : (set ℝ) := set.range (λ m : ℤ, int.fract (α * ↑m)),
  have hnonempty : S ≠ ∅, -- by using m=0 we have α*0 = 0, hence {0} is in S
  from begin
    assume h : S = ∅,
    have h1 : (0 : ℤ) ∉ set.univ, from by {
      intro h2,
      have h3 : (0 : ℝ) ∈ S, from by {unfold S,exact set.mem_range.mpr ⟨0,rfl⟩},
      exact set.eq_empty_iff_forall_not_mem.mp h h3,
    },
    show false, from h1 trivial,
  end,

  have h_inf : infinite S, -- using the fact that α is irrational and def of irrational,
  -- we have {iα} ≠ {jα} if i≠j. Since det(iα) ∉ S and S is nonempty, it follows S is infinite
  from begin
    assume h : finite S,
    have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), 
    from begin
      assume i j : ℤ,
      assume hneq : i ≠ j,

      assume h1 : (int.fract (α * ↑i)) = (int.fract (α * ↑j)),
      have h2 : (int.fract (α * ↑i)) = ((int.fract (α * ↑i)) - (int.fract (α * ↑i)) + (int.fract (α * ↑i))) 
      ∧ (int.fract (α * ↑j)) = ((int.fract (α * ↑j)) - (int.fract (α * ↑j)) + (int.fract (α * ↑j))) ↔ true, from by {split;assumption,},
      have h3 : ((int.fract (α * ↑i)) - (int.fract (α * ↑i))) + (int.fract (α * ↑i)) = ((int.fract (α * ↑j)) - (int.fract (α * ↑j))) + (int.fract (α * ↑j))
      ∧ ((int.fract (α * ↑j)) - (int.fract (α * ↑j))) + (int.fract (α * ↑j)) = ((int.fract (α * ↑i)) - (int.fract (α * ↑i))) + (int.fract (α * ↑i)) ↔ true, from by {split;assumption,},
      have h4 : ∀ x y : ℝ, x = y → (int.fract x) = (int.fract y), 
      from begin
        assume x y : ℝ,
        assume hxy : x = y,
        rw ← hxy,
      end,
      have h5 : (int.fract (α * ↑i)) = (int.fract (α * ↑j)), from eq.trans (h4 (α*↑i) (α*↑j) (congr_arg int.fract h1)) (eq.symm (h4 (α*↑j) (α*↑i) (congr_arg int.fract (eq.symm h1)))),
      have h6 : (int.fract (α * ↑i)) = (α* ↑i - int.nat_abs (α* ↑i)) ∧ (int.fract (α * ↑j)) = (α* ↑j - int.nat_abs (α* ↑j)) ↔ true, from by {split;assumption,},
      have h7 : ∀ x : ℝ, x - int.nat_abs x = (int.fract x), 
      from begin
        assume x : ℝ,
        rw int.fract_def,
      end,
      have h8 : ∀ x : ℝ, (int.fract x) = (x - int.nat_abs x), from 
        by {assume x : ℝ, rw ← (h7 x),ring},
      have h9 : (α*↑i - int.nat_abs (α * ↑i)) = (α* ↑j - int.nat_abs (α * ↑j)),
      from eq.trans (h8 (α*↑i)) (eq.trans h5 (eq.symm (h8 (α*↑j)))),
      have h10 : ∀ x y : ℝ, x = y → (int.nat_abs x) = (int.nat_abs y), from begin
        assume x y : ℝ,
        assume hx : x = y,
        rw ← hx,
      end,
      have h11 : (int.nat_abs (α * ↑i)) = (int.nat_abs (α * ↑j)), from 
        eq.trans (h10 (α*↑i) (α*↑j) (eq.symm h9)) (eq.symm (h10 (α*↑j) (α*↑i) h9)),
      have h12 : (int.nat_abs (α * ↑i)) = (int.nat_abs (int.fract (α* ↑i))) ∧ (int.nat_abs (α * ↑j)) = (int.nat_abs (int.fract (α * ↑j))) ↔ true, from by {split;assumption,},
      have h13 : (int.nat_abs (int.fract (α * ↑i))) = (int.nat_abs (int.fract (α * ↑j))) ↔ true, from by {rw ← h12,ring,}, 
      have h14 : (abs (int.fract (α * ↑i))) = (abs (int.fract (α * ↑j))) ↔ true, from by {rw h13,ring,},
      have h15 : ∀ x : ℝ, (abs (int.fract x)) = (int.nat_abs (int.fract x)), from 
        by {assume x : ℝ, rw ← int.nat_abs_of_nonneg (int.fract_nonneg x),rw abs_of_nonneg,},
      have h16 : (abs (int.fract (α * ↑i))) = (abs (int.fract (α * ↑j))) ↔ true, from by {rw (h15 (α * ↑i)),rw (h15 (α * ↑j)),ring},
      have h17 : abs (int.fract (α * ↑i)) = abs (int.fract (α * ↑j)), from 
        eq.trans (eq.symm h16) h14,
      have h18 : (abs (int.fract (α * ↑i))) = (int.nat_abs (α * ↑i)) ∧ (abs (int.fract (α * ↑j))) = (int.nat_abs (α * ↑j)) ↔ true, from by {rw h12,ring,},
      have h19 : (int.nat_abs (α * ↑i)) = (int.nat_abs (α * ↑j)) ↔ true, from by {rw ← h18,ring,},
      have h20 : (↥(α * ↑i)) ≠ 0 ∧ (↥(α * ↑j)) ≠ 0 ↔ true, from by {split;assumption,},
      have h21 : (abs (int.fract (α * ↑i))) ≠ 0 ∧ (abs (int.fract (α * ↑j))) ≠ 0 ↔ true, from by {rw h18,rw h20,}, 
      have h22 : (abs (int.fract (α * ↑i))) ≠ 0 ∧ (int.nat_abs (α * ↑i)) = (int.nat_abs (α * ↑j)) ↔ true, from by { rw h12,split;assumption,},
      have h23 : (abs (int.fract (α * ↑i))) ≠ 0 ∧ (int.fract (α * ↑i)) = (int.fract (α * ↑j)) ↔ true, from by {rw ← h12,ring,},
      have h24 : (int.fract (α
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
apply le_antisymm,

{
  -- show left-to-right
  assume y : ℝ,
  assume hy : y ∈ closure ((λ (m : int), int.fract (α * ↑m)) '' univ),
  show y ∈ set.Icc 0 1,
  have hy2 : y ∈ closure (set.range (λ (m : int), int.fract (α * ↑m))), from hy,
  have hy3 : y ∈ closure (set.Icc 0 1), from set.subset.trans hy2 (set.subset_closure_Icc_Ico),
  rw closure_eq_of_is_closed (is_closed_Icc 0 1) at hy3,
  assumption,
},

{
  -- show right-to-left
  assume y : ℝ,
  assume hy : y ∈ set.Icc 0 1,
  show y ∈ closure ((λ (m : int), int.fract (α * ↑m)) '' univ),
  from closure_mono (set.subset_univ (λ (m : int), int.fract (α * ↑m))) hy,
},


end

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  sorry,
end

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have f : ∀ i : ℤ, ∃ j : ℤ, abs (i - j) ≤ 1, begin
    assume (i : ℤ),
    have h : 0 < abs i, begin
      assume h,
      have : 0 < 0, begin
        rw h,
      end,
      exact dec_trivial this,
    end,
    have : 0 ≤ abs i, begin
      rw abs_of_nonneg,
      apply_instance,
    end,
    have h2 : 0 < 1, begin
      norm_num,
    end,
    have h3 : 1 ≤ abs i, begin
      exact le_of_lt (lt_of_lt_of_le h2 h),
    end,
    have h4 : i ≤ abs i, begin 
      rw ← nat_int.coe_nat_add,
      calc i + -i ≤ abs i + -i : by apply add_le_add_right
      ... = abs i : by {rw ← abs_neg, rw sub_eq_add_neg, refl,},
    end,
    have h5 : abs i ≤ 1 + i, begin
      apply le_of_lt,
      apply lt_add_of_le_of_pos' h h2,
      apply le_of_sqr_le_sqr,
      rw abs_of_nonneg,
      simp,
    end,
    use (-i),
    split,
    apply le_trans h4 h5,
    exact (show 1 + -i ≤ 1 + i, from by {rw <- sub_eq_add_neg, norm_num}),
  end,

  have f2 : ∀ i j : ℤ, abs (i - j) ≤ 1 → abs (int.fract i - int.fract j) ≤ 1, begin
    assume (i j : ℤ) (h : abs (i - j) ≤ 1),
    by_cases h₁ : i = j,
      rw h₁,
      norm_num,
    have h₂ : abs (i - j) ≠ 0,
      assume h₃ : abs (i - j) = 0,
      rw h₃ at h,
      have h₄ : 0 < 0,
        exact h,
      exact dec_trivial h₄,
    have h₅ : 1 ∣ abs (i - j),
      apply dvd_of_abs_mul_abs_le_one,
      norm_num,
    rw @abs_int_fract i j (h₂) at h₅,
    rw ← int.coe_nat_dvd at h₅,
    have h₆ : 1 ∣ (i - j),
      rw abs_mul at h₅,
      rwa mul_one at h₅,
    rw dvd_iff_mod_eq_zero at h₆,
    rw int.mod_eq_of_lt (int.mod_lt i) at h₆,
    rw int.mod_eq_of_lt (int.mod_lt j) at h₆,
    rw int.sub_mod at h₆,
    rw add_assoc (-i) i at h₆,
    rw add_right_neg i at h₆,
    rw @add_comm _ (-j) at h₆,
    rw add_assoc (-j) j at h₆,
    rw add_right_neg j at h₆,
    rw ← int.sub_mod at h₆,
    rw ← add_assoc (-i) (int.mod j) at h₆,
    rw add_right_neg i at h₆,
    rw add_assoc (-j) (int.mod i) at h₆,
    rw add_right_neg j at h₆,
    have h₇ : -i + int.mod j = -j + int.mod i,
      rwa (show -i + int.mod j + i + j = -j + int.mod i + i + j, by ring),
    rw ← h₇ at h₆,
    rw @int.sub_mod _ _ (int.mod_lt i) at h₆,
    rw @int.sub_mod _ _ (int.mod_lt j) at h₆,
    rw int.sub_self at h₆,
    rw int.sub_self at h₆,
    rw h₆,
    norm_num,
  end,

  have f3 : ∀ x y : ℤ, abs (x - y) ≤ 1 → abs (int.fract x - int.fract y) ≤ 1 → 
    abs (int.fract x - int.fract y) ≤ abs (x - y), begin
      assume x y h₁ h₂,
      apply le_trans h₂,
      exact h₁,
    end,
  have f4 : ∀ x y z : ℤ, abs (x - y) ≤ 1 → abs (int.fract x - int.fract y) ≤ 1 → 
    abs (int.fract x - int.fract y) ≤ abs (z - y), begin
      assume x y z h₁ h₂,
      have h₃ : abs (x - y) ≤ abs (z - y), begin
        apply le_trans h₁,
        apply abs_abs_sub_abs_sub_le,
      end,
      apply le_trans h₂,
      exact h₃,
    end,

  have f5 : ∀ i j k : ℤ, abs (i - j) ≤ 1 → abs (int.fract i - int.fract j) ≤ 1 → 
    0 < abs (int.fract i - int.fract j) → 0 < abs (k - j), begin
    assume i j k H₁ H₂ H₃,
    have H₄ : abs (int.fract i - int.fract j) = abs (k - j), begin
      apply eq.trans,
      rw ← abs_sub,
      rw ← abs_sub,
      exact abs_sub_of_abs_abs_sub_abs_sub_le (f3 i j k H₁ H₂),
      exact abs_sub_of_abs_abs_sub_abs_sub_le (f4 i j k H₁ H₂),
    end,
    rw ← H₄ at H₃,
    exact H₃,
  end,

  have f6 : ∀ i j k : ℤ, abs (i - j) ≤ 1 → abs (int.fract i - int.fract j) ≤ 1 → 
    0 < abs (int.fract i - int.fract j) → 0 < abs (k - i), begin
    assume i j k H₁ H₂ H₃,
    rw add_comm at H₁,
    rw add_comm at H₂,
    rw ← sub_eq_add_neg at H₃,
    have H₄ : 0 < abs (int.fract k - int.fract j),
      rw ← abs_neg,
      exact H₃,
    apply f5 k i j H₁ H₂ H₄,
  end,

  have f7 : ∀ (i j : ℤ), abs (i - j) ≤ 1 → abs (int.fract i - int.fract j) ≤ 1 → 
    int.fract i = int.fract j, begin
    assume i j H₁ H₂,
    cases le_or_gt 0 (int.fract i - int.fract j) with H₃ H₄,
      have H₅ : int.fract i - int.fract j < 0,
        rwa not_lt at H₄,

end --Needs more than 2000 tokens!

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := 
begin
  have h1 : ∀ m n : ℤ, m < n → α * ↑m - (floor (α * ↑m)) ≤ α * ↑n - (floor (α * ↑n)), from by {
    assume (m n : ℤ) (h : m < n),
    have h1 : (α * ↑m) < (α * ↑n), from mul_lt_mul_of_pos_left h (by norm_num),
    apply (floor_mono h1),
  },
  have h2 : ∀ m n : ℤ, m < n → (floor (α * ↑m)) - (floor (α * ↑n)) ≤ 0, from by {
    assume (m n : ℤ) (h : m < n), 
    have h1 : (α * ↑m) < (α * ↑n), from mul_lt_mul_of_pos_left h (by norm_num),
    have h2 : (floor (α * ↑n)) ≤ (floor (α * ↑m)), from floor_mono h1,
    apply nat.sub_le_self h2,
  },
  have h3 : ∀ m n : ℤ, m < n → (α * ↑n) - (α * ↑m) = (floor (α * ↑n)) - (floor (α * ↑m)), from by {
    assume (m n : ℤ) (h : m < n), 
    have h1 : (α * ↑m) < (α * ↑n), from mul_lt_mul_of_pos_left h (by norm_num),
    have h2 : (α * ↑m) - (floor (α * ↑m)) ≤ (α * ↑n) - (floor (α * ↑n)), from h1 ▸ h1,
    have h3 : (α * ↑n) - (floor (α * ↑n)) - ((α * ↑m) - (floor (α * ↑m))) = (floor (α * ↑n)) - (floor (α * ↑m)), from by 
      {repeat{rw ← sub_eq_iff_eq_add}, rw ← fractional_part_eq, rw ← fractional_part_eq},
    have h4 : (α * ↑n) - (floor (α * ↑n)) - ((α * ↑m) - (floor (α * ↑m))) - ((floor (α * ↑n)) - (floor (α * ↑m))) = 0, from by 
      {ring},
    apply eq_zero_of_sub_eq_zero h4,
  },
  have h4 : ∀ m n : ℤ, m < n → 0 < (α * ↑n) - (α * ↑m), from by {
    assume (m n : ℤ) (h : m < n), 
    have h1 : (α * ↑m) < (α * ↑n), from mul_lt_mul_of_pos_left h (by norm_num),
    have h2 : (floor (α * ↑n)) ≤ (floor (α * ↑m)), from floor_mono h1,
    have h3 : (α * ↑n) - (floor (α * ↑n)) - ((α * ↑m) - (floor (α * ↑m))) = (floor (α * ↑n)) - (floor (α * ↑m)), from by 
      {repeat{rw ← sub_eq_iff_eq_add}, rw ← fractional_part_eq, rw ← fractional_part_eq},
    have h4 : (α * ↑n) - (floor (α * ↑n)) - ((α * ↑m) - (floor (α * ↑m))) - ((floor (α * ↑n)) - (floor (α * ↑m))) = 0, from by 
      {ring},
    have h5 : (α * ↑n) - (floor (α * ↑n)) - ((α * ↑m) - (floor (α * ↑m))) = ((floor (α * ↑n)) - (floor (α * ↑m))), from by
      {rw ← eq_zero_of_sub_eq_zero h4,},
    have h6 : (α * ↑n) - (α * ↑m) = ((floor (α * ↑n)) - (floor (α * ↑m))), from by
      {rw h3 at h5, rw h5,},
    have h7 : 0 < (α * ↑n) - (α * ↑m), from by
      {rw ← sub_pos (h2 ▸ rfl) at h6, rw h6, rw int.coe_nat_lt_coe_nat_iff, norm_num,},
    exact h7,
  },
  have h5 : ∀ m n : ℤ, m < n →  (floor (α * ↑m)) - (floor (α * ↑n)) < m - n, from by {
    assume (m n : ℤ) (h : m < n),
    have h1 : 0 < (α * ↑n) - (α * ↑m), from h ▸ h4,
    have h2 : (α * ↑n) - (α * ↑m) = (floor (α * ↑n)) - (floor (α * ↑m)), from h ▸ h3,
    have h3 : 0 < (floor (α * ↑n)) - (floor (α * ↑m)), from by 
      {rw ← sub_pos rfl at h1, rw h2 at h1, rw ← int.coe_nat_lt_coe_nat_iff at h1, norm_num,}, 
    have h4 : 0 ≤ (floor (α * ↑n)) - (floor (α * ↑m)) - (m - n), from by
      {rw ← int.coe_nat_le_coe_nat_iff, have h5 : (floor (α * ↑n)) - (floor (α * ↑m)) ∈ ℕ, from by 
        exact int.coe_nat_sub_coe_nat_of_le (h2 ▸ h1), have h6 : m - n ∈ ℕ, from by
        norm_num, norm_num,},
    have h5 : 0 < m - n + ((floor (α * ↑n)) - (floor (α * ↑m)) - (m - n)), from by
      {rw int.coe_nat_lt_coe_nat_iff, rw nat.add_sub_of_le h4, norm_num,},
    show (floor (α * ↑m)) - (floor (α * ↑n)) < m - n, from by {rw ← h2, rw ← sub_pos rfl at h5, rw h5,},
  },
  have h6 : ∀ m n : ℤ, m < n → abs ((floor (α * ↑m)) - (floor (α * ↑n))) < abs (m - n), from by {
    assume (m n : ℤ) (h : m < n),
    have h1 : (floor (α * ↑m)) - (floor (α * ↑n)) < m - n, from h ▸ h5,
    have h2 : abs ((floor (α * ↑m)) - (floor (α * ↑n))) < abs (m - n), from by {
      rw abs_lt_iff, split, exact h1, split,
      {rw nat.sub_lt_iff_lt_add',split,
      norm_num, rw abs_pos_iff, exact h1,},
      {exact nat.sub_nonneg (floor (α * ↑n)) (floor (α * ↑m)),},
    },
    exact h2,
  },
  have h7 : ∀ m n : ℤ, m < n → abs (α * ↑m - (floor (α * ↑m))) < abs (m - n), from by {
    assume (m n : ℤ) (h : m < n),
    have h1 : α * ↑m - (floor (α * ↑m)) ≤ α * ↑n - (floor (α * ↑n)), from h ▸ h1,
    have h2 : (floor (α * ↑m)) - (floor (α * ↑n)) < m - n, from h ▸ h5,
    have h3 : abs ((floor (α * ↑m)) - (floor (α * ↑n))) < abs (m - n), from h ▸ h6,
    have h
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j : ℤ,
    assume h_distinct : i ≠ j,
    have h_fract_ne : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume h_eq : int.fract (α * ↑i) = int.fract (α * ↑j),
      calc α = α*i-(α*↑i-int.fract (α*↑i)) : by {rw sub_eq_add_neg,ring}
      ... = α*(i-j)-(α*↑i-int.fract (α*↑i)) : by rw [h_eq,mul_add,mul_one]
      ... = α*(i-j)-(α*(i-j)) : by rw [← sub_eq_add_neg,← sub_eq_add_neg,mul_comm (i-j) α]
      ... = 0 : by ring, 
      },
    exact h_fract_ne,
    },
  have h2 : ∀ i j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j : ℤ,
    by_cases h_eq : i = j,
    from by simp [h2],
    from by {exact h1 i j h_eq },
    },
  have h3 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = ⋃ i : ℤ, {int.fract (α * ↑i)}, from
    by {
      have h_mem : ∀ i : ℤ, int.fract (α * ↑i) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
        assume i : ℤ,
        have h_m : m ∈ (@set.univ ℤ), from set.mem_univ i,
        show int.fract (α * ↑i) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by
          {
            apply set.mem_image_of_mem i, exact h_m,
          },
        },
      have h4 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ ⋃ i : ℤ, {int.fract (α * ↑i)}, from by
        {
          exact set.subset_sUnion_of_mem h_mem,
        },
      have h5 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by
        {
          exact set.subset.refl _,
        },
      have h6 : ∀ i : ℤ, int.fract (α * ↑i) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by
        {
          assume i : ℤ,
          have h_m : (i : ℤ) ∈ (@set.univ ℤ), from by {
            exact set.mem_univ i,
          },
          have h_mem : int.fract (α * ↑i) ∈ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by
            {
              apply set.mem_image_of_mem i, exact h_m,
            },
          exact h_mem,
        },
      have h7 : ⋃ i : ℤ, {int.fract (α * ↑i)} ⊆ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
        have h_subset : ∀ i : ℤ, {int.fract (α * ↑i)} ⊆ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
          assume i : ℤ,
          have h_subset : ∅ ⊆ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {
            have h_subset : ∅ ⊆ {(i : ℤ)}, from by {
              exact set.subset.refl _,
            },
            have h_subset : {(i : ℤ)} ⊆ (@set.univ ℤ), from by
              {
                exact set.subset_univ _,
              },
            have h_subset : {(i : ℤ)} ⊆ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by
              {
                have h_subset : {(i : ℤ)} ⊆ (λ (m : ℤ), int.fract (α * ↑m)) '' {(i : ℤ)}, from by
                  {
                    have h_subset : {(i : ℤ)} ⊆ {(i : ℤ)}, from
                      by {
                        exact set.subset.refl _,
                      },
                    have h_subset : {(i : ℤ)} ⊆ (λ (m : ℤ), int.fract (α * ↑m)) '' {(i : ℤ)}, from
                      by {
                        exact set.subset_image_of_subset h_subset,
                      },
                    exact h_subset,
                  },
                have h_subset : {(i : ℤ)} ⊆ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from by
                  {
                    have h_subset : {(i : ℤ)} ⊆ (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ), from
                      by {
                        have h_subset : {(i : ℤ)} ⊆ (λ (m : ℤ), int.fract (α * ↑m)) '' {(i : ℤ)}, from
                          by {
                            exact set.subset_inter_right h_subset,
                          },
                        exact h_subset,
                      },
                    exact h_subset,
                  },
                exact h_subset,
              },
            have h_subset : ∅ ⊆ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from
              by {
                exact set.subset_sUnion_of_mem h_subset,
              },
            exact h_subset,
          },
          have h_subset : {int.fract (α * ↑i)} ⊆ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by
            {
              exact set.subset_sUnion_of_mem h_subset,
            },
          exact h_subset,
        },
        exact set.sUnion_subset h_subset,
      },
      have h_eq : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = ⋃ i : ℤ, {int.fract (α * ↑i)}, from
        by {
          exact set.subset.antisymm h4 h7,
        },
      exact h_eq,
      }, 
  have h_infinite : ∀ i j : ℤ, i ≠ j → int.
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let the_set : set ℝ := set.range int.fract ∩ set.Icc 0 1,
  let the_naturals : set ℕ := set.range (λ x : ℕ, set.finite_int_range 0 x),
  let the_ints : set ℤ := ⋃ (n : ℕ) (h : n ∈ the_naturals), (λ x : ℕ, x - n) '' (set.finite_int_range 0 n),
  have the_ints_subset_range : the_ints ⊆ set.range int.fract, from 
    by {intros x hx, rcases hx with ⟨y, hy⟩, rcases hy with ⟨⟨n, hn⟩, ⟨h1, h2⟩⟩, use int.fract (x + n), 
        rw ← int.fract_add, rw set.mem_image, use (x-n), simp [h2, int.fract_add, nat.add_sub_cancel_right]},
  have the_ints_subset_Icc : the_ints ⊆ set.Icc 0 1, from 
    by {intros x hx, rcases hx with ⟨y, hy⟩, rcases hy with ⟨⟨n, hn⟩, ⟨h1, h2⟩⟩, simp [h2, int.fract_add, nat.add_sub_cancel_right],
        rw ← int.fract_add, rw ← ← set.mem_Icc, rw set.mem_range, use (y+n), simp [h1]},
  have the_ints_subset_the_set : the_ints ⊆ the_set, from set.subset.trans the_ints_subset_Icc (set.inter_subset_left _ the_set.2),

  have h1 : set.range int.fract ∩ set.Icc 0 1 ⊆ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from 
    by {intros x hx, rcases hx with ⟨h1, h2⟩, 
        have h3 : ∃n : ℕ, ∀ m : ℕ, m > n → ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑m, from sorry,
        rcases h3 with ⟨n,h3⟩, 
        have h4 : ∃ N : ℤ, ∀ k : ℤ, (k ≥ N) → int.fract x - α * ↑k < (1 : ℝ) / ↑n, from sorry,
        rcases h4 with ⟨N,h4⟩, 
        use (int.fract x - α * ↑N), rw ← set.mem_Icc, rw set.mem_range, use int.fract x, simp [h2],
        have h5 : ∀ m : ℤ, m ≥ 0 → ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(m - N), from 
          assume (m : ℤ) (h : m ≥ 0), begin
            have h5 : ∃k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(((m : ℕ) - N) : ℕ), from h4 (m - N) (int.le_of_lt (nat.lt_of_lt_of_le h (nat.le_add_right (m - N) N))),
            rcases h5 with ⟨k, h5⟩, use k, simp [h5], end,
        have h6 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(N), from h5 (N) (int.zero_le N),
        rcases h6 with ⟨k, h6⟩,
        have h7 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(1), from h5 1 (int.le_add_left N 1),
        rcases h7 with ⟨k1, h7⟩,
        have h8 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(2), from h5 2 (int.le_add_left N 2),
        rcases h8 with ⟨k2, h8⟩,
        have h9 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(3), from h5 3 (int.le_add_left N 3),
        rcases h9 with ⟨k3, h9⟩,
        have h10 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(4), from h5 4 (int.le_add_left N 4),
        rcases h10 with ⟨k4, h10⟩,
        have h11 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(5), from h5 5 (int.le_add_left N 5),
        rcases h11 with ⟨k5, h11⟩,
        have h12 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(6), from h5 6 (int.le_add_left N 6),
        rcases h12 with ⟨k6, h12⟩,
        have h13 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(7), from h5 7 (int.le_add_left N 7),
        rcases h13 with ⟨k7, h13⟩,
        have h14 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(8), from h5 8 (int.le_add_left N 8),
        rcases h14 with ⟨k8, h14⟩,
        have h15 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(9), from h5 9 (int.le_add_left N 9),
        rcases h15 with ⟨k9, h15⟩,
        have h16 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(10), from h5 10 (int.le_add_left N 10),
        rcases h16 with ⟨k10, h16⟩,
        have h17 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(11), from h5 11 (int.le_add_left N 11),
        rcases h17 with ⟨k11, h17⟩,
        have h18 : ∃ k : ℤ, int.fract x - α * ↑(k : ℤ) < (1 : ℝ) / ↑(12), from h5 12 (int.le_add_left N 12),
        rcases h18 with ⟨k12, h18⟩,
        show x ∈ closure ((λ (m : ℤ), int.fract (
end --Needs more than 2000 tokens!

--OUTPUT 10
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (m n : ℤ), (α ∈ ℚ) → (int.fract (α * ↑m) = int.fract (α * ↑n)) → m = n, from 
    assume (m n : ℤ) (hα_rat : α ∈ ℚ) (hmαn_eq : int.fract (α * ↑m) = int.fract (α * ↑n)),
    have h2 : int.fract (α * (↑m - ↑n)) = 0, from by rw [←add_neg_self, ←sub_eq_add_neg, ←hmαn_eq, ←add_assoc],
    have h3 : ∃ (q : ℤ), int.fract (α * (↑m - ↑n)) = q, from ⟨int.floor (α * ↑(m - n)), by rw [int.add_fract, add_comm, int.add_fract]⟩,
    have h4 : α = (int.floor (α * ↑(m - n)) : ℤ) / (↑(m - n) : ℤ), from 
      show α = (int.floor (α * ↑(m - n)) : ℤ)/(↑(m - n) : ℤ),
      begin
        have h1 : α * (↑m - ↑n : ℤ) = int.floor (α * ↑(m - n)), from 
          begin exact (int.add_fract (α * ↑m) (- ↑n)) ⟨(int.fract_ne_zero_of_ne_zero (α * ↑m)).1,by rw [mul_comm, neg_one_mul]⟩⟩ h2, end,
        rw h1,
        have h2 : ↑(m - n) = (↑(m - n) : ℤ), from rfl,
        rw h2,
        ring,
      end,
    have h5 : α ∈ ℚ, from by {rw hα_rat, exact ⟨(m - n : ℤ), by rw h4⟩},
    show m = n, from rat_unique_denom h5 (by rw [h4, mul_comm]) (neg_ne_zero (m - n)),

  have h2 : ∀ (m n : ℤ), (int.fract (α * ↑m) = int.fract (α * ↑n)) → m = n, from by {
    assume (m n : ℤ) (hmαn_eq : int.fract (α * ↑m) = int.fract (α * ↑n)),
    have h3 : ∃ q : ℤ, ↑q * α < ↑n, from ⟨m, by rwa [←mul_one, ←hmαn_eq, int.lt_iff_add_one_le, int.fract_le_iff_floor_add_one_le]⟩,
    have h4 : ∃ q : ℤ, ↑n < ↑q * α, from ⟨m + 1, by rwa [←mul_one, ←hmαn_eq, int.lt_iff_add_one_le, int.fract_le_iff_floor_add_one_le]⟩,
    show m = n, from (hα_irrat h3 h4),
  },

  have h3 : ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ @set.univ ℝ, from by {
    assume x : ℝ, assume h1 : x ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ),
    show x ∈ @set.univ ℝ, from by {
      obtain ⟨m, h2⟩ := h1,
      have h3 : m ∈ @set.univ ℤ, from by {exact set.mem_univ m},
      show x ∈ @set.univ ℝ, from by {rw h2, exact set.mem_univ (int.fract (α * ↑m))},
    },
  },

  have h4 : ∀ (m n : ℤ), int.fract (α * ↑m) = int.fract (α * ↑n), from by {
    assume (m n : ℤ) ,
    have h1 : int.fract (α * ↑m) = int.fract (α * ↑n), from by {rw [mul_comm α m, mul_comm α n]},
    show int.fract (α * ↑m) = int.fract (α * ↑n), from by {rw h1},
  },

  have h5 : ∀ (m n : ℤ), m = n, from
    assume (m n : ℤ), h2 m n (h4 m n),

  have h6 : ∀ (m n : ℤ), int.fract (α * ↑m) = int.fract (α * ↑n), from
    assume (m n : ℤ), by rw [h5 m n],

  have h7 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = (@set.univ ℝ), from set.eq_univ_iff_forall.1 (by {assume x, rw h7}),

  have h8 : (@set.univ ℝ) ⊆ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {
    assume x : ℝ, assume hx_univ : x ∈ (@set.univ ℝ),
    obtain ⟨ m, hm⟩ := exists_rat_between_two_irrat_gt hα_irrat ⟨0, by norm_num⟩ hx_univ,
    have h1 : ∀ n, ∃ y : ℝ, n * ↑m ∈ set.Icc (x - int.fract (α * n * ↑m)) (x + int.fract (α * n * ↑m)), from 
      assume n : ℝ, ⟨int.fract (α * n * ↑m), by have h1 := int.add_fract (α * n * ↑m) (- n * ↑m);
                                                     have h2 := int.le_add_iff_nonpos_left (- n * ↑m);
                                                     have h3 := int.fract_nonneg _;
                                                     have h4 : ↑x ≤ ↑x + int.fract (α * ↑n * ↑m), from by rw [add_comm, ←add_assoc, ←add_assoc, h1],
                                                     have h5 : ↑x - int.fract (α * ↑n * ↑m) ≤ ↑x, from by rw [add_comm, ←add_assoc, ←add_assoc, h1]; norm_num,
                                                     rw [set.mem_Icc, h3, h2, h5, h4]⟩,
    have h2 : ∃ n : ℕ, ∃ y : ℝ, n * ↑m ∈ set.Icc (x - int.fract (α * n * ↑m)) (x + int.fract (α * n * ↑m)), from
      ⟨nat.succ (↑m / 2), int.fract (α * ↑(nat.succ (↑m / 2 * ↑m)) * ↑m), by have h1 := by rwa [←mul_assoc, ←int.right_distrib, ←int.distrib_int_cast, ←nat.cast_mul, ←nat.cast_one, nat.cast_mul_one, mul_comm, ←nat.one_mul, ←nat.mul_add_mul_div_left];
                                                                                    have h2 := int.le_add_iff_nonpos_left (- nat.succ (↑m / 2) * ↑m);
                                                                
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
