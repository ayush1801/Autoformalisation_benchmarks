import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from 
    assume (i j : ℤ) (h : i ≠ j),
    have h1 : (α * ↑i) - (int.floor (α * ↑i)) = (int.fract (α * ↑i)), from int.fract_eq_of_floor_sub_eq (int.floor_le (α * ↑i)),
    have h2 : (α * ↑j) - (int.floor (α * ↑j)) = (int.fract (α * ↑j)), from int.fract_eq_of_floor_sub_eq (int.floor_le (α * ↑j)),
    have h3 : (α * ↑i) - (int.floor (α * ↑i)) = (α * ↑j) - (int.floor (α * ↑j)), from by rw [h1,h2],
    have h4 : (α * ↑i) - (int.floor (α * ↑i)) = (α * ↑j) - (int.floor (α * ↑j)), from by rw [h1,h2],
    have h5 : α = (int.floor (α * ↑i) - int.floor (α * ↑j)) / (i - j), from by rw [mul_comm α i,mul_comm α j,mul_sub,mul_div_cancel (ne_of_gt (int.cast_pos.2 (int.coe_nat_pos.2 (nat.succ_pos 0)))),mul_comm (i - j) α,h4],
    have h6 : α ∈ ℚ, from by rw [h5],
    have h7 : irrational α, from hα_irrat,
    have h8 : ¬ (α ∈ ℚ), from h7,
    show (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by {apply h8,exact h6},

  have h2 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from 
    assume (i j : ℤ) (h : i ≠ j),
    have h1 : (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from by {apply set.mem_cons_of_ne,exact h1 h},
    show (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from h1,

  have h3 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from 
    assume (i j : ℤ) (h : i ≠ j),
    have h1 : (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from by {apply set.mem_cons_of_ne,exact h1 h},
    show (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from h1,

  have h4 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from 
    assume (i j : ℤ) (h : i ≠ j),
    have h1 : (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from by {apply set.mem_cons_of_ne,exact h1 h},
    show (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from h1,

  have h5 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from 
    assume (i j : ℤ) (h : i ≠ j),
    have h1 : (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from by {apply set.mem_cons_of_ne,exact h1 h},
    show (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from h1,

  have h6 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from 
    assume (i j : ℤ) (h : i ≠ j),
    have h1 : (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from by {apply set.mem_cons_of_ne,exact h1 h},
    show (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from h1,

  have h7 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from 
    assume (i j : ℤ) (h : i ≠ j),
    have h1 : (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from by {apply set.mem_cons_of_ne,exact h1 h},
    show (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from h1,

  have h8 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from 
    assume (i j : ℤ) (h : i ≠ j),
    have h1 : (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from by {apply set.mem_cons_of_ne,exact h1 h},
    show (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from h1,

  have h9 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from 
    assume (i j : ℤ) (h : i ≠ j),
    have h1 : (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from by {apply set.mem_cons_of_ne,exact h1 h},
    show (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from h1,

  have h10 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from 
    assume (i j : ℤ) (h : i ≠ j),
    have h1 : (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from by {apply set.mem_cons_of_ne,exact h1 h},
    show (int.fract (α * ↑i)) ∉ (int.fract (α * ↑j)) :: set.univ, from h1,

  have h11 : ∀ (i
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
    assume (i j : ℤ) (h2 : i ≠ j),
    have h3 : α ≠ (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
      assume h4 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j),
      have h5 : (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j) ∈ ℚ, from by {
        rw h4, exact ℚ.coe_nat_rat,
      },
      have h6 : (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j) ∈ ℝ, from by {
        rw h4, exact ℝ.coe_nat_rat,
      },
      have h7 : (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j) ∈ ℝ ∩ ℚ, from by {
        split, exact h6, exact h5,
      },
      have h8 : (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j) ∈ ℝ ∩ ℚ ∩ {x : ℝ | irrational x}, from by {
        split, exact h7, exact hα_irrat,
      },
      have h9 : (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j) ∈ ∅, from by {
        apply set.not_mem_empty, exact h8,
      },
      have h10 : false, from by {
        rw h9,
      },
      exact h10,
    },
    have h11 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume h12 : int.fract (α * ↑i) = int.fract (α * ↑j),
      have h13 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
        rw h12, ring,
      },
      exact h3 h13,
    },
    exact h11,

  have h14 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h15 : i ≠ j,
    exact h1 i j h15,
  },
  have h16 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h17 : i ≠ j,
    exact h14 j i (ne.symm h17),
  },
  have h18 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h19 : i ≠ j,
    exact h16 j i (ne.symm h19),
  },
  have h20 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h21 : i ≠ j,
    exact h18 i j h21,
  },
  have h22 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h23 : i ≠ j,
    exact h20 j i (ne.symm h23),
  },
  have h24 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h25 : i ≠ j,
    exact h22 i j h25,
  },
  have h26 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h27 : i ≠ j,
    exact h24 j i (ne.symm h27),
  },
  have h28 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h29 : i ≠ j,
    exact h26 i j h29,
  },
  have h30 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h31 : i ≠ j,
    exact h28 j i (ne.symm h31),
  },
  have h32 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h33 : i ≠ j,
    exact h30 i j h33,
  },
  have h34 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h35 : i ≠ j,
    exact h32 j i (ne.symm h35),
  },
  have h36 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h37 : i ≠ j,
    exact h34 i j h37,
  },
  have h38 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h39 : i ≠ j,
    exact h36 j i (ne.symm h39),
  },
  have h40 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h41 : i ≠ j,
    exact h38 i j h41,
  },
  have h42 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h43 : i ≠ j,
    exact h40 j i (ne.symm h43),
  },
  have h44 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h45 : i ≠ j,
    exact h42 i j h45,
  },
  have h46 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume h47 : i ≠ j,
    exact h44 j i (ne.symm h47),
  },
  have h48 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
    assume i j,
    assume
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
    assume (i j : ℤ) (h2 : i ≠ j),
    have h3 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
      rw [int.fract_eq_sub_floor, int.fract_eq_sub_floor], ring,
    },
    have h4 : (i - j) ≠ 0, from by {
      assume h5 : (i - j) = 0,
      have h6 : α = 0, from by {rw [h5, sub_eq_zero] at h3, rw [h3, div_zero]},
      have h7 : α ≠ 0, from by {apply hα_irrat.ne,},
      contradiction,
    },
    have h8 : α ∈ ℚ, from by {rw [h3, ← int.coe_nat_eq_coe_int_of_nonneg (int.coe_nat_lt_coe_int_of_lt (int.coe_nat_pos_of_ne_zero h4))], apply_instance},
    have h9 : α ∉ ℚ, from by {apply hα_irrat.ne,},
    contradiction,

  have h10 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0, from 
    assume (i j : ℤ) (h11 : i ≠ j),
    have h12 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {apply h1, exact h11,},
    have h13 : int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0, from by {apply sub_ne_zero_of_ne, exact h12,},
    show int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0, from by {apply h13,},

  have h14 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc 0 1, from 
    assume (i j : ℤ) (h15 : i ≠ j),
    have h16 : int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0, from by {apply h10, exact h15,},
    have h17 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc 0 1, from by {
      have h18 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-1) 1, from by {
        have h19 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-1) 2, from by {
          have h20 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-2) 2, from by {
            have h21 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-2) 3, from by {
              have h22 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-3) 3, from by {
                have h23 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-3) 4, from by {
                  have h24 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-4) 4, from by {
                    have h25 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-4) 5, from by {
                      have h26 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-5) 5, from by {
                        have h27 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-5) 6, from by {
                          have h28 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-6) 6, from by {
                            have h29 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-6) 7, from by {
                              have h30 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-7) 7, from by {
                                have h31 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-7) 8, from by {
                                  have h32 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-8) 8, from by {
                                    have h33 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-8) 9, from by {
                                      have h34 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-9) 9, from by {
                                        have h35 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-9) 10, from by {
                                          have h36 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-10) 10, from by {
                                            have h37 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-10) 11, from by {
                                              have h38 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-11) 11, from by {
                                                have h39 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-11) 12, from by {
                                                  have h40 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-12) 12, from by {
                                                    have h41 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-12) 13, from by {
                                                      have h42 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-13) 13, from by {
                                                        have h43 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-13) 14, from by {
                                                          have h44 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-14) 14, from by {
                                                            have h45 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-14) 15, from by {
                                                              have h46 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-15) 15, from by {
                                                                have h47 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-15) 16, from by {
                                                                  have h48 : int.fract (α * ↑i) - int.fract (α * ↑j) ∈ set.Icc (-16
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
  
  assume (h7 : ε > 0),
  cases h2 ε h7 with N1 h8,
  cases h3 ε h7 with N2 h9,

  let N := max N1 N2,
  use N,

  have h10 : ∀ n > N, n > N1 ∧ n > N2 := by {
    assume n h,
    split,
    exact lt_of_le_of_lt (le_max_left N1 N2) h, 
    exact lt_of_le_of_lt (le_max_right N1 N2) h,
  },
  
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

  have h15 : ∀ n > N, ((l - ε) < (x n)) ∧ ((x n) < (l+ε)), 
  from by {
    intros n1 h16, cases (h11 n1 h16);
    split; linarith,
  },

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
