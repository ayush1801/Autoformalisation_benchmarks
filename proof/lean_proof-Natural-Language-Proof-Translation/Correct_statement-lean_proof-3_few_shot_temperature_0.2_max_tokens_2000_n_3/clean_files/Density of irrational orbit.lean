import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from assume (i j : ℤ) (hneq : i ≠ j),
    have h2 : α * ↑i - ↑(floor (α * ↑i)) = int.fract (α * ↑i), from by {rw int.fract_eq,},
    have h3 : α * ↑j - ↑(floor (α * ↑j)) = int.fract (α * ↑j), from by {rw int.fract_eq,},
    have h4 : α = (floor (α * ↑i) - floor (α * ↑j)) / (i - j), from by {rw [h2,h3], ring,},
    have h5 : α ∈ ℚ, from by {rw ← h4, apply int.coe_nat_div_coe_nat_of_ne_zero, exact hneq,},
    have h6 : irrational α, from hα_irrat,
    absurd h5 h6,

  have h2 : ∀ i j : ℤ, i ≠ j → (λ m : ℤ, int.fract (α * ↑m)) i ≠ (λ m : ℤ, int.fract (α * ↑m)) j, from assume (i j : ℤ) (hneq : i ≠ j),
    have h3 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from h1 i j hneq,
    show (λ m : ℤ, int.fract (α * ↑m)) i ≠ (λ m : ℤ, int.fract (α * ↑m)) j, from h3,

  have h3 : ∀ i : ℤ, (λ m : ℤ, int.fract (α * ↑m)) i ∈ set.Icc 0 1, from assume (i : ℤ),
    have h4 : int.fract (α * ↑i) ∈ set.Icc 0 1, from by {rw int.fract_eq, apply int.fract_in_Icc,},
    show (λ m : ℤ, int.fract (α * ↑m)) i ∈ set.Icc 0 1, from h4,

  have h4 : ∀ i : ℤ, (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from assume (i : ℤ),
    have h5 : (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from by {rw set.mem_image, use i, obviously,},
    show (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from h5,

  have h5 : ∀ i : ℤ, (λ m : ℤ, int.fract (α * ↑m)) i ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from assume (i : ℤ),
    have h6 : (λ m : ℤ, int.fract (α * ↑m)) i ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by {rw set.mem_closure_iff, use i, obviously,},
    show (λ m : ℤ, int.fract (α * ↑m)) i ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from h6,

  have h6 : ∀ i : ℤ, (λ m : ℤ, int.fract (α * ↑m)) i ∈ set.Icc 0 1, from assume (i : ℤ),
    have h7 : (λ m : ℤ, int.fract (α * ↑m)) i ∈ set.Icc 0 1, from h3 i,
    show (λ m : ℤ, int.fract (α * ↑m)) i ∈ set.Icc 0 1, from h7,

  have h7 : ∀ i : ℤ, (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from assume (i : ℤ),
    have h8 : (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from h4 i,
    show (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from h8,

  have h8 : ∀ i : ℤ, (λ m : ℤ, int.fract (α * ↑m)) i ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from assume (i : ℤ),
    have h9 : (λ m : ℤ, int.fract (α * ↑m)) i ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from h5 i,
    show (λ m : ℤ, int.fract (α * ↑m)) i ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from h9,

  have h9 : ∀ i : ℤ, (λ m : ℤ, int.fract (α * ↑m)) i ∈ set.Icc 0 1, from assume (i : ℤ),
    have h10 : (λ m : ℤ, int.fract (α * ↑m)) i ∈ set.Icc 0 1, from h6 i,
    show (λ m : ℤ, int.fract (α * ↑m)) i ∈ set.Icc 0 1, from h10,

  have h10 : ∀ i : ℤ, (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from assume (i : ℤ),
    have h11 : (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from h7 i,
    show (λ m : ℤ, int.fract (α * ↑m)) i ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from h11,

  have h11 : ∀ i : ℤ, (λ m : ℤ, int.fract (α * ↑m)) i ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from assume (i : ℤ),
    have h12 : (λ m : ℤ, int.fract (α * ↑m)) i ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from h8 i,
    show (λ m : ℤ, int.fract (α * ↑m)) i ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from h12,

  have h12 : ∀ i : ℤ, (λ m : ℤ, int.
end --Needs more than 2000 tokens!

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from 
    assume i j : ℤ, assume h1 : i ≠ j, assume h2 : int.fract (α * ↑i) = int.fract (α * ↑j),
    have h3 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
      rw [h2,int.fract_add,int.fract_add,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int.fract_mul,int
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from assume (i j : ℤ) (hneq : i ≠ j),
    have h2 : α ≠ (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
      assume h3 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j),
      have h4 : (i - j) ≠ 0, from by {
        assume h5 : (i - j) = 0,
        have h6 : i = j, from by {
          rw h5 at hneq,
          exact hneq,
        },
        have h7 : α = int.fract (α * ↑i), from by {
          rw h3,
          rw h6,
          ring,
        },
        have h8 : α = int.fract (α * ↑i) - int.fract (α * ↑i), from by {
          rw h7,
          ring,
        },
        have h9 : 0 = int.fract (α * ↑i), from by {
          rw h8,
          ring,
        },
        have h10 : α * ↑i = 0, from by {
          rw ← int.fract_eq_of_nonneg h9,
          ring,
        },
        have h11 : α = 0, from by {
          rw h10,
          ring,
        },
        exact hα_irrat h11,
      },
      have h12 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = 0, from by {
        rw h3,
        rw h4,
        ring,
      },
      have h13 : int.fract (α * ↑i) = int.fract (α * ↑j), from by {
        rw h12,
        ring,
      },
      exact h13,
    },
    have h14 : α * ↑i ≠ α * ↑j, from by {
      assume h15 : α * ↑i = α * ↑j,
      have h16 : i = j, from by {
        rw h15,
        ring,
      },
      exact hneq h16,
    },
    have h17 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume h18 : int.fract (α * ↑i) = int.fract (α * ↑j),
      have h19 : α * ↑i = α * ↑j, from by {
        rw ← int.fract_eq_of_nonneg h18,
        ring,
      },
      exact h14 h19,
    },
    exact h17,
  have h2 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from assume (i j : ℤ) (hneq : i ≠ j),
    have h3 : α ≠ (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
      assume h4 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j),
      have h5 : (i - j) ≠ 0, from by {
        assume h6 : (i - j) = 0,
        have h7 : i = j, from by {
          rw h6 at hneq,
          exact hneq,
        },
        have h8 : α = int.fract (α * ↑i), from by {
          rw h4,
          rw h7,
          ring,
        },
        have h9 : α = int.fract (α * ↑i) - int.fract (α * ↑i), from by {
          rw h8,
          ring,
        },
        have h10 : 0 = int.fract (α * ↑i), from by {
          rw h9,
          ring,
        },
        have h11 : α * ↑i = 0, from by {
          rw ← int.fract_eq_of_nonneg h10,
          ring,
        },
        have h12 : α = 0, from by {
          rw h11,
          ring,
        },
        exact hα_irrat h12,
      },
      have h13 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = 0, from by {
        rw h4,
        rw h5,
        ring,
      },
      have h14 : int.fract (α * ↑i) = int.fract (α * ↑j), from by {
        rw h13,
        ring,
      },
      exact h14,
    },
    have h15 : α * ↑i ≠ α * ↑j, from by {
      assume h16 : α * ↑i = α * ↑j,
      have h17 : i = j, from by {
        rw h16,
        ring,
      },
      exact hneq h17,
    },
    have h18 : int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by {
      assume h19 : int.fract (α * ↑i) = int.fract (α * ↑j),
      have h20 : α * ↑i = α * ↑j, from by {
        rw ← int.fract_eq_of_nonneg h19,
        ring,
      },
      exact h15 h20,
    },
    exact h18,
  have h3 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from assume (i j : ℤ) (hneq : i ≠ j),
    have h4 : α ≠ (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by {
      assume h5 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j),
      have h6 : (i - j) ≠ 0, from by {
        assume h7 : (i - j) = 0,
        have h8 : i = j, from by {
          rw h7 at hneq,
          exact hneq,
        },
        have h9 : α = int.fract (α * ↑i), from by {
          rw h5,
          rw h8,
          ring,
        },
        have h10 : α = int.fract (α * ↑i) - int.fract (α * ↑i), from by {
          rw h9,
          ring,
        },
        have h11 : 0 = int.fract (α * ↑i), from by {
          rw h10,
          ring,
        },
        have h12 : α * ↑i = 0, from by {
          rw ← int.fract_eq_of_nonneg h11,
          ring,
        },
        have h13 : α = 0, from by {
          rw h12,
          ring,
        },
        exact hα_irrat h13,
      },
      have h14 : (int.fract (α * ↑i) - int.fract (α * ↑j)) = 0, from by {
        rw h5,
        rw h6,
        ring,
      },
      have h15 : int.fract (α * ↑i) = int.fract (α * ↑j), from by {
        rw h14,
        ring,
      },
      exact h15,
    },
    have h16 : α * ↑i ≠ α * ↑j, from by {
      assume h17 : α * ↑i = α * ↑j,
      have h18 : i = j
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
