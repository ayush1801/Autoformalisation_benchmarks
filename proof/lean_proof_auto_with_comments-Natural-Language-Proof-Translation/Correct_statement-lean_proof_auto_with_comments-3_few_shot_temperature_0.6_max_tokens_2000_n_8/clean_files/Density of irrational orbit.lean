import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  let S := (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ),
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from by auto [hα_irrat, int.fract_eq_iff_eq, int.cast_inj],

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  have h2 : ∃ s : ℝ, s ∈ (closure S), from by auto [bw],

  have h3 : ∀ x y : ℝ, x ∈ S → y ∈ S → abs (x - y) ∈ S, from by auto [abs_of_nonneg (sub_nonneg.2 (int.fract_nonneg _))],

  have h4 : ∀ x y : ℝ, x ∈ S → y ∈ S → abs (x - y) < 1, from by auto [int.fract_lt_one],

  have h5 : ∀ x : ℝ, x ∈ S → 0 ≤ x, from by auto [int.fract_nonneg],

  have h6 : ∀ x : ℝ, x ∈ S → x < 1, from by auto [int.fract_lt_one],

  have h7 : ∀ x y : ℝ, x ∈ S → y ∈ S → abs (x - y) < (1 : ℝ), from by auto [abs_of_nonneg (sub_nonneg.2 (int.fract_nonneg _))],
  
  show closure S = set.Icc 0 1, from by auto [closure_eq_of_is_closed, set.is_closed_Icc, h2, h3, h4, h5, h6, h7],
end

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $α$ be an irrational number. Then for distinct $i, j \in \Z$, we must have $\{i α\} \neq\{j α\}$.
  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto using [hα_irrat, irrational_iff_not_rat],

  -- If this were not true, then
  have h2 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h1],

  -- $\{i \alpha\} \neq\{j \alpha\}$
  have h3 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h2],

  -- Hence,
  have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by auto [h3],

  -- $S:=\{\{i \alpha\} \mid i \in \Z\}$
  let S := (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ),

  -- is an infinite subset of $\left[0,1\right]$.
  have h5 : ∀ x : ℤ, x ∈ @set.univ ℤ → (int.fract (α * ↑x)) ∈ set.Icc 0 1, from by auto [int.fract_nonneg, int.fract_lt_one],
  have h6 : S ⊆  set.Icc 0 1, from by auto [h5],
  have h7 : set.Icc 0 1 ⊆ closure S, from by auto [closure_subset, h6],

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
  have h8 : ∃ x : ℝ, x ∈ closure S ∧ ∃ s : set ℝ, finite s ∧ x ∈ closure s, from by auto [closure_iff_nhds_ne_empty],
  have h9 : ∃ x : ℝ, x ∈ closure S ∧ ∃ s : set ℝ, finite s ∧ x ∈ closure s, from by auto [h8],

  -- There exists $x \in S$ such that $\{x\}<\epsilon$ (which exists as $0$ is a limit point)
  have h10 : ∃ (x : ℤ), x ∈ @set.univ ℤ ∧ (int.fract (α * ↑x)) < (1 : ℝ), from by auto [h9, set.mem_univ, int.fract_nonneg, int.fract_lt_one],
  have h11 : ∃ (x : ℤ), x ∈ @set.univ ℤ ∧ (int.fract (α * ↑x)) < (1 : ℝ), from by auto [h10],

  -- and $N$ such that $N \cdot\{x\} \leq y<(N+1) \cdot\{x\}$
  have h12 : ∃ N : ℤ, (int.fract (α * ↑N)) ≤ (1 : ℝ) ∧ (int.fract (α * ↑N)) < (1 : ℝ), from by auto [h11, int.fract_nonneg, int.fract_lt_one],
  have h13 : ∃ N : ℤ, (int.fract (α * ↑N)) ≤ (1 : ℝ) ∧ (int.fract (α * ↑N)) < (1 : ℝ), from by auto [h12],

  -- we get: $|y-\{N x\}|<\epsilon$.
  have h14 : ∃ N : ℤ, (int.fract (α * ↑N)) ≤ (1 : ℝ) ∧ (int.fract (α * ↑N)) < (1 : ℝ), from by auto [h13],

  -- To show that $S$ is dense in $[0, 1]$, consider $y \in[0,1]$, and $\epsilon>0$. 
  have h15 : ∃ N : ℤ, (int.fract (α * ↑N)) ≤ (1 : ℝ) ∧ (int.fract (α * ↑N)) < (1 : ℝ), from by auto [h14],

  -- Then by selecting $x \in S$ such that $\{x\}<\epsilon$ (which exists as $0$ is a limit point),
  have h16 : ∃ N : ℤ, (int.fract (α * ↑N)) ≤ (1 : ℝ) ∧ (int.fract (α * ↑N)) < (1 : ℝ), from by auto [h15],

  -- and $N$ such that $N \cdot\{x\} \leq y<(N+1) \cdot\{x\}$
  have h17 : ∃ N : ℤ, (int.fract (α * ↑N)) ≤ (1 : ℝ) ∧ (int.fract (α * ↑N)) < (1 : ℝ), from by auto [h16],

  -- we get: $|y-\{N x\}|<\epsilon$.
  have h18 : ∃ N : ℤ, (int.fract (α * ↑N)) ≤ (1 : ℝ) ∧ (int.fract (α * ↑N)) < (1 : ℝ), from by auto [h17],
  have h19 : closure S = set.Icc 0 1, from by auto [closure_eq_of_is_closed, h7, h18],
  show closure S = set.Icc 0 1, from by auto [h19],
end

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- fractional part of integer multiples of $\alpha$ is a subset of $[0,1]$
  have h1 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ (set.Icc 0 1), from by auto [set.Icc_subset, int.fract_range],
  -- $\alpha$ is irrational
  have hα_irrat_1 : irrational (1 : ℝ), from by auto,
  have hα_irrat_2 : irrational (-1 : ℝ), from by auto,
  -- fractional part of integer multiples of $\alpha$ is an infinite set
  have h2 : infinite ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [hα_irrat, hα_irrat_1, hα_irrat_2, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int],
  -- fractional part of integer multiples of $\alpha$ has zero as a limit point
  have h3 : limit_point ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) 0, from by auto [int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.fract_eq_of_int_eq_int, int.f
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
    -- let α be an irrational number
    assume hα_irrat : irrational α,
    -- for any distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$
    have h_distinct_ne : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)),
    begin
        -- assume i, j are distinct integers
        assume i j : ℤ,
        assume h_ne: i ≠ j,
        -- assume $\{i \alpha\} =\{j \alpha\}$
        assume h_eq : int.fract (α * ↑i) = int.fract (α * ↑j),
        -- then $i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor$
        have h_eq1 : (α * ↑i) - (int.floor (α * ↑i)) = int.fract (α * ↑i), from by auto [int.fract_def, int.floor_le],
        have h_eq2 : (α * ↑j) - (int.floor (α * ↑j)) = int.fract (α * ↑j), from by auto [int.fract_def, int.floor_le],
        have h_eq3 : int.fract (α * ↑i) = int.fract (α * ↑j), from h_eq,
        have h_eq4 : (α * ↑i) - (int.floor (α * ↑i)) = (α * ↑j) - (int.floor (α * ↑j)), from eq.trans (eq.symm h_eq1) (eq.trans h_eq3 h_eq2),
        -- which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$.
        have h_eq5 : α = (int.floor (α * ↑i) - int.floor (α * ↑j)) / (i - j), from by auto [int.div_eq_iff_mul_eq, eq.trans (eq.symm h_eq4) (eq.trans (eq.symm h_eq1) (eq.trans (eq.symm h_eq3) h_eq2)), eq.symm (int.div_mul_cancel (i - j))],
        have h_eq6 : α ∈ ℚ, from by auto [int.coe_nat_dvd, eq.symm h_eq5],
        -- contradiction
        contradiction,
    end,
    -- hence, $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$ is an infinite subset of $\left[0,1\right]$.
    have h_S_finite : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ≠ ∅, from by auto [exists.intro 0],
    have h_S_infinite : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ≠ set.finite_univ, from by auto [eq_self_iff_true, h_S_finite, h_distinct_ne],
    have h_S_infinite' : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = set.Icc 0 1, from by auto [h_S_infinite],
    -- by Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$.
    have h_S_limit_point : ∃ x ∈ set.Icc 0 1, ∀ ε > 0, ∃ y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), dist x y < ε, from by auto [set.bounded_Icc, set.compact_Icc, set.closed_Icc, set.compact_Icc, set.bounded_Icc, set.Icc_subset_univ, set.eq_univ_of_univ_subset, set.eq_univ_of_univ_subset, set.Icc_subset_univ],
    -- one can thus find pairs of elements of $S$ that are arbitrarily close.
    -- since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
    have h_S_limit_point' : ∃ x ∈ set.Icc 0 1, ∀ ε > 0, ∃ y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), dist x y < ε, from by auto [set.bounded_Icc, set.compact_Icc, set.closed_Icc, set.compact_Icc, set.bounded_Icc, set.Icc_subset_univ, set.eq_univ_of_univ_subset, set.eq_univ_of_univ_subset, set.Icc_subset_univ],
    -- to show that $S$ is dense in $[0, 1]$, consider $y \in[0,1]$, and $\epsilon>0$.
    have h_S_dense : ∀ y ∈ set.Icc 0 1, ∀ ε > 0, ∃ x ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), dist x y < ε,
    begin
        -- assume y ∈ [0, 1]
        assume y : ℝ,
        assume h_le : 0 ≤ y,
        assume h_le' : y ≤ 1,
        -- assume ε > 0
        assume ε : ℝ,
        assume h_ε : 0 < ε,
        -- then by selecting $x \in S$ such that $\{x\}<\epsilon$ (which exists as $0$ is a limit point), and $N$ such that $N \cdot\{x\} \leq y<(N+1) \cdot\{x\}$, we get: $|y-\{N x\}|<\epsilon$.
        have h_x : ∃ x ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), ∀ ε > 0, ∃ y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), dist x y < ε, from by auto [h_S_limit_point'], 
        have h_x' : ∃ x : ℝ, ∀ ε > 0, ∃ y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), dist x y < ε, from by auto [h_x],
        have h_x'' : ∃ x : ℝ, ∀ ε > 0, ∃ y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), abs (x - y) < ε, from by auto [h_x'],
        have h_x''' : ∃ x : ℝ, ∀ ε > 0, ∃ y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), abs (x - y) < ε, from by auto [h_x''],
        have h_x'''' : ∃ x : ℝ, ∃ y ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), abs (x - y) < ε, from by auto [h_x'''],
        have h_x'''''
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- by Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$
  have h1 : ∃ x : ℝ, x ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ x ≠ 0, from by auto [compact_closure, compact_Icc, Icc_subset_closure, int.fract_ne_zero],
  -- One can thus find pairs of elements of $S$ that are arbitrarily close.
  have h2 : ∃ (x y : ℝ), x ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ y ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ x ≠ y ∧ 0 < abs (x - y), from by auto [closure_iff, h1],
  -- Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
  have h3 : 0 ∈ closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [closure_iff, h2],

  -- To show that $S$ is dense in $[0, 1]$,
  have h4 : ∀ y ∈ set.Icc 0 1, ∃ (x : ℝ), x ∈ ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ y ∈ set.Ioo x (x + abs (x - y)), from by auto [closure_iff, h3],

  show closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from by auto [closure_iff, h4, h3, h2],
end

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number. Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$. If this were not true, then
  have h1 : ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
    begin
      assume (i : ℤ) (j : ℤ) (hij : i ≠ j),
      assume hij_eq : int.fract (α * ↑i) = int.fract (α * ↑j),
      have h1 : α = (int.fract (α * ↑i) - int.fract (α * ↑j)) / (i - j), from by auto using [int.fract_add],
      -- which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}
      have h2 : α ∈ ℚ, from by auto [h1],
      show false, from hα_irrat h2,
    end,

  -- Hence,
  -- $$
  -- S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}
  -- $$
  -- is an infinite subset of $\left[0,1\right]$.
  have h2 : infinite ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from 
    begin
      show infinite ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto using [h1, set.finite_univ, set.infinite_iff_nonempty_of_injective],
    end,

  have h3 : ∀ n : ℤ, n ≠ 0 → int.fract (α * ↑n) ∈ ({(λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)}), from by auto using [set.mem_image],

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$. One can thus find pairs of elements of $S$ that are arbitrarily close. Since (the absolute value of) the difference of any two elements of $S$ is also an element of $S$, it follows that $0$ is a limit point of $S$.
  let S : set ℝ := (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ),
  have h4 : ∀ x ∈ S, ∃ y, y ∈ S ∧ dist x y < 1, from 
    begin
      assume (x : ℝ) (hx : x ∈ S),
      have h1 : (∃ n : ℤ, x = int.fract (α * ↑n)), from by auto [set.mem_image],
      have h2 : (∃ n : ℤ, int.fract (α * ↑n) = x), from by auto [h1],
      have h3 : (∃ n : ℤ, int.fract (α * ↑n) = x ∧ n ≠ 0), from by auto using [h2, hx, h3],
      have h4 : (∃ n : ℤ, int.fract (α * ↑n) = x ∧ n ≠ 0 ∧ n ≠ 1), from by auto using [h3, h3],
      have h5 : ∃ y, y ∈ S ∧ dist x y < 1, from by auto using [h4, h3, h2, hx, h1, h3, exists_and_dist_lt_one],
      show ∃ y, y ∈ S ∧ dist x y < 1, from by auto [h5],
    end,
  have h5 : ∀ (x : ℝ) (hx : x ∈ S), limit_point S x, from by auto using [h4, limit_point_of_forall_dist_lt],
  have h6 : ∀ (n : ℤ) (hn : n ≠ 0), limit_point S (int.fract (α * ↑n)), from by auto using [h5, h3],
  have h7 : limit_point S 0, from by auto using [h6, limit_point_of_forall_dist_lt],
  have h8 : 0 ∈ closure S, from by auto using [h7],
  have h9 : 0 ∈ set.Icc 0 1, from by auto using [set.mem_Icc, set.mem_Icc],
  have h10 : S ⊆ set.Icc 0 1, from by auto using [h9, h8, subset_insert_of_mem],

  -- To show that $S$ is dense in $[0, 1]$, consider $y \in[0,1]$, and $\epsilon>0$. Then by selecting $x \in S$ such that $\{x\}<\epsilon$ (which exists as $0$ is a limit point), and $N$ such that $N \cdot\{x\} \leq y<(N+1) \cdot\{x\}$, we get: $|y-\{N x\}|<\epsilon$.
  have h11 : ∀ (y : ℝ) (hy : y ∈ set.Icc 0 1) (ε : ℝ) (hε : ε > 0), ∃ (x : ℝ) (hx : x ∈ S), dist x y < ε, from
    begin
      assume (y : ℝ) (hy : y ∈ set.Icc 0 1) (ε : ℝ) (hε : ε > 0),
      have h1 : ∃ (x : ℝ) (hx : x ∈ S), dist x 0 < ε, from by auto using [h8, hε, h7, h11],
      have h2 : ∃ (n : ℤ), int.fract (α * ↑n) = x, from by auto [set.mem_image, h1],
      have h3 : ∃ (n : ℤ), int.fract (α * ↑n) = x ∧ n ≠ 0, from by auto using [h2, h3],
      have h4 : ∃ (n : ℤ), int.fract (α * ↑n) = x ∧ n ≠ 0 ∧ n ≠ 1, from by auto using [h3, h3],
      have h5 : ∃ (n : ℤ), int.fract (α * ↑n) = x ∧ n ≠ 0 ∧ n ≠ 1 ∧ 0 < ↑n * (int.fract (α * ↑n)) ∧ ↑n * (int.fract (α * ↑n)) ≤ y, from by auto using [h4, h3, h2, h1, h3, exists_and_dist_lt_one, exists_and_dist_lt_one, exists_and_dist_lt_one, exists_and_dist_lt_one],
      have h6 : ∃ (n : ℤ), int.fract (α * ↑n) = x ∧ n ≠ 0 ∧ n ≠ 1 ∧ 0 < ↑n * (int.fract (α * ↑n)) ∧ ↑n * (int.fract (α * ↑n)) ≤ y ∧ y < (↑n + 1) * (int.fract (α * ↑n)), from by auto using [h5, h5, h1, h3, h2, h3, exists_and_dist_lt_one, exists_and_dist_lt_one, exists_and_dist_lt_one, exists_and_dist_lt_one],
      have h7 : ∃ (n : ℤ), int.fract (α * ↑n) = x ∧ n ≠ 0 ∧ n ≠ 1 ∧ 0 < ↑n * (int.fract (α * ↑n)) ∧ ↑n * (int.fract (α * ↑n)) ≤ y ∧ y < (↑n + 1) * (int.fract (α
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- ∀ x : ℤ, ∃ y : ℤ, ∀ y' : ℤ, y ≠ y' → int.fract (α * ↑y) ≠ int.fract (α * ↑y')
  have h1 : ∀ x : ℤ, ∃ y : ℤ, ∀ y' : ℤ, y ≠ y' → int.fract (α * ↑y) ≠ int.fract (α * ↑y'), 
  { 
    assume x : ℤ,
    -- ℤ → α ≠ 0
    have h1_1 : (ℤ → α) ≠ 0, from by auto [irrational.def, int.coe_nat_ne_zero, int.coe_int_ne_zero, not_false_iff],
    -- α ≠ 0
    have h1_2 : α ≠ 0, from by auto [h1_1, int.cast_ne_zero],
    -- by_contradiction
    by_contradiction,
    -- Suppose ∀ x : ℤ, ∃ y : ℤ, ∀ y' : ℤ, y ≠ y' → int.fract (α * ↑y) ≠ int.fract (α * ↑y')
    assume h2 : ∀ x : ℤ, ∃ y : ℤ, ∀ y' : ℤ, y ≠ y' → int.fract (α * ↑y) ≠ int.fract (α * ↑y'),
    -- ∃ y : ℤ, ∀ y' : ℤ, y ≠ y' → int.fract (α * ↑y) ≠ int.fract (α * ↑y')
    have h3 : ∃ y : ℤ, ∀ y' : ℤ, y ≠ y' → int.fract (α * ↑y) ≠ int.fract (α * ↑y'), from by auto [h2],
    -- ∃ y : ℤ, int.fract (α * ↑y) = int.fract (α * ↑x)
    have h4 : ∃ y : ℤ, int.fract (α * ↑y) = int.fract (α * ↑x), from by auto [h3],
    -- int.fract (α * ↑y) = int.fract (α * ↑x)
    obtain ⟨y, h4_1⟩ : ∃ y : ℤ, int.fract (α * ↑y) = int.fract (α * ↑x), from h4,
    -- α * ↑y = α * ↑x
    have h5 : α * ↑y = α * ↑x, from by auto [int.fract_eq_iff, h4_1],
    -- α * ↑y = α * ↑x → α * ↑y - α * ↑x = 0
    have h6 : α * ↑y = α * ↑x → α * ↑y - α * ↑x = 0, from by auto [sub_eq_zero],
    -- α * ↑y - α * ↑x = 0
    have h7 : α * ↑y - α * ↑x = 0, from by auto [h5, h6],
    -- α * ↑y - α * ↑x = 0 → α * (↑y - ↑x) = 0
    have h8 : α * ↑y - α * ↑x = 0 → α * (↑y - ↑x) = 0, from by auto [sub_eq_zero],
    -- α * (↑y - ↑x) = 0
    have h9 : α * (↑y - ↑x) = 0, from by auto [h7, h8],
    -- α = 0
    have h10 : α = 0, from by auto [h9, h1_2, mul_eq_zero],
    -- α = 0 → α ≠ 0
    have h11 : α = 0 → α ≠ 0, from by auto [h1_2],
    -- α ≠ 0
    have h12 : α ≠ 0, from by auto [h10, h11],
    -- This is a contradiction
    have h13 : false, from by auto [h12],
    -- Contradiction
    contradiction,
  },

  -- The set of fractional parts of the multiples of α is infinite
  have h2 : infinite ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from by auto [h1, exists_forall_of_infinite],

  -- The set of fractional parts of the multiples of α has a limit point
  have h3 : ∃ x : ℝ, x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ ∀ ε > 0, ∃ y : ℝ, y ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ abs (x - y) < ε, from by auto [h2, closure_iff_nhds_within_eq, set.finite_to_set],
  -- ∃ x : ℝ, x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ ∀ ε > 0, ∃ y : ℝ, y ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ abs (x - y) < ε
  obtain ⟨x, h3_1, h3_2⟩ : ∃ x : ℝ, x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ ∀ ε > 0, ∃ y : ℝ, y ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ abs (x - y) < ε, from h3,

  -- The set of fractional parts of the multiples of α has 0 as a limit point
  have h4 : ∃ x : ℝ, x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ ∀ ε > 0, ∃ y : ℝ, y ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ abs (x - y) < ε, from by auto [h3, h3_1, h3_2],
  -- ∃ x : ℝ, x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ ∀ ε > 0, ∃ y : ℝ, y ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ abs (x - y) < ε
  obtain ⟨x, h4_1, h4_2⟩ : ∃ x : ℝ, x ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ ∀ ε > 0, ∃ y : ℝ, y ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ abs (x - y) < ε, from h4,
  -- ∀ ε > 0, ∃ y : ℝ, y ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ abs (x - y) < ε
  have h5 : ∀ ε > 0, ∃ y : ℝ, y ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ abs (x - y) < ε, from by auto [h4_1, h4_2],
  -- ∃ ε > 0, ∃ y : ℝ, y ∈ ((λ m : ℤ, int.fract (
end --Needs more than 2000 tokens!

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  -- Let $\alpha$ be an irrational number, Then for distinct $i, j \in \mathbb{Z}$, we must have $\{i \alpha\} \neq\{j \alpha\}$
  assume hα : irrational α,
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from
    by auto [int.fract_eq_iff, int.fract_ne_iff, hα, exists_eq_mul_right_of_dvd, int.coe_nat_dvd_iff, int.coe_nat_eq_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_mul_coe_nat, int.coe_nat_dvd, int.coe_nat_lt, int.coe_nat_pos, int.coe_nat_one, int.coe_nat_zero],

  -- If this were not true, then $i \alpha-\lfloor i \alpha\rfloor=\{i \alpha\}=\{j \alpha\}=j \alpha-\lfloor j \alpha\rfloor$, which yields the false statement $\alpha=\frac{\lfloor i \alpha\rfloor-\lfloor j \alpha\rfloor}{i-j} \in \mathbb{Q}$
  have h2 : (∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → irrational α, from
    by auto [int.fract_eq_iff, int.fract_ne_iff, exists_eq_mul_right_of_dvd, int.coe_nat_dvd_iff, int.coe_nat_eq_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_mul_coe_nat, int.coe_nat_dvd, int.coe_nat_lt, int.coe_nat_pos, int.coe_nat_one, int.coe_nat_zero],

  have h3 : irrational α, from by auto [h2, h1],

  -- Hence, $S:=\{\{i \alpha\} \mid i \in \mathbb{Z}\}$ is an infinite subset of $\left[0,1\right]$
  have h4 : ∀ i : ℤ, int.fract (α * ↑i) ∈ set.Icc 0 1, from by auto [int.fract_nonneg, int.fract_lt_one],
  have h5 : set.univ ℤ = (λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' set.Icc 0 1, from by auto [int.fract_nonneg, int.fract_lt_one],
  have h6 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) = (λ (m : ℤ), int.fract (α * ↑m)) '' ((λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' set.Icc 0 1), from by auto [set.image_preimage_eq],
  have h7 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) = (λ (m : ℤ), int.fract (α * ↑m)) '' set.Icc 0 1, from by auto [h5, h6],
  have h8 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) = (λ (m : ℤ), int.fract (α * ↑m)) ⁻¹' set.Icc 0 1, from by auto [h5, h6],
  have h9 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) = set.Icc 0 1, from by auto [h8, h4],

  have h10 : (λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ) ≠ ∅, from by auto [h9],

  -- By the Bolzano-Weierstrass theorem, $S$ has a limit point in $[0, 1]$
  have h11 : closure ((λ (m : ℤ), int.fract (α * ↑m)) '' (@set.univ ℤ)) ≠ ∅, from by auto [h10, closure_ne_empty],

  -- One can thus find pairs of elements of $S$ that are arbitrarily close
  have h12 : ∀ (x₁ x₂ : ℤ), x₁ ≠ x₂ → int.fract (α * ↑x₁) ≠ int.fract (α * ↑x₂), from
    by auto [int.fract_eq_iff, int.fract_ne_iff, exists_eq_mul_right_of_dvd, int.coe_nat_dvd_iff, int.coe_nat_eq_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_mul_coe_nat, int.coe_nat_dvd, int.coe_nat_lt, int.coe_nat_pos, int.coe_nat_one, int.coe_nat_zero],
  have h13 : ∀ (x₁ x₂ : ℤ), x₁ ≠ x₂ → (int.fract (α * ↑x₁) - int.fract (α * ↑x₂)) ≠ 0, from
    by auto [int.fract_eq_iff, int.fract_ne_iff, exists_eq_mul_right_of_dvd, int.coe_nat_dvd_iff, int.coe_nat_eq_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_mul_coe_nat, int.coe_nat_dvd, int.coe_nat_lt, int.coe_nat_pos, int.coe_nat_one, int.coe_nat_zero],
  have h14 : ∀ (x₁ x₂ : ℤ), x₁ ≠ x₂ → int.fract (α * ↑x₁ - α * ↑x₂) ≠ 0, from
    by auto [int.fract_eq_iff, int.fract_ne_iff, exists_eq_mul_right_of_dvd, int.coe_nat_dvd_iff, int.coe_nat_eq_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_mul_coe_nat, int.coe_nat_dvd, int.coe_nat_lt, int.coe_nat_pos, int.coe_nat_one, int.coe_nat_zero],
  have h15 : ∀ (x₁ x₂ : ℤ), x₁ ≠ x₂ → int.fract (α * ↑x₁) - int.fract (α * ↑x₂) ≠ 0, from
    by auto [int.fract_eq_iff, int.fract_ne_iff, exists_eq_mul_right_of_dvd, int.coe_nat_dvd_iff, int.coe_nat_eq_coe_nat_iff, int.coe_nat_lt_coe_nat_iff, int.coe_nat_mul_coe_nat, int.coe_nat_dvd, int.coe_nat_lt, int.coe_nat_pos, int.coe_nat_one, int.coe_nat_zero],

  have h16 : ∀ (x₁ x₂ : ℤ), x₁ ≠ x₂ → ∃ (ε : ℝ), ε > 0 ∧ ∀ (y : ℝ), abs (int.fract (α * ↑x₁) -
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
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by auto [set.subset_of_mem_powerset, set.subset_of_mem_powerset],
  -- Then $(A ∩ B) ⊆ A$, by intersection of set is a subset
  have h2 : (A ∩ B) ⊆ A, from by auto [set.inter_subset_left],
  -- Then $(A ∩ B) ⊆ S$, by subset relation is transitive 
  have h3 : (A ∩ B) ⊆ S, from by auto [set.subset.trans],
  -- Hence $(A ∩ B) ∈  𝒫 S$, by power set definition
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
  -- expand the power
  calc (x + y)^2 = (x+y)*(x+y) : by auto [sq]
  -- distributive property of multiplication over addition gives:
  ... = x*(x+y) + y*(x+y) : by auto [add_mul]
  -- applying the above property further gives:
  ... = x*x + x*y + y*x + y*y : by auto [mul_comm, add_mul] using [ring]
  -- rearranging the terms using commutativity and adding gives:
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
  -- Group has Latin Square Property
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by auto using [use (a⁻¹ * b)],
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by auto using [use b * a⁻¹], 

  -- Setting $b = a$, this becomes:
  have h3 : ∀ a : G, ∃! x : G, a * x = a, from by auto [h1],
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from by auto [h2],

  -- These $x$ and $y$ are both $(1 : G)$, by definition of identity element
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
