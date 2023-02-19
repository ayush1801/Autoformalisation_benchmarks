import data.real.irrational
import topology.basic
import algebra.order.floor


--OUTPUT 1
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), by {
    assume (i j : ℤ) (h1 : i ≠ j), 
    have h2 : (α * ↑i) - int.floor (α * ↑i) = int.fract (α * ↑i), from sorry,
    have h3 : (α * ↑j) - int.floor (α * ↑j) = int.fract (α * ↑j), from sorry,
    have h4 : (α * ↑i) - int.floor (α * ↑i) = (α * ↑j) - int.floor (α * ↑j), from sorry,
    have h5 : (α * ↑i) = (α * ↑j), from sorry,
    have h6 : (i : ℝ) = (j : ℝ), from sorry,
    have h7 : i = j, from sorry,
    show (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  },
  have h2 : ∃ s : set ℝ, ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ∈ s ∧ int.fract (α * ↑j) ∈ s, from sorry,
  have h3 : ∃ s : set ℝ, ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i) ∈ s) ∨ (int.fract (α * ↑j) ∈ s), from sorry,
  have h4 : ∃ s : set ℝ, ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ∈ s, from sorry,
  have h5 : ∃ s : set ℝ, ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑j) ∈ s, from sorry,
  have h6 : ∃ s : set ℝ, ∀ (i j : ℤ), i ≠ j → int.fract (α * ↑i) ∈ s ∧ int.fract (α * ↑j) ∈ s, from sorry,
  have h7 : ∃ s : set ℝ, ∀ i : ℤ, int.fract (α * ↑i) ∈ s, from sorry,
  have h8 : ∃ s : set ℝ, ∀ i : ℤ, int.fract (α * ↑i) ∈ s ∧ int.fract (α * ↑j) ∈ s, from sorry,
  have h9 : ∃ s : set ℝ, ∀ i : ℤ, int.fract (α * ↑i) ∈ s, from sorry,
  have h10 : ∃ s : set ℤ, ∀ i : ℤ, int.fract (α * ↑i) ∈ s, from sorry,
  have h11 : ∃ s : set ℤ, ∀ i : ℤ, int.fract (α * ↑i) ∈ s, from sorry,
  have h12 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = ∃ s : set ℤ, ∀ i : ℤ, int.fract (α * ↑i) ∈ s, from sorry,
  have h13 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = ∃ s : set ℤ, ∀ i : ℤ, int.fract (α * ↑i) ∈ s, from sorry,
  have h14 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) = ∃ s : set ℤ, ∀ i : ℤ, int.fract (α * ↑i) ∈ s, from sorry,
  have h15 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = closure ∃ s : set ℤ, ∀ i : ℤ, int.fract (α * ↑i) ∈ s, from sorry,
  have h16 : closure ∃ s : set ℤ, ∀ i : ℤ, int.fract (α * ↑i) ∈ s = set.Icc 0 1, from sorry,
  show closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from sorry,
end

--OUTPUT 2
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := 
begin
  have h1 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ (set.Icc 0 1), from sorry,
  have h2 : ∀ y : ℝ, y ∈ (set.Icc 0 1) → ∃ x : ℝ, x ∈ ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ∧ abs (y - x) < 1, from sorry,
  have h3 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from sorry,
  have h4 : set.Icc 0 1 ⊆ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)), from sorry,
  show closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1, from sorry,
end

--OUTPUT 3
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)), from sorry,

  have h2 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑j) - int.fract (α * ↑i) ≠ 0), from sorry,

  have h3 : ∀ i j : ℤ, (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑j) - int.fract (α * ↑i) ≠ 0), from sorry,

  have h4 : ∀ i j : ℤ, (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑i) - int.fract (α * ↑j) ≠ 0), from sorry,

  have h5 : ∀ i j : ℤ, (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑i) - int.fract (α * ↑j)).nat_abs ≠ 0, from sorry,

  have h6 : ∀ i j : ℤ, (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑i) - int.fract (α * ↑j)).nat_abs ≠ 0 → (int.fract (α * ↑i) - int.fract (α * ↑j)).nat_abs ∈ set.Icc 0 1, from sorry,

  have h7 : ∀ i j : ℤ, (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1, from sorry,

  have h8 : ∀ i : ℤ, (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h9 : ∀ i j : ℤ, (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑i) - int.fract (α * ↑j)) ∈ set.Icc 0 1 → (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h10 : ∀ i j : ℤ, (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h11 : ∀ i j : ℤ, (i ≠ j) → ((int.fract (α * ↑i)) ∈ set.Icc 0 1), from sorry,

  have h12 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h13 : ∀ i : ℤ, (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h14 : ∀ i : ℤ, (int.fract (α * ↑i)) ∈ set.Icc 0 1 → ((λ m : ℤ, int.fract (α * ↑m)) i) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from sorry,

  have h15 : ∀ i : ℤ, ((λ m : ℤ, int.fract (α * ↑m)) i) ∈ (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ), from sorry,

  have h16 : (λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ) ⊆ set.Icc 0 1, from sorry,

  have h17 : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) ⊆ set.Icc 0 1, from sorry,

  have h18 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)), from sorry,

  have h19 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) → (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h20 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h21 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑j)) ∈ set.Icc 0 1, from sorry,

  have h22 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h23 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)) → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h24 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)) → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)) → (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h25 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h26 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i)) ∈ set.Icc 0 1 → (int.fract (α * ↑j)) ∈ set.Icc 0 1, from sorry,

  have h27 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑j)) ∈ set.Icc 0 1, from sorry,

  have h28 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑j)) ∈ set.Icc 0 1 → (int.fract (α * ↑j)) ∈ set.Icc 0 1, from sorry,

  have h29 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑j)) ∈ set.Icc 0 1, from sorry,

  have h30 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i)) ∈ set.Icc 0 1 → (int.fract (α * ↑j)) ∈ set.Icc 0 1, from sorry,

  have h31 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i)) ∈ set.Icc 0 1 → (int.fract (α * ↑j)) ∈ set.Icc 0 1 → (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h32 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑i)) ∈ set.Icc 0 1, from sorry,

  have h33 : ∀ i j : ℤ, (i ≠ j) → (int.fract (α * ↑j)) ∈ set.
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n),
  {
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : int.fract (α * ↑m) = α * ↑m - int.nat_abs (α * ↑m), from sorry,
    have h2 : int.fract (α * ↑n) = α * ↑n - int.nat_abs (α * ↑n), from sorry,
    have h3 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
  },
  have h2 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n),
  {
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : int.fract (α * ↑m) = α * ↑m - int.nat_abs (α * ↑m), from sorry,
    have h2 : int.fract (α * ↑n) = α * ↑n - int.nat_abs (α * ↑n), from sorry,
    have h3 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
  },
  have h3 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n),
  {
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : int.fract (α * ↑m) = α * ↑m - int.nat_abs (α * ↑m), from sorry,
    have h2 : int.fract (α * ↑n) = α * ↑n - int.nat_abs (α * ↑n), from sorry,
    have h3 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
  },
  have h4 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n),
  {
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : int.fract (α * ↑m) = α * ↑m - int.nat_abs (α * ↑m), from sorry,
    have h2 : int.fract (α * ↑n) = α * ↑n - int.nat_abs (α * ↑n), from sorry,
    have h3 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
  },
  have h5 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n),
  {
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : int.fract (α * ↑m) = α * ↑m - int.nat_abs (α * ↑m), from sorry,
    have h2 : int.fract (α * ↑n) = α * ↑n - int.nat_abs (α * ↑n), from sorry,
    have h3 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
  },
  have h6 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n),
  {
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : int.fract (α * ↑m) = α * ↑m - int.nat_abs (α * ↑m), from sorry,
    have h2 : int.fract (α * ↑n) = α * ↑n - int.nat_abs (α * ↑n), from sorry,
    have h3 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
  },
  have h7 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n),
  {
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : int.fract (α * ↑m) = α * ↑m - int.nat_abs (α * ↑m), from sorry,
    have h2 : int.fract (α * ↑n) = α * ↑n - int.nat_abs (α * ↑n), from sorry,
    have h3 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
  },
  have h8 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n),
  {
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : int.fract (α * ↑m) = α * ↑m - int.nat_abs (α * ↑m), from sorry,
    have h2 : int.fract (α * ↑n) = α * ↑n - int.nat_abs (α * ↑n), from sorry,
    have h3 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
  },
  have h9 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n),
  {
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : int.fract (α * ↑m) = α * ↑m - int.nat_abs (α * ↑m), from sorry,
    have h2 : int.fract (α * ↑n) = α * ↑n - int.nat_abs (α * ↑n), from sorry,
    have h3 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
  },
  have h10 : ∀ m n : ℤ, m ≠ n → int.fract (α * ↑m) ≠ int.fract (α * ↑n),
  {
    assume (m n : ℤ) (hmn : m ≠ n),
    have h1 : int.fract (α * ↑m) = α * ↑m - int.nat_abs (α * ↑m), from sorry,
    have h2 : int.fract (α * ↑n) = α * ↑n - int.nat_abs (α * ↑n), from sorry,
    have h3 : int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
    show int.fract (α * ↑m) ≠ int.fract (α * ↑n), from sorry,
  },
  have h11 : ∀
end --Needs more than 2000 tokens!

--OUTPUT 5
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h2 : ∀ i : ℤ, int.fract (α * ↑i) ∈ Icc 0 1, from sorry,
  have h3 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h4 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h5 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h6 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h7 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h8 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h9 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h10 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h11 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h12 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h13 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h14 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h15 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h16 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h17 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h18 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h19 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h20 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h21 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h22 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h23 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h24 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h25 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h26 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h27 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h28 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h29 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h30 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h31 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h32 : ∀ i : ℤ, ∃ m : ℤ, int.fract (α * ↑i) ∈ Icc 0 1 ∧ int.fract (α * ↑i) = int.fract (α * ↑m), from sorry,
  have h33 : ∀ i : ℤ, ∃ m
end --Needs more than 2000 tokens!

--OUTPUT 6
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → set.finite {i, j} := sorry,
  have h2 : ∀ i j : ℤ, i ≠ j → {int.fract (α * ↑i), int.fract (α * ↑j)} ≠ {0} := sorry,
  have h3 : ∀ i j : ℤ, i ≠ j → (set.finite {int.fract (α * ↑i), int.fract (α * ↑j)}) ∧ 
    ({int.fract (α * ↑i), int.fract (α * ↑j)} ≠ {0}) := sorry,
  have h4 : ∀ i j : ℤ, i ≠ j → (set.finite {int.fract (α * ↑i), int.fract (α * ↑j)}) ∧ 
    (int.fract (α * ↑i) ≠ int.fract (α * ↑j)) := sorry,

  have h5 : ∀ i : ℤ, (λ j, int.fract (α * ↑j)) i ∈ set.Icc 0 1 := sorry,
  have h6 : ∀ i : ℤ, (λ j, int.fract (α * ↑j)) i ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) := sorry,

  have h7 : ∀ (x : ℤ) (y : ℤ), x ≠ y → ∃ (a : ℤ) (b : ℤ), abs (a - b) < 1 := sorry,
  have h8 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), abs (a - b) < 1 := sorry,
  have h9 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) := sorry,
  have h10 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) ∧ (a * α - b * α > 0) := sorry,

  have h11 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) ∧ (a * α - b * α > 0) ∧ 
    (int.fract (a * α) - int.fract (b * α) = a * α - b * α) := sorry,
  have h12 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) ∧ (int.fract (a * α) - int.fract (b * α) = a * α - b * α) := sorry,

  have h13 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) ∧ (int.fract (a * α) - int.fract (b * α) = a * α - b * α) ∧ 
    (int.fract (a * α) - int.fract (b * α) ≠ 0) := sorry,

  have h14 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) ∧ (int.fract (a * α) - int.fract (b * α) = a * α - b * α) ∧ 
    (int.fract (a * α) - int.fract (b * α) ≠ 0) ∧ (int.fract (a * α) ≠ int.fract (b * α)) := sorry,

  have h15 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) ∧ (int.fract (a * α) - int.fract (b * α) = a * α - b * α) ∧ 
    (int.fract (a * α) - int.fract (b * α) ≠ 0) ∧ (int.fract (a * α) ≠ int.fract (b * α)) ∧ 
    (int.fract (a * α) - int.fract (b * α) ∈ set.Icc 0 1) := sorry,

  have h16 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) ∧ (int.fract (a * α) - int.fract (b * α) = a * α - b * α) ∧ 
    (int.fract (a * α) - int.fract (b * α) ≠ 0) ∧ (int.fract (a * α) ≠ int.fract (b * α)) ∧ 
    (int.fract (a * α) - int.fract (b * α) ∈ set.Icc 0 1) ∧ 
    (int.fract (a * α) - int.fract (b * α) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))) := sorry,

  have h17 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) ∧ (int.fract (a * α) - int.fract (b * α) = a * α - b * α) ∧ 
    (int.fract (a * α) - int.fract (b * α) ≠ 0) ∧ (int.fract (a * α) ≠ int.fract (b * α)) ∧ 
    (int.fract (a * α) - int.fract (b * α) ∈ set.Icc 0 1) ∧ (int.fract (a * α) - int.fract (b * α) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))) ∧ 
    (int.fract (a * α) - int.fract (b * α) ∈ set.Icc 0 1) := sorry,

  have h18 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) ∧ (int.fract (a * α) - int.fract (b * α) = a * α - b * α) ∧ 
    (int.fract (a * α) - int.fract (b * α) ≠ 0) ∧ (int.fract (a * α) ≠ int.fract (b * α)) ∧ 
    (int.fract (a * α) - int.fract (b * α) ∈ set.Icc 0 1) ∧ (int.fract (a * α) - int.fract (b * α) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))) ∧ 
    (int.fract (a * α) - int.fract (b * α) ∈ set.Icc 0 1) ∧ (int.fract (a * α) - int.fract (b * α) ∈ closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ))) := sorry,

  have h19 : ∀ (x : ℤ), ∃ (a : ℤ) (b : ℤ), (a ≠ b) ∧ (abs (a - b) < 1) ∧ (int.
end --Needs more than 2000 tokens!

--OUTPUT 7
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from by {
    assume (i : ℤ) (j : ℤ) (h1 : i ≠ j),
    have h2 : (int.fract (α * ↑i)) = α * ↑i - (int.nat_abs (α * ↑i)), from sorry,
    have h3 : (int.fract (α * ↑j)) = α * ↑j - (int.nat_abs (α * ↑j)), from sorry,
    have h4 : (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
    show (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  },
  have h2 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h3 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,

  have h4 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from
    by {
      assume (i : ℤ) (j : ℤ) (h4 : i ≠ j),
      have h5 : (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
      show (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
    },
  have h5 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h6 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h7 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h8 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h9 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h10 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h11 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h12 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h13 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h14 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h15 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h16 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h17 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h18 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h19 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h20 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h21 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h22 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h23 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h24 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h25 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h26 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h27 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h28 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h29 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h30 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h31 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h32 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h33 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h34 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h35 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h36 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

  have h37 : ∀ i j : ℤ, i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,

end --Needs more than 2000 tokens!

--OUTPUT 8
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 :=
begin
  have h1 : ∀ (i j : ℤ), i ≠ j → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h2 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → (int.fract (α * ↑j)) ≠ (int.fract (α * ↑i)), from sorry,
  have h3 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → (int.fract (α * ↑i)) ≠ (int.fract (α * ↑j)), from sorry,
  have h4 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → (int.fract (α * ↑j)) ≠ (int.fract (α * ↑i)), from sorry,
  have h5 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h6 : ∀ i j : ℤ, i ≠ j → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,

  have h7 : ∀ i : ℤ, ∃ j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h8 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,

  have h9 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,

  have h10 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,
  have h11 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,

  have h12 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,

  have h13 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h14 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h15 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,
  have h16 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,

  have h17 : ∀ i : ℤ, ∃ j : ℤ, j ≠ i → int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,
  have h18 : ∀ i : ℤ, ∃ j : ℤ, int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,
  have h19 : ∀ i : ℤ, ∃ j : ℤ, j ≠ i → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h20 : ∀ i : ℤ, ∃ j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,

  have h21 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,
  have h22 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,
  have h23 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h24 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,

  have h25 : ∀ i : ℤ, ∃ j : ℤ, j ≠ i → int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,

  have h26 : ∀ i : ℤ, ∃ j : ℤ, j ≠ i → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h27 : ∀ i : ℤ, ∃ j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,

  have h28 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,

  have h29 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,
  have h30 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,

  have h31 : ∀ i : ℤ, ∃ j : ℤ, j ≠ i → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h32 : ∀ i : ℤ, ∃ j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,

  have h33 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,
  have h34 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,

  have h35 : ∀ i : ℤ, ∃ j : ℤ, j ≠ i → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h36 : ∀ i : ℤ, ∃ j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h37 : ∃ i : ℤ, ∀ j : ℤ, j ≠ i → int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,
  have h38 : ∃ i : ℤ, ∀ j : ℤ, int.fract (α * ↑j) ≠ int.fract (α * ↑i), from sorry,

  have h39 : ∀ i : ℤ, ∃ j : ℤ, j ≠ i → int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,
  have h40 : ∀ i : ℤ, ∃ j : ℤ, int.fract (α * ↑i) ≠ int.fract (α * ↑j), from sorry,

  have h41 : ∃ i : ℤ
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
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from sorry,
  have h2 : (A ∩ B) ⊆ A, from sorry,
  have h3 : (A ∩ B) ⊆ S, from sorry,
  show (A ∩ B) ∈  𝒫 S, from sorry,
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
  calc (x + y)^2 = (x+y)*(x+y) : by sorry
  ... = x*(x+y) + y*(x+y) : by sorry
  ... = x*x + x*y + y*x + y*y : by sorry
  ... = x^2 + 2*x*y + y^2 : by sorry,
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
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from sorry,
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from sorry,

  have h3 : ∀ a : G, ∃! x : G, a * x = a, from sorry,
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from sorry,

  have h5 : ∀ a : G, classical.some (h3 a) = (1 : G), from sorry,
  have h6 : ∀ a : G, classical.some (h4 a) = (1 : G), from sorry,

  show ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a, from by {
    use (1 : G),
    have h7 : ∀ e : G, (∀ a : G, e * a = a ∧ a * e = a) → e = 1, from by {
      assume (e : G) (h7 : ∀ a : G, e * a = a ∧ a * e = a),
      have h8 : ∀ a : G, e = classical.some (h3 a), from sorry,
      have h9 : ∀ a : G, e = classical.some (h4 a), from sorry,
      show e = (1 : G), from sorry,     
    },
    sorry,
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
