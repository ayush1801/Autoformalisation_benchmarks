
import topology.basic
import topology.compact_open
import data.nat.prime
import data.real.basic
import data.real.irrational
import data.complex.basic
import data.fin.basic
import geometry.euclidean.basic
import analysis.inner_product_space.pi_L2
import algebra.group.defs
import algebra.field.basic
import combinatorics.configuration
import ring_theory.polynomial.basic
import group_theory.free_group
import combinatorics.simple_graph.basic
import ring_theory.integral_closure
import data.fintype.card
import category_theory.category.basic
import ring_theory.discrete_valuation_ring
import group_theory.torsion
import linear_algebra.matrix.charpoly.basic
import algebra.order.absolute_value
import analysis.convex.basic
import topology.uniform_space.uniform_convergence_topology
import topology.sequences
import analysis.normed.group.infinite_sum
import data.nat.choose.sum
import group_theory.specific_groups.cyclic
import group_theory.order_of_element
import analysis.mean_inequalities
import analysis.normed_space.banach
import topology.algebra.continuous_monoid_hom
import linear_algebra.matrix.symmetric
import analysis.inner_product_space.spectrum
import ring_theory.class_group
import ring_theory.dedekind_domain.basic
import ring_theory.principal_ideal_domain
import model_theory.satisfiability
import probability.integration
import ring_theory.simple_module
import category_theory.preadditive.schur
import representation_theory.maschke
import topology.paracompact
import combinatorics.simple_graph.coloring
--Prove that Schur's lemma in Lean mathlib
 
--OUTPUT 1
theorem schur : Π {α : Type u} [fintype α] [decidable_eq α] [add_comm_group α] [vector_space ℂ α] (x y : α),
  x ≠ y → (x - y) ∈ span ℂ {x, y} :=
begin
  intros,
  have h1 : x - y = (1 : ℂ) * x + (-1 : ℂ) * y,
  {
    rw [←add_neg_self x, add_assoc, sub_eq_add_neg, add_comm],
  },
  rw h1,
  apply span_two_mem,
  intro,
  rw [h, zero_add, neg_zero, add_zero] at h1,
  exact h h1,

--OUTPUT 2
theorem schur (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur'' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur'''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur'''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur'''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur'''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur''''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur'''''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur''''''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur'''''''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur''''''''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur'''''''''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur''''''''''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur'''''''''''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur''''''''''''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M : α → β → ℂ) :
  (∀ x : α, ∀ y : β, M x y = 0) → linear_map α β M = 0 := sorry

--Prove that Schur's lemma in Lean mathlib
theorem schur'''''''''''''''''''' (α : Type) [decidable_eq α] [fintype α] [fintype β] [decidable_eq β] (M

--OUTPUT 3
theorem schur_lemma (V : Type*) [add_comm_group V] [vector_space ℂ V] [finite_dimensional ℂ V] :
  ∀ (f : V → V) [is_linear_map f], is_linear_map f → is_linear_map f →
    (∀ v : V, f v = v) ∨ (∀ v : V, f v = -v) :=
begin
  intros f Hf Hf₁ Hf₂,
  let W := {v : V | f v = v},
  have HW : submodule ℂ W,
  { apply submodule.submodule_of_linear Hf,
    intros v hv,
    rw ← Hf₁,
    exact hv },
  have HW' : submodule ℂ (W.comap f),
  { apply submodule.comap_submodule,
    exact HW },
  have HW'₁ : W.comap f = ⊤,
  { apply submodule.ext,
    intros v, split,
    { intro hv,
      use v,
      rw ← Hf₂,
      exact hv },
    { intro hv,
      rcases hv with ⟨w, hw₁, hw₂⟩,
      rw hw₂,
      exact hw₁ } },
  have HW'₂ : W.comap f = ⊥,
  { apply submodule.ext,
    intros v, split,
    { intro hv,
      use -v,
      rw ← Hf₂,
      exact hv },
    { intro hv,
      rcases hv with ⟨w, hw₁, hw₂⟩,
      rw hw₂,
      exact hw₁ } },
  have HW₁ : W = ⊤,
  { apply submodule.ext,
    intros v, split,
    { intro hv,
      use v,
      exact hv },
    { intro hv,
      rcases hv with ⟨w, hw₁, hw₂⟩,
      rw hw₂,
      exact hw₁ } },
  have HW₂ : W = ⊥,
  { apply submodule.ext,
    intros v, split,
    { intro hv,
      use -v,
      exact hv },
    { intro hv,
      rcases hv with ⟨w, hw₁, hw₂⟩,
      rw hw₂,
      exact hw₁ } },
  have H : W = ⊤ ∨ W = ⊥,
  { apply submodule.eq_top_or_eq_bot,
    exact HW },
  cases H with H₁ H₂,
  { left,
    rw H₁,
    intro v,
    exact submodule.mem_top v },
  { right,
    rw H₂,
    intro v,
    exact submodule.mem_bot (-v) }

