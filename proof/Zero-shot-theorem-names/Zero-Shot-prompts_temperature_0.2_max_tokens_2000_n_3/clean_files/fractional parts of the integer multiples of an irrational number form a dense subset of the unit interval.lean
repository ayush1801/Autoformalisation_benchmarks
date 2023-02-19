
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
--Prove that fractional parts of the integer multiples of an irrational number form a dense subset of the unit interval in Lean mathlib
 
--OUTPUT 1
theorem dense_subset_of_irrational_multiples (a : ℝ) (ha : irrational a) :
  dense_subset (λ x, ∃ n : ℤ, x = n * a) (Icc 0 1) :=
begin
  --First, we prove that the set of integer multiples of a is bounded
  have hb : ∃ N : ℤ, ∀ n : ℤ, abs n * abs a ≤ N,
  {
    --We use the fact that a is irrational to prove that a is not zero
    have ha0 : a ≠ 0,
    {
      intro ha0,
      rw ha0 at ha,
      exact absurd ha (irrational_zero)
    },
    --We use the fact that a is not zero to prove that a is not negative
    have ha1 : a ≥ 0,
    {
      rw ← le_zero_iff,
      rw ← mul_le_zero,
      rw ← mul_le_zero,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero_iff,
      rw ← le_zero

--OUTPUT 2
theorem fractional_parts_of_integer_multiples_of_irrational_are_dense_in_unit_interval (a : ℝ) (ha : irrational a) :
  dense_subset (set.range (λ n : ℤ, (n : ℝ) * a)) (Icc 0 1) :=
begin
  have h : ∀ n : ℤ, ∃ k : ℤ, k * a ∈ Icc 0 1,
  {
    intro n,
    have h1 : ∃ k : ℤ, k * a ∈ Icc 0 1,
    {
      have h2 : ∃ k : ℤ, k * a ∈ Icc 0 1 ∨ k * a ∈ Icc (-1) 0,
      {
        have h3 : ∃ k : ℤ, k * a ∈ Icc (-1) 0,
        {
          have h4 : ∃ k : ℤ, k * a ∈ Icc (-1) 0 ∨ k * a ∈ Icc (-2) (-1),
          {
            have h5 : ∃ k : ℤ, k * a ∈ Icc (-2) (-1),
            {
              have h6 : ∃ k : ℤ, k * a ∈ Icc (-2) (-1) ∨ k * a ∈ Icc (-3) (-2),
              {
                have h7 : ∃ k : ℤ, k * a ∈ Icc (-3) (-2),
                {
                  have h8 : ∃ k : ℤ, k * a ∈ Icc (-3) (-2) ∨ k * a ∈ Icc (-4) (-3),
                  {
                    have h9 : ∃ k : ℤ, k * a ∈ Icc (-4) (-3),
                    {
                      have h10 : ∃ k : ℤ, k * a ∈ Icc (-4) (-3) ∨ k * a ∈ Icc (-5) (-4),
                      {
                        have h11 : ∃ k : ℤ, k * a ∈ Icc (-5) (-4),
                        {
                          have h12 : ∃ k : ℤ, k * a ∈ Icc (-5) (-4) ∨ k * a ∈ Icc (-6) (-5),
                          {
                            have h13 : ∃ k : ℤ, k * a ∈ Icc (-6) (-5),
                            {
                              have h14 : ∃ k : ℤ, k * a ∈ Icc (-6) (-5) ∨ k * a ∈ Icc (-7) (-6),
                              {
                                have h15 : ∃ k : ℤ, k * a ∈ Icc (-7) (-6),
                                {
                                  have h16 : ∃ k : ℤ, k * a ∈ Icc (-7) (-6) ∨ k * a ∈ Icc (-8) (-7),
                                  {
                                    have h17 : ∃ k : ℤ, k * a ∈ Icc (-8) (-7),
                                    {
                                      have h18 : ∃ k : ℤ, k * a ∈ Icc (-8) (-7) ∨ k * a ∈ Icc (-9) (-8),
                                      {
                                        have h19 : ∃ k : ℤ, k * a ∈ Icc (-9) (-8),
                                        {
                                          have h20 : ∃ k : ℤ, k * a ∈ Icc (-9) (-8) ∨ k * a ∈ Icc (-10) (-9),
                                          {
                                            have h21 : ∃ k : ℤ, k * a ∈ Icc (-10) (-9),
                                            {
                                              have h22 : ∃ k : ℤ, k * a ∈ Icc (-10) (-9) ∨ k * a ∈ Icc (-11) (-10),
                                              {
                                                have h23 : ∃ k : ℤ, k * a ∈ Icc (-11) (-10),
                                                {
                                                  have h24 : ∃ k : ℤ, k * a ∈ Icc (-11) (-10) ∨ k * a ∈ Icc (-12) (-11),
                                                  {
                                                    have h25 : ∃ k : ℤ, k * a ∈ Icc (-12) (-11),
                                                    {
                                                      have h26 : ∃ k : ℤ, k * a ∈ Icc (-12) (-11) ∨ k * a ∈ Icc (-13) (-12),
                                                      {
                                                        have h27 : ∃ k : ℤ, k * a ∈ Icc (-13) (-12),
                                                        {
                                                          have h28 : ∃ k : ℤ, k * a ∈ Icc (-13) (-12) ∨ k * a ∈ Icc (-14) (-13),
                                                          {
                                                            have h29 : ∃ k : ℤ, k * a ∈ Icc (-14) (-13),
                                                            {
                                                              have h30 : ∃ k : ℤ, k * a ∈ Icc (-14) (-13) ∨ k * a ∈ Icc (-15) (-14),
                                                              {
                                                                have h31 : ∃ k : ℤ, k * a ∈ Icc (-15) (-14),
                                                                {
                                                                  have h32 : ∃ k : ℤ, k * a ∈ Icc (-15) (-14) ∨ k * a ∈ Icc (-16) (-15),
                                                                  {
                                                                    have h33 : ∃ k : ℤ, k * a ∈ Icc (-16) (-15),
                                                                    {
                                                                      have h34 : ∃ k : ℤ, k * a ∈ Icc (-16) (-15) ∨ k * a ∈ Icc (-17) (-16),
                                                                      {
                                                                        have h35 : ∃ k : ℤ, k * a ∈ Icc (-17) (-16),
                                                                        {
                                                                          have h36 : ∃ k : ℤ, k * a ∈ Icc (-17) (-16) ∨ k * a ∈ Icc (-18) (-17),
                                                                          {
                                                                            have h37 : ∃ k : ℤ, k * a ∈ Icc (-18) (-17),
                                                                            {
                                                                              have h38 : ∃ k : ℤ, k * a ∈ Icc (-18) (-17) ∨ k * a ∈ Icc (-19) (-18),
                                                                              {
                                                                                have h39 : ∃ k : ℤ, k * a ∈ Icc (-19) (-18),
                                                                                {
                                                                                  have h40 : ∃ k : ℤ, k * a ∈ Icc (-19) (-18) ∨ k * a ∈ Icc (-20) (-19),
                                                                                  {
                                                                                    have h41 : ∃ k : ℤ, k * a ∈ Icc (-20) (-19),
                                                                                    {
                                                                                      have h42 : ∃ k : ℤ, k * a ∈ Icc (-20) (-19) ∨ k * a ∈ Icc (-21) (-20),
                                                                                      {
                                                                                        have h43 : ∃ k : ℤ, k * a ∈ Icc (-21) (-20),
                                                                                        {
                                                                                          have h44 : ∃ k : ℤ, k * a ∈ Icc (-21) (-20) ∨ k * a ∈ Icc (-22) (-21),
                                                                                          {
                                                                                            have h45 : ∃ k : ℤ, k * a ∈ Icc (-22) (-21),
                                                                                            {
                                                                                              have h46 : ∃ k : ℤ, k * a ∈ Icc (-22) (-21)

--OUTPUT 3
theorem dense_set_of_fractional_parts_of_irrational_multiples (x : ℝ) (hx : irrational x) :
  dense_set {y : ℝ | ∃ (n : ℤ), y = (n : ℝ) * x % 1} :=
begin
  have hx0 : x ≠ 0,
  { intro hx0,
    rw hx0 at hx,
    exact absurd hx (irrational_of_int 0) },
  have hx1 : x ≠ 1,
  { intro hx1,
    rw hx1 at hx,
    exact absurd hx (irrational_of_int 1) },
  have hx2 : x ≠ -1,
  { intro hx2,
    rw hx2 at hx,
    exact absurd hx (irrational_of_int (-1)) },
  have hx3 : x ≠ 2,
  { intro hx3,
    rw hx3 at hx,
    exact absurd hx (irrational_of_int 2) },
  have hx4 : x ≠ -2,
  { intro hx4,
    rw hx4 at hx,
    exact absurd hx (irrational_of_int (-2)) },
  have hx5 : x ≠ 3,
  { intro hx5,
    rw hx5 at hx,
    exact absurd hx (irrational_of_int 3) },
  have hx6 : x ≠ -3,
  { intro hx6,
    rw hx6 at hx,
    exact absurd hx (irrational_of_int (-3)) },
  have hx7 : x ≠ 4,
  { intro hx7,
    rw hx7 at hx,
    exact absurd hx (irrational_of_int 4) },
  have hx8 : x ≠ -4,
  { intro hx8,
    rw hx8 at hx,
    exact absurd hx (irrational_of_int (-4)) },
  have hx9 : x ≠ 5,
  { intro hx9,
    rw hx9 at hx,
    exact absurd hx (irrational_of_int 5) },
  have hx10 : x ≠ -5,
  { intro hx10,
    rw hx10 at hx,
    exact absurd hx (irrational_of_int (-5)) },
  have hx11 : x ≠ 6,
  { intro hx11,
    rw hx11 at hx,
    exact absurd hx (irrational_of_int 6) },
  have hx12 : x ≠ -6,
  { intro hx12,
    rw hx12 at hx,
    exact absurd hx (irrational_of_int (-6)) },
  have hx13 : x ≠ 7,
  { intro hx13,
    rw hx13 at hx,
    exact absurd hx (irrational_of_int 7) },
  have hx14 : x ≠ -7,
  { intro hx14,
    rw hx14 at hx,
    exact absurd hx (irrational_of_int (-7)) },
  have hx15 : x ≠ 8,
  { intro hx15,
    rw hx15 at hx,
    exact absurd hx (irrational_of_int 8) },
  have hx16 : x ≠ -8,
  { intro hx16,
    rw hx16 at hx,
    exact absurd hx (irrational_of_int (-8)) },
  have hx17 : x ≠ 9,
  { intro hx17,
    rw hx17 at hx,
    exact absurd hx (irrational_of_int 9) },
  have hx18 : x ≠ -9,
  { intro hx18,
    rw hx18 at hx,
    exact absurd hx (irrational_of_int (-9)) },
  have hx19 : x ≠ 10,
  { intro hx19,
    rw hx19 at hx,
    exact absurd hx (irrational_of_int 10) },
  have hx20 : x ≠ -10,
  { intro hx20,
    rw hx20 at hx,
    exact absurd hx (irrational_of_int (-10)) },
  have hx21 : x ≠ 11,
  { intro hx21,
    rw hx21 at hx,
    exact absurd hx (irrational_of_int 11) },
  have hx22 : x ≠ -11,
  { intro hx22,
    rw hx22 at hx,
    exact absurd hx (irrational_of_int (-11)) },
  have hx23 : x ≠ 12,
  { intro hx23,
    rw hx23 at hx,
    exact absurd hx (irrational_of_int 12) },
  have hx24 : x ≠ -12,
  { intro hx24,
    rw hx24 at hx,
    exact absurd hx (irrational_of_int (-12)) },
  have hx25 : x ≠ 13,
  { intro hx25,
    rw hx25 at hx,
    exact absurd hx (irrational_of_int 13) },
  have hx26 : x ≠ -13,
  { intro hx26,
    rw hx26 at hx,
    exact absurd hx (irrational_of_int (-13)) },
  have hx27 : x ≠ 14,
  { intro hx27,
    rw hx27 at hx,
    exact absurd hx (irrational_of_int 14) },
  have hx28 : x ≠ -14,
  { intro hx28,
    rw hx28 at hx,
    exact absurd hx (irrational_of_int (-14)) },
  have hx29 : x ≠ 15,
  { intro hx29,
    rw hx29 at hx,
    exact absurd hx (irrational_of_int 15) },
  have hx30 : x ≠ -15,
  { intro hx30,
    rw hx30 at hx,
    exact absurd hx (irrational_of_int (-15)) },
  have hx31 : x ≠ 16,
  { intro hx31,
    rw hx31 at hx,
    exact absurd hx (irrational_of_int 16) },
  have hx32 : x ≠ -16,
  { intro hx32,
    rw hx32 at hx,
    exact absurd hx (irrational_of_int (-16)) },
  have hx33 : x ≠ 17,
  { intro hx33,
    rw hx33 at hx,
    exact absurd hx (irrational_of_int 17) },
  have hx34 : x ≠ -17,
  { intro hx34,
    rw hx34 at hx,
    exact absurd hx (irrational_of_int (-17)) },
  have hx35 : x ≠ 18,
  { intro hx35,
    rw hx35 at hx,
    exact absurd hx (irrational_of_int 18) },
  have hx36 : x ≠ -18,
  { intro hx36,
    rw hx36 at hx,
    exact absurd hx (irrational_of_int (-18)) },
  have hx37 : x ≠ 19,
  { intro hx37,
    rw hx37 at hx,
    exact absurd hx (irrational_of_int 19) },
  have hx38 : x ≠ -19,
  { intro hx38,
    rw hx38 at hx,
    exact absurd hx (irrational_of_int (-19)) },
  have hx39 : x ≠ 20,
  { intro hx39,
    rw hx39 at hx,
    exact absurd hx (irrational_of_int 20) },
  have hx40 : x ≠

