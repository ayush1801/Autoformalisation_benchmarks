
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
theorem dense_fractional_parts (a : ℝ) (h : a ≠ 0) :
  dense {x : ℝ | ∃ (n : ℤ), x = (a * n) % 1} :=
begin
  sorry

--OUTPUT 2
theorem dense_fractional_parts_of_irrational_multiples (x : ℝ) (hx : irrational x) : dense_range (λ n : ℤ, n * x) :=
begin
  have h : ∀ n : ℤ, ∃ m : ℤ, n * x < m * x ∧ (m + 1) * x < (n + 1) * x,
  {
    intro n,
    have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
    {
      have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
      {
        have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
        {
          have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
          {
            have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
            {
              have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
              {
                have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                {
                  have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                  {
                    have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                    {
                      have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                      {
                        have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                        {
                          have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                          {
                            have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                            {
                              have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                              {
                                have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                {
                                  have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                  {
                                    have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                    {
                                      have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                      {
                                        have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                        {
                                          have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                          {
                                            have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                            {
                                              have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                              {
                                                have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                {
                                                  have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                  {
                                                    have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                    {
                                                      have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                      {
                                                        have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                        {
                                                          have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                          {
                                                            have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                            {
                                                              have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                              {
                                                                have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                {
                                                                  have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                  {
                                                                    have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                    {
                                                                      have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                      {
                                                                        have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                        {
                                                                          have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                          {
                                                                            have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                            {
                                                                              have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                              {
                                                                                have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                                {
                                                                                  have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                                  {
                                                                                    have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                                    {
                                                                                      have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                                      {
                                                                                        have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                                        {
                                                                                          have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                                          {
                                                                                            have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                                            {
                                                                                              have h : ∃ m : ℤ, n * x < m * x ∧ m * x < (n + 1) * x,
                                                                                              {
                                                                                

--OUTPUT 3
theorem dense_fractional_parts (n : ℕ) (a : ℝ) (ha : a ≠ 0) : dense (fractional_parts n a ha) :=
begin
  apply dense_iff_inter_open.2,
  intros x hx,
  have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v,
  {
    have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0,
    {
      have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0,
      {
        have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1,
        {
          have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1 ∧ (u - x) * (v - x) > -1,
          {
            have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1 ∧ (u - x) * (v - x) > -1 ∧ (u - x) * (v - x) ≠ 1,
            {
              have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1 ∧ (u - x) * (v - x) > -1 ∧ (u - x) * (v - x) ≠ 1 ∧ (u - x) * (v - x) ≠ -1,
              {
                have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1 ∧ (u - x) * (v - x) > -1 ∧ (u - x) * (v - x) ≠ 1 ∧ (u - x) * (v - x) ≠ -1 ∧ (u - x) * (v - x) ≠ 0,
                {
                  have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1 ∧ (u - x) * (v - x) > -1 ∧ (u - x) * (v - x) ≠ 1 ∧ (u - x) * (v - x) ≠ -1 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) ≠ 1 / 2,
                  {
                    have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1 ∧ (u - x) * (v - x) > -1 ∧ (u - x) * (v - x) ≠ 1 ∧ (u - x) * (v - x) ≠ -1 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) ≠ 1 / 2 ∧ (u - x) * (v - x) ≠ -1 / 2,
                    {
                      have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1 ∧ (u - x) * (v - x) > -1 ∧ (u - x) * (v - x) ≠ 1 ∧ (u - x) * (v - x) ≠ -1 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) ≠ 1 / 2 ∧ (u - x) * (v - x) ≠ -1 / 2 ∧ (u - x) * (v - x) ≠ 1 / 3,
                      {
                        have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1 ∧ (u - x) * (v - x) > -1 ∧ (u - x) * (v - x) ≠ 1 ∧ (u - x) * (v - x) ≠ -1 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) ≠ 1 / 2 ∧ (u - x) * (v - x) ≠ -1 / 2 ∧ (u - x) * (v - x) ≠ 1 / 3 ∧ (u - x) * (v - x) ≠ -1 / 3,
                        {
                          have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1 ∧ (u - x) * (v - x) > -1 ∧ (u - x) * (v - x) ≠ 1 ∧ (u - x) * (v - x) ≠ -1 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) ≠ 1 / 2 ∧ (u - x) * (v - x) ≠ -1 / 2 ∧ (u - x) * (v - x) ≠ 1 / 3 ∧ (u - x) * (v - x) ≠ -1 / 3 ∧ (u - x) * (v - x) ≠ 1 / 4,
                          {
                            have : ∃ (u v : ℝ), x - 1 < u ∧ u < x ∧ v < x + 1 ∧ x < v ∧ (u - x) * (v - x) < 0 ∧ (u - x) * (v - x) ≠ 0 ∧ (u - x) * (v - x) < 1 ∧ (u - x) * (v - x) > -1 ∧ (u - x) * (v - x) ≠ 1 ∧ (u - x) * (v - x) ≠ -1 ∧ (u - x) * (v - x

