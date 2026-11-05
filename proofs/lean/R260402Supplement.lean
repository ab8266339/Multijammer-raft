import Mathlib

/-!
Supplementary boundary and parity facts for accepted paper WCL2026-2945.
Checked on DESKTOP-BRJD313 with Lean/mathlib v4.31.0.
This module does not claim the full LLN limit, finite-ray decomposition,
probabilistic derivation of the binomial model, or Raft protocol safety.
-/

namespace R260402Supplement

open Finset

/-- The beta = 1 single-jammer boundary is the perpendicular bisector.
Coordinates put the leader at (0,0) and the jammer at (d,0). -/
theorem apollonius_beta_one_line {d x y : ℝ} (hd : d ≠ 0) :
    (x - d) ^ 2 + y ^ 2 = x ^ 2 + y ^ 2 ↔ x = d / 2 := by
  constructor
  · intro h
    have hz : d * (d - 2 * x) = 0 := by nlinarith
    have he := (mul_eq_zero.mp hz).resolve_left hd
    linarith
  · intro h
    rw [h]
    ring

/-- For odd total node count 2m+1, there are 2m followers. The successful
half-binomial tail includes the central coefficient. Valid also at m=0. -/
theorem quorum_half_odd_symmetry (m : ℕ) :
    2 * ∑ k ∈ Ico m (2 * m + 1), (2 * m).choose k =
      2 ^ (2 * m) + (2 * m).choose m := by
  have hlen : 2 * m + 1 - (m + 1) = m := by omega
  have h1 : ∑ k ∈ Ico (m + 1) (2 * m + 1), (2 * m).choose k =
      ∑ i ∈ range m, (2 * m).choose (m + 1 + i) := by
    rw [sum_Ico_eq_sum_range, hlen]
  have h2 : ∀ i ∈ range m,
      (2 * m).choose (m + 1 + i) = (2 * m).choose (m - 1 - i) := by
    intro i hi
    rw [mem_range] at hi
    rw [← Nat.choose_symm (by omega : m + 1 + i ≤ 2 * m)]
    congr 1
    omega
  have h3 : ∑ i ∈ range m, (2 * m).choose (m - 1 - i) =
      ∑ i ∈ range m, (2 * m).choose i :=
    sum_range_reflect (fun j => (2 * m).choose j) m
  have hsym : ∑ k ∈ Ico (m + 1) (2 * m + 1), (2 * m).choose k =
      ∑ i ∈ range m, (2 * m).choose i := by
    rw [h1, sum_congr rfl h2, h3]
  have htotal : ∑ k ∈ range (2 * m + 1), (2 * m).choose k =
      2 ^ (2 * m) := Nat.sum_range_choose (2 * m)
  have hsplit : (∑ k ∈ range m, (2 * m).choose k) +
      (∑ k ∈ Ico m (2 * m + 1), (2 * m).choose k) =
      ∑ k ∈ range (2 * m + 1), (2 * m).choose k := by
    rw [range_eq_Ico, range_eq_Ico]
    exact sum_Ico_consecutive _ (by omega) (by omega)
  have htail : (2 * m).choose m +
      (∑ k ∈ Ico (m + 1) (2 * m + 1), (2 * m).choose k) =
      ∑ k ∈ Ico m (2 * m + 1), (2 * m).choose k := by
    have h := sum_Ico_consecutive (fun k => (2 * m).choose k)
      (show m ≤ m + 1 by omega) (show m + 1 ≤ 2 * m + 1 by omega)
    simpa using h
  omega

/-- Numerical binomial-tail expression at p=1/2 for an odd total node
count. This is an algebraic expression, not a probability space. -/
noncomputable def oddHalfQuorum (m : ℕ) : ℝ :=
  (∑ k ∈ Ico m (2 * m + 1), (2 * m).choose k : ℕ) / 2 ^ (2 * m)

/-- The precise odd-node correction missing from the old symmetry file. -/
theorem odd_half_quorum_exact (m : ℕ) :
    oddHalfQuorum m =
      1 / 2 + ((2 * m).choose m : ℝ) / (2 * 2 ^ (2 * m)) := by
  have h : (2 : ℝ) * (∑ k ∈ Ico m (2 * m + 1), (2 * m).choose k : ℕ) =
      2 ^ (2 * m) + ((2 * m).choose m : ℝ) := by
    exact_mod_cast quorum_half_odd_symmetry m
  unfold oddHalfQuorum
  have hp : (2 : ℝ) ^ (2 * m) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- For every finite odd total node count the half-probability expression
is strictly greater than 1/2, despite converging to 1/2 asymptotically. -/
theorem odd_half_quorum_gt_half (m : ℕ) : (1 : ℝ) / 2 < oddHalfQuorum m := by
  rw [odd_half_quorum_exact]
  have hc : 0 < (2 * m).choose m := Nat.choose_pos (by omega)
  have hcr : (0 : ℝ) < ((2 * m).choose m : ℝ) := by exact_mod_cast hc
  have hterm : (0 : ℝ) < ((2 * m).choose m : ℝ) / (2 * 2 ^ (2 * m)) :=
    div_pos hcr (by positivity)
  linarith

#print axioms apollonius_beta_one_line
#print axioms quorum_half_odd_symmetry
#print axioms odd_half_quorum_exact
#print axioms odd_half_quorum_gt_half

end R260402Supplement
