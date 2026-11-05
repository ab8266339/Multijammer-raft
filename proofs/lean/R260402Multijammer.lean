/-
Formalization of the core mathematical claims of R260402
"Raft-Based Wireless Blockchain Networks in the Presence of Multiple
Malicious Jammers" (IEEE WCL resubmission of WCL2026-1798).

  * Theorem 1    : uplink critical radius — with S = ∑ᵢ dᵢ^{-γ},
                   β ≤ r^{-γ}/S  ↔  r ≤ R_U = (βS)^{-1/γ}
  * Section II   : Raft quorum arithmetic — the leader counts itself, so
                   k follower acks put the entry on a strict majority of
                   the n servers iff k ≥ ⌊n/2⌋
  * Theorem 2    : N = 1 material —
                   (a) ray re-entry: past an on-ray jammer the DL
                       condition ((r-d)/r)^γ ≥ β holds iff
                       r ≥ d/(1-β^{1/γ})  (β < 1), so the ray-wise
                       success set is NOT radially connected;
                   (b) the boundary identity with c = β^{2/γ} ≠ 1 is
                       exactly the Apollonius circle of eq. (10)
  * Section V-C  : worst-case power — the linear form ∑ Pᵢcᵢ over the
                   simplex is maximised (and attained) by concentrating
                   the budget on the largest coefficient;
                   Poisson-PGF identity  ∑ e^{-μ}(μq)^k/k! = e^{-μ(1-q)}

Lean 4 + Mathlib (leanprover/lean4:v4.31.0).  This file is a proof
artifact and is NOT part of the manuscript.
-/
import Mathlib

set_option maxHeartbeats 1600000

namespace R260402

open Real Finset

/-! ### rpow monotonicity helper -/

/-- For positive bases and positive exponent, `x ^ γ ≤ y ^ γ ↔ x ≤ y`. -/
lemma rpow_le_rpow_iff_base {x y γ : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hγ : 0 < γ) : x ^ γ ≤ y ^ γ ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hxy
    rw [not_le] at hxy
    exact absurd h (not_le.mpr (Real.rpow_lt_rpow hy.le hxy hγ))
  · intro h
    exact Real.rpow_le_rpow hx.le h hγ.le

/-! ### Theorem 1 — uplink critical radius -/

/-- **Theorem 1 (paper eq. (8)).**  With `S = ∑ᵢ dᵢ^{-γ} > 0`, the uplink
mean-SINR condition `r^{-γ}/S ≥ β` holds iff `r ≤ R_U = (βS)^{-1/γ}`. -/
theorem uplink_critical_radius {γ β S r : ℝ}
    (hγ : 0 < γ) (hβ : 0 < β) (hS : 0 < S) (hr : 0 < r) :
    β ≤ r ^ (-γ) / S ↔ r ≤ (β * S) ^ (-(1 / γ)) := by
  have hβS : 0 < β * S := mul_pos hβ hS
  have hrγ : 0 < r ^ γ := Real.rpow_pos_of_pos hr γ
  have hRU : 0 < (β * S) ^ (-(1 / γ)) := Real.rpow_pos_of_pos hβS _
  have hexp : (-(1 / γ)) * γ = -1 := by field_simp
  have key : ((β * S) ^ (-(1 / γ))) ^ γ = 1 / (β * S) := by
    rw [← Real.rpow_mul hβS.le, hexp, Real.rpow_neg_one, one_div]
  rw [le_div_iff₀ hS, Real.rpow_neg hr.le, ← one_div, le_div_iff₀ hrγ,
    ← rpow_le_rpow_iff_base hr hRU hγ, key, le_div_iff₀ hβS, mul_comm]

/-! ### Raft quorum arithmetic (Section II, Proposition 1) -/

/-- **Corrected quorum count.**  In an `n`-server Raft group the leader
counts itself, so `k` follower acknowledgements place the entry on a
strict majority of the `n` servers (`2(k+1) > n`) iff `k ≥ ⌊n/2⌋`.
This is the `⌊n/2⌋` lower summation limit of paper eq. (12). -/
theorem quorum_followers_needed (n k : ℕ) :
    2 * (k + 1) > n ↔ n / 2 ≤ k := by omega

/-- The previously used threshold `⌈n/2⌉ = (n+1)/2` was strictly
stronger for odd `n`, demanding one more follower than the Raft
majority `⌊n/2⌋` needs. -/
theorem old_threshold_too_strong (m : ℕ) :
    (2 * m + 1 + 1) / 2 = (2 * m + 1) / 2 + 1 := by
  omega

/-! ### Theorem 2, N = 1 — ray re-entry (non-star-shapedness) -/

/-- **Re-entry radius (response letter, Comment 1).**  For a single
on-ray jammer at distance `d` and `β < 1`, a follower past the jammer
satisfies the DL condition `((r-d)/r)^γ ≥ β` iff
`r ≥ d/(1-β^{1/γ})`.  Together with failure just past the jammer this
shows the ray-wise success set re-enters, so it is not an interval. -/
theorem ray_reentry {γ β d r : ℝ} (hγ : 0 < γ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hd : 0 < d) (hr : d < r) :
    β ≤ ((r - d) / r) ^ γ ↔ d / (1 - β ^ (1 / γ)) ≤ r := by
  have hr0 : 0 < r := hd.trans hr
  have hrd : 0 < r - d := sub_pos.mpr hr
  have hk0 : 0 < β ^ (1 / γ) := Real.rpow_pos_of_pos hβ0 _
  have hk1 : β ^ (1 / γ) < 1 :=
    Real.rpow_lt_one hβ0.le hβ1 (by positivity)
  have h1k : 0 < 1 - β ^ (1 / γ) := sub_pos.mpr hk1
  have hkγ : (β ^ (1 / γ)) ^ γ = β := by
    rw [← Real.rpow_mul hβ0.le]
    rw [one_div, inv_mul_cancel₀ hγ.ne', Real.rpow_one]
  have hfracpos : 0 < (r - d) / r := div_pos hrd hr0
  constructor
  · intro h
    -- β ≤ ((r-d)/r)^γ  ⇒  β^{1/γ} ≤ (r-d)/r  ⇒  r(1-β^{1/γ}) ≥ d
    have h2 : β ^ (1 / γ) ≤ (r - d) / r := by
      have h3 : (β ^ (1 / γ)) ^ γ ≤ ((r - d) / r) ^ γ := by
        rw [hkγ]; exact h
      exact (rpow_le_rpow_iff_base (x := β ^ (1 / γ))
        (y := (r - d) / r) hk0 hfracpos hγ).mp h3
    rw [le_div_iff₀ hr0] at h2
    rw [div_le_iff₀ h1k]
    nlinarith
  · intro h
    have h2 : β ^ (1 / γ) ≤ (r - d) / r := by
      rw [div_le_iff₀ h1k] at h
      rw [le_div_iff₀ hr0]
      nlinarith
    have h3 := (rpow_le_rpow_iff_base (x := β ^ (1 / γ))
      (y := (r - d) / r) hk0 hfracpos hγ).mpr h2
    rwa [hkγ] at h3

/-- Just past the jammer the condition genuinely fails, for any
`β > 0`: close enough to the jammer, `((r-d)/r)^γ < β`.  Combined with
`ray_reentry` this is the non-star-shapedness of Theorem 2. -/
theorem failure_past_jammer {γ β d : ℝ} (hγ : 0 < γ) (hβ0 : 0 < β)
    (hd : 0 < d) :
    ∃ r > d, ((r - d) / r) ^ γ < β := by
  -- choose r with (r-d)/r < min 1 (β^{1/γ}) by taking r-d tiny
  set k := min (1 / 2) (β ^ (1 / γ) / 2) with hk
  have hβγ : 0 < β ^ (1 / γ) := Real.rpow_pos_of_pos hβ0 _
  have hk0 : 0 < k := lt_min (by norm_num) (by positivity)
  have hk1 : k < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have h1k : (0 : ℝ) < 1 - k := by linarith
  refine ⟨d / (1 - k), ?_, ?_⟩
  · rw [gt_iff_lt, lt_div_iff₀ h1k]
    nlinarith
  · have hr0 : 0 < d / (1 - k) := by positivity
    have hfrac : (d / (1 - k) - d) / (d / (1 - k)) = k := by
      have hd' : d ≠ 0 := hd.ne'
      have h1k' : (1 : ℝ) - k ≠ 0 := h1k.ne'
      field_simp
      ring
    rw [hfrac]
    have hkβ : k < β ^ (1 / γ) :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have h := Real.rpow_lt_rpow hk0.le hkβ hγ
    have hkγβ : (β ^ (1 / γ)) ^ γ = β := by
      rw [← Real.rpow_mul hβ0.le, one_div, inv_mul_cancel₀ hγ.ne',
        Real.rpow_one]
    rwa [hkγβ] at h

/-! ### Theorem 2, N = 1 — the Apollonius circle (paper eq. (10)) -/

/-- **Apollonius identity.**  With `c = β^{2/γ} ≠ 1`, the boundary locus
`(x-d)² + y² = c(x²+y²)` is exactly the circle centred at
`(d/(1-c), 0)` with squared radius `c d²/(1-c)²`. -/
theorem apollonius_circle {c d x y : ℝ} (hc : c ≠ 1) :
    (x - d) ^ 2 + y ^ 2 = c * (x ^ 2 + y ^ 2) ↔
      (x - d / (1 - c)) ^ 2 + y ^ 2 = c * d ^ 2 / (1 - c) ^ 2 := by
  have h1c : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have key : (x - d) ^ 2 + y ^ 2 - c * (x ^ 2 + y ^ 2)
      = (1 - c) * ((x - d / (1 - c)) ^ 2 + y ^ 2
        - c * d ^ 2 / (1 - c) ^ 2) := by
    field_simp
    ring
  constructor
  · intro h
    have h0 : (1 - c) * ((x - d / (1 - c)) ^ 2 + y ^ 2
        - c * d ^ 2 / (1 - c) ^ 2) = 0 := by
      rw [← key]; linarith
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact absurd h' h1c
    · linarith
  · intro h
    have h0 : (x - d) ^ 2 + y ^ 2 - c * (x ^ 2 + y ^ 2) = 0 := by
      rw [key]
      have : (x - d / (1 - c)) ^ 2 + y ^ 2 - c * d ^ 2 / (1 - c) ^ 2
          = 0 := by linarith
      rw [this, mul_zero]
    linarith

/-- The exponent bookkeeping behind eq. (10): `(β^{1/γ})² = β^{2/γ}`,
so the ratio `ρ₁ = β^{1/γ} r` squares to the `c` used above. -/
theorem beta_exponent_identity {γ β : ℝ} (hβ : 0 ≤ β) :
    (β ^ (1 / γ)) ^ (2 : ℕ) = β ^ (2 / γ) := by
  rw [← Real.rpow_natCast (β ^ (1 / γ)) 2, ← Real.rpow_mul hβ]
  congr 1
  push_cast
  ring

/-! ### Section V-C — worst-case power concentration (LP vertex) -/

/-- **Upper bound.**  Any budget split `P` with `∑ P = Ptot` satisfies
`∑ Pᵢcᵢ ≤ Ptot · max c`: the interference sum can never beat full
concentration on the largest coefficient. -/
theorem worst_case_upper_bound {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (P c : ι → ℝ)
    (hP : ∀ i ∈ s, 0 ≤ P i) :
    ∑ i ∈ s, P i * c i ≤ (∑ i ∈ s, P i) * s.sup' hs c := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  exact mul_le_mul_of_nonneg_left (Finset.le_sup' c hi) (hP i hi)

/-- **Attainment (the simplex vertex).**  Concentrating the whole budget
on a maximising coefficient realises the bound, so the LP optimum of
Section V-C sits at the all-power-on-nearest-jammer vertex. -/
theorem worst_case_attained {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hs : s.Nonempty) (c : ι → ℝ) (Ptot : ℝ) :
    ∃ P : ι → ℝ, (∀ i, 0 ≤ Ptot → 0 ≤ P i) ∧
      ∑ i ∈ s, P i = Ptot ∧
      ∑ i ∈ s, P i * c i = Ptot * s.sup' hs c := by
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_mem_eq_sup' hs c
  refine ⟨fun i => if i = j then Ptot else 0, ?_, ?_, ?_⟩
  · intro i hPt
    by_cases h : i = j <;> simp [h, hPt]
  · simp [Finset.sum_ite_eq' s j (fun _ => Ptot), hj]
  · rw [hjmax]
    have : ∀ i ∈ s, (if i = j then Ptot else 0) * c i
        = if i = j then Ptot * c j else 0 := by
      intro i _
      by_cases h : i = j <;> simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' s j
      (fun _ => Ptot * c j)]
    simp [hj]

/-! ### Section V-C — the Poisson-PGF identity -/

/-- **PGF step of the PPP heuristic.**  For any real `μ` and `q`,
`∑ₖ e^{-μ} (μq)^k / k! = e^{-μ(1-q)}`, which is
`E[q^K] = e^{-μ(1-q)}` for `K ~ Poisson(μ)`. -/
theorem poisson_pgf (μ q : ℝ) :
    ∑' k : ℕ, Real.exp (-μ) * ((μ * q) ^ k / (Nat.factorial k)) =
      Real.exp (-(μ * (1 - q))) := by
  have hexp : ∑' k : ℕ, (μ * q) ^ k / (Nat.factorial k)
      = Real.exp (μ * q) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [tsum_mul_left, hexp, ← Real.exp_add]
  ring_nf

/-! ### Proposition 1 — the exact quorum value at `P_A = 1/2` -/

/-- **Binomial symmetry behind the corrected limit statement.**  For even
`n = 2m` the corrected quorum sum at `P_A = 1/2` is exactly one half:
`2 · ∑_{k=⌊n/2⌋}^{n-1} C(n-1,k) = 2^{n-1}`, hence
`P_q(2m, 1/2) = 1/2` exactly (the piecewise limit value adopted after
review, not the indicator value `0` or `1`). -/
theorem quorum_half_symmetry (m : ℕ) (hm : 1 ≤ m) :
    2 * ∑ k ∈ Finset.Ico m (2 * m), (2 * m - 1).choose k
      = 2 ^ (2 * m - 1) := by
  have hmm : 2 * m - m = m := by omega
  have h1 : ∑ k ∈ Finset.Ico m (2 * m), (2 * m - 1).choose k
      = ∑ i ∈ Finset.range m, (2 * m - 1).choose (m + i) := by
    rw [Finset.sum_Ico_eq_sum_range, hmm]
  have h2 : ∀ i ∈ Finset.range m,
      (2 * m - 1).choose (m + i) = (2 * m - 1).choose (m - 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← Nat.choose_symm (by omega : m + i ≤ 2 * m - 1)]
    congr 1
    omega
  have h3 : ∑ i ∈ Finset.range m, (2 * m - 1).choose (m - 1 - i)
      = ∑ i ∈ Finset.range m, (2 * m - 1).choose i :=
    Finset.sum_range_reflect (fun j => (2 * m - 1).choose j) m
  have htot : ∑ k ∈ Finset.range (2 * m), (2 * m - 1).choose k
      = 2 ^ (2 * m - 1) := by
    have h := Nat.sum_range_choose (2 * m - 1)
    have h2m : 2 * m - 1 + 1 = 2 * m := by omega
    rwa [h2m] at h
  have hsplit :
      ∑ k ∈ Finset.range m, (2 * m - 1).choose k
        + ∑ k ∈ Finset.Ico m (2 * m), (2 * m - 1).choose k
      = ∑ k ∈ Finset.range (2 * m), (2 * m - 1).choose k := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have hS : ∑ k ∈ Finset.Ico m (2 * m), (2 * m - 1).choose k
      = ∑ i ∈ Finset.range m, (2 * m - 1).choose i := by
    rw [h1, Finset.sum_congr rfl h2, h3]
  omega

/-! ### Axiom audit — every theorem must use only the standard axioms -/

#print axioms uplink_critical_radius
#print axioms quorum_followers_needed
#print axioms old_threshold_too_strong
#print axioms ray_reentry
#print axioms failure_past_jammer
#print axioms apollonius_circle
#print axioms beta_exponent_identity
#print axioms worst_case_upper_bound
#print axioms worst_case_attained
#print axioms poisson_pgf
#print axioms quorum_half_symmetry

end R260402
