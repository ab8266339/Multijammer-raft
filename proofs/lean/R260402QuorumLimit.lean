import Mathlib

/-!
Asymptotic Raft quorum probability for accepted paper WCL2026-2945 / R260402.

`quorumProb n p` is the binomial upper sum from follower threshold `⌊n/2⌋`
through `n - 1`. For every success probability `p ∈ [0,1]`,
`quorumProb n p` tends to `0`, `1/2`, or `1` according as `p < 1/2`,
`p = 1/2`, or `p > 1/2`.

The off-half bounds are finite Chernoff comparisons coming from the binomial
theorem. The half case uses even/odd binomial symmetry together with the
elementary central-binomial bound `C(2m,m) / 4^m ≤ 1/√(2m+1)`.
No concentration inequality, central-limit input, or final limit is assumed.
-/

set_option maxHeartbeats 2000000

namespace R260402QuorumLimit

open Finset Filter

/-- One binomial probability mass, written as a finite product. -/
noncomputable def binomTerm (N k : ℕ) (p : ℝ) : ℝ :=
  (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)

/-- Quorum probability at follower success rate `p` in an `n`-server group.
The leader counts itself, so the sum starts at `⌊n/2⌋` follower acknowledgements.
The `n = 0` and `n = 1` values are immaterial for the limit at infinity. -/
noncomputable def quorumProb (n : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Ico (n / 2) n,
    (Nat.choose (n - 1) k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k)

lemma quorumProb_eq (n : ℕ) (p : ℝ) :
    quorumProb n p = ∑ k ∈ Ico (n / 2) n, binomTerm (n - 1) k p := rfl

lemma binomTerm_nonneg {N k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binomTerm N k p := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  unfold binomTerm
  positivity

lemma quorumProb_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ quorumProb n p := by
  rw [quorumProb_eq]
  exact sum_nonneg fun k _ => binomTerm_nonneg hp0 hp1

lemma sum_binomTerm (N : ℕ) (p : ℝ) :
    ∑ k ∈ range (N + 1), binomTerm N k p = 1 := by
  have hbinom := add_pow p (1 - p) N
  rw [show p + (1 - p) = 1 by ring, one_pow] at hbinom
  have hsum :
      ∑ k ∈ range (N + 1), binomTerm N k p =
        ∑ k ∈ range (N + 1), p ^ k * (1 - p) ^ (N - k) * (N.choose k) := by
    refine sum_congr rfl ?_
    intro k _
    unfold binomTerm
    ring
  exact hsum.trans hbinom.symm

lemma binomTerm_reflect {N k : ℕ} (hk : k ≤ N) (p : ℝ) :
    binomTerm N k p = binomTerm N (N - k) (1 - p) := by
  unfold binomTerm
  rw [Nat.choose_symm hk]
  have hsub : N - (N - k) = k := by omega
  rw [hsub]
  ring

lemma binomTerm_center (m : ℕ) (p : ℝ) :
    binomTerm (2 * m) m p =
      (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m := by
  unfold binomTerm
  rw [show 2 * m - m = m by omega, Nat.centralBinom, mul_pow]
  ring

/-- Pascal recurrence for the central coefficient, cast to `ℝ`. -/
lemma centralBinom_cast_succ (m : ℕ) :
    (Nat.centralBinom (m + 1) : ℝ) =
      (2 * (2 * (m : ℝ) + 1) / ((m : ℝ) + 1)) * (Nat.centralBinom m : ℝ) := by
  have h := congr_arg (Nat.cast : ℕ → ℝ) (Nat.succ_mul_centralBinom_succ m)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm
  calc
    ((m : ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ)
        = (2 : ℝ) * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := h
    _ = ((m : ℝ) + 1) *
          ((2 * (2 * (m : ℝ) + 1) / ((m : ℝ) + 1)) * (Nat.centralBinom m : ℝ)) := by
        field_simp [hm]

/-- One step of the elementary bound `√((2m+1)(2m+3)) ≤ 2m+2`. -/
lemma sqrt_ratio_step (m : ℕ) :
    (1 / Real.sqrt (2 * (m : ℝ) + 1)) *
        ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) ≤
      1 / Real.sqrt (2 * (m : ℝ) + 3) := by
  set A : ℝ := 2 * (m : ℝ) + 1
  have hA : 0 < A := by unfold A; positivity
  have hAp : 0 < A + 1 := by linarith
  have hA2 : 0 < A + 2 := by linarith
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hs2 : 0 < Real.sqrt (A + 2) := Real.sqrt_pos.mpr hA2
  have hsq : Real.sqrt (A * (A + 2)) ≤ A + 1 := by
    rw [Real.sqrt_le_left hAp.le]
    nlinarith
  have hmul : Real.sqrt A * Real.sqrt (A + 2) ≤ A + 1 := by
    rwa [Real.sqrt_mul hA.le] at hsq
  have hstep : A * Real.sqrt (A + 2) ≤ Real.sqrt A * (A + 1) := by
    calc
      A * Real.sqrt (A + 2)
          = Real.sqrt A * Real.sqrt A * Real.sqrt (A + 2) := by
            rw [Real.mul_self_sqrt hA.le]
      _ = Real.sqrt A * (Real.sqrt A * Real.sqrt (A + 2)) := by ring
      _ ≤ Real.sqrt A * (A + 1) :=
            mul_le_mul_of_nonneg_left hmul hsA.le
  have hleft :
      (1 / Real.sqrt A) * (A / (A + 1)) =
        A / (Real.sqrt A * (A + 1)) := by
    field_simp [hsA.ne', hAp.ne']
  have hineq : A / (Real.sqrt A * (A + 1)) ≤ 1 / Real.sqrt (A + 2) := by
    rw [div_le_div_iff₀ (mul_pos hsA hAp) hs2]
    simpa [one_mul] using hstep
  have hshift1 : A + 1 = 2 * (m : ℝ) + 2 := by unfold A; ring
  have hshift2 : A + 2 = 2 * (m : ℝ) + 3 := by unfold A; ring
  rw [← hleft, hshift1, hshift2] at hineq
  simpa [A] using hineq

/-- `C(2m, m) / 4^m ≤ 1/√(2m+1)`, proved from the Pascal recurrence. -/
theorem centralBinom_div_four_pow_le (m : ℕ) :
    (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m ≤
      1 / Real.sqrt (2 * (m : ℝ) + 1) := by
  induction m with
  | zero =>
    simp [Nat.centralBinom_zero, Real.sqrt_one]
  | succ m ih =>
    have hratio :
        (Nat.centralBinom (m + 1) : ℝ) / (4 : ℝ) ^ (m + 1) =
          ((Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m) *
            ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) := by
      rw [centralBinom_cast_succ, pow_succ]
      field_simp
      ring
    rw [hratio]
    have hstep :
        (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m *
            ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) ≤
          1 / Real.sqrt (2 * (m : ℝ) + 3) := by
      calc
        (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m *
              ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2))
            ≤ (1 / Real.sqrt (2 * (m : ℝ) + 1)) *
                ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) := by
              exact mul_le_mul_of_nonneg_right ih (by positivity)
        _ ≤ 1 / Real.sqrt (2 * (m : ℝ) + 3) := sqrt_ratio_step m
    have hidx : (2 : ℝ) * (m : ℝ) + 3 = 2 * ((m + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    simpa [hidx] using hstep

lemma four_mul_prob_lt_one {p : ℝ} (hp : p ≠ 1 / 2) :
    4 * p * (1 - p) < 1 := by
  have hsq : 0 < (1 - 2 * p) ^ 2 := by
    refine sq_pos_of_ne_zero ?_
    intro h
    apply hp
    linarith
  nlinarith [hsq]

lemma central_edge_le {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m ≤
      (4 * p * (1 - p)) ^ m := by
  have hle : (Nat.centralBinom m : ℝ) ≤ (4 : ℝ) ^ m := by
    exact_mod_cast Nat.centralBinom_le_four_pow m
  have hnn : 0 ≤ (p * (1 - p)) ^ m := by
    have : 0 ≤ p * (1 - p) := by nlinarith [hp0, hp1]
    exact pow_nonneg this _
  calc
    (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m
        ≤ (4 : ℝ) ^ m * (p * (1 - p)) ^ m := mul_le_mul_of_nonneg_right hle hnn
    _ = (4 * (p * (1 - p))) ^ m := by rw [← mul_pow]
    _ = (4 * p * (1 - p)) ^ m := by ring

theorem tendsto_central_edge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : p ≠ 1 / 2) :
    Tendsto (fun m : ℕ => (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m) atTop (nhds 0) := by
  have hρ0 : 0 ≤ 4 * p * (1 - p) := by nlinarith [hp0, hp1]
  have hρ1 : 4 * p * (1 - p) < 1 := four_mul_prob_lt_one hp
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  refine squeeze_zero (fun m => ?_) (fun m => central_edge_le hp0 hp1) hpow
  have : 0 ≤ p * (1 - p) := by nlinarith [hp0, hp1]
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg this _)

/-- Markov comparison after multiplying the upper tail by `r^{k-t} ≥ 1`. -/
theorem binom_tail_le_tilt (N t : ℕ) {p r : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r) (ht : t ≤ N) :
    ∑ k ∈ Ico t (N + 1), binomTerm N k p ≤
      (1 - p + p * r) ^ N / r ^ t := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hterm : ∀ k ∈ Ico t (N + 1),
      binomTerm N k p ≤ binomTerm N k p * r ^ (k - t) := by
    intro k hk
    have hkt : t ≤ k := (mem_Ico.mp hk).1
    have hone : (1 : ℝ) ≤ r ^ (k - t) := one_le_pow₀ hr
    exact le_mul_of_one_le_right (binomTerm_nonneg hp0 hp1) hone
  have hsumle :
      ∑ k ∈ Ico t (N + 1), binomTerm N k p ≤
        ∑ k ∈ Ico t (N + 1), binomTerm N k p * r ^ (k - t) :=
    sum_le_sum hterm
  have hrewrite : ∀ k ∈ Ico t (N + 1),
      binomTerm N k p * r ^ (k - t) =
        ((Nat.choose N k : ℝ) * (p * r) ^ k * (1 - p) ^ (N - k)) / r ^ t := by
    intro k hk
    have hkt : t ≤ k := (mem_Ico.mp hk).1
    unfold binomTerm
    have hrpow : r ^ t ≠ 0 := pow_ne_zero _ hr0.ne'
    have hpow : r ^ (k - t) = r ^ k / r ^ t := by
      rw [eq_div_iff hrpow]
      exact pow_sub_mul_pow r hkt
    rw [hpow, mul_pow]
    field_simp [hrpow]
  have hsum1 :
      ∑ k ∈ Ico t (N + 1), binomTerm N k p * r ^ (k - t) =
        (∑ k ∈ Ico t (N + 1),
          (Nat.choose N k : ℝ) * (p * r) ^ k * (1 - p) ^ (N - k)) / r ^ t := by
    rw [sum_congr rfl hrewrite]
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul]
  have htilt_nonneg : ∀ k ∈ range (N + 1),
      0 ≤ (Nat.choose N k : ℝ) * (p * r) ^ k * (1 - p) ^ (N - k) := by
    intro k _
    have hpr : 0 ≤ p * r := mul_nonneg hp0 (le_trans zero_le_one hr)
    positivity
  have hfull :
      ∑ k ∈ range (N + 1),
          (Nat.choose N k : ℝ) * (p * r) ^ k * (1 - p) ^ (N - k) =
        (p * r + (1 - p)) ^ N := by
    have hbinom := add_pow (p * r) (1 - p) N
    refine Eq.trans ?_ hbinom.symm
    refine sum_congr rfl ?_
    intro k _
    ring
  have htail :
      ∑ k ∈ Ico t (N + 1),
          (Nat.choose N k : ℝ) * (p * r) ^ k * (1 - p) ^ (N - k) ≤
        ∑ k ∈ range (N + 1),
          (Nat.choose N k : ℝ) * (p * r) ^ k * (1 - p) ^ (N - k) := by
    have hsplit := sum_Ico_consecutive
      (fun k => (Nat.choose N k : ℝ) * (p * r) ^ k * (1 - p) ^ (N - k))
      (show 0 ≤ t by omega) (show t ≤ N + 1 by omega)
    simp only [← range_eq_Ico] at hsplit
    have hlow : 0 ≤ ∑ k ∈ range t,
        (Nat.choose N k : ℝ) * (p * r) ^ k * (1 - p) ^ (N - k) := by
      refine sum_nonneg ?_
      intro k hk
      exact htilt_nonneg k (mem_range.mpr (lt_of_lt_of_le (mem_range.mp hk) (by omega)))
    linarith
  calc
    ∑ k ∈ Ico t (N + 1), binomTerm N k p
        ≤ ∑ k ∈ Ico t (N + 1), binomTerm N k p * r ^ (k - t) := hsumle
    _ = (∑ k ∈ Ico t (N + 1),
          (Nat.choose N k : ℝ) * (p * r) ^ k * (1 - p) ^ (N - k)) / r ^ t := hsum1
    _ ≤ (∑ k ∈ range (N + 1),
          (Nat.choose N k : ℝ) * (p * r) ^ k * (1 - p) ^ (N - k)) / r ^ t := by
          exact div_le_div_of_nonneg_right htail (pow_nonneg hr0.le t)
    _ = (p * r + (1 - p)) ^ N / r ^ t := by rw [hfull]
    _ = (1 - p + p * r) ^ N / r ^ t := by
          rw [add_comm]

lemma tilt_base {p : ℝ} (hp : p ≠ 0) :
    1 - p + p * ((1 - p) / p) = 2 * (1 - p) := by
  field_simp [hp]
  ring

/-- The one-step multiplier in the Chernoff closed forms. -/
lemma tilt_square_factor {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (2 * (1 - p)) ^ 2 / ((1 - p) / p) = 4 * p * (1 - p) := by
  have hq : (1 - p) ≠ 0 := by linarith
  calc
    (2 * (1 - p)) ^ 2 / ((1 - p) / p)
        = (2 * (1 - p)) ^ 2 * (p / (1 - p)) := by
          rw [div_eq_mul_inv, inv_div]
    _ = 4 * (1 - p) ^ 2 * (p / (1 - p)) := by
          rw [mul_pow]
          norm_num
    _ = 4 * (1 - p) * ((1 - p) * (p / (1 - p))) := by ring
    _ = 4 * (1 - p) * p := by rw [mul_div_cancel₀ _ hq]
    _ = 4 * p * (1 - p) := by ring

/-- Closed form of the even-length Chernoff expression, indexed by `k = m - 1`. -/
lemma even_bound_formula {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (k : ℕ) :
    (2 * (1 - p)) ^ (2 * k + 1) / ((1 - p) / p) ^ (k + 1) =
      2 * p * (4 * p * (1 - p)) ^ k := by
  induction k with
  | zero =>
    have hq : 0 < 1 - p := by linarith
    calc
      (2 * (1 - p)) ^ (2 * 0 + 1) / ((1 - p) / p) ^ (0 + 1)
          = (2 * (1 - p)) / ((1 - p) / p) := by simp
      _ = (2 * (1 - p)) * (p / (1 - p)) := by rw [div_eq_mul_inv, inv_div]
      _ = 2 * ((1 - p) * (p / (1 - p))) := by ring
      _ = 2 * p := by rw [mul_div_cancel₀ _ hq.ne']
      _ = 2 * p * (4 * p * (1 - p)) ^ 0 := by simp
  | succ k ih =>
    have hexp : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    have hdenexp : k + 1 + 1 = (k + 1) + 1 := by omega
    have hnum : (2 * (1 - p)) ^ ((2 * k + 1) + 2) =
        (2 * (1 - p)) ^ (2 * k + 1) * (2 * (1 - p)) ^ 2 := by
      rw [pow_add]
    have hden : ((1 - p) / p) ^ ((k + 1) + 1) =
        ((1 - p) / p) ^ (k + 1) * ((1 - p) / p) := by
      rw [pow_add, pow_one]
    calc
      (2 * (1 - p)) ^ (2 * (k + 1) + 1) / ((1 - p) / p) ^ (k + 1 + 1)
          = (2 * (1 - p)) ^ ((2 * k + 1) + 2) / ((1 - p) / p) ^ ((k + 1) + 1) := by
            rw [hexp, hdenexp]
      _ = ((2 * (1 - p)) ^ (2 * k + 1) * (2 * (1 - p)) ^ 2) /
            (((1 - p) / p) ^ (k + 1) * ((1 - p) / p)) := by
            rw [hnum, hden]
      _ = ((2 * (1 - p)) ^ (2 * k + 1) / ((1 - p) / p) ^ (k + 1)) *
            ((2 * (1 - p)) ^ 2 / ((1 - p) / p)) := by
            rw [← div_mul_div_comm]
      _ = (2 * p * (4 * p * (1 - p)) ^ k) * (4 * p * (1 - p)) := by
            rw [ih, tilt_square_factor hp hp1]
      _ = 2 * p * ((4 * p * (1 - p)) ^ k * (4 * p * (1 - p))) := by ring
      _ = 2 * p * (4 * p * (1 - p)) ^ (k + 1) := by rw [pow_succ]

/-- Closed form of the odd-length Chernoff expression. -/
lemma odd_bound_formula {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m : ℕ) :
    (2 * (1 - p)) ^ (2 * m) / ((1 - p) / p) ^ m = (4 * p * (1 - p)) ^ m := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hexp : 2 * (m + 1) = 2 * m + 2 := by omega
    have hnum : (2 * (1 - p)) ^ (2 * m + 2) =
        (2 * (1 - p)) ^ (2 * m) * (2 * (1 - p)) ^ 2 := by
      rw [pow_add]
    have hden : ((1 - p) / p) ^ (m + 1) =
        ((1 - p) / p) ^ m * ((1 - p) / p) := by
      rw [pow_succ]
    calc
      (2 * (1 - p)) ^ (2 * (m + 1)) / ((1 - p) / p) ^ (m + 1)
          = (2 * (1 - p)) ^ (2 * m + 2) / ((1 - p) / p) ^ (m + 1) := by
            rw [hexp]
      _ = ((2 * (1 - p)) ^ (2 * m) * (2 * (1 - p)) ^ 2) /
            (((1 - p) / p) ^ m * ((1 - p) / p)) := by
            rw [hnum, hden]
      _ = ((2 * (1 - p)) ^ (2 * m) / ((1 - p) / p) ^ m) *
            ((2 * (1 - p)) ^ 2 / ((1 - p) / p)) := by
            rw [← div_mul_div_comm]
      _ = (4 * p * (1 - p)) ^ m * (4 * p * (1 - p)) := by
            rw [ih, tilt_square_factor hp hp1]
      _ = (4 * p * (1 - p)) ^ (m + 1) := by rw [pow_succ]

lemma quorumProb_even (m : ℕ) (p : ℝ) :
    quorumProb (2 * m) p =
      ∑ k ∈ Ico m (2 * m), binomTerm (2 * m - 1) k p := by
  rw [quorumProb_eq]
  have hdiv : (2 * m) / 2 = m := Nat.mul_div_cancel_left m (by decide : 0 < 2)
  simp [hdiv]

lemma quorumProb_odd (m : ℕ) (p : ℝ) :
    quorumProb (2 * m + 1) p =
      ∑ k ∈ Ico m (2 * m + 1), binomTerm (2 * m) k p := by
  rw [quorumProb_eq]
  have hdiv : (2 * m + 1) / 2 = m := by omega
  simp [hdiv]

lemma lower_sum_even (m : ℕ) (hm : 1 ≤ m) (p : ℝ) :
    ∑ k ∈ Ico 0 m, binomTerm (2 * m - 1) k p =
      ∑ k ∈ Ico m (2 * m), binomTerm (2 * m - 1) k (1 - p) := by
  have hpt : ∀ k ∈ Ico 0 m,
      binomTerm (2 * m - 1) k p =
        binomTerm (2 * m - 1) ((2 * m - 1) - k) (1 - p) := by
    intro k hk
    have hkN : k ≤ 2 * m - 1 := by
      have hklt : k < m := (mem_Ico.mp hk).2
      omega
    exact binomTerm_reflect hkN p
  rw [sum_congr rfl hpt]
  have href := sum_Ico_reflect (fun j => binomTerm (2 * m - 1) j (1 - p)) 0
    (m := m) (n := 2 * m - 1) (by omega : m ≤ (2 * m - 1) + 1)
  rw [show (2 * m - 1) + 1 - m = m by omega,
      show (2 * m - 1) + 1 - 0 = 2 * m by omega] at href
  exact href

/-- Even total node count: the `p` tail and the `1-p` tail partition the binomial row. -/
theorem quorum_even_complement {m : ℕ} (hm : 1 ≤ m) (p : ℝ) :
    quorumProb (2 * m) p + quorumProb (2 * m) (1 - p) = 1 := by
  have hlen : (2 * m - 1) + 1 = 2 * m := by omega
  have htot : ∑ k ∈ Ico 0 (2 * m), binomTerm (2 * m - 1) k p = 1 := by
    have h := sum_binomTerm (2 * m - 1) p
    simpa only [hlen, range_eq_Ico] using h
  have hsplit := sum_Ico_consecutive (binomTerm (2 * m - 1) · p)
    (show 0 ≤ m by omega) (show m ≤ 2 * m by omega)
  rw [quorumProb_even, quorumProb_even, ← lower_sum_even m hm, add_comm, hsplit, htot]

lemma lower_sum_odd (m : ℕ) (p : ℝ) :
    ∑ k ∈ Ico 0 m, binomTerm (2 * m) k p =
      ∑ k ∈ Ico (m + 1) (2 * m + 1), binomTerm (2 * m) k (1 - p) := by
  have hpt : ∀ k ∈ Ico 0 m,
      binomTerm (2 * m) k p = binomTerm (2 * m) (2 * m - k) (1 - p) := by
    intro k hk
    have hkN : k ≤ 2 * m := by
      have hklt : k < m := (mem_Ico.mp hk).2
      omega
    exact binomTerm_reflect hkN p
  rw [sum_congr rfl hpt]
  have href := sum_Ico_reflect (fun j => binomTerm (2 * m) j (1 - p)) 0
    (m := m) (n := 2 * m) (by omega : m ≤ 2 * m + 1)
  rw [show 2 * m + 1 - m = m + 1 by omega,
      show 2 * m + 1 - 0 = 2 * m + 1 by omega] at href
  exact href

lemma sum_Ico_singleton_center (m : ℕ) (p : ℝ) :
    ∑ k ∈ Ico m (m + 1), binomTerm (2 * m) k p = binomTerm (2 * m) m p := by
  have hs := sum_Ico_succ_top (a := m) (b := m) le_rfl (binomTerm (2 * m) · p)
  simpa using hs

/-- Odd total node count: the two tails overlap on the central mass. -/
theorem quorum_odd_complement (m : ℕ) (p : ℝ) :
    quorumProb (2 * m + 1) p + quorumProb (2 * m + 1) (1 - p) =
      1 + (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m := by
  have htot : ∑ k ∈ Ico 0 (2 * m + 1), binomTerm (2 * m) k p = 1 := by
    have h := sum_binomTerm (2 * m) p
    rwa [range_eq_Ico] at h
  have hsplit := sum_Ico_consecutive (binomTerm (2 * m) · p)
    (Nat.zero_le m) (by omega : m ≤ 2 * m + 1)
  have hpart : ∑ k ∈ Ico 0 m, binomTerm (2 * m) k p + quorumProb (2 * m + 1) p = 1 := by
    rw [quorumProb_odd]
    exact hsplit.trans htot
  rw [lower_sum_odd] at hpart
  have hsplitq := sum_Ico_consecutive (binomTerm (2 * m) · (1 - p))
    (by omega : m ≤ m + 1) (by omega : m + 1 ≤ 2 * m + 1)
  have hmid := sum_Ico_singleton_center m (1 - p)
  have htail :
      quorumProb (2 * m + 1) (1 - p) =
        binomTerm (2 * m) m (1 - p) +
          ∑ k ∈ Ico (m + 1) (2 * m + 1), binomTerm (2 * m) k (1 - p) := by
    rw [quorumProb_odd, ← hsplitq, hmid]
  have hcenter : binomTerm (2 * m) m (1 - p) =
      (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m := by
    have href := binomTerm_reflect (N := 2 * m) (k := m) (by omega) p
    rw [show 2 * m - m = m by omega] at href
    rw [← href, binomTerm_center]
  calc
    quorumProb (2 * m + 1) p + quorumProb (2 * m + 1) (1 - p)
        = quorumProb (2 * m + 1) p +
            (binomTerm (2 * m) m (1 - p) +
              ∑ k ∈ Ico (m + 1) (2 * m + 1), binomTerm (2 * m) k (1 - p)) := by
          rw [htail]
    _ = quorumProb (2 * m + 1) p +
          ((Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m +
            ∑ k ∈ Ico (m + 1) (2 * m + 1), binomTerm (2 * m) k (1 - p)) := by
          rw [hcenter]
    _ = (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m +
          (∑ k ∈ Ico (m + 1) (2 * m + 1), binomTerm (2 * m) k (1 - p) +
            quorumProb (2 * m + 1) p) := by
          ring
    _ = (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m + 1 := by
          rw [hpart]
    _ = 1 + (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m := by ring

theorem quorumProb_even_half {m : ℕ} (hm : 1 ≤ m) :
    quorumProb (2 * m) (1 / 2) = 1 / 2 := by
  have h := quorum_even_complement hm (1 / 2)
  have hsub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hsub] at h
  linarith

theorem quorumProb_odd_half (m : ℕ) :
    quorumProb (2 * m + 1) (1 / 2) =
      1 / 2 + (Nat.centralBinom m : ℝ) / (2 * (4 : ℝ) ^ m) := by
  have h := quorum_odd_complement m (1 / 2)
  have hsym : quorumProb (2 * m + 1) (1 - 1 / 2) = quorumProb (2 * m + 1) (1 / 2) := by
    congr 1
    norm_num
  rw [hsym] at h
  have hpow : ((1 / 2 : ℝ) * (1 - 1 / 2)) ^ m = (1 / 4 : ℝ) ^ m := by
    congr 1
    norm_num
  rw [hpow, show (1 / 4 : ℝ) ^ m = 1 / (4 : ℝ) ^ m by rw [div_pow, one_pow]] at h
  have htwo : 2 * quorumProb (2 * m + 1) (1 / 2) =
      1 + (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m := by
    have hmul : (Nat.centralBinom m : ℝ) * (1 / (4 : ℝ) ^ m) =
        (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m := by
      rw [mul_one_div]
    linarith
  have hden : (2 : ℝ) ≠ 0 := by norm_num
  have hdouble : 2 * ((Nat.centralBinom m : ℝ) / (2 * (4 : ℝ) ^ m)) =
      (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m := by
    field_simp
  linarith

theorem odd_half_abs_le (m : ℕ) :
    |quorumProb (2 * m + 1) (1 / 2) - 1 / 2| ≤
      1 / (2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
  rw [quorumProb_odd_half, add_sub_cancel_left]
  have hnn : 0 ≤ (Nat.centralBinom m : ℝ) / (2 * (4 : ℝ) ^ m) := by positivity
  rw [abs_of_nonneg hnn]
  have hle := centralBinom_div_four_pow_le m
  calc
    (Nat.centralBinom m : ℝ) / (2 * (4 : ℝ) ^ m)
        = ((Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m) / 2 := by
          rw [mul_comm, ← div_div]
    _ ≤ (1 / Real.sqrt (2 * (m : ℝ) + 1)) / 2 :=
          div_le_div_of_nonneg_right hle (by norm_num)
    _ = 1 / (Real.sqrt (2 * (m : ℝ) + 1) * 2) := by rw [div_div]
    _ = 1 / (2 * Real.sqrt (2 * (m : ℝ) + 1)) := by rw [mul_comm]

lemma quorumProb_eq_zero_of_p_zero {n : ℕ} (hn : 2 ≤ n) : quorumProb n 0 = 0 := by
  unfold quorumProb
  refine sum_eq_zero ?_
  intro k hk
  have hk0 : k ≠ 0 := by
    have hle : n / 2 ≤ k := (mem_Ico.mp hk).1
    have hone : 1 ≤ n / 2 := by omega
    omega
  rw [zero_pow hk0]
  ring

theorem tendsto_quorumProb_zero :
    Tendsto (fun n => quorumProb n 0) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨2, ?_⟩
  intro n hn
  rw [quorumProb_eq_zero_of_p_zero hn, Real.dist_eq, sub_zero, abs_zero]
  exact hε

lemma tendsto_nat_pred_atTop : Tendsto (fun m : ℕ => m - 1) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b + 1)] with m hm
  omega

theorem quorumProb_even_le {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    quorumProb (2 * m) p ≤ 2 * p * (4 * p * (1 - p)) ^ (m - 1) := by
  have hp1 : p ≤ 1 := le_of_lt (lt_trans hp (by norm_num : (1 / 2 : ℝ) < 1))
  have hr : 1 ≤ (1 - p) / p := by
    rw [one_le_div hp0]
    linarith
  have ht : m ≤ 2 * m - 1 := by omega
  have htilt := binom_tail_le_tilt (2 * m - 1) m hp0.le hp1 hr ht
  have hbase := tilt_base hp0.ne'
  have hform := even_bound_formula hp0 (lt_trans hp (by norm_num)) (m - 1)
  have hexp1 : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
  have hexp2 : m - 1 + 1 = m := by omega
  have hup : (2 * m - 1) + 1 = 2 * m := by omega
  calc
    quorumProb (2 * m) p
        ≤ (1 - p + p * ((1 - p) / p)) ^ (2 * m - 1) / ((1 - p) / p) ^ m := by
          rw [quorumProb_even]
          simpa only [hup] using htilt
    _ = (2 * (1 - p)) ^ (2 * m - 1) / ((1 - p) / p) ^ m := by
          rw [hbase]
    _ = 2 * p * (4 * p * (1 - p)) ^ (m - 1) := by
          rw [← hexp1, ← hexp2]
          exact hform

theorem quorumProb_odd_le {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) (m : ℕ) :
    quorumProb (2 * m + 1) p ≤ (4 * p * (1 - p)) ^ m := by
  have hp1 : p ≤ 1 := le_of_lt (lt_trans hp (by norm_num : (1 / 2 : ℝ) < 1))
  have hr : 1 ≤ (1 - p) / p := by
    rw [one_le_div hp0]
    linarith
  have ht : m ≤ 2 * m := by omega
  have htilt := binom_tail_le_tilt (2 * m) m hp0.le hp1 hr ht
  have hbase := tilt_base hp0.ne'
  have hform := odd_bound_formula hp0 (lt_trans hp (by norm_num)) m
  calc
    quorumProb (2 * m + 1) p
        ≤ (1 - p + p * ((1 - p) / p)) ^ (2 * m) / ((1 - p) / p) ^ m := by
          rw [quorumProb_odd]
          exact htilt
    _ = (2 * (1 - p)) ^ (2 * m) / ((1 - p) / p) ^ m := by rw [hbase]
    _ = (4 * p * (1 - p)) ^ m := hform

theorem tendsto_quorumProb_even_of_lt_half {p : ℝ} (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    Tendsto (fun m => quorumProb (2 * m) p) atTop (nhds 0) := by
  rcases eq_or_lt_of_le hp0 with rfl | hppos
  · rw [Metric.tendsto_atTop]
    intro ε hε
    refine ⟨1, ?_⟩
    intro m hm
    rw [quorumProb_eq_zero_of_p_zero (by omega : 2 ≤ 2 * m), Real.dist_eq, sub_zero, abs_zero]
    exact hε
  · have hρ0 : 0 ≤ 4 * p * (1 - p) := by nlinarith [hp0, le_of_lt hp]
    have hρ1 : 4 * p * (1 - p) < 1 := four_mul_prob_lt_one (ne_of_lt hp)
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have hshift := hpow.comp tendsto_nat_pred_atTop
    have hbound : Tendsto (fun m : ℕ => 2 * p * (4 * p * (1 - p)) ^ (m - 1)) atTop (nhds 0) := by
      have hmul := hshift.const_mul (2 * p)
      simpa using hmul
    refine squeeze_zero' (Eventually.of_forall fun m => quorumProb_nonneg hp0 (le_of_lt (lt_trans hp (by norm_num)))) ?_ hbound
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact quorumProb_even_le hppos hp hm

theorem tendsto_quorumProb_odd_of_lt_half {p : ℝ} (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    Tendsto (fun m => quorumProb (2 * m + 1) p) atTop (nhds 0) := by
  rcases eq_or_lt_of_le hp0 with rfl | hppos
  · rw [Metric.tendsto_atTop]
    intro ε hε
    refine ⟨1, ?_⟩
    intro m hm
    rw [quorumProb_eq_zero_of_p_zero (by omega : 2 ≤ 2 * m + 1), Real.dist_eq, sub_zero, abs_zero]
    exact hε
  · have hρ0 : 0 ≤ 4 * p * (1 - p) := by nlinarith [hp0, le_of_lt hp]
    have hρ1 : 4 * p * (1 - p) < 1 := four_mul_prob_lt_one (ne_of_lt hp)
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    refine squeeze_zero (fun m => quorumProb_nonneg hp0 (le_of_lt (lt_trans hp (by norm_num))))
      (fun m => quorumProb_odd_le hppos hp m) hpow

/-- Even and odd subsequences determine the limit along every `n`. -/
theorem tendsto_of_even_odd {f : ℕ → ℝ} {L : ℝ}
    (he : Tendsto (fun m => f (2 * m)) atTop (nhds L))
    (ho : Tendsto (fun m => f (2 * m + 1)) atTop (nhds L)) :
    Tendsto f atTop (nhds L) := by
  rw [Metric.tendsto_atTop] at he ho ⊢
  intro ε hε
  obtain ⟨Ne, hNe⟩ := he ε hε
  obtain ⟨No, hNo⟩ := ho ε hε
  refine ⟨max (2 * Ne) (2 * No + 1), ?_⟩
  intro n hn
  rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
  · have hk : Ne ≤ k := by
      have h2 : 2 * Ne ≤ 2 * k := le_trans (le_max_left _ _) hn
      omega
    exact hNe k hk
  · have hk : No ≤ k := by
      have h2 : 2 * No + 1 ≤ 2 * k + 1 := le_trans (le_max_right _ _) hn
      omega
    exact hNo k hk

theorem tendsto_quorumProb_of_lt_half {p : ℝ} (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    Tendsto (fun n => quorumProb n p) atTop (nhds 0) :=
  tendsto_of_even_odd (tendsto_quorumProb_even_of_lt_half hp0 hp)
    (tendsto_quorumProb_odd_of_lt_half hp0 hp)

theorem tendsto_quorumProb_even_of_gt_half {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 1 / 2 < p) :
    Tendsto (fun m => quorumProb (2 * m) p) atTop (nhds 1) := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq : 1 - p < 1 / 2 := by linarith
  have h0 := tendsto_quorumProb_even_of_lt_half hq0 hq
  have hsub : Tendsto (fun m => (1 : ℝ) - quorumProb (2 * m) (1 - p)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub h0
  have hsub' : Tendsto (fun m => (1 : ℝ) - quorumProb (2 * m) (1 - p)) atTop (nhds 1) := by
    simpa using hsub
  refine hsub'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hcomp := quorum_even_complement hm p
  linarith

theorem tendsto_quorumProb_odd_of_gt_half {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 1 / 2 < p) :
    Tendsto (fun m => quorumProb (2 * m + 1) p) atTop (nhds 1) := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq : 1 - p < 1 / 2 := by linarith
  have h0 := tendsto_quorumProb_odd_of_lt_half hq0 hq
  have hcent := tendsto_central_edge hp0 hp1 (ne_of_gt hp)
  have hsum : Tendsto (fun m =>
      (1 : ℝ) - quorumProb (2 * m + 1) (1 - p) +
        (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m) atTop (nhds (1 - 0 + 0)) :=
    (tendsto_const_nhds.sub h0).add hcent
  have hsum' : Tendsto (fun m =>
      (1 : ℝ) - quorumProb (2 * m + 1) (1 - p) +
        (Nat.centralBinom m : ℝ) * (p * (1 - p)) ^ m) atTop (nhds 1) := by
    simpa using hsum
  refine hsum'.congr fun m => ?_
  have hcomp := quorum_odd_complement m p
  linarith

theorem tendsto_quorumProb_of_gt_half {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 1 / 2 < p) :
    Tendsto (fun n => quorumProb n p) atTop (nhds 1) :=
  tendsto_of_even_odd (tendsto_quorumProb_even_of_gt_half hp0 hp1 hp)
    (tendsto_quorumProb_odd_of_gt_half hp0 hp1 hp)

lemma tendsto_inv_two_sqrt :
    Tendsto (fun m : ℕ => (1 : ℝ) / (2 * Real.sqrt (2 * (m : ℝ) + 1))) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun m : ℕ => (1 : ℝ) / Real.sqrt (2 * (m : ℝ) + 1)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε ^ 2)
    refine ⟨N, ?_⟩
    intro m hm
    have hm' : 1 / ε ^ 2 < (m : ℝ) :=
      lt_of_lt_of_le hN (Nat.cast_le.mpr hm)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    have hs : 0 < Real.sqrt (2 * (m : ℝ) + 1) := by positivity
    rw [div_lt_iff₀ hs]
    have hsq : (1 / ε) ^ 2 < 2 * (m : ℝ) + 1 := by
      rw [div_pow, one_pow]
      linarith
    have hlt : 1 / ε < Real.sqrt (2 * (m : ℝ) + 1) :=
      (Real.lt_sqrt (by positivity : (0 : ℝ) ≤ 1 / ε)).mpr hsq
    have hmul := mul_lt_mul_of_pos_left hlt hε
    rwa [mul_one_div_cancel hε.ne'] at hmul
  have hconst := hsqrt.const_mul ((1 : ℝ) / 2)
  have hzero : Tendsto (fun m : ℕ => (1 / 2) * (1 / Real.sqrt (2 * (m : ℝ) + 1))) atTop (nhds 0) := by
    simpa using hconst
  refine hzero.congr fun m => ?_
  field_simp

theorem tendsto_quorumProb_even_of_half :
    Tendsto (fun m => quorumProb (2 * m) (1 / 2)) atTop (nhds (1 / 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨1, ?_⟩
  intro m hm
  rw [quorumProb_even_half hm, Real.dist_eq, sub_self, abs_zero]
  exact hε

theorem tendsto_quorumProb_odd_of_half :
    Tendsto (fun m => quorumProb (2 * m + 1) (1 / 2)) atTop (nhds (1 / 2)) := by
  have hdiff : Tendsto (fun m => quorumProb (2 * m + 1) (1 / 2) - 1 / 2) atTop (nhds 0) := by
    refine squeeze_zero ?_ ?_ tendsto_inv_two_sqrt
    · intro m
      rw [quorumProb_odd_half, add_sub_cancel_left]
      positivity
    · intro m
      have habs := odd_half_abs_le m
      have hnn : 0 ≤ quorumProb (2 * m + 1) (1 / 2) - 1 / 2 := by
        rw [quorumProb_odd_half, add_sub_cancel_left]
        positivity
      rwa [abs_of_nonneg hnn] at habs
  have h := hdiff.const_add ((1 : ℝ) / 2)
  have h' : Tendsto (fun m => 1 / 2 + (quorumProb (2 * m + 1) (1 / 2) - 1 / 2)) atTop
      (nhds (1 / 2)) := by
    simpa using h
  refine h'.congr fun m => ?_
  ring

theorem tendsto_quorumProb_of_half :
    Tendsto (fun n => quorumProb n (1 / 2)) atTop (nhds (1 / 2)) :=
  tendsto_of_even_odd tendsto_quorumProb_even_of_half tendsto_quorumProb_odd_of_half

/-- Full quorum limit. The value is `0` below one half, `1` above one half,
and exactly the symmetry value `1/2` at one half. -/
theorem quorumProb_tendsto {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Tendsto (fun n => quorumProb n p) atTop
      (nhds (if p < 1 / 2 then 0 else if 1 / 2 < p then 1 else 1 / 2)) := by
  split_ifs with hlt hgt
  · exact tendsto_quorumProb_of_lt_half hp0 hlt
  · exact tendsto_quorumProb_of_gt_half hp0 hp1 hgt
  · have hle : 1 / 2 ≤ p := le_of_not_gt hlt
    have hge : p ≤ 1 / 2 := le_of_not_gt hgt
    have heq : p = 1 / 2 := le_antisymm hge hle
    subst heq
    exact tendsto_quorumProb_of_half

#print axioms binomTerm_nonneg
#print axioms quorumProb_nonneg
#print axioms sum_binomTerm
#print axioms binomTerm_reflect
#print axioms binomTerm_center
#print axioms centralBinom_cast_succ
#print axioms sqrt_ratio_step
#print axioms centralBinom_div_four_pow_le
#print axioms four_mul_prob_lt_one
#print axioms central_edge_le
#print axioms tendsto_central_edge
#print axioms binom_tail_le_tilt
#print axioms tilt_base
#print axioms even_bound_formula
#print axioms odd_bound_formula
#print axioms quorumProb_even
#print axioms quorumProb_odd
#print axioms lower_sum_even
#print axioms quorum_even_complement
#print axioms lower_sum_odd
#print axioms sum_Ico_singleton_center
#print axioms quorum_odd_complement
#print axioms quorumProb_even_half
#print axioms quorumProb_odd_half
#print axioms odd_half_abs_le
#print axioms quorumProb_eq_zero_of_p_zero
#print axioms tendsto_quorumProb_zero
#print axioms tendsto_nat_pred_atTop
#print axioms quorumProb_even_le
#print axioms quorumProb_odd_le
#print axioms tendsto_quorumProb_even_of_lt_half
#print axioms tendsto_quorumProb_odd_of_lt_half
#print axioms tendsto_of_even_odd
#print axioms tendsto_quorumProb_of_lt_half
#print axioms tendsto_quorumProb_even_of_gt_half
#print axioms tendsto_quorumProb_odd_of_gt_half
#print axioms tendsto_quorumProb_of_gt_half
#print axioms tendsto_inv_two_sqrt
#print axioms tendsto_quorumProb_even_of_half
#print axioms tendsto_quorumProb_odd_of_half
#print axioms tendsto_quorumProb_of_half
#print axioms quorumProb_tendsto
#print axioms Nat.centralBinom_le_four_pow
#print axioms Nat.succ_mul_centralBinom_succ
#print axioms Nat.sum_range_choose
#print axioms add_pow
#print axioms tendsto_pow_atTop_nhds_zero_of_lt_one

end R260402QuorumLimit
