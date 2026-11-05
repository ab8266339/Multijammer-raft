import Mathlib

open Set Filter
open scoped Topology BigOperators

namespace R260402Geometry

noncomputable section

/- General coordinates are rotated so the ray is the positive horizontal axis.
No special placement (collinearity, distinct distances, or integer exponent)
is imposed on the finite jammer family. -/
structure Config (ι : Type*) [Fintype ι] where
  u : ι → ℝ
  v : ι → ℝ
  gamma : ℝ
  beta : ℝ
  radius : ℝ
  gamma_gt_two : 2 < gamma
  beta_pos : 0 < beta
  radius_pos : 0 < radius
  away_origin : ∀ i, 0 < u i ^ 2 + v i ^ 2

variable {ι : Type*} [Fintype ι]

def sqDist (c : Config ι) (i : ι) (r : ℝ) : ℝ :=
  (r - c.u i) ^ 2 + c.v i ^ 2

def field (c : Config ι) (r : ℝ) : ℝ :=
  r ^ (-c.gamma) - c.beta * ∑ i, (sqDist c i r) ^ (-c.gamma / 2)

def regular (c : Config ι) : Set ℝ :=
  {r | 0 < r ∧ ∀ i, 0 < sqDist c i r}

def domain (c : Config ι) : Set ℝ := regular c ∩ Iic c.radius

def success (c : Config ι) : Set ℝ := {r ∈ domain c | 0 ≤ field c r}

theorem analyticAt_rpow_pos (a : ℝ) {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℝ (fun t : ℝ => t ^ a) x := by
  have h : AnalyticAt ℝ (fun t : ℝ => Real.exp (Real.log t * a)) x :=
    ((analyticAt_id.log hx).mul analyticAt_const).rexp'
  apply h.congr
  filter_upwards [eventually_gt_nhds hx] with t ht
  exact (Real.rpow_def_of_pos ht a).symm

theorem analyticAt_sqDist (c : Config ι) (i : ι) (r : ℝ) :
    AnalyticAt ℝ (sqDist c i) r := by
  unfold sqDist
  fun_prop

theorem analyticAt_field (c : Config ι) {r : ℝ} (hr : r ∈ regular c) :
    AnalyticAt ℝ (field c) r := by
  apply (analyticAt_rpow_pos (-c.gamma) hr.1).sub
  apply analyticAt_const.mul
  exact Finset.analyticAt_fun_sum Finset.univ fun i _ =>
    (analyticAt_rpow_pos (-c.gamma / 2) (hr.2 i)).comp (analyticAt_sqDist c i r)

theorem sqDist_nonneg (c : Config ι) (i : ι) (r : ℝ) :
    0 ≤ sqDist c i r := by unfold sqDist; positivity

theorem sqDist_zero_iff (c : Config ι) (i : ι) (r : ℝ) :
    sqDist c i r = 0 ↔ r = c.u i ∧ c.v i = 0 := by
  unfold sqDist
  constructor
  · intro h
    have h1 : (r - c.u i) ^ 2 = 0 := by nlinarith [sq_nonneg (c.v i)]
    have h2 : c.v i ^ 2 = 0 := by nlinarith [sq_nonneg (r - c.u i)]
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

theorem analyticAt_interference (c : Config ι) {r : ℝ}
    (hr : ∀ i, 0 < sqDist c i r) :
    AnalyticAt ℝ (fun t => c.beta * ∑ i, (sqDist c i t) ^ (-c.gamma / 2)) r := by
  apply analyticAt_const.mul
  exact Finset.analyticAt_fun_sum Finset.univ fun i _ =>
    (analyticAt_rpow_pos (-c.gamma / 2) (hr i)).comp (analyticAt_sqDist c i r)

theorem field_tendsto_zero (c : Config ι) :
    Tendsto (field c) (𝓝[>] (0 : ℝ)) atTop := by
  have hg : -c.gamma < 0 := by linarith [c.gamma_gt_two]
  have hp := tendsto_rpow_neg_nhdsGT_zero hg
  have hq : ∀ i, 0 < sqDist c i 0 := by
    intro i
    simpa [sqDist] using c.away_origin i
  let B := c.beta * ∑ i, (sqDist c i 0) ^ (-c.gamma / 2)
  have hc : Tendsto (fun t => c.beta * ∑ i, (sqDist c i t) ^ (-c.gamma / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 B) :=
    (analyticAt_interference c hq).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_atTop.2
  intro M
  filter_upwards [hp.eventually_ge_atTop (M + B + 1),
    hc.eventually (eventually_lt_nhds (lt_add_one B))] with r hr hs
  unfold field
  linarith

theorem field_tendsto_pole (c : Config ι) {a : ℝ} (ha : 0 < a)
    (i : ι) (hi : sqDist c i a = 0) :
    Tendsto (field c) (𝓝[≠] a) atBot := by
  classical
  obtain ⟨hau, hv⟩ := (sqDist_zero_iff c i a).mp hi
  have hq : Tendsto (sqDist c i) (𝓝[≠] a) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have ht : Tendsto (sqDist c i) (𝓝[≠] a) (𝓝 (sqDist c i a)) :=
        (analyticAt_sqDist c i a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa [hi] using ht
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_compl_iff, mem_singleton_iff] at hr
      change 0 < sqDist c i r
      simp only [sqDist, ← hau, hv, zero_pow (by decide : 2 ≠ 0), add_zero, sq]
      exact mul_self_pos.mpr (sub_ne_zero.mpr hr)
  have hg : -c.gamma / 2 < 0 := by linarith [c.gamma_gt_two]
  have hj : Tendsto (fun r => c.beta * (sqDist c i r) ^ (-c.gamma / 2))
      (𝓝[≠] a) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero hg |>.comp hq).const_mul_atTop c.beta_pos
  have hc : Tendsto (fun r : ℝ => r ^ (-c.gamma)) (𝓝[≠] a) (𝓝 (a ^ (-c.gamma))) :=
    (analyticAt_rpow_pos (-c.gamma) ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_atBot.2
  intro M
  filter_upwards [hj.eventually_ge_atTop (a ^ (-c.gamma) + 1 - M),
    hc.eventually (eventually_lt_nhds (lt_add_one (a ^ (-c.gamma))))] with r hr hs
  have hsum : (sqDist c i r) ^ (-c.gamma / 2) ≤ ∑ j, (sqDist c j r) ^ (-c.gamma / 2) :=
    Finset.single_le_sum (fun j _ => Real.rpow_nonneg (sqDist_nonneg c j r) _) (Finset.mem_univ i)
  have hm := mul_le_mul_of_nonneg_left hsum c.beta_pos.le
  unfold field
  linarith

theorem analytic_zeros_finite_on_compact {f : ℝ → ℝ} {U K : Set ℝ} {a : ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hU : IsConnected U)
    (ha : a ∈ U) (hne : f a ≠ 0) (hK : IsCompact K) (hKU : K ⊆ U) :
    {x ∈ K | f x = 0}.Finite := by
  have hz := hf.preimage_zero_mem_codiscreteWithin hne ha hU
  have hzK : f ⁻¹' {0}ᶜ ∈ codiscreteWithin K := (codiscreteWithin_mono hKU) hz
  have heq : K \ (f ⁻¹' {0}ᶜ) = {x ∈ K | f x = 0} := by
    ext x
    simp
  rw [← heq]
  exact hK.finite_sdiff_of_mem_codiscreteWithin hzK

theorem isolated_of_left_divergence {f : ℝ → ℝ} {a b x : ℝ}
    (hax : a < x) (hxb : x < b) (hf : AnalyticOnNhd ℝ f (Ioo a b))
    (hlim : Tendsto f (𝓝[>] a) atTop ∨ Tendsto f (𝓝[>] a) atBot) :
    ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := by
  have hne : ∀ᶠ y in 𝓝[>] a, f y ≠ 0 := by
    rcases hlim with h | h
    · filter_upwards [h.eventually_ge_atTop 1] with y hy
      linarith
    · filter_upwards [h.eventually_le_atBot (-1)] with y hy
      linarith
  have hlt : ∀ᶠ y in 𝓝[>] a, y < b :=
    (eventually_lt_nhds (hax.trans hxb)).filter_mono nhdsWithin_le_nhds
  obtain ⟨z, hz0, hz1, hz2⟩ := (hne.and (hlt.and self_mem_nhdsWithin)).exists
  have hz : z ∈ Ioo a b := ⟨hz2, hz1⟩
  have hconn : IsConnected (Ioo a b) := ⟨⟨x, hax, hxb⟩, isPreconnected_Ioo⟩
  have hcod := hf.preimage_zero_mem_codiscreteWithin hz0 hz hconn
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hcod
  have hmem : ∀ᶠ y in 𝓝[≠] x, y ∈ Ioo a b :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨hax, hxb⟩)
  filter_upwards [hcod x ⟨hax, hxb⟩, hmem] with y hy hym
  rcases hy with hy | hy
  · exact hy
  · exact False.elim (hy hym)

def poles (c : Config ι) : Finset ℝ := by
  classical
  exact (Finset.univ.filter fun i => c.v i = 0).image c.u

theorem mem_poles_iff (c : Config ι) (r : ℝ) :
    r ∈ poles c ↔ ∃ i, sqDist c i r = 0 := by
  classical
  simp only [poles, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    sqDist_zero_iff]
  constructor
  · rintro ⟨i, hv, hu⟩
    exact ⟨i, hu.symm, hv⟩
  · rintro ⟨i, hu, hv⟩
    exact ⟨i, hv, hu.symm⟩

theorem zero_not_poles (c : Config ι) : 0 ∉ poles c := by
  intro h
  obtain ⟨i, hi⟩ := (mem_poles_iff c 0).mp h
  have hp : 0 < sqDist c i 0 := by simpa [sqDist] using c.away_origin i
  linarith

theorem regular_iff (c : Config ι) (r : ℝ) :
    r ∈ regular c ↔ 0 < r ∧ r ∉ poles c := by
  constructor
  · rintro ⟨hr, hq⟩
    refine ⟨hr, ?_⟩
    intro h
    obtain ⟨i, hi⟩ := (mem_poles_iff c r).mp h
    have := hq i
    linarith
  · rintro ⟨hr, hn⟩
    refine ⟨hr, fun i => ?_⟩
    apply lt_of_le_of_ne (sqDist_nonneg c i r)
    intro he
    exact hn ((mem_poles_iff c r).mpr ⟨i, he.symm⟩)

theorem regular_interval (c : Config ι) {x : ℝ} (hx : x ∈ regular c) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ (a = 0 ∨ a ∈ poles c) ∧
      Ioo a b ⊆ regular c := by
  classical
  have hx' := (regular_iff c x).mp hx
  let L := (insert 0 (poles c)).filter (fun a => a < x)
  let H := (insert (x + 1) (poles c)).filter (fun b => x < b)
  have hL0 : 0 ∈ L := by simp [L, hx'.1]
  have hH1 : x + 1 ∈ H := by simp [H]
  have hLn : L.Nonempty := ⟨0, hL0⟩
  have hHn : H.Nonempty := ⟨x + 1, hH1⟩
  let a := L.max' hLn
  let b := H.min' hHn
  have ham : a ∈ L := Finset.max'_mem L hLn
  have hbm : b ∈ H := Finset.min'_mem H hHn
  have ha0 : 0 ≤ a := Finset.le_max' L 0 hL0
  have hax : a < x := (Finset.mem_filter.mp ham).2
  have hxb : x < b := (Finset.mem_filter.mp hbm).2
  have hap : a = 0 ∨ a ∈ poles c := Finset.mem_insert.mp (Finset.mem_filter.mp ham).1
  refine ⟨a, b, ha0, hax, hxb, hap, ?_⟩
  intro r hr
  apply (regular_iff c r).mpr
  refine ⟨lt_of_le_of_lt ha0 hr.1, ?_⟩
  intro hp
  rcases lt_trichotomy r x with hrx | hrx | hrx
  · have hm : r ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hp, hrx⟩
    have hh : r ≤ a := Finset.le_max' L r hm
    linarith [hr.1]
  · exact hx'.2 (hrx ▸ hp)
  · have hm : r ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hp, hrx⟩
    have hh : b ≤ r := Finset.min'_le H r hm
    linarith [hr.2]

/- Local no-accumulation on the closed deployment radius suffices. The
physical instantiation must establish this condition, not assume it. -/
theorem finite_zeros_of_local_exclusion {f : ℝ → ℝ} {D : Set ℝ} {R : ℝ}
    (hD : D ⊆ Icc 0 R)
    (hlocal : ∀ x ∈ Icc 0 R, ∀ᶠ y in 𝓝[≠] x, y ∈ D → f y ≠ 0) :
    {y ∈ D | f y = 0}.Finite := by
  let Z : Set ℝ := {y ∈ D | f y = 0}
  have hz : Zᶜ ∈ codiscreteWithin (Icc 0 R) := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro x hx
    filter_upwards [hlocal x hx] with y hy
    left
    simpa only [Z, mem_compl_iff, mem_setOf_eq, not_and] using hy
  have hf := isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin hz
  have heq : Icc 0 R \ Zᶜ = Z := by
    ext y
    simp only [Set.mem_sdiff, mem_Icc, mem_compl_iff, not_not]
    exact ⟨fun h => h.2, fun h => ⟨hD h.1, h⟩⟩
  rwa [heq] at hf

theorem isolated_regular_zeros (c : Config ι) {x : ℝ} (hx : x ∈ regular c) :
    ∀ᶠ y in 𝓝[≠] x, field c y ≠ 0 := by
  obtain ⟨a, b, ha0, hax, hxb, hap, hI⟩ := regular_interval c hx
  apply isolated_of_left_divergence hax hxb (fun r hr => analyticAt_field c (hI hr))
  rcases hap with hap | hap
  · subst a
    exact Or.inl (field_tendsto_zero c)
  · have han : a ≠ 0 := by
      intro h
      exact zero_not_poles c (h ▸ hap)
    have ha : 0 < a := lt_of_le_of_ne ha0 (Ne.symm han)
    obtain ⟨i, hi⟩ := (mem_poles_iff c a).mp hap
    have hsub : Ioi a ⊆ ({a} : Set ℝ)ᶜ := by
      intro r hr
      exact ne_of_gt hr
    exact Or.inr ((field_tendsto_pole c ha i hi).mono_left (nhdsWithin_mono a hsub))

/-- General finite-jammer ray-root theorem. The hypotheses are exactly the
configuration's positive radius, threshold and exponent and nonzero jammer
positions; no finiteness, analyticity, or non-accumulation assumption is passed in. -/
theorem finite_ray_roots (c : Config ι) :
    {r ∈ domain c | field c r = 0}.Finite := by
  apply finite_zeros_of_local_exclusion (R := c.radius)
  · intro r hr
    exact ⟨hr.1.1.le, hr.2⟩
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      have hne : ∀ᶠ y in 𝓝[>] (0 : ℝ), field c y ≠ 0 := by
        filter_upwards [(field_tendsto_zero c).eventually_ge_atTop 1] with y hy
        linarith
      rw [eventually_nhdsWithin_iff] at hne
      filter_upwards [hne.filter_mono nhdsWithin_le_nhds] with y hy
      intro hyD
      exact hy hyD.1.1
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      by_cases hp : x ∈ poles c
      · obtain ⟨i, hi⟩ := (mem_poles_iff c x).mp hp
        filter_upwards [(field_tendsto_pole c hxpos i hi).eventually_le_atBot (-1)] with y hy
        intro _
        linarith
      · filter_upwards [isolated_regular_zeros c ((regular_iff c x).mpr ⟨hxpos, hp⟩)] with y hy
        exact fun _ => hy

theorem finite_bracket {s : Finset ℝ} {l x u : ℝ}
    (hl : l ∈ s) (hu : u ∈ s) (hlx : l < x) (hxu : x < u) (hx : x ∉ s) :
    ∃ a ∈ s, ∃ b ∈ s, l ≤ a ∧ a < x ∧ x < b ∧ b ≤ u ∧
      ∀ r ∈ Ioo a b, r ∉ s := by
  classical
  let L := s.filter (fun a => a < x)
  let H := s.filter (fun b => x < b)
  have hLl : l ∈ L := Finset.mem_filter.mpr ⟨hl, hlx⟩
  have hHu : u ∈ H := Finset.mem_filter.mpr ⟨hu, hxu⟩
  have hLn : L.Nonempty := ⟨l, hLl⟩
  have hHn : H.Nonempty := ⟨u, hHu⟩
  let a := L.max' hLn
  let b := H.min' hHn
  have ham : a ∈ L := Finset.max'_mem L hLn
  have hbm : b ∈ H := Finset.min'_mem H hHn
  have hal : l ≤ a := Finset.le_max' L l hLl
  have hbu : b ≤ u := Finset.min'_le H u hHu
  refine ⟨a, (Finset.mem_filter.mp ham).1, b, (Finset.mem_filter.mp hbm).1,
    hal, (Finset.mem_filter.mp ham).2, (Finset.mem_filter.mp hbm).2, hbu, ?_⟩
  intro r hr hp
  rcases lt_trichotomy r x with hrx | hrx | hrx
  · have hm : r ∈ L := Finset.mem_filter.mpr ⟨hp, hrx⟩
    have hh : r ≤ a := Finset.le_max' L r hm
    linarith [hr.1]
  · exact hx (hrx ▸ hp)
  · have hm : r ∈ H := Finset.mem_filter.mpr ⟨hp, hrx⟩
    have hh : b ≤ r := Finset.min'_le H r hm
    linarith [hr.2]

theorem interval_nonneg_of_no_zero {f : ℝ → ℝ} {a b x : ℝ}
    (hf : ContinuousOn f (Ioo a b)) (hne : ∀ r ∈ Ioo a b, f r ≠ 0)
    (hx : x ∈ Ioo a b) (hx0 : 0 ≤ f x) :
    ∀ r ∈ Ioo a b, 0 ≤ f r := by
  intro r hr
  by_contra h
  have hneg : f r < 0 := lt_of_not_ge h
  obtain ⟨z, hz, hzero⟩ :=
    isPreconnected_Ioo.intermediate_value hr hx hf (show (0 : ℝ) ∈ Icc (f r) (f x) from ⟨hneg.le, hx0⟩)
  exact hne z hz hzero

def cuts (c : Config ι) : Finset ℝ := by
  classical
  exact insert 0 (insert c.radius (poles c ∪ (finite_ray_roots c).toFinset))

theorem zero_mem_cuts (c : Config ι) : 0 ∈ cuts c := by
  classical
  simp [cuts]
theorem radius_mem_cuts (c : Config ι) : c.radius ∈ cuts c := by
  classical
  simp [cuts]
theorem poles_subset_cuts (c : Config ι) : ∀ r ∈ poles c, r ∈ cuts c := by
  classical
  intro r hr
  simp [cuts, hr]

theorem roots_subset_cuts (c : Config ι) {r : ℝ}
    (hr : r ∈ domain c) (hz : field c r = 0) : r ∈ cuts c := by
  classical
  have hm : r ∈ (finite_ray_roots c).toFinset := (finite_ray_roots c).mem_toFinset.mpr ⟨hr, hz⟩
  simp [cuts, hm]

theorem cell_success (c : Config ι) {a b x : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ c.radius) (hgap : ∀ r ∈ Ioo a b, r ∉ cuts c)
    (hx : x ∈ Ioo a b) (hxS : x ∈ success c) :
    Ioo a b ⊆ success c := by
  have hD : Ioo a b ⊆ domain c := by
    intro r hr
    refine ⟨(regular_iff c r).mpr ⟨lt_of_le_of_lt ha hr.1, ?_⟩, hr.2.le.trans hb⟩
    intro hp
    exact hgap r hr (poles_subset_cuts c r hp)
  have hne : ∀ r ∈ Ioo a b, field c r ≠ 0 := by
    intro r hr hz
    exact hgap r hr (roots_subset_cuts c (hD hr) hz)
  have hcont : ContinuousOn (field c) (Ioo a b) :=
    fun r hr => (analyticAt_field c (hD hr).1).continuousAt.continuousWithinAt
  have hpos := interval_nonneg_of_no_zero hcont hne hx hxS.2
  intro r hr
  exact ⟨hD hr, hpos r hr⟩

def intervalFamily (c : Config ι) : Finset (Set ℝ) := by
  classical
  exact (((cuts c).product (cuts c)).filter
    (fun ab => Ioo ab.1 ab.2 ⊆ success c)).image (fun ab => Ioo ab.1 ab.2) ∪
    ((cuts c).filter (fun x => x ∈ success c)).image (fun x => ({x} : Set ℝ))

/-- Exact finite ray decomposition. Open cells and singleton endpoints are
listed separately; their union is closed relative to the physical domain. -/
theorem success_eq_finite_interval_union (c : Config ι) :
    success c = ⋃ J ∈ intervalFamily c, J := by
  classical
  ext x
  constructor
  · intro hx
    by_cases hxc : x ∈ cuts c
    · simp only [mem_iUnion]
      refine ⟨{x}, ?_, by simp⟩
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxc, hx⟩, rfl⟩
    · have hx0 : 0 < x := hx.1.1.1
      have hxR : x < c.radius := by
        have hle : x ≤ c.radius := hx.1.2
        have hne : x ≠ c.radius := by
          intro he
          exact hxc (he ▸ radius_mem_cuts c)
        exact lt_of_le_of_ne hle hne
      obtain ⟨a, ha, b, hb, ha0, hax, hxb, hbR, hgap⟩ :=
        finite_bracket (zero_mem_cuts c) (radius_mem_cuts c) hx0 hxR hxc
      have hcell := cell_success c ha0 hbR hgap ⟨hax, hxb⟩ hx
      simp only [mem_iUnion]
      refine ⟨Ioo a b, ?_, ⟨hax, hxb⟩⟩
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      exact ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩, hcell⟩, rfl⟩
  · simp only [mem_iUnion]
    rintro ⟨J, hJ, hxJ⟩
    rcases Finset.mem_union.mp hJ with hJ | hJ
    · obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hJ
      exact (Finset.mem_filter.mp hab).2 hxJ
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hJ
      have he : x = r := Set.mem_singleton_iff.mp hxJ
      exact he ▸ (Finset.mem_filter.mp hr).2

theorem intervalFamily_ordConnected (c : Config ι) :
    ∀ J ∈ intervalFamily c, Set.OrdConnected J := by
  classical
  intro J hJ
  rcases Finset.mem_union.mp hJ with hJ | hJ
  · obtain ⟨ab, _, rfl⟩ := Finset.mem_image.mp hJ
    exact Set.ordConnected_Ioo
  · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hJ
    exact Set.ordConnected_singleton

theorem success_relatively_closed (c : Config ι) :
    IsClosed {x : domain c | 0 ≤ field c x} := by
  have hf : ContinuousOn (field c) (domain c) :=
    fun r hr => (analyticAt_field c hr.1).continuousAt.continuousWithinAt
  change IsClosed ((fun x : domain c => field c x) ⁻¹' Ici 0)
  exact isClosed_Ici.preimage (continuousOn_iff_continuous_restrict.mp hf)

theorem intervalFamily_subset_success (c : Config ι) {J : Set ℝ}
    (hJ : J ∈ intervalFamily c) : J ⊆ success c := by
  intro x hx
  rw [success_eq_finite_interval_union]
  exact mem_iUnion.mpr ⟨J, mem_iUnion.mpr ⟨hJ, hx⟩⟩

theorem closure_inter_domain_subset_success (c : Config ι) {J : Set ℝ}
    (hJ : J ⊆ success c) : closure J ∩ domain c ⊆ success c := by
  intro r hr
  refine ⟨hr.2, ?_⟩
  have hm : MapsTo (field c) J (Ici 0) := fun y hy => (hJ hy).2
  have hc := (analyticAt_field c hr.2.1).continuousAt.continuousWithinAt.mem_closure hr.1 hm
  simpa only [isClosed_Ici.closure_eq, mem_Ici] using hc

theorem interval_closure_inter_ordConnected {D : Set ℝ} {a b : ℝ}
    (hD : Ioo a b ⊆ D) : Set.OrdConnected (closure (Ioo a b) ∩ D) := by
  have hcl : closure (Ioo a b) ⊆ Icc a b := closure_minimal Ioo_subset_Icc_self isClosed_Icc
  apply Set.ordConnected_of_Ioo
  intro x hx y hy _ z hz
  have hzcell : z ∈ Ioo a b := ⟨(hcl hx.1).1.trans_lt hz.1, hz.2.trans_le (hcl hy.1).2⟩
  exact ⟨subset_closure hzcell, hD hzcell⟩

def closedIntervalFamily (c : Config ι) : Finset (Set ℝ) := by
  classical
  exact (intervalFamily c).image (fun J => closure J ∩ domain c)

/-- Complete decomposition into finitely many intervals, each closed in
the punctured ray domain. This retains the origin component (0,a]. -/
theorem success_eq_finite_relatively_closed_intervals (c : Config ι) :
    success c = ⋃ J ∈ closedIntervalFamily c, J := by
  classical
  ext x
  constructor
  · intro hx
    have hxu := hx
    rw [success_eq_finite_interval_union] at hxu
    simp only [mem_iUnion] at hxu ⊢
    obtain ⟨J, hJ, hxJ⟩ := hxu
    exact ⟨closure J ∩ domain c, Finset.mem_image.mpr ⟨J, hJ, rfl⟩, subset_closure hxJ, hx.1⟩
  · simp only [mem_iUnion]
    rintro ⟨K, hK, hxK⟩
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hK
    exact closure_inter_domain_subset_success c (intervalFamily_subset_success c hJ) hxK

theorem closedIntervalFamily_properties (c : Config ι) :
    ∀ K ∈ closedIntervalFamily c,
      Set.OrdConnected K ∧ IsClosed ((fun x : domain c => (x : ℝ)) ⁻¹' K) := by
  classical
  intro K hK
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hK
  constructor
  · rcases Finset.mem_union.mp hJ with hJ | hJ
    · obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hJ
      apply interval_closure_inter_ordConnected
      intro r hr
      exact ((Finset.mem_filter.mp hab).2 hr).1
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hJ
      have hD : ({r} : Set ℝ) ⊆ domain c :=
        Set.singleton_subset_iff.mpr (Finset.mem_filter.mp hr).2.1
      rw [isClosed_singleton.closure_eq, inter_eq_left.mpr hD]
      exact Set.ordConnected_singleton
  · have heq : (fun x : domain c => (x : ℝ)) ⁻¹' (closure J ∩ domain c) =
        (fun x : domain c => (x : ℝ)) ⁻¹' closure J := by
      ext x
      simp only [mem_preimage, mem_inter_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, x.property⟩⟩
    rw [heq]
    exact isClosed_closure.preimage continuous_subtype_val

theorem isOpen_regular (c : Config ι) : IsOpen (regular c) := by
  have heq : regular c = Ioi 0 ∩ ⋂ i, (sqDist c i) ⁻¹' Ioi 0 := by
    ext r
    simp [regular]
  rw [heq]
  apply isOpen_Ioi.inter
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_Ioi.preimage
  unfold sqDist
  fun_prop

/-- Any boundary point strictly inside the deployment disk that is not a
jammer singularity is a zero of the analytic boundary function. -/
theorem interior_boundary_is_root (c : Config ι) {r : ℝ}
    (hr : r ∈ regular c) (hrR : r < c.radius) (hf : r ∈ frontier (success c)) :
    field c r = 0 := by
  have hc := (analyticAt_field c hr).continuousAt
  by_contra hne
  rcases lt_or_gt_of_ne hne with hn | hp
  · have hev : ∀ᶠ y in 𝓝 r, field c y < 0 :=
      hc.tendsto.eventually (eventually_lt_nhds hn)
    have hfreq : ∃ᶠ y in 𝓝 r, y ∈ success c := mem_closure_iff_frequently.mp hf.1
    obtain ⟨y, hyS, hyneg⟩ := (hfreq.and_eventually hev).exists
    linarith [hyS.2]
  · have hdm : domain c ∈ 𝓝 r := by
      apply Filter.inter_mem ((isOpen_regular c).mem_nhds hr)
      have hb : ∀ᶠ y in 𝓝 r, y < c.radius := eventually_lt_nhds hrR
      exact hb.mono (fun y hy => show y ∈ Iic c.radius from hy.le)
    have hev : ∀ᶠ y in 𝓝 r, 0 < field c y :=
      hc.tendsto.eventually (eventually_gt_nhds hp)
    have hS : success c ∈ 𝓝 r := by
      filter_upwards [hdm, hev] with y hyD hy
      exact ⟨hyD, hy.le⟩
    exact hf.2 (mem_interior_iff_mem_nhds.mpr hS)

theorem rotated_norm_sq (d t : ℝ) :
    (d * Real.cos t) ^ 2 + (d * Real.sin t) ^ 2 = d ^ 2 := by
  calc
    _ = d ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
    _ = d ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]

def ofPolar (d phi : ι → ℝ) (theta gamma beta R : ℝ)
    (hd : ∀ i, 0 < d i) (hg : 2 < gamma) (hb : 0 < beta) (hR : 0 < R) : Config ι where
  u i := d i * Real.cos (theta - phi i)
  v i := d i * Real.sin (theta - phi i)
  gamma := gamma
  beta := beta
  radius := R
  gamma_gt_two := hg
  beta_pos := hb
  radius_pos := hR
  away_origin i := by
    rw [rotated_norm_sq]
    exact sq_pos_of_pos (hd i)

/-- The rotated-coordinate model is exactly the paper's polar squared
distance, for arbitrary theta and jammer angles. -/
theorem sqDist_ofPolar (d phi : ι → ℝ) (theta gamma beta R : ℝ)
    (hd : ∀ i, 0 < d i) (hg : 2 < gamma) (hb : 0 < beta) (hR : 0 < R)
    (i : ι) (r : ℝ) :
    sqDist (ofPolar d phi theta gamma beta R hd hg hb hR) i r =
      r ^ 2 + d i ^ 2 - 2 * r * d i * Real.cos (theta - phi i) := by
  have h := rotated_norm_sq (d i) (theta - phi i)
  dsimp [sqDist, ofPolar]
  nlinarith

/-- Replacing each squared-distance power with rho^(-gamma), rho=sqrt(q),
recovers the exact analytic field used in the manuscript. -/
theorem field_sqrt_formula (c : Config ι) (r : ℝ) :
    field c r = r ^ (-c.gamma) -
      c.beta * ∑ i, (Real.sqrt (sqDist c i r)) ^ (-c.gamma) := by
  have hi : ∀ i, (Real.sqrt (sqDist c i r)) ^ (-c.gamma) =
      (sqDist c i r) ^ (-c.gamma / 2) := by
    intro i
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (sqDist_nonneg c i r)]
    congr 1
    ring
  simp_rw [hi]
  rfl

/-- The sign test is precisely the SINR threshold test when at least one
jammer is present; the interference denominator is proved positive. -/
theorem field_nonneg_iff_sinr [Nonempty ι] (c : Config ι) {r : ℝ}
    (hr : r ∈ regular c) :
    0 ≤ field c r ↔
      c.beta ≤ r ^ (-c.gamma) / (∑ i, sqDist c i r ^ (-c.gamma / 2)) := by
  have hs : 0 < ∑ i, sqDist c i r ^ (-c.gamma / 2) :=
    Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hr.2 i) _) Finset.univ_nonempty
  rw [le_div_iff₀ hs, field, sub_nonneg]

#print axioms analyticAt_field
#print axioms field_tendsto_zero
#print axioms field_tendsto_pole
#print axioms analytic_zeros_finite_on_compact
#print axioms finite_zeros_of_local_exclusion
#print axioms isolated_regular_zeros
#print axioms finite_ray_roots
#print axioms success_eq_finite_interval_union
#print axioms intervalFamily_ordConnected
#print axioms success_relatively_closed
#print axioms success_eq_finite_relatively_closed_intervals
#print axioms closedIntervalFamily_properties
#print axioms interior_boundary_is_root
#print axioms sqDist_ofPolar
#print axioms field_sqrt_formula
#print axioms field_nonneg_iff_sinr

end
end R260402Geometry
