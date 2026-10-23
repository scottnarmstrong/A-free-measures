module

public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import PDEFoundation.Ambient.Basic

/-!
# Doubling scales of singular measures

Cubes `Q_r(x)` are
`Metric.closedBall x r` on `Vec d` (sup metric).

* `AFree.ae_tendsto_volume_div_closedBall_zero`: the density of Lebesgue measure with respect to `ρ` vanishes.
* `AFree.exists_doubling_scale`: the doubling scales at a single point.
* `AFree.ae_doubling_scales`: the combined a.e. statement.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace AFree

open PDE

/-- For a finite measure `ρ` singular to Lebesgue measure, at `ρ`-a.e. `x` every cube centred at `x`
has positive `ρ`-measure and `|Q_r(x)| / ρ(Q_r(x)) → 0` as `r ↓ 0`. -/
theorem ae_tendsto_volume_div_closedBall_zero {d : ℕ} (ρ : Measure (Vec d)) [IsFiniteMeasure ρ]
    (hρ : ρ ⟂ₘ volume) :
    ∀ᵐ x ∂ρ, (∀ r, 0 < r → 0 < ρ (Metric.closedBall x r)) ∧
      Tendsto (fun r => volume (Metric.closedBall x r) / ρ (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 0) := by
  have h1 := Besicovitch.ae_tendsto_rnDeriv (volume : Measure (Vec d)) ρ
  have h2 : ∀ᵐ x ∂ρ, (volume : Measure (Vec d)).rnDeriv ρ x = 0 :=
    Measure.rnDeriv_eq_zero_of_mutuallySingular hρ.symm Measure.AbsolutelyContinuous.rfl
  filter_upwards [h1, h2] with x hx hx0
  rw [hx0] at hx
  refine ⟨fun r hr => ?_, hx⟩
  by_contra hcon
  have h0 : ρ (Metric.closedBall x r) = 0 := by simpa using hcon
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), volume (Metric.closedBall x s) /
      ρ (Metric.closedBall x s) < 1 := hx.eventually (gt_mem_nhds zero_lt_one)
  have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < r ∧ 0 < s := by
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs using ⟨hs.2, hs.1⟩
  obtain ⟨s, hs1, hs2, hs3⟩ := (hev.and hev2).exists
  have hz : ρ (Metric.closedBall x s) = 0 :=
    measure_mono_null (Metric.closedBall_subset_closedBall hs2.le) h0
  have hv : volume (Metric.closedBall x s) ≠ 0 := by
    rw [Real.volume_pi_closedBall _ hs3.le]
    simp [hs3]
  rw [hz, ENNReal.div_zero hv] at hs1
  simp at hs1

/-- At a point satisfying the conclusion of `ae_tendsto_volume_div_closedBall_zero`, for `t ∈ (0, 1)`
there are arbitrarily small `r` with `t^(d+1) ρ(Q_r(x)) ≤ ρ(Q_{tr}(x))`. -/
theorem exists_doubling_scale {d : ℕ} (ρ : Measure (Vec d)) [IsFiniteMeasure ρ]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {x : Vec d}
    (hpos : ∀ r, 0 < r → 0 < ρ (Metric.closedBall x r))
    (hlim : Tendsto (fun r => volume (Metric.closedBall x r) / ρ (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 0)) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ r ∈ Set.Ioo 0 r₀,
      ENNReal.ofReal (t ^ (d + 1)) * ρ (Metric.closedBall x r) ≤
        ρ (Metric.closedBall x (t * r)) := by
  by_contra hcon
  push Not at hcon
  set T : ℝ≥0∞ := ENNReal.ofReal (t ^ (d + 1)) with hT
  set p : ℕ → ℝ := fun k => t ^ (k + 1) * r₀ with hp
  have hppos : ∀ k, 0 < p k := fun k => by positivity
  have hplt : ∀ k, p k < r₀ := fun k => by
    have : t ^ (k + 1) < 1 := pow_lt_one₀ ht0.le ht1 (Nat.succ_ne_zero k)
    simpa [hp] using mul_lt_mul_of_pos_right this hr₀
  have hstep : ∀ k, ρ (Metric.closedBall x (p (k + 1))) ≤
      T * ρ (Metric.closedBall x (p k)) := fun k => by
    have := hcon (p k) ⟨hppos k, hplt k⟩
    have e : p (k + 1) = t * p k := by simp [hp]; ring
    rw [e]; exact this.le
  have hbound : ∀ k, ρ (Metric.closedBall x (p k)) ≤ T ^ k * ρ (Metric.closedBall x (p 0)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc _ ≤ T * ρ (Metric.closedBall x (p k)) := hstep k
        _ ≤ T * (T ^ k * ρ (Metric.closedBall x (p 0))) := by gcongr
        _ = _ := by rw [pow_succ, mul_assoc, mul_left_comm]
  have htr : Tendsto (fun k : ℕ => t ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ht0.le ht1
  have hpt : Tendsto p atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hppos⟩
    have := ((htr.comp (tendsto_add_atTop_nat 1)).mul_const r₀)
    simpa [hp] using this
  have hev := (hpt.eventually (hlim.eventually (gt_mem_nhds zero_lt_one)))
  set a : ℝ := (ρ (Metric.closedBall x (p 0))).toReal with ha
  have hapos : 0 < a := ENNReal.toReal_pos (hpos _ (hppos 0)).ne' (measure_ne_top ρ _)
  set c : ℝ := (2 * (t * r₀)) ^ d with hc
  have hcpos : 0 < c := by positivity
  have hev2 : ∀ᶠ k : ℕ in atTop, t ^ k * a < c :=
    (htr.mul_const a).eventually (gt_mem_nhds (by simpa using hcpos))
  obtain ⟨k, hk1, hk2⟩ := (hev.and hev2).exists
  have hpk : 0 < ρ (Metric.closedBall x (p k)) := hpos _ (hppos k)
  have h3 : volume (Metric.closedBall x (p k)) < 1 * ρ (Metric.closedBall x (p k)) :=
    (ENNReal.div_lt_iff (Or.inl hpk.ne') (Or.inl (measure_ne_top ρ _))).1 hk1
  rw [one_mul, Real.volume_pi_closedBall _ (hppos k).le] at h3
  have h4 := h3.trans_le (hbound k)
  have hlam0 : ρ (Metric.closedBall x (p 0)) = ENNReal.ofReal a :=
    (ENNReal.ofReal_toReal (measure_ne_top ρ _)).symm
  rw [hlam0, hT, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    Fintype.card_fin, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h4
  have e1 : (2 * p k) ^ d = c * (t ^ k) ^ d := by
    have : 2 * p k = (2 * (t * r₀)) * t ^ k := by simp only [hp]; ring
    rw [this, mul_pow]
  have e2 : (t ^ (d + 1)) ^ k = (t ^ k) ^ d * t ^ k := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  rw [e1, e2, mul_assoc, mul_comm c] at h4
  have hq : 0 < (t ^ k) ^ d := by positivity
  have := lt_of_mul_lt_mul_left h4 hq.le
  linarith

/-- Combination of the two preceding statements: `ρ`-a.e. `x` has the properties of both. -/
theorem ae_doubling_scales {d : ℕ} (ρ : Measure (Vec d)) [IsFiniteMeasure ρ]
    (hρ : ρ ⟂ₘ volume) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ᵐ x ∂ρ, (∀ r, 0 < r → 0 < ρ (Metric.closedBall x r)) ∧
      Tendsto (fun r => volume (Metric.closedBall x r) / ρ (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 0) ∧
      ∀ r₀, 0 < r₀ → ∃ r ∈ Set.Ioo 0 r₀,
        ENNReal.ofReal (t ^ (d + 1)) * ρ (Metric.closedBall x r) ≤
          ρ (Metric.closedBall x (t * r)) := by
  filter_upwards [ae_tendsto_volume_div_closedBall_zero ρ hρ] with x hx
  exact ⟨hx.1, hx.2, fun r₀ hr₀ => exists_doubling_scale ρ ht0 ht1 hx.1 hx.2 r₀ hr₀⟩

end AFree
