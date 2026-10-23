module

public import AFree.Paper.Bessel.Fourier
public import AFree.Harmonic.Kernel.NegativeLp

/-!
# The Bessel kernel

With `b = negKernel (besselSymbol s)`: `b ∈ L¹` and `T_{m_s} u = b ⋆ u` on Schwartz functions; `b ∈ L^p`
for `p < p(d,s)`; the real part `Re b` is in `L¹ ∩ L^p` and `‖Re b - Re β‖_p ≤ ‖b - β‖_p`; and
`besselPotential_s u = b ⋆ u` for smooth `u` supported in `B₁`. These are the ingredients of the proof of
[DPR, Lemma 2.1].
-/

@[expose] public section

open MeasureTheory PDE
open scoped SchwartzMap ENNReal

namespace AFree.Bessel

variable {d : ℕ}

/-- The Bessel kernel `b = negKernel (besselSymbol s)`. -/
noncomputable def besselKernel (d : ℕ) (s : ℝ) : Vec d → ℂ :=
  negKernel (besselSymbol (d := d) s)

/-- `b ∈ L¹` and `T_{m_s} u = b ⋆ u` on Schwartz functions. -/
theorem besselKernel_a {s : ℝ} (hs : 0 < s) :
    Integrable (besselKernel d s) ∧ ∀ (u : 𝓢(Vec d, ℂ)) (x : Vec d),
      vecMultiplier (besselSymbol s) u x = ∫ y, besselKernel d s (x - y) * u y :=
  ⟨integrable_negKernel hs (isSymbol_besselSymbol s),
    fun u x => vecMultiplier_eq_negKernel hs (isSymbol_besselSymbol s) u x⟩

/-- `b ∈ L^p` for `1 ≤ p < p(d,s)`. -/
theorem besselKernel_b (hd : 0 < d) {s : ℝ} (hs : 0 < s) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p < besselExponent d s) : MemLp (besselKernel d s) p volume := by
  have hpt : p ≠ ⊤ := ne_top_of_lt (hp.trans_le le_top)
  have hq : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp1; simpa using this
  have hq0 : 0 < p.toReal := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpq : p = ENNReal.ofReal p.toReal := (ENNReal.ofReal_toReal hpt).symm
  have key : ∃ s' : ℝ, 0 < s' ∧ s' ≤ s ∧ p.toReal * ((d : ℝ) - s') < d := by
    by_cases hsd : s < d
    · refine ⟨s, hs, le_rfl, ?_⟩
      simp only [besselExponent, hsd, ↓reduceIte] at hp
      have hds : 0 < (d : ℝ) - s := by linarith
      have h1 : p.toReal < d / (d - s) :=
        (ENNReal.lt_ofReal_iff_toReal_lt hpt).1 hp
      exact (lt_div_iff₀ hds).1 h1
    · have hsd := not_lt.1 hsd
      refine ⟨d * (1 - 1 / (2 * p.toReal)), ?_, ?_, ?_⟩
      · have : 1 / (2 * p.toReal) ≤ 1 / 2 := by
          rw [one_div_le_one_div (by positivity) (by norm_num)]; linarith
        have h2 : 0 < 1 - 1 / (2 * p.toReal) := by linarith
        positivity
      · have : 0 < 1 / (2 * p.toReal) := by positivity
        nlinarith
      · have : (d : ℝ) - d * (1 - 1 / (2 * p.toReal)) = d / (2 * p.toReal) := by
          field_simp; ring
        rw [this]
        have : p.toReal * (d / (2 * p.toReal)) = d / 2 := by field_simp
        rw [this]; linarith
  obtain ⟨s', hs', hss', hps'⟩ := key
  have hm : IsSymbol (-s') (besselSymbol (d := d) s) :=
    (isSymbol_besselSymbol (d := d) s).mono (by linarith)
  rw [hpq]
  exact memLp_negKernel hd hs' hm hq hps'

/-- `Re b ∈ L¹ ∩ L^p` and `‖Re b - Re β‖_p ≤ ‖b - β‖_p`. -/
theorem besselKernel_c (hd : 0 < d) {s : ℝ} (hs : 0 < s) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p < besselExponent d s) :
    Integrable (fun x => (besselKernel d s x).re) ∧
      MemLp (fun x => (besselKernel d s x).re) p volume ∧
      ∀ β : Vec d → ℂ, eLpNorm (fun x => (besselKernel d s x).re - (β x).re) p volume ≤
        eLpNorm (fun x => besselKernel d s x - β x) p volume :=
  ⟨(besselKernel_a (d := d) hs).1.re, (besselKernel_b hd hs hp1 hp).re, fun β => by
    by_cases hβ : AEStronglyMeasurable (fun x => besselKernel d s x - β x) volume
    · refine eLpNorm_mono_ae ?_ (Filter.Eventually.of_forall fun x => ?_)
      · simpa [Complex.sub_re] using Complex.continuous_re.comp_aestronglyMeasurable hβ
      · simpa [← Complex.sub_re] using Complex.abs_re_le_norm (besselKernel d s x - β x)
    · rw [eLpNorm_of_not_aestronglyMeasurable hβ]; exact le_top⟩

/-- `besselPotential_s u = b ⋆ u` for smooth `u` supported in `B₁`. -/
theorem besselKernel_d {s : ℝ} (hs : 0 < s) (u : Vec d → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hsupp : tsupport u ⊆ euclideanBall (0 : Vec d) 1) (x : Vec d) :
    besselPotential s u x = ∫ y, besselKernel d s (x - y) * (u y : ℂ) := by
  have hc : HasCompactSupport u :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec d) 1) (isClosed_tsupport u)
      (fun y hy => Metric.ball_subset_closedBall
        (euclideanBall_subset_supBall (x₀ := (0 : Vec d)) (R := 1) one_pos (hsupp hy)))
  have hf : ⇑(toSchwartzC u hu hc) = fun y => (u y : ℂ) := funext (toSchwartzC_apply u hu hc)
  have h1 := vecMultiplier_besselSymbol_eq s (toSchwartzC u hu hc) x
  have h2 := (besselKernel_a (d := d) hs).2 (toSchwartzC u hu hc) x
  rw [hf] at h1
  simp only [toSchwartzC_apply] at h2
  rw [besselPotential, ← h1, h2]

end AFree.Bessel
