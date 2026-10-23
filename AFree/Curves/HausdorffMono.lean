module

public import AFree.Curves.HausdorffLip

/-!
# `𝓗¹` on `e`-monotone curves

Such curves are injective and bi-Lipschitz-comparable with their parameter.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

private lemma sub_unit (e : Vec d) (he : vecEuclideanNorm e = 1) (x y : Vec d) :
    |vecDot x e - vecDot y e| ≤ vecEuclideanNorm (x - y) := by
  rw [← vecDot_sub_left]
  simpa [he] using abs_vecDot_le_vecEuclideanNorm_mul (x - y) e

/-- Let `γ` be `1`-Lipschitz on `[a, b]` (Euclidean norm)
with `(γ s' - γ s) ⬝ e ≥ c (s' - s)` for `s ≤ s'` in `[a, b]`, `|e| = 1`, `c > 0`. Then `γ` is
injective on `[a, b]` and for every `A ⊆ [a, b]`: `c 𝓛¹(A) ≤ 𝓗¹(γ(A)) ≤ 𝓛¹(A)`. -/
theorem hausdorffOne_monotone_curve {γ : ℝ → Vec d} {a b c : ℝ} {e : Vec d}
    (he : vecEuclideanNorm e = 1) (hc : 0 < c)
    (hL : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, vecEuclideanNorm (γ s' - γ s) ≤ |s' - s|)
    (hm : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s ≤ s' → c * (s' - s) ≤ vecDot (γ s' - γ s) e) :
    InjOn γ (Icc a b) ∧ ∀ A ⊆ Icc a b,
      ENNReal.ofReal c * volume A ≤ euclideanHausdorffOne d (γ '' A) ∧
        euclideanHausdorffOne d (γ '' A) ≤ volume A := by
  set φ : ℝ → ℝ := fun s => vecDot (γ s) e with hφ
  have hφm : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, c * |s - s'| ≤ |φ s - φ s'| := by
    intro s hs s' hs'
    rcases le_total s s' with h | h
    · have := hm s hs s' hs' h
      rw [vecDot_sub_left] at this
      have hp := mul_nonneg hc.le (sub_nonneg.mpr h)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by simp only [hφ]; linarith)]
      simp only [hφ]; linarith
    · have := hm s' hs' s hs h
      rw [vecDot_sub_left] at this
      have hp := mul_nonneg hc.le (sub_nonneg.mpr h)
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by simp only [hφ]; linarith)]
      simp only [hφ]; linarith
  have hinj : InjOn γ (Icc a b) := by
    intro s hs s' hs' h
    have := hφm s hs s' hs'
    have h0 : |φ s - φ s'| = 0 := by simp [hφ, h]
    rw [h0] at this
    have : |s - s'| ≤ 0 := by nlinarith [abs_nonneg (s - s')]
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
  refine ⟨hinj, fun A hA => ⟨?_, ?_⟩⟩
  · have hinjφ : InjOn φ A := by
      intro s hs s' hs' h
      have := hφm s (hA hs) s' (hA hs')
      rw [h, sub_self, abs_zero] at this
      have : |s - s'| ≤ 0 := by nlinarith [abs_nonneg (s - s')]
      exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
    set ψ : ℝ → ℝ := Function.invFunOn φ A with hψ
    have hψφ : ∀ s ∈ A, ψ (φ s) = s := fun s hs => hinjφ.leftInvOn_invFunOn hs
    have hlip : LipschitzOnWith (Real.toNNReal c⁻¹) ψ (φ '' A) := by
      refine LipschitzOnWith.of_dist_le_mul ?_
      rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
      rw [hψφ s hs, hψφ s' hs', Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), Real.dist_eq,
        Real.dist_eq, inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
      exact hφm s (hA hs) s' (hA hs')
    have himg : ψ '' (φ '' A) = A := by
      rw [image_image]; exact (image_congr hψφ).trans (image_id' A)
    have h1 := hlip.hausdorffMeasure_image_le (zero_le_one' ℝ)
    rw [himg, ENNReal.rpow_one, hausdorffMeasure_real] at h1
    have h2 : volume (φ '' A) ≤ euclideanHausdorffOne d (γ '' A) := by
      have := volume_image_le_hausdorffOne (π := fun x : Vec d => vecDot x e) (sub_unit e he)
        (γ '' A)
      rwa [image_image] at this
    calc ENNReal.ofReal c * volume A ≤ ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * volume (φ '' A)) :=
          mul_le_mul_right h1 _
      _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * euclideanHausdorffOne d (γ '' A)) :=
          mul_le_mul_right (mul_le_mul_right h2 _) _
      _ = euclideanHausdorffOne d (γ '' A) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne']; simp
  · have := hausdorffOne_image_le_pos (B := Icc a b) hA (γ := γ) (L := 1) one_pos
      (fun x hx y hy => by simpa using hL y hy x hx)
    simpa using this

end AFree
