module

public import AFree.Curves.Rainwater.GkCurve

/-!
# Measure comparison on `𝒢(C)`
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- The volume of a subset `A` of `[0,1]` is the Lebesgue outer measure of `A ⊂ ℝ`. -/
lemma volume_unitInterval_apply (A : Set I) : volume A = volume ((↑) '' A : Set ℝ) :=
  (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply volume A

/-- For `γ ∈ 𝒢(C)`, `A ⊆ [0,1]`:
`cos α · 𝓛¹(A) ≤ 𝓗¹(γ(A)) ≤ 𝓛¹(A)`; for `E ⊆ ℝ^d`: `𝓗¹(E ∩ γ[0,1]) ≤ 𝓛¹(γ⁻¹E)` and
`𝓛¹(γ⁻¹E) ≤ (cos α)⁻¹ 𝓗¹(E ∩ γ[0,1])`. -/
theorem ccurveSpace_measure_comparison {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ}
    (hα : 0 < α) (hα2 : α < Real.pi / 2) {γ : C(I, Vec d)} (hγ : γ ∈ ccurveSpace e α) :
    (∀ A : Set I, ENNReal.ofReal (Real.cos α) * volume A ≤ euclideanHausdorffOne d (γ '' A) ∧
      euclideanHausdorffOne d (γ '' A) ≤ volume A) ∧
    ∀ E : Set (Vec d), euclideanHausdorffOne d (E ∩ range γ) ≤ volume (γ ⁻¹' E) ∧
      volume (γ ⁻¹' E) ≤ ENNReal.ofReal (Real.cos α)⁻¹ * euclideanHausdorffOne d (E ∩ range γ) := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hmono := hausdorffOne_monotone_curve (γ := ccurveExt γ) (a := 0) (b := 1) he hc
    (fun s hs s' hs' => by
      rw [ccurveExt_of_mem γ hs, ccurveExt_of_mem γ hs']
      exact ccurveSpace_dist_le hγ ⟨s, hs⟩ ⟨s', hs'⟩)
    (fun s hs s' hs' hss' => by
      rw [ccurveExt_of_mem γ hs, ccurveExt_of_mem γ hs']
      exact (hγ ⟨s, hs⟩ ⟨s', hs'⟩ hss').2)
  have hA : ∀ A : Set I, ENNReal.ofReal (Real.cos α) * volume A ≤
      euclideanHausdorffOne d (γ '' A) ∧ euclideanHausdorffOne d (γ '' A) ≤ volume A := by
    intro A
    have himg : γ '' A = ccurveExt γ '' ((↑) '' A) := by
      rw [← image_comp]
      exact image_congr fun x _ => (ccurveExt_coe γ x).symm
    rw [himg, volume_unitInterval_apply]
    exact hmono.2 _ (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  refine ⟨hA, fun E => ?_⟩
  have hE : E ∩ range γ = γ '' (γ ⁻¹' E) := (image_preimage_eq_inter_range).symm
  rw [hE]
  refine ⟨(hA _).2, ?_⟩
  have h1 := (hA (γ ⁻¹' E)).1
  calc volume (γ ⁻¹' E)
      = ENNReal.ofReal (Real.cos α)⁻¹ * (ENNReal.ofReal (Real.cos α) * volume (γ ⁻¹' E)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne']
        simp
    _ ≤ _ := by gcongr

end AFree
