module

public import AFree.Paper.BD.Symmetric
public import AFree.Paper.BD.EuFree
public import AFree.Paper.BD.Kernel
public import AFree.Paper.BD.Trace

/-!
# Theorems 1.7 and 1.8 from Theorem 1.1 for the Saint-Venant operator

Proofs of [DPR, Theorem 1.7] and [DPR, Corollary 1.8]. Theorem 1.1 of order `2` enters only through the
hypothesis `hmain`; `isFree_saintVenant_of_isBDGradientOn` shows that `Eu` is free for the
Saint-Venant operator, so `hmain` applies to `Eu`.
-/

public section

open MeasureTheory PDE

namespace AFree

variable {d : ℕ}

/-- Conditionally on the instance `hmain` of Theorem 1.1
(`k = 2`, Saint-Venant operator), `polar(Eˢu)` is `|Eˢu|`-a.e. in the wave cone, symmetric and
nonzero. -/
theorem polar_lebesgueSingularPart_mem_symm_ne_zero_of_main {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {u : Vec d → Vec d} {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)}
    (hEu : IsBDGradientOn Ω u Eu)
    (hmain : ∀ᵐ x ∂(euclideanVariation Eu).singularPart volume,
      polar Eu x ∈ waveCone 2 saintVenant) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Eu),
      polar (lebesgueSingularPart Eu) x ∈ waveCone 2 saintVenant ∧
        (∀ p q : Fin d, polar (lebesgueSingularPart Eu) x (p, q) =
          polar (lebesgueSingularPart Eu) x (q, p)) ∧
        polar (lebesgueSingularPart Eu) x ≠ 0 := by
  rw [← euclideanVariation_lebesgueSingularPart] at hmain
  filter_upwards [hmain, polar_lebesgueSingularPart_ae Eu,
    piEuclideanNorm_polar_eq_one (lebesgueSingularPart Eu)] with x h1 h2 h3
  refine ⟨h2 ▸ h1, fun p q => ?_, ?_⟩
  · rw [h2]; exact (isBDGradientOn_symm hΩ hEu).2 x p q
  · intro h0
    rw [h0] at h3
    simp [piEuclideanNorm] at h3

/-- [DPR, Theorem 1.7], conditional on the instance `hmain` of Theorem 1.1 for the
Saint-Venant operator (`k = 2`) applied to `Eu`: the polar of `Eˢu` is `a ⊙ b` with `a, b ≠ 0`. -/
theorem polar_lebesgueSingularPart_eq_symmTensor_of_main {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {u : Vec d → Vec d} {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)}
    (hEu : IsBDGradientOn Ω u Eu)
    (hmain : ∀ᵐ x ∂(euclideanVariation Eu).singularPart volume,
      polar Eu x ∈ waveCone 2 saintVenant) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Eu),
      ∃ a : Vec d, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Eu) x = fun p => (a p.1 * b p.2 + b p.1 * a p.2) / 2 := by
  filter_upwards [polar_lebesgueSingularPart_mem_symm_ne_zero_of_main hΩ hEu hmain] with x hx
  exact exists_symmTensor_of_mem_waveCone_saintVenant (fun p q => hx.2.1 p q) hx.2.2 hx.1

/-- If `div u ∈ L²(Ω)`, then `Σ_i polar(Eˢu)_{ii} = 0`
`|Eˢu|`-a.e. -/
theorem ae_sum_polar_diag_lebesgueSingularPart_eq_zero {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {u : Vec d → Vec d} {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)}
    (hEu : IsBDGradientOn Ω u Eu) (hdiv : HasL2Divergence Ω u) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Eu),
      ∑ i, polar (lebesgueSingularPart Eu) x (i, i) = 0 := by
  have hint : Integrable (fun x => ∑ i, polar (lebesgueSingularPart Eu) x (i, i))
      (euclideanVariation (lebesgueSingularPart Eu)) :=
    integrable_finsetSum _ fun i _ => integrable_polar_apply _ (i, i)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (g := fun _ => (0 : ℝ))
    (fun s _ _ => hint.integrableOn) (fun s _ _ => (integrable_zero _ _ _).integrableOn)
    fun s hs _ => ?_
  rw [integral_finsetSum _ fun i _ => (integrable_polar_apply _ (i, i)).integrableOn]
  simp only [integral_zero]
  rw [← (trace_singularPart_eq_zero hΩ hEu hdiv).2 s hs]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← coordMeasure_eq_setIntegral _ (i, i) hs]; rfl

/-- [DPR, Corollary 1.8], conditional on the instance `hmain` of Theorem 1.1 for the
Saint-Venant operator (`k = 2`) applied to `Eu`: if `div u ∈ L²(Ω)` then `a · b = 0`. -/
theorem polar_lebesgueSingularPart_eq_symmTensor_orth_of_main {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {u : Vec d → Vec d} {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)}
    (hEu : IsBDGradientOn Ω u Eu)
    (hdiv : ∃ g : Vec d → ℝ, MemLp g 2 (volume.restrict Ω) ∧
      ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
        ∫ x in Ω, ∑ i, u x i * euclideanCoordDeriv i φ x = -∫ x in Ω, g x * φ x)
    (hmain : ∀ᵐ x ∂(euclideanVariation Eu).singularPart volume,
      polar Eu x ∈ waveCone 2 saintVenant) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Eu),
      ∃ a : Vec d, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧ vecDot a b = 0 ∧
        polar (lebesgueSingularPart Eu) x = fun p => (a p.1 * b p.2 + b p.1 * a p.2) / 2 := by
  filter_upwards [polar_lebesgueSingularPart_eq_symmTensor_of_main hΩ hEu hmain,
    ae_sum_polar_diag_lebesgueSingularPart_eq_zero hΩ hEu hdiv] with x ⟨a, ha, b, hb, hx⟩ htr
  refine ⟨a, ha, b, hb, ?_, hx⟩
  rw [hx] at htr
  simp only [vecDot]
  rw [← htr]
  exact Finset.sum_congr rfl fun i _ => by ring

end AFree
