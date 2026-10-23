module

public import AFree.Harmonic.Kernel.Dyadic
public import AFree.Harmonic.Kernel.SupBound

/-!
# Pointwise bounds for the dyadic kernels

For `m ∈ S^{-s}` (`s ≥ 0`), `l ≥ 1`, `N ∈ ℕ`:
`(1 + 2^l ‖x‖)^N ‖K_l x‖ ≤ C 2^{ld} (2^{-s})^l` and the same for `∇K_l` with `2^{l(d+1)}`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped SchwartzMap ContDiff

namespace AFree

noncomputable section

variable {d : ℕ}

theorem norm_fderiv_smul_comp_smul (G : Vec d → ℂ) (hG : Differentiable ℝ G) (a b : ℝ)
    (x : Vec d) :
    ‖fderiv ℝ (fun y => b • G (a • y)) x‖ ≤ |b| * |a| * ‖fderiv ℝ G (a • x)‖ := by
  let L : Vec d →L[ℝ] Vec d := a • ContinuousLinearMap.id ℝ (Vec d)
  have hL : HasFDerivAt (fun y : Vec d => a • y) L x := (hasFDerivAt_id x).const_smul a
  have h1 := ((hG (a • x)).hasFDerivAt.comp x hL).const_smul b
  have h2 : HasFDerivAt (fun y => b • G (a • y)) (b • (fderiv ℝ G (a • x)).comp L) x := h1
  rw [h2.fderiv]
  have hLn : ‖L‖ ≤ |a| := by
    refine (norm_smul a _).le.trans ?_
    have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Vec d)
    rw [Real.norm_eq_abs]; nlinarith [abs_nonneg a]
  refine (norm_smul_le b ((fderiv ℝ G (a • x)).comp L)).trans ?_
  rw [Real.norm_eq_abs, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖(fderiv ℝ G (a • x)).comp L‖ ≤ ‖fderiv ℝ G (a • x)‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ G (a • x)‖ * |a| := mul_le_mul_of_nonneg_left hLn (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem lpKernel_weighted_le {s : ℝ} (hs : 0 ≤ s) {m : Vec d → ℂ} (hm : IsSymbol (-s) m)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℕ, 1 ≤ l → ∀ x : Vec d,
      (1 + (2 : ℝ) ^ l * ‖x‖) ^ N * ‖lpKernel m l x‖ ≤
        C * ((2 : ℝ) ^ l) ^ d * ((2 : ℝ) ^ (-s)) ^ l ∧
      (1 + (2 : ℝ) ^ l * ‖x‖) ^ N * ‖fderiv ℝ (lpKernel m l) x‖ ≤
        C * ((2 : ℝ) ^ l) ^ (d + 1) * ((2 : ℝ) ^ (-s)) ^ l := by
  obtain ⟨s0, C0, hC0, hC⟩ := exists_vecFourierInv_weighted_le d N
  obtain ⟨S0, hS0, hS⟩ := lpScaledS_sup_le hs hm s0
  refine ⟨C0 * S0, mul_nonneg hC0 hS0, fun l hl x => ?_⟩
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  set l := l' + 1 with hl'
  set H : 𝓢(Vec d, ℂ) := lpScaledS hm.1 l with hH
  set G : Vec d → ℂ := vecFourierInv (⇑H) with hG
  set t : ℝ := (2 : ℝ) ^ l with ht
  have htpos : 0 < t := by positivity
  have hc0 : (((2 : ℝ)⁻¹) ^ l) ≠ 0 := by positivity
  have hsym : lpSym m l = fun ξ => (⇑H) ((((2 : ℝ)⁻¹) ^ l) • ξ) := lpSym_succ_eq l'
  have hcinv : ((((2 : ℝ)⁻¹) ^ l))⁻¹ = t := by rw [inv_pow, inv_inv]
  have hcd : |((((2 : ℝ)⁻¹) ^ l) ^ d)⁻¹| = t ^ d := by
    rw [← inv_pow, hcinv, abs_of_pos (by positivity)]
  have hK : lpKernel m l = fun y => (t ^ d) • G (t • y) := by
    unfold lpKernel
    rw [hsym]
    funext y
    rw [vecFourierInv_comp_smul _ hc0, hcinv, hcd]
  have hGdiff : Differentiable ℝ G := by
    have : G = ⇑(vecFourierInvCLM H) := (vecFourierInv_coe H).symm
    rw [this]; exact (vecFourierInvCLM H).differentiable
  have hbd := hC H (t • x)
  have hsup := hS l
  have hnorm : ‖t • x‖ = t * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg htpos.le]
  rw [hnorm] at hbd
  have hCS : C0 * (s0.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) H ≤
      C0 * S0 * ((2 : ℝ) ^ (-s)) ^ l := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsup hC0
  have htd : (0 : ℝ) ≤ t ^ d := by positivity
  refine ⟨?_, ?_⟩
  · rw [hK]
    simp only [norm_smul, Real.norm_of_nonneg htd]
    calc (1 + t * ‖x‖) ^ N * (t ^ d * ‖G (t • x)‖) =
          t ^ d * ((1 + t * ‖x‖) ^ N * ‖G (t • x)‖) := by ring
      _ ≤ t ^ d * (C0 * S0 * ((2 : ℝ) ^ (-s)) ^ l) :=
          mul_le_mul_of_nonneg_left (hbd.1.trans hCS) htd
      _ = _ := by ring
  · have hf := norm_fderiv_smul_comp_smul G hGdiff t (t ^ d) x
    have hf' : ‖fderiv ℝ (lpKernel m l) x‖ ≤ |t ^ d| * |t| * ‖fderiv ℝ G (t • x)‖ := by
      rw [hK]; simpa [Real.norm_eq_abs] using hf
    rw [abs_of_nonneg htd, abs_of_pos htpos] at hf'
    calc (1 + t * ‖x‖) ^ N * ‖fderiv ℝ (lpKernel m l) x‖
        ≤ (1 + t * ‖x‖) ^ N * (t ^ d * t * ‖fderiv ℝ G (t • x)‖) :=
          mul_le_mul_of_nonneg_left hf' (by positivity)
      _ = t ^ d * t * ((1 + t * ‖x‖) ^ N * ‖fderiv ℝ G (t • x)‖) := by ring
      _ ≤ t ^ d * t * (C0 * S0 * ((2 : ℝ) ^ (-s)) ^ l) :=
          mul_le_mul_of_nonneg_left (hbd.2.trans hCS) (by positivity)
      _ = _ := by ring

end

end AFree
