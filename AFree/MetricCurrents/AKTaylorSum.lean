module

public import AFree.MetricCurrents.AKTaylorMulti
public import AFree.MetricCurrents.AKTaylorReduction
public import AFree.MetricCurrents.AKTaylorScale

/-!
# Taylor lemma, Step 4: summation over the grid
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.AKTaylor

open PDE AFree

variable {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ} {π : Fin k → Vec d → ℝ}
  {ψ : Fin k → Vec k → ℝ} {Λ M : ℝ≥0} {μ : Measure (Vec d)}

/-- The grid vertex `y_J = r J`. -/
def yJ (r : ℝ) (J : Fin k → ℤ) : Vec k := fun l => r * (J l : ℝ)

/-- The piece `f_J = f_R · χ_J ∘ π`. -/
noncomputable def wJ (π : Fin k → Vec d → ℝ) (R : ℝ) (f : Vec d → ℝ) (r : ℝ) (J : Fin k → ℤ)
    (x : Vec d) : ℝ :=
  cutoffWeight π R f x * gridChi r J (evalTuple π x)

/-- The piecewise-constant Jacobian `ξ = ∑_{J ∈ F} det(Dψ(y_J)) χ_J`. -/
noncomputable def xiFun (ψ : Fin k → Vec k → ℝ) (r : ℝ) (F : Finset (Fin k → ℤ)) (y : Vec k) : ℝ :=
  ∑ J ∈ F, (jacMat ψ (yJ r J)).det * gridChi r J y

/-- The output of Step 1, bundled. -/
structure ScaleData (ψ : Fin k → Vec k → ℝ) (R : ℝ) (δ : ℝ≥0) (r : ℝ) (F : Finset (Fin k → ℤ)) :
    Prop where
  r_pos : 0 < r
  r_le : r ≤ 1
  mod : ∀ y y' : Vec k, ‖y‖ ≤ R + 4 → ‖y'‖ ≤ R + 4 → ‖y - y'‖ ≤ 2 * r → ∀ i,
    ‖fderiv ℝ (ψ i) y - fderiv ℝ (ψ i) y'‖ ≤ δ
  mem : ∀ J, J ∈ F ↔ ∃ y : Vec k, ‖y‖ ≤ R + 1 ∧ gridChi r J y ≠ 0

lemma exists_scaleData {ψ : Fin k → Vec k → ℝ} (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (R : ℝ) {δ : ℝ≥0}
    (hδ : 0 < δ) : ∃ (r : ℝ) (F : Finset (Fin k → ℤ)), ScaleData ψ R δ r F := by
  obtain ⟨r, hr, hr1, hmod, F, hF⟩ := scale_and_grid hψ R (δ := δ) (by exact_mod_cast hδ)
  exact ⟨r, F, ⟨hr, hr1, hmod, hF⟩⟩

lemma ScaleData.norm_yJ_le {R : ℝ} {δ : ℝ≥0} {r : ℝ} {F : Finset (Fin k → ℤ)}
    (sd : ScaleData ψ R δ r F) {J : Fin k → ℤ} (hJ : J ∈ F) : ‖yJ r J‖ ≤ R + 2 := by
  obtain ⟨y, hy, hχ⟩ := (sd.mem J).1 hJ
  have h := (grid_partition_of_unity sd.r_pos).2.2.2.1 J y hχ
  have h1 : ‖yJ r J - y‖ ≤ r := by
    refine (pi_norm_le_iff_of_nonneg sd.r_pos.le).2 fun l => ?_
    have h' := (h l).le
    rw [abs_sub_comm] at h'
    simpa [yJ, Real.norm_eq_abs] using h'
  have h2 : ‖yJ r J‖ ≤ ‖y‖ + ‖yJ r J - y‖ := norm_le_norm_add_norm_sub' (yJ r J) y
  linarith [sd.r_le]

lemma lipb_gridChi_comp (cx : Ctx T π ψ Λ M μ) {r : ℝ} (hr : 0 < r) (J : Fin k → ℤ) :
    IsBddLipFun (fun x => gridChi r J (evalTuple π x)) := by
  have G := grid_partition_of_unity (m := k) hr
  refine ⟨⟨(r⁻¹ * k * Λ).toNNReal, fun x x' => ?_⟩, 1, fun x => ?_⟩
  · have h1 := gridChi_abs_sub_le hr J (evalTuple π x) (evalTuple π x')
    have h2 : ∑ l, |evalTuple π x l - evalTuple π x' l| ≤ k * (Λ * vecEuclideanNorm (x - x')) := by
      calc ∑ l, |evalTuple π x l - evalTuple π x' l| ≤ ∑ _l : Fin k, Λ * vecEuclideanNorm (x - x') :=
            Finset.sum_le_sum fun l _ => by simpa [evalTuple] using cx.hπ l x x'
        _ = _ := by simp
    rw [Real.coe_toNNReal _ (by positivity)]
    calc _ ≤ _ := h1
      _ ≤ r⁻¹ * (k * (Λ * vecEuclideanNorm (x - x'))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  · rw [abs_of_nonneg (G.2.1 J _).1]; exact (G.2.1 J _).2

lemma lipb_wJ (cx : Ctx T π ψ Λ M μ) {r : ℝ} (hr : 0 < r) (R : ℝ) {f : Vec d → ℝ}
    (hf : IsBddLipFun f) (J : Fin k → ℤ) : IsBddLipFun (wJ π R f r J) :=
  lipb_mul (lipb_cutoffWeight cx R hf) (lipb_gridChi_comp cx hr J)

section cube

variable {R : ℝ} {δ : ℝ≥0} {r : ℝ} {F : Finset (Fin k → ℤ)}

/-- Steps 2 and 3 on the cube `J ∈ F`. -/
lemma per_cube (cx : Ctx T π ψ Λ M μ) (sd : ScaleData ψ R δ r F) (hδ1 : δ ≤ 1)
    (D : Set (Matrix (Fin k) (Fin k) ℝ)) (hD : ∀ y, jacMat ψ y ∈ D)
    (hlin : ∀ f, IsBddLipFun f → ∀ A ∈ D, T f (matAct A π) = A.det * T f π)
    {f : Vec d → ℝ} (hf : IsBddLipFun f) {J : Fin k → ℤ} (hJ : J ∈ F) :
    |T (wJ π R f r J) (psiPi ψ π) - (jacMat ψ (yJ r J)).det * T (wJ π R f r J) π| ≤
      cubeConst k Λ M * δ * ∫ x, |wJ π R f r J x| ∂μ := by
  have hw : (0 : ℝ) ≤ 2 * r := by linarith [sd.r_pos]
  have hc := sd.norm_yJ_le hJ
  have hwJ := lipb_wJ cx sd.r_pos R hf J
  have hδ : ∀ z, ‖z - yJ r J‖ ≤ 2 * r → ∀ i,
      ‖fderiv ℝ (ψ i) z - fderiv ℝ (ψ i) (yJ r J)‖ ≤ δ := by
    intro z hz i
    refine sd.mod z (yJ r J) ?_ (by linarith) hz i
    have h2 : ‖z‖ ≤ ‖yJ r J‖ + ‖z - yJ r J‖ := norm_le_norm_add_norm_sub' z (yJ r J)
    linarith [sd.r_le]
  have hsupp : ∀ x, wJ π R f r J x ≠ 0 → ‖evalTuple π x - yJ r J‖ < 2 * r := by
    intro x hx
    have hχ : gridChi r J (evalTuple π x) ≠ 0 := right_ne_zero_of_mul hx
    have h := (grid_partition_of_unity sd.r_pos).2.2.2.1 J _ hχ
    have : ‖evalTuple π x - yJ r J‖ < r := by
      refine (pi_norm_lt_iff sd.r_pos).2 fun l => ?_
      simpa [yJ, evalTuple, Real.norm_eq_abs] using h l
    linarith [sd.r_pos]
  obtain ⟨-, hfr⟩ := freezing cx hw hδ hwJ hsupp
  rw [hfr]
  exact multilinear_expansion cx hδ1 hw hδ hwJ (hlin _ hwJ _ (hD _))

end cube

end AFree.MetricCurrents.AKTaylor
