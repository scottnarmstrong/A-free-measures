module

public import AFree.Paper.OrderK.BlowUpSetting
public import AFree.Paper.OrderK.AlgebraScale

/-!
# The order-`k` blow-up equation

The properties of the first-order blow-up (support, normalization and smallness, as in `AFree.Paper.BlowUp`)
hold unchanged, and the rescaled equation holds with the scaling weights `r^{k-h}`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix PDE
open scoped ENNReal

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem blowMap_eq_affMap (x₀ : Vec d) (r : ℝ) :
    blowMap x₀ r = affMap r⁻¹ (-(r⁻¹ • x₀)) := by
  funext y
  simp [blowMap, affMap, sub_eq_add_neg]

theorem isOpen_blowMap_image {Ω : Set (Vec d)} (hΩ : IsOpen Ω) (x₀ : Vec d) {r : ℝ} (hr : r ≠ 0) :
    IsOpen (blowMap x₀ r '' Ω) :=
  (blowHomeo x₀ hr).isOpenMap Ω hΩ

theorem integral_blowMeasure_eq (x₀ : Vec d) {r : ℝ} (hr : r ≠ 0) (c : ℝ≥0∞)
    (σ : Measure (Vec d)) (G : Vec d → ℝ) :
    ∫ z, G z ∂blowMeasure x₀ r c σ = c.toReal * ∫ y, G (blowMap x₀ r y) ∂σ := by
  have hemb := measurableEmbedding_blowMap x₀ hr
  unfold blowMeasure
  rw [integral_smul_measure, hemb.integral_map, smul_eq_mul]

omit [Fintype κ] in
/-- The rescaled equation: for every test function `ψ` in `T_j(Ω)` and
`e ∈ κ`, `Σ_h (-1)^h r^{k-h} Σ_{|α|=h} ∫ [∂^α(ψ Ã_α)] P_r dσ_r = 0`, `Ã_α(z) = A_α(x₀ + r z)`. -/
theorem lem_blowupk_B5k {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {k : ℕ}
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω)
    {σ : Measure (Vec d)} {P : Vec d → ι → ℝ} (h : IsFreePairVar Ω k A σ P) (x₀ : Vec d)
    {r : ℝ} (hr : 0 < r) (c : ℝ≥0∞) {ψ : Vec d → ℝ}
    (hψ : IsTestFunctionOn (blowMap x₀ r '' Ω) ψ) (e : κ) :
    ∑ h' ∈ Finset.range (k + 1), (-1 : ℝ) ^ h' * r ^ (k - h') *
      ∑ α ∈ Finset.Nat.antidiagonalTuple d h', ∫ z, ∑ i : ι,
        multiCoordDeriv α (fun w => ψ w * A α (x₀ + r • w) e i) z * blowDensity x₀ r P z i
          ∂blowMeasure x₀ r c σ = 0 := by
  set T := blowMap x₀ r with hT
  have hTΩ : IsOpen (T '' Ω) := isOpen_blowMap_image hΩ x₀ hr.ne'
  have hφ : IsTestFunctionOn Ω (ψ ∘ T) := isTestFunctionOn_comp_blowMap x₀ hr.ne' hψ
  have key := h.2 (ψ ∘ T) hφ e
  -- smoothness of the rescaled products
  have hB : ∀ α i, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => A α (x₀ + r • w) e i) (T '' Ω) := by
    intro α i
    refine (hA α e i).comp (contDiffOn_const.add (contDiffOn_id.const_smul r)) ?_
    rintro w ⟨y, hy, rfl⟩
    have : x₀ + r • T y = y := by
      simp [hT, blowMap, smul_smul, mul_inv_cancel₀ hr.ne']
    simpa [this] using hy
  have hg : ∀ α i, ContDiff ℝ (⊤ : ℕ∞) (fun w => ψ w * A α (x₀ + r • w) e i) := fun α i =>
    (lem_smoothext hTΩ hψ (hB α i)).1
  have hcomp : ∀ α i, (fun z => (ψ ∘ T) z * A α z e i) =
      fun z => (fun w => ψ w * A α (x₀ + r • w) e i) (affMap r⁻¹ (-(r⁻¹ • x₀)) z) := by
    intro α i
    funext z
    have : x₀ + r • T z = z := by simp [hT, blowMap, smul_smul, mul_inv_cancel₀ hr.ne']
    simp only [Function.comp_apply, ← blowMap_eq_affMap, ← hT, this]
  have hder : ∀ α i, multiCoordDeriv α (fun z => (ψ ∘ T) z * A α z e i) =
      fun z => (r⁻¹) ^ multiAbs α *
        multiCoordDeriv α (fun w => ψ w * A α (x₀ + r • w) e i) (T z) := by
    intro α i
    rw [hcomp α i]
    funext z
    have := multiCoordDeriv_comp_affMap isOpen_univ (smOn_univ_iff.2 (hg α i)) r⁻¹
      (-(r⁻¹ • x₀)) α (Set.mem_univ z)
    rw [this, ← blowMap_eq_affMap]
  have hP : ∀ α, ∫ z, ∑ i : ι, multiCoordDeriv α (fun w => ψ w * A α (x₀ + r • w) e i) z *
        blowDensity x₀ r P z i ∂blowMeasure x₀ r c σ =
      c.toReal * ∫ y, ∑ i : ι, multiCoordDeriv α (fun w => ψ w * A α (x₀ + r • w) e i) (T y) *
        P y i ∂σ := by
    intro α
    rw [integral_blowMeasure_eq x₀ hr.ne' c σ]
    simp only [blowDensity_blowMap x₀ hr.ne', hT]
  have hS : ∀ h' ∈ Finset.range (k + 1), ∀ α ∈ Finset.Nat.antidiagonalTuple d h',
      ∫ y, ∑ i : ι, multiCoordDeriv α (fun z => (ψ ∘ T) z * A α z e i) y * P y i ∂σ =
        (r⁻¹) ^ h' * ∫ y, ∑ i : ι,
          multiCoordDeriv α (fun w => ψ w * A α (x₀ + r • w) e i) (T y) * P y i ∂σ := by
    intro h' _ α hα
    have hαa : multiAbs α = h' := by
      rw [Finset.Nat.mem_antidiagonalTuple] at hα; exact hα
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hder α, hαa, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hfin : ∀ h' ∈ Finset.range (k + 1), (-1 : ℝ) ^ h' * r ^ (k - h') *
      ∑ α ∈ Finset.Nat.antidiagonalTuple d h', ∫ z, ∑ i : ι,
        multiCoordDeriv α (fun w => ψ w * A α (x₀ + r • w) e i) z * blowDensity x₀ r P z i
          ∂blowMeasure x₀ r c σ =
      r ^ k * c.toReal * ∑ α ∈ Finset.Nat.antidiagonalTuple d h', (-1 : ℝ) ^ h' *
        ∫ y, ∑ i : ι, multiCoordDeriv α (fun z => (ψ ∘ T) z * A α z e i) y * P y i ∂σ := by
    intro h' hh'
    have hle : h' ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hh')
    have hpow : r ^ (k - h') = r ^ k * (r⁻¹) ^ h' := by
      rw [inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hr.ne'), ← pow_add,
        Nat.sub_add_cancel hle]
    have e2 : ∑ α ∈ Finset.Nat.antidiagonalTuple d h', (-1 : ℝ) ^ h' *
        ∫ y, ∑ i : ι, multiCoordDeriv α (fun z => (ψ ∘ T) z * A α z e i) y * P y i ∂σ =
        ∑ α ∈ Finset.Nat.antidiagonalTuple d h', (-1 : ℝ) ^ h' * ((r⁻¹) ^ h' * ∫ y, ∑ i : ι,
          multiCoordDeriv α (fun w => ψ w * A α (x₀ + r • w) e i) (T y) * P y i ∂σ) :=
      Finset.sum_congr rfl fun α hα => by rw [hS h' hh' α hα]
    rw [Finset.sum_congr rfl fun α _ => hP α, e2, hpow]
    simp only [← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl hfin, ← Finset.mul_sum, key, mul_zero]

end

end AFree
