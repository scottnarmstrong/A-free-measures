module

public import AFree.Paper.OrderK.Blow

/-!
# The data of the order-`k` blow-up contradiction

For a radius `r ≤ r̄` and `ε ≤ 1/8` the mollified blow-up supplies the inputs of the cut-off lemma:
the smooth functions `u, V, μ, Y`, the mollified equation and the smallness bounds. The error terms are cut to zero outside the index range where they are defined.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix PDE
open scoped ENNReal

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The error mollification `Y_{α,β}`, set to `0` outside `|α| ≤ k`, `β ≤ α` (where it is not used). -/
def errYk (k : ℕ) (x₀ : Vec d) (r : ℝ) (c : ℝ≥0∞) (ε : ℝ) (σ : Measure (Vec d))
    (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ) (P : Vec d → ι → ℝ) (α β : Fin d → ℕ) :
    Vec d → κ → ℝ :=
  if multiAbs α ≤ k ∧ β ∈ multiLE α then errY x₀ r c ε σ A P α β else fun _ _ => 0

theorem errYk_eq {k : ℕ} {x₀ : Vec d} {r : ℝ} {c : ℝ≥0∞} {ε : ℝ} {σ : Measure (Vec d)}
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ} {P : Vec d → ι → ℝ} {α β : Fin d → ℕ}
    (hα : multiAbs α ≤ k) (hβ : β ∈ multiLE α) :
    errYk k x₀ r c ε σ A P α β = errY x₀ r c ε σ A P α β := by
  simp [errYk, hα, hβ]

theorem multiAbs_of_mem_antidiagonalTuple {h : ℕ} {α : Fin d → ℕ}
    (hα : α ∈ Finset.Nat.antidiagonalTuple d h) : multiAbs α = h :=
  Finset.Nat.mem_antidiagonalTuple.1 hα

theorem blowDelta_nonneg (σ : Measure (Vec d)) (x₀ : Vec d) (P : Vec d → ι → ℝ) (r : ℝ) :
    0 ≤ blowDelta σ x₀ P r :=
  add_nonneg (integral_nonneg fun _ => piEuclideanNorm_nonneg _)
    (integral_nonneg fun _ => piEuclideanNorm_nonneg _)

/-- Everything the cut-off lemma needs from the blow-up at a single scale `j`. -/
theorem blowStepK {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {k : ℕ}
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω)
    {σ : Measure (Vec d)} [IsFiniteMeasure σ] {P : Vec d → ι → ℝ} (hPm : Measurable P)
    (hPi : Integrable P σ) (h : IsFreePairVar Ω k A σ P) {x₀ : Vec d} {P0 : ι → ℝ}
    (hP0 : P0 = P x₀) {c0 rb CA : ℝ} (hs : IsBlowSettingK Ω k A x₀ P0 c0 rb CA) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ rb) (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r))
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    let c := blowConst σ x₀ r
    ContDiff ℝ (⊤ : ℕ∞) (mollU x₀ r c ε σ) ∧ (∀ x, 0 ≤ mollU x₀ r c ε σ x) ∧
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => mollVK x₀ r c ε σ P P0 x i)) ∧
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => mollMuK x₀ r c ε σ P x i)) ∧
    (∀ α β c', ContDiff ℝ (⊤ : ℕ∞) (fun x => errYk k x₀ r c ε σ A P α β x c')) ∧
    (∀ x, mollMuK x₀ r c ε σ P x = mollU x₀ r c ε σ x • P0 + mollVK x₀ r c ε σ P P0 x) ∧
    (∀ x ∈ euclideanBall (0 : Vec d) (7 / 8), ∀ c' : κ,
      ∑ h' ∈ Finset.range (k + 1), r ^ (k - h') * ∑ α ∈ Finset.Nat.antidiagonalTuple d h',
          ∑ i, A α x₀ c' i * multiCoordDeriv α (fun y => mollMuK x₀ r c ε σ P y i) x =
        -(∑ h' ∈ Finset.range (k + 1), r ^ (k - h') *
          ∑ α ∈ Finset.Nat.antidiagonalTuple d h', ∑ β ∈ multiLE α, mollSign α β *
            multiCoordDeriv β (fun y => errYk k x₀ r c ε σ A P α β y c') x)) ∧
    (∫ x in euclideanBall (0 : Vec d) (7 / 8), mollU x₀ r c ε σ x ≤ 1) ∧
    (∫ x in euclideanBall (0 : Vec d) (7 / 8), piEuclideanNorm (mollVK x₀ r c ε σ P P0 x) ≤
      blowDelta σ x₀ P r) ∧
    (∫ x in euclideanBall (0 : Vec d) (7 / 8), piEuclideanNorm (mollMuK x₀ r c ε σ P x) ≤
      piEuclideanNorm P0 + blowDelta σ x₀ P r) ∧
    (∀ α, multiAbs α ≤ k → ∀ β ∈ multiLE α,
      ∫ x in euclideanBall (0 : Vec d) (7 / 8), piEuclideanNorm (errYk k x₀ r c ε σ A P α β x) ≤
        CA * r * (piEuclideanNorm P0 + blowDelta σ x₀ P r)) := by
  intro c
  subst hP0
  have hc : c ≠ ∞ := blowConst_ne_top hpos
  have hsmall := lem_smallk hΩ hA hs hr0 hr1 hPm hPi hpos hε hε8
  have hY : ∀ α β c', ContDiff ℝ (⊤ : ℕ∞) (fun x => errYk k x₀ r c ε σ A P α β x c') := by
    intro α β c'
    by_cases hαβ : multiAbs α ≤ k ∧ β ∈ multiLE α
    · have hf := integrable_errDensity hΩ hA hs hr0 hr1 hPm hPi hc hαβ.1 hαβ.2
      rw [errYk_eq hαβ.1 hαβ.2]
      exact contDiff_pi.1 (contDiff_mollify hε _ hf) c'
    · have : errYk k x₀ r c ε σ A P α β = fun _ _ => 0 := by simp [errYk, hαβ]
      rw [this]
      exact contDiff_const
  refine ⟨contDiff_mollU hc hε, mollU_nonneg hε.le σ, fun i => contDiff_pi.1
    (contDiff_mollVK hr0 hc hPi hε _) i, fun i => contDiff_pi.1 (contDiff_mollMuK hr0 hc hPi hε) i,
    hY, mollMuK_eq x₀ r c ε σ P _, fun x hx c' => ?_, hsmall.1, hsmall.2.1, hsmall.2.2.1,
    fun α hα β hβ => ?_⟩
  · refine Eq.trans (lem_mollvar hΩ hA hPm hPi h hs hr0 hr1 hc hε hε8 hx c') ?_
    congr 1
    refine Finset.sum_congr rfl fun h' hh' => ?_
    have hle : h' ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hh')
    congr 1
    refine Finset.sum_congr rfl fun α hα => ?_
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [errYk_eq (by rw [multiAbs_of_mem_antidiagonalTuple hα]; exact hle) hβ]
  · rw [errYk_eq hα hβ]
    exact hsmall.2.2.2 α β hα hβ

end

end AFree
