module

public import AFree.Harmonic.Symbol.Basic
public import AFree.Analysis.Bump

/-!
# Littlewood–Paley partition on `Vec d`

`lpPsi0 = χ_{1,2}` equals `1` on `|ξ| ≤ 1` and vanishes for `|ξ| > 3/2`. With
`ψ(ξ) = ψ₀(ξ) - ψ₀(2ξ)` supported in `1/2 < |ξ| ≤ 3/2`, the dyadic pieces
`ψ₀, ψ(2^{-1}·), ψ(2^{-2}·), …` sum (telescopically) to `ψ₀(2^{-L} ·)`, which increases to `1`.
-/

@[expose] public section

open PDE

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The low-frequency cutoff `ψ₀`: `1` on `|ξ| ≤ 1`, supported in `|ξ| ≤ 3/2`. -/
def lpPsi0 : Vec d → ℝ := euclideanCutoff 1 2

/-- The annular piece `ψ(ξ) = ψ₀(ξ) - ψ₀(2ξ)`. -/
def lpPsi (ξ : Vec d) : ℝ := lpPsi0 ξ - lpPsi0 ((2 : ℝ) • ξ)

/-- Dyadic piece `0 ↦ ψ₀`, `l + 1 ↦ ψ(2^{-(l+1)} ξ)`. -/
def lpPiece : ℕ → Vec d → ℝ
  | 0 => lpPsi0
  | l + 1 => fun ξ => lpPsi (((2 : ℝ)⁻¹) ^ (l + 1) • ξ)

/-- The truncated partition `ψ₀ + Σ_{1 ≤ l ≤ L} ψ(2^{-l} ξ)`. -/
def lpCut (L : ℕ) (ξ : Vec d) : ℝ := ∑ l ∈ Finset.range (L + 1), lpPiece l ξ

/-- The truncated symbol `m_L = m · (ψ₀ + Σ_{1 ≤ l ≤ L} ψ_l)`. -/
def lpTrunc (m : Vec d → ℂ) (L : ℕ) : Vec d → ℂ := fun ξ => m ξ * (lpCut L ξ : ℂ)

theorem contDiff_lpPsi0 : ContDiff ℝ (⊤ : ℕ∞) (lpPsi0 (d := d)) := contDiff_euclideanCutoff 1 2

theorem lpPsi0_nonneg (ξ : Vec d) : 0 ≤ lpPsi0 ξ := euclideanCutoff_nonneg _ _ ξ

theorem lpPsi0_le_one (ξ : Vec d) : lpPsi0 ξ ≤ 1 := euclideanCutoff_le_one _ _ ξ

theorem lpPsi0_eq_one {ξ : Vec d} (h : vecEuclideanNorm ξ ≤ 1) : lpPsi0 ξ = 1 :=
  euclideanCutoff_eq_one one_pos one_lt_two h

theorem lpPsi0_eq_zero {ξ : Vec d} (h : 3 / 2 < vecEuclideanNorm ξ) : lpPsi0 ξ = 0 := by
  by_contra hne
  have hmem : ξ ∈ tsupport (lpPsi0 (d := d)) := subset_tsupport _ hne
  have := euclideanCutoff_tsupport_subset (d := d) one_pos one_lt_two hmem
  simp only [Set.mem_ofPred_eq] at this
  have h2 := vecEuclideanNorm_sq ξ
  nlinarith [vecEuclideanNorm_nonneg ξ]

theorem contDiff_lpPsi : ContDiff ℝ (⊤ : ℕ∞) (lpPsi (d := d)) := by
  unfold lpPsi
  exact contDiff_lpPsi0.sub (contDiff_lpPsi0.comp (contDiff_const_smul _))

theorem lpPsi_eq_zero_of_le {ξ : Vec d} (h : vecEuclideanNorm ξ ≤ 1 / 2) : lpPsi ξ = 0 := by
  unfold lpPsi
  rw [lpPsi0_eq_one (by linarith), lpPsi0_eq_one, sub_self]
  rw [vecEuclideanNorm_smul]; simp; linarith

theorem lpPsi_eq_zero_of_gt {ξ : Vec d} (h : 3 / 2 < vecEuclideanNorm ξ) : lpPsi ξ = 0 := by
  unfold lpPsi
  rw [lpPsi0_eq_zero h, lpPsi0_eq_zero]
  · simp
  · rw [vecEuclideanNorm_smul]; simp; linarith [vecEuclideanNorm_nonneg ξ]

/-- `ψ` is supported in the annulus `1/2 ≤ |ξ| ≤ 2` (in fact `1/2 < |ξ| ≤ 3/2`). -/
theorem lpPsi_ne_zero {ξ : Vec d} (h : lpPsi ξ ≠ 0) :
    1 / 2 < vecEuclideanNorm ξ ∧ vecEuclideanNorm ξ ≤ 3 / 2 :=
  ⟨not_le.1 fun h' => h (lpPsi_eq_zero_of_le h'), not_lt.1 fun h' => h (lpPsi_eq_zero_of_gt h')⟩

theorem lpPsi_support_subset : tsupport (lpPsi (d := d)) ⊆
    {ξ | 1 / 2 ≤ vecEuclideanNorm ξ ∧ vecEuclideanNorm ξ ≤ 2} := by
  apply closure_minimal
  · intro ξ hξ
    have := lpPsi_ne_zero hξ
    exact ⟨this.1.le, by linarith [this.2]⟩
  · exact (isClosed_le continuous_const PDE.continuous_vecEuclideanNorm).inter
      (isClosed_le PDE.continuous_vecEuclideanNorm continuous_const)

/-- Telescoping: `ψ₀ + Σ_{1 ≤ l ≤ L} ψ(2^{-l} ξ) = ψ₀(2^{-L} ξ)`. -/
theorem lpCut_eq (L : ℕ) (ξ : Vec d) : lpCut L ξ = lpPsi0 (((2 : ℝ)⁻¹) ^ L • ξ) := by
  induction L with
  | zero => simp [lpCut, lpPiece]
  | succ L ih =>
    rw [lpCut, Finset.sum_range_succ, ← lpCut, ih]
    simp only [lpPiece, lpPsi]
    have : (2 : ℝ) • (((2 : ℝ)⁻¹) ^ (L + 1) • ξ) = ((2 : ℝ)⁻¹) ^ L • ξ := by
      rw [smul_smul, pow_succ]; congr 1; field_simp
    rw [this]; ring

theorem contDiff_lpCut (L : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (lpCut (d := d) L) := by
  have : lpCut (d := d) L = fun ξ => lpPsi0 (((2 : ℝ)⁻¹) ^ L • ξ) := funext (lpCut_eq L)
  rw [this]
  exact contDiff_lpPsi0.comp (contDiff_const_smul _)

theorem lpCut_nonneg (L : ℕ) (ξ : Vec d) : 0 ≤ lpCut L ξ := by
  rw [lpCut_eq]; exact lpPsi0_nonneg _

theorem lpCut_le_one (L : ℕ) (ξ : Vec d) : lpCut L ξ ≤ 1 := by
  rw [lpCut_eq]; exact lpPsi0_le_one _

theorem lpCut_eq_one {L : ℕ} {ξ : Vec d} (h : vecEuclideanNorm ξ ≤ 2 ^ L) : lpCut L ξ = 1 := by
  rw [lpCut_eq]
  apply lpPsi0_eq_one
  rw [vecEuclideanNorm_smul, abs_of_nonneg (by positivity), inv_pow]
  have : (0 : ℝ) < 2 ^ L := by positivity
  rw [inv_mul_le_iff₀ this]; linarith

theorem lpCut_one_of_large {ξ : Vec d} :
    ∀ᶠ L in Filter.atTop, lpCut L ξ = 1 := by
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (vecEuclideanNorm ξ) (one_lt_two : (1 : ℝ) < 2)
  filter_upwards [Filter.eventually_ge_atTop L] with M hM
  exact lpCut_eq_one (hL.le.trans (pow_le_pow_right₀ one_le_two hM))

/-- `lpCut L → 1` pointwise. -/
theorem tendsto_lpCut (ξ : Vec d) : Filter.Tendsto (fun L => lpCut L ξ) Filter.atTop (nhds 1) :=
  tendsto_const_nhds.congr' (lpCut_one_of_large.mono fun _ h => h.symm)

theorem lpPiece_succ_ne_zero {l : ℕ} {ξ : Vec d} (h : lpPiece (l + 1) ξ ≠ 0) :
    2 ^ l < vecEuclideanNorm ξ ∧ vecEuclideanNorm ξ ≤ 3 * 2 ^ l := by
  have := lpPsi_ne_zero h
  rw [vecEuclideanNorm_smul, abs_of_nonneg (by positivity), inv_pow] at this
  have hp : (0 : ℝ) < 2 ^ (l + 1) := by positivity
  have h1 := this.1
  have h2 := this.2
  rw [inv_mul_eq_div] at h1 h2
  rw [lt_div_iff₀ hp] at h1
  rw [div_le_iff₀ hp] at h2
  rw [pow_succ] at h1 h2
  constructor <;> nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) l]

end

end AFree
