module

public import AFree.Curves

/-!
# Coordinate lines

Splitting `ℝ^(n+1) ≃ ℝ × ℝ^n` along coordinate `i`, the fibres are the lines `r ↦ x₀ + r e_i`, and
`𝓗¹` of a fibre piece is the Lebesgue measure of the parameter set (`hausdorffOne_line`).
-/

@[expose] public section

open MeasureTheory PDE
open scoped ENNReal

namespace AFree.Bundle.AC

variable {n : ℕ}

/-- The splitting of coordinate `i` off `ℝ^(n+1)`. -/
noncomputable def split (i : Fin (n + 1)) : Vec (n + 1) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i

theorem volume_preserving_split (i : Fin (n + 1)) :
    MeasurePreserving (split i) volume volume :=
  volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i

/-- The line over `y` in the direction `e_i`. -/
noncomputable def line (i : Fin (n + 1)) (y : Fin n → ℝ) (r : ℝ) : Vec (n + 1) :=
  (split i).symm (r, y)

theorem line_apply_same (i : Fin (n + 1)) (y : Fin n → ℝ) (r : ℝ) : line i y r i = r := by
  simp [line, split]

theorem split_line (i : Fin (n + 1)) (y : Fin n → ℝ) (r : ℝ) : split i (line i y r) = (r, y) :=
  (split i).apply_symm_apply _

theorem split_fst (i : Fin (n + 1)) (x : Vec (n + 1)) : (split i x).1 = x i := by
  simp [split]

theorem line_split (i : Fin (n + 1)) (x : Vec (n + 1)) :
    line i (split i x).2 (split i x).1 = x := by
  simp [line]

theorem line_eq (i : Fin (n + 1)) (y : Fin n → ℝ) (r : ℝ) :
    line i y r = line i y 0 + r • basisVec i := by
  ext j
  refine Fin.succAboveCases i ?_ ?_ j
  · simp [line_apply_same]
  · intro k
    simp [line, split, basisVec_apply, Fin.succAbove_ne]

theorem vecEuclideanNorm_basisVec' (i : Fin (n + 1)) : vecEuclideanNorm (basisVec i) = 1 := by
  rw [vecEuclideanNorm, vecNormSq_basisVec, Real.sqrt_one]

theorem line_injective (i : Fin (n + 1)) (y : Fin n → ℝ) : Function.Injective (line i y) := by
  intro r r' h
  have := congrArg (fun x => x i) h
  simpa [line_apply_same] using this

theorem lipschitz_line (i : Fin (n + 1)) (y : Fin n → ℝ) : LipschitzWith 1 (line i y) := by
  refine LipschitzWith.of_dist_le_mul fun r r' => ?_
  rw [line_eq i y r, line_eq i y r', dist_eq_norm]
  have : line i y 0 + r • basisVec i - (line i y 0 + r' • basisVec i) = (r - r') • basisVec i := by
    rw [sub_smul]; abel
  rw [this]
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_
  by_cases h : j = i <;> simp [basisVec_apply, h]

theorem deriv_line (i : Fin (n + 1)) (y : Fin n → ℝ) (s : ℝ) :
    deriv (line i y) s = basisVec i := by
  have : line i y = fun s : ℝ => line i y 0 + s • basisVec i := funext (line_eq i y)
  rw [this]
  simpa using (((hasDerivAt_id s).smul_const (basisVec i)).const_add (line i y 0)).deriv

theorem contDiff_line (i : Fin (n + 1)) (y : Fin n → ℝ) : ContDiff ℝ 1 (line i y) := by
  have : line i y = fun s : ℝ => line i y 0 + s • basisVec i := funext (line_eq i y)
  rw [this]; fun_prop

/-- Fibre pieces. -/
theorem fiber_eq (i : Fin (n + 1)) (T : Set (Vec (n + 1))) (y : Fin n → ℝ) :
    T ∩ {x | (split i x).2 = y} = line i y '' {r | line i y r ∈ T} := by
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨(split i x).1, ?_, ?_⟩
    · have : line i y (split i x).1 = x := by
        rw [line, ← hy]; exact (split i).symm_apply_apply x
      simpa [this] using hx
    · rw [line, ← hy]; exact (split i).symm_apply_apply x
  · rintro ⟨r, hr, rfl⟩
    exact ⟨hr, by simp [split_line]⟩

/-- `𝓗¹` of a fibre piece is the Lebesgue measure of the parameter set. -/
theorem hausdorffOne_fiber (i : Fin (n + 1)) (T : Set (Vec (n + 1))) (y : Fin n → ℝ) :
    euclideanHausdorffOne (n + 1) (T ∩ {x | (split i x).2 = y}) =
      volume {r | line i y r ∈ T} := by
  rw [fiber_eq]
  have : line i y = fun s : ℝ => line i y 0 + s • basisVec i := funext (line_eq i y)
  rw [this]
  exact hausdorffOne_line _ _ (vecEuclideanNorm_basisVec' i) _

end AFree.Bundle.AC
