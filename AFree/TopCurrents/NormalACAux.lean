module

public import AFree.Paper.AugmentedMeasure
public import AFree.Paper.Currents.Free

/-!
# Single-coordinate vector measures (helper for absolute continuity of normal currents)

`coordSingle μ i j` is the vector measure with the single nonzero coordinate `j`, equal to the
coordinate `μᵢ` of `μ`. We record its Euclidean norms, variation and integrals.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {X : Type*} [MeasurableSpace X]

/-- The vector measure with the single coordinate `j`, equal to `μᵢ`. -/
noncomputable def coordSingle (μ : VectorMeasure X (ι → ℝ)) (i : ι) (j : κ) :
    VectorMeasure X (κ → ℝ) :=
  (coordMeasure μ i).mapRange (AddMonoidHom.single (fun _ : κ => ℝ) j) (continuous_pi fun k => by
      by_cases h : k = j
      · subst h; simpa using continuous_id'
      · simpa [Pi.single_eq_of_ne h] using continuous_const)

omit [Fintype ι] [Fintype κ] in
lemma coordSingle_apply (μ : VectorMeasure X (ι → ℝ)) (i : ι) (j : κ) (E : Set X) :
    coordSingle μ i j E = Pi.single j (μ E i) := by
  simp [coordSingle, VectorMeasure.mapRange_apply, coordMeasure_apply]

lemma piEuclideanNorm_single (j : κ) (a : ℝ) : piEuclideanNorm (Pi.single j a : κ → ℝ) = |a| := by
  unfold piEuclideanNorm
  have : ∑ k, (Pi.single j a : κ → ℝ) k * (Pi.single j a : κ → ℝ) k = a * a := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [Pi.single_eq_of_ne hk]
    · simp
  rw [this, Real.sqrt_mul_self_eq_abs]

omit [Fintype ι] in
lemma coordSingle_norm (μ : VectorMeasure X (ι → ℝ)) (i : ι) (j : κ) (E : Set X) :
    piEuclideanNorm (coordSingle μ i j E) = |μ E i| := by
  rw [coordSingle_apply, piEuclideanNorm_single]

omit [Fintype ι] [Fintype κ] in
lemma coordMeasure_coordSingle_self (μ : VectorMeasure X (ι → ℝ)) (i : ι) (j : κ) :
    coordMeasure (coordSingle μ i j) j = coordMeasure μ i := by
  ext E hE
  simp [coordMeasure_apply, coordSingle_apply]

omit [Fintype ι] [Fintype κ] in
lemma coordMeasure_coordSingle_ne (μ : VectorMeasure X (ι → ℝ)) (i : ι) {j j' : κ} (h : j' ≠ j) :
    coordMeasure (coordSingle μ i j) j' = 0 := by
  ext E hE
  simp [coordMeasure_apply, coordSingle_apply, Pi.single_eq_of_ne h]

/-- Two vector measures with the same Euclidean norms on all sets have the same variation. -/
lemma euclideanVariation_eq_of_norm_eq {ι' : Type*} [Fintype ι'] (μ : VectorMeasure X (ι → ℝ))
    (ν : VectorMeasure X (ι' → ℝ)) (h : ∀ E, piEuclideanNorm (μ E) = piEuclideanNorm (ν E)) :
    euclideanVariation μ = euclideanVariation ν :=
  le_antisymm
    (euclideanVariation_le_of_forall μ fun E _ => (h E) ▸ ofReal_piEuclideanNorm_le_euclideanVariation ν E)
    (euclideanVariation_le_of_forall ν fun E _ => (h E).symm ▸ ofReal_piEuclideanNorm_le_euclideanVariation μ E)

lemma euclideanVariation_coordSingle_le (μ : VectorMeasure X (ι → ℝ)) (i : ι) (j : κ) :
    euclideanVariation (coordSingle μ i j) ≤ euclideanVariation μ :=
  euclideanVariation_le_of_forall _ fun E _ => by
    rw [coordSingle_norm]
    exact (ENNReal.ofReal_le_ofReal (abs_apply_le_piEuclideanNorm (μ E) i)).trans
      (ofReal_piEuclideanNorm_le_euclideanVariation μ E)

/-- `(∫ g dμ)ᵢ = (∫ g d coordSingle μ i j)ⱼ`. -/
lemma integral_coordSingle_self (μ : VectorMeasure X (ι → ℝ)) (i : ι) (j : κ) {g : X → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    (∫ᵛ x, g x ∂•(coordSingle μ i j)) j = (∫ᵛ x, g x ∂•μ) i :=
  (integral_apply_eq_of_coordMeasure_eq (coordSingle μ i j) μ j i hg hC
    (coordMeasure_coordSingle_self μ i j).symm (euclideanVariation_coordSingle_le μ i j)).symm

omit [Fintype ι] in
/-- The other coordinates of `∫ g d coordSingle μ i j` vanish. -/
lemma integral_coordSingle_ne (μ : VectorMeasure X (ι → ℝ)) (i : ι) {j j' : κ} (h : j' ≠ j)
    {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    (∫ᵛ x, g x ∂•(coordSingle μ i j)) j' = 0 := by
  have := integral_apply_eq_of_coordMeasure_eq (0 : VectorMeasure X (Unit → ℝ))
    (coordSingle μ i j) () j' hg hC (by rw [coordMeasure_coordSingle_ne μ i h]; ext E hE; simp [coordMeasure_apply])
    (euclideanVariation_le_of_forall _ fun E _ => by simp [piEuclideanNorm])
  simpa using this

end AFree
