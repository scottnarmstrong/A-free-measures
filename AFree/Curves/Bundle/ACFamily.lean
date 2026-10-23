module

public import AFree.Curves.Bundle.ACLine
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The family of segments for the `L^d` case

With
`Z = {ρ > 0}` for `ρ = dμ/d vol`, the index space `[0,1]`, a Borel sampler `Ψ : [0,1] → ℝ^n` with
`Ψ_# Leb ~ vol`, the family `E_t = {x ∈ Z : |x_i| < m, x̂ = Ψ t}` is a rectifiable family for `μ`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped ENNReal unitInterval

namespace AFree.Bundle.AC

variable {n : ℕ}

/-- `Z ∩ {|x_i| < m}`, `Z = {dμ/d vol > 0}`. -/
def piece (μ : Measure (Vec (n + 1))) (i : Fin (n + 1)) (m : ℕ) : Set (Vec (n + 1)) :=
  {x | 0 < μ.rnDeriv volume x} ∩ {x | |x i| < m}

theorem measurableSet_piece (μ : Measure (Vec (n + 1))) (i : Fin (n + 1)) (m : ℕ) :
    MeasurableSet (piece μ i m) :=
  (measurableSet_lt measurable_const (Measure.measurable_rnDeriv _ _)).inter
    (measurableSet_lt (by fun_prop) measurable_const)

theorem measurableSet_fiber (i : Fin (n + 1)) (y : Fin n → ℝ) :
    MeasurableSet {x | (split i x).2 = y} :=
  (measurable_snd.comp (split i).measurable) (measurableSet_singleton y)

/-- The family `E_t`. -/
def fam (μ : Measure (Vec (n + 1))) (i : Fin (n + 1)) (m : ℕ) (Ψ : I → Fin n → ℝ) (t : I) :
    Set (Vec (n + 1)) :=
  piece μ i m ∩ {x | (split i x).2 = Ψ t}

/-- The slice function `h_A(y) = Leb {r : line(y, r) ∈ A ∩ piece}`. -/
noncomputable def slice (μ : Measure (Vec (n + 1))) (i : Fin (n + 1)) (m : ℕ)
    (A : Set (Vec (n + 1))) (y : Fin n → ℝ) : ℝ≥0∞ :=
  volume {r | line i y r ∈ A ∩ piece μ i m}

theorem hausdorffOne_fam_inter (μ : Measure (Vec (n + 1))) (i : Fin (n + 1)) (m : ℕ)
    (Ψ : I → Fin n → ℝ) (A : Set (Vec (n + 1))) (t : I) :
    euclideanHausdorffOne (n + 1) (fam μ i m Ψ t ∩ A) = slice μ i m A (Ψ t) := by
  have : fam μ i m Ψ t ∩ A = (A ∩ piece μ i m) ∩ {x | (split i x).2 = Ψ t} := by
    ext x; simp only [fam, Set.mem_inter_iff]; tauto
  rw [this, hausdorffOne_fiber]; rfl

theorem measurable_slice (μ : Measure (Vec (n + 1))) (i : Fin (n + 1)) (m : ℕ)
    {A : Set (Vec (n + 1))} (hA : MeasurableSet A) : Measurable (slice μ i m A) := by
  have hS : MeasurableSet ((split i).symm ⁻¹' (A ∩ piece μ i m)) :=
    (split i).symm.measurable (hA.inter (measurableSet_piece μ i m))
  exact measurable_measure_prodMk_right (μ := (volume : Measure ℝ)) hS

theorem lintegral_slice (μ : Measure (Vec (n + 1))) (i : Fin (n + 1)) (m : ℕ)
    {A : Set (Vec (n + 1))} (hA : MeasurableSet A) :
    ∫⁻ y, slice μ i m A y = volume (A ∩ piece μ i m) := by
  have hS : MeasurableSet ((split i).symm ⁻¹' (A ∩ piece μ i m)) :=
    (split i).symm.measurable (hA.inter (measurableSet_piece μ i m))
  have h1 := Measure.prod_apply_symm (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin n → ℝ))) hS
  have h2 : volume ((split i).symm ⁻¹' (A ∩ piece μ i m)) = volume (A ∩ piece μ i m) :=
    (volume_preserving_split i).symm.measure_preimage_equiv _
  rw [← h2, Measure.volume_eq_prod, h1]
  rfl

variable {Ψ : I → Fin n → ℝ}

theorem lintegral_family (μ : Measure (Vec (n + 1))) (i : Fin (n + 1)) (m : ℕ)
    (hΨ : Measurable Ψ) {A : Set (Vec (n + 1))} (hA : MeasurableSet A) :
    ∫⁻ t, euclideanHausdorffOne (n + 1) (fam μ i m Ψ t ∩ A) =
      ∫⁻ y, slice μ i m A y ∂(volume.map Ψ) := by
  simp_rw [hausdorffOne_fam_inter]
  exact (lintegral_map (measurable_slice μ i m hA) hΨ).symm

/-- `∫ 𝓗¹(E_t ∩ A) dt = 0` iff `vol (A ∩ piece) = 0`, for a sampler with `Ψ_# Leb ~ vol`. -/
theorem lintegral_family_eq_zero_iff (μ : Measure (Vec (n + 1))) (i : Fin (n + 1)) (m : ℕ)
    (hΨ : Measurable Ψ) (h₁ : volume.map Ψ ≪ volume) (h₂ : (volume : Measure (Fin n → ℝ)) ≪ volume.map Ψ)
    {A : Set (Vec (n + 1))} (hA : MeasurableSet A) :
    ∫⁻ t, euclideanHausdorffOne (n + 1) (fam μ i m Ψ t ∩ A) = 0 ↔
      volume (A ∩ piece μ i m) = 0 := by
  rw [lintegral_family μ i m hΨ hA, ← lintegral_slice μ i m hA,
    lintegral_eq_zero_iff (measurable_slice μ i m hA),
    lintegral_eq_zero_iff (measurable_slice μ i m hA)]
  exact ⟨fun h => h₂.ae_le h, fun h => h₁.ae_le h⟩

theorem piece_null_of_null (μ : Measure (Vec (n + 1))) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (i : Fin (n + 1)) (m : ℕ) {A : Set (Vec (n + 1))} (hA : MeasurableSet A) (h : μ A = 0) :
    volume (A ∩ piece μ i m) = 0 := by
  have h1 : ∫⁻ x in A, μ.rnDeriv volume x = 0 := by
    rw [Measure.setLIntegral_rnDeriv' hμ hA, h]
  rw [setLIntegral_eq_zero_iff hA (Measure.measurable_rnDeriv _ _)] at h1
  refine measure_mono_null (fun x hx => ?_) h1
  intro hx2
  have := hx2 hx.1
  have := hx.2.1
  simp_all

theorem family_isRectifiable (μ : Measure (Vec (n + 1))) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (i : Fin (n + 1)) (m : ℕ) (hΨ : Measurable Ψ) (h₁ : volume.map Ψ ≪ volume)
    (h₂ : (volume : Measure (Fin n → ℝ)) ≪ volume.map Ψ) :
    IsRectifiableFamily μ (fam μ i m Ψ) := by
  have hbound : ∀ t, euclideanHausdorffOne (n + 1) (fam μ i m Ψ t) ≤ ENNReal.ofReal (2 * m) := by
    intro t
    have := hausdorffOne_fam_inter μ i m Ψ Set.univ t
    rw [Set.inter_univ] at this
    rw [this, slice]
    calc volume {r | line i (Ψ t) r ∈ Set.univ ∩ piece μ i m}
        ≤ volume (Set.Ioo (-(m : ℝ)) m) := by
          refine measure_mono fun r hr => ?_
          have : |line i (Ψ t) r i| < m := hr.2.2
          rw [line_apply_same] at this
          exact abs_lt.1 this
      _ = ENNReal.ofReal (2 * m) := by
          rw [Real.volume_Ioo]; congr 1; ring
  refine ⟨fun t => ⟨(measurableSet_piece μ i m).inter (measurableSet_fiber i _), ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨(hbound t).trans_lt ENNReal.ofReal_lt_top, fun _ => line i (Ψ t),
      fun _ => ⟨1, lipschitz_line i _⟩, ?_⟩
    have : fam μ i m Ψ t ⊆ ⋃ _ : ℕ, Set.range (line i (Ψ t)) := by
      intro x hx
      have h := fiber_eq i (piece μ i m) (Ψ t)
      have hx' : x ∈ line i (Ψ t) '' {r | line i (Ψ t) r ∈ piece μ i m} := h ▸ hx
      obtain ⟨r, _, rfl⟩ := hx'
      exact Set.mem_iUnion.2 ⟨0, r, rfl⟩
    rw [Set.sdiff_eq_empty.2 this]; exact measure_empty
  · intro A hA
    have : (fun t => euclideanHausdorffOne (n + 1) (fam μ i m Ψ t ∩ A)) =
        slice μ i m A ∘ Ψ := funext (hausdorffOne_fam_inter μ i m Ψ A)
    rw [this]; exact (measurable_slice μ i m hA).comp hΨ
  · calc ∫⁻ t, euclideanHausdorffOne (n + 1) (fam μ i m Ψ t)
        ≤ ∫⁻ _ : I, ENNReal.ofReal (2 * m) := lintegral_mono hbound
      _ < ⊤ := by
        rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_lt_top
  · intro A hA hμA
    exact (lintegral_family_eq_zero_iff μ i m hΨ h₁ h₂ hA).2 (piece_null_of_null μ hμ i m hA hμA)

end AFree.Bundle.AC
