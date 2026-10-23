module

public import AFree.Curves.Bundle.ACFamily
public import Mathlib.Probability.Kernel.Representation

/-!
# The arc test

For `V ∈ 𝒢_μ`, `μ ≪ vol`, the segments `E_t` are inside the
`C¹` arcs `r ↦ line(Ψ t, r)`, so `e_i ∈ V` holds `μ`-a.e. on `{|x_i| < m}`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped ENNReal unitInterval

namespace AFree.Bundle.AC

/-- Membership `v ∈ V x` is a Borel condition for a Borel subspace field. -/
theorem measurableSet_mem {d : ℕ} {V : Vec d → Submodule ℝ (Vec d)} (hV : IsBorelSubspaceField V)
    (v : Vec d) : MeasurableSet {x | v ∈ V x} := by
  obtain ⟨P, hP, hP'⟩ := hV
  have h : ∀ x, v ∈ V x ↔ (P x).mulVec v = v := by
    intro x
    obtain ⟨-, hidem, hr⟩ := hP' x
    rw [← hr]
    constructor
    · rintro ⟨w, rfl⟩
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hidem]
    · intro hv; exact ⟨v, by simpa using hv⟩
  simp_rw [h]
  have : Measurable fun x => (P x).mulVec v := by
    refine measurable_pi_iff.2 fun j => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ fun k _ => (hP j k).mul_const _
  exact this (measurableSet_singleton v)

theorem exists_sampler (n : ℕ) :
    ∃ Ψ : I → Fin n → ℝ, Measurable Ψ ∧ volume.map Ψ ≪ volume ∧
      (volume : Measure (Fin n → ℝ)) ≪ volume.map Ψ := by
  obtain ⟨ν, hν, h1, h2⟩ := exists_isFiniteMeasure_absolutelyContinuous
    (volume : Measure (Fin n → ℝ))
  have hne : ν Set.univ ≠ 0 := fun h0 =>
    NeZero.ne (volume : Measure (Fin n → ℝ)) (Measure.measure_univ_eq_zero.1 (h1 h0))
  have hnt : ν Set.univ ≠ ⊤ := measure_ne_top _ _
  have : IsProbabilityMeasure ((ν Set.univ)⁻¹ • ν) :=
    ⟨by simp [ENNReal.inv_mul_cancel hne hnt]⟩
  obtain ⟨Ψ, hΨ, hmap⟩ := Measure.exists_measurable_map_eq ((ν Set.univ)⁻¹ • ν)
  refine ⟨Ψ, hΨ, ?_, ?_⟩
  · rw [hmap]
    intro s hs
    show ((ν Set.univ)⁻¹ • ν) s = 0
    simp [h2 hs]
  · rw [hmap]
    intro s hs
    apply h1
    simpa [ENNReal.inv_eq_zero, hnt] using hs

/-- `e_i ∈ V(x)` for `μ`-a.e. `x` with `|x_i| < m`. -/
theorem slab_ae {n : ℕ} (μ : Measure (Vec (n + 1))) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    {V : Vec (n + 1) → Submodule ℝ (Vec (n + 1))} (hV : IsDecompTestField μ V)
    (i : Fin (n + 1)) (m : ℕ) : ∀ᵐ x ∂μ, |x i| < (m : ℝ) → basisVec i ∈ V x := by
  obtain ⟨Ψ, hΨ, h₁, h₂⟩ := exists_sampler n
  have hF := family_isRectifiable μ hμ i m hΨ h₁ h₂
  set B : Set (Vec (n + 1)) := {x | basisVec i ∉ V x} with hBdef
  have hB : MeasurableSet B := (measurableSet_mem hV.1 _).compl
  have hzero : ∀ᵐ t, euclideanHausdorffOne (n + 1) (fam μ i m Ψ t ∩ B) = 0 := by
    filter_upwards [hV.2 _ hF] with t ht
    have harc : IsC1Arc (line i (Ψ t)) (Set.Ioo (-(m : ℝ)) m) :=
      ⟨⟨_, _, rfl⟩, (contDiff_line i _).contDiffOn, (line_injective i _).injOn, fun s _ => by
        rw [deriv_line]
        intro h
        have := congrFun h i
        simp at this⟩
    have h := ht _ _ harc
    have hsub : fam μ i m Ψ t ⊆ line i (Ψ t) '' Set.Ioo (-(m : ℝ)) m := by
      intro x hx
      refine ⟨(split i x).1, ?_, ?_⟩
      · have := hx.1.2
        rw [split_fst]
        exact abs_lt.1 this
      · have := line_split i x
        rwa [hx.2] at this
    rw [Set.inter_eq_left.2 hsub] at h
    have hmeas : MeasurableSet (fam μ i m Ψ t) :=
      (measurableSet_piece μ i m).inter (measurableSet_fiber i _)
    replace h := (ae_restrict_iff' hmeas).1 h
    refine measure_mono_null (fun x hx => ?_) h
    intro hx2
    have := hx2 hx.1 ((split i x).1) (by
      rw [split_fst]; exact abs_lt.1 hx.1.1.2) (by
      have := line_split i x
      rwa [hx.1.2] at this)
    rw [deriv_line] at this
    exact hx.2 this
  have h0 : ∫⁻ t, euclideanHausdorffOne (n + 1) (fam μ i m Ψ t ∩ B) = 0 :=
    (lintegral_congr_ae hzero).trans lintegral_zero
  have hv := (lintegral_family_eq_zero_iff μ i m hΨ h₁ h₂ hB).1 h0
  have hv' : ∀ᵐ x ∂(volume : Measure (Vec (n + 1))), x ∉ B ∩ piece μ i m :=
    measure_eq_zero_iff_ae_notMem.1 hv
  filter_upwards [hμ.ae_le hv', Measure.rnDeriv_pos hμ] with x hx hρ hslab
  by_contra hne
  exact hx ⟨hne, hρ, by simpa using hslab⟩

end AFree.Bundle.AC
