module

public import AFree.Curves.BundleTop.Rank

/-!
# `K(x) ⊂ range P` is a measurable condition

The condition `K(x) ⊂ range P` is expressed in the countable form
`∀ ε ∈ ℚ₊, ∃ m, ∀ i ∈ I_m(x), |(I - P) wᵢ| ≤ ε`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Matrix

namespace AFree.BundleTop

open PDE AFree.Curves

variable {d : ℕ} {w : ℕ → Vec d} {M : ℕ → ℕ → Set (Vec d)} {x : Vec d}

lemma continuous_defect (P : Fin d → Fin d → ℝ) :
    Continuous fun v : Vec d => vecEuclideanNorm (v - Matrix.of P *ᵥ v) :=
  continuous_vecEuclideanNorm.comp
    (continuous_id.sub (Continuous.matrix_mulVec continuous_const continuous_id))

/-- `Φ(x, P) = 0` iff `K(x) ⊂ range P`. -/
lemma selK_fixed_iff (hw : ∀ i, vecEuclideanNorm (w i) = 1) (P : Fin d → Fin d → ℝ) :
    (∀ v ∈ selK w M x, Matrix.of P *ᵥ v = v) ↔
      ∀ q : ℚ, 0 < q → ∃ m, ∀ i ∈ selI M m x, vecEuclideanNorm (w i - Matrix.of P *ᵥ w i) ≤ q := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨q, hq, hlt⟩ := hcon
    choose i hi hgt using hlt
    obtain ⟨v, hv, φ, hφ, hlim⟩ := exists_limit_selK (ι := Unit) hw
      (fun m _ => w (i m)) fun m _ => mem_selA (hi m)
    have hlim' : Tendsto (fun k => w (i (φ k))) atTop (𝓝 (v ())) :=
      ((continuous_apply ()).tendsto _).comp hlim
    have hle : (q : ℝ) ≤ vecEuclideanNorm (v () - Matrix.of P *ᵥ v ()) :=
      ge_of_tendsto ((continuous_defect P).continuousAt.tendsto.comp hlim')
        (Eventually.of_forall fun k => (hgt (φ k)).le)
    rw [h _ (hv ())] at hle
    have h0 : vecEuclideanNorm (v () - v ()) = 0 := by
      rw [sub_self]; exact vecEuclideanNorm_eq_zero_iff.2 rfl
    rw [h0] at hle
    exact absurd hle (by exact_mod_cast not_le.2 hq)
  · intro h v hv
    have hle : ∀ q : ℚ, 0 < q → vecEuclideanNorm (v - Matrix.of P *ᵥ v) ≤ q := by
      intro q hq
      obtain ⟨m, hm⟩ := h q hq
      have hcl : IsClosed {u : Vec d | vecEuclideanNorm (u - Matrix.of P *ᵥ u) ≤ q} :=
        isClosed_le (continuous_defect P) continuous_const
      have hsub : selA w M m x ⊆ {u : Vec d | vecEuclideanNorm (u - Matrix.of P *ᵥ u) ≤ q} := by
        rintro _ ⟨i, hi, rfl⟩
        exact hm i hi
      exact closure_minimal hsub hcl (mem_selK.1 hv m)
    have h0 : vecEuclideanNorm (v - Matrix.of P *ᵥ v) = 0 := by
      refine le_antisymm ?_ (vecEuclideanNorm_nonneg _)
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn hε
      have := hle q (by exact_mod_cast hq0)
      linarith
    have := vecEuclideanNorm_eq_zero_iff.1 h0
    exact (sub_eq_zero.1 this).symm

/-- The set of `(x, P)` with `K(x) ⊂ range P` (`Φ(x, P) = 0`)
is measurable. -/
lemma measurableSet_fixed (hM : ∀ i n, MeasurableSet (M i n))
    (hw : ∀ i, vecEuclideanNorm (w i) = 1) :
    MeasurableSet {p : Vec d × (Fin d → Fin d → ℝ) | ∀ v ∈ selK w M p.1, Matrix.of p.2 *ᵥ v = v} := by
  have : {p : Vec d × (Fin d → Fin d → ℝ) | ∀ v ∈ selK w M p.1, Matrix.of p.2 *ᵥ v = v} =
      ⋂ q : ℚ, ⋂ (_ : 0 < q), ⋃ m : ℕ, ⋂ i : ℕ,
        ({p | i ∈ selI M m p.1}ᶜ ∪ {p | vecEuclideanNorm (w i - Matrix.of p.2 *ᵥ w i) ≤ q}) := by
    ext p
    simp only [mem_ofPred_eq, selK_fixed_iff hw, mem_iInter, mem_iUnion, mem_union, mem_compl_iff]
    refine forall_congr' fun q => forall_congr' fun _ => exists_congr fun m => forall_congr' fun i => ?_
    tauto
  rw [this]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun m =>
    MeasurableSet.iInter fun i => ?_
  refine MeasurableSet.union ?_ ?_
  · exact (measurableSet_mem_selI hM m i).preimage measurable_fst |>.compl
  · have hc : Continuous fun P : Fin d → Fin d → ℝ => vecEuclideanNorm (w i - Matrix.of P *ᵥ w i) :=
      continuous_vecEuclideanNorm.comp
        (continuous_const.sub (Continuous.matrix_mulVec (continuous_id : Continuous fun P : Fin d → Fin d → ℝ => Matrix.of P) continuous_const))
    exact measurableSet_le (hc.measurable.comp measurable_snd) measurable_const

end AFree.BundleTop
