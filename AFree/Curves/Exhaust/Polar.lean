module

public import AFree.Curves.Exhaust.Mass
public import AFree.Measure.VectorIntegral

/-!
# The polar of a curve current lies in the cone
-/

@[expose] public section

open MeasureTheory Set

namespace AFree

open PDE

variable {d : ℕ}

/-- `ℓ ⬝ T(B) = ∫_B ℓ ⬝ T⃗ d|T|` for a `1`-current `T` and measurable `B`. -/
lemma vecDot_kvecOne_eq_setIntegral (T : VectorMeasure (Vec d) (KVec d 1)) {B : Set (Vec d)}
    (hB : MeasurableSet B) (ℓ : Vec d) :
    vecDot (kvecOneToVec (T B)) ℓ =
      ∫ x in B, vecDot (kvecOneToVec (polar T x)) ℓ ∂(euclideanVariation T) := by
  have hint : ∀ j, Integrable (fun x => polar T x ⟨{j}, Finset.card_singleton j⟩ * ℓ j)
      ((euclideanVariation T).restrict B) := fun j =>
    ((integrable_polar_apply T _).restrict).mul_const _
  simp only [vecDot, kvecOneToVec]
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, ← coordMeasure_eq_setIntegral T _ hB]
  rfl

lemma integrable_vecDot_polar (T : VectorMeasure (Vec d) (KVec d 1)) (ℓ : Vec d) :
    Integrable (fun x => vecDot (kvecOneToVec (polar T x)) ℓ) (euclideanVariation T) := by
  simp only [vecDot, kvecOneToVec]
  exact integrable_finsetSum _ fun j _ => (integrable_polar_apply T _).mul_const _

lemma measurable_vecDot_polar (T : VectorMeasure (Vec d) (KVec d 1)) (ℓ : Vec d) :
    Measurable (fun x => vecDot (kvecOneToVec (polar T x)) ℓ) := by
  simp only [vecDot, kvecOneToVec]
  exact Finset.measurable_sum _ fun j _ => (measurable_polar_apply T _).mul_const _

/-- Write `p = kvecOneToVec (polar N_ρ)`. Then `p ∈ C`
`|N_ρ|`-a.e.; `w ⬝ p > 0` `[ρ]`-a.e.; and for every `μ ≪ [ρ]`, `p ∈ C ∖ {0}` `μ`-a.e. -/
theorem curveCurrent_polar {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] :
    (∀ᵐ x ∂(euclideanVariation (curveCurrent e α ρ)),
        kvecOneToVec (polar (curveCurrent e α ρ) x) ∈ cone e α) ∧
      (∀ᵐ x ∂(curveMix (ccurveSpace e α) ρ),
        0 < vecDot (kvecOneToVec (polar (curveCurrent e α ρ) x)) e) ∧
      ∀ μ : Measure (Vec d), μ ≪ curveMix (ccurveSpace e α) ρ →
        ∀ᵐ x ∂μ, kvecOneToVec (polar (curveCurrent e α ρ) x) ∈ cone e α ∧
          kvecOneToVec (polar (curveCurrent e α ρ) x) ≠ 0 := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα2⟩
  obtain ⟨hmass, hac⟩ := curveCurrent_mass_lower he hα hα2 ρ
  set T := curveCurrent e α ρ with hT
  obtain ⟨D0, hD0c, hD0p, hcone⟩ := (cone_calculus he hα hα2).2.2.2
  -- polar cone part
  have hl : ∀ ℓ ∈ D0, ∀ᵐ x ∂(euclideanVariation T),
      vecDot (kvecOneToVec (polar T x)) ℓ ≤ 0 := by
    intro ℓ hℓ
    have h := ae_nonneg_of_forall_setIntegral_nonneg (μ := euclideanVariation T)
      (f := fun x => -vecDot (kvecOneToVec (polar T x)) ℓ)
      (integrable_vecDot_polar T ℓ).neg (fun B hB _ => by
        rw [integral_neg, ← vecDot_kvecOne_eq_setIntegral T hB ℓ, hT,
          vecDot_curveCurrent hα hα2 ρ hB ℓ, neg_nonneg]
        refine integral_nonpos_of_ae (ae_restrict_of_ae ?_)
        filter_upwards [(curveDeriv_borel hα hα2).2.2 ρ] with p hp
        rw [vecDot_comm]
        exact hD0p ℓ hℓ _ hp.2.1)
    filter_upwards [h] with x hx using by simpa using hx
  have hcone_ae : ∀ᵐ x ∂(euclideanVariation T), kvecOneToVec (polar T x) ∈ cone e α := by
    have := (ae_ball_iff hD0c).2 hl
    filter_upwards [this] with x hx
    rw [hcone]
    simp only [mem_iInter]
    intro ℓ hℓ
    have := hx ℓ hℓ
    rwa [vecDot_comm] at this
  -- positivity of w ⬝ p
  have hpos : ∀ᵐ x ∂(curveMix (ccurveSpace e α) ρ),
      0 < vecDot (kvecOneToVec (polar T x)) e := by
    have hZ : MeasurableSet {x | vecDot (kvecOneToVec (polar T x)) e ≤ 0} :=
      measurableSet_le (measurable_vecDot_polar T e) measurable_const
    have h1 := (hmass _ hZ).1
    have h2 : vecDot (kvecOneToVec (T {x | vecDot (kvecOneToVec (polar T x)) e ≤ 0})) e ≤ 0 := by
      rw [vecDot_kvecOne_eq_setIntegral T hZ e]
      exact setIntegral_nonpos hZ fun x hx => hx
    have h3 := h1.trans (ENNReal.ofReal_le_ofReal h2)
    rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero, mul_eq_zero] at h3
    have h4 := h3.resolve_left (by simpa using hc)
    rw [ae_iff]
    simpa using h4
  refine ⟨hcone_ae, hpos, fun μ hμ => ?_⟩
  filter_upwards [hμ.ae_le hpos, (hμ.trans hac).ae_le hcone_ae] with x hx1 hx2
  refine ⟨hx2, fun h0 => ?_⟩
  rw [h0] at hx1
  simp [vecDot] at hx1

end AFree
