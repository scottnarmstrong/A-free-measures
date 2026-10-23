module

public import AFree.Paper.SimpleAE.Cut
public import AFree.Paper.Currents.Covector
public import AFree.Algebra.KVec

/-!
# A.e. simplicity for locally normal `(d-2)`-currents

[DPR, Remark 1.11]: the polar of a locally normal `(d-2)`-current is simple a.e. with respect to the
singular part, proved for `d ≤ 2`, for one ball, and globally.
-/

public section

open MeasureTheory

namespace AFree

open PDE

variable {d : ℕ}

/-- If `d ≤ 2` then `d - 2 = 0` and every `P x` is simple. -/
theorem isSimpleKVec_of_dim_le_two (hd : d ≤ 2) (w : KVec d (d - 2)) : IsSimpleKVec w :=
  isSimpleKVec_of_eq_zero (by omega) w

/-- For `d ≥ 3` and `B = B_R`, `P(x)` is simple for `σˢ`-a.e. `x`,
`σ = τ ⌞ B`. -/
theorem simpleae_ball (hd : 3 ≤ d) {τ : Measure (Vec d)} {P : Vec d → KVec d (d - 2)}
    (hT : IsLocNormalCurrent τ P) (R : ℝ) :
    ∀ᵐ x ∂(τ.restrict (Metric.ball (0 : Vec d) R)).singularPart volume, IsSimpleKVec (P x) := by
  obtain ⟨hfin, _, ⟨hvar, hpol⟩, τ', P', _, _, hbd, hout⟩ := cut hT R
  set B := Metric.ball (0 : Vec d) R
  set σ := τ.restrict B
  have h := ae_exists_covector_interiorProduct_eq_zero B Metric.isOpen_ball (r := 1)
    (fun _ => d - 2) (fun _ => ⟨by omega, by omega⟩)
    (fun _ => σ.withDensityᵥ P) (fun _ => ⟨hout, _, hbd⟩) σ
    (by rwa [hvar] at hout)
    (fun K _ _ => measure_lt_top σ K) (fun _ => by rw [hvar])
  have hle : σ.singularPart volume ≪ σ :=
    Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ _)
  filter_upwards [h, hle.ae_le hpol] with x ⟨ω, hω, hx⟩ hxp
  rw [← hxp]
  have hx0 := hx 0
  refine simplelin (covectorKernel ω) (finrank_covectorKernel ω hω) _ ?_
  exact (equiv_interiorProduct_kvecSpan (by omega) ω hω _).1 hx0

/-- If `P(x)` is simple `(τ ⌞ B_R)ˢ`-a.e. for every `R ∈ ℕ`
(with `τ` locally finite), then `P(x)` is simple `τˢ`-a.e. -/
theorem simpleae_globalize {τ : Measure (Vec d)} (hτ : IsLocallyFiniteMeasure τ)
    {k : ℕ} (P : Vec d → KVec d k)
    (h : ∀ R : ℕ, ∀ᵐ x ∂(τ.restrict (Metric.ball (0 : Vec d) R)).singularPart volume,
      IsSimpleKVec (P x)) :
    ∀ᵐ x ∂τ.singularPart volume, IsSimpleKVec (P x) := by
  rw [ae_iff]
  have hU : {x | ¬ IsSimpleKVec (P x)} ⊆
      ⋃ n : ℕ, {x | ¬ IsSimpleKVec (P x)} ∩ Metric.ball (0 : Vec d) n := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact Set.mem_iUnion.2 ⟨n, hx, by simpa using hn⟩
  refine measure_mono_null hU (measure_iUnion_null fun n => ?_)
  refine singularPart_apply_eq_zero_of_restrict τ Metric.isOpen_ball.measurableSet
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : Vec d) n).measure_lt_top) Set.inter_subset_right ?_
  exact measure_mono_null Set.inter_subset_left (ae_iff.1 (h n))

/-- [DPR, Remark 1.11]: `P(x)` is simple for `τˢ`-a.e. `x`. -/
theorem simpleae {τ : Measure (Vec d)} {P : Vec d → KVec d (d - 2)}
    (hT : IsLocNormalCurrent τ P) : ∀ᵐ x ∂τ.singularPart volume, IsSimpleKVec (P x) := by
  by_cases hd : d ≤ 2
  · exact Filter.Eventually.of_forall fun x => isSimpleKVec_of_dim_le_two hd (P x)
  · exact simpleae_globalize hT.1 P fun R => simpleae_ball (by omega) hT R

end AFree
