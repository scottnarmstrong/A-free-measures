module

public import AFree.Rademacher.Chain.PertRadius
public import AFree.Rademacher.Chain.PertCover
public import AFree.Rademacher.Chain.PertAssemble
public import AFree.Rademacher.Chain.PertSteps

/-!
# AM Lemma 4.8: the single-stage perturbation

The single-stage perturbation: from `f ∈ X₀` to `f'' ∈ X₀` close to `f` with large directional oscillation on a compact set.
-/

@[expose] public section

open PDE MeasureTheory Filter Topology Set
open scoped ENNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- [AM, Lemma 4.8]. In the setting `(S)`, let `f ∈ X₀`,
`ε, σ > 0` and `E' ⊆ E` Borel. There are `f'' ∈ X₀` and a compact `K ⊆ E'` with
`‖f'' - f‖_sup ≤ 2ε`, `μ K ≥ μ E' / (4 m)` and `U_σ f'' ≥ D` on `K`, where `v = ε_i` and
`D = δ / (3 √m)`. -/
theorem lem_perturbation {μ : Measure (Vec d)} {V : Vec d → Submodule ℝ (Vec d)} {i : Fin d}
    {m : ℕ} {δ : ℝ} {E : Set (Vec d)} {e : Vec d → Fin d → Vec d}
    (hS : Setting μ V i m δ E e) {f : Vec d → ℝ} (hf : f ∈ X0 e) {ε σ : ℝ} (hε : 0 < ε)
    (hσ : 0 < σ) {E' : Set (Vec d)} (hEE : E' ⊆ E) (hE' : MeasurableSet E') :
    ∃ f'' ∈ X0 e, ∃ K ⊆ E', IsCompact K ∧ (∀ y, |f'' y - f y| ≤ 2 * ε) ∧
      μ E' / (4 * (m : ℝ≥0∞)) ≤ μ K ∧
      ∀ x ∈ K, settingD δ m ≤ dirOsc f'' (basisVec i) σ 0 x := by
  have hfin := hS.finite
  have he : IsFrame e := hS.frame
  -- Step 1
  obtain ⟨s, hs0, hs2, hf's, hf'close, hf'D⟩ := pert_shrinking hf hε
  set f' : Vec d → ℝ := fun x => (1 - s) * f x with hf'
  -- Step 2
  obtain ⟨k, hk, hSm, hpieces⟩ := pert_pieces hS hEE hE'
  set q := δ / Real.sqrt m with hq
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hS.m_pos
  have hqpos : 0 < q := by have := hS.delta_pos; positivity
  set S : Set (Vec d) := {x ∈ E' | q ≤ |vecDot (basisVec i) (e x k)|} with hSdef
  have hSE' : S ⊆ E' := fun x hx => hx.1
  -- constants
  have hsq := Real.sqrt_nonneg (d : ℝ)
  set c : ℝ := min (min (q / 24) (s / (2 * (2 + Real.sqrt d)))) (min (s / 3) (1 / 8)) with hcdef
  have hcpos : 0 < c := lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity)
    (by norm_num))
  have hcq : c ≤ q / 24 := (min_le_left _ _).trans (min_le_left _ _)
  have hcs : c ≤ s / (2 * (2 + Real.sqrt d)) := (min_le_left _ _).trans (min_le_right _ _)
  have hcs3 : c ≤ s / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hc8 : c ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hc1 : (2 + Real.sqrt d) * c ≤ s / 2 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (2 + Real.sqrt d))).1 hcs
    nlinarith
  have hc2 : 3 * c ≤ s := by linarith
  obtain ⟨hβ0, hβ2, hcos, htan⟩ := cone_angle hcpos hc8
  set β := Real.arccos c with hβ
  -- radii
  have hRex := fun p : Vec d => pert_radius he hf's hs0 hs2 hcpos hc8 hc1 hc2 hσ hf'D p
  choose R hRpos hRσ hRc hLD using hRex
  -- covering
  obtain ⟨T, ρ, ρ', Kf, hT, hdis, hμ⟩ := pert_covering μ (S := S) hSm (R := R)
    (fun p _ => hRpos p) (fun p _ K => IsCNull (cone (e p k) β) K) (by
      intro p hp r hr hrR
      have hld := hLD p r hr hrR
      refine pert_local_cone_null hS hk hβ0 hβ2 (ω := c / 4) (by rw [hcos]; linarith)
        (fun y hy => hld.e_close y (by linarith) k) (hSm.inter measurableSet_closedBall)
        (fun x hx => ⟨hEE (hSE' hx.1), hx.2⟩))
  -- the cut-off functions
  obtain ⟨ε', hε'pos, hε'ε, hε'ρ⟩ := exists_pos_le_finset T (fun p => ρ p ^ 2)
    (fun p hp => pow_pos (hT p hp).2.1 2) (a := min ε s) (lt_min hε hs0)
  have hgex : ∀ p : Vec d, ∃ g : Vec d → ℝ, p ∈ T → (ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ ε') ∧
      tsupport g ⊆ Metric.closedBall p (ρ' p) ∧
      (∀ x, -ε' ≤ fderiv ℝ g x (e p k) ∧ fderiv ℝ g x (e p k) ≤ 1 + ε') ∧
      (∀ x ∈ Kf p, fderiv ℝ g x (e p k) = 1) ∧
      ∀ x w, vecDot w (e p k) = 0 → |fderiv ℝ g x w| ≤ (2 / Real.tan β) * vecEuclideanNorm w) := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨hpS, hρ0, hρR, hρρ', hρ'2, hKsub, hKc, hKnull⟩ := hT p hp
      obtain ⟨g, hg⟩ := lem_perturbcut (IsFrame.norm_eq_one he p k) hβ0 hβ2 hρ0 hρρ' hKc
        (hKsub.trans inter_subset_right) hKnull hε'pos
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose g hg using hgex
  set ς : Vec d → ℝ := fun p => if fderiv ℝ f' p (e p k) ≤ 0 then 1 else -1 with hς
  -- the pieces
  have hpiece : ∀ p ∈ T, Piece e f' (basisVec i) k q s (c / 4) (c / 4) (c / 2) σ ε' p (ρ p)
      (ρ' p) (g p) (Kf p) (ς p) := by
    intro p hp
    obtain ⟨hpS, hρ0, hρR, hρρ', hρ'2, hKsub, hKc, hKnull⟩ := hT p hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg p hp
    refine ⟨hLD p _ hρ0 hρR, ⟨h1, h2, h3, h4, h5, fun x w hw => ?_⟩, hρρ', hρ'2,
      (hε'ε.trans (min_le_right _ _)), hε'ρ p hp, ?_, ?_, hKsub.trans inter_subset_right,
      fun x hx => (hKsub hx).1.2, ?_, ?_⟩
    · have := h6 x w hw
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (vecEuclideanNorm_nonneg _))
      linarith
    · linarith [hRσ p]
    · linarith [hRc p]
    · simp only [hς]
      by_cases hneg : fderiv ℝ f' p (e p k) ≤ 0
      · exact Or.inl ⟨by simp [hneg], hneg⟩
      · exact Or.inr ⟨by simp [hneg], lt_of_not_ge hneg⟩
    · linarith
  have hv := vecEuclideanNorm_basisVec i
  obtain ⟨hX0, hGb, hdir⟩ := pert_assemble hf's he hv hε'pos T ρ ρ' g Kf ς hpiece hdis
  have hε'ε1 : ε' ≤ ε := hε'ε.trans (min_le_left _ _)
  refine ⟨_, hX0, ⋃ p ∈ T, Kf p, ?_, T.isCompact_biUnion fun p hp => (hT p hp).2.2.2.2.2.2.1,
    fun y => ?_, ?_, ?_⟩
  · exact iUnion₂_subset fun p hp => ((hT p hp).2.2.2.2.2.1.trans inter_subset_left).trans hSE'
  · have h1 := hf'close y
    have h2 := hGb y
    have : f' y + ∑ p ∈ T, ς p / 2 * g p y - f y = (f' y - f y) + ∑ p ∈ T, ς p / 2 * g p y := by
      ring
    rw [this]
    calc _ ≤ |f' y - f y| + |∑ p ∈ T, ς p / 2 * g p y| := abs_add_le _ _
      _ ≤ 2 * ε := by linarith
  · apply ENNReal.div_le_of_le_mul
    calc μ E' ≤ (m : ℝ≥0∞) * μ S := hpieces
      _ ≤ (m : ℝ≥0∞) * (4 * μ (⋃ p ∈ T, Kf p)) := by gcongr
      _ = μ (⋃ p ∈ T, Kf p) * (4 * m) := by ring
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx
    have := hdir p hp x hxp
    have hD : settingD δ m = q / 3 := by
      unfold settingD; rw [hq]; field_simp
    rw [hD]; exact this

end AFree.Rademacher
