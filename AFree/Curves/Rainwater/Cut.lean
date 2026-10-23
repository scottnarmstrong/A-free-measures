module

public import AFree.Curves.Rainwater.GkTop

/-!
# Covering a `C`-curve by `𝒢_k`-curves
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- The reparametrized extended graph curve `ξ(s) = γ̄(u₀ + cos α · s)`, where
`γ̄(u) = u e + η(clamp u)`. -/
private noncomputable def xiCurve (e : Vec d) (α u₀ u₁ : ℝ) (η : ℝ → Vec d) (s : ℝ) : Vec d :=
  graphCurve e (fun u => η (if h : u₀ ≤ u₁ then (Set.projIcc u₀ u₁ h u : ℝ) else u))
    (u₀ + Real.cos α * s)

private lemma xi_incr {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {u₀ u₁ : ℝ} (h01 : u₀ ≤ u₁) {η : ℝ → Vec d}
    (hη : IsConeGraphFn e α u₀ u₁ η) {s s' : ℝ} (hss : s ≤ s') :
    vecEuclideanNorm (xiCurve e α u₀ u₁ η s' - xiCurve e α u₀ u₁ η s) ≤ s' - s ∧
      Real.cos α * (s' - s) ≤ vecDot (xiCurve e α u₀ u₁ η s' - xiCurve e α u₀ u₁ η s) e := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  set cl : ℝ → ℝ := fun u => (Set.projIcc u₀ u₁ h01 u : ℝ) with hcl
  have hmem : ∀ u, cl u ∈ Icc u₀ u₁ := fun u => (Set.projIcc u₀ u₁ h01 u).2
  have hlip : ∀ u u', |cl u' - cl u| ≤ |u' - u| := fun u u' => by
    have := Set.abs_projIcc_sub_projIcc (h := h01) (c := u') (d := u)
    exact this
  set η' : ℝ → Vec d := fun u => η (cl u) with hη'
  have hxi : ∀ t, xiCurve e α u₀ u₁ η t = graphCurve e η' (u₀ + Real.cos α * t) := fun t => by
    simp [xiCurve, h01, hη', hcl]
  set u := u₀ + Real.cos α * s
  set u' := u₀ + Real.cos α * s'
  have huu : u' - u = Real.cos α * (s' - s) := by simp only [u, u']; ring
  have hd : vecDot (xiCurve e α u₀ u₁ η s' - xiCurve e α u₀ u₁ η s) e = u' - u := by
    rw [hxi, hxi, Curves.vecDot_sub_left]
    have key : ∀ t, vecDot (graphCurve e η' t) e = t := fun t => by
      rw [graphCurve, Curves.vecDot_add_left, Curves.vecDot_smul_left, Curves.vecDot_self,
        (by have := vecEuclideanNorm_sq e; rw [he] at this; linarith : vecNormSq e = 1),
        hη.1 _ (hmem t)]
      ring
    rw [key, key]
  refine ⟨?_, by rw [hd, huu]⟩
  have hw : vecNormSq (η' u' - η' u) ≤ (Real.tan α * |u' - u|) ^ 2 := by
    have h1 := hη.2 _ (hmem u') _ (hmem u)
    have h2 : Real.tan α * |cl u' - cl u| ≤ Real.tan α * |u' - u| :=
      mul_le_mul_of_nonneg_left (hlip u u') (Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2).le
    have h0 := vecEuclideanNorm_sq (η' u' - η' u)
    rw [← h0]
    exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) (h1.trans (by simpa [hη', abs_sub_comm]
      using h2)) 2
  have hpy := Curves.vecNormSq_sub_dot_smul he
    (xiCurve e α u₀ u₁ η s' - xiCurve e α u₀ u₁ η s)
  have hw' : xiCurve e α u₀ u₁ η s' - xiCurve e α u₀ u₁ η s -
      vecDot (xiCurve e α u₀ u₁ η s' - xiCurve e α u₀ u₁ η s) e • e = η' u' - η' u := by
    rw [hd, hxi, hxi, graphCurve, graphCurve, sub_smul]; abel
  rw [hw', hd] at hpy
  have h3 : Real.tan α * |u' - u| = Real.sin α * (s' - s) := by
    rw [huu, abs_of_nonneg (mul_nonneg hc.le (sub_nonneg.2 hss)), Real.tan_eq_sin_div_cos]
    field_simp
  rw [h3] at hw
  have hs1 := Real.sin_sq_add_cos_sq α
  rw [huu] at hpy
  refine Curves.vecEuclideanNorm_le_of_sq (sub_nonneg.2 hss) ?_
  calc vecNormSq (xiCurve e α u₀ u₁ η s' - xiCurve e α u₀ u₁ η s)
      = vecNormSq (η' u' - η' u) + (Real.cos α * (s' - s)) ^ 2 := by linarith
    _ ≤ (Real.sin α * (s' - s)) ^ 2 + (Real.cos α * (s' - s)) ^ 2 := by linarith
    _ = (s' - s) ^ 2 := by
        have : (Real.sin α * (s' - s)) ^ 2 + (Real.cos α * (s' - s)) ^ 2 =
          (Real.sin α ^ 2 + Real.cos α ^ 2) * (s' - s) ^ 2 := by ring
        rw [this, hs1, one_mul]

private lemma continuous_xi {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    {u₀ u₁ : ℝ} (h01 : u₀ ≤ u₁) {η : ℝ → Vec d} (hη : IsConeGraphFn e α u₀ u₁ η) :
    Continuous (xiCurve e α u₀ u₁ η) := by
  have hηc : ContinuousOn η (Icc u₀ u₁) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := (Real.tan α).toNNReal) fun x hx y hy => ?_)
      |>.continuousOn
    have h1 := hη.2 x hx y hy
    have h2 := norm_le_vecEuclideanNorm (η x - η y)
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _
      (Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2).le]
    linarith
  have hc : Continuous fun s : ℝ => η (Set.projIcc u₀ u₁ h01 (u₀ + Real.cos α * s) : ℝ) :=
    hηc.comp_continuous (continuous_subtype_val.comp (continuous_projIcc.comp (by fun_prop)))
      fun s => (Set.projIcc u₀ u₁ h01 _).2
  unfold xiCurve graphCurve
  simp only [h01, ↓reduceDIte]
  exact (by fun_prop : Continuous fun s : ℝ => (u₀ + Real.cos α * s) • e).add hc

/-- A `C`-curve `G` (`C = C(e, α)`) is covered by finitely many `ζ_j ∈ 𝒢(C)`, and
each `ζ_j` whose image meets `B(k)` lies in `𝒢_k`. Consequently, if `𝓛¹(ζ⁻¹E) = 0` for all
`ζ ∈ 𝒢_k`, then `𝓗¹(E ∩ B(k) ∩ G) = 0` (no Borel hypothesis on `E` is needed). -/
theorem ccurve_cut {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {G : Set (Vec d)} (hG : IsCCurve (cone e α) G) (k : ℕ) :
    (∃ (M : ℕ) (ζ : Fin M → C(I, Vec d)), (∀ j, ζ j ∈ ccurveSpace e α) ∧
        G ⊆ ⋃ j, range (ζ j) ∧
        ∀ j, (range (ζ j) ∩ euclideanClosedBall 0 (k : ℝ)).Nonempty → ζ j ∈ ccurveSpaceK e α k) ∧
    ∀ E : Set (Vec d), (∀ ζ ∈ ccurveSpaceK e α k, volume (ζ ⁻¹' E) = 0) →
      euclideanHausdorffOne d (E ∩ euclideanClosedBall 0 (k : ℝ) ∩ G) = 0 := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  obtain ⟨u₀, u₁, η, h01, hη, rfl⟩ := ccurve_exists_graph he hα hα2 hG
  have hxi := continuous_xi hα hα2 h01 hη
  set M : ℕ := ⌈(u₁ - u₀) / Real.cos α⌉₊ + 1 with hM
  let ζ : Fin M → C(I, Vec d) := fun j =>
    ⟨fun s => xiCurve e α u₀ u₁ η ((j : ℕ) + (s : ℝ)),
      hxi.comp (continuous_const.add continuous_subtype_val)⟩
  have hζG : ∀ j, ζ j ∈ ccurveSpace e α := fun j s s' hss => by
    have := xi_incr he hα hα2 h01 hη (s := (j : ℕ) + (s : ℝ)) (s' := (j : ℕ) + (s' : ℝ))
      (by have : (s : ℝ) ≤ s' := hss; linarith)
    exact (by simpa using this : _ ∧ _)
  have hcover : graphCurve e η '' Icc u₀ u₁ ⊆ ⋃ j, range (ζ j) := by
    rintro _ ⟨u, hu, rfl⟩
    set s : ℝ := (u - u₀) / Real.cos α with hs
    have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.2 hu.1) hc.le
    have hs1 : s ≤ (u₁ - u₀) / Real.cos α :=
      div_le_div_of_nonneg_right (sub_le_sub_right hu.2 _) hc.le
    have hj : ⌊s⌋₊ < M := by
      have : (⌊s⌋₊ : ℝ) ≤ ⌈(u₁ - u₀) / Real.cos α⌉₊ :=
        (Nat.floor_le hs0).trans (hs1.trans (Nat.le_ceil _))
      have := Nat.cast_le.1 this
      omega
    refine mem_iUnion.2 ⟨⟨⌊s⌋₊, hj⟩, ⟨s - ⌊s⌋₊, ⟨by linarith [Nat.floor_le hs0], ?_⟩⟩, ?_⟩
    · linarith [Nat.lt_floor_add_one s]
    · change xiCurve e α u₀ u₁ η ((⌊s⌋₊ : ℕ) + (s - ⌊s⌋₊)) = _
      have hu' : u₀ + Real.cos α * s = u := by rw [hs]; field_simp; ring
      rw [add_sub_cancel, xiCurve, hu', graphCurve]
      simp [h01, Set.projIcc_of_mem h01 hu, graphCurve]
  have hmeetK : ∀ j, (range (ζ j) ∩ euclideanClosedBall 0 (k : ℝ)).Nonempty →
      ζ j ∈ ccurveSpaceK e α k := by
    rintro j ⟨_, ⟨s, rfl⟩, hx⟩
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity), sub_zero] at hx
    exact ⟨hζG j, s, hx⟩
  refine ⟨⟨M, ζ, hζG, hcover, hmeetK⟩, fun E hE => ?_⟩
  refine measure_mono_null (t := ⋃ j : Fin M, ⋃ (_ : ζ j ∈ ccurveSpaceK e α k),
    E ∩ range (ζ j)) ?_ (measure_iUnion_null fun j => measure_iUnion_null fun hj => ?_)
  · rintro x ⟨⟨hxE, hxB⟩, hxG⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcover hxG)
    exact mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hmeetK j ⟨x, hj, hxB⟩, hxE, hj⟩⟩
  · have hcmp := (ccurveSpace_measure_comparison he hα hα2 (hζG j)).2 E
    exact le_antisymm (hcmp.1.trans (hE _ hj).le) bot_le

end AFree
