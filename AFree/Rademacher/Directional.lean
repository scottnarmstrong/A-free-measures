module

public import AFree.Defs
public import AFree.Rademacher.Dot
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Directional oscillation

For a Lipschitz `F`, a unit
vector `v` and `0 ≤ σ' < σ`: the difference quotient `q_F(x, h) = (F(x + h v) - F(x)) / h`, its
supremum `T⁺_{σ,σ'}F(x)` and infimum `T⁻_{σ,σ'}F(x)` over `σ' < h ≤ σ`, the oscillation
`U_{σ,σ'} = T⁺ - T⁻` and `U_σ = U_{σ,0}`.
-/

@[expose] public section

open PDE Filter Topology Set
open scoped NNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- The difference quotient `q_F(x, h) = (F(x + h v) - F(x)) / h`. -/
noncomputable def dirQuot (F : Vec d → ℝ) (v x : Vec d) (h : ℝ) : ℝ := (F (x + h • v) - F x) / h

/-- `T⁺_{σ,σ'}F(x) = sup_{σ' < h ≤ σ} q_F(x, h)`. -/
noncomputable def dirSup (F : Vec d → ℝ) (v : Vec d) (σ σ' : ℝ) (x : Vec d) : ℝ :=
  sSup (dirQuot F v x '' Ioc σ' σ)

/-- `T⁻_{σ,σ'}F(x) = inf_{σ' < h ≤ σ} q_F(x, h)`. -/
noncomputable def dirInf (F : Vec d → ℝ) (v : Vec d) (σ σ' : ℝ) (x : Vec d) : ℝ :=
  sInf (dirQuot F v x '' Ioc σ' σ)

/-- `U_{σ,σ'} = T⁺_{σ,σ'} - T⁻_{σ,σ'}`; the oscillation `U_σ` of the source is `dirOsc F v σ 0`. -/
noncomputable def dirOsc (F : Vec d → ℝ) (v : Vec d) (σ σ' : ℝ) (x : Vec d) : ℝ :=
  dirSup F v σ σ' x - dirInf F v σ σ' x

theorem abs_dirQuot_le {F : Vec d → ℝ} {K : ℝ≥0} (hF : IsEuclLipschitzWith K F) {v : Vec d}
    (hv : vecEuclideanNorm v = 1) (x : Vec d) {h : ℝ} (hh : h ≠ 0) : |dirQuot F v x h| ≤ K := by
  unfold dirQuot
  have h1 := hF (x + h • v) x
  rw [add_sub_cancel_left, vecEuclideanNorm_smul, hv, mul_one] at h1
  rw [abs_div, div_le_iff₀ (abs_pos.2 hh)]
  linarith

private theorem bdd_image {F : Vec d → ℝ} (hF : IsLipFun F) {v : Vec d}
    (hv : vecEuclideanNorm v = 1) (x : Vec d) {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    BddAbove (dirQuot F v x '' S) ∧ BddBelow (dirQuot F v x '' S) := by
  obtain ⟨K, hK⟩ := hF
  refine ⟨⟨K, ?_⟩, ⟨-K, ?_⟩⟩ <;> rintro _ ⟨h, hh, rfl⟩ <;>
    have := abs_dirQuot_le hK hv x (ne_of_gt (hS hh)) <;> [exact (abs_le.1 this).2;
      exact (abs_le.1 this).1]

private theorem Ioc_sub {σ' σ : ℝ} (h : 0 ≤ σ') : Ioc σ' σ ⊆ Ioi 0 := fun _ hx => lt_of_le_of_lt h hx.1

theorem dirOsc_nonneg {F : Vec d → ℝ} (hF : IsLipFun F) {v : Vec d} (hv : vecEuclideanNorm v = 1)
    {σ σ' : ℝ} (hσ' : 0 ≤ σ') (x : Vec d) : 0 ≤ dirOsc F v σ σ' x := by
  unfold dirOsc dirSup dirInf
  by_cases hne : (Ioc σ' σ).Nonempty
  · obtain ⟨hb1, hb2⟩ := bdd_image hF hv x (Ioc_sub hσ')
    exact sub_nonneg.2 (csInf_le_csSup (hne.image _) hb2 hb1)
  · rw [not_nonempty_iff_eq_empty.1 hne]; simp

private theorem osc_mono {F : Vec d → ℝ} (hF : IsLipFun F) {v : Vec d}
    (hv : vecEuclideanNorm v = 1) (x : Vec d) {S T : Set ℝ} (hST : S ⊆ T) (hT : T ⊆ Ioi 0)
    (hS : S.Nonempty) :
    sSup (dirQuot F v x '' S) - sInf (dirQuot F v x '' S) ≤
      sSup (dirQuot F v x '' T) - sInf (dirQuot F v x '' T) := by
  obtain ⟨hb1, hb2⟩ := bdd_image hF hv x hT
  have h1 : sSup (dirQuot F v x '' S) ≤ sSup (dirQuot F v x '' T) :=
    csSup_le_csSup hb1 (hS.image _) (image_mono hST)
  have h2 : sInf (dirQuot F v x '' T) ≤ sInf (dirQuot F v x '' S) :=
    csInf_le_csInf hb2 (hS.image _) (image_mono hST)
  linarith

/-- `U_{σ,σ'}F ≤ U_σ F` for `σ' ≥ 0` (the hypothesis `σ' < σ` is not
needed). -/
theorem dirOsc_le_dirOsc_zero {F : Vec d → ℝ} (hF : IsLipFun F) {v : Vec d}
    (hv : vecEuclideanNorm v = 1) {σ σ' : ℝ} (hσ' : 0 ≤ σ') (x : Vec d) :
    dirOsc F v σ σ' x ≤ dirOsc F v σ 0 x := by
  by_cases hne : (Ioc σ' σ).Nonempty
  · exact osc_mono hF hv x (Ioc_subset_Ioc_left hσ') (Ioc_sub le_rfl) hne
  · have := dirOsc_nonneg hF hv (σ := σ) (le_refl 0) x
    unfold dirOsc dirSup dirInf at this ⊢
    rw [not_nonempty_iff_eq_empty.1 hne]; simpa using this

/-- `σ ↦ U_σ F(x)` is nondecreasing. -/
theorem dirOsc_zero_mono {F : Vec d → ℝ} (hF : IsLipFun F) {v : Vec d}
    (hv : vecEuclideanNorm v = 1) (x : Vec d) {σ₁ σ₂ : ℝ} (h : σ₁ ≤ σ₂) :
    dirOsc F v σ₁ 0 x ≤ dirOsc F v σ₂ 0 x := by
  by_cases hne : (Ioc 0 σ₁).Nonempty
  · exact osc_mono hF hv x (Ioc_subset_Ioc_right h) (Ioc_sub le_rfl) hne
  · have := dirOsc_nonneg hF hv (σ := σ₂) (le_refl 0) x
    unfold dirOsc dirSup dirInf at this ⊢
    rw [not_nonempty_iff_eq_empty.1 hne]; simpa using this

private theorem sSup_sub_le {S : Set ℝ} {f g : ℝ → ℝ} {c : ℝ} (hne : S.Nonempty)
    (hf : BddAbove (f '' S)) (hg : BddAbove (g '' S)) (h : ∀ t ∈ S, |g t - f t| ≤ c) :
    |sSup (g '' S) - sSup (f '' S)| ≤ c := by
  have key : ∀ {f g : ℝ → ℝ}, BddAbove (f '' S) → (∀ t ∈ S, g t ≤ f t + c) →
      sSup (g '' S) ≤ sSup (f '' S) + c := by
    intro f g hf hfg
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact (hfg t ht).trans (add_le_add_left (le_csSup hf ⟨t, ht, rfl⟩) c)
  have h1 := key hf (f := f) (g := g) fun t ht => by linarith [(abs_le.1 (h t ht)).2]
  have h2 := key hg (f := g) (g := f) fun t ht => by linarith [(abs_le.1 (h t ht)).1]
  rw [abs_le]; constructor <;> linarith

private theorem sInf_sub_le {S : Set ℝ} {f g : ℝ → ℝ} {c : ℝ} (hne : S.Nonempty)
    (hf : BddBelow (f '' S)) (hg : BddBelow (g '' S)) (h : ∀ t ∈ S, |g t - f t| ≤ c) :
    |sInf (g '' S) - sInf (f '' S)| ≤ c := by
  have key : ∀ {f g : ℝ → ℝ}, BddBelow (f '' S) → (∀ t ∈ S, |g t - f t| ≤ c) →
      sInf (f '' S) - c ≤ sInf (g '' S) := by
    intro f g hf hfg
    refine le_csInf (hne.image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    have := csInf_le hf ⟨t, ht, rfl⟩
    linarith [(abs_le.1 (hfg t ht)).1]
  have h1 := key hf (f := f) (g := g) h
  have h2 := key hg (f := g) (g := f) fun t ht => by rw [abs_sub_comm]; exact h t ht
  rw [abs_le]; constructor <;> linarith

/-- For `σ' > 0` and `|G - F| ≤ M` pointwise (so `M` may be taken
to be `‖G - F‖_sup`): `|T^±_{σ,σ'}G(x) - T^±_{σ,σ'}F(x)| ≤ 2M/σ'`, hence
`|U_{σ,σ'}G(x) - U_{σ,σ'}F(x)| ≤ 4M/σ'`. -/
theorem dirOsc_lipschitz_dependence {F G : Vec d → ℝ} (hF : IsLipFun F) (hG : IsLipFun G)
    {v : Vec d} (hv : vecEuclideanNorm v = 1) {σ σ' : ℝ} (hσ' : 0 < σ') {M : ℝ}
    (hM : ∀ y, |G y - F y| ≤ M) (x : Vec d) :
    |dirSup G v σ σ' x - dirSup F v σ σ' x| ≤ 2 * M / σ' ∧
    |dirInf G v σ σ' x - dirInf F v σ σ' x| ≤ 2 * M / σ' ∧
    |dirOsc G v σ σ' x - dirOsc F v σ σ' x| ≤ 4 * M / σ' := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x)
  have hc : 0 ≤ 2 * M / σ' := by positivity
  by_cases hne : (Ioc σ' σ).Nonempty
  · obtain ⟨hF1, hF2⟩ := bdd_image hF hv x (Ioc_sub hσ'.le)
    obtain ⟨hG1, hG2⟩ := bdd_image hG hv x (Ioc_sub hσ'.le)
    have hpt : ∀ h ∈ Ioc σ' σ, |dirQuot G v x h - dirQuot F v x h| ≤ 2 * M / σ' := by
      intro h hh
      have hhpos : 0 < h := hσ'.trans hh.1
      have e1 : dirQuot G v x h - dirQuot F v x h =
          ((G - F) (x + h • v) - (G - F) x) / h := by
        unfold dirQuot; simp only [Pi.sub_apply]; ring
      rw [e1, abs_div, abs_of_pos hhpos, div_le_div_iff₀ hhpos hσ']
      have : |(G - F) (x + h • v) - (G - F) x| ≤ 2 * M := by
        simp only [Pi.sub_apply]
        calc |G (x + h • v) - F (x + h • v) - (G x - F x)|
            ≤ |G (x + h • v) - F (x + h • v)| + |G x - F x| := abs_sub _ _
          _ ≤ 2 * M := by linarith [hM (x + h • v), hM x]
      calc |(G - F) (x + h • v) - (G - F) x| * σ' ≤ 2 * M * σ' :=
            mul_le_mul_of_nonneg_right this hσ'.le
        _ ≤ 2 * M * h := mul_le_mul_of_nonneg_left hh.1.le (by positivity)
    have h1 := sSup_sub_le (f := dirQuot F v x) (g := dirQuot G v x) hne hF1 hG1 hpt
    have h2 := sInf_sub_le (f := dirQuot F v x) (g := dirQuot G v x) hne hF2 hG2 hpt
    refine ⟨h1, h2, ?_⟩
    unfold dirOsc dirSup dirInf
    have e1 := abs_le.1 h1
    have e2 := abs_le.1 h2
    have e3 : 4 * M / σ' = 2 * (2 * M / σ') := by ring
    rw [abs_le, e3]; constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  · unfold dirOsc dirSup dirInf
    rw [not_nonempty_iff_eq_empty.1 hne]
    simp only [Set.image_empty, Real.sSup_empty, Real.sInf_empty, abs_zero, sub_self]
    refine ⟨hc, hc, ?_⟩
    positivity

theorem tendsto_dirQuot {F : Vec d → ℝ} {x : Vec d} (hF : DifferentiableAt ℝ F x) (v : Vec d) :
    Tendsto (dirQuot F v x) (𝓝[>] 0) (𝓝 (fderiv ℝ F x v)) := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h2 : HasDerivAt (fun t : ℝ => F (x + t • v)) (fderiv ℝ F x v) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq 0 (by simpa using hF.hasFDerivAt) h1 (by simp)
  have h3 := h2.tendsto_slope_zero_right
  refine h3.congr fun t => ?_
  simp [dirQuot, div_eq_inv_mul]

theorem dirQuot_mem_Icc {F : Vec d → ℝ} (hF : IsLipFun F) {v : Vec d}
    (hv : vecEuclideanNorm v = 1) (x : Vec d) {σ h : ℝ} (hh : h ∈ Ioc 0 σ) :
    dirInf F v σ 0 x ≤ dirQuot F v x h ∧ dirQuot F v x h ≤ dirSup F v σ 0 x := by
  obtain ⟨hb1, hb2⟩ := bdd_image hF hv x (Ioc_sub (le_refl (0 : ℝ)) (σ := σ))
  exact ⟨csInf_le hb2 ⟨h, hh, rfl⟩, le_csSup hb1 ⟨h, hh, rfl⟩⟩

/-- If `F` is differentiable at `x` then `U_σ F(x) → 0` as
`σ ↓ 0`. -/
theorem dirOsc_tendsto_zero {F : Vec d → ℝ} (hF : IsLipFun F) {v : Vec d}
    (hv : vecEuclideanNorm v = 1) {x : Vec d} (hd : DifferentiableAt ℝ F x) :
    Tendsto (fun σ => dirOsc F v σ 0 x) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hq⟩ := Metric.tendsto_nhdsWithin_nhds.1 (tendsto_dirQuot hd v) (ε / 3)
    (by positivity)
  refine ⟨δ, hδ, fun σ hσ hσδ => ?_⟩
  have hσ0 : 0 < σ := hσ
  have hσδ' : σ < δ := by simpa [abs_of_pos hσ0] using hσδ
  have hbound : ∀ h ∈ Ioc 0 σ, |dirQuot F v x h - fderiv ℝ F x v| < ε / 3 := by
    intro h hh
    have := hq (show h ∈ Ioi (0 : ℝ) from hh.1) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hh.1]; exact lt_of_le_of_lt hh.2 hσδ')
    simpa [Real.dist_eq] using this
  have hne : (Ioc 0 σ).Nonempty := ⟨σ, hσ0, le_rfl⟩
  have hs : dirSup F v σ 0 x ≤ fderiv ℝ F x v + ε / 3 := by
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨h, hh, rfl⟩
    linarith [(abs_lt.1 (hbound h hh)).2]
  have hi : fderiv ℝ F x v - ε / 3 ≤ dirInf F v σ 0 x := by
    refine le_csInf (hne.image _) ?_
    rintro _ ⟨h, hh, rfl⟩
    linarith [(abs_lt.1 (hbound h hh)).1]
  have hnn := dirOsc_nonneg hF hv (σ := σ) (le_refl 0) x
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  unfold dirOsc
  linarith

/-- If `F` is differentiable at `x` and `0 < h ≤ σ` then
`U_σ F(x) ≥ |D_v F(x) - q_F(x, h)|`, with `D_v F(x) = fderiv ℝ F x v`. -/
theorem abs_fderiv_sub_dirQuot_le {F : Vec d → ℝ} (hF : IsLipFun F) {v : Vec d}
    (hv : vecEuclideanNorm v = 1) {x : Vec d} (hd : DifferentiableAt ℝ F x) {σ h : ℝ}
    (hh : 0 < h) (hhσ : h ≤ σ) :
    |fderiv ℝ F x v - dirQuot F v x h| ≤ dirOsc F v σ 0 x := by
  have hσ : 0 < σ := hh.trans_le hhσ
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc 0 σ := Ioc_mem_nhdsGT hσ
  have hup : fderiv ℝ F x v ≤ dirSup F v σ 0 x :=
    le_of_tendsto (tendsto_dirQuot hd v) (hev.mono fun t ht => (dirQuot_mem_Icc hF hv x ht).2)
  have hlow : dirInf F v σ 0 x ≤ fderiv ℝ F x v :=
    ge_of_tendsto (tendsto_dirQuot hd v) (hev.mono fun t ht => (dirQuot_mem_Icc hF hv x ht).1)
  have hq := dirQuot_mem_Icc hF hv x (show h ∈ Ioc 0 σ from ⟨hh, hhσ⟩)
  unfold dirOsc
  rw [abs_le]; constructor <;> linarith [hq.1, hq.2]

/-- Basic properties of the directional oscillation `U_σ` for Lipschitz `F`, `G` and a
unit vector `v`: (a) monotonicity, (b) Lipschitz dependence, (c) the limit `U_σ F(x) → 0` at a
point of differentiability, (d) `U_σ F(x) ≥ |D_v F(x) - q_F(x, h)|` for `0 < h ≤ σ`. -/
theorem lem_U {v : Vec d} (hv : vecEuclideanNorm v = 1) :
    (∀ F, IsLipFun F → ∀ (σ σ' : ℝ), 0 ≤ σ' → ∀ x, dirOsc F v σ σ' x ≤ dirOsc F v σ 0 x) ∧
    (∀ F, IsLipFun F → ∀ x (σ₁ σ₂ : ℝ), σ₁ ≤ σ₂ → dirOsc F v σ₁ 0 x ≤ dirOsc F v σ₂ 0 x) ∧
    (∀ F G, IsLipFun F → IsLipFun G → ∀ (σ σ' : ℝ), 0 < σ' → ∀ M : ℝ, (∀ y, |G y - F y| ≤ M) →
      ∀ x, |dirSup G v σ σ' x - dirSup F v σ σ' x| ≤ 2 * M / σ' ∧
        |dirInf G v σ σ' x - dirInf F v σ σ' x| ≤ 2 * M / σ' ∧
        |dirOsc G v σ σ' x - dirOsc F v σ σ' x| ≤ 4 * M / σ') ∧
    (∀ F, IsLipFun F → ∀ x, DifferentiableAt ℝ F x →
      Tendsto (fun σ => dirOsc F v σ 0 x) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ F, IsLipFun F → ∀ x, DifferentiableAt ℝ F x → ∀ σ h : ℝ, 0 < h → h ≤ σ →
      |fderiv ℝ F x v - dirQuot F v x h| ≤ dirOsc F v σ 0 x) :=
  ⟨fun _ hF _ _ hσ' x => dirOsc_le_dirOsc_zero hF hv hσ' x,
    fun _ hF x _ _ h => dirOsc_zero_mono hF hv x h,
    fun _ _ hF hG _ _ hσ' _ hM x => dirOsc_lipschitz_dependence hF hG hv hσ' hM x,
    fun _ hF _ hd => dirOsc_tendsto_zero hF hv hd,
    fun _ hF _ hd _ _ hh hhσ => abs_fderiv_sub_dirQuot_le hF hv hd hh hhσ⟩

end AFree.Rademacher
