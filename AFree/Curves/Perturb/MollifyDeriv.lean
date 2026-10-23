module

public import AFree.Curves.Perturb.Mollify
public import AFree.Curves.Perturb.Nbhd

/-!
# Derivatives of the mollification of `g`
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

lemma perturb_hasDerivAt_along {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x w : Vec d) :
    HasDerivAt (fun s : ℝ => f (x + s • w)) (fderiv ℝ f x w) 0 := by
  have hdf : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
  have hι : HasDerivAt (fun s : ℝ => x + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have := hdf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hι (by simp)
  exact this

private lemma perturb_norm_add_le3 (x y z : Vec d) :
    vecEuclideanNorm (x + y + z) ≤ vecEuclideanNorm x + vecEuclideanNorm y + vecEuclideanNorm z :=
  (vecEuclideanNorm_add_le _ _).trans (by linarith [vecEuclideanNorm_add_le x y])

/-- `0 ≤ D_e f ≤ 1` everywhere, and `D_e f = 1` on the open
`δ/3`-neighbourhood of `K`, for `f = g * ρ` when `g` has the monotonicity and slope bounds along `e`
with `A` the open `δ`-neighbourhood of `K`, and `supp ρ ⊆ B(δ/3)`. -/
theorem perturb_e_derivative {e : Vec d} (he : vecEuclideanNorm e = 1) {K : Set (Vec d)} {δ : ℝ}
    (hδ : 0 < δ) {g ρ : Vec d → ℝ} {ε : ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x ∧ g x ≤ ε)
    (hmono : ∀ z, ∀ s : ℝ, 0 ≤ s → g z ≤ g (z + s • e) ∧ g (z + s • e) ≤ g z + s)
    (hseg : ∀ z, ∀ s : ℝ, 0 ≤ s → (∀ σ ∈ Icc 0 s, z + σ • e ∈ perturbOpenNbhd K δ) →
      g (z + s • e) = g z + s)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y, ρ y = 1) (hρs : ∀ y, ρ y ≠ 0 → vecEuclideanNorm y ≤ δ / 3) :
    (∀ x, 0 ≤ fderiv ℝ (perturbMollify ρ g) x e ∧ fderiv ℝ (perturbMollify ρ g) x e ≤ 1) ∧
      ∀ x ∈ perturbOpenNbhd K (δ / 3), fderiv ℝ (perturbMollify ρ g) x e = 1 := by
  have hf := (perturb_smooth_bounds hg hg0 hρ hρc hρ0 hρ1).1
  have hslope : ∀ x, Tendsto (fun t : ℝ => t⁻¹ * (perturbMollify ρ g (x + t • e) -
      perturbMollify ρ g x)) (𝓝[>] 0) (𝓝 (fderiv ℝ (perturbMollify ρ g) x e)) := by
    intro x
    have := (perturb_hasDerivAt_along hf x e).tendsto_slope_zero_right
    simpa using this
  refine ⟨fun x => ⟨?_, ?_⟩, fun x hx => ?_⟩
  · refine ge_of_tendsto (hslope x) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have := (perturbMollify_sub_mem hg hρ.continuous hρc hρ0 hρ1 x (t • e) (lo := 0) (hi := t)
      fun y _ => by
        have := hmono (x - y) t (le_of_lt ht)
        exact ⟨by linarith [this.1], by linarith [this.2]⟩).1
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht)) this
  · refine le_of_tendsto (hslope x) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have := (perturbMollify_sub_mem hg hρ.continuous hρc hρ0 hρ1 x (t • e) (lo := 0) (hi := t)
      fun y _ => by
        have := hmono (x - y) t (le_of_lt ht)
        exact ⟨by linarith [this.1], by linarith [this.2]⟩).2
    rw [inv_mul_le_iff₀ ht]; linarith
  · obtain ⟨k, hk, hxk⟩ := hx
    refine tendsto_nhds_unique (hslope x) ((tendsto_const_nhds (x := (1 : ℝ))).congr' ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ / 3 by linarith)] with t ht
    have hdiff : perturbMollify ρ g (x + t • e) - perturbMollify ρ g x = t := by
      have := perturbMollify_sub_mem hg hρ.continuous hρc hρ0 hρ1 x (t • e) (lo := t) (hi := t)
        fun y hy => by
          have hy3 := hρs y hy
          have h1 := hseg (x - y) t ht.1.le fun σ hσ => by
            refine ⟨k, hk, ?_⟩
            have hs : (x - y + σ • e) - k = (x - k) + (-y) + σ • e := by abel
            rw [hs]
            refine (perturb_norm_add_le3 _ _ _).trans_lt ?_
            rw [vecEuclideanNorm_neg, vecEuclideanNorm_smul, he, mul_one, abs_of_nonneg hσ.1]
            linarith [hσ.2, ht.2]
          exact ⟨by linarith, by linarith⟩
      exact le_antisymm this.2 this.1
    rw [hdiff, inv_mul_cancel₀ ht.1.ne']

/-- If `|g(z + v) - g(z)| ≤ |v| / t` for `v ∈ e^⊥`, then the
mollification satisfies `|D_w f(x)| ≤ |w| / t` for `w ∈ e^⊥`, i.e. `|d_W f| ≤ 1/t`. -/
theorem perturb_W_derivative {e : Vec d} {t : ℝ} (ht : 0 < t) {g ρ : Vec d → ℝ} {ε : ℝ}
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x ∧ g x ≤ ε)
    (hW : ∀ z v, vecDot v e = 0 → |g (z + v) - g z| ≤ vecEuclideanNorm v / t)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y, ρ y = 1) :
    ∀ x w, vecDot w e = 0 →
      |fderiv ℝ (perturbMollify ρ g) x w| ≤ (1 / t) * vecEuclideanNorm w := by
  intro x w hw
  have hf := (perturb_smooth_bounds hg hg0 hρ hρc hρ0 hρ1).1
  have hder := perturb_hasDerivAt_along hf x w
  have hC : 0 ≤ (1 / t) * vecEuclideanNorm w := mul_nonneg (by positivity) (vecEuclideanNorm_nonneg w)
  have := hder.le_of_lip' hC (Eventually.of_forall fun h => ?_)
  · simpa using this
  · have hv : vecDot (h • w) e = 0 := by rw [vecDot_smul_left, hw, mul_zero]
    have hb : ∀ y, ρ y ≠ 0 → -(|h| * ((1 / t) * vecEuclideanNorm w)) ≤
        g (x - y + h • w) - g (x - y) ∧ g (x - y + h • w) - g (x - y) ≤
        |h| * ((1 / t) * vecEuclideanNorm w) := by
      intro y _
      have := hW (x - y) (h • w) hv
      rw [vecEuclideanNorm_smul] at this
      have e1 : |h| * vecEuclideanNorm w / t = |h| * ((1 / t) * vecEuclideanNorm w) := by ring
      rw [e1] at this
      exact abs_le.mp this
    have := perturbMollify_sub_mem hg hρ.continuous hρc hρ0 hρ1 x (h • w) hb
    simp only [zero_smul, add_zero, Real.norm_eq_abs, sub_zero]
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]

end AFree
