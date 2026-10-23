module

public import AFree.Harmonic.Symbol.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Examples of symbols

Polynomials of degree `≤ j` lie in `S^j`; `(1 + q ξ)⁻¹ ∈ S^{-2k}` for an elliptic homogeneous
`q` of degree `2k`; and `(1 + 4π²|ξ|²)^{-s/2} ∈ S^{-s}`.
-/

@[expose] public section

open PDE

namespace AFree

noncomputable section

variable {d : ℕ}

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem SymBound.of_fderiv {s : ℝ} {n : ℕ} {f : Vec d → E}
    (h : SymBound (s - 1) n (fderiv ℝ f)) : SymBound s (n + 1) f := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun ξ => ?_⟩
  rw [← norm_iteratedFDeriv_fderiv]
  convert hC ξ using 3
  push_cast; ring

theorem SymBound.fderiv {s : ℝ} {n : ℕ} {f : Vec d → E}
    (h : SymBound s (n + 1) f) : SymBound (s - 1) n (fderiv ℝ f) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun ξ => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  convert hC ξ using 3
  push_cast; ring

theorem SymBound.congr_exp {s s' : ℝ} (h : s = s') {n : ℕ} {f : Vec d → E} (hf : SymBound s n f) :
    SymBound s' n f := h ▸ hf

theorem SymBound.real_smul (c : ℝ) {s : ℝ} {f : Vec d → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (h : ∀ i ≤ n, SymBound s i f) : SymBound s n (fun ξ => c • f ξ) := by
  have := SymBound.bilin (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) (f := fun _ : Vec d => c) (g := f)
    contDiff_const hf n (fun i _ => SymBound.const c 0 le_rfl i) h
  simpa using this

end

/-! ### Powers of a positive symbol -/

/-- If `w` is a positive real symbol of order `a` bounded below by `c (1 + |ξ|)^a`, then
`w ^ t` is a symbol of order `t a`. -/
theorem symBound_rpow {a : ℝ} {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hpos : ∀ ξ, 0 < w ξ) (hS : ∀ n, SymBound a n w) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ ξ, c * (1 + vecEuclideanNorm ξ) ^ a ≤ w ξ) :
    ∀ (n : ℕ) (t : ℝ), SymBound (t * a) n (fun ξ => w ξ ^ t) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t
  have hsm : ∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun ξ => w ξ ^ t) := fun t =>
    hw.rpow_const_of_ne (fun ξ => (hpos ξ).ne')
  rcases n with _ | n
  · obtain ⟨A, hA0, hA⟩ := (hS 0).nonneg
    refine ⟨if 0 ≤ t then A ^ t else c ^ t, fun ξ => ?_⟩
    have hx := one_add_vecEuclideanNorm_pos ξ
    have hp : 0 ≤ (1 + vecEuclideanNorm ξ) ^ a := Real.rpow_nonneg hx.le _
    have hwx := hpos ξ
    simp only [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hwx t)]
    have hA' : w ξ ≤ A * (1 + vecEuclideanNorm ξ) ^ a := by
      have := hA ξ
      simpa [Real.norm_eq_abs, abs_of_pos hwx] using this
    have key : ((1 + vecEuclideanNorm ξ) ^ a) ^ t = (1 + vecEuclideanNorm ξ) ^ (t * a) := by
      rw [← Real.rpow_mul hx.le, mul_comm]
    split_ifs with ht
    · calc w ξ ^ t ≤ (A * (1 + vecEuclideanNorm ξ) ^ a) ^ t :=
            Real.rpow_le_rpow hwx.le hA' ht
        _ = _ := by rw [Real.mul_rpow hA0 hp, key]
    · have ht' : t ≤ 0 := (not_le.mp ht).le
      have hcp : 0 < c * (1 + vecEuclideanNorm ξ) ^ a :=
        mul_pos hc (Real.rpow_pos_of_pos hx _)
      calc w ξ ^ t ≤ (c * (1 + vecEuclideanNorm ξ) ^ a) ^ t :=
            Real.rpow_le_rpow_of_nonpos hcp (hlow ξ) ht'
        _ = _ := by rw [Real.mul_rpow hc.le hp, key]
  · -- the derivative of `w ^ t`
    have hder : fderiv ℝ (fun ξ => w ξ ^ t) =
        fun ξ => (t * w ξ ^ (t - 1)) • fderiv ℝ w ξ := by
      funext ξ
      exact (hw.differentiable (by simp) ξ |>.hasFDerivAt.rpow_const
        (Or.inl (hpos ξ).ne')).fderiv
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ w) := hw.fderiv_right (by simp)
    have h1 : ∀ i ≤ n, SymBound ((t - 1) * a) i (fun ξ => w ξ ^ (t - 1)) :=
      fun i hi => ih i (by omega) (t - 1)
    have h2 : ∀ i ≤ n, SymBound (a - 1) i (fderiv ℝ w) :=
      fun i _ => (hS (i + 1)).fderiv
    have hf1 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => t * w ξ ^ (t - 1)) :=
      contDiff_const.mul (hsm (t - 1))
    have h1' : ∀ i ≤ n, SymBound ((t - 1) * a) i (fun ξ => t * w ξ ^ (t - 1)) := fun i hi => by
      simpa using SymBound.real_smul t (hsm (t - 1)) i (fun j hj => h1 j (hj.trans hi))
    have h3 := SymBound.bilin (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (Vec d →L[ℝ] ℝ) →L[ℝ] (Vec d →L[ℝ] ℝ))
      hf1 hfd n h1' h2
    apply SymBound.of_fderiv
    rw [hder]
    exact h3.congr_exp (by ring)



end

end AFree
