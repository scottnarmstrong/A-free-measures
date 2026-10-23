module

public import AFree.Harmonic.Kernel.Pieces
public import AFree.Harmonic.Kernel.Scaling

/-!
# `L¹` norms of the dyadic kernels

For `m ∈ S^{-s}` (`s ≥ 0`) the dyadic symbol pieces `m ψ_l` are compactly supported smooth, and
their inverse Fourier transforms `K_l` satisfy `‖K_l‖_{L¹} ≤ C (2^{-s})^l` for `l ≥ 1`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped SchwartzMap ContDiff

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The `l`-th dyadic piece `m(ξ) · ψ_l(ξ)` of the symbol `m`. -/
def lpSym (m : Vec d → ℂ) (l : ℕ) : Vec d → ℂ := fun ξ => m ξ * (lpPiece l ξ : ℂ)

/-- The kernel of the `l`-th dyadic piece. -/
def lpKernel (m : Vec d → ℂ) (l : ℕ) : Vec d → ℂ := vecFourierInv (lpSym m l)

theorem contDiff_lpPiece (l : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (lpPiece (d := d) l) := by
  cases l with
  | zero => exact contDiff_lpPsi0
  | succ l => exact contDiff_lpPsi.comp (contDiff_const_smul _)

theorem hasCompactSupport_lpPiece (l : ℕ) : HasCompactSupport (lpPiece (d := d) l) := by
  cases l with
  | zero => exact hasCompactSupport_euclideanCutoff one_pos one_lt_two
  | succ l =>
    refine (isCompact_vecNormSq_le (d := d) (3 * 2 ^ l)).of_isClosed_subset (isClosed_tsupport _) ?_
    apply closure_minimal
    · intro ξ hξ
      have := (lpPiece_succ_ne_zero hξ).2
      show vecNormSq ξ ≤ (3 * 2 ^ l) ^ 2
      have h2 := vecEuclideanNorm_sq ξ
      nlinarith [vecEuclideanNorm_nonneg ξ]
    · exact isClosed_le contDiff_vecNormSq.continuous continuous_const

theorem contDiff_lpSym {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (l : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (lpSym m l) :=
  hm.mul (Complex.ofRealCLM.contDiff.comp (contDiff_lpPiece l))

theorem hasCompactSupport_lpSym (m : Vec d → ℂ) (l : ℕ) : HasCompactSupport (lpSym m l) := by
  refine (hasCompactSupport_lpPiece (d := d) l).mono ?_
  intro ξ hξ
  simp only [lpSym, Function.mem_support, ne_eq, mul_eq_zero, not_or, Complex.ofReal_eq_zero]
    at hξ
  exact hξ.2

/-- The dyadic symbol piece as a Schwartz function. -/
def lpSymS {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (l : ℕ) : 𝓢(Vec d, ℂ) :=
  (hasCompactSupport_lpSym m l).toSchwartzMap (by exact_mod_cast contDiff_lpSym hm l)

theorem contDiff_lpScaled {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (l : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (lpScaled m l) :=
  (hm.comp (contDiff_const_smul _)).mul contDiff_lpPsiC

theorem hasCompactSupport_lpScaled (m : Vec d → ℂ) (l : ℕ) : HasCompactSupport (lpScaled m l) := by
  refine (hasCompactSupport_lpPsi (d := d)).mono ?_
  intro η hη
  simp only [lpScaled, Function.mem_support, ne_eq, mul_eq_zero, not_or, Complex.ofReal_eq_zero]
    at hη
  exact hη.2

/-- The rescaled piece as a Schwartz function. -/
def lpScaledS {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (l : ℕ) : 𝓢(Vec d, ℂ) :=
  (hasCompactSupport_lpScaled m l).toSchwartzMap (by exact_mod_cast contDiff_lpScaled hm l)

theorem lpSym_succ_eq {m : Vec d → ℂ} (l : ℕ) :
    lpSym m (l + 1) = fun ξ => lpScaled m (l + 1) ((((2 : ℝ)⁻¹) ^ (l + 1)) • ξ) := by
  funext ξ
  simp only [lpSym, lpScaled, lpPiece, smul_smul]
  have : ((2 : ℝ) ^ (l + 1)) * ((2 : ℝ)⁻¹) ^ (l + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
  rw [this, one_smul]

/-- Support of derivatives of the rescaled pieces lies in `|η| ≤ 2`. -/
theorem lpScaled_iteratedFDeriv_ne_zero {m : Vec d → ℂ} {l n : ℕ} {η : Vec d}
    (h : iteratedFDeriv ℝ n (lpScaled m l) η ≠ 0) : vecEuclideanNorm η ≤ 2 := by
  have h1 := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := lpScaled m l) n
    (Function.mem_support.2 h)
  have hsub : tsupport (lpScaled m l) ⊆ tsupport (lpPsi (d := d)) := by
    unfold tsupport
    apply closure_mono
    intro x hx
    simp only [lpScaled, Function.mem_support, ne_eq, mul_eq_zero, not_or,
      Complex.ofReal_eq_zero] at hx
    exact hx.2
  exact (lpPsi_support_subset (hsub h1)).2

/-- Any finite family of Schwartz seminorms of the rescaled pieces decays like `(2^{-s})^l`. -/
theorem lpScaledS_sup_le {s : ℝ} (hs : 0 ≤ s) {m : Vec d → ℂ} (hm : IsSymbol (-s) m)
    (s0 : Finset (ℕ × ℕ)) :
    ∃ S0 : ℝ, 0 ≤ S0 ∧ ∀ l : ℕ,
      (s0.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) (lpScaledS hm.1 l) ≤
        S0 * ((2 : ℝ) ^ (-s)) ^ l := by
  have hB : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (l : ℕ) (η : Vec d),
      ‖iteratedFDeriv ℝ n (lpScaled m l) η‖ ≤ B * ((2 : ℝ) ^ (-s)) ^ l :=
    fun n => lpScaled_iteratedFDeriv_le hs hm n
  choose B hB0 hBb using hB
  set S0 : ℝ := ∑ i ∈ s0, (2 : ℝ) ^ i.1 * B i.2 with hS
  have hS0 : 0 ≤ S0 := Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hB0 _)
  refine ⟨S0, hS0, fun l => ?_⟩
  set ρl : ℝ := ((2 : ℝ) ^ (-s)) ^ l with hρl
  have hρ0 : 0 ≤ ρl := by positivity
  have hsem : ∀ i ∈ s0, (schwartzSeminormFamily ℂ (Vec d) ℂ i) (lpScaledS hm.1 l) ≤
      S0 * ρl := by
    intro i hi
    have h1 : (schwartzSeminormFamily ℂ (Vec d) ℂ i) (lpScaledS hm.1 l) ≤
        (2 : ℝ) ^ i.1 * B i.2 * ρl := by
      show SchwartzMap.seminorm ℂ i.1 i.2 (lpScaledS hm.1 l) ≤ _
      refine SchwartzMap.seminorm_le_bound ℂ i.1 i.2 _ (by have := hB0 i.2; positivity) fun η => ?_
      by_cases hz : iteratedFDeriv ℝ i.2 (lpScaled m l) η = 0
      · have : iteratedFDeriv ℝ i.2 (⇑(lpScaledS hm.1 l)) η = 0 := hz
        rw [this]; simp only [norm_zero, mul_zero]
        have := hB0 i.2; positivity
      · have hη := lpScaled_iteratedFDeriv_ne_zero hz
        have hn : ‖η‖ ≤ 2 := (norm_le_vecEuclideanNorm η).trans hη
        have h2 := hBb i.2 l η
        calc ‖η‖ ^ i.1 * ‖iteratedFDeriv ℝ i.2 (⇑(lpScaledS hm.1 l)) η‖
            ≤ 2 ^ i.1 * (B i.2 * ρl) :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hn _) h2 (norm_nonneg _) (by positivity)
          _ = _ := by ring
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hρ0)
    exact Finset.single_le_sum (f := fun i : ℕ × ℕ => (2 : ℝ) ^ i.1 * B i.2)
      (fun i _ => mul_nonneg (by positivity) (hB0 _)) hi
  exact Seminorm.finset_sup_apply_le (mul_nonneg hS0 hρ0) hsem

/-- The `L¹` norm of the `l`-th dyadic kernel decays like `(2^{-s})^l`. -/
theorem exists_integral_norm_lpKernel_le {s : ℝ} (hs : 0 ≤ s) {m : Vec d → ℂ}
    (hm : IsSymbol (-s) m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℕ, 1 ≤ l →
      ∫ x, ‖lpKernel m l x‖ ≤ C * ((2 : ℝ) ^ (-s)) ^ l := by
  obtain ⟨s0, C0, hC0, hC⟩ := exists_integral_norm_vecFourierInv_le d
  obtain ⟨S0, hS0, hS⟩ := lpScaledS_sup_le hs hm s0
  refine ⟨C0 * S0, mul_nonneg hC0 hS0, fun l hl => ?_⟩
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have hc0 : (((2 : ℝ)⁻¹) ^ (l' + 1)) ≠ 0 := by positivity
  have hsym : lpSym m (l' + 1) =
      fun ξ => (⇑(lpScaledS hm.1 (l' + 1))) ((((2 : ℝ)⁻¹) ^ (l' + 1)) • ξ) := lpSym_succ_eq l'
  calc ∫ x, ‖lpKernel m (l' + 1) x‖
      = ∫ x, ‖vecFourierInv (⇑(lpScaledS hm.1 (l' + 1))) x‖ := by
        unfold lpKernel
        rw [hsym]
        exact integral_norm_vecFourierInv_comp_smul _ hc0
    _ ≤ C0 * (s0.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) (lpScaledS hm.1 (l' + 1)) :=
        hC _
    _ ≤ C0 * (S0 * ((2 : ℝ) ^ (-s)) ^ (l' + 1)) :=
        mul_le_mul_of_nonneg_left (hS _) hC0
    _ = C0 * S0 * ((2 : ℝ) ^ (-s)) ^ (l' + 1) := by ring

end

end AFree
