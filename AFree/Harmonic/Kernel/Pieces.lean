module

public import AFree.Harmonic.Symbol.Members
public import AFree.Harmonic.Symbol.LittlewoodPaley
public import AFree.Harmonic.Kernel.L1Bound

/-!
# Dyadic pieces of a symbol

For `m ∈ S^{-s}` (`s ≥ 0`) and `l ≥ 0`, the rescaled annular piece
`lpScaled m l η = m(2^l η) ψ(η)` has all derivatives bounded by `B · (2^{-s})^l`, uniformly
in `l`; this is the engine of the `L¹` kernel bounds.
-/

@[expose] public section

open MeasureTheory PDE
open scoped SchwartzMap ContDiff

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The rescaled annular piece `η ↦ m(2^l η) ψ(η)`. -/
def lpScaled (m : Vec d → ℂ) (l : ℕ) : Vec d → ℂ :=
  fun η => m (((2 : ℝ) ^ l) • η) * (lpPsi η : ℂ)

theorem contDiff_lpPsiC : ContDiff ℝ (⊤ : ℕ∞) (fun η : Vec d => (lpPsi η : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp contDiff_lpPsi

theorem hasCompactSupport_lpPsi : HasCompactSupport (lpPsi (d := d)) := by
  refine (isCompact_vecNormSq_le (d := d) 2).of_isClosed_subset (isClosed_tsupport _) ?_
  intro ξ hξ
  have := (lpPsi_support_subset hξ).2
  show vecNormSq ξ ≤ 2 ^ 2
  have h2 := vecEuclideanNorm_sq ξ
  nlinarith [vecEuclideanNorm_nonneg ξ]

/-- `ψ` as a complex Schwartz function. -/
def lpPsiS : 𝓢(Vec d, ℂ) := toSchwartzC lpPsi contDiff_lpPsi hasCompactSupport_lpPsi

theorem iteratedFDeriv_lpPsiC_eq_zero {j : ℕ} {η : Vec d} (h : ¬ 1 / 2 ≤ vecEuclideanNorm η) :
    iteratedFDeriv ℝ j (fun η : Vec d => (lpPsi η : ℂ)) η = 0 := by
  by_contra hne
  have h1 := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := fun η : Vec d => (lpPsi η : ℂ)) j
    (Function.mem_support.2 hne)
  have hsub : tsupport (fun η : Vec d => (lpPsi η : ℂ)) ⊆ tsupport lpPsi := by
    unfold tsupport
    apply closure_mono
    intro x hx
    simpa [Function.mem_support] using hx
  exact h (lpPsi_support_subset (hsub h1)).1

theorem rpow_aux {t : ℝ} (ht : 0 < t) {s : ℝ} (i : ℕ) {u : ℝ} (hu : t / 2 ≤ u) (hs : 0 ≤ s) :
    u ^ (-s - (i : ℝ)) * t ^ i ≤ 2 ^ (s + (i : ℝ)) * t ^ (-s) := by
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have h0 : u ^ (-s - (i : ℝ)) ≤ (t / 2) ^ (-s - (i : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hu
      (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg _
          linarith)
  have h1 : (t / 2) ^ (-s - (i : ℝ)) = t ^ (-s - (i : ℝ)) * 2 ^ (s + (i : ℝ)) := by
    rw [div_eq_mul_inv, Real.mul_rpow ht.le (by norm_num), Real.inv_rpow (by norm_num),
      show -s - (i : ℝ) = -(s + i) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      inv_inv]
  have h2 : t ^ (-s - (i : ℝ)) * t ^ i = t ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]; congr 1; ring
  calc u ^ (-s - (i : ℝ)) * t ^ i ≤ (t / 2) ^ (-s - (i : ℝ)) * t ^ i :=
        mul_le_mul_of_nonneg_right h0 (by positivity)
    _ = 2 ^ (s + (i : ℝ)) * (t ^ (-s - (i : ℝ)) * t ^ i) := by rw [h1]; ring
    _ = _ := by rw [h2]

/-- Derivative bounds for the rescaled pieces, uniform in `l`:
`‖D^n (m(2^l ·) ψ)(η)‖ ≤ B (2^{-s})^l`. -/
theorem lpScaled_iteratedFDeriv_le {s : ℝ} (hs : 0 ≤ s) {m : Vec d → ℂ} (hm : IsSymbol (-s) m)
    (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (l : ℕ) (η : Vec d),
      ‖iteratedFDeriv ℝ n (lpScaled m l) η‖ ≤ B * ((2 : ℝ) ^ (-s)) ^ l := by
  have hC : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec d,
      ‖iteratedFDeriv ℝ i m ξ‖ ≤ C * (1 + vecEuclideanNorm ξ) ^ (-s - (i : ℝ)) :=
    fun i => (hm.bound i).nonneg
  choose C hC0 hCb using hC
  set E : ℕ → ℝ := fun j => (SchwartzMap.seminorm ℝ 0 j) (lpPsiS (d := d)) with hE
  have hE0 : ∀ j, 0 ≤ E j := fun j => apply_nonneg _ _
  have hEb : ∀ j (η : Vec d), ‖iteratedFDeriv ℝ j (fun η : Vec d => (lpPsi η : ℂ)) η‖ ≤ E j := by
    intro j η
    have := SchwartzMap.le_seminorm ℝ 0 j (lpPsiS (d := d)) η
    rw [pow_zero, one_mul] at this
    exact this
  refine ⟨‖(ContinuousLinearMap.mul ℝ ℂ)‖ * ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * (C i * 2 ^ (s + (i : ℝ))) * E (n - i),
    mul_nonneg (norm_nonneg (ContinuousLinearMap.mul ℝ ℂ)) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC0 i) (by positivity))) (hE0 _)),
    fun l η => ?_⟩
  set t : ℝ := (2 : ℝ) ^ l with ht
  have htpos : 0 < t := by positivity
  have hρ : ((2 : ℝ) ^ (-s)) ^ l = t ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  rw [hρ]
  let g : Vec d →L[ℝ] Vec d := t • ContinuousLinearMap.id ℝ (Vec d)
  have hg : ‖g‖ ≤ t := by
    refine (norm_smul t _).le.trans ?_
    have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Vec d)
    rw [Real.norm_of_nonneg htpos.le]; nlinarith
  have hA : lpScaled m l = fun η => (ContinuousLinearMap.mul ℝ ℂ) (m (g η))
      ((fun η : Vec d => (lpPsi η : ℂ)) η) := by
    funext η; simp [lpScaled, g, ht]
  have hmsm : ContDiff ℝ (⊤ : ℕ∞) (fun η => m (g η)) := hm.1.comp g.contDiff
  have hle := (ContinuousLinearMap.mul ℝ ℂ).norm_iteratedFDeriv_le_of_bilinear (𝕜 := ℝ)
    (hmsm.of_le (mod_cast le_top)) (contDiff_lpPsiC.of_le (mod_cast le_top)) η (n := n) (N := n)
    le_rfl
  rw [hA]
  refine hle.trans ?_
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_)
    (norm_nonneg (ContinuousLinearMap.mul ℝ ℂ))
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hη : 1 / 2 ≤ vecEuclideanNorm η
  · -- the main case
    have hcomp : ‖iteratedFDeriv ℝ i (fun η => m (g η)) η‖ ≤
        ‖iteratedFDeriv ℝ i m (g η)‖ * t ^ i := by
      have h := g.iteratedFDeriv_comp_right (n := (i : ℕ∞ω)) (hm.1.of_le (mod_cast le_top)) η
        (i := i) le_rfl
      have h' : iteratedFDeriv ℝ i (fun η => m (g η)) η =
          (iteratedFDeriv ℝ i m (g η)).compContinuousLinearMap fun _ => g := h
      rw [h']
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hg i) (norm_nonneg _)
    have hgη : vecEuclideanNorm (g η) = t * vecEuclideanNorm η := by
      simp [g, vecEuclideanNorm_smul, abs_of_pos htpos]
    have hu : t / 2 ≤ 1 + vecEuclideanNorm (g η) := by rw [hgη]; nlinarith
    have h1 := hCb i (g η)
    have h2 := rpow_aux htpos i hu hs
    have h3 : ‖iteratedFDeriv ℝ i (fun η => m (g η)) η‖ ≤ C i * (2 ^ (s + (i : ℝ)) * t ^ (-s)) :=
      hcomp.trans <| by
        calc ‖iteratedFDeriv ℝ i m (g η)‖ * t ^ i
            ≤ (C i * (1 + vecEuclideanNorm (g η)) ^ (-s - (i : ℝ))) * t ^ i :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = C i * ((1 + vecEuclideanNorm (g η)) ^ (-s - (i : ℝ)) * t ^ i) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h2 (hC0 i)
    have h4 := hEb (n - i) η
    have hc : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun η => m (g η)) η‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun η : Vec d => (lpPsi η : ℂ)) η‖
        ≤ (n.choose i : ℝ) * (C i * (2 ^ (s + (i : ℝ)) * t ^ (-s))) * E (n - i) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h3 hc) h4 (norm_nonneg _)
            (mul_nonneg hc (mul_nonneg (hC0 i) (by positivity)))
      _ = _ := by ring
  · rw [iteratedFDeriv_lpPsiC_eq_zero hη]
    simp only [norm_zero, mul_zero]
    have : 0 ≤ (n.choose i : ℝ) * (C i * 2 ^ (s + (i : ℝ))) * E (n - i) * t ^ (-s) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC0 i) (by positivity)))
        (hE0 _) |> fun h => mul_nonneg h (by positivity)
    exact this

end

end AFree
