module

public import AFree.Paper.OrderK.StrongConstancyRep
public import AFree.Paper.OrderK.HarmonicWt0
public import AFree.Paper.OrderK.HarmonicDual

/-!
# The pieces `f_j`: weak-type smallness and distributional smallness

Reality, weak-type smallness and distributional smallness of `f_j`.
-/

@[expose] public section

open MeasureTheory PDE Matrix Filter Topology
open scoped SchwartzMap ComplexConjugate

namespace AFree

noncomputable section

variable {d : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- `Σ_α ‖G^{(α)}‖_{L¹}` with the Euclidean norm on `ℝ^κ`. -/
def sumL1 (k : ℕ) (G : (Fin d → ℕ) → Vec d → κ → ℝ) : ℝ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∫ x, piEuclideanNorm (G α x)

theorem abs_le_piEuclideanNorm (v : κ → ℝ) (c : κ) : |v c| ≤ piEuclideanNorm v := by
  unfold piEuclideanNorm
  apply Real.abs_le_sqrt
  have := Finset.single_le_sum (f := fun i => v i * v i) (fun i _ => mul_self_nonneg _)
    (Finset.mem_univ c)
  simpa [sq] using this

private theorem continuous_piEuclideanNorm_sc : Continuous fun v : κ → ℝ => piEuclideanNorm v := by
  unfold piEuclideanNorm; fun_prop

theorem integrable_piEuclideanNorm {F : Vec d → κ → ℝ} (hF : Continuous F)
    (hc : HasCompactSupport F) : Integrable fun x => piEuclideanNorm (F x) :=
  (continuous_piEuclideanNorm_sc.comp hF).integrable_of_hasCompactSupport
    (hc.comp_left (g := fun v : κ → ℝ => piEuclideanNorm v) (by simp [piEuclideanNorm]))

omit [Fintype κ] in
theorem tsupport_apply_subset (F : Vec d → κ → ℝ) (c : κ) :
    tsupport (fun y => F y c) ⊆ tsupport F := by
  refine closure_mono fun y hy h => hy ?_
  simp [h]

/-- Reality: `f` is real valued. -/
theorem im_fPiece (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) {c0 : ℝ} (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ))
    {G : (Fin d → ℕ) → Vec d → κ → ℝ}
    (hG : ∀ α, ContDiff ℝ (⊤ : ℕ∞) (G α) ∧ HasCompactSupport (G α)) (x : Vec d) :
    (fPiece k A P₀ G x).im = 0 := by
  unfold fPiece
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  obtain ⟨-, -, -, hr⟩ := (lem_symbolsk k A P₀ hc0 hell).2.1 α hα c
  exact im_ccMult_eq_zero (isSymbol_m0Symb k A P₀ hc0 hell hα c) hr
    (isCc_apply_of (hG α).1 (hG α).2 c) x

/-- Weak-type smallness of `f_j`. -/
theorem weakType_fPiece (hd : 0 < d) (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ)
    {c0 : ℝ} (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ G : (Fin d → ℕ) → Vec d → κ → ℝ,
      (∀ α, ContDiff ℝ (⊤ : ℕ∞) (G α) ∧ HasCompactSupport (G α)) →
      (∀ α, tsupport (G α) ⊆ euclideanBall (0 : Vec d) 1) → ∀ lam : ℝ, 0 < lam →
        volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam < ‖fPiece k A P₀ G x‖} ≤
          ENNReal.ofReal (B / lam * sumL1 k G) := by
  classical
  set T := Finset.Nat.antidiagonalTuple d k with hT
  set s : Finset ((Fin d → ℕ) × κ) := T ×ˢ Finset.univ with hs
  have hex : ∀ p : (Fin d → ℕ) × κ, ∃ C : ℝ, p ∈ s → 0 < C ∧
      ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → tsupport f ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ lam : ℝ, 0 < lam → volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
          lam < ‖ccMult (m0Symb k A P₀ p.1 p.2) f x‖} ≤
            ENNReal.ofReal (C / lam * ∫ x, |f x|) := by
    intro p
    by_cases hp : p ∈ s
    · have hα : p.1 ∈ T := (Finset.mem_product.1 hp).1
      obtain ⟨-, -, -, hr⟩ := (lem_symbolsk k A P₀ hc0 hell).2.1 p.1 hα p.2
      obtain ⟨C, hC, -, h⟩ := lem_wt0 hd (isSymbol_m0Symb k A P₀ hc0 hell hα p.2) hr
      exact ⟨C, fun _ => ⟨hC, h⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose C hC using hex
  set Csum : ℝ := ∑ p ∈ s, C p with hCsum
  set N : ℝ := (s.card : ℝ) with hN
  have hCle : ∀ p ∈ s, C p ≤ Csum := fun p hp =>
    Finset.single_le_sum (f := C) (fun q hq => (hC q hq).1.le) hp
  refine ⟨Csum * N * Fintype.card κ, by
    have := Finset.sum_nonneg (fun p hp => (hC p hp).1.le) (s := s) ; positivity, ?_⟩
  intro G hG hGs lam hlam
  by_cases hsn : s.Nonempty
  swap
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.1 hsn
    have h0 : ∀ x, fPiece k A P₀ G x = 0 := fun x => by
      unfold fPiece
      rw [← Finset.sum_product' (f := fun α c => ccMult (m0Symb k A P₀ α c) (fun y => G α y c) x)]
      rw [← hs, this]; simp
    have : {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam < ‖fPiece k A P₀ G x‖} = ∅ := by
      ext x; simp [h0, hlam.le]
    rw [this]; simp
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hsn.card_pos
  set t : (Fin d → ℕ) × κ → Vec d → ℂ := fun p x =>
    ccMult (m0Symb k A P₀ p.1 p.2) (fun y => G p.1 y p.2) x with ht
  have hf : ∀ x, fPiece k A P₀ G x = ∑ p ∈ s, t p x := fun x => by
    unfold fPiece
    rw [hs, Finset.sum_product]
  have hsub : {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam < ‖fPiece k A P₀ G x‖} ⊆
      ⋃ p ∈ s, {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam / N < ‖t p x‖} := by
    rintro x ⟨hx2, hx⟩
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hcon
    have : ‖∑ p ∈ s, t p x‖ ≤ lam := by
      calc ‖∑ p ∈ s, t p x‖ ≤ ∑ p ∈ s, ‖t p x‖ := norm_sum_le _ _
        _ ≤ ∑ p ∈ s, lam / N := Finset.sum_le_sum fun p hp => hcon p hp hx2
        _ = lam := by rw [Finset.sum_const, nsmul_eq_mul, ← hN]; field_simp
    rw [hf] at hx; linarith
  have hpt : ∀ p ∈ s, volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam / N < ‖t p x‖} ≤
      ENNReal.ofReal (C p * N / lam * ∫ x, piEuclideanNorm (G p.1 x)) := by
    intro p hp
    have hα : p.1 ∈ T := (Finset.mem_product.1 hp).1
    have hcc := isCc_apply_of (hG p.1).1 (hG p.1).2 p.2
    have h1 := (hC p hp).2 (fun y => G p.1 y p.2) hcc.1
      ((tsupport_apply_subset (G p.1) p.2).trans (hGs p.1)) (lam / N) (by positivity)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hI : ∫ x, |G p.1 x p.2| ≤ ∫ x, piEuclideanNorm (G p.1 x) := by
      refine integral_mono ?_ (integrable_piEuclideanNorm (hG p.1).1.continuous (hG p.1).2)
        fun x => abs_le_piEuclideanNorm _ _
      exact (hcc.1.continuous.integrable_of_hasCompactSupport hcc.2).abs
    have : C p / (lam / N) = C p * N / lam := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hI (by have := (hC p hp).1; positivity)
  calc volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam < ‖fPiece k A P₀ G x‖}
      ≤ volume (⋃ p ∈ s, {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam / N < ‖t p x‖}) :=
        measure_mono hsub
    _ ≤ ∑ p ∈ s, volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam / N < ‖t p x‖} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ p ∈ s, ENNReal.ofReal (C p * N / lam * ∫ x, piEuclideanNorm (G p.1 x)) :=
        Finset.sum_le_sum hpt
    _ = ENNReal.ofReal (∑ p ∈ s, C p * N / lam * ∫ x, piEuclideanNorm (G p.1 x)) :=
        (ENNReal.ofReal_sum_of_nonneg fun p hp => by
          have := (hC p hp).1
          have : 0 ≤ ∫ x, piEuclideanNorm (G p.1 x) :=
            integral_nonneg fun _ => by unfold piEuclideanNorm; positivity
          positivity).symm
    _ ≤ ENNReal.ofReal (Csum * N * Fintype.card κ / lam * sumL1 k G) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hg : ∀ α, 0 ≤ ∫ x, piEuclideanNorm (G α x) := fun α =>
          integral_nonneg fun _ => by unfold piEuclideanNorm; positivity
        calc ∑ p ∈ s, C p * N / lam * ∫ x, piEuclideanNorm (G p.1 x)
            ≤ ∑ p ∈ s, Csum * N / lam * ∫ x, piEuclideanNorm (G p.1 x) :=
              Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right
                (by gcongr; exact hCle p hp) (hg _)
          _ = Csum * N / lam * (Fintype.card κ * sumL1 k G) := by
              rw [← Finset.mul_sum, hs, Finset.sum_product]
              simp only [hT, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sumL1, ← Finset.mul_sum]
          _ = _ := by ring

/-- Distributional smallness: `|∫ ψ f_j| ≤ B ‖ψ̂‖₁ Σ_α ‖G^{(α)}‖₁`. -/
theorem integral_fPiece_le (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) {c0 : ℝ}
    (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ))
    {ψ : Vec d → ℝ} (hψ : IsCc ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ G : (Fin d → ℕ) → Vec d → κ → ℝ,
      (∀ α, ContDiff ℝ (⊤ : ℕ∞) (G α) ∧ HasCompactSupport (G α)) →
        ‖∫ x, (ψ x : ℂ) * fPiece k A P₀ G x‖ ≤ B * sumL1 k G := by
  classical
  set T := Finset.Nat.antidiagonalTuple d k with hT
  set s : Finset ((Fin d → ℕ) × κ) := T ×ˢ Finset.univ with hs
  have hex : ∀ p : (Fin d → ℕ) × κ, ∃ Ap : ℝ, p ∈ s → 0 ≤ Ap ∧ (∀ ξ, ‖m0Symb k A P₀ p.1 p.2 ξ‖ ≤ Ap) := by
    intro p
    by_cases hp : p ∈ s
    · obtain ⟨Ap, hA0, hA⟩ := (isSymbol_m0Symb k A P₀ hc0 hell (Finset.mem_product.1 hp).1 p.2).exists_norm_le_zero
      exact ⟨Ap, fun _ => ⟨hA0, hA⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose Am hAm using hex
  set Fh : ℝ := ∫ ξ, ‖vecFourier (fun y => (ψ y : ℂ)) ξ‖ with hFh
  have hFh0 : 0 ≤ Fh := integral_nonneg fun _ => norm_nonneg _
  refine ⟨(∑ p ∈ s, Am p) * Fh * Fintype.card κ, mul_nonneg (mul_nonneg
    (Finset.sum_nonneg fun p hp => (hAm p hp).1) hFh0) (Nat.cast_nonneg _), ?_⟩
  intro G hG
  have hcc : ∀ p : (Fin d → ℕ) × κ, IsCc (fun y => G p.1 y p.2) := fun p =>
    isCc_apply_of (hG p.1).1 (hG p.1).2 p.2
  have hint : ∀ p : (Fin d → ℕ) × κ, ∀ m : Vec d → ℂ, Integrable fun x =>
      (ψ x : ℂ) * ccMult m (fun y => G p.1 y p.2) x := fun p m => by
    have hc : Continuous fun x => (ψ x : ℂ) * ccMult m (fun y => G p.1 y p.2) x :=
      (Complex.continuous_ofReal.comp hψ.1.continuous).mul (vecMultiplier m (schw _)).continuous
    refine hc.integrable_of_hasCompactSupport ?_
    exact (hψ.2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_right
  have hsum : ∫ x, (ψ x : ℂ) * fPiece k A P₀ G x =
      ∑ p ∈ s, ∫ x, (ψ x : ℂ) * ccMult (m0Symb k A P₀ p.1 p.2) (fun y => G p.1 y p.2) x := by
    rw [← integral_finsetSum _ fun p _ => hint p _]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    unfold fPiece
    rw [hs, Finset.sum_product, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by rw [Finset.mul_sum]
  have hterm : ∀ p ∈ s, ‖∫ x, (ψ x : ℂ) * ccMult (m0Symb k A P₀ p.1 p.2) (fun y => G p.1 y p.2) x‖ ≤
      Am p * Fh * ∫ x, piEuclideanNorm (G p.1 x) := by
    intro p hp
    obtain ⟨hr1, hr2⟩ := (lem_symbolsk k A P₀ hc0 hell).2.1 p.1 (Finset.mem_product.1 hp).1 p.2 |>.2
    have hd3 := (lem_dual (isSymbol_m0Symb k A P₀ hc0 hell (Finset.mem_product.1 hp).1 p.2)
      (m0Symb_neg k A P₀ (Finset.mem_product.1 hp).1 p.2) (hAm p hp).2 hψ (hcc p)).2.2
    refine hd3.trans ?_
    have hI : ∫ x, |G p.1 x p.2| ≤ ∫ x, piEuclideanNorm (G p.1 x) :=
      integral_mono ((hcc p).1.continuous.integrable_of_hasCompactSupport (hcc p).2).abs
        (integrable_piEuclideanNorm (hG p.1).1.continuous (hG p.1).2)
        fun x => abs_le_piEuclideanNorm _ _
    exact mul_le_mul_of_nonneg_left hI (mul_nonneg (hAm p hp).1 hFh0)
  have hsF : ∀ g : (Fin d → ℕ) → ℝ, ∑ p ∈ s, g p.1 = Fintype.card κ * ∑ α ∈ T, g α := fun g => by
    rw [hs, Finset.sum_product, Finset.mul_sum]
    simp
  rw [hsum]
  calc _ ≤ ∑ p ∈ s, ‖∫ x, (ψ x : ℂ) * ccMult (m0Symb k A P₀ p.1 p.2) (fun y => G p.1 y p.2) x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ s, Am p * Fh * ∫ x, piEuclideanNorm (G p.1 x) := Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ s, ((∑ q ∈ s, Am q) * Fh) * ∫ x, piEuclideanNorm (G p.1 x) :=
        Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := Am)
            (fun q hq => (hAm q hq).1) hp) hFh0)
          (integral_nonneg fun _ => by unfold piEuclideanNorm; positivity)
    _ = ((∑ q ∈ s, Am q) * Fh) * ∑ p ∈ s, ∫ x, piEuclideanNorm (G p.1 x) := by
        rw [← Finset.mul_sum]
    _ = ((∑ q ∈ s, Am q) * Fh) * (Fintype.card κ * sumL1 k G) := by
        rw [hsF (fun α => ∫ x, piEuclideanNorm (G α x))]; rfl
    _ = _ := by ring

end

end AFree
