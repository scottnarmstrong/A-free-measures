module

public import AFree.MetricCurrents.AKTaylorFreeze

/-!
# Taylor lemma, Step 3: the multilinear expansion and the per-cube estimate
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.AKTaylor

open PDE AFree

variable {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ} {π : Fin k → Vec d → ℝ}
  {ψ : Fin k → Vec k → ℝ} {Λ M : ℝ≥0} {μ : Measure (Vec d)}

/-- The constant `C₃ = 2^k Λ ((M+1)Λ)^{k-1}` of the per-cube estimate. -/
noncomputable def cubeConst (k : ℕ) (Λ M : ℝ≥0) : ℝ :=
  2 ^ k * (Λ : ℝ) * (((M : ℝ) + 1) * Λ) ^ (k - 1)

/-- Step 3. On a cube with `δ`-oscillation of `Dψ` (`δ ≤ 1`),
if `T(f, Aπ) = det A · T(f, π)` for `A = Dψ(c)`, then
`|T(f, τ) - det Dψ(c) · T(f, π)| ≤ C₃ δ ∫ |f| dμ_T`. -/
theorem multilinear_expansion (cx : Ctx T π ψ Λ M μ) {δ : ℝ≥0} (hδ1 : δ ≤ 1) {c : Vec k} {w : ℝ}
    (hw : 0 ≤ w)
    (hδ : ∀ z, ‖z - c‖ ≤ w → ∀ i, ‖fderiv ℝ (ψ i) z - fderiv ℝ (ψ i) c‖ ≤ δ)
    {f : Vec d → ℝ} (hf : IsBddLipFun f)
    (hlin : T f (matAct (jacMat ψ c) π) = (jacMat ψ c).det * T f π) :
    |T f (tauTuple ψ π c w) - (jacMat ψ c).det * T f π| ≤ cubeConst k Λ M * δ * ∫ x, |f x| ∂μ := by
  classical
  set a : Fin k → Vec d → ℝ := matAct (jacMat ψ c) π with ha
  set b : Fin k → Vec d → ℝ := fun i x => eTil ψ i c w (evalTuple π x) with hb
  have haL : ∀ i, IsEuclLipschitzWith (M * Λ) (a i) := fun i => by
    have := lip_comp cx.hπ (fun y => fderiv ℝ (ψ i) c y) M fun y y' => by
      have h1 := (fderiv ℝ (ψ i) c).le_opNorm (y - y')
      rw [map_sub] at h1
      simp only [Real.norm_eq_abs] at h1
      nlinarith [norm_nonneg (y - y'), cx.hM i c]
    intro x y
    have h := this x y
    simpa [ha, matAct_jacMat] using h
  have hbL : ∀ i, IsEuclLipschitzWith (δ * Λ) (b i) := fun i =>
    lip_comp cx.hπ (eTil ψ i c w) δ (eTil_lip cx hw hδ i)
  have haT : IsLipTuple a := fun i => ⟨_, haL i⟩
  have hbT : IsLipTuple b := fun i => ⟨_, hbL i⟩
  have hab : IsLipTuple (fun i x => a i x + b i x) := fun i => isLipFun_add (haT i) (hbT i)
  have htau : tauTuple ψ π c w = fun i x => (a i x + b i x) + (ψ i c - fderiv ℝ (ψ i) c c) := by
    funext i x
    simp [tauTuple, ha, hb, matAct_jacMat]
  have h1 : T f (tauTuple ψ π c w) =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        T f (fun i => if i ∈ S then b i else a i) := by
    rw [htau, T_add_const cx.hT hf hab, T_expand cx.hT hf haT hbT]
  have h0mem : (∅ : Finset (Fin k)) ∈ (Finset.univ : Finset (Fin k)).powerset :=
    Finset.empty_mem_powerset _
  have hempty : T f (fun i => if i ∈ (∅ : Finset (Fin k)) then b i else a i) =
      (jacMat ψ c).det * T f π := by
    simpa using hlin
  have hsplit := Finset.add_sum_erase _ (fun S => T f (fun i => if i ∈ S then b i else a i)) h0mem
  rw [hempty] at hsplit
  have hdiff : T f (tauTuple ψ π c w) - (jacMat ψ c).det * T f π =
      ∑ S ∈ ((Finset.univ : Finset (Fin k)).powerset).erase ∅,
        T f (fun i => if i ∈ S then b i else a i) := by
    rw [h1, ← hsplit]; ring
  -- bound for one nonempty `S`
  have hterm : ∀ S ∈ ((Finset.univ : Finset (Fin k)).powerset).erase ∅,
      |T f (fun i => if i ∈ S then b i else a i)| ≤
        (δ * Λ) * (((M + 1 : ℝ≥0) * Λ : ℝ≥0) : ℝ) ^ (k - 1) * ∫ x, |f x| ∂μ := by
    intro S hS
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hS)
    obtain ⟨i0, hi0⟩ := hSne
    set K : Fin k → ℝ≥0 := fun i => if i ∈ S then δ * Λ else M * Λ with hK
    have hKl : ∀ i, IsEuclLipschitzWith (K i) ((fun i => if i ∈ S then b i else a i) i) := by
      intro i
      by_cases hi : i ∈ S
      · simpa [hK, hi] using hbL i
      · simpa [hK, hi] using haL i
    have hmain := cx.hμ.1.2 f hf _ K hKl
    have hKle : ∀ i, (K i : ℝ) ≤ (((M + 1 : ℝ≥0) * Λ : ℝ≥0) : ℝ) := by
      intro i
      have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
      have hΛ0 := Λ.coe_nonneg
      by_cases hi : i ∈ S
      · simp only [hK, hi, ite_true, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one]
        nlinarith [M.coe_nonneg]
      · simp only [hK, hi, ite_false, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one]
        nlinarith [M.coe_nonneg]
    have hprod : (∏ i, (K i : ℝ)) ≤ (δ * Λ) * (((M + 1 : ℝ≥0) * Λ : ℝ≥0) : ℝ) ^ (k - 1) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => (K i : ℝ)) (Finset.mem_univ i0)]
      have hKi0 : (K i0 : ℝ) = δ * Λ := by simp [hK, hi0]
      rw [hKi0]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ∏ i ∈ Finset.univ.erase i0, (K i : ℝ)
          ≤ ∏ _i ∈ Finset.univ.erase i0, (((M + 1 : ℝ≥0) * Λ : ℝ≥0) : ℝ) :=
            Finset.prod_le_prod₀ (fun i _ => (K i).coe_nonneg) (fun i _ => hKle i)
        _ = _ := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _)]
            simp
    have hint : 0 ≤ ∫ x, |f x| ∂μ := integral_nonneg fun x => abs_nonneg _
    exact hmain.trans (mul_le_mul_of_nonneg_right hprod hint)
  rw [hdiff]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  have hcard : (((Finset.univ : Finset (Fin k)).powerset.erase ∅).card : ℝ) ≤ 2 ^ k := by
    have : ((Finset.univ : Finset (Fin k)).powerset.erase ∅).card ≤ 2 ^ k := by
      calc _ ≤ ((Finset.univ : Finset (Fin k)).powerset).card := Finset.card_erase_le
        _ = 2 ^ k := by simp
    exact_mod_cast this
  have hnn : 0 ≤ (δ * Λ : ℝ) * (((M + 1 : ℝ≥0) * Λ : ℝ≥0) : ℝ) ^ (k - 1) *
      ∫ x, |f x| ∂μ :=
    mul_nonneg (by positivity) (integral_nonneg fun x => abs_nonneg _)
  rw [nsmul_eq_mul]
  calc _ ≤ (2 : ℝ) ^ k * ((δ * Λ : ℝ) * (((M + 1 : ℝ≥0) * Λ : ℝ≥0) : ℝ) ^ (k - 1) *
        ∫ x, |f x| ∂μ) := mul_le_mul_of_nonneg_right hcard hnn
    _ = _ := by
      unfold cubeConst
      push_cast
      ring

end AFree.MetricCurrents.AKTaylor
