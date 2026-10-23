module

public import AFree.Harmonic.Kernel.NegativePointwise
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# `L^p` integrability of the negative-order kernel (the kernel estimate in the proof of [DPR, Lemma 2.1])

For `m ∈ S^{-s}`, `s > 0`, the kernel `K = negKernel m` lies in `L^p` for `1 ≤ p < ∞` with
`p (d - s) < d` (all `p` if `s ≥ d`).
-/

@[expose] public section

open MeasureTheory PDE Filter Set
open scoped SchwartzMap ContDiff Topology ENNReal

namespace AFree

noncomputable section

variable {d : ℕ}

/-- Local integrability of `‖x‖^{-γ}` for `γ < d`. -/
theorem integrable_indicator_norm_rpow (hd : 0 < d) {γ : ℝ} (hγ : γ < d) :
    Integrable (fun x : Vec d => (Ioo (0 : ℝ) 1).indicator (fun y => y ^ (-γ)) ‖x‖) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hfin : Module.finrank ℝ (Vec d) = d := by simp [Vec]
  rw [integrable_fun_norm_addHaar (volume : Measure (Vec d)), hfin]
  have h1 : IntegrableOn (fun y : ℝ => y ^ (-γ + ((d : ℝ) - 1))) (Ioo 0 1) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]; linarith
  have h2 : Integrable ((Ioo (0 : ℝ) 1).indicator (fun y : ℝ => y ^ (-γ + ((d : ℝ) - 1)))) :=
    (integrable_indicator_iff measurableSet_Ioo).2 h1
  refine h2.integrableOn.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : 0 < y := hy
  by_cases hy1 : y ∈ Ioo (0 : ℝ) 1
  · simp only [indicator_of_mem hy1, smul_eq_mul]
    rw [Real.rpow_add hy0, ← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one, mul_comm]
  · simp [indicator_of_notMem hy1]

theorem integrable_norm_rpow_negKernel (hd : 0 < d) {s : ℝ} (hs0 : 0 < s) {m : Vec d → ℂ}
    (hm : IsSymbol (-s) m) {p : ℝ} (hp : 1 ≤ p) (hps : p * ((d : ℝ) - s) < d) :
    Integrable (fun x : Vec d => ‖negKernel m x‖ ^ p) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hp0 : 0 < p := by linarith
  set t : ℝ := min s ((d : ℝ) - (d : ℝ) / (2 * p)) with ht
  have hdp : (d : ℝ) / (2 * p) ≤ (d : ℝ) / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hdp0 : 0 < (d : ℝ) / (2 * p) := by positivity
  have ht0 : 0 < t := lt_min hs0 (by linarith)
  have htd : t < d := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hts : t ≤ s := min_le_left _ _
  set γ : ℝ := p * ((d : ℝ) - t) with hγ
  have hγd : γ < d := by
    have : (d : ℝ) - t = max ((d : ℝ) - s) ((d : ℝ) / (2 * p)) := by
      rw [ht, ← max_sub_sub_left]; congr 1; ring
    rw [hγ, this]
    rcases le_total ((d : ℝ) - s) ((d : ℝ) / (2 * p)) with h | h
    · rw [max_eq_right h]
      calc p * ((d : ℝ) / (2 * p)) = d / 2 := by field_simp
        _ < d := by linarith
    · rw [max_eq_left h]; exact hps
  obtain ⟨C1, hC10, hC1⟩ := norm_negKernel_le_of_le ht0 htd hts hm
  set M : ℕ := d + 1 with hM
  obtain ⟨C2, hC20, hC2⟩ := norm_negKernel_le_decay_of_pos hd hs0 hm M
  have hMp : (d : ℝ) < (M : ℝ) * p := by
    rw [hM]; push_cast; nlinarith
  have hK := integrable_negKernel hs0 hm
  set G : Vec d → ℝ := fun x => C1 ^ p * (Ioo (0 : ℝ) 1).indicator (fun y => y ^ (-γ)) ‖x‖ +
    C2 ^ p * 2 ^ ((M : ℝ) * p) * (1 + ‖x‖) ^ (-((M : ℝ) * p)) with hG
  have hGint : Integrable G := by
    refine ((integrable_indicator_norm_rpow hd hγd).const_mul _).add ?_
    have hfin : (Module.finrank ℝ (Vec d) : ℝ) < (M : ℝ) * p := by
      have : Module.finrank ℝ (Vec d) = d := by simp [Vec]
      rw [this]; exact hMp
    exact (integrable_one_add_norm (μ := (volume : Measure (Vec d))) hfin).const_mul _
  refine hGint.mono' ((hK.aestronglyMeasurable.norm.aemeasurable.pow_const p).aestronglyMeasurable)
    ?_
  have hae : ∀ᵐ x : Vec d ∂volume, x ≠ 0 := by
    have : ({0} : Set (Vec d))ᶜ ∈ ae (volume : Measure (Vec d)) :=
      compl_mem_ae_iff.2 (measure_singleton 0)
    exact this
  filter_upwards [hae] with x hx
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hx1 : ‖x‖ < 1
  · have h1 := hC1 x hx
    have h2 : ‖negKernel m x‖ ^ p ≤ (C1 * ‖x‖ ^ (t - (d : ℝ))) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) h1 hp0.le
    have h3 : (C1 * ‖x‖ ^ (t - (d : ℝ))) ^ p = C1 ^ p * ‖x‖ ^ (-γ) := by
      rw [Real.mul_rpow hC10 (by positivity), ← Real.rpow_mul hxn.le]
      congr 2; rw [hγ]; ring
    have h4 : (Ioo (0 : ℝ) 1).indicator (fun y => y ^ (-γ)) ‖x‖ = ‖x‖ ^ (-γ) :=
      indicator_of_mem (show ‖x‖ ∈ Ioo (0 : ℝ) 1 from ⟨hxn, hx1⟩) _
    have h5 : 0 ≤ C2 ^ p * 2 ^ ((M : ℝ) * p) * (1 + ‖x‖) ^ (-((M : ℝ) * p)) := by positivity
    rw [hG]; simp only
    rw [h4]; linarith
  · push Not at hx1
    have h1 := hC2 x hx1
    have hxM : 0 < ‖x‖ ^ M := by positivity
    have h2 : ‖negKernel m x‖ ≤ C2 * (‖x‖ ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hxM, mul_comm]; exact h1
    have h3 : ‖negKernel m x‖ ^ p ≤ (C2 * (‖x‖ ^ M)⁻¹) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) h2 hp0.le
    have h4 : (C2 * (‖x‖ ^ M)⁻¹) ^ p = C2 ^ p * ‖x‖ ^ (-((M : ℝ) * p)) := by
      rw [Real.mul_rpow hC20 (by positivity), Real.inv_rpow hxM.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hxn.le, ← Real.rpow_neg (by positivity)]
    have h5 : ‖x‖ ^ (-((M : ℝ) * p)) ≤ 2 ^ ((M : ℝ) * p) * (1 + ‖x‖) ^ (-((M : ℝ) * p)) := by
      have h6 : (1 + ‖x‖) ≤ 2 * ‖x‖ := by linarith
      have h7 : (2 * ‖x‖) ^ (-((M : ℝ) * p)) ≤ (1 + ‖x‖) ^ (-((M : ℝ) * p)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h6 (by have := hMp; nlinarith)
      rw [Real.mul_rpow (by norm_num) hxn.le, Real.rpow_neg (by norm_num)] at h7
      have h8 : (0 : ℝ) < 2 ^ ((M : ℝ) * p) := by positivity
      have h9 : ‖x‖ ^ (-((M : ℝ) * p)) ≤ 2 ^ ((M : ℝ) * p) * ((1 + ‖x‖) ^ (-((M : ℝ) * p))) := by
        have := mul_le_mul_of_nonneg_left h7 h8.le
        rwa [← mul_assoc, mul_inv_cancel₀ h8.ne', one_mul] at this
      exact h9
    have h10 : 0 ≤ C1 ^ p * (Ioo (0 : ℝ) 1).indicator (fun y => y ^ (-γ)) ‖x‖ := by
      apply mul_nonneg (by positivity)
      by_cases hmem : ‖x‖ ∈ Ioo (0 : ℝ) 1
      · rw [indicator_of_mem hmem]; positivity
      · rw [indicator_of_notMem hmem]
    calc ‖negKernel m x‖ ^ p ≤ C2 ^ p * ‖x‖ ^ (-((M : ℝ) * p)) := h3.trans (le_of_eq h4)
      _ ≤ C2 ^ p * (2 ^ ((M : ℝ) * p) * (1 + ‖x‖) ^ (-((M : ℝ) * p))) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = C2 ^ p * 2 ^ ((M : ℝ) * p) * (1 + ‖x‖) ^ (-((M : ℝ) * p)) := by ring
      _ ≤ G x := by rw [hG]; simp only; linarith

/-- The kernel estimate of the proof of [DPR, Lemma 2.1]: `K ∈ L^p` for `1 ≤ p` with `p (d - s) < d`. -/
theorem memLp_negKernel (hd : 0 < d) {s : ℝ} (hs0 : 0 < s) {m : Vec d → ℂ}
    (hm : IsSymbol (-s) m) {p : ℝ} (hp : 1 ≤ p) (hps : p * ((d : ℝ) - s) < d) :
    MemLp (negKernel m) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have h := integrable_norm_rpow_negKernel hd hs0 hm hp hps
  rw [← integrable_norm_rpow_iff (integrable_negKernel hs0 hm).aestronglyMeasurable
    (by simpa using hp0) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
  exact h

end

end AFree
