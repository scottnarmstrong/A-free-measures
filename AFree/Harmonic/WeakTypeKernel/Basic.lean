module

public import PDEFoundation.Analysis.Newtonian.WeakType.AssemblyFinal
public import PDEFoundation.Analysis.Newtonian.WeakType.MollifyConverge
public import Mathlib.Analysis.Convolution

/-!
# Convolution with an integrable kernel: basic estimates

For a continuous integrable kernel `K` and a continuous compactly supported `g`, the convolution
`x ↦ ∫ K (x - y) * g y` is bounded and integrable, hence square integrable, and its
distribution function is controlled by Chebyshev.
-/

@[expose] public section

open MeasureTheory Set Filter PDE PDE.NewtonWeakType
open scoped ENNReal Topology Convolution

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The convolution `x ↦ ∫ K (x - y) * F y i` of a kernel with the `i`-th coordinate of a field. -/
def kconv (K : Vec d → ℝ) (i : Fin d) (F : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∫ y, K (x - y) * F y i

theorem integrable_kernel_mul {K : Vec d → ℝ} (hKi : Integrable K) {g : Vec d → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (x : Vec d) :
    Integrable (fun y => K (x - y) * g y) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have h1 : Integrable (fun y => K (x - y)) := hKi.comp_sub_left x
  exact h1.mul_bdd hg.aestronglyMeasurable (c := C) (Eventually.of_forall hC)

theorem kconv_eq_convolution {K : Vec d → ℝ} (g : Vec d → ℝ) (x : Vec d) :
    ∫ y, K (x - y) * g y = (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] K) x := by
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)

theorem abs_integral_kernel_mul_le {K : Vec d → ℝ} (hKi : Integrable K) {g : Vec d → ℝ}
    {C : ℝ} (hC : ∀ y, |g y| ≤ C) (x : Vec d) :
    |∫ y, K (x - y) * g y| ≤ C * ∫ y, |K y| := by
  have h1 : Integrable (fun y => |K (x - y)|) := (hKi.comp_sub_left x).abs
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  calc |∫ y, K (x - y) * g y| ≤ ∫ y, |K (x - y) * g y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, C * |K (x - y)| := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (h1.const_mul C) (Eventually.of_forall fun y => ?_)
        show |K (x - y) * g y| ≤ C * |K (x - y)|
        rw [abs_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hC y) (abs_nonneg _)
    _ = C * ∫ y, |K y| := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (fun y => |K y|) volume x

theorem integrable_integral_kernel_mul {K : Vec d → ℝ} (hKi : Integrable K) {g : Vec d → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => ∫ y, K (x - y) * g y) := by
  have := (hg.integrable_of_hasCompactSupport hgc).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) hKi
  exact this.congr (Eventually.of_forall fun x => (kconv_eq_convolution g x).symm)

/-- Chebyshev for the convolution of an integrable continuous kernel with a test function. -/
theorem volume_lt_abs_integral_kernel_mul_le {K : Vec d → ℝ}
    (hKi : Integrable K) {g : Vec d → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {c : ℝ} (hc : 0 < c) :
    volume {x | c < |∫ y, K (x - y) * g y|} ≤
      ENNReal.ofReal (c⁻¹ ^ 2 * ∫ x, (∫ y, K (x - y) * g y) ^ 2) := by
  set h : Vec d → ℝ := fun x => ∫ y, K (x - y) * g y with hh
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hC' : ∀ y, |g y| ≤ C := fun y => by simpa using hC y
  have hint : Integrable h := integrable_integral_kernel_mul hKi hg hgc
  have hmeas : AEStronglyMeasurable h volume := hint.aestronglyMeasurable
  have hbd : ∀ x, |h x| ≤ C * ∫ y, |K y| := abs_integral_kernel_mul_le hKi hC'
  have hsq : Integrable (fun x => h x ^ 2) := by
    refine (hint.abs.const_mul (C * ∫ y, |K y|)).mono' (hmeas.pow 2)
      (Eventually.of_forall fun x => ?_)
    have e : h x ^ 2 = |h x| * |h x| := by rw [abs_mul_abs_self, sq]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), e]
    exact mul_le_mul_of_nonneg_right (hbd x) (abs_nonneg _)
  have hcs : 0 < c ^ 2 := by positivity
  have hcheb := mul_meas_ge_le_integral_of_nonneg (μ := volume)
    (Eventually.of_forall fun x => sq_nonneg (h x)) hsq (c ^ 2)
  have hsub : {x | c < |h x|} ⊆ {x | c ^ 2 ≤ h x ^ 2} := fun x hx => by
    have : c ^ 2 ≤ |h x| ^ 2 := pow_le_pow_left₀ hc.le (le_of_lt hx) 2
    simpa using this
  refine (measure_mono hsub).trans ?_
  have hfin : volume {x | c ^ 2 ≤ h x ^ 2} ≠ ⊤ := by
    have := hsq.measure_ge_lt_top hcs
    refine (lt_of_le_of_lt (measure_mono ?_) this).ne
    intro x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (h x))] using hx
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  have := hcheb
  simp only [Measure.real] at this
  rw [inv_pow, inv_mul_eq_div, le_div_iff₀ hcs, mul_comm]
  exact this

end

end AFree
