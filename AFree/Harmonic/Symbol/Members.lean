module

public import AFree.Harmonic.Symbol.Examples
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Members of the symbol classes

Polynomials, inverses of elliptic homogeneous polynomials, and Bessel potentials.
-/

@[expose] public section

open PDE

namespace AFree

noncomputable section

variable {d : ℕ}

/-- A complex polynomial symbol `ξ ↦ p(ξ)`. -/
def polySymbol (p : MvPolynomial (Fin d) ℂ) : Vec d → ℂ :=
  fun ξ => MvPolynomial.eval (fun i => (ξ i : ℂ)) p

/-- The coordinate function `ξ ↦ ξ_i` is a symbol of order `1`. -/
theorem isSymbol_coord (i : Fin d) : IsSymbol 1 (fun ξ : Vec d => (ξ i : ℂ)) := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec d => (ξ i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)
  refine ⟨hL, fun n => ?_⟩
  rcases n with _ | n
  · refine ⟨1, fun ξ => ?_⟩
    simp only [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero, Real.rpow_one, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_apply_le_vecEuclideanNorm ξ i]
  · apply SymBound.of_fderiv
    have : fderiv ℝ (fun ξ : Vec d => (ξ i : ℂ)) =
        fun _ => (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) := by
      funext ξ
      exact (Complex.ofRealCLM.hasFDerivAt.comp ξ
        (hasFDerivAt_apply i ξ)).fderiv
    rw [this]
    simpa using SymBound.const (d := d) (Complex.ofRealCLM.comp
      (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) 0 le_rfl n

theorem isSymbol_coord_pow (i : Fin d) (k : ℕ) :
    IsSymbol (k : ℝ) (fun ξ : Vec d => (ξ i : ℂ) ^ k) := by
  induction k with
  | zero => simpa using IsSymbol.const (d := d) (1 : ℂ) le_rfl
  | succ k ih =>
    have := ih.mul (isSymbol_coord i)
    simpa [pow_succ] using this

theorem isSymbol_prod_coord_pow (e : Fin d →₀ ℕ) :
    IsSymbol ((e.sum fun _ k => k : ℕ) : ℝ) (fun ξ : Vec d => e.prod fun i k => (ξ i : ℂ) ^ k) := by
  classical
  have key : ∀ t : Finset (Fin d), IsSymbol ((∑ i ∈ t, e i : ℕ) : ℝ)
      (fun ξ : Vec d => ∏ i ∈ t, (ξ i : ℂ) ^ e i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using IsSymbol.const (d := d) (1 : ℂ) le_rfl
    | insert a t ha ih =>
      have := (isSymbol_coord_pow (d := d) a (e a)).mul ih
      simpa [Finset.sum_insert ha, Finset.prod_insert ha, Nat.cast_add] using this
  simpa [Finsupp.prod, Finsupp.sum] using key e.support

/-- Polynomials of degree `≤ j` are symbols of order `j`. -/
theorem isSymbol_polySymbol (p : MvPolynomial (Fin d) ℂ) {j : ℕ} (hj : p.totalDegree ≤ j) :
    IsSymbol (j : ℝ) (polySymbol p) := by
  classical
  have hp : polySymbol p = fun ξ : Vec d => ∑ v ∈ p.support,
      p.coeff v * v.prod fun i k => (ξ i : ℂ) ^ k := by
    funext ξ
    have h := congrArg (MvPolynomial.eval fun i => (ξ i : ℂ)) (MvPolynomial.as_sum p)
    simp only [map_sum, MvPolynomial.eval_monomial] at h
    exact h
  rw [hp]
  refine IsSymbol.sum _ fun v hv => ?_
  have := (isSymbol_prod_coord_pow v).smul (p.coeff v)
  refine IsSymbol.mono ?_ this
  exact_mod_cast (MvPolynomial.le_totalDegree hv).trans hj

/-! ### Reduction from real to complex symbols -/

theorem SymBound.ofReal_iff {s : ℝ} {n : ℕ} {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    SymBound s n (fun ξ => (w ξ : ℂ)) ↔ SymBound s n w := by
  have h : ∀ ξ, ‖iteratedFDeriv ℝ n (fun ξ => (w ξ : ℂ)) ξ‖ = ‖iteratedFDeriv ℝ n w ξ‖ := by
    intro ξ
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left (f := w) (n := (⊤ : ℕ∞))
      hw.contDiffAt (mod_cast le_top)
  unfold SymBound
  simp only [h]

/-- The positive-power lemma packaged for complex symbols. -/
theorem isSymbol_rpow {a : ℝ} {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hpos : ∀ ξ, 0 < w ξ) (hS : IsSymbol a (fun ξ => (w ξ : ℂ))) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ ξ, c * (1 + vecEuclideanNorm ξ) ^ a ≤ w ξ) (t : ℝ) :
    IsSymbol (t * a) (fun ξ => ((w ξ ^ t : ℝ) : ℂ)) := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => w ξ ^ t) :=
    hw.rpow_const_of_ne (fun ξ => (hpos ξ).ne')
  refine ⟨Complex.ofRealCLM.contDiff.comp hsm, fun n => ?_⟩
  exact (SymBound.ofReal_iff hsm).2
    (symBound_rpow hw hpos (fun n => (SymBound.ofReal_iff hw).1 (hS.bound n)) hc hlow n t)

theorem eval_ofReal_polySymbol (q : MvPolynomial (Fin d) ℝ) (ξ : Vec d) :
    polySymbol (MvPolynomial.map Complex.ofRealHom q) ξ = ((MvPolynomial.eval ξ q : ℝ) : ℂ) := by
  unfold polySymbol
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- `(1 + q ξ)⁻¹ ∈ S^{-2k}` for a real homogeneous polynomial `q` of degree `2k` with
`q ξ ≥ c |ξ|^{2k}`. -/
theorem isSymbol_inv_one_add (q : MvPolynomial (Fin d) ℝ) {k : ℕ}
    (hq : q.IsHomogeneous (2 * k)) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ ξ : Vec d, c * vecEuclideanNorm ξ ^ (2 * k) ≤ MvPolynomial.eval ξ q) :
    IsSymbol (-(2 * k : ℝ)) (fun ξ : Vec d => (1 + (MvPolynomial.eval ξ q : ℂ))⁻¹) := by
  set w : Vec d → ℝ := fun ξ => 1 + MvPolynomial.eval ξ q with hwdef
  have hwC : (fun ξ => (w ξ : ℂ)) =
      fun ξ => 1 + polySymbol (MvPolynomial.map Complex.ofRealHom q) ξ := by
    funext ξ; simp [hwdef, eval_ofReal_polySymbol]
  have hS : IsSymbol (2 * k : ℝ) (fun ξ => (w ξ : ℂ)) := by
    rw [hwC]
    have h1 : IsSymbol ((2 * k : ℕ) : ℝ) (polySymbol (MvPolynomial.map Complex.ofRealHom q)) :=
      isSymbol_polySymbol _ (hq.map Complex.ofRealHom).totalDegree_le
    have h0 : IsSymbol ((2 * k : ℕ) : ℝ) (fun _ : Vec d => (1 : ℂ)) :=
      IsSymbol.const _ (Nat.cast_nonneg _)
    push_cast at h1 h0
    exact h0.add h1
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := by
    have h2 := Complex.reCLM.contDiff.comp hS.1
    simpa [Function.comp_def] using h2
  have hpos : ∀ ξ, 0 < w ξ := fun ξ => by
    have h1 := hlow ξ
    have h2 : 0 ≤ vecEuclideanNorm ξ ^ (2 * k) := pow_nonneg (vecEuclideanNorm_nonneg ξ) _
    simp only [hwdef]; nlinarith
  have hc' : 0 < min 1 c / 2 ^ (2 * k) := by positivity
  have hlow' : ∀ ξ, min 1 c / 2 ^ (2 * k) * (1 + vecEuclideanNorm ξ) ^ (2 * (k : ℝ)) ≤ w ξ := by
    intro ξ
    set r := vecEuclideanNorm ξ with hr
    have hr0 : 0 ≤ r := vecEuclideanNorm_nonneg ξ
    have e : (1 + r) ^ (2 * (k : ℝ)) = (1 + r) ^ (2 * k) := by
      rw [← Real.rpow_natCast]; push_cast; rfl
    rw [e]
    have hm1 : min 1 c ≤ 1 := min_le_left _ _
    have hm2 : min 1 c ≤ c := min_le_right _ _
    have hmp : 0 < min 1 c := lt_min one_pos hc
    -- (1 + r)^(2k) ≤ 2^(2k) * (1 + r^(2k))
    have hb : (1 + r) ^ (2 * k) ≤ 2 ^ (2 * k) * (1 + r ^ (2 * k)) := by
      rcases le_total r 1 with h | h
      · calc (1 + r) ^ (2 * k) ≤ 2 ^ (2 * k) := pow_le_pow_left₀ (by linarith) (by linarith) _
          _ ≤ _ := by
            have : 0 ≤ r ^ (2 * k) := pow_nonneg hr0 _
            nlinarith [pow_pos (two_pos : (0:ℝ) < 2) (2 * k)]
      · calc (1 + r) ^ (2 * k) ≤ (2 * r) ^ (2 * k) := pow_le_pow_left₀ (by linarith) (by linarith) _
          _ = 2 ^ (2 * k) * r ^ (2 * k) := by rw [mul_pow]
          _ ≤ _ := by
            have : 0 < r ^ (2 * k) := by positivity
            nlinarith [pow_pos (two_pos : (0:ℝ) < 2) (2 * k)]
    have h2k : (0 : ℝ) < 2 ^ (2 * k) := by positivity
    have hq := hlow ξ
    have hrk : 0 ≤ r ^ (2 * k) := pow_nonneg hr0 _
    rw [div_mul_eq_mul_div, div_le_iff₀ h2k]
    simp only [hwdef]
    nlinarith [mul_le_mul_of_nonneg_left hb hmp.le, mul_nonneg hmp.le hrk,
      mul_le_mul_of_nonneg_right hm2 hrk]
  have := isSymbol_rpow hw hpos hS hc' hlow' (-1)
  have e : (fun ξ => ((w ξ ^ (-1 : ℝ) : ℝ) : ℂ)) =
      fun ξ : Vec d => (1 + (MvPolynomial.eval ξ q : ℂ))⁻¹ := by
    funext ξ; simp [hwdef, Real.rpow_neg_one]
  rw [e] at this
  have e2 : (-1 * (2 * (k : ℝ))) = -(2 * k) := by ring
  rwa [e2] at this

/-- The Bessel symbol `(1 + 4π²|ξ|²)^{-s/2}` as a complex function. -/
def besselSymbol (s : ℝ) : Vec d → ℂ :=
  fun ξ => (((1 + 4 * Real.pi ^ 2 * vecEuclideanNorm ξ ^ 2) ^ (-s / 2) : ℝ) : ℂ)

/-- `(1 + 4π²|ξ|²)^{-s/2} ∈ S^{-s}` for real `s`. -/
theorem isSymbol_besselSymbol (s : ℝ) : IsSymbol (-s) (besselSymbol (d := d) s) := by
  set w : Vec d → ℝ := fun ξ => 1 + 4 * Real.pi ^ 2 * vecNormSq ξ with hwdef
  have hwr : ∀ ξ : Vec d, w ξ = 1 + 4 * Real.pi ^ 2 * vecEuclideanNorm ξ ^ 2 := fun ξ => by
    simp [hwdef, vecEuclideanNorm_sq]
  have hwC : (fun ξ => (w ξ : ℂ)) = fun ξ : Vec d =>
      1 + (4 * (Real.pi : ℂ) ^ 2) * ∑ i : Fin d, (ξ i : ℂ) * (ξ i : ℂ) := by
    funext ξ
    simp [hwdef, vecNormSq_eq_sum_sq, sq]
  have hS : IsSymbol 2 (fun ξ => (w ξ : ℂ)) := by
    rw [hwC]
    have h0 : IsSymbol 2 (fun _ : Vec d => (1 : ℂ)) := IsSymbol.const _ (by norm_num)
    have h1 : IsSymbol (1 + 1) (fun ξ : Vec d => ∑ i : Fin d, (ξ i : ℂ) * (ξ i : ℂ)) :=
      IsSymbol.sum _ fun i _ => (isSymbol_coord i).mul (isSymbol_coord i)
    have h2 := h1.smul (4 * (Real.pi : ℂ) ^ 2)
    norm_num at h2
    exact h0.add h2
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := by
    have h2 := Complex.reCLM.contDiff.comp hS.1
    simpa [Function.comp_def] using h2
  have hpos : ∀ ξ, 0 < w ξ := fun ξ => by
    rw [hwr]; have := sq_nonneg (vecEuclideanNorm ξ); positivity
  have hlow : ∀ ξ, (1 / 2 : ℝ) * (1 + vecEuclideanNorm ξ) ^ (2 : ℝ) ≤ w ξ := by
    intro ξ
    rw [hwr, Real.rpow_two]
    have hπ : 3 < Real.pi := Real.pi_gt_three
    have h0 := vecEuclideanNorm_nonneg ξ
    nlinarith [sq_nonneg (vecEuclideanNorm ξ - 1), sq_nonneg (vecEuclideanNorm ξ),
      mul_nonneg (sq_nonneg (vecEuclideanNorm ξ)) (sub_nonneg.2 (le_of_lt (show (1:ℝ) < 4 * Real.pi ^ 2 by nlinarith)))]
  have := isSymbol_rpow hw hpos hS (by norm_num) hlow (-s / 2)
  have e : (fun ξ => ((w ξ ^ (-s / 2) : ℝ) : ℂ)) = besselSymbol (d := d) s := by
    funext ξ; simp [besselSymbol, hwr]
  rw [e] at this
  have e2 : (-s / 2 * 2) = -s := by ring
  rwa [e2] at this

end

end AFree
