module

public import AFree.Paper.OrderK.StrongConstancyPieces
public import AFree.Paper.OrderK.StrongConstancyEnd

/-!
# Strong constancy of order `k`

Strong constancy for the cut-off systems of order `k` [DPR, Section 2.3].
-/

@[expose] public section

open MeasureTheory PDE Matrix Filter Topology
open scoped SchwartzMap ComplexConjugate

namespace AFree

noncomputable section

variable {d : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι]

theorem integrable_ccMult (m : Vec d → ℂ) (f : Vec d → ℝ) : Integrable (ccMult m f) :=
  (vecMultiplier m (schw f)).integrable

theorem integrable_hPiece (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (w : Vec d → ℝ)
    (H : (Fin d → ℕ) → Vec d → κ → ℝ) : Integrable (hPiece k A P₀ w H) := by
  unfold hPiece
  refine (integrable_ccMult _ _).add ?_
  refine integrable_finsetSum _ fun h _ => integrable_finsetSum _ fun β _ =>
    integrable_finsetSum _ fun c _ => integrable_ccMult _ _

theorem euclideanBall_one_subset_two : euclideanBall (0 : Vec d) 1 ⊆ euclideanBall (0 : Vec d) 2 := by
  intro x hx
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos, sub_zero] at hx
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt two_pos, sub_zero]
  linarith

/-- Strong constancy of order `k`. Let `d, k ≥ 1`, `A_α ∈ ℝ^{κ×ι}`, `P₀ ∈ ℝ^ι` with
`|𝔸_k(ξ) P₀| ≥ c₀ |ξ|^k`. Let `w_j ≥ 0` (supported in `closed B_{3/4}`), `G_j^{(α)}`, `H_{j,β}`
(supported in `B₁`) be `C_c^∞` and satisfy the cut-off system with
`Σ_α ‖G_j^{(α)}‖₁ → 0`, `sup_j ‖H_{j,β}‖₁ < ∞`, `sup_j ‖w_j‖₁ < ∞`. Then a subsequence of `w_j`
converges in `L¹(ℝ^d)`. -/
theorem prop_sck (hd : 0 < d) {k : ℕ} (hk : 1 ≤ k) (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (P₀ : ι → ℝ) {c0 : ℝ} (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ))
    (w : ℕ → Vec d → ℝ) (G H : ℕ → (Fin d → ℕ) → Vec d → κ → ℝ)
    (hw : ∀ j, IsCc (w j))
    (hG : ∀ j α, ContDiff ℝ (⊤ : ℕ∞) (G j α) ∧ HasCompactSupport (G j α))
    (hH : ∀ j β, ContDiff ℝ (⊤ : ℕ∞) (H j β) ∧ HasCompactSupport (H j β))
    (hw0 : ∀ j x, 0 ≤ w j x)
    (hws : ∀ j, tsupport (w j) ⊆ euclideanClosedBall (0 : Vec d) (3 / 4))
    (hGs : ∀ j α, tsupport (G j α) ⊆ euclideanBall (0 : Vec d) 1)
    (hsys : ∀ j, IsSystemK k A P₀ (w j) (G j) (H j))
    (hGsmall : Tendsto (fun j => sumL1 k (G j)) atTop (𝓝 0))
    (hHb : ∀ h ∈ Finset.range k, ∀ β ∈ Finset.Nat.antidiagonalTuple d h,
      ∃ C : ℝ, ∀ j, ∫ x, piEuclideanNorm (H j β x) ≤ C)
    (hwb : ∃ C : ℝ, ∀ j, ∫ x, |w j x| ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ W : Vec d → ℝ, Integrable W ∧
      Tendsto (fun i => ∫ x, |w (φ i) x - W x|) atTop (𝓝 0) := by
  obtain ⟨⟨hfim, hfa⟩, hpsi, ⟨hhim, φ, hφ, g, hgi, hgt⟩⟩ :=
    cl_pieces hd hk A P₀ hc0 hell w G H hw hG hH hGs hsys hGsmall hHb hwb
  set B1 := euclideanBall (0 : Vec d) 1 with hB1
  set hR : ℕ → Vec d → ℝ := fun n x => (hPiece k A P₀ (w (φ n)) (H (φ n)) x).re with hhR
  set fR : ℕ → Vec d → ℝ := fun j x => (fPiece k A P₀ (G j) x).re with hfR
  have hrel : ∀ j x, w j x - (hPiece k A P₀ (w j) (H j) x).re = fR j x := fun j x => by
    have h := cl_rep k A P₀ hc0 hell (hw j) (hG j) (hH j) (hsys j) x
    have h2 := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.add_re] at h2
    simp only [hfR]; linarith
  have hrel' : ∀ n x, w (φ n) x - hR n x = fR (φ n) x := fun n x => hrel (φ n) x
  refine ⟨φ, hφ, ?_⟩
  refine sc_endgame (ws := fun n => w (φ n)) (hR := hR) (hL := fun x => (g x).re)
    (fun n => (hw (φ n)).1.continuous.integrable_of_hasCompactSupport (hw (φ n)).2)
    (fun n => hw0 (φ n)) (fun n => hws (φ n))
    (fun n => ((integrable_hPiece k A P₀ _ _).re).integrableOn) hgi.re ?_ ?_ ?_
  · refine squeeze_zero (fun n => integral_nonneg fun x => abs_nonneg _) (fun n => ?_) hgt
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
      ((((integrable_hPiece k A P₀ _ _).integrableOn).sub hgi).norm) (Filter.Eventually.of_forall
        fun x => ?_)
    have := Complex.abs_re_le_norm (hPiece k A P₀ (w (φ n)) (H (φ n)) x - g x)
    simpa [hhR] using this
  · intro ψ hψ hψc hψs
    have h1 := (hpsi ψ ⟨hψ, hψc⟩).comp hφ.tendsto_atTop
    have h2 : ∀ n, ∫ x, ψ x * (w (φ n) x - hR n x) =
        (∫ x, (ψ x : ℂ) * fPiece k A P₀ (G (φ n)) x).re := fun n => by
      have : ∫ x, (ψ x : ℂ) * fPiece k A P₀ (G (φ n)) x = ((∫ x, ψ x * fR (φ n) x : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have him := hfim (φ n) x
        apply Complex.ext <;> simp [hfR, him]
      rw [this, Complex.ofReal_re]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hrel'])
    simp only [h2]
    have := (Complex.continuous_re.tendsto 0).comp h1
    rw [Complex.zero_re] at this
    exact this
  · intro l hl
    have h1 := (hfa l hl).comp hφ.tendsto_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le)
      (fun n => measure_mono ?_)
    rintro x ⟨hx, hlt⟩
    refine ⟨euclideanBall_one_subset_two hx, ?_⟩
    have : l < -fR (φ n) x := by
      rw [← hrel' n x] at *
      rcases max_cases (-(w (φ n) x - hR n x)) 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hlt <;>
        linarith [hrel' n x]
    have := Complex.abs_re_le_norm (fPiece k A P₀ (G (φ n)) x)
    have h3 := neg_le_abs (fR (φ n) x)
    simp only [hfR] at *
    linarith

end

end AFree
