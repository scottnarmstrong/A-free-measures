module

public import AFree.Paper.OrderK.StrongConstancyPiecesC

/-!
# Properties of the pieces `f_j` and `h_j`

Smallness and compactness of the two pieces of the Fourier decomposition.
-/

@[expose] public section

open MeasureTheory PDE Matrix Filter Topology
open scoped SchwartzMap ComplexConjugate

namespace AFree

noncomputable section

variable {d : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- Properties of the pieces: (a) `f_j` is real and `|{x ∈ B₂ : |f_j| > λ}| → 0`;
(b) `∫ ψ f_j → 0` for real `ψ ∈ C_c^∞`; (c) `h_j` is real and a subsequence converges in
`L¹(B₁)`. -/
theorem cl_pieces (hd : 0 < d) {k : ℕ} (hk : 1 ≤ k) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ)
    {c0 : ℝ} (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ))
    (w : ℕ → Vec d → ℝ) (G H : ℕ → (Fin d → ℕ) → Vec d → κ → ℝ) (hw : ∀ j, IsCc (w j))
    (hG : ∀ j α, ContDiff ℝ (⊤ : ℕ∞) (G j α) ∧ HasCompactSupport (G j α))
    (hH : ∀ j β, ContDiff ℝ (⊤ : ℕ∞) (H j β) ∧ HasCompactSupport (H j β))
    (hGs : ∀ j α, tsupport (G j α) ⊆ euclideanBall (0 : Vec d) 1)
    (hsys : ∀ j, IsSystemK k A P₀ (w j) (G j) (H j))
    (hGsmall : Tendsto (fun j => sumL1 k (G j)) atTop (𝓝 0))
    (hHb : ∀ h ∈ Finset.range k, ∀ β ∈ Finset.Nat.antidiagonalTuple d h,
      ∃ C : ℝ, ∀ j, ∫ x, piEuclideanNorm (H j β x) ≤ C)
    (hwb : ∃ C : ℝ, ∀ j, ∫ x, |w j x| ≤ C) :
    ((∀ j x, (fPiece k A P₀ (G j) x).im = 0) ∧ ∀ lam : ℝ, 0 < lam →
      Tendsto (fun j => volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
        lam < ‖fPiece k A P₀ (G j) x‖}) atTop (𝓝 0)) ∧
    (∀ ψ : Vec d → ℝ, IsCc ψ →
      Tendsto (fun j => ∫ x, (ψ x : ℂ) * fPiece k A P₀ (G j) x) atTop (𝓝 0)) ∧
    ((∀ j x, (hPiece k A P₀ (w j) (H j) x).im = 0) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : Vec d → ℂ, IntegrableOn g (euclideanBall (0 : Vec d) 1) ∧
      Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) 1,
        ‖hPiece k A P₀ (w (φ n)) (H (φ n)) x - g x‖) atTop (𝓝 0)) := by
  refine ⟨⟨fun j x => im_fPiece k A P₀ hc0 hell (hG j) x, fun lam hlam => ?_⟩,
    fun ψ hψ => ?_, ⟨fun j x => ?_, ?_⟩⟩
  · obtain ⟨B, -, hB⟩ := weakType_fPiece hd k A P₀ hc0 hell
    have h1 : Tendsto (fun j => ENNReal.ofReal (B / lam * sumL1 k (G j))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (hGsmall.const_mul (B / lam))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le)
      fun j => hB (G j) (hG j) (hGs j) lam hlam
  · obtain ⟨B, -, hB⟩ := integral_fPiece_le k A P₀ hc0 hell hψ
    refine squeeze_zero_norm (fun j => hB (G j) (hG j)) ?_
    simpa using hGsmall.const_mul B
  · have h := cl_rep k A P₀ hc0 hell (hw j) (hG j) (hH j) (hsys j) x
    have h2 := congrArg Complex.im h
    rw [Complex.add_im, im_fPiece k A P₀ hc0 hell (hG j) x] at h2
    simpa using h2.symm
  · exact exists_subseq_hPiece hd hk A P₀ hc0 hell w H hw hH hwb hHb

end

end AFree
