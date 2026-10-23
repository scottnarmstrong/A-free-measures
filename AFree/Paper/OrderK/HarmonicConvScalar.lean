module

public import AFree.Analysis.ConvCompact
public import AFree.Paper.OrderK.HarmonicBasic

/-!
# Compactness of convolution with a scalar `L¹` kernel

Scalar version of the convolution compactness lemma `AFree.exists_subseq_tendsto_conv`,
which plays the role of [DPR, Lemma 2.1] here, obtained from the vector-valued lemma applied to `Re K` and `Im K` embedded in
the first coordinate.
-/

@[expose] public section

open MeasureTheory PDE Filter Topology
open scoped Convolution

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The scalar convolution `(K ⋆ F)(x) = ∫ K(x - y) F(y) dy` of a complex kernel with a real
function. -/
def cconv (K : Vec d → ℂ) (F : Vec d → ℝ) (x : Vec d) : ℂ :=
  ∫ y, K (x - y) * (F y : ℂ)

/-- Embedding of a scalar function in the first coordinate of `Vec d` (`d ≥ 1`). -/
def emb (hd : 0 < d) (g : Vec d → ℝ) : Vec d → Vec d := fun x => Pi.single ⟨0, hd⟩ (g x)

theorem vecEuclideanNorm_single_zero (hd : 0 < d) (a : ℝ) :
    vecEuclideanNorm (Pi.single (⟨0, hd⟩ : Fin d) a : Vec d) = |a| := by
  unfold vecEuclideanNorm vecNormSq vecDot
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp [Real.sqrt_mul_self_eq_abs]
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

theorem integrable_emb (hd : 0 < d) {g : Vec d → ℝ} (hg : Integrable g) : Integrable (emb hd g) :=
  (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) (⟨0, hd⟩ : Fin d)).integrable_comp hg

theorem integral_vecEuclideanNorm_emb (hd : 0 < d) (g : Vec d → ℝ) :
    ∫ x, vecEuclideanNorm (emb hd g x) = ∫ x, |g x| := by
  simp [emb, vecEuclideanNorm_single_zero]

theorem conv_emb (hd : 0 < d) (k F : Vec d → ℝ) (x : Vec d) :
    conv (emb hd k) (emb hd F) x = ∫ y, k (x - y) * F y := by
  unfold conv emb vecDot
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

/-- A common subsequence for finitely many sequences, each of which has convergent
subsequences of every subsequence. -/
theorem exists_common_subseq {ι' : Type*} (t : Finset ι') (u : ι' → ℕ → Vec d → ℝ)
    (h : ∀ i ∈ t, ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : Vec d → ℝ,
      IntegrableOn g (euclideanBall (0 : Vec d) 1) ∧
      Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) 1, |u i (φ (ψ n)) x - g x|) atTop
        (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i ∈ t, ∃ g : Vec d → ℝ,
      IntegrableOn g (euclideanBall (0 : Vec d) 1) ∧
      Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) 1, |u i (φ n) x - g x|) atTop (𝓝 0) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | insert a t ha ih =>
    obtain ⟨φ, hφ, hg⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨ψ, hψ, g, hgi, hgt⟩ := h a (Finset.mem_insert_self a t) φ hφ
    refine ⟨φ ∘ ψ, hφ.comp hψ, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨g, hgi, hgt⟩
    · obtain ⟨g', hg', ht'⟩ := hg i hi
      exact ⟨g', hg', ht'.comp hψ.tendsto_atTop⟩

/-- The real or imaginary part of a complex kernel (`true` for the real part). -/
def kpart (b : Bool) (K : Vec d → ℂ) (x : Vec d) : ℝ :=
  if b then (K x).re else (K x).im

theorem integrable_kpart (b : Bool) {K : Vec d → ℂ} (hK : Integrable K) :
    Integrable (kpart b K) := by
  cases b
  · exact hK.im
  · exact hK.re

theorem norm_re_im_le (a b : ℝ) : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ≤ |a| + |b| := by
  refine (norm_add_le _ _).trans ?_
  simp

theorem cconv_eq_of_integrable (K : Vec d → ℂ) (F : Vec d → ℝ) (x : Vec d)
    (h : Integrable fun y => K (x - y) * (F y : ℂ)) (hd : 0 < d) :
    cconv K F x = ((conv (emb hd (kpart true K)) (emb hd F) x : ℝ) : ℂ) +
      ((conv (emb hd (kpart false K)) (emb hd F) x : ℝ) : ℂ) * Complex.I := by
  rw [conv_emb, conv_emb]
  have hre := Complex.reCLM.integral_comp_comm h
  have him := Complex.imCLM.integral_comp_comm h
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_add] at hre him
  unfold cconv
  rw [← Complex.re_add_im (∫ y, K (x - y) * (F y : ℂ))]
  simp only [kpart, ite_true, Bool.false_eq_true, ite_false]
  rw [← hre, ← him]

/-- Compactness of convolution with scalar `L¹` kernels: for `d ≥ 1`, integrable
complex kernels `K_ν` and integrable real `F_j^ν` with `‖F_j^ν‖₁ ≤ C`, a subsequence of
`Σ_ν K_ν ⋆ F_j^ν` converges in `L¹(B₁; ℂ)`. (A single pair is the case of a singleton `s`.) -/
theorem cor_convscalar {ν : Type*} (hd : 0 < d) (s : Finset ν) (K : ν → Vec d → ℂ)
    (hK : ∀ i ∈ s, Integrable (K i)) (F : ν → ℕ → Vec d → ℝ)
    (hF : ∀ i ∈ s, ∀ j, Integrable (F i j)) {C : ℝ} (hC : ∀ i ∈ s, ∀ j, ∫ x, |F i j x| ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : Vec d → ℂ,
      IntegrableOn g (euclideanBall (0 : Vec d) 1) ∧
      Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) 1,
        ‖∑ i ∈ s, cconv (K i) (F i (φ n)) x - g x‖) atTop (𝓝 0) := by
  classical
  set B := euclideanBall (0 : Vec d) 1 with hB
  let u : ν × Bool → ℕ → Vec d → ℝ := fun p n =>
    conv (emb hd (kpart p.2 (K p.1))) (emb hd (F p.1 n))
  have h1 : ∀ p ∈ s ×ˢ (Finset.univ : Finset Bool), ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : Vec d → ℝ, IntegrableOn g B ∧
        Tendsto (fun n => ∫ x in B, |u p (φ (ψ n)) x - g x|) atTop (𝓝 0) := by
    intro p hp φ hφ
    have hps : p.1 ∈ s := (Finset.mem_product.1 hp).1
    obtain ⟨ψ, hψ, g, hg, ht⟩ := exists_subseq_tendsto_conv
      (integrable_emb hd (integrable_kpart p.2 (hK _ hps)))
      (F := fun j => emb hd (F p.1 (φ j))) (fun j => integrable_emb hd (hF _ hps _)) (C := C)
      (fun j => by rw [integral_vecEuclideanNorm_emb]; exact hC _ hps _)
    exact ⟨ψ, hψ, g, hg, ht⟩
  obtain ⟨φ, hφ, hg⟩ := exists_common_subseq _ u h1
  choose! g hgi hgt using hg
  set G : Vec d → ℂ := fun x => ∑ i ∈ s,
    (((g (i, true) x : ℝ) : ℂ) + ((g (i, false) x : ℝ) : ℂ) * Complex.I) with hG
  -- almost everywhere integrability of the convolution integrands
  have hae : ∀ᵐ x : Vec d, ∀ i ∈ s, ∀ n, Integrable fun y => K i (x - y) * (F i n y : ℂ) := by
    refine (Filter.eventually_all_finset s).2 fun i hi => ?_
    refine ae_all_iff.2 fun n => ?_
    have := (((hF i hi n).ofReal (𝕜 := ℂ)).ae_convolution_exists
      (ContinuousLinearMap.mul ℂ ℂ) (hK i hi))
    filter_upwards [this] with x hx
    simpa [ConvolutionExistsAt, mul_comm] using hx
  have hu : ∀ p ∈ s ×ˢ (Finset.univ : Finset Bool), ∀ n, Integrable (u p n) := fun p hp n =>
    integrable_conv (integrable_emb hd (integrable_kpart p.2 (hK _ (Finset.mem_product.1 hp).1)))
      (integrable_emb hd (hF _ (Finset.mem_product.1 hp).1 n))
  have hmem : ∀ i ∈ s, ∀ b : Bool, (i, b) ∈ s ×ˢ (Finset.univ : Finset Bool) := fun i hi b =>
    Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩
  refine ⟨φ, hφ, G, ?_, ?_⟩
  · refine integrable_finsetSum _ fun i hi => ?_
    exact ((hgi _ (hmem i hi true)).ofReal (𝕜 := ℂ)).add
      (((hgi _ (hmem i hi false)).ofReal (𝕜 := ℂ)).mul_const _)
  · have hbound : ∀ n, ∫ x in B, ‖∑ i ∈ s, cconv (K i) (F i (φ n)) x - G x‖ ≤
        ∑ i ∈ s, ((∫ x in B, |u (i, true) (φ n) x - g (i, true) x|) +
          ∫ x in B, |u (i, false) (φ n) x - g (i, false) x|) := by
      intro n
      have hint : ∀ i ∈ s, ∀ b : Bool,
          IntegrableOn (fun x => |u (i, b) (φ n) x - g (i, b) x|) B := fun i hi b =>
        (((hu _ (hmem i hi b) (φ n)).integrableOn).sub (hgi _ (hmem i hi b))).abs
      have e : ∫ x in B, ∑ i ∈ s, (|u (i, true) (φ n) x - g (i, true) x| +
          |u (i, false) (φ n) x - g (i, false) x|) =
          ∑ i ∈ s, ((∫ x in B, |u (i, true) (φ n) x - g (i, true) x|) +
            ∫ x in B, |u (i, false) (φ n) x - g (i, false) x|) := by
        have hs : ∀ i ∈ s, IntegrableOn (fun x => |u (i, true) (φ n) x - g (i, true) x| +
            |u (i, false) (φ n) x - g (i, false) x|) B := fun i hi =>
          (hint i hi true).add (hint i hi false)
        rw [integral_finsetSum _ hs]
        exact Finset.sum_congr rfl fun i hi => integral_add (hint i hi true) (hint i hi false)
      rw [← e]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
        (integrable_finsetSum _ fun i hi => (hint i hi true).add (hint i hi false)) ?_
      refine ae_restrict_of_ae ?_
      filter_upwards [hae] with x hx
      have hc : ∀ i ∈ s, cconv (K i) (F i (φ n)) x =
          ((u (i, true) (φ n) x : ℝ) : ℂ) + ((u (i, false) (φ n) x : ℝ) : ℂ) * Complex.I :=
        fun i hi => cconv_eq_of_integrable _ _ _ (hx i hi (φ n)) hd
      rw [Finset.sum_congr rfl hc, hG, ← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      have : (((u (i, true) (φ n) x : ℝ) : ℂ) + ((u (i, false) (φ n) x : ℝ) : ℂ) * Complex.I) -
          (((g (i, true) x : ℝ) : ℂ) + ((g (i, false) x : ℝ) : ℂ) * Complex.I) =
          (((u (i, true) (φ n) x - g (i, true) x : ℝ)) : ℂ) +
            ((u (i, false) (φ n) x - g (i, false) x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this]
      exact norm_re_im_le _ _
    refine squeeze_zero (fun n => integral_nonneg fun x => norm_nonneg _) hbound ?_
    have : Tendsto (fun n => ∑ i ∈ s, ((∫ x in B, |u (i, true) (φ n) x - g (i, true) x|) +
        ∫ x in B, |u (i, false) (φ n) x - g (i, false) x|)) atTop
        (𝓝 (∑ i ∈ s, ((0 : ℝ) + 0))) :=
      tendsto_finsetSum _ fun i hi => (hgt _ (hmem i hi true)).add (hgt _ (hmem i hi false))
    simpa using this

end

end AFree
