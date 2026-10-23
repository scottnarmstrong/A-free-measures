module

public import AFree.Paper.OrderK.StrongConstancyRep
public import AFree.Paper.OrderK.HarmonicConvScalar
public import AFree.Paper.OrderK.StrongConstancyPiecesA
public import AFree.Harmonic.Kernel

/-!
# The pieces `h_j`: `L¹(B₁)` compactness

Compactness of `h_j` in `L¹(B₁)`.
-/

@[expose] public section

open MeasureTheory PDE Matrix Filter Topology
open scoped SchwartzMap ComplexConjugate

namespace AFree

noncomputable section

variable {d : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι]

theorem ccMult_eq_cconv {s : ℝ} (hs : 0 < s) {m : Vec d → ℂ} (hm : IsSymbol (-s) m)
    {f : Vec d → ℝ} (hf : IsCc f) (x : Vec d) : ccMult m f x = cconv (negKernel m) f x := by
  unfold ccMult cconv
  rw [vecMultiplier_eq_negKernel hs hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [schw_apply hf]

/-- A subsequence of `h_j` converges in `L¹(B₁; ℂ)`. -/
theorem exists_subseq_hPiece (hd : 0 < d) {k : ℕ} (hk : 1 ≤ k)
    (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) {c0 : ℝ} (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ))
    (w : ℕ → Vec d → ℝ) (H : ℕ → (Fin d → ℕ) → Vec d → κ → ℝ) (hw : ∀ j, IsCc (w j))
    (hH : ∀ j β, ContDiff ℝ (⊤ : ℕ∞) (H j β) ∧ HasCompactSupport (H j β))
    (hwb : ∃ C : ℝ, ∀ j, ∫ x, |w j x| ≤ C)
    (hHb : ∀ h ∈ Finset.range k, ∀ β ∈ Finset.Nat.antidiagonalTuple d h,
      ∃ C : ℝ, ∀ j, ∫ x, piEuclideanNorm (H j β x) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : Vec d → ℂ,
      IntegrableOn g (euclideanBall (0 : Vec d) 1) ∧
      Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) 1,
        ‖hPiece k A P₀ (w (φ n)) (H (φ n)) x - g x‖) atTop (𝓝 0) := by
  classical
  obtain ⟨Cw, hCw⟩ := hwb
  have hHb' : ∀ p : (Σ _ : ℕ, Fin d → ℕ), ∃ C : ℝ, p ∈ (Finset.range k).sigma
      (fun h => Finset.Nat.antidiagonalTuple d h) → ∀ j, ∫ x, piEuclideanNorm (H j p.2 x) ≤ C := by
    intro p
    by_cases hp : p ∈ (Finset.range k).sigma (fun h => Finset.Nat.antidiagonalTuple d h)
    · obtain ⟨C, hC⟩ := hHb p.1 (Finset.mem_sigma.1 hp).1 p.2 (Finset.mem_sigma.1 hp).2
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose Cb hCb using hHb'
  set P : Finset (Σ _ : ℕ, Fin d → ℕ) :=
    (Finset.range k).sigma (fun h => Finset.Nat.antidiagonalTuple d h) with hP
  set S : Finset ((Σ _ : ℕ, Fin d → ℕ) × κ) := P ×ˢ Finset.univ with hS
  set s : Finset (Option ((Σ _ : ℕ, Fin d → ℕ) × κ)) := Finset.insertNone S with hs
  let K : Option ((Σ _ : ℕ, Fin d → ℕ) × κ) → Vec d → ℂ := fun o =>
    o.elim (negKernel (m1Symb k A P₀)) fun q => negKernel (mBetaSymb k A P₀ q.1.2 q.2)
  let F : Option ((Σ _ : ℕ, Fin d → ℕ) × κ) → ℕ → Vec d → ℝ := fun o j =>
    o.elim (w j) fun q y => H j q.1.2 y q.2
  have hm1 : IsSymbol (-(2 * k : ℝ)) (m1Symb k A P₀) := isSymbol_m1Symb k A P₀ hc0 hell
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < 2 * k := by linarith
  have hmb : ∀ q ∈ S, IsSymbol (-1) (mBetaSymb k A P₀ q.1.2 q.2) := fun q hq => by
    have hq1 := (Finset.mem_sigma.1 (Finset.mem_product.1 hq).1)
    refine ((lem_symbolsk k A P₀ hc0 hell).2.2 q.1.2 q.2).2 ?_
    have := Finset.Nat.mem_antidiagonalTuple.1 hq1.2
    have := Finset.mem_range.1 hq1.1
    omega
  have hKi : ∀ o ∈ s, Integrable (K o) := by
    intro o ho
    rcases o with _ | q
    · exact integrable_negKernel hk2 hm1
    · exact integrable_negKernel one_pos (hmb q (by simpa [hs] using ho))
  have hcc : ∀ (j : ℕ) (q : (Σ _ : ℕ, Fin d → ℕ) × κ), IsCc (fun y => H j q.1.2 y q.2) := fun j q =>
    isCc_apply_of (hH j q.1.2).1 (hH j q.1.2).2 q.2
  have hFi : ∀ o ∈ s, ∀ j, Integrable (F o j) := by
    intro o _ j
    rcases o with _ | q
    · exact (hw j).1.continuous.integrable_of_hasCompactSupport (hw j).2
    · exact (hcc j q).1.continuous.integrable_of_hasCompactSupport (hcc j q).2
  set C : ℝ := |Cw| + ∑ p ∈ P, |Cb p| with hC
  have hFb : ∀ o ∈ s, ∀ j, ∫ x, |F o j x| ≤ C := by
    intro o ho j
    rcases o with _ | q
    · have := hCw j
      have : 0 ≤ ∑ p ∈ P, |Cb p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      simp only [F, Option.elim]
      linarith [le_abs_self Cw]
    · have hqS : q ∈ S := by simpa [hs] using ho
      have hq : q.1 ∈ P := (Finset.mem_product.1 hqS).1
      have h1 : ∫ x, |H j q.1.2 x q.2| ≤ ∫ x, piEuclideanNorm (H j q.1.2 x) :=
        integral_mono ((hcc j q).1.continuous.integrable_of_hasCompactSupport (hcc j q).2).abs
          (integrable_piEuclideanNorm (hH j q.1.2).1.continuous (hH j q.1.2).2)
          fun x => abs_le_piEuclideanNorm _ _
      have h2 := hCb q.1 hq j
      have h3 : |Cb q.1| ≤ ∑ p ∈ P, |Cb p| :=
        Finset.single_le_sum (f := fun p => |Cb p|) (fun _ _ => abs_nonneg _) hq
      simp only [F, Option.elim]
      linarith [le_abs_self (Cb q.1), abs_nonneg Cw]
  obtain ⟨φ, hφ, g, hgi, hgt⟩ := cor_convscalar hd s K hKi F hFi hFb
  refine ⟨φ, hφ, g, hgi, ?_⟩
  refine hgt.congr fun n => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  congr 3
  rw [hs, Finset.sum_insertNone]
  simp only [K, F, Option.elim]
  rw [hPiece, ← ccMult_eq_cconv hk2 hm1 (hw _)]
  congr 1
  rw [hS, hP, Finset.sum_product, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun β hβ => Finset.sum_congr rfl
    fun c _ => ?_
  have hmem : ((⟨h, β⟩ : (Σ _ : ℕ, Fin d → ℕ)), c) ∈ S :=
    Finset.mem_product.2 ⟨Finset.mem_sigma.2 ⟨hh, hβ⟩, Finset.mem_univ _⟩
  exact (ccMult_eq_cconv one_pos (hmb _ hmem) (hcc (φ n) (⟨h, β⟩, c)) x).symm

end

end AFree
