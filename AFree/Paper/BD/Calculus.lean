module

public import AFree.Defs
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Coordinate-derivative calculus for the BD section

Coordinate derivatives of smooth functions commute, `∂^{α + e_i} = ∂_i ∂^α`, and test functions are
stable under `∂_i`.
-/

public section

open MeasureTheory PDE

namespace AFree

namespace BD

variable {d : ℕ}

/-- Coordinate derivatives of a smooth function commute. -/
theorem coordDeriv_comm {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i j : Fin d) :
    euclideanCoordDeriv i (euclideanCoordDeriv j g) =
      euclideanCoordDeriv j (euclideanCoordDeriv i g) := by
  funext x
  have hc : ContDiffAt ℝ 2 g x :=
    hg.contDiffAt.of_le (WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hsym := (hc.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField])).eq (basisVec j) (basisVec i)
  have e : ∀ a b : Fin d, euclideanCoordDeriv a (euclideanCoordDeriv b g) x =
      fderiv ℝ (fderiv ℝ g) x (basisVec a) (basisVec b) := by
    intro a b
    unfold euclideanCoordDeriv
    have hfd : DifferentiableAt ℝ (fderiv ℝ g) x :=
      (hg.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
    have h1 : (fun y => fderiv ℝ g y (basisVec b)) = fun y => (fderiv ℝ g y) (basisVec b) := rfl
    rw [h1, fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  rw [e i j, e j i]
  exact hsym.symm

theorem contDiff_iterate_D {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : Fin d) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((euclideanCoordDeriv j)^[n] g) := by
  induction n with
  | zero => exact hg
  | succ n ih => rw [Function.iterate_succ_apply']; exact contDiff_euclideanCoordDeriv ih j

theorem iterate_coordDeriv_comm {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i j : Fin d) (n : ℕ) :
    (euclideanCoordDeriv j)^[n] (euclideanCoordDeriv i g) =
      euclideanCoordDeriv i ((euclideanCoordDeriv j)^[n] g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      coordDeriv_comm (contDiff_iterate_D hg j n) j i]

theorem contDiff_foldr {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (α : Fin d → ℕ)
    (l : List (Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞) (l.foldr (fun j g => (euclideanCoordDeriv j)^[α j] g) φ) := by
  induction l with
  | nil => exact hφ
  | cons j l ih => exact contDiff_iterate_D ih j _

theorem foldr_congr_mem {f g : Fin d → (Vec d → ℝ) → (Vec d → ℝ)} {φ : Vec d → ℝ}
    (l : List (Fin d)) (h : ∀ k ∈ l, f k = g k) : l.foldr f φ = l.foldr g φ := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldr_cons]
    rw [ih fun m hm => h m (List.mem_cons_of_mem _ hm), h k List.mem_cons_self]

theorem foldr_add_single (l : List (Fin d)) (hl : l.Nodup) (i : Fin d) (hi : i ∈ l)
    (α : Fin d → ℕ) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    l.foldr (fun j g => (euclideanCoordDeriv j)^[(α + Pi.single i 1 : Fin d → ℕ) j] g) φ =
      euclideanCoordDeriv i (l.foldr (fun j g => (euclideanCoordDeriv j)^[α j] g) φ) := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    by_cases hij : j = i
    · subst hij
      have hcongr : l.foldr (fun k g => (euclideanCoordDeriv k)^[(α + Pi.single j 1 : Fin d → ℕ) k] g) φ =
          l.foldr (fun k g => (euclideanCoordDeriv k)^[α k] g) φ := by
        refine foldr_congr_mem l ?_
        intro k hk
        have : k ≠ j := fun h => hl.1 (h ▸ hk)
        simp [Pi.single_eq_of_ne this]
      rw [List.foldr_cons, List.foldr_cons, hcongr, Pi.add_apply, Pi.single_eq_same,
        Function.iterate_succ_apply']
    · have hil : i ∈ l := (List.mem_cons.1 hi).resolve_left (Ne.symm hij)
      rw [List.foldr_cons, List.foldr_cons, ih hl.2 hil, Pi.add_apply,
        Pi.single_eq_of_ne hij, add_zero]
      exact iterate_coordDeriv_comm (contDiff_foldr hφ α l) i j _

theorem multiCoordDeriv_add_single (α : Fin d → ℕ) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    multiCoordDeriv (α + Pi.single i 1) φ = euclideanCoordDeriv i (multiCoordDeriv α φ) :=
  foldr_add_single _ (List.nodup_finRange d) i (List.mem_finRange i) α hφ

theorem multiCoordDeriv_zero (φ : Vec d → ℝ) : multiCoordDeriv (0 : Fin d → ℕ) φ = φ := by
  unfold multiCoordDeriv
  induction (List.finRange d) with
  | nil => rfl
  | cons j l ih => simp

/-- `∂^{e_a + e_b} φ = ∂_b ∂_a φ` (second order). -/
theorem multiCoordDeriv_two (a b : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    multiCoordDeriv (Pi.single a 1 + Pi.single b 1) φ =
      euclideanCoordDeriv b (euclideanCoordDeriv a φ) := by
  have h1 : multiCoordDeriv (0 + Pi.single a 1 : Fin d → ℕ) φ = euclideanCoordDeriv a φ := by
    rw [multiCoordDeriv_add_single _ _ hφ, multiCoordDeriv_zero]
  have e : (Pi.single a 1 + Pi.single b 1 : Fin d → ℕ) = (0 + Pi.single a 1) + Pi.single b 1 := by
    rw [zero_add]
  rw [e, multiCoordDeriv_add_single _ _ hφ, h1]

/-- Coordinate derivatives of test functions are test functions. -/
theorem isTest_D {Ω : Set (Vec d)} {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Ω φ) (i : Fin d) :
    IsTestFunctionOn Ω (euclideanCoordDeriv i φ) :=
  ⟨contDiff_euclideanCoordDeriv hφ.1 i, hasCompactSupport_euclideanCoordDeriv hφ.2.1 i,
    (tsupport_euclideanCoordDeriv_subset_tsupport i φ).trans hφ.2.2⟩

theorem integrableOn_coord {Ω : Set (Vec d)} {u : Vec d → Vec d} (hu : IntegrableOn u Ω) (i : Fin d) :
    IntegrableOn (fun x => u x i) Ω :=
  (integrable_pi_iff.1 hu) i

/-- Bounded continuous multiplier of an integrable coordinate. -/
theorem integrableOn_coord_mul {Ω : Set (Vec d)} {u : Vec d → Vec d} (hu : IntegrableOn u Ω)
    (i : Fin d) {g : Vec d → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    IntegrableOn (fun x => u x i * g x) Ω := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
  have := (integrableOn_coord hu i).bdd_mul hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  simpa only [IntegrableOn, mul_comm] using this

/-- The defining identity of `Eu`, solved for the vector integral:
`(∫ φ dEu)_{ij} = -½ (∫_Ω u_i ∂_jφ + ∫_Ω u_j ∂_iφ)`. -/
theorem integral_eq_of_isBDGradientOn {Ω : Set (Vec d)} {u : Vec d → Vec d}
    {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)} (hEu : IsBDGradientOn Ω u Eu)
    {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Ω φ) (i j : Fin d) :
    (∫ᵛ x, φ x ∂•Eu) (i, j) =
      -((∫ x in Ω, u x i * euclideanCoordDeriv j φ x) +
        ∫ x in Ω, u x j * euclideanCoordDeriv i φ x) / 2 := by
  have h := hEu.2.2 φ hφ i j
  have hj := isTest_D hφ j
  have hi := isTest_D hφ i
  rw [integral_div, integral_add (integrableOn_coord_mul hEu.1 i hj.1.continuous hj.2.1)
    (integrableOn_coord_mul hEu.1 j hi.1.continuous hi.2.1)] at h
  rw [neg_div]
  linarith

end BD

end AFree
