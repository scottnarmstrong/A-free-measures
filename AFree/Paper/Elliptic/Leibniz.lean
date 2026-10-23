module

public import AFree.Paper.Elliptic.Calculus
public import AFree.Analysis.Bump
public import AFree.Analysis.WaveCone

/-!
# The cut-off and the elliptic system: algebra

This file holds the pointwise algebra, smoothness and support statements for the cut-off system; the
integral bounds and the concrete instantiation with the mollified blow-ups are in
`AFree.Paper.Elliptic.Mollified` and `AFree.Paper.Elliptic`.
-/

@[expose] public section

open Matrix

namespace AFree

open PDE

variable {d m n : ℕ}

/-- `w = χ u`. -/
noncomputable def leibnizW (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => euclideanCutoff (1 / 2 : ℝ) (3 / 4) x * u x

/-- `G^{(ℓ)} = −Bᵀ A_ℓ (χ V)`. -/
noncomputable def leibnizG (A : Fin d → Matrix (Fin n) (Fin m) ℝ) (P₀ : Vec m)
    (V : Vec d → Vec m) (ℓ : Fin d) : Vec d → Vec d :=
  fun x => -((symbolColumns A P₀)ᵀ *ᵥ (A ℓ *ᵥ (euclideanCutoff (1 / 2 : ℝ) (3 / 4) x • V x)))

/-- `R = Σ_ℓ (∂_ℓ χ) A_ℓ V − r χ A₀ μ + u B ∇χ`. -/
noncomputable def leibnizR (A : Fin d → Matrix (Fin n) (Fin m) ℝ) (A₀ : Matrix (Fin n) (Fin m) ℝ)
    (P₀ : Vec m) (r : ℝ) (μ : Vec d → Vec m) (u : Vec d → ℝ) (V : Vec d → Vec m) :
    Vec d → Vec n :=
  fun x => (∑ ℓ, euclideanCoordDeriv ℓ (euclideanCutoff (1 / 2 : ℝ) (3 / 4)) x • (A ℓ *ᵥ V x)) -
    r • (euclideanCutoff (1 / 2 : ℝ) (3 / 4) x • (A₀ *ᵥ μ x)) +
    u x • (symbolColumns A P₀ *ᵥ classicalGradient (euclideanCutoff (1 / 2 : ℝ) (3 / 4)) x)

/-- `H = Bᵀ R`. -/
noncomputable def leibnizH (A : Fin d → Matrix (Fin n) (Fin m) ℝ) (A₀ : Matrix (Fin n) (Fin m) ℝ)
    (P₀ : Vec m) (r : ℝ) (μ : Vec d → Vec m) (u : Vec d → ℝ) (V : Vec d → Vec m) :
    Vec d → Vec d :=
  fun x => (symbolColumns A P₀)ᵀ *ᵥ leibnizR A A₀ P₀ r μ u V x

local notation "χ" => euclideanCutoff (1 / 2 : ℝ) (3 / 4)

section Support

lemma fderiv_eq_zero_of_notMem_tsupport {f : Vec d → ℝ} {x : Vec d} (h : x ∉ tsupport f) :
    fderiv ℝ f x = 0 := by
  by_contra hne
  exact h (support_fderiv_subset ℝ hne)

lemma cutoff_eq_zero_of_notMem {x : Vec d} (h : x ∉ tsupport (χ : Vec d → ℝ)) : χ x = 0 :=
  image_eq_zero_of_notMem_tsupport h

lemma coordDeriv_cutoff_eq_zero_of_notMem {x : Vec d} (h : x ∉ tsupport (χ : Vec d → ℝ))
    (ℓ : Fin d) : euclideanCoordDeriv ℓ χ x = 0 := by
  unfold euclideanCoordDeriv
  rw [fderiv_eq_zero_of_notMem_tsupport h]
  simp

lemma classicalGradient_cutoff_eq_zero_of_notMem {x : Vec d}
    (h : x ∉ tsupport (χ : Vec d → ℝ)) : classicalGradient χ x = 0 := by
  funext ℓ
  exact coordDeriv_cutoff_eq_zero_of_notMem h ℓ

lemma coordDeriv_eq_zero_of_notMem_tsupport {f : Vec d → ℝ} {x : Vec d} (h : x ∉ tsupport f)
    (ℓ : Fin d) : euclideanCoordDeriv ℓ f x = 0 := by
  by_contra hne
  exact h (support_euclideanCoordDeriv_subset_tsupport ℓ f hne)

lemma notMem_tsupport_cutoff_of_notMem {x : Vec d} (h : x ∉ euclideanBall (0 : Vec d) (7 / 8)) :
    x ∉ tsupport (χ : Vec d → ℝ) := fun hx =>
  h (euclideanBall_zero_mono (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
    (tsupport_euclideanCutoff_half hx))

end Support

section Smooth

lemma contDiff_mulVec {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℝ) {f : Vec d → Vec q}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (fun z => C *ᵥ f z) := by
  refine contDiff_pi.2 fun i => ?_
  have : (fun z => (C *ᵥ f z) i) = fun z => ∑ j, C i j * f z j := rfl
  rw [this]
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_pi.1 hf j)

lemma contDiff_classicalGradient_cutoff : ContDiff ℝ (⊤ : ℕ∞) (classicalGradient (χ : Vec d → ℝ)) :=
  contDiff_pi.2 fun ℓ => contDiff_euclideanCoordDeriv (contDiff_euclideanCutoff _ _) ℓ

lemma continuous_classicalGradient_cutoff : Continuous (classicalGradient (χ : Vec d → ℝ)) :=
  contDiff_classicalGradient_cutoff.continuous

end Smooth

section Core

variable {A : Fin d → Matrix (Fin n) (Fin m) ℝ} {A₀ : Matrix (Fin n) (Fin m) ℝ} {P₀ : Vec m}
  {r : ℝ} {μ : Vec d → Vec m} {u : Vec d → ℝ} {V : Vec d → Vec m}

lemma vecCoordDeriv_smul_const (a : Vec d → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (v : Vec m)
    (ℓ : Fin d) (x : Vec d) :
    vecCoordDeriv ℓ (fun z => a z • v) x = euclideanCoordDeriv ℓ a x • v := by
  funext i
  have := euclideanCoordDeriv_mul (a := a) (b := fun _ => v i) (x := x) ℓ
    ((ha.differentiable (by simp)) x) (differentiableAt_const _)
  simp only [vecCoordDeriv, Pi.smul_apply, smul_eq_mul]
  rw [this]
  simp [euclideanCoordDeriv]

/-- The pointwise algebra of the cut-off system: at a point where the mollified equation holds,
`B ∇w = −Σ ∂_ℓ(A_ℓ χ V) + R`, transported by `Bᵀ`. -/
theorem leibniz_identity_of_pde (hμ : ContDiff ℝ (⊤ : ℕ∞) μ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hV : ∀ x, V x = μ x - u x • P₀) {x : Vec d}
    (hpde : (∑ ℓ, A ℓ *ᵥ vecCoordDeriv ℓ μ x) + r • (A₀ *ᵥ μ x) = 0) :
    matVecMul (ellipticMatrix A P₀) (classicalGradient (leibnizW u) x) =
      (∑ ℓ, vecCoordDeriv ℓ (leibnizG A P₀ V ℓ) x) + leibnizH A A₀ P₀ r μ u V x := by
  have hVs : ContDiff ℝ (⊤ : ℕ∞) V := by
    have : V = fun x => μ x - u x • P₀ := funext hV
    rw [this]; exact hμ.sub (hu.smul contDiff_const)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (χ : Vec d → ℝ) := contDiff_euclideanCutoff _ _
  have hχV : ContDiff ℝ (⊤ : ℕ∞) (fun z => χ z • V z) := hχ.smul hVs
  set B := symbolColumns A P₀ with hB
  have hBg : ∀ g : Vec d, B *ᵥ g = ∑ ℓ, g ℓ • (A ℓ *ᵥ P₀) := by
    intro g
    funext k
    simp [hB, symbolColumns, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hG : ∀ ℓ, vecCoordDeriv ℓ (leibnizG A P₀ V ℓ) x =
      -(Bᵀ *ᵥ (A ℓ *ᵥ (euclideanCoordDeriv ℓ χ x • V x + χ x • vecCoordDeriv ℓ V x))) := by
    intro ℓ
    unfold leibnizG
    rw [vecCoordDeriv_neg, vecCoordDeriv_mulVec _ (contDiff_mulVec _ hχV),
      vecCoordDeriv_mulVec _ hχV, vecCoordDeriv_smul hχ hVs]
  have hdV : ∀ ℓ, vecCoordDeriv ℓ V x = vecCoordDeriv ℓ μ x - euclideanCoordDeriv ℓ u x • P₀ := by
    intro ℓ
    have : V = fun z => μ z - u z • P₀ := funext hV
    have hup : ContDiff ℝ (⊤ : ℕ∞) (fun z => u z • P₀) := hu.smul contDiff_const
    rw [this, vecCoordDeriv_sub hμ hup, vecCoordDeriv_smul_const u hu]
  have hpde' : ∑ ℓ, euclideanCoordDeriv ℓ u x • (A ℓ *ᵥ P₀) =
      -(∑ ℓ, A ℓ *ᵥ vecCoordDeriv ℓ V x) - r • (A₀ *ᵥ μ x) := by
    have h1 : ∑ ℓ, A ℓ *ᵥ vecCoordDeriv ℓ μ x = (∑ ℓ, A ℓ *ᵥ vecCoordDeriv ℓ V x) +
        ∑ ℓ, euclideanCoordDeriv ℓ u x • (A ℓ *ᵥ P₀) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [hdV, Matrix.mulVec_sub, Matrix.mulVec_smul]
      abel
    rw [h1] at hpde
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero]
    rw [← hpde]
    abel
  have hE : B *ᵥ classicalGradient (leibnizW u) x =
      -(∑ ℓ, A ℓ *ᵥ (euclideanCoordDeriv ℓ χ x • V x + χ x • vecCoordDeriv ℓ V x)) +
        leibnizR A A₀ P₀ r μ u V x := by
    have hg : ∀ ℓ, classicalGradient (leibnizW u) x ℓ =
        u x * euclideanCoordDeriv ℓ χ x + χ x * euclideanCoordDeriv ℓ u x := fun ℓ => by
      rw [mul_comm (u x)]
      exact euclideanCoordDeriv_mul ℓ ((hχ.differentiable (by simp)) x)
        ((hu.differentiable (by simp)) x)
    have hS : ∑ ℓ, A ℓ *ᵥ (euclideanCoordDeriv ℓ χ x • V x + χ x • vecCoordDeriv ℓ V x) =
        (∑ ℓ, euclideanCoordDeriv ℓ χ x • (A ℓ *ᵥ V x)) +
          χ x • ∑ ℓ, A ℓ *ᵥ vecCoordDeriv ℓ V x := by
      simp [Matrix.mulVec_add, Matrix.mulVec_smul, Finset.sum_add_distrib, Finset.smul_sum]
    rw [hS, hBg]
    simp only [hg, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    have hBc : ∑ ℓ, euclideanCoordDeriv ℓ χ x • (A ℓ *ᵥ P₀) =
        B *ᵥ classicalGradient χ x := by
      rw [hBg]; rfl
    rw [hpde']
    unfold leibnizR
    rw [← hBc]
    simp only [smul_neg, smul_sub, smul_smul]
    module
  have hL : matVecMul (ellipticMatrix A P₀) (classicalGradient (leibnizW u) x) =
      Bᵀ *ᵥ (B *ᵥ classicalGradient (leibnizW u) x) := by
    rw [Matrix.mulVec_mulVec]; rfl
  rw [hL, hE]
  simp only [hG, leibnizH, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_sum,
    Finset.sum_neg_distrib]
  rfl

lemma tsupport_leibnizW_subset (u : Vec d → ℝ) :
    tsupport (leibnizW u) ⊆ tsupport (χ : Vec d → ℝ) :=
  tsupport_mul_subset_left

lemma support_leibnizG_subset (ℓ : Fin d) (i : Fin d) :
    Function.support (fun z => leibnizG A P₀ V ℓ z i) ⊆ Function.support (χ : Vec d → ℝ) := by
  intro z hz
  by_contra h
  apply hz
  have h0 : χ z = 0 := by simpa using h
  show leibnizG A P₀ V ℓ z i = 0
  unfold leibnizG
  rw [h0, zero_smul, Matrix.mulVec_zero, Matrix.mulVec_zero]
  simp

lemma tsupport_leibnizG_coord_subset (ℓ : Fin d) (i : Fin d) :
    tsupport (fun z => leibnizG A P₀ V ℓ z i) ⊆ tsupport (χ : Vec d → ℝ) :=
  closure_mono (support_leibnizG_subset ℓ i)

lemma leibnizR_eq_zero_of_notMem {x : Vec d} (h : x ∉ tsupport (χ : Vec d → ℝ)) :
    leibnizR A A₀ P₀ r μ u V x = 0 := by
  unfold leibnizR
  rw [cutoff_eq_zero_of_notMem h, classicalGradient_cutoff_eq_zero_of_notMem h]
  simp only [coordDeriv_cutoff_eq_zero_of_notMem h, zero_smul, Finset.sum_const_zero,
    Matrix.mulVec_zero, smul_zero, sub_zero, add_zero]

lemma leibnizH_eq_zero_of_notMem {x : Vec d} (h : x ∉ tsupport (χ : Vec d → ℝ)) :
    leibnizH A A₀ P₀ r μ u V x = 0 := by
  simp [leibnizH, leibnizR_eq_zero_of_notMem h]

/-- `tsupport G^{(ℓ)} ⊆ B_{3/4} ⊆ B₁`. -/
theorem tsupport_leibnizG_subset (ℓ : Fin d) :
    tsupport (leibnizG A P₀ V ℓ) ⊆ euclideanBall (0 : Vec d) 1 := by
  refine (closure_minimal ?_ (isClosed_tsupport _)).trans
    (tsupport_euclideanCutoff_half.trans (euclideanBall_zero_mono (by norm_num) (by norm_num)))
  intro z hz
  by_contra h
  apply hz
  funext i
  have : z ∉ Function.support (fun z => leibnizG A P₀ V ℓ z i) := fun hh =>
    h (subset_closure (support_leibnizG_subset ℓ i hh))
  simpa using this

/-- `tsupport H ⊆ B_{3/4} ⊆ B₁`. -/
theorem tsupport_leibnizH_subset :
    tsupport (leibnizH A A₀ P₀ r μ u V) ⊆ euclideanBall (0 : Vec d) 1 := by
  refine (closure_minimal ?_ (isClosed_tsupport _)).trans
    (tsupport_euclideanCutoff_half.trans (euclideanBall_zero_mono (by norm_num) (by norm_num)))
  intro z hz
  by_contra h
  exact hz (leibnizH_eq_zero_of_notMem h)

/-- `tsupport w ⊆ closure B_{3/4}`. -/
theorem tsupport_leibnizW_subset_closedBall (u : Vec d → ℝ) :
    tsupport (leibnizW u) ⊆ euclideanClosedBall (0 : Vec d) (3 / 4) :=
  (tsupport_leibnizW_subset u).trans
    (tsupport_euclideanCutoff_half.trans (euclideanBall_subset_euclideanClosedBall _ _))

/-- `w ≥ 0`. -/
theorem leibnizW_nonneg {u : Vec d → ℝ} (hu : ∀ x, 0 ≤ u x) (x : Vec d) : 0 ≤ leibnizW u x :=
  mul_nonneg (euclideanCutoff_nonneg _ _ _) (hu x)

/-- `w` is smooth. -/
theorem contDiff_leibnizW {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (leibnizW u) :=
  (contDiff_euclideanCutoff _ _).mul hu

/-- `G^{(ℓ)}` is smooth. -/
theorem contDiff_leibnizG {V : Vec d → Vec m} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (ℓ : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (leibnizG A P₀ V ℓ) := by
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (χ : Vec d → ℝ) := contDiff_euclideanCutoff _ _
  have hχV : ContDiff ℝ (⊤ : ℕ∞) (fun z => χ z • V z) := hχ.smul hV
  exact (contDiff_mulVec (symbolColumns A P₀)ᵀ (contDiff_mulVec (A ℓ) hχV)).neg

/-- `H` is smooth. -/
theorem contDiff_leibnizH (hμ : ContDiff ℝ (⊤ : ℕ∞) μ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) : ContDiff ℝ (⊤ : ℕ∞) (leibnizH A A₀ P₀ r μ u V) := by
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (χ : Vec d → ℝ) := contDiff_euclideanCutoff _ _
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∑ ℓ, euclideanCoordDeriv ℓ χ z • (A ℓ *ᵥ V z)) :=
    ContDiff.sum fun ℓ _ => (contDiff_euclideanCoordDeriv hχ ℓ).smul (contDiff_mulVec _ hV)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => r • (χ z • (A₀ *ᵥ μ z))) :=
    (hχ.smul (contDiff_mulVec A₀ hμ)).const_smul r
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => u z • (symbolColumns A P₀ *ᵥ classicalGradient χ z)) :=
    hu.smul (contDiff_mulVec _ contDiff_classicalGradient_cutoff)
  exact contDiff_mulVec _ ((h1.sub h2).add h3)

/-- The pointwise identity `M ∇w = Σ_ℓ ∂_ℓ G^{(ℓ)} + H` on all of `ℝ^d`, given the
mollified equation on `B_{7/8}` and `V = μ − u P₀`. -/
theorem leibniz_identity (hμ : ContDiff ℝ (⊤ : ℕ∞) μ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hV : ∀ x, V x = μ x - u x • P₀)
    (hpde : ∀ x ∈ euclideanBall (0 : Vec d) (7 / 8),
      (∑ ℓ, A ℓ *ᵥ vecCoordDeriv ℓ μ x) + r • (A₀ *ᵥ μ x) = 0) (x : Vec d) :
    matVecMul (ellipticMatrix A P₀) (classicalGradient (leibnizW u) x) =
      (∑ ℓ, vecCoordDeriv ℓ (leibnizG A P₀ V ℓ) x) + leibnizH A A₀ P₀ r μ u V x := by
  by_cases hx : x ∈ euclideanBall (0 : Vec d) (7 / 8)
  · exact leibniz_identity_of_pde hμ hu hV (hpde x hx)
  · have h := notMem_tsupport_cutoff_of_notMem hx
    have hw : classicalGradient (leibnizW u) x = 0 := by
      funext ℓ
      exact coordDeriv_eq_zero_of_notMem_tsupport (fun hh => h (tsupport_leibnizW_subset u hh)) ℓ
    have hG : ∀ ℓ, vecCoordDeriv ℓ (leibnizG A P₀ V ℓ) x = 0 := by
      intro ℓ
      funext i
      exact coordDeriv_eq_zero_of_notMem_tsupport
        (fun hh => h (tsupport_leibnizG_coord_subset ℓ i hh)) ℓ
    rw [hw, leibnizH_eq_zero_of_notMem h]
    have h0 : ∀ M : Mat d, matVecMul M (0 : Vec d) = 0 := fun M => by
      funext i; simp [matVecMul]
    simp [hG, h0]

end Core

section Bounds

variable {A : Fin d → Matrix (Fin n) (Fin m) ℝ} {A₀ : Matrix (Fin n) (Fin m) ℝ} {P₀ : Vec m}
  {r : ℝ} {μ : Vec d → Vec m} {u : Vec d → ℝ} {V : Vec d → Vec m}

/-- The gradient of the cut-off `χ` is bounded. -/
theorem exists_gradient_cutoff_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Vec d, vecEuclideanNorm (classicalGradient χ z) ≤ C := by
  have hcont : Continuous fun z : Vec d => vecEuclideanNorm (classicalGradient χ z) := by
    unfold vecEuclideanNorm vecNormSq vecDot
    have := continuous_classicalGradient_cutoff (d := d)
    fun_prop
  have hcs : HasCompactSupport fun z : Vec d => vecEuclideanNorm (classicalGradient χ z) := by
    refine HasCompactSupport.intro (hasCompactSupport_euclideanCutoff (d := d)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 3 / 4)).isCompact fun z hz => ?_
    rw [classicalGradient_cutoff_eq_zero_of_notMem hz]
    exact vecEuclideanNorm_eq_zero_iff.2 rfl
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  exact ((Real.norm_of_nonneg (vecEuclideanNorm_nonneg _)).symm.le.trans (hC z)).trans
    (le_max_left _ _)

/-- Pointwise bound `|G^{(ℓ)}| ≤ ‖Bᵀ‖ ‖A_ℓ‖ |V|`. -/
theorem norm_leibnizG_le (ℓ : Fin d) (x : Vec d) :
    vecEuclideanNorm (leibnizG A P₀ V ℓ x) ≤
      matBound (symbolColumns A P₀)ᵀ * matBound (A ℓ) * vecEuclideanNorm (V x) := by
  unfold leibnizG
  rw [vecEuclideanNorm_neg]
  refine (vecEuclideanNorm_mulVec_le _ _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ((vecEuclideanNorm_mulVec_le _ _).trans ?_)
    (matBound_nonneg _)
  rw [vecEuclideanNorm_smul, abs_of_nonneg (euclideanCutoff_nonneg _ _ _)]
  have h1 := euclideanCutoff_le_one (d := d) (1 / 2 : ℝ) (3 / 4) x
  have h2 := vecEuclideanNorm_nonneg (V x)
  have h3 := matBound_nonneg (A ℓ)
  nlinarith [mul_nonneg h3 h2]

/-- Pointwise bound on `R`, for `0 ≤ r ≤ 1`, `u ≥ 0` and `|∇χ| ≤ C`. -/
theorem norm_leibnizR_le {C : ℝ} (hC : ∀ z : Vec d, vecEuclideanNorm (classicalGradient χ z) ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hu : ∀ x, 0 ≤ u x) (x : Vec d) :
    vecEuclideanNorm (leibnizR A A₀ P₀ r μ u V x) ≤
      C * (∑ ℓ, matBound (A ℓ)) * vecEuclideanNorm (V x) + matBound A₀ * vecEuclideanNorm (μ x) +
        matBound (symbolColumns A P₀) * C * u x := by
  have hχ0 := euclideanCutoff_nonneg (d := d) (1 / 2 : ℝ) (3 / 4) x
  have hχ1 := euclideanCutoff_le_one (d := d) (1 / 2 : ℝ) (3 / 4) x
  have hCnn : 0 ≤ C := (vecEuclideanNorm_nonneg _).trans (hC x)
  have hX : vecEuclideanNorm (∑ ℓ, euclideanCoordDeriv ℓ χ x • (A ℓ *ᵥ V x)) ≤
      C * (∑ ℓ, matBound (A ℓ)) * vecEuclideanNorm (V x) := by
    refine (vecEuclideanNorm_sum_le _).trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun ℓ _ => ?_
    rw [vecEuclideanNorm_smul]
    have h1 : |euclideanCoordDeriv ℓ χ x| ≤ C :=
      (abs_apply_le_vecEuclideanNorm (classicalGradient χ x) ℓ).trans (hC x)
    have h2 := vecEuclideanNorm_mulVec_le (A ℓ) (V x)
    have h3 := vecEuclideanNorm_nonneg (A ℓ *ᵥ V x)
    calc |euclideanCoordDeriv ℓ χ x| * vecEuclideanNorm (A ℓ *ᵥ V x) ≤
        C * (matBound (A ℓ) * vecEuclideanNorm (V x)) :=
          mul_le_mul h1 h2 h3 hCnn
      _ = _ := by ring
  have hY : vecEuclideanNorm (r • (χ x • (A₀ *ᵥ μ x))) ≤ matBound A₀ * vecEuclideanNorm (μ x) := by
    rw [vecEuclideanNorm_smul, vecEuclideanNorm_smul, abs_of_nonneg hr0, abs_of_nonneg hχ0]
    have h2 := vecEuclideanNorm_mulVec_le A₀ (μ x)
    have h3 := vecEuclideanNorm_nonneg (A₀ *ᵥ μ x)
    have h4 : r * χ x ≤ 1 := by nlinarith
    have h5 : 0 ≤ r * χ x := mul_nonneg hr0 hχ0
    calc r * (χ x * vecEuclideanNorm (A₀ *ᵥ μ x)) = (r * χ x) * vecEuclideanNorm (A₀ *ᵥ μ x) := by
          ring
      _ ≤ 1 * vecEuclideanNorm (A₀ *ᵥ μ x) := mul_le_mul_of_nonneg_right h4 h3
      _ ≤ _ := by rw [one_mul]; exact h2.trans' le_rfl
  have hZ : vecEuclideanNorm (u x • (symbolColumns A P₀ *ᵥ classicalGradient χ x)) ≤
      matBound (symbolColumns A P₀) * C * u x := by
    rw [vecEuclideanNorm_smul, abs_of_nonneg (hu x)]
    have h2 := (vecEuclideanNorm_mulVec_le (symbolColumns A P₀) (classicalGradient χ x)).trans
      (mul_le_mul_of_nonneg_left (hC x) (matBound_nonneg _))
    calc u x * _ ≤ u x * (matBound (symbolColumns A P₀) * C) :=
          mul_le_mul_of_nonneg_left h2 (hu x)
      _ = _ := by ring
  unfold leibnizR
  rw [sub_eq_add_neg]
  refine (vecEuclideanNorm_add_le _ _).trans ?_
  refine add_le_add ((vecEuclideanNorm_add_le _ _).trans ?_) hZ
  rw [vecEuclideanNorm_neg]
  exact add_le_add hX hY

/-- `|H| ≤ ‖Bᵀ‖ |R|`. -/
theorem norm_leibnizH_le (x : Vec d) :
    vecEuclideanNorm (leibnizH A A₀ P₀ r μ u V x) ≤
      matBound (symbolColumns A P₀)ᵀ * vecEuclideanNorm (leibnizR A A₀ P₀ r μ u V x) :=
  vecEuclideanNorm_mulVec_le _ _

end Bounds

end AFree
