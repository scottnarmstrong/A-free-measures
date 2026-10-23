module

public import AFree.TopCurrents.USharpAux
public import AFree.TopCurrents.WStar

/-!
# `u_#` is a satisfies the defining clauses of `IsMetricCurrent`

The axioms are those of [AK, Definition 3.1] for metric currents, together with admissibility of `|u| 𝓛^d`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents AFree.MetricCurrents.AKExt

variable {d : ℕ} {u : Vec d → ℝ}

/-- Linearity in `f`. -/
lemma usharp_lin_f (hu : Integrable u volume) {f g : Vec d → ℝ} (hf : IsBddLipFun f)
    (hg : IsBddLipFun g) {π : Fin d → Vec d → ℝ} (hπ : IsLipTuple π) (a b : ℝ) :
    usharp u (a • f + b • g) π = a * usharp u f π + b * usharp u g π := by
  unfold usharp
  have h1 := (integrable_usharp_term hu hf hπ).const_mul a
  have h2 := (integrable_usharp_term hu hg hπ).const_mul b
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma jacMat_update (π : Fin d → Vec d → ℝ) (i : Fin d) (g : Vec d → ℝ) (x : Vec d) :
    jacMat (Function.update π i g) x =
      (jacMat π x).updateRow i (fun j => fderiv ℝ g x (Pi.single j 1)) := by
  ext l j
  by_cases h : l = i
  · subst h; simp [jacMat]
  · simp [jacMat, Function.update_of_ne h, Matrix.updateRow_ne h]

/-- Linearity in slot `i`. -/
lemma usharp_lin_slot (hu : Integrable u volume) {f : Vec d → ℝ} (hf : IsBddLipFun f)
    {π : Fin d → Vec d → ℝ} (hπ : IsLipTuple π) (i : Fin d) {ψ : Vec d → ℝ} (hψ : IsLipFun ψ)
    (a b : ℝ) :
    usharp u f (Function.update π i (a • π i + b • ψ)) =
      a * usharp u f π + b * usharp u f (Function.update π i ψ) := by
  have hπ' : IsLipTuple (Function.update π i (a • π i + b • ψ)) :=
    lipTuple_update hπ i (lip_add (lip_smul (hπ i) a) (lip_smul hψ b))
  have hπψ : IsLipTuple (Function.update π i ψ) := lipTuple_update hπ i hψ
  unfold usharp
  have h1 := (integrable_usharp_term hu hf hπ).const_mul a
  have h2 := (integrable_usharp_term hu hf hπψ).const_mul b
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
  have hae : ∀ᵐ x : Vec d, DifferentiableAt ℝ (π i) x ∧ DifferentiableAt ℝ ψ x := by
    obtain ⟨K, hK⟩ := hπ i
    obtain ⟨L, hL⟩ := hψ
    filter_upwards [Moll.ae_differentiableAt_of_eucl hK, Moll.ae_differentiableAt_of_eucl hL]
      with x h1 h2 using ⟨h1, h2⟩
  refine integral_congr_ae (hae.mono fun x ⟨hx1, hx2⟩ => ?_)
  have hd : jacDet (Function.update π i (a • π i + b • ψ)) x =
      a * jacDet π x + b * jacDet (Function.update π i ψ) x := by
    unfold jacDet
    rw [jacMat_update, jacMat_update]
    have hrow : (fun j => fderiv ℝ (a • π i + b • ψ) x (Pi.single j 1)) =
        a • (fun j => fderiv ℝ (π i) x (Pi.single j 1)) +
          b • (fun j => fderiv ℝ ψ x (Pi.single j 1)) := by
      funext j
      rw [fderiv_add (hx1.const_smul a) (hx2.const_smul b), fderiv_const_smul hx1,
        fderiv_const_smul hx2]
      simp
    have hπrow : jacMat π x = (jacMat π x).updateRow i (jacMat π x i) := by simp
    rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]
    have : (jacMat π x).updateRow i (fun j => fderiv ℝ (π i) x (Pi.single j 1)) = jacMat π x := by
      conv_rhs => rw [hπrow]
      rfl
    rw [this]
  beta_reduce
  rw [hd]
  ring

/-- Locality: `u_#(f, π) = 0` if `f` is supported in an open set on which `π i` is constant. -/
lemma usharp_locality {f : Vec d → ℝ} {π : Fin d → Vec d → ℝ} (i : Fin d) {U : Set (Vec d)}
    (hU : IsOpen U) (hfU : {x | f x ≠ 0} ⊆ U) {c : ℝ} (hc : ∀ x ∈ U, π i x = c) :
    usharp u f π = 0 := by
  unfold usharp
  have : (fun x => f x * u x * jacDet π x) = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ U
    · have hev : π i =ᶠ[𝓝 x] fun _ => c :=
        Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hc y hy
      have h0 : fderiv ℝ (π i) x = 0 := by rw [hev.fderiv_eq]; simp
      have : jacDet π x = 0 := by
        unfold jacDet
        exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [jacMat, h0]
      rw [this, mul_zero]
    · have : f x = 0 := by
        by_contra h; exact hx (hfU h)
      rw [this]; ring
  rw [this]; simp

/-- Continuity: `u_#` is continuous under pointwise convergence of equi-Lipschitz tuples. -/
lemma usharp_continuity (hu : Integrable u volume) {f : Vec d → ℝ} (hf : IsBddLipFun f)
    {π : Fin d → Vec d → ℝ} {πn : ℕ → Fin d → Vec d → ℝ} {C : ℝ≥0}
    (hC : ∀ n i, IsEuclLipschitzWith C (πn n i))
    (hlim : ∀ i x, Tendsto (fun n => πn n i x) atTop (𝓝 (π i x))) :
    Tendsto (fun n => usharp u f (πn n)) atTop (𝓝 (usharp u f π)) := by
  have hg : Integrable (fun x => f x * u x) volume := by
    obtain ⟨hfL, Cf, hCf⟩ := hf
    exact (hu.bdd_mul (lipFun_continuous hfL).aestronglyMeasurable
      (c := Cf) (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hCf x))
  have := (wstar hC (fun x i => hlim i x)).2 d id id Function.injective_id _ hg
  simpa [usharp, minorDet_full] using this

end AFree
