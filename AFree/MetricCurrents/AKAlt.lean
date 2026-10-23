module

public import AFree.MetricCurrents.AKChain1
public import AFree.MetricCurrents.AKAltAux
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Alternation [AK, Theorem 3.5]

For a metric current `T ∈ M_k(ℝ^d)`: `T(h, π) = 0` if two slots coincide, and `T(h, Aπ) = det A · T(h, π)`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AKChainAux AKAltAux

/-- The auxiliary function `φ`: it is `C¹`,
`φ(n) = n` for `n ∈ ℤ`, `0 ≤ φ' ≤ ϖ` with a constant `ϖ` (`≤ 3.15`; only some absolute bound is used),
`|φ(t) - t| ≤ 1/2`, and `φ'(s) φ'(s + 1/2) = 0` for all `s`. The half-window bump
`φ' = π max(0, cos 2πs)` is used.) -/
theorem akalt_aux_phi :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ (∀ n : ℤ, φ n = n) ∧ (∀ s, 0 ≤ deriv φ s) ∧
      (∃ ϖ : ℝ, ∀ s, deriv φ s ≤ ϖ) ∧ (∀ t, |φ t - t| ≤ 1 / 2) ∧
      ∀ s, deriv φ s * deriv φ (s + 1 / 2) = 0 :=
  exists_phi

private lemma akExt_zero_fun {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent k T) {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) :
    akExt T (fun _ => 0) π = 0 := by
  have hb : IsBorelBdd (fun _ : Vec d => (0 : ℝ)) := ⟨measurable_const, 0, by simp⟩
  have key := (akext hT).1.2.1 π hπ _ _ hb hb 0 0
  have e : ((0 : ℝ) • (fun _ : Vec d => (0 : ℝ)) + (0 : ℝ) • (fun _ : Vec d => (0 : ℝ))) =
      fun _ => 0 := by funext x; simp
  rw [e] at key
  simpa using key

/-- (a) `π_i = π_j` for some `i ≠ j` implies `T(h, π) = 0`. -/
theorem akalt_repeated_slot {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent k T) {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) {i j : Fin k}
    (hij : i ≠ j) (hπij : π i = π j) {h : Vec d → ℝ} (hh : IsBorelBdd h) : akExt T h π = 0 := by
  classical
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.2 fun h0 => by subst h0; exact i.elim0
  obtain ⟨φ, hφ, -, hφnn, ⟨ϖ, hϖ⟩, hφc, hφp⟩ := akalt_aux_phi
  have hbd : ∀ s, |deriv φ s| ≤ ϖ := fun s => by rw [abs_of_nonneg (hφnn s)]; exact hϖ s
  have hbds : ∀ (n : ℕ) (a s : ℝ), |deriv (scl φ n a) s| ≤ ϖ := fun n a s => by
    rw [deriv_scl hφ]; exact hbd _
  have hconv_scl : ∀ (a x : ℝ), Tendsto (fun n : ℕ => scl φ n a x) atTop (𝓝 x) := by
    intro a x
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (g := fun n : ℕ => (1 / 2 + |a|) * (1 / ((n : ℝ) + 1))) ?_
    · rw [Real.dist_eq]
      calc _ ≤ _ := abs_scl_sub_le hφc n a x
        _ = _ := by ring
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 + |a|)
  suffices H : ∀ f, IsBddLipFun f → T f π = 0 by
    obtain ⟨μ, hμ⟩ : ∃ μ, IsAKMass T μ := ⟨akMassMeasure T, akMassMeasure_isAKMass hT⟩
    have : IsFiniteMeasure μ := hμ.1.1
    obtain ⟨f, hf, hlim⟩ := exists_lip_approx_borelBdd μ hh
    have key := (akext hT).2.2.2.2 μ hμ f h hf hh hlim π hπ
    have h0 : (fun n => T (f n) π) = fun _ => 0 := funext fun n => H _ (hf n)
    rw [h0] at key
    exact (tendsto_nhds_unique tendsto_const_nhds key).symm
  intro f hf
  have hfB := isBorelBdd_of_isBddLipFun hf
  choose K hK using hπ
  have hπ : IsLipTuple π := fun l => ⟨K l, hK l⟩
  let π' : ℕ → Fin k → Vec d → ℝ := fun n => Function.update π i (fun x => scl φ n 0 (π i x))
  let πn : ℕ → Fin k → Vec d → ℝ := fun n =>
    Function.update (π' n) j (fun x => scl φ n (1 / 2) (π' n j x))
  have hπ'j : ∀ n, π' n j = π j := fun n => Function.update_of_ne hij.symm _ _
  have hπ'lip : ∀ n, IsLipTuple (π' n) := fun n =>
    (akchain1 hk hT i (contDiff_scl hφ n 0) ⟨ϖ, hbds n 0⟩ hπ hfB).1
  have hcd : ∀ (n : ℕ) (a : ℝ), Continuous (deriv (scl φ n a)) := fun n a =>
    (contDiff_scl hφ n a).continuous_deriv le_rfl
  have hw : ∀ n, IsBorelBdd (fun x => f x * deriv (scl φ n (1 / 2)) (π' n j x)) := fun n =>
    isBorelBdd_mul hfB ((hcd n _).comp (by rw [hπ'j]; exact continuous_of_lip (hK j))).measurable
      (fun x => hbds n _ _)
  have hT0 : ∀ n, T f (πn n) = 0 := by
    intro n
    have ak1 := akchain1 hk hT j (contDiff_scl hφ n (1 / 2)) ⟨ϖ, hbds n _⟩ (hπ'lip n) hfB
    have ak2 := akchain1 hk hT i (contDiff_scl hφ n 0) ⟨ϖ, hbds n 0⟩ hπ (hw n)
    have hz : (fun x => f x * deriv (scl φ n (1 / 2)) (π' n j x) * deriv (scl φ n 0) (π i x)) =
        fun _ => 0 := by
      funext x
      have e : π' n j x = π i x := by rw [hπ'j, hπij]
      rw [e, deriv_scl hφ, deriv_scl hφ]
      have h1 := hφp (((n : ℝ) + 1) * π i x)
      rw [add_zero]
      calc _ = f x * (deriv φ (((n : ℝ) + 1) * π i x) *
            deriv φ (((n : ℝ) + 1) * π i x + 1 / 2)) := by ring
        _ = 0 := by rw [h1, mul_zero]
    have := (akext hT).1.1 f hf (πn n) ak1.1
    rw [← this, ak1.2, ak2.2, hz]
    exact akExt_zero_fun hT hπ
  have hπn : ∀ n l x, πn n l x =
      if l = j then scl φ n (1 / 2) (π i x) else if l = i then scl φ n 0 (π i x) else π l x := by
    intro n l x
    by_cases hlj : l = j
    · subst hlj
      simp [πn, π', Function.update_of_ne hij.symm, hπij]
    · by_cases hli : l = i
      · subst hli
        simp [πn, π', hlj]
      · simp [πn, π', hlj, hli]
  have hlipn : ∀ n l, IsEuclLipschitzWith (Real.toNNReal ϖ * K i + ∑ l, K l) (πn n l) := by
    intro n l
    have hc : ∀ a, IsEuclLipschitzWith (Real.toNNReal ϖ * K i) (fun x => scl φ n a (π i x)) :=
      fun a => lip_comp (lipschitzWith_of_deriv_bdd (contDiff_scl hφ n a) (hbds n a)) (hK i)
    by_cases hlj : l = j
    · have hfun : πn n l = fun x => scl φ n (1 / 2) (π i x) :=
        funext fun x => by rw [hπn]; split_ifs; rfl
      rw [hfun]
      exact lip_mono (hc _) le_self_add
    · by_cases hli : l = i
      · have hfun : πn n l = fun x => scl φ n 0 (π i x) :=
          funext fun x => by rw [hπn]; split_ifs; rfl
        rw [hfun]
        exact lip_mono (hc _) le_self_add
      · have hfun : πn n l = π l := funext fun x => by rw [hπn]; split_ifs; rfl
        rw [hfun]
        exact lip_mono (hK l) (le_add_left (Finset.single_le_sum (fun _ _ => bot_le)
          (Finset.mem_univ l)))
  have hconv : ∀ l x, Tendsto (fun n => πn n l x) atTop (𝓝 (π l x)) := by
    intro l x
    simp only [hπn]
    by_cases hlj : l = j
    · subst hlj
      simpa [hπij] using hconv_scl (1 / 2) (π i x)
    · by_cases hli : l = i
      · subst hli
        simpa [hlj] using hconv_scl 0 (π l x)
      · simp [hlj, hli]
  have key := hT.2.2.2.2.1 f hf π hπ πn ⟨_, hlipn⟩ hconv
  simp only [hT0] at key
  exact (tendsto_nhds_unique tendsto_const_nhds key).symm

/-- (c) `T(h, Aπ) = det A · T(h, π)` for every `A ∈ ℝ^{k×k}`. -/
theorem akalt_matrix {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent k T) {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π)
    (A : Matrix (Fin k) (Fin k) ℝ) {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    akExt T h (matAct A π) = A.det * akExt T h π := by
  classical
  let Ψ : (Fin k → Fin k → ℝ) → Fin k → Vec d → ℝ := fun c i x => ∑ l, c i l * π l x
  have hΨ : ∀ c, IsLipTuple (Ψ c) := fun c i =>
    isLipFun_sum _ _ fun l _ => isLipFun_const_mul _ (hπ l)
  have hrow : ∀ (v : Fin k → ℝ), IsLipFun (fun x => ∑ l, v l * π l x) := fun v =>
    isLipFun_sum _ _ fun l _ => isLipFun_const_mul _ (hπ l)
  have hupd : ∀ [DecidableEq (Fin k)] (c : Fin k → Fin k → ℝ) (i : Fin k) (v : Fin k → ℝ),
      Ψ (Function.update c i v) = Function.update (Ψ c) i (fun x => ∑ l, v l * π l x) := by
    intro _ c i v
    funext i' x
    by_cases hi : i' = i
    · subst hi; simp [Ψ]
    · simp [Ψ, hi]
  let Φ : MultilinearMap ℝ (fun _ : Fin k => Fin k → ℝ) ℝ :=
    { toFun := fun c => akExt T h (Ψ c)
      map_update_add' := by
        intro inst c i x y
        obtain rfl := Subsingleton.elim inst (instDecidableEqFin k)
        show akExt T h (Ψ (Function.update c i (x + y))) =
          akExt T h (Ψ (Function.update c i x)) + akExt T h (Ψ (Function.update c i y))
        rw [hupd, hupd, hupd]
        have e : (fun z => ∑ l, (x + y) l * π l z) =
            fun z => (∑ l, x l * π l z) + ∑ l, y l * π l z := by
          funext z; simp [add_mul, Finset.sum_add_distrib]
        rw [e]
        exact akExt_update_add hT hh (hΨ c) i (hrow x) (hrow y)
      map_update_smul' := by
        intro inst c i a x
        obtain rfl := Subsingleton.elim inst (instDecidableEqFin k)
        show akExt T h (Ψ (Function.update c i (a • x))) =
          a • akExt T h (Ψ (Function.update c i x))
        rw [hupd, hupd, smul_eq_mul]
        have e : (fun z => ∑ l, (a • x) l * π l z) = fun z => a * ∑ l, x l * π l z := by
          funext z; simp [Finset.mul_sum, mul_assoc]
        rw [e]
        exact akExt_update_smul hT hh (hΨ c) i (hrow x) a }
  let Φa : (Fin k → ℝ) [⋀^Fin k]→ₗ[ℝ] ℝ :=
    { toMultilinearMap := Φ
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        have : Ψ v i = Ψ v j := by funext x; simp [Ψ, hv]
        exact akalt_repeated_slot hT (hΨ v) hij this hh }
  have key := DFunLike.congr_fun (AlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin k)) Φa) A
  have key : Φa A = Φa (fun i => (Pi.basisFun ℝ (Fin k)) i) *
      (Pi.basisFun ℝ (Fin k)).det A := key
  have hd : (Pi.basisFun ℝ (Fin k)).det A = A.det :=
    (Pi.basisFun_det_apply (R := ℝ) (ι := Fin k) A).trans rfl
  rw [hd] at key
  have e1 : Ψ (fun i => (Pi.basisFun ℝ (Fin k)) i) = π := by
    funext i x
    simp [Ψ, Pi.single_apply]
  have e2 : Φa A = akExt T h (matAct A π) := rfl
  have e3 : Φa (fun i => (Pi.basisFun ℝ (Fin k)) i) = akExt T h π := by
    show akExt T h (Ψ _) = _
    rw [e1]
  rw [e3, e2] at key
  rw [key]
  simp [mul_comm]

end AFree
