module

public import AFree.Paper.OrderK.BlowUpSystem
public import AFree.Paper.OrderK.StrongConstancyEnd

/-!
# The cut-off system of order `k`

The sequence form of the cut-off lemma, with the output exactly in the shape of the hypotheses of
strong constancy of order `k`: `w_j = χ u_j`, the explicit
`G_j^{(α)} = -χ(Ā_α V_j + Y_{j,α,α})`, and lower-order `H_{j,β}`.
-/

@[expose] public section

open MeasureTheory PDE Matrix Filter Topology

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem integral_abs_mul_cut_le {χ f : Vec d → ℝ} (hχ : Continuous χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x, χ x ≤ 1) (hχs : tsupport χ ⊆ euclideanBall (0 : Vec d) (3 / 4))
    (hf : Continuous f) :
    ∫ x, |χ x * f x| ≤ ∫ x in euclideanBall (0 : Vec d) (7 / 8), |f x| := by
  have hS : MeasurableSet (euclideanBall (0 : Vec d) (7 / 8)) := measurableSet_euclideanBall _ _
  have hzero : ∀ x ∉ euclideanBall (0 : Vec d) (7 / 8), |χ x * f x| = 0 := by
    intro x hx
    have : x ∉ tsupport χ := fun h =>
      hx (euclideanBall_mono (by norm_num) (by norm_num) (hχs h))
    simp [image_eq_zero_of_notMem_tsupport this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine setIntegral_mono_on
    (integrableOn_euclideanBall_of_continuous (hχ.mul hf).abs (by norm_num) (by norm_num))
    (integrableOn_euclideanBall_of_continuous hf.abs (by norm_num) (by norm_num)) hS
    fun x _ => ?_
  rw [abs_mul, abs_of_nonneg (hχ0 x)]
  exact mul_le_of_le_one_left (abs_nonneg _) (hχ1 x)

theorem setIntegral_abs_apply_le {κ' : Type*} [Fintype κ'] {v : Vec d → κ' → ℝ}
    (hv : ∀ c, Continuous fun x => v x c) (c : κ') :
    ∫ x in euclideanBall (0 : Vec d) (7 / 8), |v x c| ≤
      ∫ x in euclideanBall (0 : Vec d) (7 / 8), piEuclideanNorm (v x) := by
  have hc : Continuous fun x => piEuclideanNorm (v x) :=
    continuous_piEuclideanNorm.comp (continuous_pi hv)
  exact setIntegral_mono_on
    (integrableOn_euclideanBall_of_continuous (hv c).abs (by norm_num) (by norm_num))
    (integrableOn_euclideanBall_of_continuous hc (by norm_num) (by norm_num))
    (measurableSet_euclideanBall _ _) fun x _ => abs_le_piEuclideanNorm _ c

omit [Fintype κ] in
theorem integral_abs_systemG_le {χ : Vec d → ℝ} (Abar : (Fin d → ℕ) → Matrix κ ι ℝ)
    {V : Vec d → ι → ℝ} {Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ}
    (hχ : Continuous χ) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hχs : tsupport χ ⊆ euclideanBall (0 : Vec d) (3 / 4))
    (hV : ∀ i, Continuous fun x => V x i) (hY : ∀ α β c, Continuous fun x => Y α β x c)
    {δ η : ℝ} (hVδ : ∀ i, ∫ x in euclideanBall (0 : Vec d) (7 / 8), |V x i| ≤ δ)
    (α : Fin d → ℕ) (c : κ)
    (hYη : ∫ x in euclideanBall (0 : Vec d) (7 / 8), |Y α α x c| ≤ η) :
    ∫ x, |systemG χ Abar V Y α x c| ≤ (∑ i, |Abar α c i|) * δ + η := by
  have hS := measurableSet_euclideanBall (0 : Vec d) (7 / 8)
  set S : Vec d → ℝ := fun x => ∑ i, Abar α c i * V x i + Y α α x c with hSdef
  have hSc : Continuous S :=
    (continuous_finsetSum _ fun i _ => continuous_const.mul (hV i)).add (hY α α c)
  have e : (fun x => |systemG χ Abar V Y α x c|) = fun x => |χ x * S x| := by
    funext x; simp only [systemG, abs_neg, hSdef]
  rw [e]
  refine (integral_abs_mul_cut_le hχ hχ0 hχ1 hχs hSc).trans ?_
  have hint : ∀ i, IntegrableOn (fun x => |Abar α c i * V x i|)
      (euclideanBall (0 : Vec d) (7 / 8)) volume := fun i =>
    integrableOn_euclideanBall_of_continuous (continuous_const.mul (hV i)).abs
      (by norm_num) (by norm_num)
  have hVi : ∀ i, IntegrableOn (fun x => |V x i|) (euclideanBall (0 : Vec d) (7 / 8)) volume :=
    fun i => integrableOn_euclideanBall_of_continuous (hV i).abs (by norm_num) (by norm_num)
  have hYi : IntegrableOn (fun x => |Y α α x c|) (euclideanBall (0 : Vec d) (7 / 8)) volume :=
    integrableOn_euclideanBall_of_continuous (hY α α c).abs (by norm_num) (by norm_num)
  calc ∫ x in euclideanBall (0 : Vec d) (7 / 8), |S x|
      ≤ ∫ x in euclideanBall (0 : Vec d) (7 / 8),
          (∑ i, |Abar α c i| * |V x i| + |Y α α x c|) := by
        refine setIntegral_mono_on
          (integrableOn_euclideanBall_of_continuous hSc.abs (by norm_num) (by norm_num))
          ((integrable_finsetSum _ fun i _ => (hVi i).const_mul (|Abar α c i|)).add hYi) hS
          fun x _ => ?_
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => abs_mul _ _
    _ = (∑ i, |Abar α c i| * ∫ x in euclideanBall (0 : Vec d) (7 / 8), |V x i|) +
          ∫ x in euclideanBall (0 : Vec d) (7 / 8), |Y α α x c| := by
        rw [integral_add (integrable_finsetSum _ fun i _ => (hVi i).const_mul (|Abar α c i|)) hYi,
          integral_finsetSum _ fun i _ => (hVi i).const_mul (|Abar α c i|)]
        simp only [integral_const_mul]
    _ ≤ (∑ i, |Abar α c i|) * δ + η := by
        rw [Finset.sum_mul]
        exact add_le_add (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hVδ i) (abs_nonneg _)) hYη

theorem sumL1_systemG_le {k : ℕ} {χ : Vec d → ℝ} (Abar : (Fin d → ℕ) → Matrix κ ι ℝ)
    {V : Vec d → ι → ℝ} {Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ}
    (hχ : Continuous χ) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hχs : tsupport χ ⊆ euclideanBall (0 : Vec d) (3 / 4))
    (hχc : HasCompactSupport χ)
    (hV : ∀ i, Continuous fun x => V x i) (hY : ∀ α β c, Continuous fun x => Y α β x c)
    {δ η : ℝ} (hVδ : ∀ i, ∫ x in euclideanBall (0 : Vec d) (7 / 8), |V x i| ≤ δ)
    (hYη : ∀ α, multiAbs α = k → ∀ c,
      ∫ x in euclideanBall (0 : Vec d) (7 / 8), |Y α α x c| ≤ η) :
    sumL1 k (systemG χ Abar V Y) ≤
      (∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ c, ∑ i, |Abar α c i|) * δ +
        (∑ _α ∈ Finset.Nat.antidiagonalTuple d k, ∑ _c : κ, (1 : ℝ)) * η := by
  unfold sumL1
  have hint : ∀ α c, Integrable (fun x => systemG χ Abar V Y α x c) := fun α c => by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hχ.mul ((continuous_finsetSum _ fun i _ => continuous_const.mul (hV i)).add
        (hY α α c))).neg
    · exact IsCompact.of_isClosed_subset hχc (isClosed_tsupport _) (tsupport_systemG_subset Abar V Y α c)
  rw [Finset.sum_mul, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun α hα => ?_
  have hαk : multiAbs α = k := by
    rw [Finset.Nat.mem_antidiagonalTuple] at hα; exact hα
  calc ∫ x, piEuclideanNorm (systemG χ Abar V Y α x)
      ≤ ∑ c, ∫ x, |systemG χ Abar V Y α x c| := by
        rw [← integral_finsetSum _ fun c _ => (hint α c).abs]
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
          piEuclideanNorm_nonneg _) (integrable_finsetSum _ fun c _ => (hint α c).abs)
          (Filter.Eventually.of_forall fun x => piEuclideanNorm_le_sum_abs _)
    _ ≤ ∑ c, ((∑ i, |Abar α c i|) * δ + η) :=
        Finset.sum_le_sum fun c _ =>
          integral_abs_systemG_le Abar hχ hχ0 hχ1 hχs hV hY hVδ α c (hYη α hαk c)
    _ = (∑ c, ∑ i, |Abar α c i|) * δ + (∑ _c : κ, (1 : ℝ)) * η := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
        simp only [one_mul]

end

end AFree
