module

public import AFree.Curves.Exhaust.Span
public import AFree.Curves.Exhaust.Prop

/-!
# Absolute continuity from cone-null sets

A finite measure vanishing on compact cone-null sets for `d` orthonormal axes is absolutely
continuous.
-/

@[expose] public section

open MeasureTheory Set

namespace AFree

open PDE

variable {d : ℕ}

/-- A finite measure vanishing on compact subsets of a Borel `N` vanishes on `N`. -/
private lemma measure_eq_zero_of_compact_null {μ : Measure (Vec d)} [IsFiniteMeasure μ]
    {N : Set (Vec d)} (hN : MeasurableSet N) (h : ∀ K, K ⊆ N → IsCompact K → μ K = 0) :
    μ N = 0 := by
  rw [hN.measure_eq_iSup_isCompact]
  simp only [ENNReal.iSup_eq_zero]
  exact fun K hK hc => h K hK hc

/-- `μ ≪ ν` from `μ⌞Nᶜ ≪ ν` and `μ N = 0`. -/
private lemma absolutelyContinuous_of_restrict_compl {μ ν : Measure (Vec d)} {N : Set (Vec d)}
    (hN : MeasurableSet N) (h0 : μ N = 0) (h : μ.restrict Nᶜ ≪ ν) : μ ≪ ν := by
  intro s hs
  have h1 : μ.restrict Nᶜ s = 0 := h hs
  rw [Measure.restrict_apply' hN.compl] at h1
  refine measure_mono_null (t := (s ∩ Nᶜ) ∪ N) (fun x hx => ?_) (measure_union_null h1 h0)
  by_cases hxN : x ∈ N
  · exact Or.inr hxN
  · exact Or.inl ⟨hx, hxN⟩

/-- For `d ≥ 1` there is `α_d > 0`
(namely `1/(2√d)`) such that every finite measure `μ` on `ℝ^d` with `μ(K) = 0` for each `i` and
each compact `C(e_i, α)`-null set `K`, for orthonormal `e_1, …, e_d` and `α ∈ (0, α_d]`, is
absolutely continuous with respect to Lebesgue measure. -/
theorem conenull_ac (hd : 0 < d) :
    ∃ αd : ℝ, 0 < αd ∧ ∀ (μ : Measure (Vec d)) [IsFiniteMeasure μ] (e : Fin d → Vec d),
      (∀ i j, vecDot (e i) (e j) = if i = j then 1 else 0) → ∀ α : ℝ, 0 < α → α ≤ αd →
      (∀ (i : Fin d) (K : Set (Vec d)), IsCompact K → IsCNull (cone (e i) α) K → μ K = 0) →
        μ ≪ volume := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hdr
  refine ⟨1 / (2 * Real.sqrt d), by positivity, fun μ _ e he α hα hαd hK => ?_⟩
  have hs1 : 1 ≤ Real.sqrt d := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt d := Real.sqrt_le_sqrt (by exact_mod_cast hd)
  have hα2 : α < Real.pi / 2 := by
    have : 1 / (2 * Real.sqrt d) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith [Real.pi_gt_three]
  have hunit : ∀ i, vecEuclideanNorm (e i) = 1 := vecEuclideanNorm_eq_one_of_orthonormal he
  choose ρ N hρ hNm hNnull hNac using fun i => exhaust_prop (hunit i) hα hα2 μ
  have hac : ∀ i, μ.restrict univ ≪ curveMix (ccurveSpace (e i) α) (ρ i) := fun i => by
    rw [Measure.restrict_univ]
    refine absolutelyContinuous_of_restrict_compl (hNm i) ?_ (hNac i)
    exact measure_eq_zero_of_compact_null (hNm i) fun K hKN hKc =>
      hK i K hKc ((hNnull i).mono hKN)
  have := hρ
  have := spanac_prop (μ := μ) (P := univ) (w := e) hunit (η := 1)
    (fun a => by rw [vecEuclideanNorm_sum_smul_orthonormal he a, one_mul])
    (β := fun _ => α) (fun _ => ⟨hα, hα2⟩) (fun _ => by
      have : Real.sqrt d * α ≤ 1 / 2 := by
        calc Real.sqrt d * α ≤ Real.sqrt d * (1 / (2 * Real.sqrt d)) := by gcongr
          _ = 1 / 2 := by field_simp
      linarith) ρ hac
  rwa [Measure.restrict_univ] at this

end AFree
