module

public import AFree.MetricCurrents.AKBasic
public import AFree.MetricCurrents.AKExtAux

/-!
# The extension to bounded Borel functions [AK, (2.3)]
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents.AKExt

variable {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}

namespace MetricCurrents.AKExt

private theorem mass_unique (hT : IsMetricCurrent k T) {μ : Measure (Vec d)} (hμ : IsAKMass T μ) :
    μ = akMassMeasure T :=
  le_antisymm (hμ.2 _ (akMassMeasure_isAKMass hT).1) ((akMassMeasure_isAKMass hT).2 _ hμ.1)

private theorem approx_exists (hT : IsMetricCurrent k T) {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    ∃ f : ℕ → Vec d → ℝ, (∀ n, IsBddLipFun (f n)) ∧
      Tendsto (fun n => ∫ x, |f n x - h x| ∂akMassMeasure T) atTop (𝓝 0) := by
  have : IsFiniteMeasure (akMassMeasure T) := (akMassMeasure_isAKMass hT).1.1
  exact exists_lip_approx_borelBdd _ hh

private theorem akApprox_spec (hT : IsMetricCurrent k T) {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    (∀ n, IsBddLipFun (akApprox (akMassMeasure T) h n)) ∧
      Tendsto (fun n => ∫ x, |akApprox (akMassMeasure T) h n x - h x| ∂akMassMeasure T) atTop
        (𝓝 0) := by
  have H := approx_exists hT hh
  unfold akApprox
  simp only [H, ↓reduceDIte]
  exact H.choose_spec

/-- Triangle estimate for two Lipschitz approximants. -/
private theorem dist_le (hT : IsMetricCurrent k T) {h : Vec d → ℝ} (hh : IsBorelBdd h)
    {u v : Vec d → ℝ} (hu : IsBddLipFun u) (hv : IsBddLipFun v) {π : Fin k → Vec d → ℝ}
    {K : Fin k → ℝ≥0} (hK : ∀ i, IsEuclLipschitzWith (K i) (π i)) :
    |T u π - T v π| ≤ (∏ i, (K i : ℝ)) *
      (∫ x, |u x - h x| ∂akMassMeasure T + ∫ x, |v x - h x| ∂akMassMeasure T) := by
  have : IsFiniteMeasure (akMassMeasure T) := (akMassMeasure_isAKMass hT).1.1
  have hP : 0 ≤ ∏ i, (K i : ℝ) := Finset.prod_nonneg fun i _ => (K i).2
  refine (akbasic_abs_sub_le hT (akMassMeasure_isAKMass hT).1 hu hv hK).trans
    (mul_le_mul_of_nonneg_left ?_ hP)
  have i1 := (integrable_of_borelBdd (borelBdd_sub (borelBdd_of_bddLip hu) hh) (akMassMeasure T)).abs
  have i2 := (integrable_of_borelBdd (borelBdd_sub (borelBdd_of_bddLip hv) hh) (akMassMeasure T)).abs
  rw [← integral_add i1 i2]
  refine integral_mono ((integrable_of_borelBdd
    (borelBdd_sub (borelBdd_of_bddLip hu) (borelBdd_of_bddLip hv)) (akMassMeasure T)).abs) (i1.add i2) fun x => ?_
  calc |u x - v x| = |(u x - h x) - (v x - h x)| := by ring_nf
    _ ≤ |u x - h x| + |v x - h x| := abs_sub _ _

/-- The core limit statement: `T(f_n, π) → akExt T h π` along any `L¹(μ_T)`-approximation. -/
theorem tendsto_of_approx (hT : IsMetricCurrent k T) {h : Vec d → ℝ} (hh : IsBorelBdd h)
    {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) {f : ℕ → Vec d → ℝ}
    (hf : ∀ n, IsBddLipFun (f n))
    (hlim : Tendsto (fun n => ∫ x, |f n x - h x| ∂akMassMeasure T) atTop (𝓝 0)) :
    Tendsto (fun n => T (f n) π) atTop (𝓝 (akExt T h π)) := by
  choose K hK using hπ
  have hP : 0 ≤ ∏ i, (K i : ℝ) := Finset.prod_nonneg fun i _ => (K i).2
  obtain ⟨hg, hglim⟩ := akApprox_spec hT hh
  set g := akApprox (akMassMeasure T) h with hgdef
  have hcauchy : CauchySeq fun n => T (g n) π := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have ht : Tendsto (fun n => (∏ i, (K i : ℝ)) * (∫ x, |g n x - h x| ∂akMassMeasure T))
        atTop (𝓝 0) := by
      simpa using hglim.const_mul (∏ i, (K i : ℝ))
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 ht) (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm
    have h2 := hN n hn
    have hnn : ∀ j, 0 ≤ (∏ i, (K i : ℝ)) * ∫ x, |g j x - h x| ∂akMassMeasure T := fun j =>
      mul_nonneg hP (integral_nonneg fun x => abs_nonneg _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn m)] at h1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn n)] at h2
    rw [Real.dist_eq]
    calc |T (g m) π - T (g n) π| ≤ (∏ i, (K i : ℝ)) * (∫ x, |g m x - h x| ∂akMassMeasure T +
          ∫ x, |g n x - h x| ∂akMassMeasure T) := dist_le hT hh (hg m) (hg n) hK
      _ < ε := by rw [mul_add]; linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hext : akExt T h π = L := hL.limUnder_eq
  rw [hext]
  have hdiff : Tendsto (fun n => T (f n) π - T (g n) π) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => (∏ i, (K i : ℝ)) * (∫ x, |f n x - h x| ∂akMassMeasure T +
        ∫ x, |g n x - h x| ∂akMassMeasure T)) atTop (𝓝 0) := by
      simpa using (hlim.add hglim).const_mul (∏ i, (K i : ℝ))
    refine squeeze_zero_norm (fun n => ?_) hb
    rw [Real.norm_eq_abs]
    exact dist_le hT hh (hf n) (hg n) hK
  simpa using hdiff.add hL

variable {π : Fin k → Vec d → ℝ}

theorem ext_eq_of_bddLip (hT : IsMetricCurrent k T) {f : Vec d → ℝ} (hf : IsBddLipFun f)
    (hπ : IsLipTuple π) : akExt T f π = T f π := by
  have := tendsto_of_approx hT (borelBdd_of_bddLip hf) hπ (f := fun _ => f) (fun _ => hf)
    (by simp)
  exact tendsto_nhds_unique this tendsto_const_nhds

theorem ext_abs_le (hT : IsMetricCurrent k T) {μ : Measure (Vec d)} (hμ : IsAKMassAdmissible T μ)
    {h : Vec d → ℝ} (hh : IsBorelBdd h) {K : Fin k → ℝ≥0}
    (hK : ∀ i, IsEuclLipschitzWith (K i) (π i)) :
    |akExt T h π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |h x| ∂μ := by
  have : IsFiniteMeasure μ := hμ.1
  have hμT := akMassMeasure_isAKMass hT
  have : IsFiniteMeasure (akMassMeasure T) := hμT.1.1
  have hP : 0 ≤ ∏ i, (K i : ℝ) := Finset.prod_nonneg fun i _ => (K i).2
  obtain ⟨f, hf, hl⟩ := approx_exists hT hh
  have tend := tendsto_of_approx hT hh (fun i => ⟨K i, hK i⟩) hf hl
  have hle : akMassMeasure T ≤ μ := hμT.2 μ hμ
  have hint : Integrable (fun x => |h x|) μ := (integrable_of_borelBdd hh μ).abs
  have hmono : ∫ x, |h x| ∂akMassMeasure T ≤ ∫ x, |h x| ∂μ :=
    integral_mono_measure hle (Filter.Eventually.of_forall fun x => abs_nonneg _) hint
  have bound : ∀ n, |T (f n) π| ≤ (∏ i, (K i : ℝ)) *
      (∫ x, |h x| ∂μ + ∫ x, |f n x - h x| ∂akMassMeasure T) := by
    intro n
    refine (hμT.1.2 (f n) (hf n) π K hK).trans (mul_le_mul_of_nonneg_left ?_ hP)
    have i1 := (integrable_of_borelBdd hh (akMassMeasure T)).abs
    have i2 := (integrable_of_borelBdd (borelBdd_sub (borelBdd_of_bddLip (hf n)) hh)
      (akMassMeasure T)).abs
    have : ∫ x, |f n x| ∂akMassMeasure T ≤ ∫ x, |h x| ∂akMassMeasure T +
        ∫ x, |f n x - h x| ∂akMassMeasure T := by
      rw [← integral_add i1 i2]
      refine integral_mono (integrable_of_borelBdd (borelBdd_of_bddLip (hf n)) _).abs
        (i1.add i2) fun x => ?_
      calc |f n x| = |h x + (f n x - h x)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have hr : Tendsto (fun n => (∏ i, (K i : ℝ)) *
      (∫ x, |h x| ∂μ + ∫ x, |f n x - h x| ∂akMassMeasure T)) atTop
      (𝓝 ((∏ i, (K i : ℝ)) * (∫ x, |h x| ∂μ + 0))) :=
    (tendsto_const_nhds.add hl).const_mul _
  simpa using le_of_tendsto_of_tendsto' tend.abs hr bound

theorem ext_lin (hT : IsMetricCurrent k T) (hπ : IsLipTuple π) {h g : Vec d → ℝ}
    (hh : IsBorelBdd h) (hg : IsBorelBdd g) (a b : ℝ) :
    akExt T (a • h + b • g) π = a * akExt T h π + b * akExt T g π := by
  have hC1 := hT.2.2.1
  have : IsFiniteMeasure (akMassMeasure T) := (akMassMeasure_isAKMass hT).1.1
  obtain ⟨f, hf, hfl⟩ := approx_exists hT hh
  obtain ⟨f', hf', hfl'⟩ := approx_exists hT hg
  have hnew : ∀ n, IsBddLipFun (a • f n + b • f' n) := fun n =>
    bddLip_add (bddLip_smul (hf n) a) (bddLip_smul (hf' n) b)
  have hlim : Tendsto (fun n => ∫ x, |(a • f n + b • f' n) x - (a • h + b • g) x|
      ∂akMassMeasure T) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => |a| * ∫ x, |f n x - h x| ∂akMassMeasure T +
        |b| * ∫ x, |f' n x - g x| ∂akMassMeasure T) atTop (𝓝 0) := by
      simpa using (hfl.const_mul |a|).add (hfl'.const_mul |b|)
    refine squeeze_zero (fun n => integral_nonneg fun x => abs_nonneg _) (fun n => ?_) hb
    have i1 := (integrable_of_borelBdd (borelBdd_sub (borelBdd_of_bddLip (hf n)) hh)
      (akMassMeasure T)).abs.const_mul |a|
    have i2 := (integrable_of_borelBdd (borelBdd_sub (borelBdd_of_bddLip (hf' n)) hg)
      (akMassMeasure T)).abs.const_mul |b|
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2]
    refine integral_mono (integrable_of_borelBdd (borelBdd_sub
      (borelBdd_of_bddLip (hnew n)) (borelBdd_add (borelBdd_smul hh a) (borelBdd_smul hg b)))
      _).abs (i1.add i2) fun x => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * f n x + b * f' n x - (a * h x + b * g x)|
        = |a * (f n x - h x) + b * (f' n x - g x)| := by ring_nf
      _ ≤ |a * (f n x - h x)| + |b * (f' n x - g x)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]
  have t1 := tendsto_of_approx hT (borelBdd_add (borelBdd_smul hh a) (borelBdd_smul hg b)) hπ
    hnew hlim
  have t2 := tendsto_of_approx hT hh hπ hf hfl
  have t3 := tendsto_of_approx hT hg hπ hf' hfl'
  have e : (fun n => T (a • f n + b • f' n) π) = fun n => a * T (f n) π + b * T (f' n) π :=
    funext fun n => hC1 π hπ _ _ (hf n) (hf' n) a b
  rw [e] at t1
  exact tendsto_nhds_unique t1 ((t2.const_mul a).add (t3.const_mul b))

theorem ext_slot_lin (hT : IsMetricCurrent k T) {h : Vec d → ℝ} (hh : IsBorelBdd h)
    (hπ : IsLipTuple π) (i : Fin k) {ψ : Vec d → ℝ} (hψ : IsLipFun ψ) (a b : ℝ) :
    akExt T h (Function.update π i (a • π i + b • ψ)) =
      a * akExt T h π + b * akExt T h (Function.update π i ψ) := by
  have hC2 := hT.2.2.2.1
  obtain ⟨f, hf, hfl⟩ := by
    have : IsFiniteMeasure (akMassMeasure T) := (akMassMeasure_isAKMass hT).1.1
    exact approx_exists hT hh
  have hπ1 : IsLipTuple (Function.update π i (a • π i + b • ψ)) :=
    lipTuple_update hπ i (lip_add (lip_smul (hπ i) a) (lip_smul hψ b))
  have hπ2 := lipTuple_update hπ i hψ
  have t1 := tendsto_of_approx hT hh hπ1 hf hfl
  have t2 := tendsto_of_approx hT hh hπ hf hfl
  have t3 := tendsto_of_approx hT hh hπ2 hf hfl
  have e : (fun n => T (f n) (Function.update π i (a • π i + b • ψ))) =
      fun n => a * T (f n) π + b * T (f n) (Function.update π i ψ) :=
    funext fun n => hC2 _ (hf n) π hπ i ψ hψ a b
  rw [e] at t1
  exact tendsto_nhds_unique t1 ((t2.const_mul a).add (t3.const_mul b))

theorem ext_cont (hT : IsMetricCurrent k T) {μ : Measure (Vec d)} (hμ : IsAKMass T μ)
    {hn : ℕ → Vec d → ℝ} {h : Vec d → ℝ} (hhn : ∀ n, IsBorelBdd (hn n)) (hh : IsBorelBdd h)
    (hlim : Tendsto (fun n => ∫ x, |hn n x - h x| ∂μ) atTop (𝓝 0)) (hπ : IsLipTuple π) :
    Tendsto (fun n => akExt T (hn n) π) atTop (𝓝 (akExt T h π)) := by
  choose K hK using hπ
  have hπ' : IsLipTuple π := fun i => ⟨K i, hK i⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun n => (∏ i, (K i : ℝ)) * ∫ x, |hn n x - h x| ∂μ) atTop (𝓝 0) := by
    simpa using hlim.const_mul (∏ i, (K i : ℝ))
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
  have e := ext_lin hT hπ' (hhn n) hh 1 (-1)
  have e2 : (1 : ℝ) • hn n + (-1 : ℝ) • h = fun x => hn n x - h x := by
    funext x; simp [sub_eq_add_neg]
  rw [e2] at e
  rw [Real.norm_eq_abs, show akExt T (hn n) π - akExt T h π = akExt T (fun x => hn n x - h x) π
    by rw [e]; ring]
  exact ext_abs_le hT hμ.1 (borelBdd_sub (hhn n) hh) hK

theorem ext_ae (hT : IsMetricCurrent k T) {μ : Measure (Vec d)} (hμ : IsAKMass T μ)
    {h g : Vec d → ℝ} (hh : IsBorelBdd h) (hg : IsBorelBdd g) (hae : h =ᵐ[μ] g)
    (hπ : IsLipTuple π) : akExt T h π = akExt T g π := by
  choose K hK using hπ
  have hπ' : IsLipTuple π := fun i => ⟨K i, hK i⟩
  have e := ext_lin hT hπ' hh hg 1 (-1)
  have e2 : (1 : ℝ) • h + (-1 : ℝ) • g = fun x => h x - g x := by
    funext x; simp [sub_eq_add_neg]
  rw [e2] at e
  have h0 : ∫ x, |h x - g x| ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with x hx
    simp [hx]
  have := ext_abs_le hT hμ.1 (borelBdd_sub hh hg) hK
  rw [h0, mul_zero, abs_nonpos_iff, e] at this
  linarith

theorem ext_unique (hT : IsMetricCurrent k T) {Tb : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}
    (hTb : IsAKExtension T Tb) {h : Vec d → ℝ} (hh : IsBorelBdd h) (hπ : IsLipTuple π) :
    Tb h π = akExt T h π := by
  obtain ⟨hE1, hE2, -, hE3⟩ := hTb
  choose K hK using hπ
  have hπ' : IsLipTuple π := fun i => ⟨K i, hK i⟩
  have hμT := akMassMeasure_isAKMass hT
  obtain ⟨f, hf, hfl⟩ := by
    have : IsFiniteMeasure (akMassMeasure T) := hμT.1.1
    exact approx_exists hT hh
  have t1 := tendsto_of_approx hT hh hπ' hf hfl
  have t2 : Tendsto (fun n => T (f n) π) atTop (𝓝 (Tb h π)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun n => (∏ i, (K i : ℝ)) * ∫ x, |f n x - h x| ∂akMassMeasure T)
        atTop (𝓝 0) := by simpa using hfl.const_mul (∏ i, (K i : ℝ))
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
    have hfn := borelBdd_of_bddLip (hf n)
    have e := hE2 π hπ' (f n) h hfn hh 1 (-1)
    have e2 : (1 : ℝ) • f n + (-1 : ℝ) • h = fun x => f n x - h x := by
      funext x; simp [sub_eq_add_neg]
    rw [e2] at e
    rw [Real.norm_eq_abs, ← hE1 _ (hf n) π hπ', show Tb (f n) π - Tb h π =
      Tb (fun x => f n x - h x) π by rw [e]; ring]
    exact hE3 _ hμT.1 _ (borelBdd_sub hfn hh) π K hK
  exact (tendsto_nhds_unique t1 t2).symm

end MetricCurrents.AKExt

/-- [AK, (2.3)] For `T ∈ M_k(ℝ^d)`, `akExt T` is an extension of `T` to `B^∞ × Lip^k`
with the properties (E1)–(E4) of `IsAKExtension`; it is the only one; it is continuous for `L¹(μ_T)` convergence, depends only on the
`μ_T`-class of `h`, and is the limit `lim_n T(f_n, π)` for every sequence `f_n ∈ Lip_b` with
`∫ |f_n - h| dμ_T → 0`. -/
theorem akext (hT : IsMetricCurrent k T) :
    IsAKExtension T (akExt T) ∧
    (∀ Tb, IsAKExtension T Tb → ∀ h, IsBorelBdd h → ∀ π : Fin k → Vec d → ℝ, IsLipTuple π →
      Tb h π = akExt T h π) ∧
    (∀ μ, IsAKMass T μ → ∀ (hn : ℕ → Vec d → ℝ) (h : Vec d → ℝ), (∀ n, IsBorelBdd (hn n)) →
      IsBorelBdd h → Tendsto (fun n => ∫ x, |hn n x - h x| ∂μ) atTop (𝓝 0) →
      ∀ π : Fin k → Vec d → ℝ, IsLipTuple π →
        Tendsto (fun n => akExt T (hn n) π) atTop (𝓝 (akExt T h π))) ∧
    (∀ μ, IsAKMass T μ → ∀ h g : Vec d → ℝ, IsBorelBdd h → IsBorelBdd g → h =ᵐ[μ] g →
      ∀ π : Fin k → Vec d → ℝ, IsLipTuple π → akExt T h π = akExt T g π) ∧
    (∀ μ, IsAKMass T μ → ∀ (f : ℕ → Vec d → ℝ) (h : Vec d → ℝ), (∀ n, IsBddLipFun (f n)) →
      IsBorelBdd h → Tendsto (fun n => ∫ x, |f n x - h x| ∂μ) atTop (𝓝 0) →
      ∀ π : Fin k → Vec d → ℝ, IsLipTuple π →
        Tendsto (fun n => T (f n) π) atTop (𝓝 (akExt T h π))) := by
  refine ⟨⟨fun f hf π hπ => ext_eq_of_bddLip hT hf hπ,
    fun π hπ h g hh hg a b => ext_lin hT hπ hh hg a b,
    fun h hh π hπ i ψ hψ a b => ext_slot_lin hT hh hπ i hψ a b,
    fun μ hμ h hh π K hK => ext_abs_le hT hμ hh hK⟩,
    fun Tb hTb h hh π hπ => ext_unique hT hTb hh hπ,
    fun μ hμ hn h hhn hh hlim π hπ => ext_cont hT hμ hhn hh hlim hπ,
    fun μ hμ h g hh hg hae π hπ => ext_ae hT hμ hh hg hae hπ,
    fun μ hμ f h hf hh hlim π hπ => ?_⟩
  rw [mass_unique hT hμ] at hlim
  exact tendsto_of_approx hT hh hπ hf hlim

end AFree
