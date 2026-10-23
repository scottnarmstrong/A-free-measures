module

public import AFree.Paper.OrderK.HarmonicSymbols
public import AFree.Paper.OrderK.HarmonicMultideriv

/-!
# Fourier representation `w_j = f_j + h_j`

The splitting of `w_j` into a piece `f_j` driven by `G` and a piece `h_j` driven by `w_j, H`.
-/

@[expose] public section

open MeasureTheory PDE Matrix
open scoped SchwartzMap ComplexConjugate

namespace AFree

noncomputable section

variable {d : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- `f_j = Σ_α Σ_c T_{m_{0,α,c}} G^{(α)}_{j,c}`. -/
def fPiece (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ)
    (G : (Fin d → ℕ) → Vec d → κ → ℝ) (x : Vec d) : ℂ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ c : κ,
    ccMult (m0Symb k A P₀ α c) (fun y => G α y c) x

/-- `h_j = T_{m_1} w_j + Σ_β Σ_c T_{m_{β,c}} H_{j,β,c}`. -/
def hPiece (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (w : Vec d → ℝ)
    (H : (Fin d → ℕ) → Vec d → κ → ℝ) (x : Vec d) : ℂ :=
  ccMult (m1Symb k A P₀) w x + ∑ h ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h,
    ∑ c : κ, ccMult (mBetaSymb k A P₀ β c) (fun y => H β y c) x

theorem isCc_apply_of {F : Vec d → κ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (c : κ) : IsCc (fun y => F y c) :=
  ⟨contDiff_pi.1 hF c, hc.comp_left (g := fun v : κ → ℝ => v c) rfl⟩

theorem vecFourier_schw_multiCoordDeriv {u : Vec d → ℝ} (hu : IsCc u) (α : Fin d → ℕ)
    (ξ : Vec d) :
    vecFourier (schw (multiCoordDeriv α u)) ξ = (2 * Real.pi * Complex.I) ^ (∑ i, α i) *
      (((∏ i, ξ i ^ α i : ℝ)) : ℂ) * vecFourier (schw u) ξ := by
  have h1 : ⇑(schw (multiCoordDeriv α u)) = fun x => ((multiCoordDeriv α u x : ℝ) : ℂ) :=
    funext (schw_apply (isCc_multiCoordDeriv hu α))
  have h2 : ⇑(schw u) = fun x => ((u x : ℝ) : ℂ) := funext (schw_apply hu)
  rw [h1, h2]
  exact vecFourier_multiCoordDeriv hu α ξ

/-- The cut-off system as an identity of Schwartz functions, component `c`. -/
theorem schw_system {k : ℕ} {A : (Fin d → ℕ) → Matrix κ ι ℝ} {P₀ : ι → ℝ} {w : Vec d → ℝ}
    {G H : (Fin d → ℕ) → Vec d → κ → ℝ} (hw : IsCc w)
    (hG : ∀ α, ContDiff ℝ (⊤ : ℕ∞) (G α) ∧ HasCompactSupport (G α))
    (hH : ∀ β, ContDiff ℝ (⊤ : ℕ∞) (H β) ∧ HasCompactSupport (H β))
    (hsys : IsSystemK k A P₀ w G H) (c : κ) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (((A α *ᵥ P₀) c : ℝ) : ℂ) •
        schw (multiCoordDeriv α w) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k, schw (multiCoordDeriv α (fun y => G α y c)) +
      ∑ h ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h,
        schw (multiCoordDeriv β (fun y => H β y c)) := by
  ext x
  have hx := congrFun (hsys x) c
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, multiCoordDerivVec] at hx
  simp only [_root_.add_apply, _root_.smul_apply, _root_.sum_apply, smul_eq_mul]
  have e1 : ∀ α, (schw (multiCoordDeriv α w)) x = ((multiCoordDeriv α w x : ℝ) : ℂ) := fun α =>
    schw_apply (isCc_multiCoordDeriv hw α) x
  have e2 : ∀ α, (schw (multiCoordDeriv α fun y => G α y c)) x =
      ((multiCoordDeriv α (fun y => G α y c) x : ℝ) : ℂ) := fun α =>
    schw_apply (isCc_multiCoordDeriv (isCc_apply_of (hG α).1 (hG α).2 c) α) x
  have e3 : ∀ β, (schw (multiCoordDeriv β fun y => H β y c)) x =
      ((multiCoordDeriv β (fun y => H β y c) x : ℝ) : ℂ) := fun β =>
    schw_apply (isCc_multiCoordDeriv (isCc_apply_of (hH β).1 (hH β).2 c) β) x
  simp only [e1, e2, e3]
  rw [Finset.sum_congr rfl (fun i _ => mul_comm (((A i *ᵥ P₀) c : ℝ) : ℂ)
    ((multiCoordDeriv i w x : ℝ) : ℂ))]
  exact_mod_cast hx

/-- The system after the Fourier transform: component `c` of `(2πi)^k a(ξ) ŵ = …`. -/
theorem fourier_system {k : ℕ} {A : (Fin d → ℕ) → Matrix κ ι ℝ} {P₀ : ι → ℝ} {w : Vec d → ℝ}
    {G H : (Fin d → ℕ) → Vec d → κ → ℝ} (hw : IsCc w)
    (hG : ∀ α, ContDiff ℝ (⊤ : ℕ∞) (G α) ∧ HasCompactSupport (G α))
    (hH : ∀ β, ContDiff ℝ (⊤ : ℕ∞) (H β) ∧ HasCompactSupport (H β))
    (hsys : IsSystemK k A P₀ w G H) (c : κ) (ξ : Vec d) :
    (2 * Real.pi * Complex.I) ^ k * ((symbA k A P₀ ξ c : ℝ) : ℂ) * vecFourier (schw w) ξ =
      (2 * Real.pi * Complex.I) ^ k * ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
        ((∏ i, ξ i ^ α i : ℝ) : ℂ) * vecFourier (schw (fun y => G α y c)) ξ +
      ∑ h ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h,
        (2 * Real.pi * Complex.I) ^ (∑ i, β i) * ((∏ i, ξ i ^ β i : ℝ) : ℂ) *
          vecFourier (schw (fun y => H β y c)) ξ := by
  have h := congrArg (fun S : 𝓢(Vec d, ℂ) => vecFourierCLM S ξ) (schw_system hw hG hH hsys c)
  simp only [map_add, map_sum, map_smul, _root_.add_apply, _root_.sum_apply, _root_.smul_apply,
    vecFourierCLM_apply, smul_eq_mul] at h
  have e1 : ∀ α ∈ Finset.Nat.antidiagonalTuple d k,
      (((A α *ᵥ P₀) c : ℝ) : ℂ) * vecFourier (schw (multiCoordDeriv α w)) ξ =
        (2 * Real.pi * Complex.I) ^ k * ((∏ i, ξ i ^ α i : ℝ) : ℂ) *
          (((A α *ᵥ P₀) c : ℝ) : ℂ) * vecFourier (schw w) ξ := fun α hα => by
    rw [vecFourier_schw_multiCoordDeriv hw, Finset.Nat.mem_antidiagonalTuple.1 hα]
    ring
  have e2 : ∀ α ∈ Finset.Nat.antidiagonalTuple d k,
      vecFourier (schw (multiCoordDeriv α (fun y => G α y c))) ξ =
        (2 * Real.pi * Complex.I) ^ k * (((∏ i, ξ i ^ α i : ℝ)) : ℂ) *
          vecFourier (schw (fun y => G α y c)) ξ := fun α hα => by
    rw [vecFourier_schw_multiCoordDeriv (isCc_apply_of (hG α).1 (hG α).2 c),
      Finset.Nat.mem_antidiagonalTuple.1 hα]
  have e3 : ∀ β, vecFourier (schw (multiCoordDeriv β (fun y => H β y c))) ξ =
      (2 * Real.pi * Complex.I) ^ (∑ i, β i) * (((∏ i, ξ i ^ β i : ℝ)) : ℂ) *
        vecFourier (schw (fun y => H β y c)) ξ := fun β =>
    vecFourier_schw_multiCoordDeriv (isCc_apply_of (hH β).1 (hH β).2 c) β ξ
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at h
  simp only [e3] at h
  have hA : (((symbA k A P₀ ξ c : ℝ)) : ℂ) = ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
      ((∏ i, ξ i ^ α i : ℝ) : ℂ) * (((A α *ᵥ P₀) c : ℝ) : ℂ) := by
    rw [symbA_apply]; push_cast; rfl
  rw [hA, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.mul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun _ _ => by ring) (h.trans ?_)
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem gamma_mul_lam (k : ℕ) :
    (-(2 * (Real.pi : ℂ) * Complex.I)) ^ k * (2 * (Real.pi : ℂ) * Complex.I) ^ k =
      (((2 * Real.pi) ^ (2 * k) : ℝ) : ℂ) := by
  have h : (-(2 * (Real.pi : ℂ) * Complex.I)) * (2 * (Real.pi : ℂ) * Complex.I) =
      (((2 * Real.pi) ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ)) ^ 2) * Complex.I_sq
  rw [← mul_pow, h, ← Complex.ofReal_pow, ← pow_mul]

/-- The identity `ŵ = m_1 ŵ + Σ m_{0,α,c} Ĝ + Σ m_{β,c} Ĥ` on the Fourier side. -/
theorem fourier_rep {k : ℕ} {A : (Fin d → ℕ) → Matrix κ ι ℝ} {P₀ : ι → ℝ} {w : Vec d → ℝ}
    {G H : (Fin d → ℕ) → Vec d → κ → ℝ} (hw : IsCc w)
    (hG : ∀ α, ContDiff ℝ (⊤ : ℕ∞) (G α) ∧ HasCompactSupport (G α))
    (hH : ∀ β, ContDiff ℝ (⊤ : ℕ∞) (H β) ∧ HasCompactSupport (H β))
    (hsys : IsSystemK k A P₀ w G H) (ξ : Vec d) :
    vecFourier (schw w) ξ =
      m1Symb k A P₀ ξ * vecFourier (schw w) ξ +
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ c : κ,
        m0Symb k A P₀ α c ξ * vecFourier (schw fun y => G α y c) ξ +
      ∑ h ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h, ∑ c : κ,
        mBetaSymb k A P₀ β c ξ * vecFourier (schw fun y => H β y c) ξ := by
  set W := vecFourier (schw w) ξ with hW
  set lam : ℂ := (2 * (Real.pi : ℂ) * Complex.I) ^ k with hlam
  set L' : ℂ := (-(2 * (Real.pi : ℂ) * Complex.I)) ^ k with hL'
  set R : ℝ := (2 * Real.pi) ^ (2 * k) with hR
  set a : κ → ℝ := fun c => symbA k A P₀ ξ c with ha
  set S1 : κ → ℂ := fun c => ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
    ((∏ i, ξ i ^ α i : ℝ) : ℂ) * vecFourier (schw fun y => G α y c) ξ with hS1
  set S2 : κ → ℂ := fun c => ∑ h ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h,
    (2 * (Real.pi : ℂ) * Complex.I) ^ (∑ i, β i) * ((∏ i, ξ i ^ β i : ℝ) : ℂ) *
      vecFourier (schw fun y => H β y c) ξ with hS2
  have hF : ∀ c, lam * (a c : ℂ) * W = lam * S1 c + S2 c := fun c =>
    fourier_system hw hG hH hsys c ξ
  have hP : L' * lam = (R : ℂ) := gamma_mul_lam k
  have hc : ∀ c, (R : ℂ) * (a c : ℂ) * (a c : ℂ) * W =
      (R : ℂ) * (a c : ℂ) * S1 c + L' * (a c : ℂ) * S2 c := fun c => by
    linear_combination (L' * (a c : ℂ)) * hF c - ((a c : ℂ) * (a c : ℂ) * W - (a c : ℂ) * S1 c) * hP
  have hq : (symbQ k A P₀ ξ : ℂ) * W = ∑ c, ((R : ℂ) * (a c : ℂ) * S1 c + L' * (a c : ℂ) * S2 c) := by
    rw [← Finset.sum_congr rfl fun c _ => hc c]
    simp only [symbQ, ha, hR]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hD : (1 + (symbQ k A P₀ ξ : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 1 + symbQ k A P₀ ξ := by
      have := symbQ_nonneg k A P₀ ξ; linarith
    exact_mod_cast this.ne'
  have hm1' : m1Symb k A P₀ ξ = (1 + (symbQ k A P₀ ξ : ℂ))⁻¹ := rfl
  set u : ℂ := (1 + (symbQ k A P₀ ξ : ℂ))⁻¹ with hu
  have hm0 : ∀ α c, m0Symb k A P₀ α c ξ = u * (((R * (∏ i, ξ i ^ α i) * a c : ℝ)) : ℂ) :=
    fun α c => by
      simp only [m0Symb, hu, ha, hR]
      push_cast
      rw [div_eq_mul_inv]
      ring
  have hmb : ∀ β c, mBetaSymb k A P₀ β c ξ =
      u * (L' * (2 * (Real.pi : ℂ) * Complex.I) ^ (∑ i, β i) *
        (((∏ i, ξ i ^ β i) * a c : ℝ) : ℂ)) := fun β c => by
    simp only [mBetaSymb, gammaCoef, hu, ha, hL']
    ring
  set Y1 : ℂ := ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ c : κ,
    (((R * (∏ i, ξ i ^ α i) * a c : ℝ)) : ℂ) * vecFourier (schw fun y => G α y c) ξ with hY1
  set Y2 : ℂ := ∑ h ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h, ∑ c : κ,
    (L' * (2 * (Real.pi : ℂ) * Complex.I) ^ (∑ i, β i) *
      (((∏ i, ξ i ^ β i) * a c : ℝ) : ℂ)) * vecFourier (schw fun y => H β y c) ξ with hY2
  have e1 : ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ c : κ,
      m0Symb k A P₀ α c ξ * vecFourier (schw fun y => G α y c) ξ = u * Y1 := by
    rw [hY1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hm0]; ring
  have e2 : ∑ h ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h, ∑ c : κ,
      mBetaSymb k A P₀ β c ξ * vecFourier (schw fun y => H β y c) ξ = u * Y2 := by
    rw [hY2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hmb]; ring
  have hY : Y1 + Y2 = (symbQ k A P₀ ξ : ℂ) * W := by
    rw [hq, Finset.sum_add_distrib]
    congr 1
    · rw [hY1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hS1]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      push_cast
      ring
    · rw [hY2]
      simp only [hS2, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      push_cast
      ring
  have hmul : u * (1 + (symbQ k A P₀ ξ : ℂ)) = 1 := inv_mul_cancel₀ hD
  have hfin : u * W + u * Y1 + u * Y2 = u * (W + (Y1 + Y2)) := by ring
  rw [e1, e2, hm1', hfin, hY]
  linear_combination (-W) * hmul

/-- Fourier representation: `w = f + h` pointwise, `f = Σ T_{m_{0,α,c}} G^{(α)}_c`,
`h = T_{m_1} w + Σ T_{m_{β,c}} H_{β,c}`. -/
theorem cl_rep (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) {c0 : ℝ} (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ))
    {w : Vec d → ℝ} {G H : (Fin d → ℕ) → Vec d → κ → ℝ} (hw : IsCc w)
    (hG : ∀ α, ContDiff ℝ (⊤ : ℕ∞) (G α) ∧ HasCompactSupport (G α))
    (hH : ∀ β, ContDiff ℝ (⊤ : ℕ∞) (H β) ∧ HasCompactSupport (H β))
    (hsys : IsSystemK k A P₀ w G H) (x : Vec d) :
    (w x : ℂ) = fPiece k A P₀ G x + hPiece k A P₀ w H x := by
  have hT1 := (isSymbol_m1Symb k A P₀ hc0 hell).hasTemperateGrowth
  have hT0 : ∀ α ∈ Finset.Nat.antidiagonalTuple d k, ∀ c,
      (m0Symb k A P₀ α c).HasTemperateGrowth := fun α hα c =>
    (isSymbol_m0Symb k A P₀ hc0 hell hα c).hasTemperateGrowth
  have hTb : ∀ β c, (mBetaSymb k A P₀ β c).HasTemperateGrowth := fun β c =>
    (isSymbol_mBetaSymb k A P₀ hc0 hell β c).hasTemperateGrowth
  set Tm : 𝓢(Vec d, ℂ) := vecMultiplier (m1Symb k A P₀) (schw w) +
    ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ c : κ,
      vecMultiplier (m0Symb k A P₀ α c) (schw fun y => G α y c) +
    ∑ h ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h, ∑ c : κ,
      vecMultiplier (mBetaSymb k A P₀ β c) (schw fun y => H β y c) with hTm
  have hF : vecFourierCLM Tm = vecFourierCLM (schw w) := by
    ext ξ
    simp only [hTm, map_add, map_sum, _root_.add_apply, _root_.sum_apply, vecFourierCLM_apply]
    rw [vecFourier_vecMultiplier hT1,
      Finset.sum_congr rfl (fun α hα => Finset.sum_congr rfl fun c _ =>
        vecFourier_vecMultiplier (hT0 α hα c) _ ξ)]
    simp only [vecFourier_vecMultiplier (hTb _ _)]
    exact (fourier_rep hw hG hH hsys ξ).symm
  have hTeq : Tm = schw w := by
    have := congrArg vecFourierInvCLM hF
    simpa [vecFourierInvCLM_vecFourierCLM] using this
  have := congrArg (fun S : 𝓢(Vec d, ℂ) => S x) hTeq
  simp only [hTm, _root_.add_apply, _root_.sum_apply, schw_apply hw] at this
  rw [fPiece, hPiece, ← this, ccMult]
  simp only [ccMult]
  ring

end

end AFree
