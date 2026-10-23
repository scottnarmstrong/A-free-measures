module

public import AFree.Paper.OrderK.AlgebraLeibniz
public import AFree.Measure.VectorIntegral
public import AFree.Defs.Finite

/-!
# Reverse Leibniz, smooth extension by zero, and variable-coefficient free pairs

The reverse Leibniz identity, smooth extension by zero, and the definition of an `A`-free pair
with variable smooth coefficients.
-/

@[expose] public section

open MeasureTheory PDE Matrix

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Reverse Leibniz identity: for `χ, f ∈ C^∞` and every multi-index `γ`,
`χ ∂^γ f = Σ_{δ ≤ γ} (-1)^{|γ-δ|} (γ δ) ∂^δ((∂^{γ-δ} χ) f)`; each function `(∂^{γ-δ} χ) f` is
smooth with `tsupport ⊆ tsupport χ`, compactly supported if `χ` is. -/
theorem lem_revleibniz {χ f : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (γ : Fin d → ℕ) :
    (∀ x, χ x * multiCoordDeriv γ f x =
      ∑ δ ∈ multiLE γ, (-1 : ℝ) ^ multiAbs (γ - δ) * multiChoose γ δ *
        multiCoordDeriv δ (fun y => multiCoordDeriv (γ - δ) χ y * f y) x) ∧
    ∀ δ ∈ multiLE γ, ContDiff ℝ (⊤ : ℕ∞) (fun y => multiCoordDeriv (γ - δ) χ y * f y) ∧
      tsupport (fun y => multiCoordDeriv (γ - δ) χ y * f y) ⊆ tsupport χ ∧
      (HasCompactSupport χ → HasCompactSupport (fun y => multiCoordDeriv (γ - δ) χ y * f y)) := by
  have hχs : SmOn Set.univ χ := smOn_univ_iff.2 hχ
  have hfs : SmOn Set.univ f := smOn_univ_iff.2 hf
  refine ⟨fun x => multiCoordDeriv_rev isOpen_univ γ hχs hfs (Set.mem_univ x), fun δ _ => ?_⟩
  have hsub : tsupport (fun y => multiCoordDeriv (γ - δ) χ y * f y) ⊆ tsupport χ :=
    (tsupport_mul_subset_left (f := multiCoordDeriv (γ - δ) χ) (g := f)).trans
      (tsupport_multiCoordDeriv_subset χ (γ - δ))
  refine ⟨smOn_univ_iff.1 (((hχs.multi _).mul hfs)), hsub, fun hc => ?_⟩
  exact IsCompact.of_isClosed_subset hc (isClosed_tsupport _) hsub

/-- If `ψ` is a test function in the open set `Ω` and `B` is `C^∞` on `Ω`, then
`ψ B` is `C^∞` on `ℝ^d` with compact support inside `tsupport ψ`, and so is every `∂^α(ψ B)`; in
particular these are continuous and bounded. -/
theorem lem_smoothext {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {ψ : Vec d → ℝ}
    (hψ : IsTestFunctionOn Ω ψ) {B : Vec d → ℝ} (hB : ContDiffOn ℝ (⊤ : ℕ∞) B Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => ψ y * B y) ∧ HasCompactSupport (fun y => ψ y * B y) ∧
      tsupport (fun y => ψ y * B y) ⊆ tsupport ψ ∧
      ∀ α : Fin d → ℕ, ContDiff ℝ (⊤ : ℕ∞) (multiCoordDeriv α (fun y => ψ y * B y)) ∧
        HasCompactSupport (multiCoordDeriv α (fun y => ψ y * B y)) ∧
        tsupport (multiCoordDeriv α (fun y => ψ y * B y)) ⊆ tsupport ψ ∧
        Continuous (multiCoordDeriv α (fun y => ψ y * B y)) ∧
        ∃ C : ℝ, ∀ x, ‖multiCoordDeriv α (fun y => ψ y * B y) x‖ ≤ C := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => ψ y * B y) := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ Ω
    · exact (hψ.1.contDiffAt).mul (hB.contDiffAt (hΩ.mem_nhds hx))
    · have hx' : x ∉ tsupport ψ := fun h => hx (hψ.2.2 h)
      have : (fun y => ψ y * B y) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hx'] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
      exact contDiffAt_const.congr_of_eventuallyEq this
  have hsub : tsupport (fun y => ψ y * B y) ⊆ tsupport ψ :=
    tsupport_mul_subset_left (f := ψ) (g := B)
  have hcs : HasCompactSupport (fun y => ψ y * B y) :=
    IsCompact.of_isClosed_subset hψ.2.1 (isClosed_tsupport _) hsub
  refine ⟨hsm, hcs, hsub, fun α => ?_⟩
  have hcc := isCc_multiCoordDeriv (⟨hsm, hcs⟩ : IsCc fun y => ψ y * B y) α
  obtain ⟨C, hC⟩ := hcc.1.continuous.bounded_above_of_compact_support hcc.2
  exact ⟨hcc.1, hcc.2, (tsupport_multiCoordDeriv_subset _ α).trans hsub, hcc.1.continuous, C, hC⟩

/-- `(σ, P)` is `A`-free in `Ω` (variable smooth coefficients, order `k`): `σ(Ωᶜ) = 0`
and, for every test function `ψ` in `Ω` and `j ∈ κ`, the `j`-th component of
`Σ_h (-1)^h Σ_{|α|=h} ∫ [∂^α(ψ A_α)] P dσ` vanishes. -/
def IsFreePairVar (Ω : Set (Vec d)) (k : ℕ) (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ)
    (σ : Measure (Vec d)) (P : Vec d → ι → ℝ) : Prop :=
  σ Ωᶜ = 0 ∧ ∀ ψ : Vec d → ℝ, IsTestFunctionOn Ω ψ → ∀ j : κ,
    ∑ h ∈ Finset.range (k + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
      (-1 : ℝ) ^ h * ∫ y, ∑ i : ι, multiCoordDeriv α (fun z => ψ z * A α z j i) y * P y i ∂σ = 0

end

end AFree
