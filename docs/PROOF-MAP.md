# Proof map

This page is a guide to the Lean proofs of the results of [DPR]. For each result it names the Lean
theorem and its statement file, the module that assembles the proof and the main intermediate
declarations, and it says where the proof follows a different route from the paper.

## Organization and conventions

- `AFree/Defs.lean`: the definitions used in the statements (see below).
- `AFreeStatements/`: the 25 main theorems, one per file, in the namespace `AFree`. Each is proved
  by the single line `by exact AFree.<Name>Proof.result …`.
- `AFree/Proofs/<Name>Proof.lean`: the theorem `result`, which applies one theorem of the
  development. Only `AFree/Proofs/WaveConeBridgeProof.lean` contains an argument of its own.
- `AFree/Paper/`: Theorem 1.1, Lemma 2.1 and the applications up to Corollary 1.13; Theorem 1.1 for
  operators of every order, with Remarks 1.3 and 1.4, is in `AFree/Paper/OrderK/`.
- `AFree/Curves/`, `AFree/Rademacher/`: cone-null sets, Rainwater's lemma, the decomposability
  bundle, Lemma 3.1 and Theorem 1.14. `AFree/MetricCurrents/`, `AFree/TopCurrents/`: metric
  currents and Theorem 1.15.
- `AFree/Harmonic/`, `AFree/Analysis/`, `AFree/Measure/`, `AFree/Algebra/`: shared infrastructure.

Several applications are proved in a conditional form that takes the instance of Theorem 1.1 they
need as a hypothesis (names ending in `_of_main`); their proof modules supply the instance. The
results feed into each other as follows.

- Theorem 1.1 for first-order operators gives Theorems 1.5, 1.6 and 1.10 and Corollary 1.13.
  Theorem 1.10 gives Corollaries 1.9 and 1.12 and the simplicity statement of Remark 1.11.
- Theorem 1.1 of order `k` gives Remark 1.3 and, for `k = 2`, Theorem 1.7 and Corollary 1.8. It is
  the constant-coefficient case of a theorem for pairs with smooth variable coefficients, which also
  gives Remark 1.4.
- Corollary 1.12 is used in the proofs of Lemma 3.1 and Theorems 1.14 and 1.15.
- Lemma 2.1 is proved on its own: neither proof of Theorem 1.1 uses it.

**Citations.** [DPR] is the paper, numbered as in arXiv:1601.06543v2. [AM] is G. Alberti and A. Marchese, *On the differentiability of Lipschitz functions with
respect to arbitrary measures*, Geom. Funct. Anal. 26 (2016), numbered as in arXiv:1408.2379v2. [AK]
is L. Ambrosio and B. Kirchheim, *Currents in metric spaces*, Acta Math. 185 (2000). A reference such
as *DPR Deviation 8* or *AM Erratum 2* points to the numbered entries of
[`docs/ERRATA-AND-DEVIATIONS.md`](ERRATA-AND-DEVIATIONS.md), which are grouped by source.

**Names.** Lean names are in the namespace `AFree`, which is omitted: `Rademacher.thm_rademacher`
stands for `AFree.Rademacher.thm_rademacher`. Names from EllipticRegularityLean keep their namespace
`PDE`. In the tables, module paths are relative to `AFree/`.

## Definitions

`AFree/Defs.lean` contains every definition used in the 25 statements. They are kept in one module so
that the comparator challenge, which restates them in one file, elaborates to the same constants.
`ℝ^d` is `Vec d = Fin d → ℝ` with Lebesgue measure. Total variations, polars, `k`-vectors,
Lipschitz constants, diameters and `𝓗¹` are taken for the Euclidean norm. The module has four parts.

1. **Measures, polars and first-order operators** ([DPR, Section 2.1]). `euclideanVariation μ` is
   the total variation `|μ|` for the Euclidean norm `piEuclideanNorm`. `polar μ` is the
   coordinatewise Radon–Nikodym derivative `dμ/d|μ|`, and `lebesgueSingularPart μ` the coordinatewise
   singular part `μˢ` with respect to Lebesgue measure. `IsTestFunctionOn Ω φ` means
   `φ ∈ C_c^∞(Ω)`. `IsFirstOrderFree` is the equation `Σ_ℓ A_ℓ ∂_ℓ μ + A₀ μ = 0` and
   `waveConeFirstOrder` its real wave cone. `IsBVGradientOn` encodes `u ∈ BV(Ω; ℝ^ℓ)`.
2. **Higher derivatives, `k`-vectors and normal currents.** `IsDerivMeasureOn` (Theorem 1.6);
   `KVec`, `wedge`, `interiorProduct`, `IsSimpleKVec`, `kvecSpan`, `covectorKernel`;
   `IsBoundaryOn` and `IsNormalCurrentOn` for currents as `Λ_k`-valued measures,
   `IsLocNormalCurrent` for locally normal currents in polar form (Remark 1.11), and `kvecOneToVec`.
3. **Operators of order `k`, BD functions and Bessel potentials.** `multiCoordDeriv`, `IsFree`,
   `waveCone`; `IsFreeVar` (Remark 1.4); `IsBDGradientOn`; `vecFourierTransform`, `besselPotential`,
   `L1Ball` and `besselExponent` (Lemma 2.1).
4. **Metric currents, flat chains and the decomposability bundle**, after [AK] and [AM].
   `IsMetricFunctional`, `IsAKMassAdmissible`, `IsAKMass`, `IsMetricCurrent` and
   `HasCompactAKSupport` ([AK, Definitions 2.2, 2.6 and 3.1]); `IsTopFlatChain`;
   `euclideanHausdorffOne`, `IsRectifiableFamily`, `IsDecompTestField` and `IsDecompBundle`
   ([AM, Section 2.7]).

`AFree/Defs/Finite.lean` shows that the variation measures are finite, so that `polar` and
`lebesgueSingularPart` are a Radon–Nikodym derivative and a singular part. The encodings are
discussed in DPR Deviations 2–5, AK Deviation 1 and AM Deviation 1.

## Main results

### Theorem 1.1, operators of order at most one

Statement `polar_mem_waveConeFirstOrder` (`AFreeStatements/FirstOrderMain.lean`); proof
`AFree/Proofs/FirstOrderMainProof.lean`.

| Step | Lean | Module |
|---|---|---|
| A free measure gives a free pair (total variation, polar) | `isFreePair_of_isFirstOrderFree` | `Paper/FreePair.lean` |
| Theorem 1.1 for free pairs, then for arbitrary finite index types | `ae_mem_waveCone_of_isFreePair`, `ae_mem_waveCone_of_isFreePair'` | `Paper/MainPair.lean`, `Paper/Reindex.lean` |
| Good points of the bad set, with doubling scales | `exists_goodPoint`, `exists_doubling_scale` | `Paper/GoodPoints.lean`, `Measure/Doubling.lean` |
| Ellipticity of `M = B_{P₀}ᵀ B_{P₀}` off the wave cone | `exists_elliptic_ellipticMatrix` | `Analysis/WaveCone.lean` |
| Blow-ups, mollification and the cut-off system | `blowUp_equation`, `leibniz_system`, `leibniz_bounds` | `Paper/BlowUp.lean`, `Paper/Elliptic.lean` |
| Strong constancy | `exists_subseq_tendsto_L1_of_elliptic`, `eq_sum_add_of_div_eq` | `Analysis/StrongConstancy.lean` |
| Concentration of the singular blow-ups | `concentration` | `Measure/Concentration.lean` |

The proof argues by contradiction at a good point of the set where the polar leaves the wave cone.
The paper inverts the elliptic part with Fourier multipliers. Here the transposed symbol is applied
to the equation, so that the cut-off blow-ups solve `div(M∇w_j) = div F_j` for a constant elliptic
matrix `M`, and `w_j = Σ_ℓ ∂_ℓ u^M_{G_j^ℓ} + u^M_{H_j}` with Newtonian potentials `u^M`. The first
part is small in measure by the weak type (1,1) estimate for the gradient of the potential, the
second is precompact in `L¹` since the kernel is locally integrable, and the Vitali lemma concludes
(DPR Deviation 8). The scales are chosen by Besicovitch doubling instead of tangent measures, and the
contradiction comes from the concentration of the blow-ups against their `L¹` convergence, with no
limit measure (DPR Deviation 10). The coercivity bound and the measurability of the bad set are
proved (DPR Deviation 11).

### Theorem 1.1, operators of every order

Statement `polar_mem_waveCone` (`AFreeStatements/GeneralMain.lean`); proof
`AFree/Proofs/GeneralMainProof.lean`, which applies `thm_general` (`Paper/OrderK/Main.lean`).

| Step | Lean | Module |
|---|---|---|
| A free measure gives a free pair, with the coefficients regarded as variable | `lem_varpair`, `IsFreePairVar` | `Paper/OrderK/AlgebraVarPair.lean`, `Paper/OrderK/AlgebraTest.lean` |
| Theorem 1.1 for pairs with smooth variable coefficients; the cases `d = 0` and `k = 0` | `thm_main_pair`, `lem_dzerok`, `lem_kzero` | `Paper/OrderK/Main.lean`, `Paper/OrderK/MainKZero.lean` |
| Bad set, good points and the ellipticity bound (iii') | `badSetK`, `lem_goodk`, `exists_ellipticity_symbA` | `Paper/OrderK/BlowUpBad.lean`, `Paper/OrderK/AlgebraCone.lean` |
| The cut-off system, by the reverse Leibniz rule | `lem_revleibniz`, `LowRep`, `lem_systemk` | `Paper/OrderK/AlgebraTest.lean`, `Paper/OrderK/BlowUpLow.lean`, `Paper/OrderK/BlowUpSystemSeq.lean` |
| Strong constancy of order `k`: the representation `w_j = f_j + h_j` | `prop_sck`, `fourier_rep` | `Paper/OrderK/StrongConstancy.lean`, `Paper/OrderK/StrongConstancyRep.lean` |
| Symbol classes, weak type (1,1) of the order-zero part, compactness of the rest | `lem_symbolsk`, `lem_wt0`, `cor_convscalar` | `Paper/OrderK/HarmonicSymbols.lean`, `Paper/OrderK/HarmonicWt0.lean`, `Paper/OrderK/HarmonicConvScalar.lean` |
| The blow-up contradiction | `thm_main_pair_blowup` | `Paper/OrderK/MainBlow.lean` |

The proof is carried out for pairs with variable coefficients from the start. The paper treats the
cut-off remainder by pseudo-differential operators. Here the cut-off is commuted with the top-order
part by a reverse Leibniz identity, so that every term is a constant-coefficient derivative of a
smooth compactly supported function. After the Fourier transform the multipliers lie in explicit
symbol classes: the order-zero one is handled by a weak type (1,1) Hörmander–Mihlin estimate and the
others are convolutions with `L¹` kernels, which are compact (DPR Deviation 9). Scales and endgame
are as in the first-order case.

### The wave cones and the complex symbol

`mem_waveConeFirstOrder_iff_complexSymbol` (`AFreeStatements/WaveConeBridge.lean`) and
`mem_waveCone_iff_complexSymbol` (`AFreeStatements/WaveConeBridgeK.lean`) show that the real wave
cones `waveConeFirstOrder` and `waveCone` of the statements are the paper's cones, defined with the
complex symbol `(2πi)^k Σ_{|α|=k} ξ^α A_α`. The first is proved in
`AFree/Proofs/WaveConeBridgeProof.lean`, the second by `waveCone_iff_complexSymbol`
(`Paper/WaveConeK.lean`). Both use `(2πi)^k ≠ 0` and the injectivity of `ℝ → ℂ` (DPR Deviation 3).

### Remark 1.3, a measure on the right-hand side

Statement `polar_mem_waveCone_of_eq_measure` (`AFreeStatements/MeasureRhs.lean`); proof
`AFree/Proofs/MeasureRhsProof.lean`, which applies `thm_rhs` (`Paper/OrderK/Rhs.lean`).

| Step | Lean | Module |
|---|---|---|
| The augmented operator `Ã(μ, σ) = 𝒜μ - σ`, whose wave cone is `Λ_𝒜 × ℝ^κ` | `augCoeffK`, `lem_augop` | `Paper/OrderK/Rhs.lean` |
| The augmented measure `(μ, σ)`, whose polar is proportional to that of `μ` | `augmentedMeasure`, `polar_augmentedMeasure_inl_proportional`, `lem_augpolar` | `Paper/AugmentedMeasure.lean`, `Paper/OrderK/Rhs.lean` |

The reduction is the paper's, with its "easy to check" assertions proved. The order is assumed to be
at least one: for `k = 0` the statement is false (DPR Deviation 6). The first-order form of the same
reduction, used for Theorem 1.10 and Corollary 1.13, is `isFirstOrderFree_augmented_of_rhs` and
`ae_polar_mem_waveCone_of_augmented` (`Paper/DivAssembly.lean`), with `augmentedCoeff`
(`Paper/Augmented.lean`).

### Remark 1.4, variable coefficients

Statement `polar_mem_waveCone_var` (`AFreeStatements/VariableCoeff.lean`); proof
`AFree/Proofs/VariableCoeffProof.lean`, which applies `thm_var` (`Paper/OrderK/Var.lean`).

| Step | Lean | Module |
|---|---|---|
| Truncation of the coefficients to multi-indices of order at most `k` | `truncCoeff`, `isFreeVar_truncCoeff` | `Paper/OrderK/Var.lean` |
| Theorem 1.1 for pairs with smooth variable coefficients | `thm_main_pair` | `Paper/OrderK/Main.lean` |
| The coefficient errors of the blow-up are `O(r)` | `errF_bound`, `integral_errY_le` | `Paper/OrderK/BlowUpErr.lean`, `Paper/OrderK/BlowUpErrInt.lean` |

"Using essentially the same proof" is replaced by the complete argument of `thm_main_pair`: after the
blow-up the coefficients are evaluated at `x₀`, and the commutators with the coefficients are
derivatives of finite measures of mass `O(r_j)` (DPR Deviation 7).

### Theorem 1.5, Alberti's rank-one theorem

Statement `polar_lebesgueSingularPart_eq_tensor` (`AFreeStatements/Alberti.lean`); proof
`AFree/Proofs/AlbertiProof.lean`, which applies `polar_lebesgueSingularPart_eq_tensor_of_main` to the
instance `albertiInstance_of_main` of first-order Theorem 1.1 (`Paper/AlbertiAssembly.lean`).

| Step | Lean | Module |
|---|---|---|
| `Du` is curl-free | `curlCoeff`, `isFirstOrderFree_curl_of_isBVGradientOn` | `Paper/Curl.lean` |
| The wave cone of the curl consists of the rank-one matrices | `mem_waveCone_curl_iff`, `exists_ne_zero_rankOne_of_mem_waveCone_curl` | `Paper/Curl.lean` |
| The polar and the variation of the singular part | `polar_lebesgueSingularPart_ae`, `euclideanVariation_lebesgueSingularPart` | `Measure/PolarFacts.lean` |

As in the paper, except that the wave cone of the curl, quoted there from Fonseca–Müller, is
computed (DPR Deviation 13). For the encoding of BV see DPR Deviation 4.

### Theorem 1.6, higher derivatives

Statement `polar_lebesgueSingularPart_eq_tensorPow` (`AFreeStatements/TensorPow.lean`); proof
`AFree/Proofs/TensorPowProof.lean`, which applies `ae_polar_lebesgueSingularPart_tensorPow`
(`Paper/TensorPow/Main.lean`).

| Step | Lean | Module |
|---|---|---|
| The first-order curl-type operator, which annihilates `Dʳu` | `curlrCoeff`, `isFirstOrderFree_curlr_of_isDerivMeasureOn` | `Paper/TensorPow/Curl.lean`, `Paper/TensorPow/Free.lean` |
| Mixed partial derivatives commute | `foldr_euclideanCoordDeriv_perm` | `Paper/TensorPow/PermDeriv.lean` |
| First-order Theorem 1.1 for this operator | `ae_polar_mem_waveConeFirstOrder_curlr` | `Paper/TensorPow/Main.lean` |
| Its wave cone consists of the tensors `a ⊗ ξ^{⊗r}` | `curlr_cone`, `exists_ne_zero_tensorPow_of_mem_waveCone_curlr` | `Paper/TensorPow/Cone.lean`, `Paper/TensorPow/Main.lean` |

As in the paper, with the index ranges of the operator corrected (DPR Erratum 5) and its wave cone
computed (DPR Deviation 13).

### Theorem 1.7, BD functions

Statement `polar_lebesgueSingularPart_eq_symmTensor` (`AFreeStatements/BD.lean`); proof
`AFree/Proofs/BDProof.lean`, which applies `polar_lebesgueSingularPart_eq_symmTensor_of_main`
(`Paper/BD/Assembly.lean`) to the instance `polar_mem_waveCone_saintVenant`
(`Paper/OrderK/MainBD.lean`) of Theorem 1.1 of order 2.

| Step | Lean | Module |
|---|---|---|
| The Saint-Venant operator | `saintVenant` | `Paper/BD/SaintVenant.lean` |
| `Eu` is symmetric and free for it | `isBDGradientOn_symm`, `isFree_saintVenant_of_isBDGradientOn` | `Paper/BD/Symmetric.lean`, `Paper/BD/EuFree.lean` |
| Its symbol annihilates a symmetric matrix iff the matrix is `a ⊗ ξ + ξ ⊗ a` | `exists_symmTensor_of_mem_waveCone_saintVenant` | `Paper/BD/Kernel.lean` |

The paper's contracted operator on symmetric matrices is replaced by the uncontracted Saint-Venant
operator on all matrices, whose kernel on symmetric matrices is computed in full (DPR Deviation 14;
the constant of the symbol is corrected in DPR Erratum 6).

### Corollary 1.8

Statement `polar_lebesgueSingularPart_eq_symmTensor_orth` (`AFreeStatements/BDOrth.lean`); proof
`AFree/Proofs/BDOrthProof.lean`, which applies `polar_lebesgueSingularPart_eq_symmTensor_orth_of_main`
(`Paper/BD/Assembly.lean`) to `polar_mem_waveCone_saintVenant`.

| Step | Lean | Module |
|---|---|---|
| The trace of `Eu` has no singular part | `trace_singularPart_eq_zero`, `BD.ae_eq_zero_on_null_of_test` | `Paper/BD/Trace.lean`, `Paper/BD/TraceCore.lean` |
| Hence the singular polar has trace zero | `ae_sum_polar_diag_lebesgueSingularPart_eq_zero` | `Paper/BD/Assembly.lean` |

`a · b = 0` follows from `tr(a ⊙ b) = a · b` and the uniqueness of the Lebesgue decomposition of
`tr Eu = div u`. Only `div u ∈ L¹_loc` is used (DPR Deviation 15).

### Corollary 1.9

Statement `exists_hyperplane_of_boundaryless` (`AFreeStatements/Hyperplane.lean`); proof
`AFree/Proofs/HyperplaneProof.lean`, which applies `ae_exists_hyperplane_of_boundaryless`
(`Paper/Currents/Hyperplane.lean`).

| Step | Lean | Module |
|---|---|---|
| Theorem 1.10 with `Ω = ℝ^d`, `kᵢ = d - 1` and `∂Tᵢ = 0` | `ae_exists_covector_of_boundaryless` | `Paper/Currents/Hyperplane.lean` |
| `v ⌟ ω = 0` iff `v ∈ Λ_{d-1}(ker ω)`, and `dim ker ω = d - 1` | `equiv_interiorProduct_kvecSpan`, `finrank_covectorKernel` | `Algebra/KVec/Equiv.lean` |

The paper deduces the corollary from Theorem 1.5 through `⋆Du`; the library deduces it from Theorem
1.10 (DPR Deviation 16).

### Theorem 1.10, normal currents

Statement `exists_covector_interiorProduct_eq_zero` (`AFreeStatements/CovectorKernel.lean`); proof
`AFree/Proofs/CovectorKernelProof.lean`, which applies `ae_exists_covector_interiorProduct_eq_zero`
(`Paper/Currents/Covector.lean`). The equivalent formulation `interiorProduct_eq_zero_iff_mem_kvecSpan`
(`AFreeStatements/InteriorProductKernel.lean`) is proved by `equiv_interiorProduct_kvecSpan`
(`Algebra/KVec/Equiv.lean`).

| Step | Lean | Module |
|---|---|---|
| Block measures of the currents and of their boundaries | `blockMeasure` | `Measure/Decomp/Blocks.lean` |
| They satisfy a first-order system `𝒜𝐓 = σ` | `systemCoeff`, `blockMeasure_system_free` | `Paper/Currents/System.lean`, `Paper/Currents/Free.lean` |
| Remark 1.3 and Theorem 1.1, first order, for the system | `ae_polar_blockMeasure_mem_waveCone_system` | `Paper/Currents/Covector.lean` |
| The symbol identity (3.3) and the wave cone of the system | `systemCoeff_symbol_mulVec`, `mem_waveConeFirstOrder_systemCoeff_iff` | `Paper/Currents/System.lean` |
| The interior product of a wedge, and `Λ_k(ker ω) ⊆ ker(· ⌟ ω)` | `interiorProduct_wedge`, `interiorProduct_eq_zero_of_mem_kvecSpan` | `Algebra/KVec/Interior.lean` |

As in the paper. The symbol identity (3.3), `μˢ ≪ |𝐓|ˢ`, the factorization (3.4) and the equivalence
of the two formulations are proved (DPR Deviation 17). Currents are `Λ_k`-valued measures with the
Euclidean norm (DPR Deviations 2 and 5).

### Remark 1.11

Three statements, each with its proof module in `AFree/Proofs/`:
`isSimpleKVec_of_mem_kvecSpan` (`AFreeStatements/SimpleLinAlg.lean`), proved by `simplelin`;
`ae_isSimpleKVec_of_isLocNormalCurrent` (`AFreeStatements/SimpleAE.lean`), proved by `simpleae`; and
`not_ae_isSimpleKVec_example` (`AFreeStatements/SimpleCounterexample.lean`), proved by `counterex`.

| Step | Lean | Module |
|---|---|---|
| Sums of simple `(d-2)`-vectors of a hyperplane are simple | `simpleadd`, `simplelin` | `Algebra/KVec/Simple.lean` |
| Restriction of a locally normal current to a ball | `cut` | `Paper/SimpleAE/Cut.lean` |
| Theorem 1.10 on each ball, then on all of `ℝ^d` | `simpleae_ball`, `simpleae_globalize`, `simpleae` | `Paper/SimpleAE/Main.lean` |
| The example in `ℝ⁵`: the measure, normality, and failure of the Plücker relations | `ceTau`, `counterex_boundary_clause`, `counterex_not_ae_simple`, `pluckerP0_not_isSimpleKVec` | `Paper/Counterexample/Measure.lean`, `Paper/Counterexample/Main.lean`, `Algebra/KVec/Plucker.lean` |

The linear algebra, the localization to bounded open sets and the properties of the example are
proved. In the Euclidean normalization the example has `T⃗ = (e₁ ∧ e₂ + e₃ ∧ e₄)/√2` and
`‖T‖ = √2 𝓗⁴ ⌞ {x₅ = 0}` (DPR Deviation 18).

### Corollary 1.12

Statement `absolutelyContinuous_of_span_eq_top` (`AFreeStatements/SpanAbsCont.lean`); proof
`AFree/Proofs/SpanAbsContProof.lean`, which applies `absolutelyContinuous_of_span_polar_eq_top`
(`Paper/Currents/SpanAbsCont.lean`).

As in the paper: Theorem 1.10 with `Ω = ℝ^d` and `kᵢ = 1` gives, at `μˢ`-almost every point, a
covector `ω ≠ 0` orthogonal to all the polars (`oneip`, `Algebra/KVec/Equiv.lean`). This is impossible
where the polars span `ℝ^d`, so `μˢ = 0`.

### Corollary 1.13

Statement `rank_polar_le_of_div_eq` (`AFreeStatements/DivRank.lean`); proof
`AFree/Proofs/DivRankProof.lean`, which applies `rank_polar_le_of_div_eq_of_main`
(`Paper/DivAssembly.lean`) to first-order Theorem 1.1.

| Step | Lean | Module |
|---|---|---|
| `Div` as a first-order operator; its wave cone is the set of matrices of rank at most `d - 1` | `divCoeff`, `mem_waveConeFirstOrder_divCoeff_iff` | `Paper/DivWaveCone.lean` |
| The right-hand side, by augmentation (Remark 1.3, first order) | `augmentedCoeff`, `isFirstOrderFree_augmented_of_rhs`, `ae_polar_mem_waveCone_of_augmented` | `Paper/Augmented.lean`, `Paper/DivAssembly.lean` |

As in the paper.

### Theorem 1.14, the converse of Rademacher's theorem

Statement `absolutelyContinuous_of_ae_differentiableAt` (`AFreeStatements/RademacherConverse.lean`);
proof `AFree/Proofs/RademacherConverseProof.lean`, which applies `Rademacher.thm_rademacher`
(`Rademacher/Chain/Radfin.lean`).

| Step | Lean | Module |
|---|---|---|
| Reduction to finite measures, by restriction to balls | `Rademacher.thm_rademacher`, `Rademacher.thm_radfin` | `Rademacher/Chain/Radfin.lean` |
| A decomposability bundle `V` exists | `Bundle.bundle_exists` | `Curves/Bundle/Exists.lean` |
| If `V ≠ ℝ^d` on a set of positive measure, a Lipschitz function is not differentiable there | `Rademacher.thm_nondiff`, `Rademacher.nondiff_iteration` | `Rademacher/Chain/Nondiff.lean`, `Rademacher/Chain/NondiffIter.lean` |
| Continuous frame, [AM, Lemma 4.8], [AM, Proposition 4.10], [AM, Lemma 4.11] | `Rademacher.lem_frame`, `Rademacher.lem_perturbation`, `Rademacher.prop_wideconenull`, `Rademacher.lem_perturbcut` | `Rademacher/Frame.lean`, `Rademacher/Chain/PertMain.lean`, `Rademacher/Chain/WideMain.lean`, `Rademacher/Chain/Cut.lean` |
| Robustness of the oscillation bound, in place of Baire category | `Rademacher.lem_robust` | `Rademacher/Robust.lean` |
| If `V = ℝ^d` almost everywhere, then `μ ≪ 𝓛^d` | `absolutelyContinuous_of_decompBundle_eq_top` | `Curves/BundleTop/Main.lean` |

The paper quotes [AM, Theorem 1.1], then Lemma 3.1 and Corollary 1.12. The library proves only the
direction of [AM, Section 4] that it needs, with an explicit iteration of the single-stage
perturbation [AM, Lemma 4.8]. That `V = ℝ^d` almost everywhere implies `μ ≪ 𝓛^d` is proved by
selecting countably many rational cones, building curve currents and applying Corollary 1.12,
instead of [AM, Sections 5–6] (DPR Deviation 19). All the [AM] entries of the errata file (AM Errata
1–7 and Deviations 1–7) concern parts of [AM] used in this proof.

### Theorem 1.15, metric currents

Two statements. The first is `absolutelyContinuous_of_isAKMass`
(`AFreeStatements/MetricCurrentAC.lean`), with proof `AFree/Proofs/MetricCurrentACProof.lean`, which
applies `curr_ac` (`TopCurrents/Assembly/CurrAC.lean`).

| Step | Lean | Module |
|---|---|---|
| The density `ν = T(·, x₁, …, x_d)`, whose total variation is `‖T‖` | `nu_main`, `nu_mass_eq_variation` | `MetricCurrents/Nu.lean` |
| [AK, Theorem 3.5]: the chain rule and alternation | `akchain`, `akalt_matrix` | `MetricCurrents/AKChain.lean`, `MetricCurrents/AKAlt.lean` |
| The variation of `ν` vanishes on Borel cone-null sets, by [AM, Proposition 7.4] and the continuity axiom | `currentnull`, `currentnull_compact`, `perturb_of_cnull` | `TopCurrents/CurrentNull.lean`, `Curves/Perturb/Main.lean` |
| A finite measure vanishing on compact cone-null sets for `d` orthonormal axes is `≪ 𝓛^d` | `conenull_ac`, `exhaust_prop`, `spanac_prop` | `Curves/Exhaust/ConeNull.lean`, `Curves/Exhaust/Prop.lean`, `Curves/Exhaust/Span.lean` |

The second is `isTopFlatChain_iff_isMetricCurrent` (`AFreeStatements/FlatChain.lean`), with proof
`AFree/Proofs/FlatChainProof.lean`, which applies `flat_main` (`TopCurrents/Assembly/Flat.lean`).

| Step | Lean | Module |
|---|---|---|
| `T = u_#` when `‖T‖ ≪ 𝓛^d` ([AK, Theorem 3.8]) | `usharp_of_curr_ac` | `TopCurrents/Representation.lean` |
| `u_#` is a metric current ([AK, Example 3.2]), by weak-* continuity of minors | `usharp_isMetricCurrent`, `wstar` | `TopCurrents/USharpMain.lean`, `TopCurrents/WStar.lean` |
| From a current to a flat chain: `u 𝓛^d` is a mass limit of smooth compactly supported densities | `flat_current_to_chain`, `sMeas`, `smoothdense` | `TopCurrents/Assembly/FlatChain.lean`, `TopCurrents/Assembly/FlatS.lean`, `TopCurrents/SmoothDense.lean` |
| From a flat chain to a current, through Corollary 1.12 for top-dimensional normal currents; uniqueness | `flat_chain_ac`, `normalac`, `flat_chain_to_current`, `flat_uniqueness` | `TopCurrents/Assembly/FlatBack.lean`, `TopCurrents/NormalAC.lean` |

The paper deduces `‖T‖ ≪ 𝓛^d` from Schioppa's Alberti representations of metric currents and the
decomposability bundle. The library uses neither. It writes `T(f, π) = ∫ f det Dπ dν` with
`ν = T(·, x₁, …, x_d)`, shows that `|ν|` vanishes on cone-null compact sets, dominates `|ν|` by
averages of curve measures (Rainwater's lemma, with an exhaustion) and concludes with Corollary 1.12
for `d` one-dimensional normal currents (DPR Deviation 21, AK Deviations 3 and 4). The equality
`𝐌^met_d(ℝ^d) = 𝐅_d(ℝ^d)` is proved for compactly supported currents, as in [AK, Theorem 11.1]
(DPR Erratum 1).

### Lemma 2.1, compactness of Bessel potentials

Statement `exists_compact_besselPotential` (`AFreeStatements/BesselCompact.lean`); proof
`AFree/Proofs/BesselCompactProof.lean`, which applies `Bessel.bessel_compact`
(`Paper/Bessel/Main.lean`).

| Step | Lean | Module |
|---|---|---|
| The Bessel kernel `b` lies in `L^p` for `p < p(d, s)`, and the potential is convolution with `b` | `Bessel.besselKernel`, `Bessel.besselKernel_b`, `Bessel.besselKernel_d` | `Paper/Bessel/Kernel.lean` |
| Young's inequality for `L^p ⋆ L¹` | `Bessel.eLpNorm_convFn_le`, `Bessel.convLp` | `Paper/Bessel/Young.lean` |
| Convolution with a continuous compactly supported kernel is compact (Arzelà–Ascoli) | `Bessel.isCompactOperator_convBall` | `Paper/Bessel/CCompact.lean` |
| The cases `d ≥ 1` and `d = 0` | `Bessel.exists_compact_pos`, `Bessel.exists_compact_zero` | `Paper/Bessel/Main.lean` |

The paper proves compactness `L¹ → L¹` and passes to `L^p` by interpolation. The library approximates
`b` in `L^p` by compactly supported continuous kernels, so that Young's inequality gives convergence
in operator norm `L¹ → L^p`, and compactness passes to the limit (DPR Deviation 12). The kernel is
the integrable kernel of the symbol `(1 + 4π²|ξ|²)^{-s/2}` (`besselSymbol`, `memLp_negKernel`), with
the constant `4π²` forced by the Fourier convention (DPR Erratum 3).

### Lemma 3.1

Statement `decompBundle_eq_top_iff` (`AFreeStatements/DecompBundleIff.lean`); proof
`AFree/Proofs/DecompBundleIffProof.lean`, which applies `lemma31` (`Curves/Lemma31/Main.lean`).

| Step | Lean | Module |
|---|---|---|
| (ii) ⇒ (i): Corollary 1.12, then the absolutely continuous case of [AM, Proposition 2.9(iii)] | `lemma31_ii_to_i`, `bundle_ac` | `Curves/Lemma31/Main.lean`, `Curves/Bundle/AC.lean` |
| (i) ⇒ (ii): `μ ≪ 𝓛^d` as in Theorem 1.14 | `lemma31_i_to_ii_absolute_continuity`, `absolutelyContinuous_of_decompBundle_eq_top` | `Curves/Lemma31/Main.lean`, `Curves/BundleTop/Main.lean` |
| (i) ⇒ (ii): the Gaussian currents `eᵢ w 𝓛^d`, `w(x) = exp(-x · x)` | `gaussCurrent`, `gaussian_normal`, `gaussian_polar` | `Curves/Lemma31/Current.lean` |

For (ii) ⇒ (i) the paper uses [AM, Corollary 6.4], which is stated for `n ≥ 2` and fails for
`n = 1`. The route above covers every `d` (DPR Deviation 20; the citations of [AM] are corrected in
DPR Erratum 7).

### The mass of a metric functional, [AK, Definition 2.6]

Statement `exists_isAKMass` (`AFreeStatements/AKMassExists.lean`); proof
`AFree/Proofs/AKMassExistsProof.lean`, which applies `akmass` (`MetricCurrents/AKMass.lean`).

The infimum of two admissible measures is admissible, by splitting `f = fφ + f(1 - φ)` with a
Lipschitz function `φ` approximating a Hahn set (`akmass_pairwise_admissible`). A decreasing sequence
of admissible measures whose total masses converge to the infimum has an admissible limit, which is
the least admissible measure (`akmass_decreasing_limit`, `akmass_limit_admissible`, `akmass_minimal`).
See AK Deviations 1 and 2 and AK Erratum 1.

### The decomposability bundle, [AM, Section 2.7]

Statement `exists_isDecompBundle` (`AFreeStatements/DecompBundleExists.lean`); proof
`AFree/Proofs/DecompBundleExistsProof.lean`, which applies `Bundle.bundle_exists`
(`Curves/Bundle/Exists.lean`).

As in [AM, Lemma 2.3], the bundle is a minimizer of `V ↦ ∫ dim V dμ` (`Bundle.dimInt`) over the
class of test fields (`Bundle.exists_minimal_decompTestField`). The class is closed under countable
intersection (`Bundle.isDecompTestField_iInf`); the Borel measurability of the intersection comes
from the resolvent limit onto the kernel of a positive semidefinite matrix (`Bundle.borelinter`,
`Bundle.IsSymmPSD.tendsto_kerProj`, in `Curves/Bundle/Intersect.lean` and
`Curves/Bundle/Resolvent.lean`). Approximate tangents are tested against `C¹` arcs (AM Deviation 1).

## Shared infrastructure

- **Harmonic analysis** (`AFree/Harmonic/`, `AFree/Analysis/`). The Fourier transform and Fourier
  multipliers on `Vec d` (`vecFourier`, `vecMultiplier`); the symbol classes `S^s` (`IsSymbol`), with
  integrable kernels for negative order (`negKernel`, `memLp_negKernel`) and uniform Hörmander kernels
  for order zero (`exists_uniform_hormander_kernels`); the local weak type (1,1) estimate for a
  Hörmander kernel, by a Calderón–Zygmund argument (`exists_weakTypeOne_of_hormander`). Compactness of
  convolution with an `L¹` kernel (`exists_subseq_tendsto_conv`) plays the role of Lemma 2.1 in both
  proofs of Theorem 1.1; the Vitali lemma [DPR, Lemma 2.2] is `tendsto_setIntegral_abs_of_vitali`.
- **Measure theory** (`AFree/Measure/`, `AFree/Defs/Finite.lean`). The polar has norm one and passes
  to singular parts (`piEuclideanNorm_polar_eq_one`, `polar_lebesgueSingularPart_ae`); integration
  against a vector measure through its polar (`integral_smul_vectorMeasure_eq`); mollification of
  measures and concentration of singular ones (`mollifyMeasure`, `concentration`); doubling scales
  (`ae_doubling_scales`); block measures (`blockMeasure`).
- **`k`-vectors** (`AFree/Algebra/KVec/`). Alternation of the coordinate `wedge`
  (`wedge_eq_zero_of_dep`), the interior product of a wedge (`interiorProduct_wedge`), the
  equivalence `equiv_interiorProduct_kvecSpan`, simplicity in a hyperplane (`simplelin`) and the
  Plücker obstruction in `Λ₂(ℝ⁵)` (`pluckerP0_not_isSimpleKVec`).
- **Metric currents** (`AFree/MetricCurrents/`, `AFree/TopCurrents/`). The mass (`akmass`); the
  extension [AK, (2.3)], for currents (`akext`, AK Erratum 2); the chain rule [AK, (3.2)], by Taylor
  expansion on a grid with Lipschitz partitions of unity (`akchain`), and alternation
  (`akalt_matrix`); the density `ν` (`nu_main`). For top-dimensional currents: minors of Lipschitz
  maps and their weak-* continuity (`minorDet`, `wstar`), the currents `u_#` (`usharp`) and the
  representation `T = u_#` (`usharp_of_curr_ac`).
- **Curves and cone-null sets** (`AFree/Curves/`). Cones, `C`-curves and `C`-null sets
  ([AM, Section 4.9]; `cone`, `IsCCurve`, `IsCNull`) and the facts on `𝓗¹` they need; Rainwater's
  lemma and [AM, Corollary 7.2] (`rainwater_lemma`, `rainwater_prop`); the dichotomy
  [AM, Lemma 7.3] (`dichotomy`), with a Lusin-type `C¹` approximation of Lipschitz curves
  (`lusin_c1_approx`); the perturbation of [AM, Proposition 7.4] (`perturb_of_cnull`); curve currents
  (`curveCurrent`, `isNormalCurrentOn_curveCurrent`) and the exhaustion by curve mixtures
  (`exhaust_prop`, `conenull_ac`).
- **The decomposability bundle** (`AFree/Curves/Bundle/`, `AFree/Curves/BundleTop/`). Existence
  (`Bundle.bundle_exists`), the absolutely continuous case of [AM, Proposition 2.9(iii)]
  (`bundle_ac`), and `V = ℝ^d` almost everywhere implies `μ ≪ 𝓛^d` (`absolutelyContinuous_of_decompBundle_eq_top`, with the `C¹`-arc
  test `BundleTop.opt_test`). The proof of Theorem 1.14 adds a continuous frame adapted to `V`
  (`Rademacher.lem_frame`, AM Deviation 2).

## Dependencies

- **Mathlib** at `065356127b`, with the toolchain `leanprover/lean4:v4.35.0-rc2`. The statements use
  Mathlib's vector measures, their integral `∫ᵛ` and the Lebesgue decomposition; the Fourier
  transform on `Vec d` is transported from Mathlib's Fourier transform on inner product spaces.
- **EllipticRegularityLean** at `1e29da0`. Its `PDEFoundation` library supplies the coordinate model
  `PDE.Vec d = Fin d → ℝ`, the Euclidean norm and dot product (`PDE.vecEuclideanNorm`, `PDE.vecDot`),
  coordinate derivatives (`PDE.euclideanCoordDeriv`) and Euclidean balls (`PDE.euclideanBall`). In
  the first-order case of Theorem 1.1, the modules `CZStatements.WeakType.*`, imported by
  `AFree/Analysis/StrongConstancy.lean`, supply the representation of a solution of
  `div(M∇w) = div F` by the Newtonian potential `PDE.newtonPotentialMat M F`
  (`PDE.eq_newtonPotentialMat_of_div_eq_div`), the local weak type (1,1) estimate for the gradient of
  this potential (`PDE.exists_newtonPotentialMat_weakTypeOne`), and its smoothness and linearity
  (`PDE.contDiff_newtonPotentialMat_and_coordDeriv`, `PDE.newtonPotentialMat_linearCombination`).
  The case of order `k` uses the weak type (1,1) estimate of `AFree/Harmonic/` instead.
