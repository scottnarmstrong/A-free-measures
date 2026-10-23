# The structure of 𝒜-free measures in Lean

[![Build and verify](https://github.com/scottnarmstrong/A-free-measures/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/A-free-measures/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/A-free-measures/actions/workflows/comparators.yml/badge.svg)](https://github.com/scottnarmstrong/A-free-measures/actions/workflows/comparators.yml)

A Lean 4 and Mathlib formalization of

> G. De Philippis and F. Rindler, *On the structure of 𝒜-free measures and applications*,
> Ann. of Math. (2) **184** (2016), 1017–1039, [arXiv:1601.06543](https://arxiv.org/abs/1601.06543).

Every theorem, lemma and corollary of the paper is formalized and proved, together with Remarks
1.3, 1.4 and 1.11. This covers the main theorem (Theorem 1.1) for operators of every order, with a
measure on the right-hand side and with variable coefficients, and all of its applications in
Sections 1 and 3:
- Alberti's rank-one theorem;
- the polar structure of BD functions;
- the dimensional structure of normal currents;
- the converse of Rademacher's theorem;
- the absolute continuity of top-dimensional metric currents.

The auxiliary Lemmas 2.1 and 3.1 are formalized and proved as well.

The library uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and
contains no `sorry`. The paper cites three external inputs:
- Alberti and Marchese's theorem on the differentiability of Lipschitz functions;
- Schioppa's Alberti representations of metric currents;
- the Ambrosio–Kirchheim theory of metric currents.

They are not assumed: the parts of them that the proofs need are proved here. So are the Fourier
analysis (Hörmander–Mihlin multipliers and their weak type (1,1) bound) and the geometric measure
theory used along the way. The weak type (1,1) bound for the gradient of the Newtonian potential
comes from the dependency EllipticRegularityLean.

## Main results

Results are cited as [DPR] (the paper, with the numbering of arXiv:1601.06543v2), [AM] (G. Alberti and A. Marchese, *On the differentiability of Lipschitz functions
with respect to arbitrary measures*, Geom. Funct. Anal. 26 (2016), arXiv:1408.2379v2) and [AK]
(L. Ambrosio and B. Kirchheim, *Currents in metric spaces*, Acta Math. 185 (2000), numbered as
in the MPI-MIS preprint 21/2000). Each statement
is in its own file in [`AFreeStatements/`](AFreeStatements), in the namespace `AFree`.

| Result | Lean theorem |
|---|---|
| [DPR, Theorem 1.1], operators of order at most one | `polar_mem_waveConeFirstOrder` |
| [DPR, Theorem 1.1], operators of every order `k` | `polar_mem_waveCone` |
| The real wave cones equal the paper's (complex symbol), order one and order `k` | `mem_waveConeFirstOrder_iff_complexSymbol`, `mem_waveCone_iff_complexSymbol` |
| [DPR, Remark 1.3], a measure on the right-hand side | `polar_mem_waveCone_of_eq_measure` |
| [DPR, Remark 1.4], variable coefficients | `polar_mem_waveCone_var` |
| [DPR, Theorem 1.5], Alberti's rank-one theorem | `polar_lebesgueSingularPart_eq_tensor` |
| [DPR, Theorem 1.6], higher derivatives | `polar_lebesgueSingularPart_eq_tensorPow` |
| [DPR, Theorem 1.7], BD functions | `polar_lebesgueSingularPart_eq_symmTensor` |
| [DPR, Corollary 1.8], BD functions with `div u ∈ L²` | `polar_lebesgueSingularPart_eq_symmTensor_orth` |
| [DPR, Corollary 1.9], boundaryless `(d-1)`-currents | `exists_hyperplane_of_boundaryless` |
| [DPR, Theorem 1.10], normal currents | `exists_covector_interiorProduct_eq_zero` |
| [DPR, Theorem 1.10], the equivalent formulation | `interiorProduct_eq_zero_iff_mem_kvecSpan` |
| [DPR, Remark 1.11], linear algebra, simplicity a.e., the example in `ℝ⁵` | `isSimpleKVec_of_mem_kvecSpan`, `ae_isSimpleKVec_of_isLocNormalCurrent`, `not_ae_isSimpleKVec_example` |
| [DPR, Corollary 1.12] | `absolutelyContinuous_of_span_eq_top` |
| [DPR, Corollary 1.13] | `rank_polar_le_of_div_eq` |
| [DPR, Theorem 1.14], converse of Rademacher's theorem | `absolutelyContinuous_of_ae_differentiableAt` |
| [DPR, Theorem 1.15], `‖T‖ ≪ 𝓛^d` for metric `d`-currents | `absolutelyContinuous_of_isAKMass` |
| [DPR, Theorem 1.15], metric currents and flat chains (compact support) | `isTopFlatChain_iff_isMetricCurrent` |
| [DPR, Lemma 2.1], compactness of Bessel potentials | `exists_compact_besselPotential` |
| [DPR, Lemma 3.1] | `decompBundle_eq_top_iff` |
| The mass of a metric functional [AK, Definition 2.6] | `exists_isAKMass` |
| The decomposability bundle [AM, Section 2.7] | `exists_isDecompBundle` |

For example, Theorem 1.1 and Theorem 1.14 read as follows (`ι` and `κ` are finite index types):

```lean
theorem polar_mem_waveCone {d k : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFree Ω k A μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveCone k A
```

```lean
theorem absolutelyContinuous_of_ae_differentiableAt {d : ℕ} (μ : Measure (Vec d))
    [IsLocallyFiniteMeasure μ]
    (hμ : ∀ f : Vec d → ℝ, (∃ K, LipschitzWith K f) → ∀ᵐ x ∂μ, DifferentiableAt ℝ f x) :
    μ ≪ volume
```

The definitions they use are in [`AFree/Defs.lean`](AFree/Defs.lean). `ℝ^d` is `Vec d = Fin d → ℝ` with Lebesgue measure. An `ℝ^m`-valued
measure on an open set `Ω` is a finite vector measure with values in `ι → ℝ` whose total variation
vanishes outside `Ω`. Total variations, polars, `k`-vectors and Lipschitz constants are taken for
the Euclidean norm.

The paper's second assertion in Theorem 1.15, $\mathbf M^{\mathrm{met}}_d(\mathbb R^d)=\mathbf F_d(\mathbb R^d)$,
is formalized for compactly supported currents, as in [AK, Theorem 11.1]: flat chains are compactly
supported by definition, while metric currents need not be. This and the other places where the
formalization departs from the printed text are listed in
[`docs/ERRATA-AND-DEVIATIONS.md`](docs/ERRATA-AND-DEVIATIONS.md). That file covers misprints and
gaps in [DPR], [AM] and [AK], encodings, and proofs that follow a different route from the paper.
[`docs/PROOF-MAP.md`](docs/PROOF-MAP.md) explains how each proof is organized.

## Verification

Two independent checks accompany the build:

- **Axiom audit.** `scripts/check_axioms.py` checks that each of the 25 theorems above depends only
  on `propext`, `Classical.choice` and `Quot.sound`.
- **Comparator.** [`Challenges/AFreeMeasures/Challenge.lean`](Challenges/AFreeMeasures/Challenge.lean)
  restates the 25 theorems with every definition they use, importing Mathlib only.
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the theorems proved
  by the library (`Solution.lean`) have exactly these statements. It compares the statements
  together with their whole dependency closure, checks the axioms, and replays the proofs in the
  Lean kernel and in the independent NanoDa kernel.

## Building

Requirements: [elan](https://github.com/leanprover/elan); the toolchain `leanprover/lean4:v4.35.0-rc2`
is selected by `lean-toolchain`. Dependencies, pinned in `lake-manifest.json`:

- Mathlib at `065356127b`;
- [EllipticRegularityLean](https://github.com/scottnarmstrong/EllipticRegularityLean) at `1e29da0`, for the coordinate model
  `Vec d` and its Euclidean norm, and for the weak type (1,1) estimate for the gradient of the
  Newtonian potential used in the first-order case of Theorem 1.1.

```bash
lake exe cache get     # Mathlib build artifacts
lake build             # the library AFree and the 25 main theorems in AFreeStatements
lake build Challenges  # the comparator challenge, its solution and the axiom audit
```

Then the checks:

```bash
lake env lean Challenges/AFreeMeasures/AxiomsAudit.lean > axioms.log 2>&1
python3 scripts/check_axioms.py axioms.log Challenges/AFreeMeasures/AxiomsAudit.lean
scripts/verify_comparator.sh  # needs landrun and nanoda_bin; see the script header
```

From a fresh checkout, `lake exe cache get` and `lake build` take about three minutes on a 16-core
machine, including the EllipticRegularityLean modules that the library uses. A first CI run on a
hosted runner, with empty caches, takes considerably longer.

## Repository layout

- `AFree/Defs.lean`: the definitions used in the statements.
- `AFreeStatements/`: the 25 main theorems, one per file. Each proof is a single line that applies
  the theorem `AFree.<Name>Proof.result` from `AFree/Proofs/`.
- `AFree/`: the proofs.
  - `Paper/`: Theorem 1.1 and its applications in Sections 1–3.
  - `Harmonic/`: Fourier multipliers and the Hörmander–Mihlin estimate.
  - `Measure/`, `Analysis/`, `Algebra/`: measure theory, analysis and `k`-vectors.
  - `Curves/`, `Rademacher/`: cone-null sets, Rainwater's lemma, the decomposability bundle and Theorem 1.14.
  - `MetricCurrents/`, `TopCurrents/`: metric currents and Theorem 1.15.
- `Challenges/AFreeMeasures/`: the comparator challenge, its solution and the axiom audit.
- `docs/`: the proof map, and the errata and deviations.

## Author, AI use and acknowledgements

The Lean development is by **Scott Armstrong**. The Lean code was written by AI agents (Claude Opus
5.5 and Claude Sonnet 5.5 in Claude Code) under his supervision. Each main theorem's proof received
a separate agent audit, and Claude Fable 5.1 independently reviewed the documentation, the
citations, the errata and the comparator challenge. This is not external peer review. The Lean
kernel checks every proof; see [`formalization.yaml`](formalization.yaml) for details.

To cite this formalization, use [`CITATION.cff`](CITATION.cff). Scott Armstrong was supported by the
European Research Council (ERC) under the European Union's Horizon Europe research and innovation
programme, grant agreement No. 101200828.

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
