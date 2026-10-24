# A dimension-free weak-type (1,1) bound for the Gaussian Riesz transforms, in Lean 4

This repository contains a Lean 4 formalization, built on [Mathlib](https://github.com/leanprover-community/mathlib4), of the main results of

> Cristian E. Gutiérrez and Juan J. Manfredi,
> *A direct obstacle proof of a dimension-free weak-type (1,1) bound for the Gaussian Riesz transforms*,
> [arXiv:2610.26478](https://arxiv.org/abs/2610.26478), 12 October 2026.

The paper's two theorems (3.1 and 5.1), Proposition 5.3 and Corollaries 5.4 and 5.5 are stated and proved, together with everything their proofs use. The development contains no `sorry` and no axioms: every result depends only on the three standard axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`).

## Results

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 3.1, the Gaussian obstacle decomposition | `ObstacleDecomposition`, `ObstacleDecompositionUnique`, `SqrtDomainSobolev` | [`ObstacleDecomposition.lean`](GaussianRiesz/ObstacleDecomposition.lean), [`ObstacleDecompositionUnique.lean`](GaussianRiesz/ObstacleDecompositionUnique.lean), [`SqrtDomainSobolev.lean`](GaussianRiesz/SqrtDomainSobolev.lean) |
| Theorem 5.1, the dimension-free weak-type (1,1) estimate | `EndpointTheorem` | [`EndpointTheorem.lean`](GaussianRiesz/EndpointTheorem.lean) |
| Proposition 5.3, the principal-value realization | `PVIdentification` | [`PVIdentification.lean`](GaussianRiesz/PVIdentification.lean) |
| Corollary 5.4, coordinate and historical spectral conventions | `CoordinateEndpointBound`, `SpectralNormalizationBound`, `UnnormalizedMeasureInvariance` | [`CoordinateEndpointBound.lean`](GaussianRiesz/CoordinateEndpointBound.lean), [`SpectralNormalizationBound.lean`](GaussianRiesz/SpectralNormalizationBound.lean), [`UnnormalizedMeasureInvariance.lean`](GaussianRiesz/UnnormalizedMeasureInvariance.lean) |
| Corollary 5.5, the complex-valued estimate with constant 8/π | `ComplexEndpointTheorem` | [`ComplexEndpointTheorem.lean`](GaussianRiesz/ComplexEndpointTheorem.lean) |

Theorem 3.1 is split into three declarations: existence of the pair (u, g) together with all the listed properties and the characterization of u as the unique minimizer of the obstacle functional (`ObstacleDecomposition`), uniqueness of the pair (`ObstacleDecompositionUnique`), and the inclusion Dom(B) ⊆ W<sup>1,2</sup>(γ) with ‖Bv‖ = ‖Dv‖ (`SqrtDomainSobolev`). Corollary 5.4 is split along its three assertions.

## The main theorem

`GaussMeasure n` is the Gaussian probability measure π<sup>−n/2</sup> e<sup>−|x|²</sup> dx on ℝ<sup>n</sup>. `RieszTransform` is the energy-normalized vector Riesz transform R<sub>γ</sub> = D L<sup>−1/2</sup> Π<sub>0</sub> on real L²(γ), with D = 2<sup>−1/2</sup>∇ the weak gradient, and `ToL1` is the inclusion of L²(γ) into L¹(γ). Theorem 5.1 says that R<sub>γ</sub> has exactly one linear extension to L¹(γ), with values in the a.e.-classes of measurable ℝ<sup>n</sup>-valued functions, that satisfies the weak-type bound with constant 2, for every n:

```lean
theorem EndpointTheorem {n : ℕ} :
    ∃! T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)),
      (∀ v : Lp ℝ 2 (GaussMeasure n),
          T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
            →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
        ∧ ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
            ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖}
              ≤ ENNReal.ofReal (2 * ‖f‖)
```

`ComplexEndpointTheorem` is the same statement for complex inputs, with constant 8/π.

## One deviation from the paper

The paper's proof of Proposition 5.3 quotes the fixed-dimensional maximal estimate (5.15) of Fabes, Gutiérrez and Scotto, which is not in Mathlib. The formalization does not assume it. The lemma `GaussMaximalTruncationLocal` proves a localized form instead: the level set of the maximal truncation is intersected with a ball B(0, R), and the constant depends on n, j and R. The proof goes through Cotlar's inequality and the endpoint estimate of Theorem 5.1. Since the paper uses (5.15) only for almost-everywhere and limit statements, the localized form is enough, and `PVIdentification` is the paper's Proposition 5.3 as stated, with the bound 2. Appendix A of the blueprint explains the deviation in detail.

## Blueprint

The directory [`blueprint/`](blueprint) contains a natural-language statement and a detailed proof for every Lean declaration, cross-referenced to the paper and to each other. They are collected, in dependency order, in [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf). To rebuild it, run `pdflatex blueprint.tex` three times in that directory.

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
git clone <repository URL> gaussianriesz-lean
cd gaussianriesz-lean
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean Axioms.lean # print the axioms used by each main result
```

The project is pinned to Lean `v4.33.0` and Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. Continuous integration rebuilds the project and checks the axioms on every push.

## Layout

```
GaussianRiesz.lean         root module, imports the main results
GaussianRiesz/             one file per definition, lemma or theorem
Axioms.lean                #print axioms for the main results
blueprint/blueprint.tex    natural-language companion (inputs blueprint/nodes/*.tex)
```

## How this formalization was produced

The formalization was produced with Trellis, an AI-assisted formalization pipeline that uses Claude (Anthropic). Each node was reviewed automatically for soundness of its natural-language proof, for faithfulness to the paper, and for agreement between its Lean statement and its natural-language statement. The deviation described above was reviewed separately. The Lean kernel checks every proof.

<!-- TODO before release: replace this comment with a sentence confirming that the authors have read the Lean statements of the definitions and the main results. -->

## Citation

Please cite the paper; see [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0, the license used by Mathlib. See [`LICENSE`](LICENSE).
