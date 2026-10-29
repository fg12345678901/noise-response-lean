# Noise-response spectral classification: Lean proofs

Machine-checked proofs supporting **Theorem 3**, its explicit potential,
and the selected local curvature identity in *When Do Noise-Induced
Learning Dynamics Admit a Potential?*

Release **v1.0.0** contains the accepted proof snapshot: 81 proof modules
and 437 named lemmas/theorems. The manuscript theorem corresponds to
`NoiseResponse.ResidualGeometry.theorem3_universal_spectral_classification`.

## Rebuild

Install the Lean toolchain specified in `lean-toolchain`, then run:

```sh
lake exe cache get
python3 scripts/check.py
```

The checker verifies source hashes, builds all modules, inspects every named
theorem's axiom dependencies and repeats the import check with `--trust=0`.
Its logs and machine-readable receipt are written to `_verification/`.
Choose a fresh `--output` directory for each repeat.

Lean is pinned to **4.35.0**, and mathlib to commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The proof uses standard classical
foundations (`propext`, `Classical.choice`, `Quot.sound`).

## Read the result

| Manuscript result | Lean declaration | Source |
|---|---|---|
| Theorem 3: three equivalent conditions | `ResidualGeometry.theorem3_universal_spectral_classification` | [Theorem3.lean](NoiseResponse/Theorem3.lean) |
| Equation (13): explicit potential | `ManuscriptPotential.manuscript_potential_formula` | [ManuscriptPotentialFormula.lean](NoiseResponse/ManuscriptPotentialFormula.lean) |
| Equation (14): scalar derivative | `IsotropicSpectrum.phi_derivative` | [IsotropicScalarPotential.lean](NoiseResponse/IsotropicScalarPotential.lean) |
| Single potential shared by all charts | `ResidualGeometry.classified_global_potential` | [Theorem3Complete.lean](NoiseResponse/Theorem3Complete.lean) |
| Local curvature kernel | `Curvature.frequency_curvature` | [CurvatureCalculus.lean](NoiseResponse/CurvatureCalculus.lean) |

All names above have prefix `NoiseResponse.`. Start with
[CORRESPONDENCE.md](CORRESPONDENCE.md) for the hypotheses and definitions
connecting the manuscript to these declarations. `THEOREM_CATALOG.json`
lists every named theorem and its source location.

The formalization covers the universal classification of the frozen
response and its explicit potential in clean constant-rank charts. The
paper's moving stochastic averaging and other consequences have their
ordinary mathematical proofs in the manuscript.

## Reproducible snapshot

`SOURCE_MANIFEST.json` records exact source hashes. `SOURCE_PROVENANCE.json`
links this portable artifact to the accepted proof development. The public
package adds documentation, a portable checker and CI; the 83 Lean source
files are byte-identical to the accepted snapshot.

Use the [v1.0.0 release](https://github.com/fg12345678901/noise-response-lean/releases/tag/v1.0.0) when citing this artifact.
The manuscript and formal statements are authored and reviewed together;
proof development used AI assistance.

## License

The original formalization and accompanying code are licensed under
Apache-2.0. Lean and mathlib are separate dependencies with their own
licenses; see [THIRD_PARTY.md](THIRD_PARTY.md).
