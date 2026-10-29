# Manuscript-to-Lean correspondence

## Scope and mathematical objects

The manuscript fixes a positive step size and output dimension at least
two. The Lean classification applies to a nonempty finite output type,
and in particular to the stated manuscript setting.

* `PSDMatrixMeasure.entry` is a matrix of actual finite complex measures.
  Positivity holds on every measurable set. The finite trace control
  measure and an integrable a.e.-PSD RN density are constructed.
* `RealReflection` is the real-process reflection law on the original
  measure. The frequency circle is `AddCircle T` with positive period;
  `fourier 1` parametrizes the unit circle and the Nyquist point is `T/2`.
* `ResidualGeometry.jacobian f ι` is the actual matrix of the Frechet
  derivative of a C3 residual restricted to a C3 clean immersed chart.
  `AdmissibleAt` requires zero residual, the tangent/kernel equality,
  constant rank along the branch and a strict normal stability gap.
  `admissible_uniform_margin` supplies an open neighborhood with one
  common bound below one.
* The normal projection and transfer are constructed from that Jacobian.
  `zero_transfer_penrose` proves all four Moore--Penrose equations.
  `response_original_one_form` identifies the audited A4 coefficient with
  the real trace one-form of manuscript equation (9).
* `HasLocalPotential` asserts a genuine local C2 function with the actual
  Frechet differential equal to the response in every chart direction.
  `AllResidualPotentials` quantifies over all finite parameter/chart
  dimensions, including zero.
* `HasClassifiedSpectrum` gives the identity on every measurable set:
  a finite nonnegative reflection-symmetric scalar measure without endpoint
  atoms, plus real PSD atoms at zero and Nyquist.

## Explicit potential

The isotropic potential is defined by a convergent cyclic trace series.
Its C2 derivative is proved before using eigenvalues to evaluate it.
`manuscript_potential_formula` converts the input Gram expression into
the positive output-Gram eigenvalue sum, with multiplicities, in (13).
`phi_derivative` gives the same scalar primitive's derivative in (14).
The zero-frequency term uses the actual output range projection; the
Nyquist term uses the actual output matrix inverse.

`globalPotential` is a single-valued function of the residual Jacobian.
`globalPotential_pullback` identifies its restrictions in all clean charts;
`classified_global_potential` proves their negative differential is the
original response. The zero-dimensional parameter case has zero response
and the zero potential.

## Proof organization

The necessity chain constructs the original-measure representation,
restricts actual ambient residuals to rank-one probes, identifies both
endpoint limits and all integer Fourier coefficients, and concludes the
measure decomposition. Sufficiency constructs smooth projectors and stable
transfers, differentiates the scalar and endpoint potentials and combines
them under the finite spectral integral.

The correspondence above is the reading guide for the mathematical
translation. The Lean checker verifies the resulting formal statements.
The selected Theorem 2 component is its local matrix curvature identity;
the moving averaging theorem is treated in the manuscript.
