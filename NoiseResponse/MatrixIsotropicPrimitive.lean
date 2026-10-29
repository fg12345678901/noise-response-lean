/- Added by cx on 2026-10-29: an actual C2 matrix trace potential for
   every finite isotropic spectrum on a differentiable supported region.
   The derivative is proved by power series; eigenvalues only evaluate it. -/
module

public import NoiseResponse.IsotropicSpectralCoefficients
public import NoiseResponse.SupportedTracePotential
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1800
set_option maxHeartbeats 6000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.IsotropicSpectrum
variable {𝕜 Ω m : Type*} [RCLike 𝕜] [MeasurableSpace Ω] [Fintype m] [DecidableEq m] [Nonempty m]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedSpace ℝ (Matrix m m 𝕜) where
  norm_smul_le r B := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜),norm_smul,RCLike.norm_ofReal,
      Real.norm_eq_abs]
local instance : NormedAlgebra ℝ (Matrix m m 𝕜) where
  norm_smul_le := norm_smul_le

def matrixTrace : Matrix m m 𝕜 →L[ℝ] ℝ :=
  (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).comp (Matrix.traceLinearMap m ℝ 𝕜).toContinuousLinearMap

@[simp] theorem matrixTrace_apply (B : Matrix m m 𝕜) : matrixTrace B=RCLike.re B.trace := rfl

theorem matrixTrace_cyclic (B C : Matrix m m 𝕜) : matrixTrace (B*C)=matrixTrace (C*B) :=
  congrArg RCLike.re (Matrix.trace_mul_comm B C)

theorem trace_power_eigenvalues (B : Matrix m m 𝕜) (hB : B.IsHermitian) (k : ℕ) :
    (B^k).trace=∑ i, (hB.eigenvalues i : 𝕜)^k := by
  conv_lhs => rw [hB.spectral_theorem,← map_pow,Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,Matrix.one_mul]
  simp [Matrix.diagonal_pow]

theorem matrixPrimitive_eigenvalues (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hu : ∀ x, ‖z x‖=1) (B : Matrix m m 𝕜) (hB : B.IsHermitian)
    (hBn : ‖B‖<1) :
    NoiseResponse.TraceSeries.tracePrimitive matrixTrace (spectralCoeff ν z) B=
      ∑ i, scalarPrimitive ν z (hB.eigenvalues i) := by
  let q := (‖B‖+1)/2
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q<1 := by dsimp only [q]; linarith
  have hBq : ‖B‖<q := by dsimp only [q]; linarith
  have he (i : m) : ‖hB.eigenvalues i‖ ≤ q :=
    (spectrum.norm_le_norm_of_mem (hB.eigenvalues_mem_spectrum_real i)).trans hBq.le
  have hs (i : m) := NoiseResponse.TraceSeries.primitiveTerm_summable
    (ContinuousLinearMap.id ℝ ℝ) (spectralCoeff ν z) (hB.eigenvalues i) q hq0 (he i)
      (spectralCoeff_summable ν z hu q hq0 hq1)
  change (∑' n, spectralCoeff ν z n/(n+1 : ℝ)*matrixTrace (B^(n+1)))=
    ∑ i, ∑' n, spectralCoeff ν z n/(n+1 : ℝ)*(hB.eigenvalues i)^(n+1)
  simp only [matrixTrace_apply,trace_power_eigenvalues B hB,map_sum,
    ← RCLike.ofReal_pow,RCLike.ofReal_re,Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => hs i)

def isotropicPotential (ν : Measure Ω) (z : Ω → ℂ) (η : ℝ)
    (P H : E → Matrix m m 𝕜) : E → ℝ :=
  NoiseResponse.TraceSeries.supportedPotential matrixTrace (spectralCoeff ν z) η P H

theorem isotropicPotential_hasFDerivAt (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hu : ∀ x, ‖z x‖=1) (η : ℝ) (hη : η ≠ 0)
    (P H : E → Matrix m m 𝕜) (x : E)
    (hP : DifferentiableAt ℝ P x) (hH : DifferentiableAt ℝ H x)
    (hPP : ∀ᶠ y in 𝓝 x, P y*P y=P y) (hPH : P x*H x=H x) (hHP : H x*P x=H x)
    (hB : ‖P x-η • H x‖<1) :
    HasFDerivAt (isotropicPotential ν z η P H)
      ((1/2 : ℝ) • ((NoiseResponse.TraceSeries.traceLeftCLM matrixTrace
        (NoiseResponse.TraceSeries.coefficientSeries (spectralCoeff ν z) (P x-η • H x))).comp
          (fderiv ℝ H x))) x := by
  let q := (‖P x-η • H x‖+1)/2
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q<1 := by dsimp only [q]; linarith
  have hBq : ‖P x-η • H x‖<q := by dsimp only [q]; linarith
  exact NoiseResponse.TraceSeries.supportedPotential_derivative matrixTrace matrixTrace_cyclic
    (spectralCoeff ν z) η hη P H x hP hH hPP hPH hHP q hBq
      (spectralCoeff_summable ν z hu q hq0 hq1)

theorem isotropicPotential_contDiffAt (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hu : ∀ x, ‖z x‖=1) (η : ℝ)
    (P H : E → Matrix m m 𝕜) (x : E)
    (hP : ContDiffAt ℝ 2 P x) (hH : ContDiffAt ℝ 2 H x)
    (hB : ‖P x-η • H x‖<1) : ContDiffAt ℝ 2 (isotropicPotential ν z η P H) x := by
  let q := (‖P x-η • H x‖+1)/2
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q<1 := by dsimp only [q]; linarith
  have hBq : ‖P x-η • H x‖<q := by dsimp only [q]; linarith
  have hc := NoiseResponse.TraceSeries.tracePrimitive_contDiffAt matrixTrace matrixTrace_cyclic
    (spectralCoeff ν z) (P x-η • H x) q hBq (spectralCoeff_summable ν z hu q hq0 hq1)
  have hh := (hc.comp x (hP.sub (hH.const_smul η))).const_smul (-(2*η)⁻¹)
  simpa only [isotropicPotential,NoiseResponse.TraceSeries.supportedPotential,smul_eq_mul] using! hh

end NoiseResponse.IsotropicSpectrum

#print axioms NoiseResponse.IsotropicSpectrum.isotropicPotential_hasFDerivAt
#print axioms NoiseResponse.IsotropicSpectrum.matrixPrimitive_eigenvalues
