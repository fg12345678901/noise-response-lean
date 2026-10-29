/- Added by cx on 2026-10-29: interchange a finite positive scalar
   spectral measure with the convergent matrix response series. -/
module

public import NoiseResponse.IsotropicResolventSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1800
set_option maxHeartbeats 7000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.IsotropicSpectrum
variable {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
local instance : NormedSpace ℝ (Matrix n n ℂ) where
  norm_smul_le r B := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),norm_smul,RCLike.norm_ofReal,
      Real.norm_eq_abs]
local instance : NormedAlgebra ℝ (Matrix n n ℂ) where
  norm_smul_le := norm_smul_le

theorem coefficientSeries_spectral_integral (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖=1)
    (B : Matrix n n ℂ) (hB : ‖B‖<1) :
    NoiseResponse.TraceSeries.coefficientSeries (spectralCoeff ν z) B=
      ∫ x, (1-((z x).re : ℂ)) •
        (matrixResolvent B (z x)*matrixResolvent B (star (z x))) ∂ν := by
  let bound : ℕ → Ω → ℝ := fun k _ => 2*(k+1 : ℝ)*‖B‖^k
  have hmeas (k : ℕ) : AEStronglyMeasurable (fun x => poissonCoeff (z x) k • B^k) ν := by
    have hs : Measurable (fun x => poissonCoeff (z x) k) := by
      unfold poissonCoeff doubleCoeff
      fun_prop
    exact hs.aestronglyMeasurable.smul_const (B^k)
  have hb (k : ℕ) : ∀ᵐ x ∂ν, ‖poissonCoeff (z x) k • B^k‖ ≤ bound k x := by
    apply Eventually.of_forall
    intro x
    rw [norm_smul]
    exact (mul_le_mul (poissonCoeff_bound (z x) (hu x) k) (norm_pow_le B k)
      (norm_nonneg _) (by positivity)).trans_eq (by rfl)
  have hs : Summable (fun k : ℕ => 2*(k+1 : ℝ)*‖B‖^k) := by
    simpa only [mul_assoc] using (linear_geometric_summable ‖B‖ (norm_nonneg B) hB).mul_left 2
  have hi : Integrable (fun x => ∑' k, bound k x) ν :=
    integrable_const (∑' k : ℕ, 2*(k+1 : ℝ)*‖B‖^k)
  have hpoint (x : Ω) : HasSum (fun k => poissonCoeff (z x) k • B^k)
      ((1-((z x).re : ℂ)) • (matrixResolvent B (z x)*matrixResolvent B (star (z x)))) := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using! poisson_matrix_hasSum B hB (z x) (hu x)
  have h := hasSum_integral_of_dominated_convergence bound hmeas hb
    (Eventually.of_forall (fun _ => hs)) hi (Eventually.of_forall hpoint)
  simpa only [integral_smul_const,spectralCoeff,NoiseResponse.TraceSeries.coefficientSeries] using h.tsum_eq

theorem coefficientSeries_readout_integral (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖=1)
    (B : Matrix n n ℂ) (hB : ‖B‖<1) (L : Matrix n n ℂ →L[ℝ] ℝ) :
    L (NoiseResponse.TraceSeries.coefficientSeries (spectralCoeff ν z) B)=
      ∫ x, L ((1-((z x).re : ℂ)) •
        (matrixResolvent B (z x)*matrixResolvent B (star (z x)))) ∂ν := by
  let bound : ℕ → Ω → ℝ := fun k _ => ‖L‖*(2*(k+1 : ℝ)*‖B‖^k)
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun x => L (poissonCoeff (z x) k • B^k)) ν := by
    have hs : Measurable (fun x => poissonCoeff (z x) k) := by
      unfold poissonCoeff doubleCoeff
      fun_prop
    simpa only [map_smul,smul_eq_mul] using
      (hs.mul_const (L (B^k))).aestronglyMeasurable
  have hb (k : ℕ) : ∀ᵐ x ∂ν, ‖L (poissonCoeff (z x) k • B^k)‖ ≤ bound k x := by
    apply Eventually.of_forall
    intro x
    apply (L.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg L)
    rw [norm_smul]
    exact mul_le_mul (poissonCoeff_bound (z x) (hu x) k) (norm_pow_le B k)
      (norm_nonneg _) (by positivity)
  have hs : Summable (fun k : ℕ => ‖L‖*(2*(k+1 : ℝ)*‖B‖^k)) := by
    exact ((linear_geometric_summable ‖B‖ (norm_nonneg B) hB).mul_left 2).congr
      (fun k => by ring) |>.mul_left ‖L‖
  have hi : Integrable (fun x => ∑' k, bound k x) ν :=
    integrable_const (∑' k : ℕ, ‖L‖*(2*(k+1 : ℝ)*‖B‖^k))
  have hpoint (x : Ω) := (poisson_matrix_hasSum B hB (z x) (hu x)).mapL L
  have hp (x : Ω) : HasSum (fun k => L (poissonCoeff (z x) k • B^k))
      (L ((1-((z x).re : ℂ)) •
        (matrixResolvent B (z x)*matrixResolvent B (star (z x))))) := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hpoint x
  have hh := hasSum_integral_of_dominated_convergence bound hmeas hb
    (Eventually.of_forall (fun _ => hs)) hi (Eventually.of_forall hp)
  have hq := NoiseResponse.TraceSeries.coefficientSeries_summable (spectralCoeff ν z) B ‖B‖
    (norm_nonneg B) le_rfl (spectralCoeff_summable ν z hu ‖B‖ (norm_nonneg B) hB)
  have hh' : HasSum (fun k => spectralCoeff ν z k*L (B^k))
      (∫ x, L ((1-((z x).re : ℂ)) •
        (matrixResolvent B (z x)*matrixResolvent B (star (z x)))) ∂ν) := by
    simpa only [map_smul,smul_eq_mul,integral_mul_const,spectralCoeff] using hh
  exact ((by simpa only [NoiseResponse.TraceSeries.coefficientSeries,map_smul,smul_eq_mul]
    using hq.hasSum.mapL L) : HasSum (fun k => spectralCoeff ν z k*L (B^k))
      (L (NoiseResponse.TraceSeries.coefficientSeries (spectralCoeff ν z) B))).unique hh'

end NoiseResponse.IsotropicSpectrum
