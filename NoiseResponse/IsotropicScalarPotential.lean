/- Added by cx on 2026-10-29: the actual scalar Phi of manuscript (14),
   constructed from the convergent spectral primitive at a=1-eta*h. -/
module

public import NoiseResponse.IsotropicSpectralCoefficients
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1500
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Complex
open scoped ComplexConjugate
namespace NoiseResponse.IsotropicSpectrum
open NoiseResponse.Classification
variable {Ω : Type*} [MeasurableSpace Ω]

theorem scalarKernel_real_formula (a : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    scalarKernel a z=(1-z.re)/(1-2*a*z.re+a^2) := by
  have hprod : z*star z=1 := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hz]
    norm_num
  have hsum : z+star z=(2*z.re : ℝ) := by
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  have hden : (1-(a : ℂ)*z)*(1-(a : ℂ)*star z)=((1-2*a*z.re+a^2 : ℝ) : ℂ) := by
    calc
      _ = 1-(a : ℂ)*(z+star z)+(a : ℂ)^2*(z*star z) := by ring
      _ = _ := by rw [hsum,hprod]; push_cast; ring
  unfold scalarKernel normalPowerKernel
  rw [hden]
  have he : (1 : ℂ)/((1-2*a*z.re+a^2 : ℝ) : ℂ)=
      (((1/(1-2*a*z.re+a^2) : ℝ)) : ℂ) := by simp
  rw [he,Complex.ofReal_re]
  ring

def phi (ν : Measure Ω) (z : Ω → ℂ) (η h : ℝ) : ℝ :=
  -η⁻¹*scalarPrimitive ν z (1-η*h)

theorem phi_derivative (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖=1)
    (η : ℝ) (hη : η ≠ 0) (h : ℝ) (ha : ‖1-η*h‖<1) :
    HasDerivAt (phi ν z η)
      (∫ x, (1-(z x).re)/(1-2*(1-η*h)*(z x).re+(1-η*h)^2) ∂ν) h := by
  have hlin : HasDerivAt (fun t : ℝ => 1-η*t) (-η) h := by
    simpa only [Pi.neg_apply,id_eq,mul_one,sub_eq_add_neg] using!
      (((hasDerivAt_id h).const_mul η).neg.const_add 1)
  have hp := (scalarPrimitive_derivative ν z hz hu (1-η*h) ha).comp h hlin
  have hh := hp.const_mul (-η⁻¹)
  have he : (∫ x, scalarKernel (1-η*h) (z x) ∂ν)=
      ∫ x, (1-(z x).re)/(1-2*(1-η*h)*(z x).re+(1-η*h)^2) ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => scalarKernel_real_formula _ _ (hu x))
  rw [← he]
  convert! hh using 1
  field_simp

end NoiseResponse.IsotropicSpectrum

#print axioms NoiseResponse.IsotropicSpectrum.phi_derivative
