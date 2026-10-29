/- Added by cx on 2026-10-29: exact stable scalar normal-transfer
   kernels behind the full flat-geometry response. -/
module

public import NoiseResponse.SpectralResolvent
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 3000000
noncomputable section
open Complex
open scoped ComplexConjugate
namespace NoiseResponse.Classification

def causalCrossKernel (a : ℝ) (z : ℂ) : ℂ := z/(1-(a : ℂ)*z)
def normalPowerKernel (a : ℝ) (z : ℂ) : ℂ :=
  1/((1-(a : ℂ)*z)*(1-(a : ℂ)*star z))
def normalTransfer (a : ℝ) (z : ℂ) : ℂ := 1/(z-(a : ℂ))

theorem stable_kernel_den_ne_zero (a : ℝ) (ha : ‖a‖<1) (z : ℂ) (hz : ‖z‖=1) :
    1-(a : ℂ)*z ≠ 0 := by
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  have hn' : (1 : ℝ)=‖a‖ := by simpa only [norm_one, norm_mul, Complex.norm_real, hz, mul_one] using hn
  linarith

theorem causalCrossKernel_bound (a : ℝ) (ha : ‖a‖<1) (z : ℂ) (hz : ‖z‖=1) :
    ‖causalCrossKernel a z‖ ≤ 1/(1-‖a‖) := by
  have hden : 1-‖a‖ ≤ ‖1-(a : ℂ)*z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((a : ℂ)*z)
    simpa only [norm_one, norm_mul, Complex.norm_real, hz, mul_one] using h
  rw [causalCrossKernel, norm_div, hz]
  exact one_div_le_one_div_of_le (by linarith) hden

theorem normalPowerKernel_poisson (a : ℝ) (ha : ‖a‖<1) (z : ℂ) (hz : ‖z‖=1) :
    normalPowerKernel a z = (1-(a : ℂ)^2)⁻¹ *
      (1+(a : ℂ)*(causalCrossKernel a z+star (causalCrossKernel a z))) := by
  have hd := stable_kernel_den_ne_zero a ha z hz
  have hdz := stable_kernel_den_ne_zero a ha (star z) (by simpa using hz)
  have hab : -1<a ∧ a<1 := by simpa only [Real.norm_eq_abs] using abs_lt.mp ha
  have hsq : (1 : ℂ)-(a : ℂ)^2 ≠ 0 := by
    have hp : 0 < 1-a^2 := by
      nlinarith [mul_pos (sub_pos.mpr hab.2) (by linarith [hab.1] : 0 < 1+a)]
    exact_mod_cast ne_of_gt hp
  have hzprod : z*star z=1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hstar : star (causalCrossKernel a z)=star z/(1-(a : ℂ)*star z) := by
    simp [causalCrossKernel, star_div, star_sub, star_mul, mul_comm]
  have hnum : (1-(a : ℂ)*z)*(1-(a : ℂ)*star z)+
      (a : ℂ)*(z*(1-(a : ℂ)*star z)+star z*(1-(a : ℂ)*z))=1-(a : ℂ)^2 := by
    calc
      _ = 1-(a : ℂ)^2*(z*star z) := by ring
      _ = _ := by rw [hzprod, mul_one]
  rw [hstar]
  unfold normalPowerKernel causalCrossKernel
  field_simp [hd, hdz, hsq]
  linear_combination hnum + (2*(a : ℂ)^2)*hzprod

theorem normalTransfer_equation (a : ℝ) (ha : ‖a‖<1) (z : ℂ) (hz : ‖z‖=1) :
    (z-(a : ℂ))*normalTransfer a z=1 := by
  have hd : z-(a : ℂ) ≠ 0 := by
    intro he
    have hn := congrArg norm (sub_eq_zero.mp he)
    have hn' : (1 : ℝ)=‖a‖ := by simpa only [hz, Complex.norm_real] using hn
    linarith
  exact mul_one_div_cancel hd

theorem normalTransfer_star (a : ℝ) (ha : ‖a‖<1) (z : ℂ) (hz : ‖z‖=1) :
    star (normalTransfer a z)=causalCrossKernel a z := by
  have hd := stable_kernel_den_ne_zero a ha z hz
  have hdz : star z-(a : ℂ) ≠ 0 := by
    intro he
    have hn := congrArg norm (sub_eq_zero.mp he)
    have hn' : (1 : ℝ)=‖a‖ := by simpa only [norm_star, hz, Complex.norm_real] using hn
    linarith
  have hp : z*star z=1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hs : star (normalTransfer a z)=1/(star z-(a : ℂ)) := by
    simp [normalTransfer]
  rw [hs]
  unfold causalCrossKernel
  field_simp [hd, hdz]
  linear_combination -hp

theorem normalTransfer_power (a : ℝ) (ha : ‖a‖<1) (z : ℂ) (hz : ‖z‖=1) :
    normalTransfer a z*star (normalTransfer a z)=normalPowerKernel a z := by
  have hd := stable_kernel_den_ne_zero a ha z hz
  have hdz := stable_kernel_den_ne_zero a ha (star z) (by simpa using hz)
  have hp : z*star z=1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hg : normalTransfer a z=star (causalCrossKernel a z) := by
    have he := congrArg star (normalTransfer_star a ha z hz)
    simpa only [star_star] using he
  rw [normalTransfer_star a ha z hz, hg]
  have hs : star (causalCrossKernel a z)=star z/(1-(a : ℂ)*star z) := by
    simp [causalCrossKernel, mul_comm]
  rw [hs]
  unfold causalCrossKernel normalPowerKernel
  rw [div_mul_div_comm, mul_comm (star z) z, hp,
    mul_comm (1-(a : ℂ)*star z) (1-(a : ℂ)*z)]

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.normalPowerKernel_poisson
