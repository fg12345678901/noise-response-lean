/- Added by cx on 2026-10-29: actual differentiation of the two-axis
   restrictions of the rank-one response (B1). -/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
namespace NoiseResponse.Classification

theorem tangent_composition_hasDerivAt (f : ℝ → ℝ) (a η : ℝ)
    (hf : DifferentiableAt ℝ f a) :
    HasDerivAt (fun t : ℝ => f (a-η*t^2)) 0 0 := by
  have hi : HasDerivAt (fun t : ℝ => a-η*t^2) 0 0 := by
    convert (hasDerivAt_const (0 : ℝ) a).fun_sub
      (((hasDerivAt_id (0 : ℝ)).fun_pow 2).const_mul η) using 1 <;> norm_num
  simpa only [Function.comp_def, mul_zero] using hf.hasDerivAt.comp_of_eq 0 hi (by norm_num)

def tangentReadout (k00 k01 c00 c01 c11 : ℝ → ℝ) (a η r t : ℝ) : ℝ :=
  let b := a-η*t^2
  k00 b*r + k01 b*t -
    ((c00 b*r^2 + 2*c01 b*r*t + c11 b*t^2) / ((r^2+t^2)*(1+b)))*r

/-- The tangential derivative at (r,0) includes the covariance term.
    This is an actual quotient/product-rule calculation of (B1). -/
theorem tangent_readout_hasDerivAt
    (k00 k01 c00 c01 c11 : ℝ → ℝ) (a η r : ℝ)
    (hr : r ≠ 0) (ha : 1+a ≠ 0)
    (hk00 : DifferentiableAt ℝ k00 a) (hk01 : DifferentiableAt ℝ k01 a)
    (hc00 : DifferentiableAt ℝ c00 a) (hc01 : DifferentiableAt ℝ c01 a)
    (hc11 : DifferentiableAt ℝ c11 a) :
    HasDerivAt (tangentReadout k00 k01 c00 c01 c11 a η r)
      (k01 a - 2*c01 a/(1+a)) 0 := by
  have hk0 := tangent_composition_hasDerivAt k00 a η hk00
  have hk1 := tangent_composition_hasDerivAt k01 a η hk01
  have hc0 := tangent_composition_hasDerivAt c00 a η hc00
  have hc1 := tangent_composition_hasDerivAt c01 a η hc01
  have hc2 := tangent_composition_hasDerivAt c11 a η hc11
  have hid := hasDerivAt_id (0 : ℝ)
  have hnum := ((hc0.mul_const (r^2)).fun_add
    ((((hc1.const_mul 2).mul_const r).fun_mul hid))).fun_add
    (hc2.fun_mul (hid.fun_pow 2))
  have hb : HasDerivAt (fun t : ℝ => a-η*t^2) 0 0 := by
    convert (hasDerivAt_const (0 : ℝ) a).fun_sub
      ((hid.fun_pow 2).const_mul η) using 1 <;> norm_num
  have hden := ((hid.fun_pow 2).const_add (r^2)).fun_mul (hb.const_add 1)
  have hne : ((r^2+(0 : ℝ)^2)*(1+(a-η*(0 : ℝ)^2))) ≠ 0 := by
    simpa using mul_ne_zero (pow_ne_zero 2 hr) ha
  have h := ((hk0.mul_const r).fun_add (hk1.fun_mul hid)).fun_sub
    ((hnum.fun_div hden hne).mul_const r)
  convert h using 1
  · rfl
  · simp only [id_eq, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,
      zero_add, add_zero, sub_zero, pow_one, Nat.cast_ofNat, div_one]
    field_simp
    <;> ring

/-- The radial derivative of the opposite coefficient at (r,0). -/
theorem radial_readout_hasDerivAt (k : ℝ → ℝ) (η r : ℝ)
    (hk : DifferentiableAt ℝ k (1-η*r^2)) :
    HasDerivAt (fun t : ℝ => k (1-η*(r+t)^2)*(r+t))
      (k (1-η*r^2) - 2*η*r^2*deriv k (1-η*r^2)) 0 := by
  have hid := (hasDerivAt_id (0 : ℝ)).const_add r
  have hi := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub
    ((hid.fun_pow 2).const_mul η)
  have hc := hk.hasDerivAt.comp_of_eq 0 hi (by norm_num)
  have h := hc.fun_mul hid
  convert h using 1
  · rfl
  · simp only [Function.comp_def, id_eq, add_zero, zero_sub, pow_one,
      Nat.cast_ofNat, Nat.reduceSub, mul_one]
    ring

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.tangent_readout_hasDerivAt
#print axioms NoiseResponse.Classification.radial_readout_hasDerivAt
