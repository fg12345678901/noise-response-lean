/- Added by cx on 2026-10-29: a genuine two-dimensional restriction of
   response (B1), with potentials implying the two axis constraints. -/
module

public import NoiseResponse.AxisResponse
public import NoiseResponse.ProbeClosedness
public import NoiseResponse.ClassificationAlgebra
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Topology
namespace NoiseResponse.Classification

def pairA (η : ℝ) (p : Plane) := 1-η*((p 0)^2+(p 1)^2)

def pairPhi (c00 c01 c11 : ℝ → ℝ) (η : ℝ) (p : Plane) :=
  (c00 (pairA η p)*(p 0)^2 + 2*c01 (pairA η p)*(p 0)*(p 1) +
    c11 (pairA η p)*(p 1)^2) /
      (((p 0)^2+(p 1)^2)*(1+pairA η p))

def pairAlpha0 (k00 k01 c00 c01 c11 : ℝ → ℝ) (η : ℝ) (p : Plane) :=
  k00 (pairA η p)*(p 0) + k01 (pairA η p)*(p 1) - pairPhi c00 c01 c11 η p*(p 0)

def pairAlpha1 (k10 k11 c00 c01 c11 : ℝ → ℝ) (η : ℝ) (p : Plane) :=
  k10 (pairA η p)*(p 0) + k11 (pairA η p)*(p 1) - pairPhi c00 c01 c11 η p*(p 1)

theorem pair_axis_x_closedness
    (k00 k01 k10 k11 c00 c01 c11 : ℝ → ℝ) (η r : ℝ)
    (hr : r ≠ 0) (ha : 1+(1-η*r^2) ≠ 0)
    (hk00 : DifferentiableAt ℝ k00 (1-η*r^2))
    (hk01 : DifferentiableAt ℝ k01 (1-η*r^2))
    (hk10 : DifferentiableAt ℝ k10 (1-η*r^2))
    (hc00 : DifferentiableAt ℝ c00 (1-η*r^2))
    (hc01 : DifferentiableAt ℝ c01 (1-η*r^2))
    (hc11 : DifferentiableAt ℝ c11 (1-η*r^2))
    (hp : HasLocalPlanePotential (pairAlpha0 k00 k01 c00 c01 c11 η)
      (pairAlpha1 k10 k11 c00 c01 c11 η) ![r,0]) :
    k10 (1-η*r^2) - k01 (1-η*r^2) -
      2*η*r^2*deriv k10 (1-η*r^2) + 2*c01 (1-η*r^2)/(1+(1-η*r^2)) = 0 := by
  have hc := local_potential_curl_zero _ _ _ hp
  have he₀ : (fun t : ℝ => pairAlpha1 k10 k11 c00 c01 c11 η
      (![r,0]+t • planeAxis 0)) =
      (fun t : ℝ => k10 (1-η*(r+t)^2)*(r+t)) := by
    funext t
    simp [pairAlpha1, pairPhi, pairA, planeAxis]
  have he₁ : (fun t : ℝ => pairAlpha0 k00 k01 c00 c01 c11 η
      (![r,0]+t • planeAxis 1)) = tangentReadout k00 k01 c00 c01 c11 (1-η*r^2) η r := by
    funext t
    have hb : 1-η*(r^2+t^2) = 1-η*r^2-η*t^2 := by ring
    simp [pairAlpha0, pairPhi, pairA, planeAxis, tangentReadout, hb]
  rw [he₀, he₁, (radial_readout_hasDerivAt k10 η r hk10).deriv,
    (tangent_readout_hasDerivAt k00 k01 c00 c01 c11 (1-η*r^2) η r
      hr ha hk00 hk01 hc00 hc01 hc11).deriv] at hc
  linarith

theorem pair_axis_y_closedness
    (k00 k01 k10 k11 c00 c01 c11 : ℝ → ℝ) (η r : ℝ)
    (hr : r ≠ 0) (ha : 1+(1-η*r^2) ≠ 0)
    (hk01 : DifferentiableAt ℝ k01 (1-η*r^2))
    (hk10 : DifferentiableAt ℝ k10 (1-η*r^2))
    (hk11 : DifferentiableAt ℝ k11 (1-η*r^2))
    (hc00 : DifferentiableAt ℝ c00 (1-η*r^2))
    (hc01 : DifferentiableAt ℝ c01 (1-η*r^2))
    (hc11 : DifferentiableAt ℝ c11 (1-η*r^2))
    (hp : HasLocalPlanePotential (pairAlpha0 k00 k01 c00 c01 c11 η)
      (pairAlpha1 k10 k11 c00 c01 c11 η) ![0,r]) :
    k10 (1-η*r^2) - k01 (1-η*r^2) +
      2*η*r^2*deriv k01 (1-η*r^2) - 2*c01 (1-η*r^2)/(1+(1-η*r^2)) = 0 := by
  have hc := local_potential_curl_zero _ _ _ hp
  have he₀ : (fun t : ℝ => pairAlpha1 k10 k11 c00 c01 c11 η
      (![0,r]+t • planeAxis 0)) = tangentReadout k11 k10 c11 c01 c00 (1-η*r^2) η r := by
    funext t
    have hb : 1-η*(t^2+r^2) = 1-η*r^2-η*t^2 := by ring
    simp [pairAlpha1, pairPhi, pairA, planeAxis, tangentReadout, hb]
    ring
  have he₁ : (fun t : ℝ => pairAlpha0 k00 k01 c00 c01 c11 η
      (![0,r]+t • planeAxis 1)) =
      (fun t : ℝ => k01 (1-η*(r+t)^2)*(r+t)) := by
    funext t
    simp [pairAlpha0, pairPhi, pairA, planeAxis]
  rw [he₀, he₁, (radial_readout_hasDerivAt k01 η r hk01).deriv,
    (tangent_readout_hasDerivAt k11 k10 c11 c01 c00 (1-η*r^2) η r
      hr ha hk11 hk10 hc11 hc01 hc00).deriv] at hc
  linarith

/-- Universal local potentials on the two axis charts force the exact
    skew and symmetric off-diagonal ODEs; neither ODE is an input. -/
theorem pair_potentials_force_odes
    (s t k00 k11 c00 c11 : ℝ → ℝ) (g η r : ℝ)
    (hr : r ≠ 0) (ha : 1+(1-η*r^2) ≠ 0)
    (hs : DifferentiableAt ℝ s (1-η*r^2))
    (ht : DifferentiableAt ℝ t (1-η*r^2))
    (hk00 : DifferentiableAt ℝ k00 (1-η*r^2))
    (hk11 : DifferentiableAt ℝ k11 (1-η*r^2))
    (hc00 : DifferentiableAt ℝ c00 (1-η*r^2))
    (hc11 : DifferentiableAt ℝ c11 (1-η*r^2))
    (hp : ∀ p ∈ ({![r,0], ![0,r]} : Set Plane),
      HasLocalPlanePotential
        (pairAlpha0 k00 (fun a => s a+t a) c00 (fun a => g+2*a*s a) c11 η)
        (pairAlpha1 (fun a => s a-t a) k11 c00 (fun a => g+2*a*s a) c11 η) p) :
    (1-(1-η*r^2))*deriv t (1-η*r^2)-t (1-η*r^2) = 0 ∧
      (1-(1-η*r^2)^2)*deriv s (1-η*r^2)-2*(1-η*r^2)*s (1-η*r^2) = g := by
  have hplus : DifferentiableAt ℝ (fun a => s a+t a) (1-η*r^2) := hs.fun_add ht
  have hminus : DifferentiableAt ℝ (fun a => s a-t a) (1-η*r^2) := hs.fun_sub ht
  have hc : DifferentiableAt ℝ (fun a => g+2*a*s a) (1-η*r^2) := by fun_prop
  have hx := pair_axis_x_closedness k00 (fun a => s a+t a) (fun a => s a-t a)
    k11 c00 (fun a => g+2*a*s a) c11 η r hr ha hk00 hplus hminus hc00 hc hc11
    (hp ![r,0] (by simp))
  have hy := pair_axis_y_closedness k00 (fun a => s a+t a) (fun a => s a-t a)
    k11 c00 (fun a => g+2*a*s a) c11 η r hr ha hplus hminus hk11 hc00 hc hc11
    (hp ![0,r] (by simp))
  have hdplus := (hs.hasDerivAt.fun_add ht.hasDerivAt).deriv
  have hdminus := (hs.hasDerivAt.fun_sub ht.hasDerivAt).deriv
  rw [hdminus] at hx
  rw [hdplus] at hy
  apply axis_closedness_implies_ode (1-η*r^2) (s (1-η*r^2)) (t (1-η*r^2))
    (deriv s (1-η*r^2)) (deriv t (1-η*r^2)) g ha
  · convert hx using 1 <;> ring
  · convert hy using 1 <;> ring

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.pair_axis_x_closedness
#print axioms NoiseResponse.Classification.pair_axis_y_closedness
#print axioms NoiseResponse.Classification.pair_potentials_force_odes
