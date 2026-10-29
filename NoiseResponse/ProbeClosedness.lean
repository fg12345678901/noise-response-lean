/- Added by cx on 2026-10-29: the local-potential to closedness interface
   for genuine two-parameter probes, rather than an assumed curl equation. -/
module

public import NoiseResponse.CurvatureCalculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace NoiseResponse.Classification

abbrev Plane := Fin 2 → ℝ

def planeAxis (i : Fin 2) : Plane := Pi.single i 1

def HasLocalPlanePotential (α₀ α₁ : Plane → ℝ) (p : Plane) : Prop :=
  ∃ V : Plane → ℝ, ContDiffAt ℝ 2 V p ∧
    ∀ᶠ q in 𝓝 p, fderiv ℝ V q (planeAxis 0) = α₀ q ∧
      fderiv ℝ V q (planeAxis 1) = α₁ q

/-- A local potential on the two-parameter chart forces the actual
    antisymmetric derivative to vanish at its base point. -/
theorem local_potential_curl_zero (α₀ α₁ : Plane → ℝ) (p : Plane)
    (h : HasLocalPlanePotential α₀ α₁ p) :
    deriv (fun t : ℝ => α₁ (p+t • planeAxis 0)) 0 =
      deriv (fun t : ℝ => α₀ (p+t • planeAxis 1)) 0 := by
  rcases h with ⟨V, hV, hv⟩
  have he (i j : Fin 2) (α : Plane → ℝ)
      (ha : ∀ᶠ q in 𝓝 p, fderiv ℝ V q (planeAxis j) = α q) :
      deriv (fun t : ℝ => α (p+t • planeAxis i)) 0 =
        fderiv ℝ (fderiv ℝ V) p (planeAxis i) (planeAxis j) := by
    have ht : Tendsto (fun t : ℝ => p+t • planeAxis i) (𝓝 0) (𝓝 p) := by
      have hc : Continuous (fun t : ℝ => p+t • planeAxis i) := by fun_prop
      simpa only [zero_smul, add_zero] using hc.tendsto 0
    have hline := Curvature.fderiv_line_hasDerivAt hV (planeAxis i) (planeAxis j)
    have hh : (fun t : ℝ => fderiv ℝ V (p+t • planeAxis i) (planeAxis j))
        =ᶠ[𝓝 0] (fun t : ℝ => α (p+t • planeAxis i)) := ht ha
    exact (hline.congr_of_eventuallyEq hh.symm).deriv
  rw [he 0 1 α₁ (hv.mono (fun _ hq => hq.2)), he 1 0 α₀ (hv.mono (fun _ hq => hq.1))]
  exact hV.isSymmSndFDerivAt (by simp) _ _

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.local_potential_curl_zero
