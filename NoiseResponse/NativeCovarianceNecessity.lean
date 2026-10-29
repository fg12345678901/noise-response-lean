/- Added by cx on 2026-10-29: instantiate the covariance-pair and
   endpoint compatibility automatically from a real matrix generator. -/
module

public import NoiseResponse.PairRepresentation
public import NoiseResponse.MatrixNecessity
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open Filter Set Matrix
open scoped Topology Matrix.Norms.Elementwise
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

theorem matrix_generating_necessity
    (Γ : ℕ → Matrix m m ℝ) (Γ0 M0 Mpi : Matrix m m ℝ)
    (hΓ0 : Γ0ᵀ = Γ0) (hM0 : M0ᵀ = M0) (hMpi : Mpiᵀ = Mpi)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ n, ‖Γ n‖ ≤ B)
    (η : ℝ) (hη : 0 < η)
    (hp : ∀ u v, OrthonormalProbePair u v →
      (covariancePair Γ Γ0 B hB0 hB u v).AllAxisPotentials η)
    (hplus : Tendsto (fun k => (1-positiveEndpointPath k) • generating Γ (positiveEndpointPath k))
      atTop (𝓝 M0))
    (hminus : Tendsto (fun k => (1+negativeEndpointPath k) • generating Γ (negativeEndpointPath k))
      atTop (𝓝 (-Mpi))) :
    (∃ c0 : ℝ, Γ0 = M0+Mpi+c0 • (1 : Matrix m m ℝ)) ∧
      ∀ n, ∃ cn : ℝ, Γ n = M0-((-1 : ℝ)^n) • Mpi+cn • (1 : Matrix m m ℝ) := by
  have hnorm (a : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) : ‖a‖ < 1 := by
    simpa only [Real.norm_eq_abs] using abs_lt.mpr ha
  apply rankone_potential_covariance_necessity Γ Γ0 M0 Mpi hΓ0 hM0 hMpi
    (covariancePair Γ Γ0 B hB0 hB)
    (by intro u v n; exact covariancePair_sym _ _ _ _ _ _ _ _)
    (by intro u v n; exact covariancePair_skew _ _ _ _ _ _ _ _)
    (by intro u v; exact covariancePair_zero _ _ _ _ _ _ _) η hη hp
  intro u v huv
  have ht := generating_endpoint_map Γ B hB (skewProbeCLM u v)
    positiveEndpointPath (fun k => hnorm _ (positiveEndpointPath_mem k))
    (fun k => 1-positiveEndpointPath k) M0 hplus
  have hs := generating_endpoint_map Γ B hB (symmetricProbeCLM u v)
    positiveEndpointPath (fun k => hnorm _ (positiveEndpointPath_mem k))
    (fun k => 1-positiveEndpointPath k) M0 hplus
  have hm := generating_endpoint_map Γ B hB (symmetricProbeCLM u v)
    negativeEndpointPath (fun k => hnorm _ (negativeEndpointPath_mem k))
    (fun k => 1+negativeEndpointPath k) (-Mpi) hminus
  constructor
  · have hz : skewProbeCLM u v M0 = 0 := by
      rw [skewProbeCLM_apply, probe_symmetric M0 hM0 u v]
      simp
    simpa only [covariancePair, PairCovariances.fromLinearProbes, PairCovariances.skew,
      smul_eq_mul, hz] using ht
  · constructor
    · simpa only [covariancePair, PairCovariances.fromLinearProbes, PairCovariances.sym,
        symmetricProbeCLM_apply, symmetricProbe, smul_eq_mul] using hs
    · simpa only [covariancePair, PairCovariances.fromLinearProbes, PairCovariances.sym,
        map_neg, symmetricProbeCLM_apply, symmetricProbe, smul_eq_mul] using hm

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.matrix_generating_necessity
