/- Added by cx on 2026-10-29: assemble genuine two-parameter potential
   tests into the arbitrary-dimensional covariance classification.
   The covariance-pair representation and its spectral endpoint
   compatibility are explicit interfaces, not new axioms. -/
module

public import NoiseResponse.ScalarNecessity
public import NoiseResponse.EndpointPaths
public import NoiseResponse.OrthonormalProbes
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open Filter Set Matrix
open scoped Topology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

def symmetricProbe (M : Matrix m m ℝ) (u v : m → ℝ) :=
  (probe M u v+probe M v u)/2

theorem symmetricProbe_eq (M : Matrix m m ℝ) (hM : Mᵀ = M) (u v : m → ℝ) :
    symmetricProbe M u v = probe M u v := by
  unfold symmetricProbe
  rw [← probe_symmetric M hM u v]
  ring

/-- Conditional on the explicit covariance/spectral representation,
    universal rank-one local potentials identify every lag matrix.
    The scalar part may depend on the lag. Both endpoint matrices remain. -/
theorem rankone_potential_covariance_necessity
    (Γ : ℕ → Matrix m m ℝ) (Γ0 M0 Mpi : Matrix m m ℝ)
    (hΓ0 : Γ0ᵀ = Γ0) (hM0 : M0ᵀ = M0) (hMpi : Mpiᵀ = Mpi)
    (P : (m → ℝ) → (m → ℝ) → PairCovariances)
    (hSym : ∀ u v n, (P u v).lagSym n = symmetricProbe (Γ n) u v)
    (hSkew : ∀ u v n, (P u v).lagSkew n = (probe (Γ n) u v-probe (Γ n) v u)/2)
    (hZero : ∀ u v, (P u v).zeroSym = symmetricProbe Γ0 u v)
    (η : ℝ) (hη : 0 < η)
    (hp : ∀ u v, OrthonormalProbePair u v → (P u v).AllAxisPotentials η)
    (hEndpoint : ∀ u v, OrthonormalProbePair u v →
      Tendsto (fun k => (1-positiveEndpointPath k)*(P u v).skew (positiveEndpointPath k))
        atTop (𝓝 0) ∧
      Tendsto (fun k => (1-positiveEndpointPath k)*(P u v).sym (positiveEndpointPath k))
        atTop (𝓝 (symmetricProbe M0 u v)) ∧
      Tendsto (fun k => (1+negativeEndpointPath k)*(P u v).sym (negativeEndpointPath k))
        atTop (𝓝 (-symmetricProbe Mpi u v))) :
    (∃ c0 : ℝ, Γ0 = M0+Mpi+c0 • (1 : Matrix m m ℝ)) ∧
      ∀ n, ∃ cn : ℝ, Γ n = M0-((-1 : ℝ)^n) • Mpi+cn • (1 : Matrix m m ℝ) := by
  have hn (u v : m → ℝ) (huv : OrthonormalProbePair u v) :=
    (P u v).necessary_lags η hη (hp u v huv)
      positiveEndpointPath negativeEndpointPath positiveEndpointPath_mem negativeEndpointPath_mem
      positiveEndpointPath_tendsto negativeEndpointPath_tendsto (hEndpoint u v huv).1
      (symmetricProbe M0 u v) (symmetricProbe Mpi u v)
      (hEndpoint u v huv).2.1 (hEndpoint u v huv).2.2
  constructor
  · obtain ⟨c0, hc0⟩ := scalar_of_orthonormal_probes (Γ0-M0-Mpi) (by
      intro u v huv
      have hz := (hn u v huv).2.1
      rw [hZero, symmetricProbe_eq Γ0 hΓ0, symmetricProbe_eq M0 hM0,
        symmetricProbe_eq Mpi hMpi] at hz
      simp only [probe_matrix_sub]
      linarith)
    refine ⟨c0, ?_⟩
    rw [← hc0]
    abel
  · intro n
    obtain ⟨cn, hcn⟩ := scalar_of_orthonormal_probes (Γ n-M0+((-1 : ℝ)^n) • Mpi) (by
      intro u v huv
      have hs := (hn u v huv).2.2 n
      have ht := (hn u v huv).1 n
      rw [hSym, symmetricProbe_eq M0 hM0, symmetricProbe_eq Mpi hMpi] at hs
      rw [hSkew] at ht
      unfold symmetricProbe at hs
      simp only [probe_matrix_add, probe_matrix_sub, probe_matrix_smul]
      nlinarith [hs, ht])
    refine ⟨cn, ?_⟩
    rw [← hcn]
    abel

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.rankone_potential_covariance_necessity
