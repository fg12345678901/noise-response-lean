/- Added by cx on 2026-10-29: realize the rank-one probe as an actual
   smooth residual with two tangent parameters and one normal parameter. -/
module

public import NoiseResponse.SpectralNecessity
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 3000000
noncomputable section
open Filter Set Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

def probeEmbedding (u v : m → ℝ) (p : Plane) : m → ℝ := p 0 • u+p 1 • v

def probeEmbeddingCLM (u v : m → ℝ) : Plane →L[ℝ] (m → ℝ) :=
  (show Plane →ₗ[ℝ] (m → ℝ) from
    { toFun := probeEmbedding u v
      map_add' := by intro p q; unfold probeEmbedding; simp only [Pi.add_apply, add_smul]; module
      map_smul' := by
        intro c p
        funext i
        change (c*p 0)*u i+(c*p 1)*v i = c*(p 0*u i+p 1*v i)
        ring }).toContinuousLinearMap

@[simp] theorem probeEmbeddingCLM_apply (u v : m → ℝ) (p : Plane) :
    probeEmbeddingCLM u v p=probeEmbedding u v p := rfl

theorem probeEmbedding_smooth (u v : m → ℝ) : ContDiff ℝ ⊤ (probeEmbedding u v) := by
  exact (probeEmbeddingCLM u v).contDiff

theorem probeEmbedding_length (u v : m → ℝ) (huv : OrthonormalProbePair u v) (p : Plane) :
    probe (1 : Matrix m m ℝ) (probeEmbedding u v p) (probeEmbedding u v p)=
      (p 0)^2+(p 1)^2 := by
  have hvu : probe (1 : Matrix m m ℝ) v u=0 := by
    rw [← probe_transpose, Matrix.transpose_one]
    exact huv.2.2
  unfold probeEmbedding
  simp only [probe_add_left, probe_add_right, probe_smul_left, probe_smul_right,
    huv.1, huv.2.1, huv.2.2, hvu]
  ring

theorem probeEmbedding_axis_nonzero (u v : m → ℝ) (huv : OrthonormalProbePair u v)
    (r : ℝ) (hr : r ≠ 0) (p : Plane) (hp : p ∈ ({![r,0], ![0,r]} : Set Plane)) :
    probeEmbedding u v p ≠ 0 := by
  intro hz
  have he := probeEmbedding_length u v huv p
  rw [hz] at he
  have hs : (p 0)^2+(p 1)^2=r^2 := by
    rcases hp with hp | hp
    · rw [hp]; simp
    · rw [Set.mem_singleton_iff.mp hp]; simp
  rw [hs] at he
  have hzero : probe (1 : Matrix m m ℝ) 0 0=0 := by
    exact map_zero (Matrix.toBilin' (1 : Matrix m m ℝ) 0)
  rw [hzero] at he
  exact hr (sq_eq_zero_iff.mp he.symm)

def probeResidual (u v : m → ℝ) (q : Plane × ℝ) : m → ℝ :=
  q.2 • probeEmbedding u v q.1

def probeNormalJacobian (u v : m → ℝ) (p : Plane) : (Plane × ℝ) →L[ℝ] (m → ℝ) :=
  (ContinuousLinearMap.snd ℝ Plane ℝ).smulRight (probeEmbedding u v p)

theorem probeResidual_smooth (u v : m → ℝ) : ContDiff ℝ ⊤ (probeResidual u v) := by
  unfold probeResidual
  exact contDiff_snd.smul ((probeEmbedding_smooth u v).comp contDiff_fst)

@[simp] theorem probeResidual_clean (u v : m → ℝ) (p : Plane) :
    probeResidual u v (p,0)=0 := by simp [probeResidual]

theorem probeResidual_derivative (u v : m → ℝ) (p : Plane) :
    HasFDerivAt (probeResidual u v) (probeNormalJacobian u v p) (p,0) := by
  have hA := ((probeEmbeddingCLM u v).comp (ContinuousLinearMap.fst ℝ Plane ℝ)).hasFDerivAt
    (x := (p,0))
  have hy := (ContinuousLinearMap.snd ℝ Plane ℝ).hasFDerivAt (x := (p,0))
  have h := hy.smul hA
  change HasFDerivAt (probeResidual u v)
    (0 • ((probeEmbeddingCLM u v).comp (ContinuousLinearMap.fst ℝ Plane ℝ))+
      probeNormalJacobian u v p) (p,0) at h
  simpa only [zero_smul, zero_add] using h

theorem probeResidual_clean_kernel (u v : m → ℝ) (p : Plane)
    (hz : probeEmbedding u v p ≠ 0) (w : Plane × ℝ) :
    fderiv ℝ (probeResidual u v) (p,0) w=0 ↔ w.2=0 := by
  rw [(probeResidual_derivative u v p).fderiv]
  change w.2 • probeEmbedding u v p=0 ↔ w.2=0
  rw [smul_eq_zero]
  simp only [hz, or_false]

def probeContraction (η : ℝ) (u v : m → ℝ) (p : Plane) : ℝ :=
  1-η*probe (1 : Matrix m m ℝ) (probeEmbedding u v p) (probeEmbedding u v p)

theorem probeContraction_formula (η : ℝ) (u v : m → ℝ)
    (huv : OrthonormalProbePair u v) (p : Plane) :
    probeContraction η u v p=pairA η p := by
  rw [probeContraction, probeEmbedding_length u v huv]
  rfl

/-- The radius tests have an actual open neighborhood with a uniform
    normal contraction margin, not just pointwise stability. -/
theorem probe_uniform_stable_chart (η : ℝ) (u v : m → ℝ)
    (huv : OrthonormalProbePair u v) (r : ℝ) (hr : r ≠ 0)
    (ha : (1-η*r^2) ∈ Ioo (-1 : ℝ) 1)
    (p : Plane) (hp : p ∈ ({![r,0], ![0,r]} : Set Plane)) :
    ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ ∃ q : ℝ, 0 ≤ q ∧ q<1 ∧
      ∀ x ∈ U, probeEmbedding u v x ≠ 0 ∧ |probeContraction η u v x| ≤ q := by
  have hlen : (p 0)^2+(p 1)^2=r^2 := by
    rcases hp with hp | hp
    · rw [hp]; simp
    · rw [Set.mem_singleton_iff.mp hp]; simp
  have hstable : |probeContraction η u v p|<1 := by
    rw [probeContraction_formula η u v huv, pairA, hlen]
    exact abs_lt.mpr ha
  let q := (|probeContraction η u v p|+1)/2
  have hq0 : 0 ≤ q := by unfold q; positivity
  have hq1 : q<1 := by unfold q; linarith
  have hpq : |probeContraction η u v p|<q := by unfold q; linarith
  let U : Set Plane := {x | probeEmbedding u v x ≠ 0} ∩ {x | |probeContraction η u v x|<q}
  refine ⟨U, ?_, ?_, q, hq0, hq1, ?_⟩
  · apply IsOpen.inter
    · exact isClosed_singleton.isOpen_compl.preimage (probeEmbedding_smooth u v).continuous
    · apply isOpen_lt _ continuous_const
      rw [show (fun x => |probeContraction η u v x|) = (fun x => |pairA η x|) by
        funext x; rw [probeContraction_formula η u v huv]]
      unfold pairA
      fun_prop
  · exact ⟨probeEmbedding_axis_nonzero u v huv r hr p hp, hpq⟩
  · intro x hx
    exact ⟨hx.1, hx.2.le⟩

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.probeResidual_clean_kernel
#print axioms NoiseResponse.Classification.probe_uniform_stable_chart
