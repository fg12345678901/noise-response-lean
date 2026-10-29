/- Added by cx on 2026-10-29: genuine residual derivatives, rank-one
   clean geometry, and the exact raw square-loss updates behind B1. -/
module

public import NoiseResponse.FlatSpectralResponse
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1200
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology Matrix.Norms.Elementwise Classical
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

def flatResidual (A : Plane → m → ℝ) (q : Plane × ℝ) : m → ℝ := q.2 • A q.1

def flatNormalJacobian (A : Plane → m → ℝ) (p : Plane) :
    (Plane × ℝ) →L[ℝ] (m → ℝ) :=
  (ContinuousLinearMap.snd ℝ Plane ℝ).smulRight (A p)

@[simp] theorem flatResidual_clean (A : Plane → m → ℝ) (p : Plane) :
    flatResidual A (p,0)=0 := by simp [flatResidual]

theorem flatResidual_contDiffAt (A : Plane → m → ℝ) (p : Plane) (y : ℝ)
    (hA : ContDiffAt ℝ 3 A p) : ContDiffAt ℝ 3 (flatResidual A) (p,y) := by
  unfold flatResidual
  exact contDiff_snd.contDiffAt.smul (hA.comp (p,y) contDiff_fst.contDiffAt)

theorem flatResidual_derivative (A : Plane → m → ℝ) (p : Plane)
    (hA : DifferentiableAt ℝ A p) :
    HasFDerivAt (flatResidual A) (flatNormalJacobian A p) (p,0) := by
  have hAc := hA.hasFDerivAt.comp (p,0) (ContinuousLinearMap.fst ℝ Plane ℝ).hasFDerivAt
  have hy := (ContinuousLinearMap.snd ℝ Plane ℝ).hasFDerivAt (x := (p,0))
  have he := hy.smul hAc
  change HasFDerivAt (flatResidual A)
    (0 • ((fderiv ℝ A p).comp (ContinuousLinearMap.fst ℝ Plane ℝ))+
      flatNormalJacobian A p) (p,0) at he
  simpa only [zero_smul, zero_add] using he

theorem flatResidual_clean_kernel (A : Plane → m → ℝ) (p : Plane)
    (hA : DifferentiableAt ℝ A p) (hz : A p ≠ 0) (w : Plane × ℝ) :
    fderiv ℝ (flatResidual A) (p,0) w=0 ↔ w.2=0 := by
  rw [(flatResidual_derivative A p hA).fderiv]
  change w.2 • A p=0 ↔ w.2=0
  rw [smul_eq_zero]
  simp only [hz, or_false]

theorem flatResidual_clean_rank (A : Plane → m → ℝ) (p : Plane)
    (hA : DifferentiableAt ℝ A p) (hz : A p ≠ 0) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (flatResidual A) (p,0)).toLinearMap)=1 := by
  rw [(flatResidual_derivative A p hA).fderiv]
  change Module.finrank ℝ (LinearMap.range
    ((ContinuousLinearMap.snd ℝ Plane ℝ).smulRight (A p)).toLinearMap)=1
  rw [ContinuousLinearMap.range_smulRight_apply, finrank_span_singleton hz]
  intro he
  have hh := congrArg (fun L : (Plane × ℝ) →L[ℝ] ℝ => L (0,1)) he
  norm_num at hh

/-- Original noisy square loss, without a preinserted effective response. -/
def flatLoss (A : Plane → m → ℝ) (σ : ℝ) (ζ : m → ℝ) (q : Plane × ℝ) : ℝ :=
  (1/2 : ℝ)*∑ i, (q.2*A q.1 i-σ*ζ i)^2

theorem probe_identity_sum (u v : m → ℝ) :
    probe (1 : Matrix m m ℝ) u v=∑ i, u i*v i := by
  simp [probe, Matrix.toBilin'_apply, Matrix.one_apply]

theorem flatLoss_tangent_derivative (A : Plane → m → ℝ) (σ : ℝ) (ζ : m → ℝ)
    (p v : Plane) (y : ℝ) (hA : DifferentiableAt ℝ A p) :
    HasDerivAt (fun t : ℝ => flatLoss A σ ζ (p+t • v,y))
      (∑ i, (y*A p i-σ*ζ i)*y*(fderiv ℝ A p v i)) 0 := by
  have hline := NoiseResponse.MatrixCalculus.hasDerivAt_line hA v
  have hi (i : m) : HasDerivAt (fun t : ℝ => (y*A (p+t • v) i-σ*ζ i)^2)
      (2*(y*A p i-σ*ζ i)*(y*fderiv ℝ A p v i)) 0 := by
    have he := (ContinuousLinearMap.proj i : (m → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hline
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply, Pi.pow_apply,
      Nat.cast_ofNat, pow_one, Nat.reduceSub, one_smul, zero_smul, add_zero] using
      ((he.const_mul y).sub_const (σ*ζ i)).fun_pow 2
  have hs := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)).const_mul (1/2 : ℝ)
  convert hs using 1
  · funext t
    rfl
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem flatLoss_tangent_formula (A : Plane → m → ℝ) (σ : ℝ) (ζ : m → ℝ)
    (p v : Plane) (y : ℝ) (hA : DifferentiableAt ℝ A p) :
    deriv (fun t : ℝ => flatLoss A σ ζ (p+t • v,y)) 0=
      y^2*probe (1 : Matrix m m ℝ) (fderiv ℝ A p v) (A p)-
        σ*y*probe 1 (fderiv ℝ A p v) ζ := by
  rw [(flatLoss_tangent_derivative A σ ζ p v y hA).deriv]
  simp only [probe_identity_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem flatLoss_normal_derivative (A : Plane → m → ℝ) (σ : ℝ) (ζ : m → ℝ)
    (p : Plane) (y : ℝ) :
    HasDerivAt (fun t : ℝ => flatLoss A σ ζ (p,t))
      (y*probe (1 : Matrix m m ℝ) (A p) (A p)-σ*probe 1 (A p) ζ) y := by
  have hi (i : m) : HasDerivAt (fun t : ℝ => (t*A p i-σ*ζ i)^2)
      (2*(y*A p i-σ*ζ i)*A p i) y := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, pow_one, Nat.reduceSub,
      one_mul] using (((hasDerivAt_id y).mul_const (A p i)).sub_const (σ*ζ i)).fun_pow 2
  have hs := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)).const_mul (1/2 : ℝ)
  convert hs using 1
  · funext t
    rfl
  · simp only [probe_identity_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem exact_flat_normal_recursion (A : Plane → m → ℝ) (σ η u : ℝ) (ζ : m → ℝ)
    (p : Plane) (hσ : σ ≠ 0) :
    (σ*u-η*deriv (fun t : ℝ => flatLoss A σ ζ (p,t)) (σ*u))/σ=
      (1-η*probe (1 : Matrix m m ℝ) (A p) (A p))*u+η*probe 1 (A p) ζ := by
  rw [(flatLoss_normal_derivative A σ ζ p (σ*u)).deriv]
  field_simp
  <;> ring

theorem exact_flat_tangent_slow_update (A : Plane → m → ℝ) (σ η u : ℝ) (ζ : m → ℝ)
    (p v : Plane) (hA : DifferentiableAt ℝ A p) (hσ : σ ≠ 0) (hη : η ≠ 0) :
    (-η*deriv (fun t : ℝ => flatLoss A σ ζ (p+t • v,σ*u)) 0)/(η^2*σ^2)=
      (-probe (1 : Matrix m m ℝ) (fderiv ℝ A p v) (A p)*u^2+
        probe 1 (fderiv ℝ A p v) ζ*u)/η := by
  rw [flatLoss_tangent_formula A σ ζ p v (σ*u) hA]
  field_simp
  <;> ring

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.exact_flat_tangent_slow_update
#print axioms NoiseResponse.Classification.flatResidual_clean_rank
