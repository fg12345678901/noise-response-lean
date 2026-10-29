/- Added by cx on 2026-10-29: genuine real derivatives for rectangular
   complex matrices. These lemmas connect the jet algebra to calculus. -/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise

-- HasDerivAt accepts arbitrary topologies; force the topology carried by
-- the normed-space instance also used by HasFDerivAt.
local instance matrixNormTopology (i j α : Type*) [Fintype i] [Fintype j]
    [NormedAddCommGroup α] : TopologicalSpace (Matrix i j α) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (inferInstance : PseudoMetricSpace (Matrix i j α)))

namespace NoiseResponse
namespace MatrixCalculus

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

def mulCLM : Matrix l m ℂ →L[ℝ] Matrix m n ℂ →L[ℝ] Matrix l n ℂ :=
  ((LinearMap.toContinuousLinearMap :
      (Matrix m n ℂ →ₗ[ℝ] Matrix l n ℂ) ≃ₗ[ℝ]
        (Matrix m n ℂ →L[ℝ] Matrix l n ℂ)).toLinearMap.comp
      (mulLinearMap ℝ)).toContinuousLinearMap

@[simp] theorem mulCLM_apply (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    mulCLM A B = A * B := rfl

def adjCLM : Matrix m n ℂ →L[ℝ] Matrix n m ℂ :=
  (show Matrix m n ℂ →ₗ[ℝ] Matrix n m ℂ from
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := by intro c A; simp }).toContinuousLinearMap

@[simp] theorem adjCLM_apply (A : Matrix m n ℂ) : adjCLM A = Aᴴ := rfl

theorem hasDerivAt_mul {A : ℝ → Matrix l m ℂ} {B : ℝ → Matrix m n ℂ}
    {Ai : Matrix l m ℂ} {Bi : Matrix m n ℂ} {x : ℝ}
    (hA : HasDerivAt A Ai x) (hB : HasDerivAt B Bi x) :
    HasDerivAt (fun t => A t * B t) (Ai * B x + A x * Bi) x := by
  have h := (mulCLM (l := l) (m := m) (n := n)).hasFDerivAt_of_bilinear
    hA.hasFDerivAt hB.hasFDerivAt
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    one_smul, mulCLM_apply, add_comm] using h.hasDerivAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_mul_apply {A : E → Matrix l m ℂ} {B : E → Matrix m n ℂ}
    {x : E} (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (v : E) :
    fderiv ℝ (fun y => A y * B y) x v =
      fderiv ℝ A x v * B x + A x * fderiv ℝ B x v := by
  have h := (mulCLM (l := l) (m := m) (n := n)).hasFDerivAt_of_bilinear
    hA.hasFDerivAt hB.hasFDerivAt
  have he := congrArg (fun L : E →L[ℝ] Matrix l n ℂ => L v) h.fderiv
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, mulCLM_apply, add_comm] using he

theorem hasDerivAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)

theorem hasDerivAt_adj {A : ℝ → Matrix m n ℂ}
    {Ai : Matrix m n ℂ} {x : ℝ} (hA : HasDerivAt A Ai x) :
    HasDerivAt (fun t => (A t)ᴴ) Aiᴴ x := by
  exact adjCLM.hasFDerivAt.comp_hasDerivAt x hA

end MatrixCalculus
end NoiseResponse

#print axioms NoiseResponse.MatrixCalculus.hasDerivAt_mul
#print axioms NoiseResponse.MatrixCalculus.hasDerivAt_adj
