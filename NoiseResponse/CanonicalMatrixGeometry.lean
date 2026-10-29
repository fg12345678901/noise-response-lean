/- Added by cx on 2026-10-29: canonical real Jacobian projectors and
   their complex matrix realization; smoothness follows from constant rank. -/
module

public import NoiseResponse.ConstantRankProjector
public import NoiseResponse.RankSafeTransfer
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1800
set_option maxHeartbeats 6000000
noncomputable section
open Matrix Filter
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.Geometry
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]

def complexify (A : Matrix m n ℝ) : Matrix m n ℂ := fun i j => (A i j : ℂ)

def complexifyCLM : Matrix m n ℝ →L[ℝ] Matrix m n ℂ :=
  (show Matrix m n ℝ →ₗ[ℝ] Matrix m n ℂ from
    { toFun := complexify
      map_add' := by intro A B; ext i j; exact Complex.ofReal_add _ _
      map_smul' := by intro c A; ext i j; exact Complex.ofReal_mul _ _ }).toContinuousLinearMap

@[simp] theorem complexifyCLM_apply (A : Matrix m n ℝ) : complexifyCLM A=complexify A := rfl

theorem complexify_mul (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    complexify (A*B)=complexify A*complexify B := by
  ext i j
  simp only [complexify,Matrix.mul_apply,Complex.ofReal_sum,Complex.ofReal_mul]

@[simp] theorem complexify_transpose (A : Matrix m n ℝ) : complexify Aᵀ=(complexify A)ᵀ := rfl

@[simp] theorem complexify_adjoint (A : Matrix m n ℝ) : (complexify A)ᴴ=(complexify A)ᵀ := by
  ext i j
  simp [complexify,Matrix.conjTranspose_apply,Matrix.transpose_apply]

theorem complexify_smul (c : ℝ) (A : Matrix m n ℝ) : complexify (c • A)=c • complexify A := by
  exact complexifyCLM.map_smul c A

theorem complexify_one [DecidableEq n] : complexify (1 : Matrix n n ℝ)=1 := by
  ext i j
  by_cases h : i=j <;> simp [complexify,Matrix.one_apply,h]

variable [DecidableEq m] [DecidableEq n]

def normalProjector (A : Matrix m n ℝ) : Matrix n n ℂ :=
  complexify (NoiseResponse.ConstantRank.normalProjector A)

theorem normalProjector_properties (A : Matrix m n ℝ) :
    (normalProjector A)ᵀ=normalProjector A ∧ (normalProjector A)ᴴ=normalProjector A ∧
      normalProjector A*normalProjector A=normalProjector A ∧
      complexify A*normalProjector A=complexify A ∧
      normalProjector A*(complexify A)ᴴ=(complexify A)ᴴ := by
  obtain ⟨ht,hpp,hpa,hap,hr⟩ := NoiseResponse.ConstantRank.normalProjector_properties A
  have ht' : (normalProjector A)ᵀ=normalProjector A := congrArg complexify ht
  refine ⟨ht',?_,?_,?_,?_⟩
  · simpa only [normalProjector,complexify_adjoint] using ht'
  · simpa only [normalProjector,complexify_mul] using congrArg complexify hpp
  · simpa only [normalProjector,complexify_mul] using congrArg complexify hap
  · simpa only [normalProjector,complexify_mul,complexify_transpose,complexify_adjoint] using
      congrArg complexify hpa

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexify_contDiffAt (A : E → Matrix m n ℝ) (x : E)
    (hA : ContDiffAt ℝ 2 A x) : ContDiffAt ℝ 2 (fun y => complexify (A y)) x := by
  simpa only [Function.comp_def,complexifyCLM_apply] using!
    (complexifyCLM (m := m) (n := n)).contDiff.contDiffAt.comp x hA

theorem complexify_fderiv (A : E → Matrix m n ℝ) (x v : E)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => complexify (A y)) x v=complexify (fderiv ℝ A x v) := by
  have hh := (complexifyCLM (m := m) (n := n)).hasFDerivAt.comp x hA.hasFDerivAt
  have he := congrArg (fun L : E →L[ℝ] Matrix m n ℂ => L v) hh.fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,complexifyCLM_apply] using! he

theorem normalProjector_contDiffAt (A : E → Matrix m n ℝ) (x : E)
    (hA : ContDiffAt ℝ 2 A x)
    (hr : ∀ᶠ y in 𝓝 x, (A y)ᵀ.rank=(A x)ᵀ.rank) :
    ContDiffAt ℝ 2 (fun y => normalProjector (A y)) x := by
  exact complexify_contDiffAt _ x (NoiseResponse.ConstantRank.normalProjector_contDiffAt A x hA hr)

end NoiseResponse.Geometry
