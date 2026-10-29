/- Added by cx on 2026-10-29: actual residual functions and clean
   immersion charts. The C2 Jacobian field is derived from C3 regularity;
   constant rank is imposed only along the clean chart. -/
module

public import NoiseResponse.JacobianClassificationEquivalence
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2200
set_option maxHeartbeats 9000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.ResidualGeometry
open NoiseResponse.Sufficiency NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.Classification
variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def jacobianCLM : ((n → ℝ) →L[ℝ] (m → ℝ)) →L[ℝ] Matrix m n ℝ :=
  (show ((n → ℝ) →L[ℝ] (m → ℝ)) →ₗ[ℝ] Matrix m n ℝ from
    { toFun := fun L => LinearMap.toMatrix' L.toLinearMap
      map_add' := by intro L K; ext i j; rfl
      map_smul' := by intro c L; ext i j; rfl }).toContinuousLinearMap

@[simp] theorem jacobianCLM_apply (L : (n → ℝ) →L[ℝ] (m → ℝ)) :
    jacobianCLM L=LinearMap.toMatrix' L.toLinearMap := rfl

def jacobian (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) (x : E) : Matrix m n ℝ :=
  LinearMap.toMatrix' (fderiv ℝ f (ι x)).toLinearMap

theorem jacobian_contDiffAt (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) (x : E)
    (hf : ContDiffAt ℝ 3 f (ι x)) (hι : ContDiffAt ℝ 3 ι x) :
    ContDiffAt ℝ 2 (jacobian f ι) x := by
  have hd := (hf.fderiv_right (m := 2) (by norm_num)).comp x (hι.of_le (by norm_num))
  simpa only [Function.comp_def,jacobianCLM_apply,jacobian] using!
    (jacobianCLM (m := m) (n := n)).contDiff.contDiffAt.comp x hd

def AdmissibleAt (η : ℝ) (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) (x : E) : Prop :=
  ContDiffAt ℝ 3 ι x ∧
    (∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 f (ι y) ∧ f (ι y)=0 ∧
      Function.Injective (fderiv ℝ ι y) ∧
      LinearMap.range (fderiv ℝ ι y).toLinearMap=LinearMap.ker (fderiv ℝ f (ι y)).toLinearMap) ∧
    (∀ᶠ y in 𝓝 x, (jacobian f ι y)ᵀ.rank=(jacobian f ι x)ᵀ.rank) ∧
    ‖normalFilter η (complexify (jacobian f ι x)) (normalProjector (jacobian f ι x))‖<1

theorem admissible_jacobian (η : ℝ) (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) (x : E)
    (h : AdmissibleAt η f ι x) : AdmissibleJacobianAt η (jacobian f ι) x :=
  ⟨jacobian_contDiffAt f ι x h.2.1.self_of_nhds.1 h.1,h.2.2.1,h.2.2.2⟩

variable {T : ℝ} [Fact (0 < T)]

def response (M : PSDMatrixMeasure (AddCircle T) m) (η : ℝ)
    (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) : E → E → ℝ :=
  measuredFrozenResponse M η (fun y => complexify (jacobian f ι y))
    (fun y => normalProjector (jacobian f ι y))

theorem classified_residual_local_potential [Nonempty n]
    (M : PSDMatrixMeasure (AddCircle T) m) (hclass : M.HasClassifiedSpectrum)
    (η : ℝ) (hη : 0 < η) (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) (x : E)
    (h : AdmissibleAt η f ι x) : HasLocalPotential (response M η f ι) x :=
  classified_local_potential M hclass η hη (jacobian f ι) x (admissible_jacobian η f ι x h)

theorem empty_parameters_response [IsEmpty n]
    (M : PSDMatrixMeasure (AddCircle T) m) (η : ℝ)
    (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) (x v : E) : response M η f ι x v=0 := by
  have hzG (z : ℂ) : transfer η (complexify (jacobian f ι x)) (normalProjector (jacobian f ι x)) z=0 :=
    Subsingleton.elim _ _
  have hzA : fderiv ℝ (fun y => complexify (jacobian f ι y)) x v=0 := by
    ext i j
    exact isEmptyElim j
  simp only [response,measuredFrozenResponse,frequencyCoefficient,hzG,hzA,
    NoiseResponse.Curvature.response,Matrix.conjTranspose_zero,Matrix.zero_mul,Matrix.mul_zero,
    zero_add,add_zero,sub_zero,smul_zero,Matrix.trace_zero,Complex.zero_re,integral_zero]

theorem classified_residual_local_potential_all_dimensions
    (M : PSDMatrixMeasure (AddCircle T) m) (hclass : M.HasClassifiedSpectrum)
    (η : ℝ) (hη : 0 < η) (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) (x : E)
    (h : AdmissibleAt η f ι x) : HasLocalPotential (response M η f ι) x := by
  cases isEmpty_or_nonempty n with
  | inl hempty =>
      letI := hempty
      refine ⟨fun _ => 0,contDiffAt_const,Eventually.of_forall (fun y v => ?_)⟩
      rw [empty_parameters_response M η f ι y v]
      simpa only [ContinuousLinearMap.zero_apply] using
        congrArg (fun L : E →L[ℝ] ℝ => L v) (hasFDerivAt_const (0 : ℝ) y).fderiv
  | inr hnonempty =>
      letI := hnonempty
      exact classified_residual_local_potential M hclass η hη f ι x h

def AllResidualPotentials (M : PSDMatrixMeasure (AddCircle T) m) (η : ℝ) : Prop :=
  ∀ (d N : ℕ) (f : (Fin N → ℝ) → (m → ℝ)) (ι : (Fin d → ℝ) → (Fin N → ℝ))
    (x : Fin d → ℝ), AdmissibleAt η f ι x → HasLocalPotential (response M η f ι) x

theorem classified_implies_all_residuals (M : PSDMatrixMeasure (AddCircle T) m)
    (hclass : M.HasClassifiedSpectrum) (η : ℝ) (hη : 0 < η) : AllResidualPotentials M η := by
  intro d N f ι x h
  exact classified_residual_local_potential_all_dimensions M hclass η hη f ι x h

end NoiseResponse.ResidualGeometry
