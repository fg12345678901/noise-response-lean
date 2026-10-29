/- Added by cx on 2026-10-29: classified original matrix measures
   give genuine local potentials for arbitrary stable constant-rank
   real Jacobian fields, with a canonical constructed normal projector. -/
module

public import NoiseResponse.ClassifiedPotentialCalculus
public import NoiseResponse.AdmissibleFlatGeometry
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2200
set_option maxHeartbeats 9000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator Classical
namespace NoiseResponse.Sufficiency
open NoiseResponse.RankSafe NoiseResponse.IsotropicSpectrum
open NoiseResponse.Classification
variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n] [Nonempty n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAlgebra ℝ (Matrix n n ℂ) where
  norm_smul_le := norm_smul_le
local instance : NormedAlgebra ℝ (Matrix m m ℂ) where
  norm_smul_le := norm_smul_le

theorem frequencyCoefficient_continuous {X : Type*} [TopologicalSpace X]
    (η : ℝ) (A Ai : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hb : ‖normalFilter η A P‖<1) (z : X → ℂ) (hz : Continuous z) (hu : ∀ w, ‖z w‖=1) :
    Continuous (fun w => frequencyCoefficient η A Ai P (z w)) := by
  let B := normalFilter η A P
  have hden : Continuous (fun w => (1 : Matrix n n ℂ)-star (z w) • B) := by fun_prop
  have hr : Continuous (fun w => matrixResolvent B (star (z w))) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    have hunit : IsUnit (1-star (z w) • B) := isUnit_one_sub_of_norm_lt_one
      (by simpa only [norm_smul,norm_star,hu w,one_mul] using hb)
    have hinv : ContinuousAt Ring.inverse (1-star (z w) • B) := by
      simpa only [IsUnit.unit_spec] using!
        (contDiffAt_ringInverse (n := 2) ℝ hunit.unit).continuousAt
    have hh := hinv.comp (f := fun v : X => (1 : Matrix n n ℂ)-star (z v) • B)
      (x := w) (hden.continuousAt (x := w))
    simpa only [IsUnit.unit_spec,matrixResolvent] using! hh
  have hG : Continuous (fun w => transfer η A P (z w)) := by
    unfold transfer
    change Continuous (fun w => η • ((star (z w) • matrixResolvent B (star (z w)))*Aᴴ))
    fun_prop
  unfold frequencyCoefficient NoiseResponse.Curvature.response
  fun_prop

variable {T : ℝ} [Fact (0 < T)]

def measuredFrozenResponse (M : PSDMatrixMeasure (AddCircle T) m) (η : ℝ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) (x v : E) : ℝ :=
  ∫ w, (frequencyCoefficient η (A x) (fderiv ℝ A x v) (P x) (fourier 1 w)*M.density w).trace.re ∂M.traceMeasure

theorem classified_measured_response (M : PSDMatrixMeasure (AddCircle T) m)
    (ν : Measure (AddCircle T)) [IsFiniteMeasure ν] (M0 Mpi : Matrix m m ℂ)
    (hdec : ∀ s : Set (AddCircle T), MeasurableSet s →
      M.value s=(ν.real s : ℂ) • (1 : Matrix m m ℂ)+
        (if (0 : AddCircle T) ∈ s then M0 else 0)+(if nyquistPoint T ∈ s then Mpi else 0))
    (η : ℝ) (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) (x v : E)
    (hb : ‖normalFilter η (A x) (P x)‖<1) :
    measuredFrozenResponse M η A P x v=splitResponse ν (fun w => fourier 1 w) η M0 Mpi A P x v := by
  have hc := frequencyCoefficient_continuous η (A x) (fderiv ℝ A x v) (P x) hb
    (fun w : AddCircle T => fourier 1 w) (fourier 1).continuous (fun w => Circle.norm_coe _)
  have hh := M.classified_continuous_test_integral ν (0 : AddCircle T) (nyquistPoint T) M0 Mpi hdec
    (fun w => frequencyCoefficient η (A x) (fderiv ℝ A x v) (P x) (fourier 1 w)) hc
  simpa only [measuredFrozenResponse,splitResponse,isotropicFrozenResponse,frequencyCoefficient,
    transfer,normalFilter,fourier_eval_zero,fourier_one_nyquist] using! hh

def HasLocalPotential (β : E → E → ℝ) (x : E) : Prop :=
  ∃ V : E → ℝ, ContDiffAt ℝ 2 V x ∧ ∀ᶠ y in 𝓝 x, ∀ v, fderiv ℝ V y v=β y v

def AdmissibleJacobianAt (η : ℝ) (A : E → Matrix m n ℝ) (x : E) : Prop :=
  ContDiffAt ℝ 2 A x ∧ (∀ᶠ y in 𝓝 x, (A y)ᵀ.rank=(A x)ᵀ.rank) ∧
    ‖normalFilter η (NoiseResponse.Geometry.complexify (A x)) (NoiseResponse.Geometry.normalProjector (A x))‖<1

theorem classified_local_potential (M : PSDMatrixMeasure (AddCircle T) m)
    (hclass : M.HasClassifiedSpectrum) (η : ℝ) (hη : 0 < η)
    (A : E → Matrix m n ℝ) (x : E) (hgood : AdmissibleJacobianAt η A x) :
    HasLocalPotential (measuredFrozenResponse M η (fun y => NoiseResponse.Geometry.complexify (A y))
      (fun y => NoiseResponse.Geometry.normalProjector (A y))) x := by
  obtain ⟨ν,M0,Mpi,hfinite,h0,hpi,href,hM0,hMpi,hdec⟩ := hclass
  letI := hfinite
  let Ac : E → Matrix m n ℂ := fun y => NoiseResponse.Geometry.complexify (A y)
  let P : E → Matrix n n ℂ := fun y => NoiseResponse.Geometry.normalProjector (A y)
  let C0 := complexifyMatrix M0
  let Cpi := complexifyMatrix Mpi
  let z : AddCircle T → ℂ := fun w => fourier 1 w
  let U := fullPotential ν z η C0 Cpi Ac P
  obtain ⟨hA,hr,hb⟩ := hgood
  have hAc := NoiseResponse.Geometry.complexify_contDiffAt A x hA
  have hP := NoiseResponse.Geometry.normalProjector_contDiffAt A x hA hr
  have hproj : IsNormalProjectorField Ac P := by
    intro y
    have hp := NoiseResponse.Geometry.normalProjector_properties (A y)
    exact ⟨hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩
  have hu : ∀ w : AddCircle T, ‖z w‖=1 := fun w => Circle.norm_coe _
  have hU := fullPotential_contDiffAt ν z hu η C0 Cpi Ac P x hAc hP hb
  refine ⟨fun y => -U y,hU.neg,?_⟩
  have hgap : ∀ᶠ y in 𝓝 x, ‖normalFilter η (Ac y) (P y)‖<1 :=
    (normalFilter_contDiffAt η Ac P x hAc hP).continuousAt.norm.eventually_lt_const hb
  filter_upwards [hA.eventually (by norm_num),hP.eventually (by norm_num),hgap] with y hyA hyP hyB
  intro v
  have hyAc := NoiseResponse.Geometry.complexify_contDiffAt A y hyA
  have hAt : (Ac y)ᴴ=(Ac y)ᵀ := NoiseResponse.Geometry.complexify_adjoint _
  have hAi : (fderiv ℝ Ac y v)ᴴ=(fderiv ℝ Ac y v)ᵀ := by
    rw [NoiseResponse.Geometry.complexify_fderiv A y v (hyA.differentiableAt (by norm_num))]
    exact NoiseResponse.Geometry.complexify_adjoint _
  have ht : (P y)ᵀ=P y := (NoiseResponse.Geometry.normalProjector_properties (A y)).1
  have hg := fullPotential_gradient_identity ν z (fourier 1).continuous.measurable hu η (ne_of_gt hη)
    C0 Cpi Ac P y v hyAc hyP hproj hAt hAi ht hyB
  have hm := classified_measured_response M ν C0 Cpi hdec η Ac P y v hyB
  change measuredFrozenResponse M η Ac P y v=splitResponse ν z η C0 Cpi Ac P y v at hm
  have hUy := fullPotential_contDiffAt ν z hu η C0 Cpi Ac P y hyAc hyP hyB
  have hn := congrArg (fun L : E →L[ℝ] ℝ => L v)
    ((hUy.differentiableAt (by norm_num)).hasFDerivAt.neg).fderiv
  simp only [ContinuousLinearMap.neg_apply,hg,neg_neg] at hn
  rw [← hm] at hn
  simpa only [Pi.neg_apply,U,Ac,P] using! hn

end NoiseResponse.Sufficiency
