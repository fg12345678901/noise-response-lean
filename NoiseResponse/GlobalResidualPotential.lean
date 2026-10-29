/- Added by cx on 2026-10-29: the potential is a single function of
   the residual Jacobian, shared by all clean charts; its pullback has
   the original measured response as its negative differential. -/
module

public import NoiseResponse.ManuscriptPotentialFormula
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2300
set_option maxHeartbeats 9000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Classical Topology Matrix.Norms.L2Operator
namespace NoiseResponse.ResidualGeometry
open NoiseResponse.Sufficiency NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.IsotropicSpectrum NoiseResponse.Classification
variable {Ω m n : Type*} [MeasurableSpace Ω]
variable [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pointPotential (ν : Measure Ω) (z : Ω → ℂ) (η : ℝ) (M0 Mpi : Matrix m m ℂ)
    (J : Matrix m n ℝ) : ℝ :=
  fullPotential ν z η M0 Mpi (fun _ : ℝ => complexify J) (fun _ : ℝ => normalProjector J) 0

def globalPotential (ν : Measure Ω) (z : Ω → ℂ) (η : ℝ) (M0 Mpi : Matrix m m ℂ)
    (f : (n → ℝ) → (m → ℝ)) (θ : n → ℝ) : ℝ :=
  pointPotential ν z η M0 Mpi (jacobian f id θ)

theorem globalPotential_pullback (ν : Measure Ω) (z : Ω → ℂ) (η : ℝ) (M0 Mpi : Matrix m m ℂ)
    (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) :
    (fun x => globalPotential ν z η M0 Mpi f (ι x))=
      fullPotential ν z η M0 Mpi (fun x => complexify (jacobian f ι x))
        (fun x => normalProjector (jacobian f ι x)) := rfl

variable {T : ℝ} [Fact (0 < T)]

theorem globalPotential_response [Nonempty n]
    (M : PSDMatrixMeasure (AddCircle T) m) (ν : Measure (AddCircle T)) [IsFiniteMeasure ν]
    (M0 Mpi : Matrix m m ℂ)
    (hdec : ∀ s : Set (AddCircle T), MeasurableSet s →
      M.value s=(ν.real s : ℂ) • (1 : Matrix m m ℂ)+
        (if (0 : AddCircle T) ∈ s then M0 else 0)+(if nyquistPoint T ∈ s then Mpi else 0))
    (η : ℝ) (hη : 0 < η) (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) (x : E)
    (hgood : AdmissibleAt η f ι x) :
    ContDiffAt ℝ 2 (fun y => globalPotential ν (fun w => fourier 1 w) η M0 Mpi f (ι y)) x ∧
      ∀ v, fderiv ℝ (fun y => globalPotential ν (fun w => fourier 1 w) η M0 Mpi f (ι y)) x v=
        -response M η f ι x v := by
  rw [globalPotential_pullback]
  let A := jacobian f ι
  let Ac : E → Matrix m n ℂ := fun y => complexify (A y)
  let P : E → Matrix n n ℂ := fun y => normalProjector (A y)
  have hg := admissible_jacobian η f ι x hgood
  have hAc := complexify_contDiffAt A x hg.1
  have hP := normalProjector_contDiffAt A x hg.1 hg.2.1
  have hu : ∀ w : AddCircle T, ‖fourier 1 w‖=1 := fun w => Circle.norm_coe _
  refine ⟨fullPotential_contDiffAt ν _ hu η M0 Mpi Ac P x hAc hP hg.2.2,?_⟩
  intro v
  have hp : IsNormalProjectorField Ac P := by
    intro y
    have hh := normalProjector_properties (A y)
    exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩
  have hAi : (fderiv ℝ Ac x v)ᴴ=(fderiv ℝ Ac x v)ᵀ := by
    rw [complexify_fderiv A x v (hg.1.differentiableAt (by norm_num))]
    exact complexify_adjoint _
  have hd := fullPotential_gradient_identity ν _ (fourier 1).continuous.measurable hu η (ne_of_gt hη)
    M0 Mpi Ac P x v hAc hP hp (complexify_adjoint _) hAi (normalProjector_properties (A x)).1 hg.2.2
  have hm := classified_measured_response M ν M0 Mpi hdec η Ac P x v hg.2.2
  rw [← hm] at hd
  exact hd

end NoiseResponse.ResidualGeometry
