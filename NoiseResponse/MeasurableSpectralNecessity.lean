/- Added by cx on 2026-10-29: upgrade continuous-test classification
   to literal measurable-set masses of the original matrix measure. -/
module

public import NoiseResponse.DiagonalScalarMeasure
public import NoiseResponse.MatrixMeasureReflection
public import NoiseResponse.FlatResponseRealization
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1200
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder Classical
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]
namespace RealMatrixSpectrum
variable (S : RealMatrixSpectrum T m)

def remainderMeasure := S.μ.restrict ({(0 : AddCircle T), nyquistPoint T}ᶜ)
def scalarRemainder (i : m) := diagonalScalarMeasure S.remainderMeasure S.F i

theorem remainder_integrable : Integrable S.F S.remainderMeasure := S.integrable.integrableOn
theorem remainder_positive : ∀ᵐ x ∂S.remainderMeasure, (S.F x).PosSemidef :=
  ae_restrict_of_ae S.positive
instance scalarRemainder_finite (i : m) : IsFiniteMeasure (S.scalarRemainder i) :=
  diagonalScalarMeasure_finite _ _ S.remainder_integrable i

theorem remainder_isotropic (η : ℝ) (hη : 0 < η) (hp : S.AllRankOnePotentials η) (i : m) :
    S.F =ᵐ[S.remainderMeasure] fun x => S.F x i i • (1 : Matrix m m ℂ) := by
  obtain ⟨l, hl⟩ := S.spectral_test_necessity η hη hp
  apply isotropic_density_of_continuous_tests _ _ S.remainder_integrable l _ i
  intro φ
  change (∫ x in {(0 : AddCircle T),nyquistPoint T}ᶜ, φ x • S.F x ∂S.μ)=_
  rw [remove_actual_atoms_test S.μ S.F S.integrable 0 (nyquistPoint T) nyquist_ne_zero.symm]
  have he := congrArg (fun L : C(AddCircle T, ℂ) →L[ℂ] Matrix m m ℂ => L φ) hl
  change (∫ x, φ x • S.F x ∂S.μ)=
    l φ • (1 : Matrix m m ℂ)+φ 0 • S.atom0+φ (nyquistPoint T) • S.atomPi at he
  rw [he]
  change _ - _ • S.atom0 - _ • S.atomPi = _
  abel

theorem scalarRemainder_test_decomposition (η : ℝ) (hη : 0 < η)
    (hp : S.AllRankOnePotentials η) (i : m) (φ : C(AddCircle T, ℂ)) :
    (∫ x, φ x • S.F x ∂S.μ)=(∫ x, φ x ∂S.scalarRemainder i) • (1 : Matrix m m ℂ)+
      φ 0 • S.atom0+φ (nyquistPoint T) • S.atomPi := by
  have hr := diagonalScalarMeasure_test_integral S.remainderMeasure S.F S.remainder_integrable
    S.remainder_positive i (S.remainder_isotropic η hη hp i) φ
  have hs := remove_actual_atoms_test S.μ S.F S.integrable 0 (nyquistPoint T) nyquist_ne_zero.symm φ
  change (∫ x in {(0 : AddCircle T),nyquistPoint T}ᶜ, φ x • S.F x ∂S.μ)=_ at hr
  rw [hr] at hs
  change _ = _ - φ 0 • S.atom0 - φ (nyquistPoint T) • S.atomPi at hs
  unfold scalarRemainder
  rw [hs]
  abel

theorem scalarRemainder_properties (η : ℝ) (hη : 0 < η)
    (hp : S.AllRankOnePotentials η) (i : m) :
    S.scalarRemainder i {(0 : AddCircle T)}=0 ∧ S.scalarRemainder i {nyquistPoint T}=0 ∧
      (S.scalarRemainder i).map (fun x => -x)=S.scalarRemainder i := by
  obtain ⟨ν, hfinite,h0,hpi,href,hν⟩ := S.positive_measure_necessity η hη hp
  letI : IsFiniteMeasure ν := hfinite
  have heq : S.scalarRemainder i=ν := by
    apply finite_measure_eq_of_fourier
    intro n
    have hfirst := S.scalarRemainder_test_decomposition η hη hp i (fourier n)
    have hsecond := hν (fourier n)
    have he := hfirst.symm.trans hsecond
    have hc := add_right_cancel (add_right_cancel he)
    have hd := congrArg (fun A : Matrix m m ℂ => A i i) hc
    simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hd
  simpa only [heq] using And.intro h0 (And.intro hpi href)

theorem split_set_endpoints (s : Set (AddCircle T)) (hs : MeasurableSet s) :
    (∫ x in s, S.F x ∂S.μ)=(∫ x in s, S.F x ∂S.remainderMeasure)+
      (if (0 : AddCircle T) ∈ s then S.atom0 else 0)+
      (if nyquistPoint T ∈ s then S.atomPi else 0) := by
  let e : Set (AddCircle T) := {0,nyquistPoint T}
  have he : MeasurableSet e := by measurability
  have hsplit := integral_add_compl (μ := S.μ.restrict s) he (S.integrable.integrableOn (s := s))
  have htwo : (∫ x in e, S.F x ∂S.μ.restrict s)=
      (∫ x in {0}, S.F x ∂S.μ.restrict s)+(∫ x in {nyquistPoint T}, S.F x ∂S.μ.restrict s) := by
    exact setIntegral_union (by
      apply Set.disjoint_left.mpr
      intro x hx0 hxpi
      apply nyquist_ne_zero (T := T)
      exact (Set.mem_singleton_iff.mp hxpi).symm.trans (Set.mem_singleton_iff.mp hx0))
      (measurableSet_singleton _) S.integrable.integrableOn.integrableOn
      S.integrable.integrableOn.integrableOn
  have hpoint (p : AddCircle T) : (∫ x in {p}, S.F x ∂S.μ.restrict s)=
      if p ∈ s then (∫ x in {p}, S.F x ∂S.μ) else 0 := by
    rw [Measure.restrict_restrict (measurableSet_singleton p)]
    by_cases hp : p ∈ s
    · simp only [hp, if_pos, Set.singleton_inter_of_mem hp]
    · simp only [hp, if_false, Set.singleton_inter_of_notMem hp, Measure.restrict_empty,
        integral_zero_measure]
  have hrest : (∫ x in eᶜ, S.F x ∂S.μ.restrict s)=∫ x in s, S.F x ∂S.remainderMeasure := by
    rw [remainderMeasure, Measure.restrict_restrict he.compl, Measure.restrict_restrict hs,
      Set.inter_comm]
  rw [htwo, hpoint 0, hpoint (nyquistPoint T), hrest] at hsplit
  change (if (0 : AddCircle T) ∈ s then S.atom0 else 0)+
    (if nyquistPoint T ∈ s then S.atomPi else 0)+(∫ x in s, S.F x ∂S.remainderMeasure)=
    (∫ x in s, S.F x ∂S.μ) at hsplit
  rw [← hsplit]
  abel

theorem scalarRemainder_set_decomposition (η : ℝ) (hη : 0 < η)
    (hp : S.AllRankOnePotentials η) (i : m) (s : Set (AddCircle T)) (hs : MeasurableSet s) :
    (∫ x in s, S.F x ∂S.μ)=((S.scalarRemainder i).real s : ℂ) • (1 : Matrix m m ℂ)+
      (if (0 : AddCircle T) ∈ s then S.atom0 else 0)+
      (if nyquistPoint T ∈ s then S.atomPi else 0) := by
  rw [S.split_set_endpoints s hs,
    diagonalScalarMeasure_set_integral S.remainderMeasure S.F S.remainder_integrable
      S.remainder_positive i (S.remainder_isotropic η hη hp i) s hs]
  rfl

end RealMatrixSpectrum

namespace PSDMatrixMeasure
variable (M : PSDMatrixMeasure (AddCircle T) m)

/-- Necessity stated for the original complex-measure matrix and all
    measurable sets; the RN representation is constructed internally. -/
theorem flat_potential_measure_necessity (hr : M.RealReflection) (η : ℝ) (hη : 0 < η)
    (hp : (M.toRealMatrixSpectrum hr).AllFlatLocalPotentials η) :
    ∃ ν : Measure (AddCircle T), IsFiniteMeasure ν ∧ ν {(0 : AddCircle T)}=0 ∧
      ν {nyquistPoint T}=0 ∧ ν.map (fun x => -x)=ν ∧
      ∀ s : Set (AddCircle T), MeasurableSet s →
        M.value s=(ν.real s : ℂ) • (1 : Matrix m m ℂ)+
          (if (0 : AddCircle T) ∈ s then M.value {0} else 0)+
          (if nyquistPoint T ∈ s then M.value {nyquistPoint T} else 0) := by
  let S := M.toRealMatrixSpectrum hr
  let i : m := Classical.arbitrary m
  have hp' := S.all_flat_implies_rank_one η hp
  have hprop := S.scalarRemainder_properties η hη hp' i
  refine ⟨S.scalarRemainder i, inferInstance, hprop.1,hprop.2.1,hprop.2.2,?_⟩
  intro s hs
  have he := S.scalarRemainder_set_decomposition η hη hp' i s hs
  have hat0 : S.atom0=M.value {0} := M.integral_spectrum_represents hr _ (measurableSet_singleton _)
  have hatpi : S.atomPi=M.value {nyquistPoint T} :=
    M.integral_spectrum_represents hr _ (measurableSet_singleton _)
  rw [M.integral_spectrum_represents hr s hs, hat0, hatpi] at he
  exact he

end PSDMatrixMeasure
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.PSDMatrixMeasure.flat_potential_measure_necessity
