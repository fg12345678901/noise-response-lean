/- Added by cx on 2026-10-29.
   Fourier identification layer. Integration against the spectral measure
   is connected separately; this theorem supplies uniqueness on the circle.
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Submodule

namespace NoiseResponse
namespace Classification

variable {T : ℝ} [Fact (0 < T)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous linear functional on circle test functions is determined
    by all its integer Fourier coefficients. It is valid for vector outputs. -/
theorem continuousLinearMap_zero_of_fourier
    (L : C(AddCircle T, ℂ) →L[ℂ] E)
    (h : ∀ k : ℤ, L (fourier k) = 0) :
    L = 0 := by
  have hspan : Submodule.span ℂ (Set.range (@fourier T)) ≤ L.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    simpa using h k
  have hclosure :
      (Submodule.span ℂ (Set.range (@fourier T))).topologicalClosure ≤ L.ker :=
    Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  rw [span_fourier_closure_eq_top] at hclosure
  ext f
  have hf : f ∈ L.ker := hclosure (by trivial)
  simpa using hf

theorem continuousLinearMap_eq_of_fourier
    (L₁ L₂ : C(AddCircle T, ℂ) →L[ℂ] E)
    (h : ∀ k : ℤ, L₁ (fourier k) = L₂ (fourier k)) :
    L₁ = L₂ := by
  have hzero : L₁ - L₂ = 0 :=
    continuousLinearMap_zero_of_fourier (L₁ - L₂) (by
      intro k
      simpa using sub_eq_zero.mpr (h k))
  exact sub_eq_zero.mp hzero

end Classification
end NoiseResponse

#print axioms NoiseResponse.Classification.continuousLinearMap_zero_of_fourier
#print axioms NoiseResponse.Classification.continuousLinearMap_eq_of_fourier
