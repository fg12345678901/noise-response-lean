/- Added by cx on 2026-10-29: identify the actual two circle points
   and their phases in every natural Fourier mode. -/
module

public import NoiseResponse.SpectralIdentification
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open scoped Topology
namespace NoiseResponse.Classification
variable {T : ℝ} [Fact (0 < T)]

def nyquistPoint (T : ℝ) : AddCircle T := ((T/2 : ℝ) : AddCircle T)

theorem fourier_one_nyquist : fourier 1 (nyquistPoint T) = (-1 : ℂ) := by
  have h := fourier_add_half_inv_index (T := T) (n := 1) (by norm_num)
    (Fact.out : 0 < T) (0 : AddCircle T)
  simpa [nyquistPoint, fourier_eval_zero] using h

theorem fourier_nat_nyquist (n : ℕ) :
    fourier (n : ℤ) (nyquistPoint T) = (-1 : ℂ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, fourier_one_nyquist, pow_succ]

theorem fourier_one_injective : Function.Injective (fun x : AddCircle T => fourier 1 x) := by
  intro x y h
  apply AddCircle.injective_toCircle (ne_of_gt (Fact.out : 0 < T))
  apply Subtype.ext
  simpa only [fourier_one] using h

theorem zero_endpoint_preimage :
    {x : AddCircle T | fourier 1 x = 1} = {0} := by
  ext x
  change fourier 1 x = 1 ↔ x=0
  rw [← fourier_eval_zero (T := T) 1]
  exact fourier_one_injective.eq_iff

theorem nyquist_endpoint_preimage :
    {x : AddCircle T | fourier 1 x = -1} = {nyquistPoint T} := by
  ext x
  change fourier 1 x = -1 ↔ x=nyquistPoint T
  rw [← fourier_one_nyquist (T := T)]
  exact fourier_one_injective.eq_iff

theorem nyquist_ne_zero : nyquistPoint T ≠ (0 : AddCircle T) := by
  intro h
  have he := fourier_one_nyquist (T := T)
  rw [h, fourier_eval_zero] at he
  norm_num at he

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.nyquist_endpoint_preimage
