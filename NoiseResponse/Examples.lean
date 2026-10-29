/- Added by cx on 2026-10-29: nonzero matrix-jet and nonvacuity witnesses
   for the proof interfaces; these are exact identities, not numerics. -/
module

public import NoiseResponse.CurvatureAlgebra
public import NoiseResponse.ScalarNecessity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open Matrix
open scoped Matrix
namespace NoiseResponse.Examples

def gi : Matrix (Fin 1) (Fin 2) ℂ := fun _ j => if j = 0 then -Complex.I else 0
def gj : Matrix (Fin 1) (Fin 2) ℂ := fun _ j => if j = 1 then -Complex.I else 0
def ai : Matrix (Fin 2) (Fin 1) ℂ := fun i _ => if i = 0 then 1 else 0
def aj : Matrix (Fin 2) (Fin 1) ℂ := fun i _ => if i = 1 then 1 else 0

theorem nonzero_curvature_entry :
    ((Curvature.variation 1 (0 : Matrix (Fin 1) (Fin 2) ℂ) gi aj 0 0 0 -
      Curvature.variation 1 (0 : Matrix (Fin 1) (Fin 2) ℂ) gj ai 0 0 0) 0 1) = Complex.I := by
  norm_num [Curvature.variation, gi, gj, ai, aj, Matrix.mul_apply,
    Matrix.conjTranspose, Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_succ,
    Matrix.zero_mul, Matrix.mul_zero]
  ring

theorem nonzero_transfer_qualifications :
    (Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ))*gi = aiᴴ ∧
      (Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ))*gj = ajᴴ := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [gi, gj, ai, aj, Matrix.mul_apply, Matrix.conjTranspose,
      Matrix.transpose_apply, Matrix.of_apply,
      Fin.sum_univ_succ]

def zeroPair : Classification.PairCovariances where
  lag00 := fun _ => 0
  lag11 := fun _ => 0
  lagSym := fun _ => 0
  lagSkew := fun _ => 0
  zero00 := 0
  zero11 := 0
  zeroSym := 0
  bound := 0
  bounded00 := by intro n; simp
  bounded11 := by intro n; simp
  boundedSym := by intro n; simp
  boundedSkew := by intro n; simp

theorem zero_pair_potentials (η : ℝ) : zeroPair.AllAxisPotentials η := by
  intro r hr ha p hp
  refine ⟨fun _ => (0 : ℝ), contDiffAt_const, Filter.Eventually.of_forall ?_⟩
  intro q
  simp [Classification.PairCovariances.k00, Classification.PairCovariances.k11,
    Classification.PairCovariances.sym, Classification.PairCovariances.skew,
    Classification.PairCovariances.c00, Classification.PairCovariances.c11,
    Classification.pairAlpha0, Classification.pairAlpha1, Classification.pairPhi,
    Classification.generating, zeroPair]

end NoiseResponse.Examples

#print axioms NoiseResponse.Examples.nonzero_curvature_entry
#print axioms NoiseResponse.Examples.nonzero_transfer_qualifications
#print axioms NoiseResponse.Examples.zero_pair_potentials
