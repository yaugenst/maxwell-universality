import Maxwell.Spectral.GlobalCubic.Quasiperiodic
import Maxwell.Spectral.SectorSimplicity

namespace Maxwell.Spectral.GlobalCubic
open PeriodicYee
open PrimitiveYee (Electric RawCell rawUnit representative character)
open Maxwell.Certificate.FourierBinding (boundaryMomentum)
open scoped Matrix
set_option maxHeartbeats 1500000
noncomputable section

def direction (g : Generator) (j : Direction) : Direction := match g with
  | .swap01 => ![1,0,2] j
  | .swap12 => ![0,2,1] j
  | .reflect0 => j

def edgePoint (g : Generator) (a : ℤ) (e : Electric) : RawCell :=
  node g a (representative e.2) - if g = .reflect0 ∧ e.1 = 0 then rawUnit 0 else 0

def edgeSign (g : Generator) (j : Direction) : ℂ := if g = .reflect0 ∧ j = 0 then -1 else 1

def sourceIndex (g : Generator) (a : ℤ) (e : Electric) : Electric :=
  (direction g e.1, PrimitiveYee.reduceCell (edgePoint g a e))

def weight (g : Generator) (a : ℤ) (c : Momentum) (e : Electric) : ℂ :=
  edgeSign g e.1 * character (boundaryMomentum c) (PrimitiveYee.reduceTranslation (edgePoint g a e))

theorem transform_apply (g : Generator) (a : ℤ) (c : Momentum) (v : Electric → ℂ) (e : Electric) :
    transform g a c v e = weight g a c e*v (sourceIndex g a e) := by
  obtain ⟨j,p⟩ := e
  cases g <;> fin_cases j <;>
    simp [transform, restrict, edgeAction, extendField, PrimitiveYee.extend,
      weight, sourceIndex, direction, edgePoint, edgeSign]

theorem transform_zero (g : Generator) (a : ℤ) (c : Momentum) : transform g a c 0 = 0 := by
  funext e
  rw [transform_apply]
  simp

theorem sourceIndex_surjective (g : Generator) (a : ℤ) : Function.Surjective (sourceIndex g a) := by
  intro e
  by_contra he
  push Not at he
  have hz : transform g a 0 (Pi.single e 1) = 0 := by
    funext f
    rw [transform_apply]
    simp [he f]
  have h := congrArg (transform g (-a) (momentum g 0)) hz
  rw [transform_inverse, transform_zero] at h
  have hh := congrFun h e
  simp at hh

theorem sourceIndex_injective (g : Generator) (a : ℤ) : Function.Injective (sourceIndex g a) :=
  (Finite.injective_iff_surjective).mpr (sourceIndex_surjective g a)

theorem weight_unit (g : Generator) (a : ℤ) (c : Momentum) (e : Electric) :
    weight g a c e*star (weight g a c e) = 1 := by
  have h := PrimitiveYee.character_unit (boundaryMomentum c)
    (PrimitiveYee.reduceTranslation (edgePoint g a e))
  by_cases he : g = .reflect0 ∧ e.1 = 0
  · simpa only [weight, edgeSign, ite_eq_left he, neg_one_mul, star_neg, neg_mul_neg, mul_comm] using h
  · simpa only [weight, edgeSign, ite_eq_right he, one_mul, mul_comm] using h

def matrix (g : Generator) (a : ℤ) (c : Momentum) : Matrix Electric Electric ℂ :=
  fun e f => if f = sourceIndex g a e then weight g a c e else 0

theorem matrix_mulVec (g : Generator) (a : ℤ) (c : Momentum) (v : Electric → ℂ) :
    matrix g a c *ᵥ v = transform g a c v := by
  funext e
  simp [matrix, Matrix.mulVec, dotProduct, ite_mul, transform_apply]

theorem matrix_mul_adjoint (g : Generator) (a : ℤ) (c : Momentum) :
    matrix g a c * (matrix g a c).conjTranspose = 1 := by
  ext e f
  by_cases hef : e = f
  · subst f
    simpa [matrix, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul] using weight_unit g a c e
  · have hindex : sourceIndex g a e ≠ sourceIndex g a f := fun h => hef (sourceIndex_injective g a h)
    simp [matrix, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul, hindex, hef]

theorem matrix_adjoint_mul (g : Generator) (a : ℤ) (c : Momentum) :
    (matrix g a c).conjTranspose * matrix g a c = 1 :=
  mul_eq_one_comm.mp (matrix_mul_adjoint g a c)

def unitaryEquiv (g : Generator) (a : ℤ) (c : Momentum) :
    EuclideanSpace ℂ Electric ≃ₗᵢ[ℂ] EuclideanSpace ℂ Electric :=
  SectorSimplicity.matrixUnitaryEquiv (matrix g a c) (matrix_adjoint_mul g a c) (matrix_mul_adjoint g a c)

end
end Maxwell.Spectral.GlobalCubic
