import Maxwell.Spectral.LocalClusterCount
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

namespace Maxwell.Spectral.CenteredInverse
open Maxwell.Certificate.FourierBinding
open PeriodicYee PrimitiveYee LocalClusterCount YeeTaylor YeeTaylorRemainder
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem invertible_of_conjugacy (A B U V : H →L[ℂ] H)
    (hUV : U*V=1) (hVU : V*U=1) (hbind : V*A*U=B) (hB : B.IsInvertible) :
    A.IsInvertible := by
  have hU : U.IsInvertible := ContinuousLinearMap.IsInvertible.of_inverse hUV hVU
  have hV : V.IsInvertible := ContinuousLinearMap.IsInvertible.of_inverse hVU hUV
  have he : U*B*V=A := by
    rw [← hbind]
    calc
      U*(V*A*U)*V = (U*V)*A*(U*V) := by simp only [mul_assoc]
      _ = A := by rw [hUV]; simp
  have hi : (U*B*V).IsInvertible := (hU.comp hB).comp hV
  rwa [he] at hi

theorem boundary_of_centered (k : Translation) (q : Momentum) (E : ℝ)
    (h : (centeredOperator k q-(E:ℂ) • 1).IsInvertible) :
    (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (PrimitiveYee.fiber Concrete.material (boundaryMomentum (centeredMomentum k q))) - (E:ℂ) • 1).IsInvertible := by
  let T := Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
  let G := YeeTaylor.electricGauge q
  have hunit := electricGauge_unitary q
  have hUV : T G * T G.conjTranspose = 1 := by
    rw [← map_mul, hunit.2, map_one]
  have hVU : T G.conjTranspose * T G = 1 := by
    rw [← map_mul, hunit.1, map_one]
  have hm : G.conjTranspose *
      (PrimitiveYee.fiber Concrete.material (boundaryMomentum (centeredMomentum k q))-(E:ℂ) • 1) * G =
      centeredFiber Concrete.material (timeReversalMomentum k) q-(E:ℂ) • 1 := by
    rw [centeredMomentum_binding]
    dsimp only [G]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hunit.1, centeredFiber_gauge]
  have hb : T G.conjTranspose *
      (T (PrimitiveYee.fiber Concrete.material (boundaryMomentum (centeredMomentum k q)))-(E:ℂ) • 1) * T G =
      centeredOperator k q-(E:ℂ) • 1 := by
    simpa only [map_mul, map_sub, map_smul, map_one, T, centeredOperator] using congrArg T hm
  exact invertible_of_conjugacy _ _ (T G) (T G.conjTranspose) hUV hVU hb h

end
end Maxwell.Spectral.CenteredInverse
