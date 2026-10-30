import Maxwell.Continuum.CalibrationCachedExact
import Maxwell.Continuum.CalibrationRationalFullSupport
import Maxwell.Continuum.CalibrationEdgeEvaluator

/-! A materialized-cache implementation of the certified edge matrix.
The alias cube has radius K+2 because the coupling is supported within
radius two before the K Neumann steps. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def cachedSchurApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  rationalCentralMaterial t E r f-rationalLeftCoupling
    (extendAliasArray (K+2) (cachedInverseApply t E r (K+2)
      (rationalNoncentral (rationalRightCoupling f)) K))

theorem cachedSchurApply_eq {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) (f : Alias → Fin 3 → V) :
    cachedSchurApply t E r K f = rationalSchurApply t E r K f := by
  unfold cachedSchurApply rationalSchurApply
  rw [cachedInverseApply_exact t E r (rationalRightCoupling_supported f).noncentral
    (K+2) K (by omega)]

def cachedSchurMatrix (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) : Matrix (Fin 24) (Fin 24) ℚ :=
  fun i j => cachedSchurApply t E r K (rationalBasisField j)
    (rationalCubeAlias (centralIndexFin.symm i).1) (centralIndexFin.symm i).2

theorem cachedSchurMatrix_eq (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) :
    cachedSchurMatrix t E r K = rationalSchurMatrix t E r K := by
  ext i j
  exact congrFun (congrFun (cachedSchurApply_eq t E r K (rationalBasisField j)) _) _

def cachedEdgeMatrix (q : ℚ) (N : ℕ) : Matrix (Fin 24) (Fin 24) ℚ :=
  symmetricRationalMatrix (cachedSchurMatrix (piCenter (N+1)) (q+7) (fun _ => 0) (N+3))

theorem cachedEdgeMatrix_eq (q : ℚ) (N : ℕ) : cachedEdgeMatrix q N = edgeMatrix q N := by
  unfold cachedEdgeMatrix edgeMatrix
  rw [cachedSchurMatrix_eq]

#print axioms cachedEdgeMatrix_eq

end Maxwell.Continuum.Calibration
