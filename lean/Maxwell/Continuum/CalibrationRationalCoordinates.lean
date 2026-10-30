import Maxwell.Continuum.CalibrationRationalMatrix
import Maxwell.Continuum.CalibrationKernel

/-! Executable extraction and insertion of the central 24 coefficients.
The insertion is the actual orthonormal central-space inclusion. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def rationalAliasParity (ν : Alias) : Corner.Parity :=
  (decide (ν 0 = 0),decide (ν 1 = 0),decide (ν 2 = 0))

theorem rationalAliasParity_cube (s : Corner.Parity) : rationalAliasParity (rationalCubeAlias s) = s := by
  obtain ⟨a,b,c⟩ := s
  cases a <;> cases b <;> cases c <;> decide

def rationalCoordinates {V : Type*} (f : Alias → Fin 3 → V) : Fin 24 → V :=
  fun i => f (rationalCubeAlias (centralIndexFin.symm i).1) (centralIndexFin.symm i).2

def rationalExpandCoordinates {V : Type*} [Zero V] (x : Fin 24 → V) : Alias → Fin 3 → V :=
  fun ν j => if rationalCentralCheck ν then x (centralIndexFin (rationalAliasParity ν,j)) else 0

theorem rationalCoordinates_represents {f : RationalAliasField} {u : FiberSpace}
    (hf : Represents f u) (i : Fin 24) :
    rationalComplexValue (rationalCoordinates f i) =
      centralFinUnitary.symm (centralProjectionToSpace u) i := by
  rw [centralFinUnitary_symm_apply]
  change rationalComplexValue (f _ _) = centralAliasProjection u _ _
  rw [centralAliasProjection_apply]
  simp only [rationalCubeAlias_eq,CornerBridge.alias_central,↓reduceIte]
  exact hf _ _

theorem rationalExpandCoordinates_represents (x : Fin 24 → RationalComplex)
    (y : EuclideanSpace ℂ (Fin 24)) (hx : ∀ i, rationalComplexValue (x i) = y i) :
    Represents (rationalExpandCoordinates x) (centralFinUnitary y).val := by
  intro ν j
  by_cases hν : IsCentralAlias ν
  · obtain ⟨s,hs⟩ := CornerBridge.parityAliasEquiv.surjective ⟨ν,hν⟩
    have ha : rationalCubeAlias s = ν := congrArg Subtype.val hs
    rw [← ha,centralFinUnitary_apply]
    unfold rationalExpandCoordinates
    have hb := (rationalCentralCheck_true (rationalCubeAlias s)).mpr (CornerBridge.alias_central s)
    rw [hb]
    simp only [↓reduceIte,rationalAliasParity_cube]
    exact hx _
  · have hb : rationalCentralCheck ν = false := Bool.eq_false_iff.mpr
      (fun h => hν ((rationalCentralCheck_true ν).mp h))
    rw [centralSpace_noncentral _ ν hν]
    simp only [rationalExpandCoordinates,hb,Bool.false_eq_true,↓reduceIte]
    exact map_zero rationalComplexLinear

def rationalCentralMatrixApply {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (M : Matrix (Fin 24) (Fin 24) ℚ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  rationalExpandCoordinates (fun i => ∑ j, M i j • rationalCoordinates f j)

theorem rationalCentralMatrixApply_represents (M : Matrix (Fin 24) (Fin 24) ℚ)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalCentralMatrixApply M f)
      (centralFinUnitary (centralMatrixCLM (M.map (Rat.castHom ℂ))
        (centralFinUnitary.symm (centralProjectionToSpace u)))).val := by
  apply rationalExpandCoordinates_represents
  intro i
  change rationalComplexLinear (∑ j, M i j • rationalCoordinates f j) = _
  simp only [map_sum,map_smul]
  simp_rw [← Rat.cast_smul_eq_qsmul ℂ,smul_eq_mul]
  change (∑ j, (M i j : ℂ)*rationalComplexValue (rationalCoordinates f j)) =
    ∑ j, (M i j : ℂ)*(centralFinUnitary.symm (centralProjectionToSpace u)) j
  apply Finset.sum_congr rfl
  intro j _
  rw [rationalCoordinates_represents hf]

#print axioms rationalCentralMatrixApply_represents

end Maxwell.Continuum.Calibration
