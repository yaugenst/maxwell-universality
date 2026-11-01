import Maxwell.Continuum.CalibrationBasisForcingTable
import Maxwell.Continuum.CalibrationForcingIndex
import Maxwell.Continuum.CalibrationCachedSchur

/-! The generated finite source is exactly the source in the existing Schur
algorithm. Finite support discharges the extension outside the allocated cube. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open FreeFiber RationalDataflow PartArray ArrayDecodeMachine

theorem tableSource_eq (column : Fin 24) (R : ℕ) (hR : 2≤R)
    (a : Table (aliasArraySize R))
    (ha : ∀i,(a.get i).value=rationalRightCoupling (rationalBasisField column)
      (arrayAliasAt R i) (arrayPolarizationAt R i)) :
    tableSource R a=rationalRightCoupling (rationalBasisField column) := by
  have data : Vector.ofFn (fun i => (a.get i).value)=
      sampleAliasArray R (rationalRightCoupling (rationalBasisField column)) := by
    apply Vector.ext
    intro i hi
    simpa only [sampleAliasArray,Vector.getElem_ofFn,arrayAliasAt,arrayPolarizationAt] using ha ⟨i,hi⟩
  rw [tableSource,data]
  exact extend_sample_supported ((rationalRightCoupling_supported _).mono hR)

theorem rightCoupling_noncentral {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (f : Alias → Fin 3 → V) : rationalNoncentral (rationalRightCoupling f)=rationalRightCoupling f := by
  funext ν j
  by_cases h : rationalCentralCheck ν <;>
    simp only [rationalNoncentral,rationalRightCoupling,Pi.smul_apply,h,Bool.false_eq_true,↓reduceIte,smul_zero]

theorem schur_source_eq (column : Fin 24) (K : ℕ) (a : Table (aliasArraySize (K+2)))
    (ha : ∀i,(a.get i).value=rationalRightCoupling (rationalBasisField column)
      (arrayAliasAt (K+2) i) (arrayPolarizationAt (K+2) i)) :
    tableSource (K+2) a=rationalNoncentral (rationalRightCoupling (rationalBasisField column)) := by
  rw [rightCoupling_noncentral]
  exact tableSource_eq column (K+2) (by omega) a ha

#print axioms schur_source_eq
end Maxwell.Continuum.Calibration.BasisForcing
