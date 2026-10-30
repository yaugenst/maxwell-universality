import Maxwell.Continuum.CalibrationCentralCoordinates

/-! Executable indexing of the actual 24 central alias-polarization modes. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def boolFinTwo : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := i.val == 1
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

def parityFinEight : Corner.Parity ≃ Fin 8 :=
  ((Equiv.prodCongr boolFinTwo (Equiv.prodCongr boolFinTwo boolFinTwo)).trans
    (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv)).trans finProdFinEquiv

def centralIndexFin : CentralIndex ≃ Fin 24 :=
  (Equiv.prodCongr parityFinEight (Equiv.refl _)).trans finProdFinEquiv

def rationalCubeAlias (s : Corner.Parity) : Alias :=
  fun j => if ![s.1,s.2.1,s.2.2] j then 0 else -1

theorem rationalCubeAlias_eq (s : Corner.Parity) : rationalCubeAlias s = CornerBridge.cubeAlias s := rfl

theorem rationalCubeAlias_injective : Function.Injective rationalCubeAlias := by
  intro s t h
  apply CornerBridge.parityAliasEquiv.injective
  apply Subtype.ext
  exact h

noncomputable def centralFinUnitary : EuclideanSpace ℂ (Fin 24) ≃ₗᵢ[ℂ] centralSpace :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ centralIndexFin.symm).trans centralUnitary

theorem centralFinUnitary_apply (x : EuclideanSpace ℂ (Fin 24)) (s : Corner.Parity) (j : Fin 3) :
    (centralFinUnitary x).val (rationalCubeAlias s) j = x (centralIndexFin (s,j)) := by
  change (centralUnitary _).val (CornerBridge.cubeAlias s) j = _
  rw [centralUnitary_apply]
  rfl

theorem centralFinUnitary_symm_apply (u : centralSpace) (i : Fin 24) :
    centralFinUnitary.symm u i = u.val (rationalCubeAlias (centralIndexFin.symm i).1)
      (centralIndexFin.symm i).2 := by
  have h := centralFinUnitary_apply (centralFinUnitary.symm u)
    (centralIndexFin.symm i).1 (centralIndexFin.symm i).2
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using h.symm

#print axioms centralFinUnitary

end Maxwell.Continuum.Calibration
