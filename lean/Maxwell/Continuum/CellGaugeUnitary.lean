import Maxwell.Continuum.CellSeparatedSymbol

/-! Real-momentum gauge transport of the actual cell Hermitian pairing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open FreeFiber CellBandFourier FiberAnalytic

theorem antiGauge_real_norm (q : Fin 3 → ℝ) (f : CellFieldL2) :
    ‖antiGauge (realMomentum q) f‖ = ‖f‖ := by
  change ‖gauge (realMomentum q) (gauge (realMomentum (fun _ => Real.pi / 2)) f)‖ = _
  rw [gauge_real_isometry, gauge_real_isometry]

def realUnitary (q : Fin 3 → ℝ) : CellFieldL2 ≃ₗᵢ[ℂ] CellFieldL2 where
  __ := (antiGauge (realMomentum q)).toLinearMap
  invFun := antiUngauge (realMomentum q)
  left_inv f := congrArg (fun T : CellMap => T f) (antiUngauge_comp_antiGauge (realMomentum q))
  right_inv f := congrArg (fun T : CellMap => T f) (antiGauge_comp_antiUngauge (realMomentum q))
  norm_map' := antiGauge_real_norm q

theorem realUnitary_apply (q : Fin 3 → ℝ) (f : CellFieldL2) :
    realUnitary q f = antiGauge (realMomentum q) f := rfl

theorem realUnitary_symm_apply (q : Fin 3 → ℝ) (f : CellFieldL2) :
    (realUnitary q).symm f = antiUngauge (realMomentum q) f := rfl

theorem gauged_inner (q : Fin 3 → ℝ) (T : FiberMap) (g f : CellFieldL2) :
    inner ℂ (CellFourier.unitary.symm (antiUngauge (realMomentum q) g))
      (T (CellFourier.unitary.symm (antiUngauge (realMomentum q) f))) =
    inner ℂ g (antiGauge (realMomentum q)
      (conjugate T (antiUngauge (realMomentum q) f))) := by
  rw [conjugate_apply]
  calc
    _ = inner ℂ (antiUngauge (realMomentum q) g)
        (CellFourier.unitary (T (CellFourier.unitary.symm (antiUngauge (realMomentum q) f)))) := by
      rw [← CellFourier.unitary.inner_map_map]
      rw [CellFourier.unitary.apply_symm_apply]
    _ = inner ℂ ((realUnitary q) ((realUnitary q).symm g))
        ((realUnitary q) (CellFourier.unitary
          (T (CellFourier.unitary.symm (antiUngauge (realMomentum q) f))))) :=
      ((realUnitary q).inner_map_map _ _).symm
    _ = _ := by rw [LinearIsometryEquiv.apply_symm_apply]; rfl

#print axioms realUnitary
#print axioms gauged_inner

end Maxwell.Continuum.CellGauge
