import Maxwell.Continuum.CellGaugeAdjoint

/-! The dual factor in the actual selected cell projection is the
physical Bloch wave at opposite momentum. The pairing is bilinear,
with the cell's literal mean-volume normalization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand FiberNormalization CellBandFourier MeasureTheory

attribute [local irreducible] normalizedFiberVector

def cellFieldValue (f : CellFieldL2) (t : Torus) : Polarization := WithLp.toLp 2 (fun j => f j t)

theorem cell_inner_integral (f g : CellFieldL2) :
    inner ℂ f g = ∫ t, inner ℂ (cellFieldValue f t) (cellFieldValue g t) ∂torusMeasure := by
  rw [PiLp.inner_apply]
  simp only [L2.inner_def, cellFieldValue, PiLp.inner_apply]
  rw [integral_finsetSum Finset.univ (fun j _ => L2.integrable_inner (𝕜 := ℂ) (f j) (g j))]

def selectedCellDualVector (q : Momentum) : CellFieldL2 :=
  antiGauge (star q) (CellFourier.unitary (star (normalizedFiberVector (unscale q))))

theorem selectedCellFunctional_inner (q : Momentum) (f : CellFieldL2) :
    selectedCellFunctional q f = inner ℂ (selectedCellDualVector q) f := by
  change bilinear (normalizedFiberVector (unscale q))
    (CellFourier.unitary.symm (antiUngauge q f)) = _
  rw [bilinear_apply, ← CellFourier.unitary.inner_map_map,
    CellFourier.unitary.apply_symm_apply, antiUngauge_inner]
  rfl

theorem unscale_neg (q : Momentum) : unscale (-q) = -unscale q := by
  simp only [unscale, smul_neg]

theorem physicalSelectedWave_dual_star {q : Momentum} (hq : q ∈ physicalChart) (x : Space) :
    star (physicalSelectedWave (-q) x) =
      I • blochField (star q) (star (normalizedFiberVector (unscale q))) x := by
  rw [physicalSelectedWave, star_smul, spatialPhase_star, unscale_neg,
    cellEigenfunction_dual_star (unscale_mem_chart hq)]
  simp only [star_neg, neg_neg, blochField]
  exact smul_comm _ _ _

theorem selectedCellDualVector_ae {q : Momentum} (hq : q ∈ physicalChart) :
    (fun t => cellFieldValue (selectedCellDualVector q) t) =ᵐ[torusMeasure]
      fun t => blochField (star q) (star (normalizedFiberVector (unscale q))) (spatialEquiv t).val := by
  filter_upwards [ae_all_iff.mpr (fun j : Fin 3 =>
    gauged_unitary_ae (star q) (star (normalizedFiberVector (unscale q)))
      (normalizedFiberVector_star_summable (unscale_mem_chart hq)) j)] with t ht
  apply PiLp.ext
  intro j
  exact ht j

def cellSourceFunctional (q : Momentum) (f : CellFieldL2) : ℂ :=
  ∫ t, bilinear (physicalSelectedWave (-q) (spatialEquiv t).val) (cellFieldValue f t) ∂torusMeasure

theorem cellSourceFunctional_eq {q : Momentum} (hq : q ∈ physicalChart) (f : CellFieldL2) :
    cellSourceFunctional q f = -I * selectedCellFunctional q f := by
  rw [selectedCellFunctional_inner, cell_inner_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [selectedCellDualVector_ae hq] with t ht
  rw [bilinear_apply, physicalSelectedWave_dual_star hq, ← ht, inner_smul_left]
  simp only [Complex.conj_I]

theorem selectedCellProjection_physical {q : Momentum} (hq : q ∈ physicalChart)
    (f : CellFieldL2) :
    selectedCellProjection q f = cellSourceFunctional q f • selectedCellWave q := by
  rw [selectedCellProjection_apply hq, cellSourceFunctional_eq hq, selectedCellWave, smul_smul]
  congr 1
  calc
    selectedCellFunctional q f = (-I*I)*selectedCellFunctional q f := by norm_num
    _ = _ := by ring

#print axioms selectedCellProjection_physical

end Maxwell.Continuum.CellGauge
