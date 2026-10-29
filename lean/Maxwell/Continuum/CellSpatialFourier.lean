import Maxwell.Continuum.CellSpatialExtension
import Maxwell.Continuum.CellBandFourierMomentum
import Maxwell.Continuum.FourierL1L2
import Maxwell.Continuum.BlochFreeGraph

/-! Bloch transform of a literal cell-supported L² field. The formula is
derived from the Euclidean Fourier integral and the complete cell Fourier
basis, with no Fourier summability condition on the field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CellGauge

open CellBandFourier FreeFiber MeasureTheory UnitAddTorus Set Bloch FourierTransform

def forwardPhase (ξ x : Space) : ℂ := Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ)) * Complex.I)

theorem forwardPhase_alias (q : QuasiCell) (ν : FreeFiber.Alias) (x : Space) :
    forwardPhase (quasiFrequencyJoin (q,ν)) x =
      spatialPhase (-(quasiMomentum q + CellGauge.corner)) x * mFourier (-ν) (torusPoint x) := by
  simp only [forwardPhase, spatialPhase, quasiMomentum, CellGauge.corner, realMomentum,
    Pi.neg_apply, Pi.add_apply, mFourier, ContinuousMap.coe_mk, torusPoint,
    Fin.prod_univ_three, fourier_coe_apply, Fin.sum_univ_three,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    quasiFrequencyJoin_apply, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_one,
    Complex.ofReal_intCast, Int.cast_neg, div_one]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  field_simp
  ring

theorem gaugeCoefficient_spatial (q : Momentum) (t : Torus) :
    coefficient q (cellPoint t) = spatialPhase q (spatialEquiv t).val := by
  rw [coefficient_apply]
  rfl

theorem torusPoint_spatialEquiv (t : Torus) : torusPoint (spatialEquiv t).val = t := by
  rw [← spatialEquiv_symm, spatialEquiv.symm_apply_apply]

theorem forwardPhase_coefficient (q : QuasiCell) (ν : FreeFiber.Alias) (t : Torus) :
    forwardPhase (quasiFrequencyJoin (q,ν)) (spatialEquiv t).val =
      mFourier (-ν) t * coefficient (-(quasiMomentum q + CellGauge.corner)) (cellPoint t) := by
  rw [forwardPhase_alias, torusPoint_spatialEquiv, gaugeCoefficient_spatial, mul_comm]

theorem extendScalar_fourier (f : PhysicalScalarCellL2) (ξ : Space) :
    𝓕 (fun x => extendScalar f x) ξ =
      (8 : ℂ) * ∫ x : physicalCell, forwardPhase ξ x.val * f x ∂cellMeanMeasure := by
  rw [Real.fourier_congr_ae (extendScalar_ae f), Real.fourier_eq']
  have he : (fun x : Space => Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ)) * Complex.I) •
      extendFunction f x) = extendFunction (fun x : physicalCell => forwardPhase ξ x.val * f x) := by
    funext x
    by_cases hx : x ∈ physicalCell
    · change forwardPhase ξ x * extendFunction f (⟨x,hx⟩ : physicalCell).val =
        extendFunction (fun y : physicalCell => forwardPhase ξ y.val * f y) (⟨x,hx⟩ : physicalCell).val
      rw [extendFunction_coe, extendFunction_coe]
    · rw [extendFunction_zero f hx, smul_zero, extendFunction_zero _ hx]
  rw [he, extendFunction_integral]
  rfl

theorem extendedField_fourier_coefficient (f : PhysicalCellL2) (q : QuasiCell) (ν : FreeFiber.Alias) (j : Fin 3) :
    𝓕 (fun x => extendField f j x) (quasiFrequencyJoin (q,ν)) =
      (8 : ℂ) * (CellFourier.unitary.symm (antiUngauge (quasiMomentum q) (spatialUnitary f))) ν j := by
  change 𝓕 (fun x => extendScalar (f j) x) (quasiFrequencyJoin (q,ν)) = _
  rw [extendScalar_fourier]
  congr 1
  have he := spatialEquiv_measurePreserving.integral_comp spatialEquiv.measurableEmbedding
    (fun x : physicalCell => forwardPhase (quasiFrequencyJoin (q,ν)) x.val * f j x)
  rw [← he]
  rw [CellFourier.unitary_symm_apply]
  change _ = mFourierBasis.repr (antiUngauge (quasiMomentum q) (spatialUnitary f) j) ν
  rw [mFourierBasis_repr, mFourierCoeff]
  apply integral_congr_ae
  rw [antiUngauge_eq]
  filter_upwards [gauge_ae (-(quasiMomentum q + CellGauge.corner)) (spatialUnitary f) j,
    spatialUnitary_ae f j] with t hg hf
  rw [hg, hf, forwardPhase_coefficient]
  change (mFourier (-ν) t * coefficient (-(quasiMomentum q + CellGauge.corner)) (cellPoint t)) *
      f j (spatialEquiv t) = mFourier (-ν) t *
      (coefficient (-(quasiMomentum q + CellGauge.corner)) (cellPoint t) * f j (spatialEquiv t))
  ring

theorem physicalCell_norm_le (x : physicalCell) : ‖x.val‖ ≤ 4 := by
  have hx := (physicalCell_mem x.val).mp x.property
  have hs : ‖x.val‖^2 ≤ 12 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin 3, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith [(hx j).1, (hx j).2]
      _ = 12 := by norm_num
  nlinarith [norm_nonneg x.val]

theorem extendScalar_integrable (f : PhysicalScalarCellL2) : Integrable (fun x => extendScalar f x) := by
  have hi := integrableOn_Lp_of_measure_ne_top (extendScalar f) (by norm_num : 1 ≤ (2 : ENNReal))
    (isCompact_closedBall (0 : Space) 4).measure_ne_top
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [extendScalar_ae f] with x hx hnot
  rw [hx]
  apply extendFunction_zero
  intro hc
  apply hnot
  simpa only [Metric.mem_closedBall, dist_zero_right] using physicalCell_norm_le ⟨x,hc⟩

theorem unitary_extendField (f : PhysicalCellL2) :
    unitary (extendField f) =ᵐ[quasiMeasure] fun q =>
      (8 : ℂ) • CellFourier.unitary.symm (antiUngauge (quasiMomentum q) (spatialUnitary f)) := by
  have hFourier (j : Fin 3) : ∀ᵐ q ∂quasiMeasure, ∀ ν : FreeFiber.Alias,
      fieldFourier (extendField f) j (quasiFrequencyJoin (q,ν)) =
        (8 : ℂ) * (CellFourier.unitary.symm (antiUngauge (quasiMomentum q) (spatialUnitary f))) ν j := by
    have ha := quasiFrequencyJoin_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (fourierL2_ae_integral (extendScalar (f j)) (extendScalar_integrable (f j)))
    apply product_ae_all_alias (p := fun qν =>
      fieldFourier (extendField f) j (quasiFrequencyJoin qν) =
        (8 : ℂ) * (CellFourier.unitary.symm
          (antiUngauge (quasiMomentum qν.1) (spatialUnitary f))) qν.2 j)
    filter_upwards [ha] with qν hqν
    exact hqν.trans (extendedField_fourier_coefficient f qν.1 qν.2 j)
  filter_upwards [ae_all_iff.mpr hFourier, unitary_coordinate_ae (extendField f)] with q hf hu
  apply Subtype.ext
  funext ν
  apply PiLp.ext
  intro j
  exact (hu ν j).trans (hf j ν)

theorem unitary_embedCell (f : CellFieldL2) :
    unitary (embedCell f) =ᵐ[quasiMeasure] fun q =>
      (8 : ℂ) • CellFourier.unitary.symm (antiUngauge (quasiMomentum q) f) := by
  change unitary (extendField (spatialUnitary.symm f)) =ᵐ[quasiMeasure] _
  simpa only [LinearIsometryEquiv.apply_symm_apply] using unitary_extendField (spatialUnitary.symm f)

#print axioms extendedField_fourier_coefficient
#print axioms unitary_embedCell

end Maxwell.Continuum.CellGauge
