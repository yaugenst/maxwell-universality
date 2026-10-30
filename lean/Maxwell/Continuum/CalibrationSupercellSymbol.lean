import Maxwell.Continuum.CalibrationSupercellEmbedding
import Maxwell.Continuum.CalibrationCutoffGrid
import Maxwell.Continuum.CalibrationTorusImages

/-! Exact identification of each sampled supercell inverse with the
literal continuum cell symbol, including the antiperiodic phase. -/

noncomputable section
set_option maxRecDepth 2048

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier PeriodicSampling Auxiliary

variable (M : ℕ) [NeZero M]

attribute [local irreducible] fiberResolvent fullFiberResolvent

omit [NeZero M] in
theorem cellUnitary_symm_apply (j : Grid M) (f : CellFieldL2) :
    (cellUnitary M j).symm f=CellFourier.unitary.symm (antiUngauge (momentum M j) f) := rfl

theorem carrier_star (x : Space) : star (carrier x)=carrier (-x) := by
  rw [Complex.star_def,← Complex.inv_eq_conj (carrier_norm x)]
  unfold carrier
  simp only [PiLp.neg_apply,Finset.sum_neg_distrib,mul_neg,Complex.ofReal_neg,neg_mul,Complex.exp_neg]

theorem cellPhase_product (j : Grid M) (a b : Alias) :
    cellPhase M j a*star (cellPhase M j b)=
      carrier (latticeShift a-latticeShift b)*Product.character M (-Product.frequency M (b-a)) j := by
  rw [cellPhase,cellPhase,star_mul,carrier_star,character_conj]
  calc
    _ = (carrier (latticeShift a)*carrier (-latticeShift b))*
        (Product.character M (Product.frequency M a) j*
          Product.character M (-Product.frequency M b) j) := by ring
    _ = _ := by
      rw [← carrier_add,Product.character_mul]
      congr 2
      funext i
      simp only [Product.frequency,Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Int.cast_sub]
      ring

theorem cellUnitary_gridInverse {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0≤σ) (hσ : σ≤h^4/64) (j : Grid M) (f : CellFieldL2) :
    cellUnitary M j (actualGridInverse z σ (fun i => centeredGrid M (j i))
      ((cellUnitary M j).symm f))=
      torusCellSymbol D hσ0 hσ
        (fun i => ((((j i).val : ℝ)/(M : ℝ) : ℝ) : UnitAddCircle)) f := by
  change _ = (scaledCutoffSymbol z σ (centeredRepresentative
    (fun i => ((((j i).val : ℝ)/(M : ℝ) : ℝ) : UnitAddCircle)))) f
  rw [centeredRepresentative_grid]
  unfold scaledCutoffSymbol cutoffFullCellSymbol cutoffSymbol realSymbol
  rw [smul_apply,fullCellSymbol_apply]
  change cellUnitary M j
      ((cutoff (WithLp.toLp 2 (gridMomentum (fun i => centeredGrid M (j i)))) : ℂ) •
        fiberResolvent z σ (gridMomentum (fun i => centeredGrid M (j i)))
          ((cellUnitary M j).symm f)) = _
  rw [map_smul,cellUnitary_apply]
  have hq : realMomentumMap (Real.pi • (WithLp.toLp 2
      (fun i => (centeredGrid M (j i) : ℝ)) : Space))=momentum M j := rfl
  rw [hq]
  rw [show momentum M j=realMomentum (gridMomentum (fun i => centeredGrid M (j i))) from rfl,
    CellGauge.fullFiberResolvent_real]
  rw [cellUnitary_symm_apply]
  rfl

#print axioms cellUnitary_gridInverse

end Maxwell.Continuum.Calibration.Supercell
