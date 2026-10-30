import Maxwell.Continuum.CellSourceContourError
import Maxwell.Continuum.PeriodicSeparatedCutoff

/-! Exact h-rescaling of the physical source-contracted Maxwell symbol.
The selected scalar quotient and the complete other-band remainder
are identified with the literal physical resolvent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand EffectiveMass Auxiliary AlmostAnalytic

attribute [local irreducible] fullCellSymbol separatedCellSymbol realMode

theorem sourceScale_square {h : ℝ} (hh : 0 < h) : (sourceScale h)^2 = h^3 := by
  rw [sourceScale, mul_pow, Real.sq_sqrt hh.le]
  ring

theorem poleContour_scaled_momentum {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (k : Space) :
    AlmostAnalytic.shiftedMomentum (h • k) (poleContourShift D hh j) 1 =
      poleMomentum D hh j (realMomentum k.ofLp) := by
  rw [poleContourShift_momentum, poleMomentum_real_shift]
  rfl

theorem selectedPoleNumerator_sourceFactors {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (k : Momentum) :
    selectedPoleNumerator D hh j k = (h : ℂ)^3*
      sourceFactor h (realMode D hh) (poleMomentum D hh j k)*
      sourceFactor h (realMode D hh) (-poleMomentum D hh j k) := by
  rw [selectedPoleNumerator, scaledSourceProduct_eq D.h_pos, scaledPoleCenter_physical]

theorem scaled_source_symbol_pole {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (k : Momentum)
    (hq : ‖poleMomentum D hh j k‖ ≤ separatedRadius)
    (hchart : poleMomentum D hh j k ∈ physicalChart)
    (hne : dielectricBand (poleMomentum D hh j k)-(z : ℂ) ≠ 0) :
    (h : ℂ)^5*((64*blochDensity : ℝ) : ℂ)*
      cellSourcePairing h (realMode D hh) (realMode D hh) (fullCellSymbol z 0) (poleMomentum D hh j k) =
        selectedGlobalQuotient D hh j k+
          ((64*blochDensity : ℝ) : ℂ)*separatedSourceSymbol D hh j (realMode D hh) (realMode D hh) k := by
  have hp := cellSourcePairing_full_pole D (realMode_real D hh) hq hchart hne
  calc
    _ = (h : ℂ)^5*(sourceFactor h (realMode D hh) (poleMomentum D hh j k)*
        sourceFactor h (realMode D hh) (-poleMomentum D hh j k)/
          (dielectricBand (poleMomentum D hh j k)-(z : ℂ))+
        ((64*blochDensity : ℝ) : ℂ)*cellSourcePairing h (realMode D hh) (realMode D hh)
          (separatedCellSymbol z 0) (poleMomentum D hh j k)) := by rw [← hp]; ring
    _ = _ := by
      rw [selectedGlobalQuotient, selectedPoleNumerator_sourceFactors, poleDenominator,
        separatedSourceSymbol_eq_pairing, sourceScale_square D.h_pos]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr D.h_pos.ne', hne]

#print axioms scaled_source_symbol_pole

end Maxwell.Continuum.CellGauge
