import Maxwell.Continuum.CellSourceFourier
import Maxwell.Continuum.CellSourceContourError
import Maxwell.Continuum.WellInteractionLattice
import Maxwell.Continuum.EffectiveMassActualSource

/-! The literal real nearest-neighbor source coupling and its exact
Fourier formula on the even physical placement lattice. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand EffectiveMass Auxiliary AlmostAnalytic Bloch MeasureTheory CellBandFourier

attribute [local irreducible] Auxiliary.resolvent realMode

def axialSourceCoupling {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (d : ℝ) : ℂ :=
  inner ℂ (sourceMode h (realMode D hh))
    (resolvent D le_rfl (by positivity)
      (fieldTranslation (poleAxialDisplacement h d j) (sourceMode h (realMode D hh))))

theorem axialSourceCoupling_real {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (d : ℝ) : (axialSourceCoupling D hh j d).im = 0 := by
  apply inner_im_zero_of_real (sourceMode_real h (realMode_real D hh))
  apply resolvent_preserves_real
  exact fieldTranslation_preserves_real _ (sourceMode_real h (realMode_real D hh))

theorem latticeShift_neg (a : Bloch.Alias) : latticeShift (-a) = -latticeShift a := by
  have he := latticeShift_add (-a) a
  rw [neg_add_cancel, latticeShift_zero] at he
  exact eq_neg_of_add_eq_zero_right (by simpa only [add_comm] using he.symm)

theorem carrier_lattice_even {a : Bloch.Alias} (ha : ∀ j, Even (a j)) : carrier (latticeShift a) = 1 := by
  choose b hb using ha
  have he : a = b+b := funext hb
  rw [he, latticeShift_add, carrier_twice_lattice]

theorem placementCell_even {L : ℕ} (hL : Even L) (d : ℕ) (ν : Bloch.Alias) :
    ∀ j, Even (placementCell L d ν j) := by
  obtain ⟨m, hm⟩ := hL
  intro j
  refine ⟨(m : ℤ)*(d : ℤ)*(placementMatrix.mulVec ν) j, ?_⟩
  simp only [placementCell, hm, Nat.cast_add]
  ring

theorem placementCell_axial (L d : ℕ) (j : Fin 3) :
    latticeShift (placementCell L d (Pi.single j 1)) =
      poleAxialDisplacement (L : ℝ)⁻¹ (d : ℝ) j := by
  rw [placementCell_displacement, poleAxialDisplacement_eq_placed, inv_inv]
  congr 2
  apply PiLp.ext
  intro i
  simp only [integerVector_apply, Pi.single_apply, PiLp.single_apply]
  split_ifs <;> simp

theorem axialSourceCoupling_fourier {L : ℕ} {z : ℝ} (hL : MasterConstants.Ls ≤ (L : ℝ))
    (hLe : Even L) (D : Calibration (L : ℝ)⁻¹ z) (j : Fin 3) (d : ℕ) :
    axialSourceCoupling D (MasterConstants.inverse_length_le_1024 hL) j (d : ℝ) =
      ((64*blochDensity : ℝ) : ℂ)*OperatorFourier.angularFourier
        (fun q => (Well.chi smallRadius q : ℂ)*cellSourcePairing (L : ℝ)⁻¹
          (realMode D (MasterConstants.inverse_length_le_1024 hL))
          (realMode D (MasterConstants.inverse_length_le_1024 hL))
          (fullCellSymbol z 0) (realMomentumMap q))
        (-poleAxialDisplacement (L : ℝ)⁻¹ (d : ℝ) j) := by
  let hh := MasterConstants.inverse_length_le_1024 hL
  let a := placementCell L d (Pi.single j 1)
  have ha : latticeShift a = poleAxialDisplacement (L : ℝ)⁻¹ (d : ℝ) j := placementCell_axial L d j
  have hc : carrier (latticeShift (-a)) = 1 := by
    rw [latticeShift_neg, carrier_neg_lattice]
    exact carrier_lattice_even (placementCell_even hLe d (Pi.single j 1))
  have he := source_resolvent_fourier_integral D le_rfl (by positivity) (-a) (realMode D hh) (realMode D hh)
  rw [hc, mul_one, latticeShift_neg, ha, neg_neg] at he
  rw [OperatorFourier.angularFourier_integral]
  refine he.trans ?_
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro q
  change _ = OperatorFourier.angularPhase q (-poleAxialDisplacement (L : ℝ)⁻¹ (d : ℝ) j)*
      ((cutoff q : ℂ)*cellSourcePairing (L : ℝ)⁻¹ (realMode D hh) (realMode D hh)
        (fullCellSymbol z 0) (realMomentumMap q))
  ring

#print axioms axialSourceCoupling_real
#print axioms axialSourceCoupling_fourier

end Maxwell.Continuum.CellGauge
