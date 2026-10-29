import Maxwell.Continuum.CellSpatialFourier
import Maxwell.Continuum.BlochTranslationFiber
import Maxwell.Continuum.EffectiveMassAuxiliaryTranslation

/-! A literal lattice translation of a cell has one Bloch phase shared
by every alias. This is the physical lattice input to the cell-block kernel. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open CellBandFourier FreeFiber MeasureTheory Bloch

def latticeShift (a : Bloch.Alias) : Space := (2 : ℝ) • integerVector a

def latticePhase (a : Bloch.Alias) (q : QuasiCell) : ℂ :=
  phase (-latticeShift a) (quasiFrequencyJoin (q,0))

theorem fourierChar_int (n : ℤ) : (Real.fourierChar (n : ℝ) : ℂ) = 1 := by
  rw [Real.fourierChar_apply]
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  push_cast
  ring

theorem phase_lattice_alias (a : Bloch.Alias) (q : QuasiCell) (ν : FreeFiber.Alias) :
    phase (-latticeShift a) (quasiFrequencyJoin (q,ν)) = latticePhase a q := by
  have he : inner ℝ (quasiFrequencyJoin (q,ν)) (-latticeShift a) =
      inner ℝ (quasiFrequencyJoin (q,0)) (-latticeShift a) +
        ((∑ j : Fin 3, -(ν j * a j) : ℤ) : ℝ) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Fin.sum_univ_three, PiLp.neg_apply, PiLp.smul_apply, latticeShift,
      integerVector_apply, quasiFrequencyJoin_apply, Pi.zero_apply, Int.cast_zero,
      Int.cast_add, Int.cast_neg, Int.cast_mul, mul_zero, add_zero, smul_eq_mul]
    field_simp
    ring
  unfold latticePhase phase
  rw [he, Real.fourierChar.map_add_eq_mul, Circle.coe_mul, fourierChar_int, mul_one]

theorem latticePhase_norm (a : Bloch.Alias) (q : QuasiCell) : ‖latticePhase a q‖ = 1 :=
  phase_norm _ _

theorem fiberTranslation_lattice (a : Bloch.Alias) (q : QuasiCell) (u : FiberSpace) :
    fiberTranslation (-latticeShift a) q u = latticePhase a q • u := by
  apply lp.ext
  funext ν
  rw [fiberTranslation_apply, phase_lattice_alias]
  rfl

def embedLatticeCell (a : Bloch.Alias) : CellFieldL2 →L[ℂ] FieldL2 :=
  (translationOperator (-latticeShift a)).comp embedCell

theorem embedLatticeCell_norm_sq (a : Bloch.Alias) (f : CellFieldL2) :
    ‖embedLatticeCell a f‖^2 = 8 * ‖f‖^2 := by
  change ‖fieldTranslation (-latticeShift a) (embedCell f)‖^2 = _
  rw [(fieldTranslation (-latticeShift a)).norm_map, embedCell_norm_sq]

theorem unitary_embedLatticeCell (a : Bloch.Alias) (f : CellFieldL2) :
    unitary (embedLatticeCell a f) =ᵐ[quasiMeasure] fun q =>
      ((8 : ℂ) * latticePhase a q) • CellFourier.unitary.symm (antiUngauge (quasiMomentum q) f) := by
  change unitary (fieldTranslation (-latticeShift a) (embedCell f)) =ᵐ[quasiMeasure] _
  filter_upwards [unitary_fieldTranslation_ae (-latticeShift a) (embedCell f), unitary_embedCell f]
    with q ht he
  rw [ht, he, fiberTranslation_lattice, smul_smul, mul_comm]

#print axioms phase_lattice_alias
#print axioms unitary_embedLatticeCell

end Maxwell.Continuum.CellGauge
