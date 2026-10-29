import Maxwell.Continuum.CellBandFourier
import Maxwell.Continuum.BlochPartition

/-! Physical period-two reconstruction and its antiperiodic corner
carrier. The resulting alias momenta are exactly `π/2 + πν`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber FiberNormalization UnitAddTorus

def torusPoint (x : Space) : Torus := fun j => (x j / 2 : ℝ)

theorem torusPoint_continuous : Continuous torusPoint := by
  apply continuous_pi
  intro j
  exact (AddCircle.continuous_mk' 1).comp ((PiLp.continuous_apply 2 _ j).div_const 2)

theorem torusPoint_period (x : Space) (n : Bloch.Alias) :
    torusPoint (x + (2 : ℝ) • Bloch.integerVector n) = torusPoint x := by
  funext j
  change (((x j + 2 * (n j : ℝ)) / 2 : ℝ) : UnitAddCircle) = (x j / 2 : ℝ)
  rw [show (x j + 2 * (n j : ℝ)) / 2 = x j / 2 + (n j : ℝ) by ring,
    AddCircle.coe_add]
  have hn : ((n j : ℝ) : UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨n j, by simp⟩
  rw [hn, add_zero]

def carrier (x : Space) : ℂ :=
  Complex.exp (((Real.pi / 2 * ∑ j : Fin 3, x j : ℝ) : ℂ) * Complex.I)

theorem carrier_continuous : Continuous carrier := by unfold carrier; fun_prop

theorem carrier_norm (x : Space) : ‖carrier x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem carrier_add (x y : Space) : carrier (x + y) = carrier x * carrier y := by
  unfold carrier
  simp only [PiLp.add_apply, Finset.sum_add_distrib, mul_add, Complex.ofReal_add, add_mul,
    Complex.exp_add]

theorem carrier_two_direction (j : Fin 3) : carrier ((2 : ℝ) • coordinateDirection j) = -1 := by
  have hs : ∑ i : Fin 3, ((2 : ℝ) • coordinateDirection j) i = 2 := by
    simp [coordinateDirection, PiLp.single_apply]
  unfold carrier
  rw [hs]
  convert Complex.exp_pi_mul_I using 1
  congr 2
  ring

def periodicField (u : FiberSpace) (x : Space) : Polarization := periodicSeries u (torusPoint x)

def antiperiodicField (u : FiberSpace) (x : Space) : Polarization := carrier x • periodicField u x

theorem periodicField_continuous (u : FiberSpace) : Continuous (periodicField u) :=
  (periodicSeries u).continuous.comp torusPoint_continuous

theorem antiperiodicField_continuous (u : FiberSpace) : Continuous (antiperiodicField u) :=
  carrier_continuous.smul (periodicField_continuous u)

theorem periodicField_period (u : FiberSpace) (x : Space) (n : Bloch.Alias) :
    periodicField u (x + (2 : ℝ) • Bloch.integerVector n) = periodicField u x := by
  rw [periodicField, torusPoint_period]
  rfl

theorem integerVector_unitAlias (j : Fin 3) : Bloch.integerVector (unitAlias j) = coordinateDirection j := by
  apply PiLp.ext
  intro i
  by_cases hi : i = j <;> simp [Bloch.integerVector, unitAlias, coordinateDirection, hi]

theorem antiperiodicField_translate (u : FiberSpace) (x : Space) (j : Fin 3) :
    antiperiodicField u (x + (2 : ℝ) • coordinateDirection j) = -antiperiodicField u x := by
  unfold antiperiodicField
  rw [carrier_add, carrier_two_direction, ← integerVector_unitAlias,
    periodicField_period, mul_neg, mul_one, neg_smul]

theorem antiperiodicField_norm (u : FiberSpace) (x : Space) :
    ‖antiperiodicField u x‖ = ‖periodicSeries u (torusPoint x)‖ := by
  rw [antiperiodicField, norm_smul, carrier_norm, one_mul]
  rfl

theorem antiperiodicField_norm_le (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) (x : Space) :
    ‖antiperiodicField u x‖ ≤ ∑' ν, ‖u ν‖ := by
  rw [antiperiodicField_norm]
  exact periodicSeries_apply_norm_le u hu _

theorem band_antiperiodicField_norm_le {t : Momentum} (ht : t ∈ PeriodicBand.chart) (x : Space) :
    ‖antiperiodicField (normalizedFiberVector t) x‖ ≤ 32 :=
  (antiperiodicField_norm_le _ (normalizedFiberVector_fourier_l1 ht).1 x).trans
    (normalizedFiberVector_fourier_l1 ht).2

#print axioms antiperiodicField_translate
#print axioms band_antiperiodicField_norm_le

end Maxwell.Continuum.CellBandFourier
