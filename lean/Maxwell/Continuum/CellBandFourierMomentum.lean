import Maxwell.Continuum.CellBandFourierGauge

/-! The reconstructed Fourier exponent is exactly the momentum in the
literal maximal Maxwell fiber, including the antiperiodic corner shift. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber UnitAddTorus Filter
open scoped Topology

def spatialPhase (q : Momentum) (x : Space) : ℂ :=
  Complex.exp (Complex.I * ∑ j : Fin 3, q j * (x j : ℂ))

theorem aliasPhase_eq (ν : Alias) (x : Space) :
    carrier x * mFourier ν (torusPoint x) = spatialPhase (aliasMomentum 0 ν) x := by
  simp only [carrier, mFourier, ContinuousMap.coe_mk, torusPoint, Fin.prod_univ_three,
    fourier_coe_apply, spatialPhase, Fin.sum_univ_three,
    aliasMomentum, Pi.zero_apply, add_zero, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_ofNat, Complex.ofReal_one, div_one]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem spatialPhase_add (q p : Momentum) (x : Space) :
    spatialPhase (q+p) x = spatialPhase q x * spatialPhase p x := by
  unfold spatialPhase
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add, Complex.exp_add]

theorem aliasMomentum_add (q : Momentum) (ν : Alias) : aliasMomentum q ν = q + aliasMomentum 0 ν := by
  funext j
  simp only [aliasMomentum, Pi.add_apply, Pi.zero_apply, add_zero]
  ring

def blochField (q : Momentum) (u : FiberSpace) (x : Space) : Polarization :=
  spatialPhase q x • antiperiodicField u x

theorem antiperiodicField_hasSum (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) (x : Space) :
    HasSum (fun ν => spatialPhase (aliasMomentum 0 ν) x • u ν) (antiperiodicField u x) := by
  have h := (periodicSeries_apply_hasSum u hu (torusPoint x)).const_smul (carrier x)
  simpa only [smul_smul, aliasPhase_eq, antiperiodicField, periodicField] using h

theorem blochField_hasSum (q : Momentum) (u : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (x : Space) :
    HasSum (fun ν => spatialPhase (aliasMomentum q ν) x • u ν) (blochField q u x) := by
  have h := (antiperiodicField_hasSum u hu x).const_smul (spatialPhase q x)
  simpa only [smul_smul, ← spatialPhase_add, ← aliasMomentum_add, blochField] using h

theorem antiperiodicField_uniform (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : Finset Alias in atTop, ∀ x : Space,
      ‖(∑ ν ∈ s, spatialPhase (aliasMomentum 0 ν) x • u ν) - antiperiodicField u x‖ < ε := by
  filter_upwards [periodicSeries_uniform u hu ε hε] with s hs x
  have heq : (∑ ν ∈ s, spatialPhase (aliasMomentum 0 ν) x • u ν) - antiperiodicField u x =
      carrier x • ((∑ ν ∈ s, mFourier ν (torusPoint x) • u ν) - periodicSeries u (torusPoint x)) := by
    simp only [smul_sub, Finset.smul_sum, smul_smul, aliasPhase_eq]
    rfl
  rw [heq, norm_smul, carrier_norm, one_mul]
  exact hs _

#print axioms aliasPhase_eq
#print axioms blochField_hasSum
#print axioms antiperiodicField_uniform

end Maxwell.Continuum.CellBandFourier
