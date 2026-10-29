import Maxwell.Composition.PeriodicBackground
import Maxwell.Defect.ConcreteFiniteStencil
import Maxwell.Spectral.InfiniteNorm

/-! The rational selected energy is folded into the actual scalar cells.
The emitted operating material defines exactly the certified shifted
infinite operator and retains an explicit scalar reserve. -/
namespace Maxwell.Composition
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
noncomputable section

def operatingMaterial (z : ℚ) (c : Cell20) : ℚ :=
  FiniteStencil.frozenMaterialQ c + 64 * z

theorem operatingMaterial_real (z : ℚ) (c : Cell20) :
    (operatingMaterial z c : ℝ) = Concrete.material c + 64 * (z : ℝ) := by
  simp only [operatingMaterial, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
    FiniteStencil.frozenMaterialQ_binding]

def operatingBackground (z : ℚ) (hz : 0 ≤ z) (hu : z ≤ 957 / 100000) :
    PeriodicScalarBackground where
  material := operatingMaterial z
  reserve := 12
  reserve_pos := by norm_num
  bounds := by
    intro c
    have hz' : (0 : ℝ) ≤ z := by exact_mod_cast hz
    have hmul : (100000 : ℚ) * z ≤ 957 := by linarith
    have hmul' : (100000 : ℝ) * (z : ℝ) ≤ 957 := by exact_mod_cast hmul
    have hu' : (z : ℝ) ≤ 957 / 100000 := by linarith
    have hl : (1 : ℝ) ≤ operatingMaterial z c := by
      rw [operatingMaterial_real]
      linarith [(Concrete.material_bounds c).1]
    have hh : (operatingMaterial z c : ℝ) ≤ 25 - 12 := by
      rw [operatingMaterial_real]
      exact (Concrete.material_headroom z hu' c).le
    exact ⟨by exact_mod_cast hl, by exact_mod_cast hh⟩

theorem operating_edge_shift (z : ℚ) (hz : 0 ≤ z) (hu : z ≤ 957 / 100000) (e : Edge) :
    periodicCoefficient (operatingBackground z hz hu).edgeMaterial e =
      periodicCoefficient (PeriodicYee.edgeAverage Concrete.material) e + 64 * (z : ℝ) := by
  simp only [periodicCoefficient, PeriodicScalarBackground.edgeMaterial,
    operatingBackground, PeriodicYee.edgeAverage, operatingMaterial_real]
  ring

theorem operating_operator (z : ℚ) (hz : 0 ≤ z) (hu : z ≤ 957 / 100000) :
    (operatingBackground z hz hu).operator = FiniteStencil.frozenOperator z := by
  rw [FiniteStencil.frozenOperator_binding]
  unfold PeriodicScalarBackground.operator electricOperator
  have hzcast : ((z : ℝ) : ℂ) = (z : ℂ) := by norm_cast
  ext x e
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, realSequenceMultiplier_apply,
    lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, operating_edge_shift, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul, hzcast]
  ring

theorem background_operator_norm (P : PeriodicScalarBackground) : ‖P.operator‖ ≤ 16 := by
  apply electricOperator_norm_le
  · intro e
    exact (by norm_num : (0 : ℝ) ≤ 1).trans
      ((PeriodicYee.edgeAverage_bounds (fun c => (P.material c : ℝ)) 1 25 P.material_bounds (edgeMod20 e)).1)
  · intro e
    exact (PeriodicYee.edgeAverage_bounds (fun c => (P.material c : ℝ)) 1 25 P.material_bounds (edgeMod20 e)).2

end
end Maxwell.Composition
