import Maxwell.Continuum.BlochAliasShift
import Maxwell.Continuum.PeriodicMaterial

/-! The physical cosine medium is exactly the bounded six-neighbor fiber potential. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory FourierTransform
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

theorem integerVector_neg (a : Alias) : integerVector (-a) = -integerVector a := by
  apply PiLp.ext
  intro i
  simp [integerVector]

theorem aliasFrequency_neg (a : Alias) : aliasFrequency (-a) = -aliasFrequency a := by
  simp only [aliasFrequency, integerVector_neg, smul_neg]

theorem integerVector_unitAlias (j : Fin 3) :
    integerVector (FreeFiber.unitAlias j) = coordinateDirection j := by
  apply PiLp.ext
  intro i
  by_cases h : i = j <;>
    simp [integerVector, FreeFiber.unitAlias, coordinateDirection, Pi.single_apply, h]

theorem inner_aliasFrequency_unitAlias (x : Space) (j : Fin 3) :
    inner ℝ x (aliasFrequency (FreeFiber.unitAlias j)) = x j / 2 := by
  rw [aliasFrequency, integerVector_unitAlias, inner_smul_right]
  simp [coordinateDirection, EuclideanSpace.inner_single_right, div_eq_mul_inv, mul_comm]

theorem phase_pair_cosine (x : Space) (j : Fin 3) :
    phase (aliasFrequency (FreeFiber.unitAlias j)) x +
      phase (aliasFrequency (-FreeFiber.unitAlias j)) x =
        2 * (Real.cos (Real.pi * x j) : ℂ) := by
  simp only [phase, aliasFrequency_neg, inner_neg_right, inner_aliasFrequency_unitAlias,
    Real.fourierChar_apply]
  have h : 2 * Real.pi * (x j / 2) = Real.pi * x j := by ring
  have hn : 2 * Real.pi * -(x j / 2) = -(Real.pi * x j) := by ring
  rw [h, hn, Complex.ofReal_neg, ← Complex.two_cos, Complex.ofReal_cos]

def physicalPotential : FieldL2 →L[ℂ] FieldL2 :=
  ∑ j : Fin 3, (FreeFiber.potentialWeight j : ℂ) •
    (fieldModulation (aliasFrequency (FreeFiber.unitAlias j)) +
      fieldModulation (aliasFrequency (-FreeFiber.unitAlias j)))

def potentialL2 : FiberL2 →L[ℂ] FiberL2 := FreeFiber.potential.compLpL 2 quasiMeasure

theorem potentialL2_ae (w : FiberL2) :
    potentialL2 w =ᵐ[quasiMeasure] (fun q => FreeFiber.potential (w q)) :=
  FreeFiber.potential.coeFn_compLpL w

theorem unitary_physicalPotential (u : FieldL2) :
    unitary (physicalPotential u) = potentialL2 (unitary u) := by
  simp only [physicalPotential, sum_apply, smul_apply,
    add_apply, map_sum, map_smul, map_add, unitary_fieldModulation,
    neg_neg]
  apply Lp.ext
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun j : Fin 3 =>
    (FreeFiber.potentialWeight j : ℂ) •
      (aliasShiftL2 (-FreeFiber.unitAlias j) (unitary u) +
        aliasShiftL2 (FreeFiber.unitAlias j) (unitary u)))
  have hj := ae_all_iff.mpr (fun j : Fin 3 =>
    (Lp.coeFn_smul (FreeFiber.potentialWeight j : ℂ)
      (aliasShiftL2 (-FreeFiber.unitAlias j) (unitary u) +
        aliasShiftL2 (FreeFiber.unitAlias j) (unitary u))).and
      ((Lp.coeFn_add (aliasShiftL2 (-FreeFiber.unitAlias j) (unitary u))
        (aliasShiftL2 (FreeFiber.unitAlias j) (unitary u))).and
        ((aliasShiftL2_ae (-FreeFiber.unitAlias j) (unitary u)).and
          (aliasShiftL2_ae (FreeFiber.unitAlias j) (unitary u)))))
  filter_upwards [hsum, hj, potentialL2_ae (unitary u)] with q hsum hj hp
  rw [hsum, hp]
  change (∑ j : Fin 3, ((FreeFiber.potentialWeight j : ℂ) •
    (aliasShiftL2 (-FreeFiber.unitAlias j) (unitary u) +
      aliasShiftL2 (FreeFiber.unitAlias j) (unitary u)) : FiberL2) q) = _
  simp only [FreeFiber.potential, sum_apply, smul_apply, add_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [(hj j).1]
  change (FreeFiber.potentialWeight j : ℂ) •
    (aliasShiftL2 (-FreeFiber.unitAlias j) (unitary u) +
      aliasShiftL2 (FreeFiber.unitAlias j) (unitary u)) q = _
  rw [(hj j).2.1]
  simp only [Pi.add_apply, (hj j).2.2.1, (hj j).2.2.2, add_comm]

end Maxwell.Continuum.Bloch
