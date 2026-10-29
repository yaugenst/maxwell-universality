import Maxwell.Probability
import Maxwell.Target
import Maxwell.TargetNorm

/-! Uniform finite detuning of an actual scalar-cell Maxwell instance.
The only material precondition is a certified positive headroom interval;
the constructor emits a valid material for every index in the finite grid. -/

namespace Maxwell.Probability
noncomputable section
open scoped Classical Matrix.Norms.L2Operator
open Maxwell.Target

local instance {n : ℕ} (I : Instance n) : Fintype I.box.Edge := inferInstance
local instance {n : ℕ} (I : Instance n) : DecidableEq I.box.Edge := inferInstance

/-- Reserved upper scalar-cell headroom, measured in frequency shift units. -/
structure MaterialHeadroom {n : ℕ} (I : Instance n) where
  width : ℚ
  positive : 0 < width
  upper : ∀ c, I.material.value c + 64 * width ≤ 25

/-- Rational arithmetic used by the actual emitted scalar cells. -/
def rationalMidpoint (τ : ℚ) (J j : ℕ) : ℚ := ((j : ℚ) + 1 / 2) * τ / J

@[simp] theorem rationalMidpoint_cast (τ : ℚ) (J j : ℕ) :
    (rationalMidpoint τ J j : ℝ) = midpoint (τ : ℝ) J j := by
  simp [rationalMidpoint, midpoint]

theorem rationalMidpoint_mem (τ : ℚ) (J : ℕ) (j : Fin J) (hτ : 0 < τ) :
    0 < rationalMidpoint τ J j.val ∧ rationalMidpoint τ J j.val < τ := by
  have h := midpoint_mem (τ : ℝ) J j.val (by exact_mod_cast hτ) j.isLt
  rw [← rationalMidpoint_cast] at h
  exact_mod_cast h

/-- Every draw satisfies the physical scalar material interval. -/
def shiftedMaterial {n : ℕ} (I : Instance n) (H : MaterialHeadroom I)
    (J : ℕ) (j : Fin J) : ScalarMaterial I.box.nx I.box.ny I.box.nz where
  value c := I.material.value c + 64 * rationalMidpoint H.width J j.val
  bounds c := by
    have hm := I.material.bounds c
    have hσ := rationalMidpoint_mem H.width J j H.positive
    have hh := H.upper c
    constructor <;> linarith

/-- The emitted instance uses the original geometry, source, tolerance, and
finite decoder, and writes the uniformly shifted value of every scalar cell. -/
def shiftedInstance {n : ℕ} (I : Instance n) (H : MaterialHeadroom I)
    (J : ℕ) (j : Fin J) : Instance n :=
  { I with material := shiftedMaterial I H J j }

@[simp] theorem shiftedInstance_dimension {n : ℕ} (I : Instance n)
    (H : MaterialHeadroom I) (J : ℕ) (j : Fin J) :
    (shiftedInstance I H J j).dimension = I.dimension := rfl

@[simp] theorem shiftedInstance_cellCount {n : ℕ} (I : Instance n)
    (H : MaterialHeadroom I) (J : ℕ) (j : Fin J) :
    (shiftedInstance I H J j).cellCount = I.cellCount := rfl

/-- Exact equality of complete finite matrices, including every PEC edge. -/
theorem shiftedInstance_realMatrix {n : ℕ} (I : Instance n)
    (H : MaterialHeadroom I) (J : ℕ) (j : Fin J) :
    (shiftedInstance I H J j).realMatrix =
      I.realMatrix - midpoint (H.width : ℝ) J j.val •
        (1 : Matrix I.box.Edge I.box.Edge ℝ) := by
  have h := operator_uniform_shift I.box I.material.value
    (rationalMidpoint H.width J j.val)
  change (operator I.box (fun c => I.material.value c +
      64 * rationalMidpoint H.width J j.val)).map (fun q => (q : ℝ)) = _
  rw [h]
  ext e f
  simp [Instance.realMatrix, maxwell, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem instance_realMatrix_hermitian {n : ℕ} (I : Instance n) :
    I.realMatrix.IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  exact (maxwell_symmetric I.material).map (fun q => (q : ℝ))

/-- Norm bound holds on all draws, without any spectral good-event premise. -/
theorem shiftedInstance_norm {n : ℕ} (I : Instance n)
    (H : MaterialHeadroom I) (J : ℕ) (j : Fin J) :
    ‖(shiftedInstance I H J j).realMatrix‖ ≤ 16 :=
  maxwell_real_toEuclideanCLM_norm_le (shiftedMaterial I H J j)

theorem instance_condition_of_inverseBound {n : ℕ} (I : Instance n)
    (L : ℝ) (h : InverseBound I.realMatrix L) :
    IsUnit I.realMatrix ∧ condition₂ I.realMatrix ≤ 16 * L := by
  obtain ⟨B, hAB, hBA, hBnorm⟩ := h
  have hunit : IsUnit I.realMatrix := ⟨⟨I.realMatrix, B, hAB, hBA⟩, rfl⟩
  refine ⟨hunit, ?_⟩
  have hnorm := maxwell_real_toEuclideanCLM_norm_le I.material
  have hinv : ‖I.realMatrix⁻¹‖ ≤ L := by
    rw [Matrix.inv_eq_left_inv hBA]
    exact hBnorm
  change ‖I.realMatrix‖ * ‖I.realMatrix⁻¹‖ ≤ 16 * L
  exact mul_le_mul hnorm hinv (norm_nonneg _) (by norm_num)

/-- The actual physical bad event, not a supplied good-event hypothesis. -/
def physicalBad {n : ℕ} (I : Instance n) (H : MaterialHeadroom I)
    (J m : ℕ) : Finset ℕ :=
  (Finset.range J).filter fun j =>
    ∃ hj : j < J, ¬ InverseBound (shiftedInstance I H J ⟨j, hj⟩).realMatrix
      (inverseBudget m I.dimension H.width)

theorem physical_good_inverseBound {n : ℕ} (I : Instance n) (H : MaterialHeadroom I)
    (J m : ℕ) (j : Fin J) (hj : j.val ∉ physicalBad I H J m) :
    InverseBound (shiftedInstance I H J j).realMatrix
      (inverseBudget m I.dimension H.width) := by
  by_contra hn
  exact hj (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, ⟨j.isLt, hn⟩⟩)

/-- The complete list has exactly the actual number of retained field edges. -/
def instanceEigenvalues {n : ℕ} (I : Instance n) : Fin I.dimension → ℝ :=
  fun i => (instance_realMatrix_hermitian I).eigenvalues
    ((Fintype.equivFin I.box.Edge).symm i)

theorem physicalBad_subset {n : ℕ} (I : Instance n) (H : MaterialHeadroom I)
    (J m : ℕ) (hm : 0 < m) :
    physicalBad I H J m ⊆
      spectralBad (instanceEigenvalues I) H.width (detuningRadius m I.dimension H.width) J := by
  intro j hj
  obtain ⟨hjrange, hjbad⟩ := Finset.mem_filter.mp hj
  obtain ⟨hjJ, hjbad⟩ := hjbad
  apply (mem_spectralBad _ _ _ _ _).mpr
  refine ⟨hjJ, ?_⟩
  by_contra hnone
  push Not at hnone
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hwidth : (0 : ℝ) < H.width := by exact_mod_cast H.positive
  have hL : 0 < inverseBudget m I.dimension H.width := by
    dsimp [inverseBudget]; positivity
  apply hjbad
  rw [shiftedInstance_realMatrix]
  apply shifted_inverseBound (instance_realMatrix_hermitian I) _ _ hL
  intro e
  have he := hnone ((Fintype.equivFin I.box.Edge) e)
  simpa only [instanceEigenvalues, Equiv.symm_apply_apply,
    detuningRadius_eq_inverseBudget_inv] using he

/-- Detuning theorem for the actual emitted Maxwell family. Material
validity, matrix dimension, and the norm bound hold on every draw. -/
theorem physical_detuning {n : ℕ} (I : Instance n) (H : MaterialHeadroom I)
    (m J : ℕ) (hm : 0 < m) (hgrid : 16 * (m + I.dimension)^2 ≤ J) :
    ∃ hJ : 0 < J,
      gridProbability J hJ (physicalBad I H J m) ≤ 3 / (64 * (m : ℝ)) ∧
      ∀ j : Fin J, j.val ∉ physicalBad I H J m →
        IsUnit (shiftedInstance I H J j).realMatrix ∧
          condition₂ (shiftedInstance I H J j).realMatrix ≤
            16 * inverseBudget m I.dimension H.width := by
  have hwidth : (0 : ℝ) < H.width := by exact_mod_cast H.positive
  obtain ⟨hJ, hprob, hsmall⟩ := finite_detuning_probability
    (instanceEigenvalues I) m J H.width hm hwidth hgrid
  refine ⟨hJ, ?_, ?_⟩
  · exact ((gridProbability_mono J hJ (physicalBad_subset I H J m hm)
      (spectralBad_subset _ _ _ _)).trans hprob).trans hsmall
  · intro j hj
    exact instance_condition_of_inverseBound _ _ (physical_good_inverseBound I H J m j hj)

/-- The encoder may use the explicit power-of-two grid without a further
size-choice premise. Every sample uses exactly `detuningBits` fair bits. -/
theorem physical_detuning_dyadic_grid {n : ℕ} (I : Instance n) (H : MaterialHeadroom I)
    (m : ℕ) (hm : 0 < m) :
    ∃ hJ : 0 < detuningGridSize m I.dimension,
      gridProbability (detuningGridSize m I.dimension) hJ
        (physicalBad I H (detuningGridSize m I.dimension) m) ≤ 3 / (64 * (m : ℝ)) ∧
      ∀ j : Fin (detuningGridSize m I.dimension),
        j.val ∉ physicalBad I H (detuningGridSize m I.dimension) m →
          IsUnit (shiftedInstance I H (detuningGridSize m I.dimension) j).realMatrix ∧
            condition₂ (shiftedInstance I H (detuningGridSize m I.dimension) j).realMatrix ≤
              16 * inverseBudget m I.dimension H.width :=
  physical_detuning I H m _ hm (detuningGridSize_sufficient m I.dimension)

@[simp] theorem shiftedInstance_source {n : ℕ} (I : Instance n)
    (H : MaterialHeadroom I) (J : ℕ) (j : Fin J) :
    (shiftedInstance I H J j).source = I.source := rfl

@[simp] theorem shiftedInstance_tolerance {n : ℕ} (I : Instance n)
    (H : MaterialHeadroom I) (J : ℕ) (j : Fin J) :
    (shiftedInstance I H J j).tolerance = I.tolerance := rfl

@[simp] theorem shiftedInstance_decoder {n : ℕ} (I : Instance n)
    (H : MaterialHeadroom I) (J : ℕ) (j : Fin J) :
    (shiftedInstance I H J j).decoder = I.decoder := rfl

/-- Dyadic input cells and dyadic detuning width produce dyadic output
cells with an explicit common denominator on every draw. -/
theorem shiftedMaterial_dyadic {n : ℕ} (I : Instance n) (H : MaterialHeadroom I)
    (p q bits : ℕ) (a : ℤ) (b : I.box.Cell → ℤ)
    (hwidth : H.width = (a : ℚ) / 2^p)
    (hbase : ∀ c, I.material.value c = (b c : ℚ) / 2^q)
    (j : Fin (2^bits)) (c : I.box.Cell) :
    (shiftedMaterial I H (2^bits) j).value c =
      (((b c * 2^(p + bits + 1) + 64 * ((2 * (j.val : ℤ) + 1) * a) * 2^q : ℤ)) : ℚ) /
        2^(q + p + bits + 1) := by
  simp only [shiftedMaterial, hbase, rationalMidpoint, hwidth, Int.cast_add,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_one, Int.cast_natCast,
    Nat.cast_pow, Nat.cast_ofNat, pow_add]
  field_simp


end
end Maxwell.Probability
