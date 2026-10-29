import Maxwell.Continuum.BoxModesOrthogonality
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Tensor-product integrals on the physical Euclidean box

The interval mode identities are lifted to the actual Lebesgue measure on
Euclidean three-space, using the measure-preserving coordinate equivalence.
The integration region is the open physical box, not a separate counting
space or an assumed product inner product.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open MeasureTheory
open scoped BigOperators

/-- The literal open rectangular box in physical Euclidean coordinates. -/
def openBox (N : Fin 3 → ℝ) : Set Point :=
  WithLp.ofLp ⁻¹' (Set.univ.pi fun j => Set.Ioo 0 (N j))

@[simp] theorem mem_openBox (N : Fin 3 → ℝ) (x : Point) :
    x ∈ openBox N ↔ ∀ j, 0 < x j ∧ x j < N j := by
  simp [openBox, Set.mem_pi]

/-- Fubini for separated scalar fields on the actual open Euclidean box. -/
theorem integral_openBox_product (N : Fin 3 → ℝ) (hN : ∀ j, 0 ≤ N j)
    (f : Fin 3 → ℝ → ℝ) :
    (∫ x in openBox N, ∏ j : Fin 3, f j (x j)) =
      ∏ j : Fin 3, ∫ t in (0 : ℝ)..N j, f j t := by
  let S : Set (Fin 3 → ℝ) := Set.univ.pi fun j => Set.Ioo 0 (N j)
  have he : MeasurableEmbedding (@WithLp.ofLp 2 (Fin 3 → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
  have hpres := (PiLp.volume_preserving_ofLp (Fin 3)).restrict_preimage_emb he S
  have h := hpres.integral_comp he (fun x : Fin 3 → ℝ => ∏ j, f j (x j))
  change (∫ x in openBox N, ∏ j, f j (x j)) =
    ∫ x in S, ∏ j, f j (x j) at h
  rw [h]
  change (∫ x, ∏ j, f j (x j)
    ∂((Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)).restrict S)) = _
  dsimp [S]
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [restrict_Ioo_eq_restrict_Ioc, intervalIntegral.integral_of_le (hN j)]

/-- Product inner products factor into the exact one-dimensional inner
products, without an integrability or orthogonality premise. -/
theorem integral_openBox_product_mul (N : Fin 3 → ℝ) (hN : ∀ j, 0 ≤ N j)
    (f g : Fin 3 → ℝ → ℝ) :
    (∫ x in openBox N, (∏ j : Fin 3, f j (x j)) * (∏ j : Fin 3, g j (x j))) =
      ∏ j : Fin 3, ∫ t in (0 : ℝ)..N j, f j t * g j t := by
  simp_rw [← Finset.prod_mul_distrib]
  exact integral_openBox_product N hN (fun j t => f j t * g j t)

/-- The cosine coordinate is the field component index; the other two
coordinates carry sine factors. -/
def coordinateMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3) (t : ℝ) : ℝ :=
  if j = c then intervalCos (N j) (ν j) t else intervalSin (N j) (ν j) t

def scalarBoxMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) (x : Point) : ℝ :=
  ∏ j : Fin 3, coordinateMode N ν c j (x j)

/-- The cosine index may be zero, whereas each sine index is positive. -/
def AdmissibleIndex (c : Fin 3) (ν : Fin 3 → ℤ) : Prop :=
  0 ≤ ν c ∧ ∀ j, j ≠ c → 0 < ν j

/-- The sole exceptional normalization factor is the constant cosine. -/
def coordinateSquareNorm (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3) : ℝ :=
  if j = c ∧ ν j = 0 then N j else N j / 2

theorem integral_coordinateMode_mul (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν μ : Fin 3 → ℤ) (c j : Fin 3)
    (hν : AdmissibleIndex c ν) (hμ : AdmissibleIndex c μ) :
    (∫ t in (0 : ℝ)..N j, coordinateMode N ν c j t * coordinateMode N μ c j t) =
      if ν j = μ j then coordinateSquareNorm N ν c j else 0 := by
  by_cases hj : j = c
  · subst j
    simpa [coordinateMode, coordinateSquareNorm] using
      integral_intervalCos_mul (N c) (hN c) (ν c) (μ c) hν.1 hμ.1
  · simpa [coordinateMode, coordinateSquareNorm, hj] using
      integral_intervalSin_mul (N j) (hN j) (ν j) (μ j) (hν.2 j hj) (hμ.2 j hj)

/-- Exact three-dimensional orthogonality and square norms, integrated over
the literal open physical box. -/
theorem integral_scalarBoxMode_mul (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν μ : Fin 3 → ℤ) (c : Fin 3)
    (hν : AdmissibleIndex c ν) (hμ : AdmissibleIndex c μ) :
    (∫ x in openBox N, scalarBoxMode N ν c x * scalarBoxMode N μ c x) =
      if ν = μ then ∏ j : Fin 3, coordinateSquareNorm N ν c j else 0 := by
  unfold scalarBoxMode
  rw [integral_openBox_product_mul N (fun j => (hN j).le)]
  simp_rw [integral_coordinateMode_mul N hN ν μ c _ hν hμ]
  by_cases h : ν = μ
  · subst μ
    simp
  · rw [ite_eq_right h]
    have hj : ∃ j : Fin 3, ν j ≠ μ j := by
      by_contra hj
      apply h
      funext j
      simp_all
    obtain ⟨j, hj⟩ := hj
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact ite_eq_right hj

/-- Every admissible component mode has positive square norm; zero cosine
indices do not create a spurious zero vector. -/
theorem scalarBoxMode_squareNorm_pos (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) :
    0 < ∏ j : Fin 3, coordinateSquareNorm N ν c j := by
  apply Finset.prod_pos
  intro j _
  unfold coordinateSquareNorm
  split_ifs
  · exact hN j
  · exact div_pos (hN j) (by norm_num)

/-- The generic normalization is one eighth of the box volume. -/
theorem scalarBoxMode_squareNorm_all_positive (N : Fin 3 → ℝ)
    (ν : Fin 3 → ℤ) (hν : ∀ j, 0 < ν j) (c : Fin 3) :
    (∏ j : Fin 3, coordinateSquareNorm N ν c j) = (∏ j : Fin 3, N j) / 8 := by
  have heq : ∀ j, coordinateSquareNorm N ν c j = N j / 2 := by
    intro j
    simp [coordinateSquareNorm, ne_of_gt (hν j)]
  simp_rw [heq]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  ring

/-- Binding to the component formulas used in the actual differential curl
calculation, rather than an independent trigonometric family. -/
theorem electric_component_eq_scalarBoxMode (N : ModeCount.BoxLengths)
    (ν : Fin 3 → ℕ) (a : Vector) (x : Point) (c : Fin 3) :
    electric (waveNumber N ν) a x c =
      a c * scalarBoxMode (fun j => (N j : ℝ)) (fun j => (ν j : ℤ)) c x := by
  have hs (j : Fin 3) : intervalSin (N j) (ν j) (x j) =
      Real.sin (waveNumber N ν j * x j) := by
    simp only [intervalSin, waveNumber, Int.cast_natCast]
    rw [mul_comm (ν j : ℝ) Real.pi]
  have hc (j : Fin 3) : intervalCos (N j) (ν j) (x j) =
      Real.cos (waveNumber N ν j * x j) := by
    simp only [intervalCos, waveNumber, Int.cast_natCast]
    rw [mul_comm (ν j : ℝ) Real.pi]
  fin_cases c <;>
    simp [electric, scalarBoxMode, coordinateMode, hs, hc, Fin.prod_univ_succ] <;> ring

#print axioms integral_openBox_product
#print axioms integral_scalarBoxMode_mul
#print axioms electric_component_eq_scalarBoxMode

end Maxwell.Continuum.BoxModes
