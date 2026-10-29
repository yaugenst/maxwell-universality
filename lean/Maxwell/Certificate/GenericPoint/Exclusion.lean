import Maxwell.Certificate.GenericPoint.Center
import Maxwell.Spectral.SeparatedInverse
import Maxwell.Spectral.YeeTaylorRemainder

/-! Spectral exclusion below the checked cluster center and inside its
punctured local neighborhood. Each inverse is constructed from actual
finite-dimensional eigenvalue separation. -/
namespace Maxwell.Certificate.GenericPoint.Data
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee Maxwell.Spectral.YeeTaylorRemainder
noncomputable section
variable (D : GenericPoint.Data)

def belowGap (E : ℝ) : ℝ := min (D.energy-E) (D.gap-|E-D.center 0|)

theorem belowGap_pos (E : ℝ) (hE : E < D.energy) (hc : |E-D.center 0| < D.gap) :
    0 < D.belowGap E := by
  exact lt_min (sub_pos.mpr hE) (sub_pos.mpr hc)

theorem center_below_gap (hgap : D.ComplementGap) (E : ℝ) (hE : E < D.energy)
    (i : Index) : D.belowGap E ≤ |(operator_symmetric D.k).eigenvalues rfl i-E| := by
  by_cases hi : i ∈ D.cluster
  · have hw := (D.cluster_window i hi).1
    have habs : 0 ≤ (operator_symmetric D.k).eigenvalues rfl i-E := by linarith
    rw [abs_of_nonneg habs]
    exact (min_le_left _ _).trans (by linarith)
  · have hg := hgap i hi 0
    have ht := abs_sub_le ((operator_symmetric D.k).eigenvalues rfl i) E (D.center 0)
    exact (min_le_right _ _).trans (by linarith)

theorem center_below_invertible (hgap : D.ComplementGap) (E : ℝ)
    (hE : E < D.energy) (hc : |E-D.center 0| < D.gap) :
    (D.continuousOperator-(E:ℂ) • 1).IsInvertible := by
  have hg : ∀ i, D.belowGap E ≤
      |D.continuousOperator_symmetric.eigenvalues rfl i-E| :=
    D.center_below_gap hgap E hE
  let B := SeparatedInverse.equiv D.continuousOperator D.continuousOperator_symmetric
    E (D.belowGap E) (D.belowGap_pos E hE hc) hg
  exact ⟨B,rfl⟩

def localGap (q : Momentum) (E : ℝ) : ℝ := min E (min (7/256-E) (YeeTaylor.radius q^2/600))

theorem localGap_pos (q : Momentum) (E : ℝ) (hr : 0 < YeeTaylor.radius q)
    (hE : 0 < E) (hEhi : E < 7/256) : 0 < localGap q E := by
  apply lt_min hE
  exact lt_min (sub_pos.mpr hEhi) (div_pos (sq_pos_of_pos hr) (by norm_num))

theorem local_below_gap (q : Momentum) (E : ℝ) (hE : E ≤ D.energy)
    (hE0 : 0 < E) (hEhi : E < 7/256)
    (hlocal : ∀ i : Index,
      0 < (centeredOperator_symmetric D.k q).eigenvalues rfl i →
      (centeredOperator_symmetric D.k q).eigenvalues rfl i < 7/256 →
      YeeTaylor.radius q^2/600 < (centeredOperator_symmetric D.k q).eigenvalues rfl i-D.energy)
    (i : Index) : localGap q E ≤ |(centeredOperator_symmetric D.k q).eigenvalues rfl i-E| := by
  let ev := (centeredOperator_symmetric D.k q).eigenvalues rfl i
  change localGap q E ≤ |ev-E|
  by_cases hlo : 0 < ev
  · by_cases hhi : ev < 7/256
    · have hl := hlocal i hlo hhi
      have hr : 0 ≤ YeeTaylor.radius q^2/600 := by positivity
      have he : 0 ≤ ev-E := by change _ < ev-D.energy at hl; linarith
      rw [abs_of_nonneg he]
      exact ((min_le_right _ _).trans (min_le_right _ _)).trans (by
        change _ < ev-D.energy at hl
        linarith)
    · have he : 0 ≤ ev-E := by linarith
      rw [abs_of_nonneg he]
      exact ((min_le_right _ _).trans (min_le_left _ _)).trans (by linarith)
  · have he : ev-E ≤ 0 := by linarith
    rw [abs_of_nonpos he]
    exact (min_le_left _ _).trans (by linarith)

theorem local_below_invertible (q : Momentum) (E : ℝ)
    (hr : 0 < YeeTaylor.radius q) (hE : E ≤ D.energy)
    (hE0 : 0 < E) (hEhi : E < 7/256)
    (hlocal : ∀ i : Index,
      0 < (centeredOperator_symmetric D.k q).eigenvalues rfl i →
      (centeredOperator_symmetric D.k q).eigenvalues rfl i < 7/256 →
      YeeTaylor.radius q^2/600 < (centeredOperator_symmetric D.k q).eigenvalues rfl i-D.energy) :
    (centeredOperator D.k q-(E:ℂ) • 1).IsInvertible := by
  let B := SeparatedInverse.equiv (centeredOperator D.k q) (centeredOperator_symmetric D.k q)
    E (localGap q E) (localGap_pos q E hr hE0 hEhi)
    (D.local_below_gap q E hE hE0 hEhi hlocal)
  exact ⟨B,rfl⟩

end
end Maxwell.Certificate.GenericPoint.Data
