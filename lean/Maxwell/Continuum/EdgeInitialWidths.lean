import Maxwell.Continuum.EdgeInitialBracket
import Maxwell.Continuum.EdgeIntegerBracket
import Maxwell.Continuum.NaturalSquareRootWidths
import Maxwell.Continuum.MachinData

/-! Fixed startup word bounds and linear precision bounds for the edge search. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate RationalWords

attribute [local irreducible] Elementary.piApprox sqrtNaturalCenter edgeRho edgeReference

theorem edgeRho_width : Width edgeRho 201 := by
  have h := (width_two.pow 100).inv (by positivity : (2 : ℚ)^100≠0)
  unfold edgeRho
  exact h

theorem edgeReference_width : Width edgeReference (2^63) := by
  have hpi := Machin.piApprox_word_bits 256
  have hp : Width (Elementary.piApprox 256).center (2^13*(256+1)^2) := ⟨hpi.1,hpi.2⟩
  have hs := sqrtNaturalCenter_width 19 256
  have h3 : Width (3 : ℚ) 2 := by constructor <;> decide
  have h4 : Width (4 : ℚ) 3 := by constructor <;> decide
  have h5 : Width (5 : ℚ) 3 := by constructor <;> decide
  have h6 : Width (6 : ℚ) 3 := by constructor <;> decide
  have h7 : Width (7 : ℚ) 3 := by constructor <;> decide
  have hfree := ((h3.mul (hp.pow 2)).mul (h4.inv (by norm_num))).sub h7
  have hpert := (edgeRho_width.mul (h5.add (width_two.mul hs))).mul (h6.inv (by norm_num))
  have h := hfree.add hpert
  simp only [← div_eq_mul_inv] at h
  unfold edgeReference
  exact h.mono (by norm_num)

theorem edgeInitial_endpoint_width : Width edgeInitial.lo (2^64) ∧ Width edgeInitial.hi (2^64) := by
  have hr := (width_two.pow 17).mul (edgeRho_width.pow 2)
  exact ⟨(edgeReference_width.sub hr).mono (by norm_num),
    (edgeReference_width.add hr).mono (by norm_num)⟩

theorem edgeInitialBrackets_endpoint_width (decideNegative : ℚ → ℕ → Bool) (k : ℕ) :
    Width (edgeBrackets decideNegative 182 edgeInitial k).lo (2^65+6*k+1) ∧
      Width (edgeBrackets decideNegative 182 edgeInitial k).hi (2^65+6*k+1) := by
  convert edgeBrackets_endpoint_width decideNegative 182 edgeInitial (2^64) k
    edgeInitial_endpoint_width.1 edgeInitial_endpoint_width.2 using 1

theorem edgeInitialBrackets_midpoint_width (decideNegative : ℚ → ℕ → Bool) (k : ℕ) :
    Width (edgeBrackets decideNegative 182 edgeInitial k).midpoint (2^66+12*k+5) := by
  have hends := edgeInitialBrackets_endpoint_width decideNegative k
  have h := (hends.1.add hends.2).mul (width_two.inv (by norm_num))
  rw [← div_eq_mul_inv] at h
  unfold Interval.midpoint
  convert h using 1
  norm_num
  omega

#print axioms edgeInitial_endpoint_width
#print axioms edgeInitialBrackets_midpoint_width

end Maxwell.Continuum.Calibration
