import Maxwell.Continuum.CutoffRawIntegration
import Maxwell.Continuum.CutoffEvaluationWidths

/-! Complete cutoff evaluation with polynomially bounded unreduced words. -/

namespace Maxwell.Continuum.Calibration.RawCutoff

open RationalDataflow

attribute [local irreducible] integral integralWidth cutoffIntegralApprox

def clamp (x : Parts) : Parts :=
  if (1/2 : ℚ)<x.value then Parts.literal (1/2)
  else if x.value<(-1/2 : ℚ) then Parts.literal (-1/2) else x

theorem clamp_valid (x : Parts) (hx : x.Valid) : (clamp x).Valid := by
  unfold clamp
  split_ifs <;> first | exact Parts.literal_valid _ | exact hx

theorem clamp_value (x : Parts) : (clamp x).value=cutoffClampRat x.value := by
  unfold clamp cutoffClampRat
  split_ifs with hh hl
  · rw [Parts.literal_value,min_eq_left hh.le,max_eq_right (by norm_num : (-1/2 : ℚ)≤1/2)]
  · rw [Parts.literal_value,min_eq_right (le_of_not_gt hh),max_eq_left hl.le]
  · rw [min_eq_right (le_of_not_gt hh),max_eq_right (le_of_not_gt hl)]

theorem clamp_width {x : Parts} {W : ℕ} (hx : x.Width W) : (clamp x).Width (W+2) := by
  have hp := Parts.literal_width cutoff_half_width
  have hm : (Parts.literal (-1/2)).Width 2 :=
    Parts.literal_width (by simpa only [neg_div] using cutoff_half_width.neg)
  unfold clamp
  split_ifs
  · exact hp.mono (by omega)
  · exact hm.mono (by omega)
  · exact hx.mono (by omega)

def denominator (N : ℕ) : Parts := integral N (Parts.literal (-1/2)) (Parts.literal (1/2))
def numerator (x : Parts) (N : ℕ) : Parts :=
  integral N (clamp (x.sub (Parts.literal (3/2)))) (clamp (x.add (Parts.literal (3/2))))
def psi (x : Parts) (N : ℕ) : Parts := (numerator x N).mul (denominator N).inverse
def chi (x : Fin 3 → Parts) (N : ℕ) : Parts := ((psi (x 0) N).mul (psi (x 1) N)).mul (psi (x 2) N)

attribute [local irreducible] denominator numerator psi

theorem denominator_valid (N : ℕ) : (denominator N).Valid := by
  unfold denominator
  exact integral_valid _ _ _ (Parts.literal_valid _) (Parts.literal_valid _)

theorem denominator_value (N : ℕ) : (denominator N).value=cutoffDenominatorApprox N := by
  unfold denominator
  rw [integral_value _ _ _ (Parts.literal_valid _) (Parts.literal_valid _)]
  simp only [Parts.literal_value,cutoffDenominatorApprox]

theorem denominator_nonzero (N : ℕ) : (denominator N).value≠0 := by
  rw [denominator_value]
  have h := cutoffDenominatorApprox_lower N
  linarith

theorem numerator_valid (x : Parts) (hx : x.Valid) (N : ℕ) : (numerator x N).Valid := by
  unfold numerator
  exact integral_valid _ _ _ (clamp_valid _ (Parts.sub_valid hx (Parts.literal_valid _)))
    (clamp_valid _ (Parts.add_valid hx (Parts.literal_valid _)))

theorem numerator_value (x : Parts) (hx : x.Valid) (N : ℕ) :
    (numerator x N).value=psiNumeratorApprox x.value N := by
  unfold numerator
  rw [integral_value _ _ _ (clamp_valid _ (Parts.sub_valid hx (Parts.literal_valid _)))
    (clamp_valid _ (Parts.add_valid hx (Parts.literal_valid _)))]
  simp only [clamp_value,Parts.sub_value _ _ hx (Parts.literal_valid _),
    Parts.add_value _ _ hx (Parts.literal_valid _),Parts.literal_value,psiNumeratorApprox]

theorem psi_valid (x : Parts) (hx : x.Valid) (N : ℕ) : (psi x N).Valid := by
  unfold psi
  exact Parts.mul_valid (numerator_valid x hx N) (Parts.inverse_valid (denominator_nonzero N))

theorem psi_value (x : Parts) (hx : x.Valid) (N : ℕ) : (psi x N).value=psiCenter x.value N := by
  unfold psi
  rw [Parts.mul_value,numerator_value x hx N,
    Parts.inverse_value _ (denominator_valid N) (denominator_nonzero N),denominator_value]
  rfl

theorem chi_valid (x : Fin 3 → Parts) (hx : ∀ i, (x i).Valid) (N : ℕ) : (chi x N).Valid :=
  Parts.mul_valid (Parts.mul_valid (psi_valid _ (hx 0) N) (psi_valid _ (hx 1) N))
    (psi_valid _ (hx 2) N)

theorem chi_value (x : Fin 3 → Parts) (hx : ∀ i, (x i).Valid) (N : ℕ) :
    (chi x N).value=chiCenter (fun i => (x i).value) N := by
  simp only [chi,Parts.mul_value,psi_value _ (hx _) N,chiCenter,Fin.prod_univ_three]

theorem integralWidth_mono (N : ℕ) {V W : ℕ} (h : V≤W) : integralWidth N V ≤ integralWidth N W := by
  unfold integralWidth
  gcongr

theorem denominator_width (N : ℕ) : (denominator N).Width (integralWidth N 2) := by
  unfold denominator
  exact integral_width N
    (Parts.literal_width (by simpa only [neg_div] using cutoff_half_width.neg))
    (Parts.literal_width cutoff_half_width)

theorem numerator_width {x : Parts} {W : ℕ} (hx : x.Width W) (N : ℕ) :
    (numerator x N).Width (integralWidth N (W+6)) := by
  have hh : (Parts.literal (3/2)).Width 3 := by
    apply Parts.literal_width
    have h := RationalWords.width_fraction (z := 3) (d := 2) (B := 3) (by decide) (by decide) (by decide)
    simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h
  unfold numerator
  exact integral_width N (clamp_width (hx.sub hh)) (clamp_width (hx.add hh))

theorem psi_width {x : Parts} {W : ℕ} (hx : x.Width W) (N : ℕ) :
    (psi x N).Width (2*integralWidth N (W+6)+2) := by
  have h := (numerator_width hx N).mul (denominator_width N).inverse
  unfold psi
  exact h.mono (by have := integralWidth_mono N (show 2≤W+6 by omega); omega)

theorem chi_width {x : Fin 3 → Parts} {W : ℕ} (hx : ∀ i, (x i).Width W) (N : ℕ) :
    (chi x N).Width (6*integralWidth N (W+6)+8) := by
  have h := ((psi_width (hx 0) N).mul (psi_width (hx 1) N)).mul (psi_width (hx 2) N)
  unfold chi
  convert h using 1
  ring

theorem chi_width_polynomial {x : Fin 3 → Parts} {W : ℕ} (hx : ∀ i, (x i).Width W) (N : ℕ) :
    (chi x N).Width (2^107*(N+1)^6*(W+7)) := by
  apply (chi_width hx N).mono
  have h := Nat.mul_le_mul_left 6 (integralWidth_polynomial N (W+6))
  have hpos : 1≤(N+1)^6*(W+7) := Nat.succ_le_of_lt (by positivity)
  nlinarith only [h,hpos]

#print axioms chi_value
#print axioms chi_width_polynomial

end Maxwell.Continuum.Calibration.RawCutoff
