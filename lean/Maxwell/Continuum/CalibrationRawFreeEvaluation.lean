import Maxwell.Continuum.CalibrationRationalFree
import Maxwell.Continuum.RationalDataflowParts

/-! Literal unreduced rational arithmetic for a free inverse block.  Its
two reciprocals have nonzero denominators on the actual calibration box. -/

namespace Maxwell.Continuum.Calibration.RawFree

open RationalDataflow FreeFiber
set_option maxHeartbeats 2000000

def squareSum (a : Fin 3 → Parts) : Parts :=
  ((a 0).mul (a 0)).add ((a 1).mul (a 1)) |>.add ((a 2).mul (a 2))

def denominator (t E : Parts) (a : Fin 3 → Parts) : Parts :=
  ((t.mul t).mul (squareSum a)).sub E

def numerator (t E : Parts) (a : Fin 3 → Parts) (i j : Fin 3) : Parts :=
  (Parts.literal (if i=j then 1 else 0)).sub
    (E.inverse.mul ((t.mul (a i)).mul (t.mul (a j))))

def entry (t E : Parts) (a : Fin 3 → Parts) (i j : Fin 3) : Parts :=
  (denominator t E a).inverse.mul (numerator t E a i j)

theorem squareSum_valid (a : Fin 3 → Parts) (ha : ∀ j, (a j).Valid) :
    (squareSum a).Valid :=
  Parts.add_valid (Parts.add_valid (Parts.mul_valid (ha 0) (ha 0))
    (Parts.mul_valid (ha 1) (ha 1))) (Parts.mul_valid (ha 2) (ha 2))

theorem squareSum_value (a : Fin 3 → Parts) (ha : ∀ j, (a j).Valid) :
    (squareSum a).value = ∑ j : Fin 3, (a j).value^2 := by
  rw [squareSum,Parts.add_value _ _
    (Parts.add_valid (Parts.mul_valid (ha 0) (ha 0)) (Parts.mul_valid (ha 1) (ha 1)))
    (Parts.mul_valid (ha 2) (ha 2)),Parts.add_value _ _ (Parts.mul_valid (ha 0) (ha 0))
    (Parts.mul_valid (ha 1) (ha 1))]
  simp only [Parts.mul_value,Fin.sum_univ_three,pow_two]

theorem denominator_valid (t E : Parts) (a : Fin 3 → Parts)
    (ht : t.Valid) (hE : E.Valid) (ha : ∀ j, (a j).Valid) :
    (denominator t E a).Valid :=
  Parts.sub_valid (Parts.mul_valid (Parts.mul_valid ht ht) (squareSum_valid a ha)) hE

theorem denominator_value (t E : Parts) (a : Fin 3 → Parts)
    (ht : t.Valid) (hE : E.Valid) (ha : ∀ j, (a j).Valid) :
    (denominator t E a).value = t.value^2*(∑ j, (a j).value^2)-E.value := by
  rw [denominator,Parts.sub_value _ _
    (Parts.mul_valid (Parts.mul_valid ht ht) (squareSum_valid a ha)) hE]
  simp only [Parts.mul_value,squareSum_value a ha,pow_two]

theorem numerator_valid (t E : Parts) (a : Fin 3 → Parts) (i j : Fin 3)
    (ht : t.Valid) (hE : E.value ≠ 0) (ha : ∀ j, (a j).Valid) :
    (numerator t E a i j).Valid :=
  Parts.sub_valid (Parts.literal_valid _) (Parts.mul_valid (Parts.inverse_valid hE)
    (Parts.mul_valid (Parts.mul_valid ht (ha i)) (Parts.mul_valid ht (ha j))))

theorem entry_valid (t E : Parts) (a : Fin 3 → Parts) (i j : Fin 3)
    (ht : t.Valid) (hE : E.value ≠ 0) (ha : ∀ j, (a j).Valid)
    (hd : (denominator t E a).value ≠ 0) : (entry t E a i j).Valid :=
  Parts.mul_valid (Parts.inverse_valid hd) (numerator_valid t E a i j ht hE ha)

theorem entry_value (t E : Parts) (a : Fin 3 → Parts) (i j : Fin 3)
    (ht : t.Valid) (hE : E.Valid) (ha : ∀ j, (a j).Valid)
    (hEn : E.value ≠ 0) (hd : (denominator t E a).value ≠ 0) :
    (entry t E a i j).value = rationalInverseMatrix t.value E.value (fun j => (a j).value) i j := by
  rw [entry,Parts.mul_value,Parts.inverse_value _ (denominator_valid t E a ht hE ha) hd,
    denominator_value t E a ht hE ha]
  rw [numerator,Parts.sub_value _ _ (Parts.literal_valid _)
    (Parts.mul_valid (Parts.inverse_valid hEn)
      (Parts.mul_valid (Parts.mul_valid ht (ha i)) (Parts.mul_valid ht (ha j))))]
  simp only [Parts.literal_value,Parts.mul_value,Parts.inverse_value E hE hEn,
    rationalInverseMatrix,Matrix.smul_apply,Matrix.sub_apply,Matrix.one_apply,
    Matrix.vecMulVec_apply,smul_eq_mul]

theorem squareSum_width (a : Fin 3 → Parts) (B : ℕ) (ha : ∀ j, (a j).Width B) :
    (squareSum a).Width (6*B+5) := by
  have h := (((ha 0).mul (ha 0)).add ((ha 1).mul (ha 1))).add ((ha 2).mul (ha 2))
  convert h using 1 <;> first | rfl | omega

theorem denominator_width (t E : Parts) (a : Fin 3 → Parts) (B : ℕ)
    (ht : t.Width B) (hE : E.Width B) (ha : ∀ j, (a j).Width B) :
    (denominator t E a).Width (9*B+8) := by
  have h := ((ht.mul ht).mul (squareSum_width a B ha)).sub hE
  convert h using 1 <;> first | rfl | omega

theorem numerator_width (t E : Parts) (a : Fin 3 → Parts) (i j : Fin 3) (B : ℕ)
    (ht : t.Width B) (hE : E.Width B) (ha : ∀ j, (a j).Width B) :
    (numerator t E a i j).Width (5*B+7) := by
  have hδ : (Parts.literal (if i=j then 1 else 0)).Width 1 := by
    split_ifs <;> norm_num [Parts.Width,Parts.literal]
  have h := hδ.sub (hE.inverse.mul ((ht.mul (ha i)).mul (ht.mul (ha j))))
  convert h using 1 <;> first | rfl | omega

theorem entry_width (t E : Parts) (a : Fin 3 → Parts) (i j : Fin 3) (B : ℕ)
    (ht : t.Width B) (hE : E.Width B) (ha : ∀ j, (a j).Width B) :
    (entry t E a i j).Width (14*B+17) := by
  have h := (denominator_width t E a B ht hE ha).inverse.mul
    (numerator_width t E a i j B ht hE ha)
  convert h using 1 <;> first | rfl | omega

theorem actual_denominator_pos (t E : ℚ) (r : Fin 3 → ℚ) (ν : Alias)
    (ht : (3 : ℝ) ≤ t) (hE : (E : ℝ) ≤ 8)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (hν : ¬IsCentralAlias ν) :
    0 < t^2*(∑ j, (rationalDirection r ν j)^2)-E := by
  have hg := gridDirection_noncentral (fun j => (r j : ℝ)) hr ν hν
  have hd : ((∑ j, (rationalDirection r ν j)^2 : ℚ) : ℝ) =
      directionSquare (gridDirection (fun j => (r j : ℝ)) ν) := by
    simp only [Rat.cast_sum,Rat.cast_pow,← rationalDirection_cast r ν,directionSquare]
  have ht2 : (9 : ℝ) ≤ (t : ℝ)^2 := by nlinarith
  have hprod := mul_le_mul ht2 hg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (t : ℝ))
  have hreal : (0 : ℝ) < (t : ℝ)^2*
      ((∑ j, (rationalDirection r ν j)^2 : ℚ) : ℝ)-(E : ℝ) := by rw [hd]; linarith
  exact_mod_cast hreal

/-- The raw free entry equals the literal continuum calibration block.
The analytic calibration-box bounds discharge both reciprocal contracts. -/
theorem actual_entry (t E : Parts) (a : Fin 3 → Parts) (r : Fin 3 → ℚ) (ν : Alias)
    (ht : t.Valid) (hE : E.Valid) (ha : ∀ j, (a j).Valid)
    (hadir : ∀ j, (a j).value = rationalDirection r ν j)
    (htbox : (3 : ℝ) ≤ t.value) (hEbox : (7 : ℝ) ≤ E.value ∧ (E.value : ℝ) ≤ 8)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (hν : ¬IsCentralAlias ν) (i j : Fin 3) :
    (entry t E a i j).Valid ∧
    (entry t E a i j).value = rationalFreeInverseMatrix t.value E.value r ν i j := by
  have hEn : E.value ≠ 0 := by
    intro hzero
    have h := hEbox.1
    rw [hzero,Rat.cast_zero] at h
    norm_num at h
  have hd : (denominator t E a).value ≠ 0 := by
    rw [denominator_value t E a ht hE ha]
    simp_rw [hadir]
    exact (actual_denominator_pos t.value E.value r ν htbox hEbox.2 hr hν).ne'
  refine ⟨entry_valid t E a i j ht hEn ha hd,?_⟩
  have hb : rationalCentralCheck ν = false := Bool.eq_false_iff.mpr
    (fun h => hν ((rationalCentralCheck_true ν).mp h))
  simp only [rationalFreeInverseMatrix,hb,Bool.false_eq_true,ite_false]
  rw [entry_value t E a i j ht hE ha hEn hd]
  congr 2
  funext k
  exact hadir k

#print axioms actual_entry
#print axioms entry_width

end Maxwell.Continuum.Calibration.RawFree
