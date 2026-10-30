import Maxwell.Continuum.CalibrationRawFreeEvaluation
import Maxwell.Continuum.CalibrationCoefficientEntries

/-! Unreduced alias coordinates and the complete free-block evaluator,
including the central identity blocks. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost RationalDataflow FreeFiber
set_option maxHeartbeats 2000000

def coordinatePart (R : ℕ) (i : Fin (aliasArraySize R)) (k : Fin 3) : Parts :=
  let a := ((aliasArrayEquiv R).symm i).1
  ⟨![a.1.val,a.2.1.val,a.2.2.val] k,R,1⟩

theorem coordinatePart_valid (R : ℕ) (i : Fin (aliasArraySize R)) (k : Fin 3) :
    (coordinatePart R i k).Valid := by simp only [coordinatePart,Parts.Valid]; omega

theorem coordinatePart_value (R : ℕ) (i : Fin (aliasArraySize R)) (k : Fin 3) :
    (coordinatePart R i k).value = (arrayAliasAt R i k : ℤ) := by
  simp only [coordinatePart,Parts.value,Nat.cast_one,div_one,arrayAliasAt,arrayAlias,
    Int.cast_sub,Int.cast_natCast]

theorem coordinatePart_width (R : ℕ) (i : Fin (aliasArraySize R)) (k : Fin 3) :
    (coordinatePart R i k).Width (R.bits.length+2) := by
  let a := ((aliasArrayEquiv R).symm i).1
  have hk : ![a.1.val,a.2.1.val,a.2.2.val] k ≤ 2*R := by
    have h0 := a.1.isLt
    have h1 := a.2.1.isLt
    have h2 := a.2.2.isLt
    unfold aliasSide at h0 h1 h2
    fin_cases k <;> norm_num <;> omega
  have hp := (RationalWords.bits_mono hk).trans (RationalAccumulator.bits_mul_le 2 R)
  have htwo : (2 : ℕ).bits.length = 2 := by decide
  rw [htwo] at hp
  exact ⟨by simpa only [coordinatePart,a] using hp.trans (by omega),by simp [coordinatePart],
    by norm_num [coordinatePart]⟩

def direction (c r : Fin 3 → Parts) (j : Fin 3) : Parts :=
  ((c j).add (Parts.literal (1/2))).add (r j)

theorem direction_valid (c r : Fin 3 → Parts)
    (hc : ∀ j, (c j).Valid) (hr : ∀ j, (r j).Valid) (j : Fin 3) :
    (direction c r j).Valid := Parts.add_valid
      (Parts.add_valid (hc j) (Parts.literal_valid _)) (hr j)

theorem direction_value (c r : Fin 3 → Parts) (ν : Alias)
    (hc : ∀ j, (c j).Valid) (hr : ∀ j, (r j).Valid)
    (hν : ∀ j, (c j).value = (ν j : ℚ)) (j : Fin 3) :
    (direction c r j).value = rationalDirection (fun j => (r j).value) ν j := by
  rw [direction,Parts.add_value _ _ (Parts.add_valid (hc j) (Parts.literal_valid _)) (hr j),
    Parts.add_value _ _ (hc j) (Parts.literal_valid _),Parts.literal_value,hν]
  rfl

theorem direction_width (c r : Fin 3 → Parts) (B : ℕ)
    (hc : ∀ j, (c j).Width B) (hr : ∀ j, (r j).Width B) (j : Fin 3) :
    (direction c r j).Width (2*B+4) := by
  have hhalf : (Parts.literal (1/2)).Width 2 := by
    norm_num [Parts.Width,Parts.literal]
    decide
  have h := ((hc j).add hhalf).add (hr j)
  convert h using 1 <;> first | rfl | omega

def freeEntry (t E : Parts) (r c : Fin 3 → Parts) (ν : Alias) (i j : Fin 3) : Parts :=
  if rationalCentralCheck ν then Parts.literal (if i=j then 1 else 0)
  else entry t E (direction c r) i j

theorem freeEntry_sound (t E : Parts) (r c : Fin 3 → Parts) (ν : Alias)
    (ht : t.Valid) (hE : E.Valid) (hr : ∀ j, (r j).Valid) (hc : ∀ j, (c j).Valid)
    (hcoord : ∀ j, (c j).value = (ν j : ℚ))
    (htbox : (3 : ℝ) ≤ t.value) (hEbox : (7 : ℝ) ≤ E.value ∧ (E.value : ℝ) ≤ 8)
    (hrbox : ∀ j, |((r j).value : ℝ)| ≤ 1/16) (i j : Fin 3) :
    (freeEntry t E r c ν i j).Valid ∧
      (freeEntry t E r c ν i j).value =
        rationalFreeInverseMatrix t.value E.value (fun j => (r j).value) ν i j := by
  by_cases hν : rationalCentralCheck ν = true
  · simp only [freeEntry,rationalFreeInverseMatrix,hν,ite_true,Matrix.one_apply,Parts.literal_value]
    exact ⟨Parts.literal_valid _,trivial⟩
  · have hnon : ¬IsCentralAlias ν := fun h => hν ((rationalCentralCheck_true ν).mpr h)
    simp only [freeEntry,hν]
    exact actual_entry t E (direction c r) (fun j => (r j).value) ν ht hE
      (direction_valid c r hc hr) (direction_value c r ν hc hr hcoord)
      htbox hEbox hrbox hnon i j

theorem freeEntry_width (t E : Parts) (r c : Fin 3 → Parts) (ν : Alias) (i j : Fin 3) (B : ℕ)
    (ht : t.Width B) (hE : E.Width B) (hr : ∀ j, (r j).Width B) (hc : ∀ j, (c j).Width B) :
    (freeEntry t E r c ν i j).Width (128*(B+3)) := by
  unfold freeEntry
  split_ifs
  · have h : (Parts.literal 1).Width 1 := by norm_num [Parts.Width,Parts.literal]
    exact h.mono (by omega)
  · have h : (Parts.literal 0).Width 1 := by norm_num [Parts.Width,Parts.literal]
    exact h.mono (by omega)
  · exact (entry_width t E (direction c r) i j (2*B+4) (ht.mono (by omega))
      (hE.mono (by omega)) (direction_width c r B hc hr)).mono (by omega)

#print axioms freeEntry_sound
#print axioms freeEntry_width

end Maxwell.Continuum.Calibration.RawFree
