import Maxwell.Cost.SourceCircuit.ArithmeticFull

namespace Maxwell.Cost.SourceCircuit.ArithmeticPass

def coordinateBits {n : ℕ} (records : List (AllocationPass.Record n)) : ℕ :=
  (records.map fun r => r.row.bits.length+r.column.val.bits.length).sum

theorem recordCosts_eq {n : ℕ} (precision width : ℕ) (records : List (AllocationPass.Record n)) :
    recordCosts precision width records =
      40*coordinateBits records+records.length*(precision*(158*width+246)+124*width+282) := by
  induction records with
  | nil => simp [recordCosts,coordinateBits]
  | cons r records ih =>
    simp only [recordCosts,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    simp only [coordinateBits,List.map_cons,List.sum_cons,List.length_cons,CompileRecord.bound]
    ring

theorem costBound_linear {n : ℕ} (precision width counterLength : ℕ)
    (r : AllocationPass.Record n) (records : List (AllocationPass.Record n))
    (flags : List Bool) (d : Data) (hv : Valid width (r::records) (false::flags) d) :
    costBound precision width counterLength r records flags d ≤
      ((r::records).length+1)*(13*counterLength+15) + recordCosts precision width (r::records) +
        (d.terms.length+(r::records).length)*(101*width+119)+(flags.count true+1)*(75*width+103) := by
  have ht := tailBound_linear precision width counterLength records flags (term r d)
    (valid_body false r records flags d hv)
  have hterms : (term r d).terms.length = d.terms.length+1 := by simp [term]
  rw [hterms] at ht
  simp only [costBound,recordCosts,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
  nlinarith

/-- Charged runtime is linear in records and coordinate bits, with explicit
polynomial dependence on precision, identifier width, and countdown width. -/
theorem costBound_bytes {n : ℕ} (precision width counterLength : ℕ)
    (r : AllocationPass.Record n) (records : List (AllocationPass.Record n))
    (flags : List Bool) (d : Data) (hv : Valid width (r::records) (false::flags) d) :
    costBound precision width counterLength r records flags d ≤
      ((r::records).length+1)*(13*counterLength+15) + 40*coordinateBits (r::records) +
        (r::records).length*(precision*(158*width+246)+124*width+282) +
        (d.terms.length+(r::records).length)*(101*width+119)+(flags.count true+1)*(75*width+103) := by
  have h := costBound_linear precision width counterLength r records flags d hv
  rw [recordCosts_eq] at h
  simpa only [Nat.add_assoc] using h

end Maxwell.Cost.SourceCircuit.ArithmeticPass
