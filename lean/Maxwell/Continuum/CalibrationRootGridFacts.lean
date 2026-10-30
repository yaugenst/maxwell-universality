import Maxwell.Continuum.CalibrationRootGridStep

/-! The five literal decoder inputs and the automatic width invariant
preserved by every quadrature iteration. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost
set_option maxHeartbeats 2500000

def naturalWidth (B : ℕ) : ℕ := 2^8*(B+1)

structure InputFacts (grid : ℕ) (frequency : Fin 3→ℤ) (B : ℕ) (n : ℕ→ℕ) : Prop where
  grid_eq : n 331=grid
  frequency_eq : ∀i,![n 336,n 337,n 338] i=
    ((-(PeriodicSampling.Product.frequency grid frequency)) i).val
  work_zero : ∀i∈NaturalQuotient.workPorts,n i=0
  source_width : ∀i∈sourceIds,(n i).bits.length≤B
  all_width : ∀i∈ids,(n i).bits.length≤naturalWidth B

theorem sourceIds_subset : sourceIds⊆ids := by decide

theorem InputFacts.next {grid B : ℕ} {frequency : Fin 3→ℤ} {n : ℕ→ℕ}
    (h : InputFacts grid frequency B n) (index : ℕ) (hi : index.bits.length≤B) :
    InputFacts grid frequency B (values (indexedInputs n index)) := by
  have source (i : ℕ) (hm : i∈sourceIds) : (indexedInputs n index i).bits.length≤B := by
    by_cases he : i=330
    · subst i
      exact hi
    · simpa only [indexedInputs,Function.update_of_ne he] using h.source_width i hm
  have hz := indexed_work_zero n index h.work_zero
  refine ⟨?_,?_,?_,?_,values_source_width _ B hz source⟩
  · rw [values_sources _ 331 (by decide),indexedInputs,Function.update_of_ne (by decide : (331:ℕ)≠330)]
    exact h.grid_eq
  · intro i
    have h336 : values (indexedInputs n index) 336=n 336 := by
      rw [values_sources _ 336 (by decide)]
      rfl
    have h337 : values (indexedInputs n index) 337=n 337 := by
      rw [values_sources _ 337 (by decide)]
      rfl
    have h338 : values (indexedInputs n index) 338=n 338 := by
      rw [values_sources _ 338 (by decide)]
      rfl
    rw [h336,h337,h338]
    exact h.frequency_eq i
  · intro i hm
    rw [values_work _ i hm,hz i hm]
  · intro i hm
    rw [values_sources _ i hm]
    exact source i hm

theorem InputFacts.indexed_frequency {grid B : ℕ} {frequency : Fin 3→ℤ} {n : ℕ→ℕ}
    (h : InputFacts grid frequency B n) (index : ℕ) (i : Fin 3) :
    ![indexedInputs n index 336,indexedInputs n index 337,indexedInputs n index 338] i=
      ((-(PeriodicSampling.Product.frequency grid frequency)) i).val := by
  simpa only [indexedInputs,Function.update_of_ne (by decide : (336:ℕ)≠330),
    Function.update_of_ne (by decide : (337:ℕ)≠330),
    Function.update_of_ne (by decide : (338:ℕ)≠330)] using h.frequency_eq i

theorem InputFacts.indexed_exact {grid B : ℕ} [NeZero grid] {frequency : Fin 3→ℤ}
    {n : ℕ→ℕ} (h : InputFacts grid frequency B n) (N index : ℕ)
    (v : ℕ→Parts) (hv : (v 9).Valid) :
    (sampleParts N (indexedInputs n index) v 6).value=
      (Calibration.rootProductSample grid (v 9).value N frequency (point grid index)).re.center ∧
    (sampleParts N (indexedInputs n index) v 7).value=
      (Calibration.rootProductSample grid (v 9).value N frequency (point grid index)).im.center := by
  apply sampleParts_exact grid N index (v 9).value frequency _ v _ rfl
    (h.indexed_frequency index) hv rfl
  simpa only [indexedInputs,Function.update_of_ne (by decide : (331:ℕ)≠330)] using h.grid_eq

#print axioms InputFacts.next
#print axioms InputFacts.indexed_exact
end Maxwell.Continuum.RationalDataflow.RootGrid
