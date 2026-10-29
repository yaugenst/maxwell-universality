import Maxwell.Cost.CalibrationMatrix.HeaderWords

namespace Maxwell.Cost.CalibrationMatrix.EraseWords
open Structured BankArray
open RationalAccumulator (Blank)

def code : List ℕ → Code
  | [] => .skip
  | i :: rest => .seq (.call (TapeOps.clear i)) (code rest)

/-- Execute a fixed cleanup schedule. Repeated names are harmless and every
bit erased is charged; the sources are the actual stored words. -/
theorem executes (banks : List ℕ) (width : ℕ) (words : ℕ → List Bool)
    (hlen : ∀ i ∈ banks, (words i).length ≤ width) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (hw : ∀ i ∈ banks, Word s.val i (words i)) :
    ∃ cost t, cost ≤ banks.length*(6*width+4)+1 ∧
      Executes input tape (code banks) cost s t ∧
      (∀ i ∈ banks, Blank t.val i) ∧ BinaryPrecision.Frame banks.toFinset s.val t.val := by
  induction banks generalizing s words with
  | nil => exact ⟨1,s,by simp,.skip s,by simp,BinaryPrecision.Frame.refl _ _⟩
  | cons i rest ih =>
    obtain ⟨m,ea,hblank,hf⟩ := HeaderWords.clear i input tape (words i) s (hw i (by simp))
    let v := Function.update words i []
    have hl (j : ℕ) (hj : j ∈ rest) : (v j).length ≤ width := by
      by_cases hji : j = i
      · simp [v,hji]
      · simpa [v,hji] using hlen j (by simp [hj])
    have hwords (j : ℕ) (hj : j ∈ rest) : Word m.val j (v j) := by
      by_cases hji : j = i
      · subst j
        simpa [v,Word,Blank] using hblank
      · simpa [v,hji] using hf.word (by simpa using hji) (hw j (by simp [hj]))
    obtain ⟨cost,t,hcost,et,ht,hg⟩ := ih v hl m hwords
    refine ⟨6*(words i).length+4+cost,t,?_,ea.seq et,?_,?_⟩
    · have hl := hlen i (by simp)
      simp only [List.length_cons]
      nlinarith
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · by_cases hi : j ∈ rest
        · exact ht j hi
        · exact hg.blank (by simpa using hi) hblank
      · exact ht j hj
    · exact (hf.mono (by simp)).trans (hg.mono (by simp))

end Maxwell.Cost.CalibrationMatrix.EraseWords
