import Maxwell.Continuum.RationalTaylorRuntimeClean
import Maxwell.Continuum.RationalTaylorExtension

/-! A reusable fixed Taylor call retains its surrounding stored bank. -/
namespace Maxwell.Continuum.RationalTaylor.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 1500000

theorem clean_extended (allIds : Finset ℕ) (hsub : RationalTaylor.ids⊆allIds)
    (cycle : Cycle) (countTape N W : ℕ) (hcount : countTape∉ids) (hc4 : 4≤countTape)
    (hwork : ∀i∈allIds,i∉RationalTaylor.ids → i∉loopWorkspace countTape)
    (v : ℕ→ℕ) (hW : 1≤W) (hw : ∀i∈RationalTaylor.ids,(v i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue word=N) (hword : s.val.tapes countTape=BitTape.shifted word origin)
    (hs : NatAssign.Bank allIds v s.val) (hz : NatAssign.Scratch s.val)
    (h607 : Blank s.val 607) (h608 : Blank s.val 608) :
    ∃cost t,Executes input tape (cleanProgram cycle countTape) cost s t ∧ cost≤cleanCost N W word.length ∧
      NatAssign.Bank allIds (RationalTaylor.extendedValues v (cycleSigns cycle) N) t.val ∧
      NatAssign.Scratch t.val ∧ Blank t.val countTape ∧ Blank t.val 607 ∧ Blank t.val 608 ∧
      BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val := by
  let v' : ℕ→ℕ := fun i => if i∈RationalTaylor.ids then v i else 0
  have b : NatAssign.Bank ids v' s.val := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · simpa only [v',ite_eq_left hi] using hs i (hsub hi)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl
      · simpa [v',RationalTaylor.ids,zero_word_iff_blank] using h607
      · simpa [v',RationalTaylor.ids,zero_word_iff_blank] using h608
  have w : ∀i∈ids,(v' i).bits.length≤W := by
    intro i _
    by_cases hi : i∈RationalTaylor.ids
    · simpa only [v',ite_eq_left hi] using hw i hi
    · simp [v',hi]
  obtain ⟨c,t,e,hc,bt,zt,zc,ft⟩ := clean_executes cycle countTape N W v' hcount hc4 hW w
    input tape word origin s hn hword b hz
  have h600 : v' 600=v 600 := by simp [v',RationalTaylor.ids]
  have h601 : v' 601=v 601 := by simp [v',RationalTaylor.ids]
  rw [h600,h601] at bt
  refine ⟨c,t,e,hc,?_,zt,zc,?_,?_,ft⟩
  · intro i hi
    by_cases ha : i∈RationalTaylor.ids
    · simpa only [RationalTaylor.extendedValues,cleanValues,ite_eq_left ha] using
        bt i (Finset.mem_union_left _ ha)
    · simpa only [RationalTaylor.extendedValues,ite_eq_right ha] using
        word_of_eq (ft.tapes i (hwork i hi ha)) (hs i hi)
  · simpa [cleanValues,RationalTaylor.ids,zero_word_iff_blank] using bt 607 (by simp [ids])
  · simpa [cleanValues,RationalTaylor.ids,zero_word_iff_blank] using bt 608 (by simp [ids])

#print axioms clean_extended
end Maxwell.Continuum.RationalTaylor.Runtime
