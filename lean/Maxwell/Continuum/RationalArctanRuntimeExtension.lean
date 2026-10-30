import Maxwell.Continuum.RationalArctanRuntimeClean
import Maxwell.Continuum.RationalArctanExtension

/-! Framed, reusable fixed-code arctangent on a larger stored bank. -/
namespace Maxwell.Continuum.RationalArctan.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 1500000

theorem clean_extended (allIds : Finset ℕ) (hsub : RationalArctan.ids⊆allIds)
    (countTape N W : ℕ) (hcount : countTape∉ids) (hc4 : 4≤countTape)
    (hwork : ∀i∈allIds,i∉RationalArctan.ids → i∉loopWorkspace countTape)
    (v : ℕ→ℕ) (hW : 2≤W) (hw : ∀i∈RationalArctan.ids,(v i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue word=N) (hword : s.val.tapes countTape=BitTape.shifted word origin)
    (hs : NatAssign.Bank allIds v s.val) (hz : NatAssign.Scratch s.val)
    (h619 : Blank s.val 619) (h628 : Blank s.val 628) :
    ∃cost t,Executes input tape (cleanProgram countTape) cost s t ∧ cost≤cleanCost N W word.length ∧
      NatAssign.Bank allIds (RationalArctan.extendedValues v negativeSigns N) t.val ∧
      NatAssign.Scratch t.val ∧ Blank t.val countTape ∧ Blank t.val 619 ∧ Blank t.val 628 ∧
      BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val := by
  let v' : ℕ→ℕ := fun i => if i∈RationalArctan.ids then v i else 0
  have b : NatAssign.Bank ids v' s.val := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · simpa only [v',ite_eq_left hi] using hs i (hsub hi)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl
      · simpa [v',RationalArctan.ids,zero_word_iff_blank] using h619
      · simpa [v',RationalArctan.ids,zero_word_iff_blank] using h628
  have w : ∀i∈ids,(v' i).bits.length≤W := by
    intro i _
    by_cases hi : i∈RationalArctan.ids
    · simpa only [v',ite_eq_left hi] using hw i hi
    · simp [v',hi]
  obtain ⟨c,t,e,hc,bt,zt,zc,ft⟩ := clean_executes countTape N W v' hcount hc4 hW w
    input tape word origin s hn hword b hz
  have h610 : v' 610=v 610 := by simp [v',RationalArctan.ids]
  have h611 : v' 611=v 611 := by simp [v',RationalArctan.ids]
  rw [h610,h611] at bt
  refine ⟨c,t,e,hc,?_,zt,zc,?_,?_,ft⟩
  · intro i hi
    by_cases ha : i∈RationalArctan.ids
    · simpa only [RationalArctan.extendedValues,cleanValues,ite_eq_left ha] using
        bt i (Finset.mem_union_left _ ha)
    · simpa only [RationalArctan.extendedValues,ite_eq_right ha] using
        word_of_eq (ft.tapes i (hwork i hi ha)) (hs i hi)
  · simpa [cleanValues,RationalArctan.ids,zero_word_iff_blank] using bt 619 (by simp [ids])
  · simpa [cleanValues,RationalArctan.ids,zero_word_iff_blank] using bt 628 (by simp [ids])

#print axioms clean_extended
end Maxwell.Continuum.RationalArctan.Runtime
