import Maxwell.Continuum.CalibrationNeumannInitialized
import Maxwell.Continuum.CalibrationNeumannArrayCopy

/-! The real table-copy routine preserves the canonical descriptor words
needed by setup. Its fixed-width countdown is deliberately excluded. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

theorem word_unique {s : BitRAMState} {i : ℕ} {xs ys : List Bool}
    (hx : BankArray.Word s i xs) (hy : BankArray.Word s i ys) : xs=ys := by
  obtain ⟨ox,hx⟩ := hx
  obtain ⟨oy,hy⟩ := hy
  have he := hx.symm.trans hy
  have ho : ox=oy := congrArg BitTape.head he
  subst oy
  apply List.ext_getElem?
  intro k
  have hk := congrArg (fun z : BitTape => z.cells (ox+k)) he
  simpa [BitTape.shifted] using hk

theorem word_recover {s t : BitRAMState} {i n : ℕ} {xs : List Bool}
    (hn : RationalAccumulator.Word s i n) (hx : BankArray.Word s i xs)
    (hy : BankArray.Word t i xs) : RationalAccumulator.Word t i n := by
  have he := word_unique hn hx
  rw [←he] at hy
  exact hy

def copyProtected : Finset ℕ := Finset.Icc 107 140 ∪ Finset.Icc 300 310

theorem copy_protects : (List.range' 107 34 ++ List.range' 300 11).all
    (fun i => PartArray.copyCode.protectsTape i)=true := by
  decide

theorem copied_descriptor_bank {n : ℕ} (a b : PartArray.Table n)
    (old new : ℕ→Parts) (v : ℕ→ℕ) {input : List Bool} {tape : ℕ→Bool}
    {cost : ℕ} {s t : Store} (he : Executes input tape PartArray.copyCode cost s t)
    (hs : SharedConversion.Ready {1} old s) (ht : SharedConversion.Ready {1} new t)
    (ha : a.Ready s) (ha' : a.Ready t) (hb : b.OutputReady s)
    (hb' : (b.filled a.get 0).OutputReady t)
    (hv : NatAssign.Bank Descriptors.ids v s.val) : NatAssign.Bank Descriptors.ids v t.val := by
  intro i hi
  by_cases hwork : i∈workPorts
  · have hid : i∈SharedConversion.bankIds {1} :=
      Finset.mem_union_left _ (Finset.mem_union_right _ hwork)
    have hsmall : i<1000 := by
      simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hwork
      omega
    have hold := hs.1 i hid
    have hnew := ht.1 i hid
    rw [dataValues_small old hsmall] at hold
    rw [dataValues_small new hsmall] at hnew
    exact word_recover (hv i hi) hold hnew
  · by_cases hp : i∈copyProtected
    · exact RationalAccumulator.word_of_eq (he.protectsTape i
        (List.all_eq_true.mp copy_protects i (by
          simp only [copyProtected,Finset.mem_union,Finset.mem_Icc] at hp
          simp only [List.mem_append,List.mem_range'_1]
          omega))) (hv i hi)
    · have hcases : i=200 ∨ i=202 ∨ i=203 ∨ i=204 ∨ i=210 ∨ i=212 ∨ i=213 ∨ i=214 := by
        simp only [Descriptors.ids,copyProtected,workPorts,temporaryPorts,RationalMagnitude.ids,
          Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi hp hwork
        omega
      rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact word_recover (hv _ hi) ha.width ha'.width
      · exact word_recover (hv _ hi) ha.basePositive ha'.basePositive
      · exact word_recover (hv _ hi) ha.baseNegative ha'.baseNegative
      · exact word_recover (hv _ hi) ha.baseDenominator ha'.baseDenominator
      · exact word_recover (hv _ hi) hb.width hb'.width
      · exact word_recover (hv _ hi) hb.basePositive hb'.basePositive
      · exact word_recover (hv _ hi) hb.baseNegative hb'.baseNegative
      · exact word_recover (hv _ hi) hb.baseDenominator hb'.baseDenominator

theorem shared_blank_clock {S : Finset ℕ} {v : ℕ→Parts} {s : Store}
    (hs : SharedConversion.Ready S v s) : RationalAccumulator.Blank s.val 101 := by
  have h := hs.1 101 (Finset.mem_union_left _ (Finset.mem_union_right _ (by
    simp [workPorts,temporaryPorts])))
  rw [dataValues_small v (by decide),RationalAccumulator.zero_word_iff_blank] at h
  exact h

#print axioms copied_descriptor_bank

end Maxwell.Continuum.Calibration.NeumannMachine
