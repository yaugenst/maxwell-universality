import Maxwell.Continuum.CalibrationCoefficientAllocation
import Maxwell.Cost.BankArray.ScratchFrame

/-! The previous padded traversal counter is cleared by executed code after
allocation. The inverse coefficient generator consequently starts from the
actual empty counter word, independently of its old padding. -/
namespace Maxwell.Continuum.Calibration.CoefficientAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def counterCode : Code := .seq code (WordCleanup.code [201])
def counterChanged : Finset ℕ := insert 201 changed

theorem counter_executes (n : ℕ→ℕ) (B H : ℕ) (hB : 10≤B) (hw : ∀k∈allIds,(n k).bits.length≤B)
    (a : Table (aliasArraySize (n 311)))
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (s : Store) (hs : NatAssign.Bank allIds n s.val)
    (ha : a.Ready s) (h37 : RationalAccumulator.Blank s.val 37) (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val)
    (counter : BankArray.Word s.val 201 xs) :
    ∃cost t,Executes input tape counterCode cost s t ∧ cost≤costBound n B H+6*xs.length+5 ∧
      a.Ready t ∧ (table n s.val.memory).OutputReady t ∧
      (table n s.val.memory).MetadataWidth (metadataWidth B) ∧
      NatAssign.Bank emissionIds n t.val ∧ RationalAccumulator.Word t.val 580 (budget n) ∧
      RationalAccumulator.Word t.val 570 (tableSize (aliasArraySize (n 311))) ∧
      RationalAccumulator.Word t.val 571 (slotWidth (budget n)) ∧ RationalAccumulator.Word t.val 572 (heap n) ∧
      RationalAccumulator.Blank t.val 201 ∧ RationalAccumulator.Blank t.val 216 ∧
      NatAssign.Bank workIds (allocatedWork n) t.val ∧
      (∀k∈workIds,(allocatedWork n k).bits.length ≤ allocatedWorkWidth B) ∧
      BinaryPrecision.Frame counterChanged s.val t.val := by
  obtain ⟨c0,u,e0,hc0,source0,out0,metadata,bank0,budget0,count0,width0,heap0,temp0,work0,workWidth,f0⟩ :=
    executes n B H hB hw a input tape s hs ha h37 h216 headers
  have old : WordCleanup.Bounded [201] xs.length u.val := by
    intro k hk
    have he:k=201:=by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hk
    subst k
    exact ⟨xs,le_rfl,BankArray.word_of_eq (f0.tapes 201 (by decide)) counter⟩
  obtain ⟨c1,t,e1,hc1,zero,f1⟩ := WordCleanup.executes [201] xs.length input tape u old
  have keep (k : ℕ) (hk:k≠201) : t.val.tapes k=u.val.tapes k := f1.tapes k (by simpa using hk)
  have scratch:=source0.scratch.transfer (fun k hk=>keep k (by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk;omega))
  have seven:=RationalAccumulator.blank_of_eq (keep 7 (by decide)) source0.seven
  have source:=source0.transfer f1.memory (fun k hk=>keep k (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)) scratch seven
  have output:=out0.transfer f1.memory (fun k hk=>keep k (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)) scratch seven
  have bank:NatAssign.Bank emissionIds n t.val:=by
    intro k hk
    have ne:k≠201:=fun he=>(show 201∉emissionIds by decide) (he ▸ hk)
    exact RationalAccumulator.word_of_eq (keep k ne) (bank0 k hk)
  refine ⟨c0+c1,t,e0.seq e1,?_,source,output,metadata,bank,
    RationalAccumulator.word_of_eq (keep 580 (by decide)) budget0,
    RationalAccumulator.word_of_eq (keep 570 (by decide)) count0,
    RationalAccumulator.word_of_eq (keep 571 (by decide)) width0,
    RationalAccumulator.word_of_eq (keep 572 (by decide)) heap0,zero 201 (by simp),
    RationalAccumulator.blank_of_eq (keep 216 (by decide)) temp0,?_,workWidth,
    (f0.mono (Finset.subset_insert _ _)).trans (f1.mono (by decide))⟩
  · simp only [List.length_cons,List.length_nil] at hc1
    omega
  · intro k hk
    apply RationalAccumulator.word_of_eq (keep k ?_) (work0 k hk)
    simp only [workIds,Finset.mem_insert,Finset.mem_singleton] at hk
    omega

#print axioms counter_executes
end Maxwell.Continuum.Calibration.CoefficientAllocation
