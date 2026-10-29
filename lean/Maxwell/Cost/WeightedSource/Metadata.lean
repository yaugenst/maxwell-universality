import Maxwell.Cost.WeightedSource.MetadataPlan
import Maxwell.Cost.IncidenceEncoding

namespace Maxwell.Cost.WeightedSource.Metadata
open Structured
open RationalAccumulator (Word Blank word_of_eq blank_of_eq)
set_option maxHeartbeats 1600000

def code (n : ℕ) : Code := .seq (NatAssign.code (prePlan n))
  (.seq (DecoderConstants.powerCode 402 412)
    (.seq (DecoderConstants.powerCode 408 515) (NatAssign.code postPlan)))
def work (n : ℕ) : Finset ℕ := NatAssign.changes (prePlan n) ∪ {68,412,515} ∪ NatAssign.changes postPlan

private theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  omega
private theorem ids_ne68 (i : ℕ) (hi : i∈ids) : i ≠ 68 := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

private theorem power_bank (source target p : ℕ) (hs : source ≠ 68) (ht : target ≠ 68)
    (hst : source ≠ target) (h4 : 4 ≤ target) (v : ℕ→ℕ) (hzero : v target=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hv : NatAssign.Bank ids v s.val) (hr : NatAssign.Scratch s.val)
    (hw : Word s.val source p) (h68 : Blank s.val 68) (htarget : target∈ids) :
    ∃ cost t, Executes input tape (DecoderConstants.powerCode source target) cost s t  ∧ 
      cost ≤ powerBudget p  ∧  NatAssign.Bank ids (Function.update v target (2^p)) t.val  ∧ 
      NatAssign.Scratch t.val  ∧  Blank t.val 68  ∧  BinaryPrecision.Frame {68,target} s.val t.val := by
  obtain ⟨cost,t,hc,he,hw,ht68,hf⟩ := DecoderConstants.power source target hs ht hst input tape p s hw
    ((RationalAccumulator.zero_word_iff_blank _ _).mp (by simpa only [hzero] using hv target htarget)) h68
  refine ⟨cost,t,he,hc,?_,?_,ht68,?_⟩
  · intro i hi
    by_cases hit : i=target
    · subst i; simpa only [Function.update_self] using hw
    · simp only [Function.update_of_ne hit]
      exact word_of_eq (hf.2.2.2.2.2.1 i (ids_ne68 i hi) hit) (hv i hi)
  · intro i hi
    exact blank_of_eq (hf.2.2.2.2.2.1 i (by omega) (by omega)) (hr i hi)
  · exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,
      fun i hi=>hf.2.2.2.2.2.1 i (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega)
        (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega)⟩

/-- All weighted-source scalar metadata is generated from the stored request
precision and heap end. No array-content assumption is needed. -/
theorem executes (n b heapEnd : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : Word s.val 401 b) (hend : Word s.val 251 heapEnd)
    (hz : ∀ i∈ids, i ≠ 401 → i ≠ 251 → Word s.val i 0)
    (hr : NatAssign.Scratch s.val) (h68 : Blank s.val 68) :
    ∃ cost t, Executes input tape (code n) cost s t  ∧  cost ≤ costBound n b heapEnd  ∧ 
      NatAssign.Bank ids (resultValues n b heapEnd) t.val  ∧  NatAssign.Scratch t.val  ∧ 
      Blank t.val 68  ∧  Blank t.val 403  ∧  Blank t.val 408  ∧  BinaryPrecision.Frame (work n) s.val t.val := by
  have initialBank : NatAssign.Bank ids (initial b heapEnd) s.val := by
    intro i hi
    by_cases h401 : i=401
    · subst i; simpa [initial] using hb
    · by_cases h251 : i=251
      · subst i; simpa [initial] using hend
      · simpa [initial,h401,h251] using hz i hi h401 h251
  have valid : ∀ a∈prePlan n, a.Valid ids := by simp [prePlan,NatAssign.Instruction.Valid,ids]
  obtain ⟨pc,a,ep,hpc,ha,ra,fa⟩ := NatAssign.executes ids ids_ge (prePlan n) valid (initial b heapEnd)
    input tape s initialBank hr
  change NatAssign.Bank ids (preValues n b heapEnd) a.val at ha
  obtain ⟨h400,h402,h514,h408,h412,h515⟩ := pre_values n b heapEnd
  obtain ⟨c1,u,e1,hc1,hu,ru,hu68,f1⟩ := power_bank 402 412 (precision n b) (by decide) (by decide)
    (by decide) (by decide) (preValues n b heapEnd) h412 input tape a ha ra
    (by simpa only [h402] using ha 402 (by decide))
    (blank_of_eq (fa.tapes 68 (by simp [NatAssign.changes,prePlan,NatAssign.Instruction.target])) h68) (by decide)
  have hu408 : Word u.val 408 (precision n b+1) := by
    simpa only [Function.update_of_ne (by decide : (408:ℕ) ≠ 412),h408] using hu 408 (by decide)
  have hu515 : Function.update (preValues n b heapEnd) 412 (2^precision n b) 515=0 := by
    simpa only [Function.update_of_ne (by decide : (515:ℕ) ≠ 412)] using h515
  obtain ⟨c2,v,e2,hc2,hv,rv,hv68,f2⟩ := power_bank 408 515 (precision n b+1) (by decide) (by decide)
    (by decide) (by decide) (Function.update (preValues n b heapEnd) 412 (2^precision n b)) hu515
    input tape u hu ru hu408 hu68 (by decide)
  have postValid : ∀ a∈postPlan, a.Valid ids := by simp [postPlan,NatAssign.Instruction.Valid,ids]
  obtain ⟨qc,t,eq,hqc,ht,rt,ft⟩ := NatAssign.executes ids ids_ge postPlan postValid (powerValues n b heapEnd)
    input tape v hv rv
  have frame : BinaryPrecision.Frame (work n) s.val t.val :=
    (((fa.mono (by intro i hi;exact Finset.mem_union_left _ (Finset.mem_union_left _ hi))).trans
      (f1.mono (by simp [work];aesop))).trans (f2.mono (by simp [work];aesop))).trans
      (ft.mono (by intro i hi;exact Finset.mem_union_right _ hi))
  have hzero403 : resultValues n b heapEnd 403=0 := (result_values n b heapEnd).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzero408 : resultValues n b heapEnd 408=0 := (result_values n b heapEnd).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨pc+(c1+(c2+qc)),t,ep.seq (e1.seq (e2.seq eq)),?_,ht,rt,
    blank_of_eq (ft.tapes 68 (by decide)) hv68,?_,?_,frame⟩
  · dsimp only [costBound]
    omega
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mp (by simpa only [hzero403] using ht 403 (by decide))
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mp (by simpa only [hzero408] using ht 408 (by decide))

theorem clock_length (n b : ℕ) : (2^(precision n b+1):ℕ).bits.length=precision n b+2 := by
  simp [PowerOfTwo.power_bits]

theorem output_separated (n b heapEnd : ℕ) :
    IncidenceEncoding.Separated heapEnd (n*(precision n b+2))
      (heapEnd+n*(precision n b+2)) (n*(precision n b+2)) := Or.inl le_rfl

/-- The original precision, heap boundary, mode arrays, mode denominator,
input layout, arithmetic bank, and Weight workspace all survive exactly. -/
theorem preserved (n : ℕ) {s t : BitRAMState} (hf : BinaryPrecision.Frame (work n) s t)
    (i : ℕ) (hi : i=401  ∨  i=251  ∨  i=128  ∨  i=129  ∨  i=153  ∨  i=100  ∨  i=101  ∨ 
      (4 ≤ i  ∧  i ≤ 9)  ∨  (30 ≤ i  ∧  i ≤ 36)  ∨  i=40  ∨  i=410  ∨  i=411) : t.tapes i=s.tapes i := by
  apply hf.tapes
  simp only [work,NatAssign.changes,prePlan,postPlan,List.map_cons,List.map_nil,
    NatAssign.Instruction.target,List.toFinset_cons,List.toFinset_nil,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.not_mem_empty,or_false]
  omega

theorem compiled_run (n b heapEnd : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : Word s.val 401 b) (hend : Word s.val 251 heapEnd)
    (hz : ∀ i∈ids, i ≠ 401 → i ≠ 251 → Word s.val i 0)
    (hr : NatAssign.Scratch s.val) (h68 : Blank s.val 68) :
    ∃ t : Store, (runPriced ((code n).compile.next input tape) (costBound n b heapEnd+1) s.val).finished=
        some (t.place (code n).size)  ∧ 
      (runPriced ((code n).compile.next input tape) (costBound n b heapEnd+1) s.val).instructions ≤ 
        200000*(widthBound n b heapEnd)^2  ∧ 
      NatAssign.Bank ids (resultValues n b heapEnd) t.val  ∧  NatAssign.Scratch t.val  ∧ 
      Blank t.val 68  ∧  Blank t.val 403  ∧  Blank t.val 408  ∧  BinaryPrecision.Frame (work n) s.val t.val := by
  obtain ⟨c,t,he,hc,ht⟩ := executes n b heapEnd input tape s hb hend hz hr h68
  have run := he.compiled_run (costBound n b heapEnd+1) (by omega)
  exact ⟨t,run.1,run.2 ▸ hc.trans (costBound_polynomial n b heapEnd),ht⟩

end Maxwell.Cost.WeightedSource.Metadata
