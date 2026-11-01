import Maxwell.Continuum.StoredAmbientPhysical
import Maxwell.Continuum.StoredPhysicalBody

/-! Ambient output uses a disjoint iterator bank and restores the shared
arithmetic scratch, preserving the actual inputs needed by physical output. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters
open RationalAccumulator (Word Blank word_of_eq blank_of_eq zero_word_iff_blank)
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

theorem ambient_kept {s t : BitRAMState}
    (f : GeometryOutput.OutputFrame StoredAmbient.relocatedWork s t)
    (i : ℕ) (lo : 4≤ i) (hi : i<5000) : t.tapes i=s.tapes i := by
  apply f.tapes
  simp only [StoredAmbient.relocatedWork,StoredAmbient.relocatedOld,List.toFinset_cons,List.toFinset_nil,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false]
  omega

theorem ambient_old {s t : BitRAMState}
    (f : GeometryOutput.OutputFrame StoredAmbient.relocatedWork s t)
    (scratch : NatAssign.Scratch t) (xs : List ℕ) (upper : ∀i∈xs,i<5000) (H : ℕ)
    (old : WordCleanup.Bounded xs H s) : WordCleanup.Bounded xs H t := by
  intro i hi
  by_cases low:i<4
  · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (scratch i low)⟩
  · obtain ⟨bits,hbits,word⟩:=old i hi
    exact ⟨bits,hbits,BankArray.word_of_eq (ambient_kept f i (by omega) (upper i hi)) word⟩

theorem StoredInputs.ambient {v : ℕ→ℕ} {parts : ℕ→Parts} {B H : ℕ} {clock : List Bool} {s t : Store}
    (h : StoredInputs v parts B H clock s)
    (f : GeometryOutput.OutputFrame StoredAmbient.relocatedWork s.val t.val)
    (scratch : NatAssign.Scratch t.val) : StoredInputs v parts B H clock t := by
  have keep := ambient_kept f
  refine ⟨h.budget_ge,h.width,?_,?_,?_,blank_of_eq (keep 7 (by decide) (by decide)) h.seven,
    blank_of_eq (keep 37 (by decide) (by decide)) h.thirtySeven,
    blank_of_eq (keep 216 (by decide) (by decide)) h.temp,
    BankArray.word_of_eq (keep 1251 (by decide) (by decide)) h.clockWord,?_,?_,?_,?_⟩
  · intro i hi
    have bounds : ∀i∈inputs,4≤ i ∧i<5000:=by decide +kernel
    exact word_of_eq (keep i (bounds i hi).1 (bounds i hi).2) (h.bank i hi)
  · exact ⟨scratch 0 (by decide),scratch 1 (by decide),scratch 2 (by decide),scratch 3 (by decide),
      blank_of_eq (keep 5 (by decide) (by decide)) h.scratch.2.2.2.2.1,
      blank_of_eq (keep 6 (by decide) (by decide)) h.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8 (by decide) (by decide)) h.scratch.2.2.2.2.2.2.1,
      blank_of_eq (keep 9 (by decide) (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  · refine ⟨?_,scratch⟩
    intro i hi
    have bounds : ∀i∈RationalDataflow.ids WellStrength.bank,4≤ i ∧i<5000:=by decide +kernel
    exact word_of_eq (keep i (bounds i hi).1 (bounds i hi).2) (h.rational.1 i hi)
  · apply ambient_old f scratch _ _ H h.oldGeometry
    intro i hi
    simp only [Geometry.clearHeaders,List.mem_append,Finset.mem_sort] at hi
    rcases hi with hi|hi
    · exact (by decide +kernel : ∀i∈Geometry.targets,i<5000) i hi
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      omega
  · exact ambient_old f scratch _ (by decide +kernel) H h.oldTable
  · exact ambient_old f scratch _ (by decide +kernel) H h.oldAllocation
  · exact ambient_old f scratch _ (by decide +kernel) H h.oldClean

theorem SuffixInputWords.ambient {p S hm nv H} {s t : Store} (h : SuffixInputWords p S hm nv H s)
    (f : GeometryOutput.OutputFrame StoredAmbient.relocatedWork s.val t.val)
    (scratch : NatAssign.Scratch t.val) : SuffixInputWords p S hm nv H t := by
  have keep:=ambient_kept f
  refine ⟨word_of_eq (keep 506 (by decide) (by decide)) h.sourceNumerator,
    word_of_eq (keep 507 (by decide) (by decide)) h.sourceDenominator,
    word_of_eq (keep 4427 (by decide) (by decide)) h.sourcePrecision,
    BankArray.word_of_eq (keep 508 (by decide) (by decide)) h.archive,
    word_of_eq (keep 503 (by decide) (by decide)) h.first,?_,
    ambient_old f scratch _ (by decide +kernel) H h.old⟩
  intro i hi
  have bounds : ∀i∈suffixSelectorPorts,4≤ i ∧i<5000:=by decide +kernel
  exact word_of_eq (keep i (bounds i hi).1 (bounds i hi).2) (h.selectors i hi)

#print axioms StoredInputs.ambient
#print axioms SuffixInputWords.ambient
end Maxwell.Continuum.WellStrengthInitialization
