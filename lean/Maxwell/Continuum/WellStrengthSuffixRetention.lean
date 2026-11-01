import Maxwell.Continuum.WellStrengthInitializedWells
import Maxwell.Continuum.StoredDescriptionSuffixInputs
import Maxwell.Cost.Structured.WordCleanup.Footprint

/-! Source archives and decoder selector words survive well production.
The few shared scratch words are recovered from its actual final clean
state and counted-loop output, rather than assuming a fresh backend. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word Blank word_of_eq blank_of_eq zero_word_iff_blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

def suffixStableWords : Finset ℕ:={503,506,507,508,4427}∪suffixSelectorPorts
def suffixRecycledWords : Finset ℕ:={0,1,2,3,4,220,221,222,223,972}
def suffixStableOld : Finset ℕ:=suffixOldPorts.toFinset\suffixRecycledWords

private theorem geometry_cleanup (kept : Finset ℕ)
    (ht : Disjoint Geometry.targets kept) (hc : Disjoint ({962,972,973}:Finset ℕ) kept) :
    (WordCleanup.code Geometry.clearHeaders).protectsSet kept=true:=by
  apply WordCleanup.code_protectsSet
  intro i hi
  simp only [Geometry.clearHeaders,List.mem_append,Finset.mem_sort] at hi
  rcases hi with hi|hi
  · exact Finset.disjoint_left.mp ht hi
  · exact Finset.disjoint_left.mp hc (by
      simpa only [List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton] using hi)

theorem wellsCode_suffix_words : wellsCode.protectsSet suffixStableWords=true:=by
  simp only [wellsCode,fullCode,code,Geometry.code,Code.protectsSet]
  rw [geometry_cleanup suffixStableWords (by decide) (by decide)]
  decide +kernel
theorem wellsCode_suffix_old : wellsCode.protectsSet suffixStableOld=true:=by
  simp only [wellsCode,fullCode,code,Geometry.code,Code.protectsSet]
  rw [geometry_cleanup suffixStableOld (by decide) (by decide)]
  decide +kernel

theorem wells_suffix_old {cost H G : ℕ} {input : List Bool} {tape : ℕ→Bool} {s t : Store}
    (run : Executes input tape wellsCode cost s t) (old : WordCleanup.Bounded suffixOldPorts H s.val)
    (scratch : NatAssign.Scratch t.val) (clean : DyadicFloor.Clean t.val)
    (count : WordCleanup.Bounded [972,973] G t.val) : WordCleanup.Bounded suffixOldPorts (H+G) t.val:=by
  intro i hi
  by_cases small:i<4
  · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (scratch i small)⟩
  by_cases four:i=4
  · subst i;exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr clean.1⟩
  by_cases quotient:i∈NaturalQuotient.workPorts
  · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (clean.2 i (Finset.mem_union_right _ quotient))⟩
  by_cases counter:i=972
  · subst i
    obtain ⟨xs,hw,word⟩:=count 972 (by simp)
    exact ⟨xs,hw.trans (by omega),word⟩
  have stable : i∈suffixStableOld:=by
    refine Finset.mem_sdiff.mpr ⟨by simpa using hi,?_⟩
    simp only [suffixRecycledWords,Finset.mem_insert,Finset.mem_singleton,not_or]
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton,not_or] at quotient
    omega
  obtain ⟨xs,hw,word⟩:=old i hi
  exact ⟨xs,hw.trans (by omega),BankArray.word_of_eq (run.protectsSet _ wellsCode_suffix_old i stable) word⟩

structure SuffixInputWords (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (nv : ℕ→ℕ) (H : ℕ) (s : Store) : Prop where
  sourceNumerator : Word s.val 506 (NormalizeRatio.sourceScalePair S).1
  sourceDenominator : Word s.val 507 (NormalizeRatio.sourceScalePair S).2
  sourcePrecision : Word s.val 4427 (RealizationParameters.sourcePrecision p S)
  archive : BankArray.Word s.val 508 (LogRats.records (List.ofFn S.source))
  first : Word s.val 503 (sourceCircuit S (RealizationParameters.precision p S hm)).size
  selectors : NatAssign.Bank suffixSelectorPorts nv s.val
  old : WordCleanup.Bounded suffixOldPorts H s.val

theorem wells_suffix_stored {p S hm data v nv saved table R H clock gv rv}
    {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (run : Executes input tape wellsCode cost s t)
    (before : SuffixInputWords p S hm nv H s)
    (geometry : GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (geometryBudget v)
      clock (Geometry.values v) gv t)
    (payload : WellPayload.State table (wellStoredPrecision p S hm) R (siteCount saved)
      (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm) rv t)
    (raw : Ready WellStrength.bank (Function.update (WellStrengthPhysical.values p S hm data) 0 (rv 0)) t)
    (clean : DyadicFloor.Clean t.val) (power : Word t.val 144 (2^wellStoredPrecision p S hm))
    (counters : WordCleanup.Bounded [972,973] (geometryBudget v) t.val) :
    SuffixStored p S hm data v nv saved table R (H+geometryBudget v) clock gv rv t:=by
  have keep (i : ℕ) (hi : i∈suffixStableWords):=run.protectsSet _ wellsCode_suffix_words i hi
  exact ⟨geometry,payload,raw,clean,power,
    word_of_eq (keep 506 (by decide)) before.sourceNumerator,
    word_of_eq (keep 507 (by decide)) before.sourceDenominator,
    word_of_eq (keep 4427 (by decide)) before.sourcePrecision,
    BankArray.word_of_eq (keep 508 (by decide)) before.archive,
    word_of_eq (keep 503 (by decide)) before.first,
    fun i hi=>word_of_eq (keep i (Finset.mem_union_right _ hi)) (before.selectors i hi),
    wells_suffix_old run before.old raw.2 clean counters⟩

#print axioms wells_suffix_old
#print axioms wells_suffix_stored
end Maxwell.Continuum.WellStrengthInitialization
