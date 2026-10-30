import Maxwell.Continuum.ProfileCacheInput
import Maxwell.Continuum.CutoffCacheGeometry
import Maxwell.Continuum.CutoffCacheBank
import Maxwell.Continuum.CutoffCacheDimensionFrame
import Maxwell.Continuum.RationalDataflowBankPartition

/-! The actual generated profile output is handed to the fixed cache
allocator after charged header exchange, bank reset, and runtime layout derivation. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open Calibration.RawCutoff
open RationalAccumulator (Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
attribute [local irreducible] runtimeBudget profileDegree

def cachePreparationCode : Code := .seq headerSwapCode (.seq cacheBankInitial.code cacheRuntimePrepareCode)
def cachePreparationCost (W : ℕ) : ℕ :=
  256*(W+1)+(8*operationCost (256*(W+3))+1+cacheRuntimePrepareCost W)

theorem cachePreparation_executes {N heap : ℕ} {memory : ℕ→Bool} (s : Store)
    (r : EncodedTableResult N (runtimeBudget N) (finalBuffer N heap memory) s)
    (hh : heap.bits.length≤producerSize N)
    (hN : RationalAccumulator.Word s.val 660 N)
    (hheap : RationalAccumulator.Word s.val 709 (cacheSourceHeap N heap))
    (hclean : ∀i∈cacheDimensionIds,Blank s.val i)
    (hblank : ∀i∈RowIndex.ids,Blank s.val i)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape cachePreparationCode cost s t ∧
      cost≤cachePreparationCost (cacheSourceWidth N) ∧
      RationalDataflow.Ready (Finset.range 8) (cacheInitialValues r.values) t ∧
      r.table.Ready t ∧ r.input.OutputReady t ∧
      NatAssign.Bank cacheDimensionIds
        (cacheDimensionValues (profileDegree N) (cacheSourceWidth N) (cacheSourceHeap N heap)) t.val ∧
      (∀i∈RowIndex.ids,Blank t.val i) ∧ Blank t.val 216 ∧
      BankArray.Word t.val 201 r.countWord ∧
      (∀i∈([206,207,208,209,709]:List ℕ),t.val.tapes i=s.val.tapes i) := by
  let W := cacheSourceWidth N
  have hm := (allocated_metadata N heap hh memory).2
  obtain ⟨c0,s0,e0,hc0,r0,a0,b0,swap0,count0,f0⟩ := r.input_executes hm input tape
  have subset : Finset.range 8⊆dftRegisters := by decide
  have width : WidthBank (Finset.range 8) W r.values := fun i hi => r.width i (subset hi)
  have good : Good (Finset.range 8) r.values := fun i hi => r.good i (subset hi)
  obtain ⟨c1,s1,e1,hc1,r1,f1⟩ := cacheBankInitial_executes r.values W width good input tape s0
    (r0.rational.restrict subset)
  have a1 := a0.arithmetic_frame (Finset.range 8) f1 r1.2
  have b1 := b0.shared_frame (Finset.range 8) (f1.mono (workspace_subset_shared _)) a1.scratch a1.seven
  have before_keep (i : ℕ) (hi : 658≤ i ∧ i<1000) : s1.val.tapes i=s.val.tapes i :=
    (f1.tapes i (outside_workspace _ _ (by omega))).trans (f0.tapes i (by
      intro h;have := headerSlots_small i h;omega))
  have loadbank : NatAssign.Bank cacheLoadIds (cacheLoadInput N W (cacheSourceHeap N heap)) s1.val := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · have bounds := Finset.mem_Icc.mp hi
      have blank := RationalAccumulator.blank_of_eq (before_keep i (by omega)) (hclean i hi)
      have z := (RationalAccumulator.zero_word_iff_blank _ _).mpr blank
      simpa only [cacheLoadInput,ite_eq_right (by omega : i≠200),ite_eq_right (by omega : i≠660),
        ite_eq_right (by omega : i≠709)] using z
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl
      · simpa only [cacheLoadInput,ite_true] using r.cache_width_word a1
      · simpa only [cacheLoadInput,ite_eq_right (by decide : (660:ℕ)≠200),ite_true] using
          RationalAccumulator.word_of_eq (before_keep 660 (by decide)) hN
      · simpa only [cacheLoadInput,ite_eq_right (by decide : (709:ℕ)≠200),
          ite_eq_right (by decide : (709:ℕ)≠660),ite_true] using
          RationalAccumulator.word_of_eq (before_keep 709 (by decide)) hheap
  have hNW : N.bits.length≤W := (runtimeBudget_parameters N).2.2.2.2.trans (runtimeBudget_le_bufferWidth N _)
  obtain ⟨c2,t,e2,hc2,b2,z2,f2⟩ := cacheRuntimePrepare_executes N W (cacheSourceHeap N heap) W
    (cacheSourceWidth_ge N) hNW (cache_nat_bits_le W) (cacheSourceHeap_bits N heap hh)
    input tape s1 loadbank r1.2
  have rt := cacheDimensions_rational_frame r1 f2 z2
  have at' := cacheDimensions_table_frame a1 f2 z2
  have bt := cacheDimensions_output_frame b1 f2 at'.scratch at'.seven
  have final_keep (i : ℕ) (hi : i∈([206,207,208,209,220,221,222,201,709]:List ℕ)) :
      t.val.tapes i=s.val.tapes i := by
    have h2 : i∉({0,1,2,3}∪cacheDimensionIds) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have h1 : i∉workspace (Finset.range 8) := by
      apply outside_workspace
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      omega
    have h0 : i∉insert 216 headerSlots := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (f2.tapes i h2).trans ((f1.tapes i h1).trans (f0.tapes i h0))
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),Nat.add_le_add hc0 (Nat.add_le_add hc1 hc2),
    rt,at',bt,b2,?_,?_,BankArray.word_of_eq (final_keep 201 (by decide)) r.count,?_⟩
  · intro i hi
    apply RationalAccumulator.blank_of_eq (final_keep i _) (hblank i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl <;> decide
  · exact RationalAccumulator.blank_of_eq ((f2.tapes 216 (by decide)).trans
      (f1.tapes 216 (outside_workspace _ _ (by decide)))) swap0
  · intro i hi
    apply final_keep i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto

#print axioms cachePreparation_executes
end Maxwell.Continuum.Profile.Runtime
