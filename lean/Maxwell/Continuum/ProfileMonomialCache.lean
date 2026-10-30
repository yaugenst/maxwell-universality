import Maxwell.Continuum.CutoffCacheNaturalBank
import Maxwell.Continuum.ProfileCachePreparation
import Maxwell.Continuum.CutoffCachePair
import Maxwell.Continuum.CutoffCacheStart
import Maxwell.Continuum.CutoffMonomialOuterBoundary

/-! Generated profile coefficients are converted to the actual cached
monomial polynomial by one fixed runtime program, including both allocations
and every Chebyshev recurrence step. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open Calibration.RawCutoff
open RationalAccumulator (Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
attribute [local irreducible] runtimeBudget profileDegree


def monomialCacheCode : Code := .seq cachePreparationCode
  (.seq cachePairCode (.seq cacheStartCode monomialOuterCode))
def monomialCacheCost (N : ℕ) : ℕ := cachePreparationCost (cacheSourceWidth N)+
  (cachePairCost (profileDegree N) (cacheSourceWidth N) (profileDegree N).bits.length+
    (30*(profileDegree N).bits.length+2048+
      monomialOuterCost (profileDegree N) (cacheSourceWidth N) (profileDegree N).bits.length))

theorem outer_preserves_cache_metadata : (List.range 10).all
    (fun i => monomialOuterCode.protectsTape (720+i))=true := by decide

theorem monomialCache_executes {N heap : ℕ} {memory : ℕ→Bool} (s : Store)
    (r : EncodedTableResult N (runtimeBudget N) (finalBuffer N heap memory) s)
    (hh : heap.bits.length≤producerSize N)
    (hN : RationalAccumulator.Word s.val 660 N)
    (hheap : RationalAccumulator.Word s.val 709 (cacheSourceHeap N heap))
    (hclean : ∀i∈cacheDimensionIds,Blank s.val i)
    (hblank : ∀i∈RowIndex.ids,Blank s.val i)
    (hcontrol : ∀i∈({206,207,208,209}:Finset ℕ),Blank s.val i)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃(cost : ℕ) (t : Store) (cache : MonomialCache (profileDegree N)),
      Executes input tape monomialCacheCode cost s t ∧ cost≤monomialCacheCost N ∧
      cache.Valid (cacheSourceWidth N) r.table.getD (profileDegree N) ∧
      cache.Ready (cacheSourceWidth N) (profileDegree N) (profileDegree N).bits t ∧
      NatAssign.Bank cacheDimensionIds
        (cacheNaturalValues (profileDegree N) (cacheSourceWidth N) (cacheSourceHeap N heap)) t.val ∧
      RationalAccumulator.Word t.val 709 (cacheSourceHeap N heap) ∧
      cache.EndsBefore (cacheEndBase (profileDegree N) (cacheSourceWidth N) (cacheSourceHeap N heap)) ∧
      (∀i:Fin (profileDegree N),
        (cache.current.getD (4*i.val+6)).Width
          (profileDegree N*(cacheSourceWidth N+2*profileDegree N+3)+1) ∧
        (cache.current.getD (4*i.val+6)).Valid ∧
        (cache.current.getD (4*i.val+6)).value=(monomialCoefficient N i).value) := by
  let D := profileDegree N
  let W := cacheSourceWidth N
  let H := cacheSourceHeap N heap
  have hD : 2≤D := profileDegree_two N
  have hW : 2≤W := (by decide : (2:ℕ)≤9).trans (cacheSourceWidth_ge N)
  obtain ⟨c0,s0,e0,hc0,r0,a0,b0,bank0,z0,swap0,count0,keep0⟩ :=
    cachePreparation_executes s r hh hN hheap hclean hblank input tape
  obtain ⟨degree0,next0,alloc0⟩ := cacheDimension_seed D W H s0 bank0
  have hmeta :=  r.cache_metadata hh
  have coeff := r.coefficients
  have rawWidth : ∀k<D,(r.table.getD k).Width W := coeff.2.1
  obtain ⟨c1,s1,word,initial,e1,hc1,valid1,r1,a1,b1,z1,swap1,count1,len1,degree1,size1,width1,
    heap1,temp1,keep1,end1⟩ := cachePair_executes r.table r.input H hD hW (cacheSourceHeap_bits N heap hh)
    hmeta.1 hmeta.2 r.cache_source_end (fun k _=>coeff.1 k) rawWidth (cacheInitialValues r.values)
    ((cacheInitialValues_width r.values).mono hW) (cacheInitialValues_good r.values)
    (by simp [cacheInitialValues]) input tape r.countWord s0 r0 a0 b0 count0 degree0 alloc0 next0 z0 swap0
  have countWidth : word.length≤monomialWorkingWidth D W := by
    rw [len1]
    change D.bits.length≤monomialWorkingWidth D W
    have hd := cache_nat_bits_le D
    unfold monomialWorkingWidth monomialStorageWidth
    omega
  have control1 : ∀i∈({206,207,208,209}:Finset ℕ),Blank s1.val i := by
    intro i hi
    have hlist : i∈([206,207,208,209]:List ℕ) := by simpa only [Finset.mem_insert,Finset.mem_singleton,
      List.mem_cons,List.not_mem_nil,or_false] using hi
    apply RationalAccumulator.blank_of_eq ((keep1 i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hlist ⊢;tauto)).trans (keep0 i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hlist ⊢;tauto)))
      (hcontrol i hi)
  obtain ⟨c2,s2,e2,hc2,ready2,count2,f2⟩ := cacheStart_executes initial input tape word s1 countWidth
    r1 a1 b1 z1 swap1 count1 degree1 control1
  have bank1 := cacheNatural_after_pair D W H s0 s1 bank0 degree1 size1 width1 heap1 temp1 keep1
  have bank2 : NatAssign.Bank cacheDimensionIds (cacheNaturalValues D W H) s2.val := by
    intro i hi
    exact RationalAccumulator.word_of_eq (f2.tapes i (by
      simp only [cacheDimensionIds,Finset.mem_Icc] at hi
      simp only [monomialControlPorts,Finset.mem_insert,Finset.mem_singleton];omega)) (bank1 i hi)
  have lenD : D.bits.length≤monomialWorkingWidth D W := by rw [←len1];exact countWidth
  obtain ⟨origin,count2⟩ := count2
  obtain ⟨c3,t,_,cache,e3,hc3,valid3,ready3,end3,_,_⟩ := monomialOuter_bounded_executes initial r.table.getD rawWidth
    coeff.1 valid1 end1 D.bits (addressValue_bits D) lenD input tape origin s2 ready2 count2
  have bank3 : NatAssign.Bank cacheDimensionIds (cacheNaturalValues D W H) t.val := by
    intro i hi
    have hr := Finset.mem_Icc.mp hi
    have he : 720+(i-720)=i := by omega
    have keep := e3.protectsTape (720+(i-720)) (List.all_eq_true.mp outer_preserves_cache_metadata
      (i-720) (by simp only [List.mem_range];omega))
    rw [he] at keep
    exact RationalAccumulator.word_of_eq keep (bank2 i hi)
  have heap3 : RationalAccumulator.Word t.val 709 H := by
    have ho : monomialOuterCode.protectsTape 709=true := by decide
    exact RationalAccumulator.word_of_eq ((e3.protectsTape 709 ho).trans
      ((f2.tapes 709 (by decide)).trans ((keep1 709 (by decide)).trans (keep0 709 (by decide))))) hheap
  refine ⟨c0+(c1+(c2+c3)),t,cache,e0.seq (e1.seq (e2.seq e3)),?_,valid3,ready3,bank3,heap3,end3,?_⟩
  · rw [r.countLength] at hc1
    exact Nat.add_le_add hc0 (Nat.add_le_add hc1 (Nat.add_le_add hc2 hc3))
  · exact valid3.stored.generated_total rawWidth (fun k _=>coeff.1 k) coeff.2.2

#print axioms monomialCache_executes
end Maxwell.Continuum.Profile.Runtime
