import Maxwell.Continuum.ChebyshevWaveCacheCompiled
import Maxwell.Continuum.RationalDataflowCachedPlan

/-! Fetching the requested complex coefficient from the table that the
wave program actually generated. No coefficient table is supplied as an oracle. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def cacheReadPlan : List (ℕ×ℕ) := [(0,8),(1,9)]
def cacheReadCode : Code := cachedPlanCode 2 cacheReadPlan
def cacheReadCost (B : ℕ) : ℕ := rowPlanCost 2 1 B cacheReadPlan

theorem cacheRead_protects_four : cacheReadCode.protectsTape 4=true := by decide

theorem LoopReady.cachedPlan_frame {Q P : ℕ} {v w : ℕ→Parts} {s t : Store}
    (h : LoopReady Q P v s) (f : RowPlanFrame ids s.val t.val) (hr : Ready ids w t)
    (h4 : t.val.tapes 4=s.val.tapes 4) (hz : ∀i∈RowIndex.ids,Blank t.val i) :
    LoopReady Q P w t := by
  have keep (i : ℕ) (hlo : 10 ≤ i) (hhi : i<1000) (hid : i∉RowIndex.ids) := f.tapes i hlo (by
    intro hi
    obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hi
    have hp := positivePort_ge k
    have hn := negativePort_ge k
    have hd := denominatorPort_ge k
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hk
    omega) hid
  refine ⟨hr,?_,⟨blank_of_eq h4 h.floor.1,?_⟩,?_,
    word_of_eq (keep 652 (by decide) (by decide) (by decide)) h.rangeWord,
    word_of_eq (keep 653 (by decide) (by decide) (by decide)) h.precisionWord⟩
  · intro i hi
    have hip : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hd : ∀i∈PhaseMachine.Runtime.ids,10 ≤ i ∧ i<1000 ∧ i∉RowIndex.ids := by decide
    have hd' := hd i hip
    exact blank_of_eq (keep i hd'.1 hd'.2.1 hd'.2.2) (h.phase i hi)
  · intro i hi
    by_cases hid : i∈RowIndex.ids
    · exact hz i hid
    · have hh : 10 ≤ i ∧ i<1000 := by
        simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton] at hi
        omega
      exact blank_of_eq (keep i hh.1 hh.2 hid) (h.floor.2 i hi)
  · intro i hi
    have hp := parameterIds_range i hi
    have hn : i∉RowIndex.ids := by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact word_of_eq (keep i (by omega) (by omega) hn) (h.parameters i hi)

theorem cacheRead_executes {n Q N D W : ℕ} {a : Table n} {q : ℚ}
    {base : ℕ→Parts} {initial : Table (2*D)} (hm : initial.MetadataWidth W)
    (input : List Bool) (tape : ℕ→Bool) (j : ℕ) (hj : j<D)
    (hlen : j.bits.length ≤ cacheBankWidth Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W)
    (s : Store) (h : CacheState a q Q N D W base initial 0 s) (hword : Word s.val 201 j) :
    ∃cost t,Executes input tape cacheReadCode cost s t ∧
      cost ≤ cacheReadCost (cacheBankWidth Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W) ∧
      ∃state : CacheState a q Q N D W base initial 0 t,
        state.values 8=waveCacheReal q Q N j ∧ state.values 9=waveCacheImag q Q N j ∧
        t.val.tapes 201=s.val.tapes 201 := by
  let B := cacheBankWidth Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W
  have hb : h.table.MetadataWidth B := (h.tableMetadata.widthBound hm).mono (by unfold B cacheBankWidth;omega)
  obtain ⟨c,t,e,hc,rt,wt,bt,zt,ft⟩ := cachedPlan_executes h.table ids 2 1 B cacheReadPlan
    (by simp [cacheReadPlan,ids]) (by simp [cacheReadPlan]) hb h.values h.bankWidth
    input tape j.bits hlen
    (by intro x hx;simp only [cacheReadPlan,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> simp only [addressValue_bits] <;> omega)
    s h.ready.ready h.output hword (fun i hi => h.ready.floor.2 i (by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton]
      omega))
  let w := rowPlanValues h.table 2 (addressValue j.bits) cacheReadPlan h.values
  have keep (i : ℕ) (hi : 10 ≤ i) (hp : i∉ports ids) (hr : i∉RowIndex.ids) := ft.tapes i hi hp hr
  have hmeta : SameMetadata w base := by
    intro i hi
    have hh : i≠8 ∧ i≠9 := by
      simp only [cacheMetadata,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    simpa only [w,rowPlanValues,cacheReadPlan,Function.update_of_ne hh.1,
      Function.update_of_ne hh.2] using h.metadata i hi
  let state : CacheState a q Q N D W base initial 0 t := { h with
    values := w
    ready := h.ready.cachedPlan_frame ft rt (e.protectsTape 4 cacheRead_protects_four) zt
    bankWidth := wt
    metadata := hmeta
    source := h.source.cachedPlan_frame ft bt.scratch bt.seven
    output := bt
    innerBlank := blank_of_eq (keep 680 (by decide) (by decide) (by decide)) h.innerBlank
    grid := word_of_eq (keep 681 (by decide) (by decide) (by decide)) h.grid
    saved := by
      intro i hi
      have hr := savedPorts_range i hi
      apply blank_of_eq (keep i (by omega) _ _) (h.saved i hi)
      · simp only [ports,ids,Finset.mem_biUnion,Finset.mem_range,cellPorts,Finset.mem_insert,
          Finset.mem_singleton,positivePort,negativePort,denominatorPort]
        omega
      · simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton]
        omega
    power := word_of_eq (keep 144 (by decide) (by decide) (by decide)) h.power }
  have coeff := h.final_coefficient j hj
  refine ⟨c,t,e,hc,state,?_,?_,ft.counter⟩
  · change w 8=waveCacheReal q Q N j
    simpa [w,rowPlanValues,cacheReadPlan,Table.getD,show 2*j<2*D by omega] using coeff.1
  · change w 9=waveCacheImag q Q N j
    simpa [w,rowPlanValues,cacheReadPlan,Table.getD,show 2*j+1<2*D by omega] using coeff.2

#print axioms cacheRead_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
