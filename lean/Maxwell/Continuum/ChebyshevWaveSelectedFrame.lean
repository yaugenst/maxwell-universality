import Maxwell.Continuum.ChebyshevWaveProducerMetadata
import Maxwell.Continuum.RationalDataflowBankPartition

/-! Stored tensor factors survive both wave generation and the indexed
query. The query's source index is restored after copying its word. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem cacheSelect_tapesBelow : cacheSelectCode.tapesBelow 1049=true := by decide

theorem selectedProducer_preserves_large {input : List Bool} {tape : ℕ→Bool} {cost : ℕ}
    {s t : Store} (e : Executes input tape selectedProducerCode cost s t) (i : ℕ) (hi : 1049 ≤ i) :
    t.val.tapes i=s.val.tapes i := by
  cases e with
  | seq e0 e1 =>
    exact (e1.tapesBelow cacheSelect_tapesBelow i hi).trans (producer_preserves_tape e0 i (by omega))

theorem cacheSelect_preserves_index {input : List Bool} {tape : ℕ→Bool} {cost j : ℕ}
    {s t : Store} (e : Executes input tape cacheSelectCode cost s t)
    (hindex : Word s.val 1048 j) (hblank : Blank s.val 201) : t.val.tapes 1048=s.val.tapes 1048 := by
  cases e with
  | seq e0 e1 =>
    obtain ⟨_,e0',_,f0⟩ := WordReplace.executes 1048 201 (by decide) input tape j.bits [] s hindex
      (by simpa only [BankArray.Word,Blank,BitTape.shifted_nil] using hblank)
    rcases e0'.deterministic e0 with ⟨rfl,rfl⟩
    exact (e1.protectsTape 1048 (by decide)).trans (f0.2.2.2.2.2.1 1048 (by decide))

def tensorBank : Finset ℕ := ids∪Finset.Ico 17 32
def tensorValues (low stored : ℕ→Parts) (j : ℕ) : Parts := if j∈ids then low j else stored j

theorem selectedProducer_tensor_ready {input : List Bool} {tape : ℕ→Bool} {cost : ℕ}
    {s t : Store} {low stored : ℕ→Parts}
    (e : Executes input tape selectedProducerCode cost s t)
    (hs : Ready tensorBank stored s) (ht : Ready ids low t) : Ready tensorBank (tensorValues low stored) t := by
  apply ht.partition hs
  intro j hj hjs i hi
  have hj' : 17 ≤ j := by
    rcases Finset.mem_union.mp hj with hsmall|hlarge
    · exact (hjs hsmall).elim
    · exact (Finset.mem_Ico.mp hlarge).1
  apply selectedProducer_preserves_large e
  simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl <;> simp only [positivePort,negativePort,denominatorPort] <;> omega

#print axioms selectedProducer_preserves_large
#print axioms cacheSelect_preserves_index
#print axioms selectedProducer_tensor_ready
end Maxwell.Continuum.Profile.WaveMachine.Runtime
