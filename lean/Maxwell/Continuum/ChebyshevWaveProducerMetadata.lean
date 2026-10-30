import Maxwell.Continuum.ChebyshevWaveProducerSelect
import Maxwell.Cost.Structured.Determinism

/-! Runtime dimensions survive sampling and cache queries. These concrete
stored words permit charged cleanup before the next Fourier factor. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

def persistentSetupIds : Finset ℕ := dimensionIds∪{145}

theorem base_cache_preserves_metadata : ∀i∈persistentSetupIds∪{146},
    (Code.seq baseCode cacheCode).protectsTape i=true := by
  have half_literal : Parts.literal (1/2:ℚ)=⟨1,0,2⟩ := by norm_num [Parts.literal]
  simp only [cacheCode,cacheStepCode,encodedCode,cosineCode,finishControl,
    finishInstructions,halveControl,Control.prepend,List.foldr_cons,List.foldr_nil,Control.code,
    RationalDataflow.Instruction.code,half_literal]
  decide

theorem select_preserves_metadata : ∀i∈persistentSetupIds∪{146},
    cacheSelectCode.protectsTape i=true := by decide

theorem producer_persistent_metadata (Q N W : ℕ) (hQ : Q.bits.length ≤ W)
    (hN : N.bits.length ≤ W) (hW : 6 ≤ W) (input : List Bool) (tape : ℕ→Bool)
    {cost : ℕ} {s t : Store} (e : Executes input tape producerCode cost s t)
    (hs : NatAssign.Bank setupIds (initialSetup Q N) s.val) (hz : NatAssign.Scratch s.val)
    (hp : Blank s.val 144) (hc : Blank s.val 146) :
    NatAssign.Bank persistentSetupIds (setupValues Q N) t.val ∧ Blank t.val 146 := by
  cases e with
  | seq e0 e1 =>
    obtain ⟨_,_,e0',_,b0,_,_,_,_,_,_,_,c0,_⟩ :=
      cacheSetup_executes Q N W hQ hN hW input tape _ hs hz hp hc
    rcases e0'.deterministic e0 with ⟨rfl,rfl⟩
    refine ⟨?_,blank_of_eq (e1.protectsTape 146 (base_cache_preserves_metadata 146 (by decide))) c0⟩
    intro i hi
    apply word_of_eq (e1.protectsTape i (base_cache_preserves_metadata i (Finset.mem_union_left _ hi)))
    apply b0 i
    exact (show persistentSetupIds ⊆ setupIds by decide) hi

theorem selectedProducer_persistent_metadata (Q N W : ℕ) (hQ : Q.bits.length ≤ W)
    (hN : N.bits.length ≤ W) (hW : 6 ≤ W) (input : List Bool) (tape : ℕ→Bool)
    {cost : ℕ} {s t : Store} (e : Executes input tape selectedProducerCode cost s t)
    (hs : NatAssign.Bank setupIds (initialSetup Q N) s.val) (hz : NatAssign.Scratch s.val)
    (hp : Blank s.val 144) (hc : Blank s.val 146) :
    NatAssign.Bank persistentSetupIds (setupValues Q N) t.val ∧ Blank t.val 146 := by
  cases e with
  | seq e0 e1 =>
    obtain ⟨b0,c0⟩ := producer_persistent_metadata Q N W hQ hN hW input tape e0 hs hz hp hc
    refine ⟨?_,blank_of_eq (e1.protectsTape 146 (select_preserves_metadata 146 (by decide))) c0⟩
    intro i hi
    exact word_of_eq (e1.protectsTape i (select_preserves_metadata i (Finset.mem_union_left _ hi))) (b0 i hi)

#print axioms producer_persistent_metadata
#print axioms selectedProducer_persistent_metadata
end Maxwell.Continuum.Profile.WaveMachine.Runtime
