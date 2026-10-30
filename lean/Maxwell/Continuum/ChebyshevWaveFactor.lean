import Maxwell.Continuum.ChebyshevWaveFactorFinish

/-! The complete reusable wave-factor call: generate, select, save the
integer pair, and restore the represented workspace for the next axis. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def factorCode (target : ℕ) : Code := .seq selectedProducerCode (factorFinishCode target)
def factorBankWidth (Q N W : ℕ) : ℕ :=
  cacheBankWidth Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) (producerWidth Q N W)
def factorCost (Q N W j : ℕ) : ℕ := selectedProducerBound Q N W j+
  factorFinishCost Q N W (factorBankWidth Q N W)

theorem factor_executes {n : ℕ} (a : Table n) (Q N W : ℕ)
    (b : Table (2*(waveDegree (8*Q) N+1)))
    (hm : b.MetadataWidth (producerWidth Q N W)) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (v : ℕ→Parts) (hw : WidthBank tensorBank W v) (hv : (v 10).Valid) (hq : |(v 10).value| ≤ Q)
    (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W) (hW : 6 ≤ W)
    (hprecision : waveWorkBits (8*Q) N+7 ≤ W) (hgrid : (waveGrid (8*Q) N).bits.length ≤ W)
    (j target : ℕ) (hj : j<waveDegree (8*Q) N+1) (ht : 17 ≤ target) (ht' : target+1<32)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : FactorReady a Q N b v s) (hindex : Word s.val 1048 j) :
    ∃cost t w output,Executes input tape (factorCode target) cost s t ∧ cost ≤ factorCost Q N W j ∧
      FactorReady a Q N output w t ∧ WidthBank tensorBank W w ∧ CacheTableMetadata output b ∧
      w target=waveCacheReal (v 10).value Q N j ∧ w (target+1)=waveCacheImag (v 10).value Q N j ∧
      w 10=v 10 ∧ (∀i,17 ≤ i → i≠target → i≠target+1 → w i=v i) ∧ Word t.val 1048 j := by
  have sub : ids⊆tensorBank := Finset.subset_union_left
  have hwlow : WidthBank ids W v := fun i hi => hw i (sub hi)
  obtain ⟨c0,s0,e0,h0,⟨state0⟩,blank0⟩ := producer_executes a Q N W b hm hsep hdisjoint hfit
    v hwlow hv hq hQ hN hW input tape s (hs.ready.restrict sub) hs.phase hs.floor hs.setup
    hs.source hs.output hs.power hs.powerCount hs.inner hs.saved
  have index0 := word_of_eq (producer_preserves_tape e0 1048 le_rfl) hindex
  have hjbits : j.bits.length ≤ factorBankWidth Q N W := by
    have hd := finalDimensions_width Q N W hQ hN hW 716 (by decide)
    rw [finalDimensions_count] at hd
    have hjd : j.bits.length ≤ (waveDegree (8*Q) N+1).bits.length := by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hj.le
    exact (hjd.trans hd).trans (by unfold factorBankWidth cacheBankWidth producerWidth;omega)
  obtain ⟨c1,s1,e1,h1,state1,real1,imag1,blank1⟩ := cacheSelect_executes hm input tape j hj hjbits
    s0 state0 index0 blank0
  have e01 : Executes input tape selectedProducerCode (c0+c1) s s1 := e0.seq e1
  have h01 : c0+c1 ≤ selectedProducerBound Q N W j := Nat.add_le_add h0 h1
  have index1 := word_of_eq (cacheSelect_preserves_index e1 index0 blank0) index0
  let u := tensorValues state1.values v
  have ru : Ready tensorBank u s1 := selectedProducer_tensor_ready e01 hs.ready state1.ready.ready
  have hu : WidthBank tensorBank (factorBankWidth Q N W) u := by
    intro i hi
    change (if i∈ids then state1.values i else v i).Width _
    by_cases his : i∈ids
    · simp only [ite_eq_left his];exact state1.bankWidth i his
    · simp only [ite_eq_right his]
      exact (hw i hi).mono (by unfold factorBankWidth cacheBankWidth producerWidth;omega)
  obtain ⟨persistent1,count1⟩ := selectedProducer_persistent_metadata Q N W hQ hN hW input tape e01
    hs.setup hs.ready.2 hs.power hs.powerCount
  have complete1 := state1.completed_bank persistent1 blank1 count1
  obtain ⟨c2,t,e2,h2,ready2,index2⟩ := factorFinish_executes a state1.table Q N W (factorBankWidth Q N W)
    target hQ hN hW ht ht' u hu input tape s1 ru state1.ready.phase state1.ready.floor complete1
    state1.source state1.output state1.innerBlank state1.saved
  have u8 : u 8=waveCacheReal (v 10).value Q N j := by simpa only [u,tensorValues,show 8∈ids by decide,ite_true] using real1
  have u9 : u 9=waveCacheImag (v 10).value Q N j := by simpa only [u,tensorValues,show 9∈ids by decide,ite_true] using imag1
  have um : SameMetadata u (baseValues (waveGrid (8*Q) N) v) := by
    intro i hi
    have hil : i∈ids := by
      simp only [cacheMetadata,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    simpa only [u,tensorValues,ite_eq_left hil] using state1.metadata i hi
  have ub := baseValues_width (waveGrid (8*Q) N) W v (hwlow 10 (by decide)) hgrid (by omega)
  have fits := waveRoundedCoefficient_bits (v 10).value Q N j hq (by omega)
  have u8width : (u 8).Width W := by
    rw [u8]
    exact (integer_literal_width _ _ fits.1 (by omega)).mono hprecision
  have u9width : (u 9).Width W := by
    rw [u9]
    exact (integer_literal_width _ _ fits.2 (by omega)).mono hprecision
  have uhigh (i : ℕ) (hi : 17 ≤ i) : u i=v i := by
    simp only [u,tensorValues,ids,Finset.mem_range,show ¬i<16 by omega,ite_false]
  have width2 := factorValues_width target W ht (by omega) u _ um ub u8width u9width
    (fun i hi => by rw [uhigh i (Finset.mem_Ico.mp hi).1];exact hw i (Finset.mem_union_right _ hi))
  have saved2 := factorValues_saved target ht u
  refine ⟨(c0+c1)+c2,t,factorValues target u,state1.table,e01.seq e2,Nat.add_le_add h01 h2,
    ready2,width2,state1.tableMetadata,saved2.1.trans u8,saved2.2.trans u9,?_,?_,word_of_eq index2 index1⟩
  · have m10 := um 10 (by decide)
    simpa [factorValues,cacheResetValues_eq,factorSaveValues,show 10≠target by omega,
      show 10≠target+1 by omega,baseValues_eq] using m10
  · intro i hi hit hit'
    exact (factorValues_high target u i hi hit hit').trans (uhigh i hi)

#print axioms factor_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
