import Maxwell.Continuum.ChebyshevWaveProducerFrame
import Maxwell.Continuum.ChebyshevWaveCacheSelect

/-! A fixed producer/query program. The tensor index is read from logical
register 16 after wave generation has preserved that register. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def CacheState.copyState {n Q N D W r : ℕ} {a : Table n} {q : ℚ}
    {base : ℕ→Parts} {initial : Table (2*D)} {s t : Store}
    (h : CacheState a q Q N D W base initial r s) (f : WordReplace.Frame 201 s.val t.val) :
    CacheState a q Q N D W base initial r t :=
  { h with
    ready := h.ready.outer_copy_frame f
    source := h.source.copy_frame (Or.inl rfl) f
    output := h.output.copy_frame (Or.inl rfl) f
      (h.source.copy_frame (Or.inl rfl) f).scratch (h.source.copy_frame (Or.inl rfl) f).seven
    innerBlank := blank_of_eq (f.2.2.2.2.2.1 680 (by decide)) h.innerBlank
    grid := word_of_eq (f.2.2.2.2.2.1 681 (by decide)) h.grid
    saved := fun i hi => blank_of_eq (f.2.2.2.2.2.1 i (by
      have hr := savedPorts_range i hi
      omega)) (h.saved i hi)
    power := word_of_eq (f.2.2.2.2.2.1 144 (by decide)) h.power }

def cacheSelectCode : Code := .seq (WordReplace.code 1048 201)
  (.seq cacheReadCode (.call (TapeOps.clear 201)))
def cacheSelectCost (B j : ℕ) : ℕ := 21*j.bits.length+25+cacheReadCost B

theorem cacheSelect_executes {n Q N D W : ℕ} {a : Table n} {q : ℚ}
    {base : ℕ→Parts} {initial : Table (2*D)} (hm : initial.MetadataWidth W)
    (input : List Bool) (tape : ℕ→Bool) (j : ℕ) (hj : j<D)
    (hlen : j.bits.length ≤ cacheBankWidth Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W)
    (s : Store) (h : CacheState a q Q N D W base initial 0 s)
    (hword : Word s.val 1048 j) (hblank : Blank s.val 201) :
    ∃cost t,Executes input tape cacheSelectCode cost s t ∧
      cost ≤ cacheSelectCost (cacheBankWidth Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W) j ∧
      ∃state : CacheState a q Q N D W base initial 0 t,
        state.values 8=waveCacheReal q Q N j ∧ state.values 9=waveCacheImag q Q N j ∧
        Blank t.val 201 := by
  obtain ⟨s0,e0,word0,f0⟩ := WordReplace.executes 1048 201 (by decide) input tape j.bits [] s hword
    (by simpa only [BankArray.Word,Blank,BitTape.shifted_nil] using hblank)
  let state0 := h.copyState f0
  obtain ⟨c1,s1,e1,h1,state1,real1,imag1,count1⟩ := cacheRead_executes hm input tape j hj hlen
    s0 state0 word0
  obtain ⟨origin,word1⟩ := BankArray.word_of_eq count1 word0
  obtain ⟨t,e2,tapes2,f2⟩ := WordCall.clear 201 input tape j.bits origin s1 word1
  have cf2 : WordReplace.Frame 201 s1.val t.val :=
    ⟨f2.1,f2.2.1,f2.2.2.1,f2.2.2.2.1,f2.2.2.2.2.1,
      fun i hi => f2.2.2.2.2.2.1 i hi hi,
      fun i _ _ h26 h27 => f2.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨(6*[].length+15*j.bits.length+21)+(c1+(6*j.bits.length+4)),t,
    e0.seq (e1.seq e2),?_,state1.copyState cf2,real1,imag1,?_⟩
  · unfold cacheSelectCost
    simp only [List.length_nil]
    omega
  · refine ⟨origin+j.bits.length,?_⟩
    simp only [tapes2,Function.update_self]

def selectedProducerCode : Code := .seq producerCode cacheSelectCode
def selectedProducerBound (Q N W j : ℕ) : ℕ := producerBound Q N W+
  cacheSelectCost (cacheBankWidth Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N)
    (producerWidth Q N W)) j

theorem selectedProducer_executes {n : ℕ} (a : Table n) (Q N W : ℕ)
    (b : Table (2*(waveDegree (8*Q) N+1)))
    (hm : b.MetadataWidth (producerWidth Q N W)) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (v : ℕ→Parts) (hw : WidthBank ids W v) (hv : (v 10).Valid) (hq : |(v 10).value| ≤ Q)
    (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W) (hW : 6 ≤ W)
    (j : ℕ) (hj : j<waveDegree (8*Q) N+1)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready ids v s) (hp : Phase.Runtime.Clean s.val) (hf : DyadicFloor.Clean s.val)
    (hsetup : NatAssign.Bank setupIds (initialSetup Q N) s.val)
    (ha : a.Ready s) (hb : b.OutputReady s)
    (hpower : Blank s.val 144) (hpowerCount : Blank s.val 146) (hinner : Blank s.val 680)
    (hsaved : ∀i∈savedPorts,Blank s.val i) (hindex : Word s.val 1048 j) :
    ∃cost t,Executes input tape selectedProducerCode cost s t ∧ cost ≤ selectedProducerBound Q N W j ∧
      ∃state : CacheState a (v 10).value Q N (waveDegree (8*Q) N+1) (producerWidth Q N W)
        (baseValues (waveGrid (8*Q) N) v) b 0 t,
        state.values 8=waveCacheReal (v 10).value Q N j ∧
        state.values 9=waveCacheImag (v 10).value Q N j ∧ Blank t.val 201 := by
  obtain ⟨c0,s0,e0,h0,⟨state0⟩,blank0⟩ := producer_executes a Q N W b hm hsep hdisjoint hfit
    v hw hv hq hQ hN hW input tape s hs hp hf hsetup ha hb hpower hpowerCount hinner hsaved
  have index0 := word_of_eq (producer_preserves_tape e0 1048 le_rfl) hindex
  have hjbits : j.bits.length ≤ producerWidth Q N W := by
    have hd := finalDimensions_width Q N W hQ hN hW 716 (by decide)
    rw [finalDimensions_count] at hd
    have hjd : j.bits.length ≤ dimensionWidth W := by
      have hjd' : j.bits.length ≤ (waveDegree (8*Q) N+1).bits.length := by
        simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hj.le
      exact hjd'.trans hd
    exact hjd.trans (by unfold producerWidth;omega)
  obtain ⟨c1,t,e1,h1,state1,real1,imag1,blank1⟩ := cacheSelect_executes hm input tape j hj
    (hjbits.trans (by unfold cacheBankWidth;omega)) s0 state0 index0 blank0
  exact ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,state1,real1,imag1,blank1⟩

#print axioms cacheSelect_executes
#print axioms selectedProducer_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
