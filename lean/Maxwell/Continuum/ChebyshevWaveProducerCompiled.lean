import Maxwell.Continuum.ChebyshevWaveProducerCost

/-! Compiled execution and the exact output table of the fixed producer. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem producer_compiled_run {n : ℕ} (a : Table n) (Q N W : ℕ)
    (b : Table (2*(waveDegree (8*Q) N+1)))
    (hm : b.MetadataWidth (producerWidth Q N W)) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hfit : waveWorkBits (8*Q) N+7≤addressValue b.width)
    (v : ℕ→Parts) (hw : WidthBank ids W v) (hv : (v 10).Valid) (hq : |(v 10).value|≤Q)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (hW : 6≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready ids v s) (hp : Phase.Runtime.Clean s.val) (hf : DyadicFloor.Clean s.val)
    (hsetup : NatAssign.Bank setupIds (initialSetup Q N) s.val)
    (ha : a.Ready s) (hb : b.OutputReady s)
    (hpower : Blank s.val 144) (hpowerCount : Blank s.val 146) (hinner : Blank s.val 680)
    (hsaved : ∀i∈savedPorts,Blank s.val i) :
    ∃t : Store,
      (runPriced (producerCode.compile.next input tape) (producerBound Q N W+1) s.val).finished=
        some (t.place producerCode.size) ∧
      (runPriced (producerCode.compile.next input tape) (producerBound Q N W+1) s.val).instructions≤
        producerTimeCoefficient*(Q+N+W+64)^240 ∧
      ∃output : Table (2*(waveDegree (8*Q) N+1)),output.OutputReady t ∧
        CacheTableMetadata output b ∧
        (∀j : Fin (waveDegree (8*Q) N+1),
          output.get ⟨2*j.val,by omega⟩=waveCacheReal (v 10).value Q N j ∧
          output.get ⟨2*j.val+1,by omega⟩=waveCacheImag (v 10).value Q N j) ∧
        a.Ready t ∧ Blank t.val 201 := by
  obtain ⟨cost,t,e,hcost,⟨state⟩,hblank⟩ := producer_executes a Q N W b hm hsep hdisjoint hfit
    v hw hv hq hQ hN hW input tape s hs hp hf hsetup ha hb hpower hpowerCount hinner hsaved
  obtain ⟨hrun,hsteps⟩ := e.compiled_run (producerBound Q N W+1) (by omega)
  refine ⟨t,hrun,hsteps ▸ hcost.trans (producerBound_polynomial Q N W),state.table,
    state.output,state.tableMetadata,?_,state.source,hblank⟩
  intro j
  exact state.final_coefficient j j.isLt

#print axioms producer_compiled_run
end Maxwell.Continuum.Profile.WaveMachine.Runtime
