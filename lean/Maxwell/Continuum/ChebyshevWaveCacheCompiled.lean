import Maxwell.Continuum.ChebyshevWaveCacheCost

/-! The fixed compiled wave-cache program, with every coefficient produced
and written by its runtime loop. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def cacheBound (Q N D W : ℕ) : ℕ :=
  2^7200*(D+1)*(waveGrid (8*Q) N+1)^15*(frequencyScale Q (waveWorkBits (8*Q) N) W)^56

theorem cache_compiled_run {n : ℕ} (a : Table n) (q : ℚ) (Q N D W : ℕ)
    (b : Table (2*D)) (hm : b.MetadataWidth W) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hq : |q| ≤ Q) (hD : D ≤ waveDegree (8*Q) N+1)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (base : ℕ→Parts) (hbase : WidthBank ids W base) (hg : Good ids base)
    (hW : 1 ≤ W) (hgrid : (waveGrid (8*Q) N).bits.length ≤ W) (hcount : D.bits.length ≤ W)
    (hone : base 15=⟨1,0,1⟩) (hi : SumInput (waveGrid (8*Q) N) q 0 0 base)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : LoopReady Q (waveWorkBits (8*Q) N) base s)
    (ha : a.Ready s) (hb : b.OutputReady s) (hn : Word s.val 201 D)
    (hz : Blank s.val 680) (hgridWord : Word s.val 681 (waveGrid (8*Q) N))
    (hsaved : ∀i∈savedPorts,Blank s.val i) (hpower : Word s.val 144 (2^waveWorkBits (8*Q) N)) :
    ∃t : Store,
      (runPriced (cacheCode.compile.next input tape) (cacheBound Q N D W+1) s.val).finished=
        some (t.place cacheCode.size) ∧
      (runPriced (cacheCode.compile.next input tape) (cacheBound Q N D W+1) s.val).instructions≤
        cacheBound Q N D W ∧
      Nonempty (CacheState a q Q N D W base b 0 t) ∧ Blank t.val 201 := by
  obtain ⟨c,t,e,hc,state,hblank⟩ := cache_executes a q Q N D W b hm hsep hdisjoint hq hD hfit
    base hbase hg hW hgrid hcount hone hi input tape s hs ha hb hn hz hgridWord hsaved hpower
  have hbound : c≤cacheBound Q N D W := hc.trans
    (cache_cost_polynomial Q (waveWorkBits (8*Q) N) W (waveGrid (8*Q) N) D hgrid hcount)
  obtain ⟨hrun,hsteps⟩ := e.compiled_run (cacheBound Q N D W+1) (by omega)
  exact ⟨t,hrun,hsteps ▸ hbound,state,hblank⟩

theorem CacheState.final_coefficient {n Q N D W : ℕ} {a : Table n} {q : ℚ}
    {base : ℕ→Parts} {initial : Table (2*D)} {s : Store}
    (h : CacheState a q Q N D W base initial 0 s) (j : ℕ) (hj : j<D) :
    h.table.get ⟨2*j,by omega⟩=waveCacheReal q Q N j ∧
      h.table.get ⟨2*j+1,by omega⟩=waveCacheImag q Q N j :=
  h.contents j hj (Nat.zero_le _)

#print axioms cache_compiled_run
#print axioms CacheState.final_coefficient
end Maxwell.Continuum.Profile.WaveMachine.Runtime
