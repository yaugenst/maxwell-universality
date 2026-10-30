import Maxwell.Continuum.FourierTensorTraversalData

/-! Reloading the stored alias count and executing the complete coefficient
compiler is itself fixed code. No fresh counter is supplied for free. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

def repeatedCoefficientCode : Code :=
  .seq (WordReplace.code 1100 1099) emittedCoefficientCode

def repeatedCoefficientCost (Q N n W : ℕ) : ℕ :=
  (21*W+21)+(coefficientTimeCoefficient*(n+1)^3*(Q+N+W+64)^240+20*W+30)

theorem emittedCoefficient_tapesBelow : emittedCoefficientCode.tapesBelow 1100=true := by
  simp only [emittedCoefficientCode,Code.tapesBelow,Bool.and_eq_true]
  exact ⟨generatedCoefficient_tapesBelow,integerEmit_tapesBelow⟩

theorem repeatedCoefficient_tapesBelow : repeatedCoefficientCode.tapesBelow 1101=true := by
  simp only [repeatedCoefficientCode,Code.tapesBelow,Bool.and_eq_true]
  exact ⟨by decide,
    Code.tapesBelow_mono emittedCoefficient_tapesBelow (by decide)⟩

theorem repeatedCoefficient_executes {n B Q N W : ℕ} (d : TensorInput n B Q N W)
    (j : Fin 3→Fin d.degree) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (h : TensorState d s)
    (hj : ∀i : Fin 3,(h.values (17+i.val)).positive=(j i).val) :
    ∃cost t,∃next : TensorState d t,Executes input tape repeatedCoefficientCode cost s t ∧
      cost ≤ repeatedCoefficientCost Q N n W ∧
      (∀i : Fin 3,(next.values (17+i.val)).positive=(j i).val) ∧
      t.val.output=(Codec.int (d.coefficient j)).reverse++s.val.output := by
  obtain ⟨old,hold,hword⟩ := h.aliasBuffer
  obtain ⟨s0,e0,count0,f0⟩ := WordReplace.executes 1100 1099 (by decide) input tape
    n.bits old s h.storedAliases hword
  obtain ⟨origin,count0⟩ := count0
  have ready0 : FactorReady d.source Q N h.table h.values s0 :=
    h.factor.low_frame f0.2.2.1 (fun k hk => f0.2.2.2.2.2.1 k (by omega))
  have full0 : Ready termBank h.values s0 :=
    termReady_external h.ready (fun k hk => f0.2.2.2.2.2.1 k (by omega))
  have query0 := word_of_eq (f0.2.2.2.2.2.1 1048 (by decide)) h.queryWord
  obtain ⟨c1,t,w,output,ys,e1,hc1,ready1,full1,width1,meta1,indices1,out1,count1,len1,
      query,hquery,word1⟩ := emittedCoefficient_executes d.source Q N W h.table
    d.sourceWidth (h.metadata.widthBound d.cacheWidth) (h.metadata.separated d.cacheSeparated)
    (h.metadata.separatedFrom d.disjoint) (by simpa only [h.metadata.width] using d.fit)
    d.frequency d.amplitude d.rows d.frequencyBound j (d.coefficient_bits j) h.values h.width hj
    d.qWidth d.nWidth d.smallWidth d.precisionWidth d.gridWidth h.query h.queryWidth
    input tape n.bits origin d.aliasWidth (addressValue_bits n) s0 ready0 full0 query0 count0
  let next : TensorState d t := {
    values := w
    table := output
    factor := ready1
    ready := full1
    width := width1
    metadata := meta1.trans h.metadata
    query := query
    queryWidth := hquery
    queryWord := word1
    aliasBuffer := ⟨ys,by rw [len1];exact d.aliasWidth,origin,count1⟩
    storedAliases := word_of_eq
      ((e1.tapesBelow emittedCoefficient_tapesBelow 1100 (by decide)).trans
        (f0.2.2.2.2.2.1 1100 (by decide))) h.storedAliases
    storedDegree := word_of_eq
      ((e1.tapesBelow emittedCoefficient_tapesBelow 1110 (by decide)).trans
        (f0.2.2.2.2.2.1 1110 (by decide))) h.storedDegree }
  refine ⟨(6*old.length+15*n.bits.length+21)+c1,t,next,e0.seq e1,?_,indices1,?_⟩
  · have hindices (i : Fin 3) : (j i).val.bits.length ≤ W := by
      have hi : 17+i.val∈termBank := by
        have := i.isLt
        simp only [termBank,tensorBank,Finset.mem_insert,Finset.mem_union,Finset.mem_Ico]
        exact Or.inr (Or.inr ⟨by omega,by omega⟩)
      simpa only [hj i] using (h.width _ hi).1
    have hb := generatedCoefficientCost_polynomial Q N n W n.bits.length
      (fun i => (j i).val) d.aliasWidth hindices
    have hreload : 6*old.length+15*n.bits.length+21 ≤ 21*W+21 := by
      have hn := d.aliasWidth
      omega
    have hfinal : c1 ≤ coefficientTimeCoefficient*(n+1)^3*(Q+N+W+64)^240+20*W+30 :=
      hc1.trans (Nat.add_le_add_right (Nat.add_le_add_right hb _) _)
    exact Nat.add_le_add hreload hfinal
  · simpa only [f0.2.2.2.2.1,TensorInput.coefficient] using out1

#print axioms repeatedCoefficient_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
