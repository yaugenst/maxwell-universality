import Maxwell.Continuum.ChebyshevWaveFactorLoad

/-! The three actual axis factors of one tensor summand are produced by
fixed calls, from frequencies and indices stored in the input bank. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def AxisInputs (v : ℕ→Parts) (q : Fin 3→ℚ) (j : Fin 3→ℕ) : Prop :=
  ∀i,(v (20+i.val)).value=q i ∧ (v (20+i.val)).Valid ∧ (v (17+i.val)).positive=j i
def axisCode (i : Fin 3) : Code := .seq (factorLoadCode (20+i.val) (17+i.val)) (factorCode (25+2*i.val))
def axisCost (Q N W j : ℕ) : ℕ := factorLoadCost W+factorCost Q N W j

theorem axis_executes {n : ℕ} (a : Table n) (Q N W : ℕ)
    (b : Table (2*(waveDegree (8*Q) N+1)))
    (hm : b.MetadataWidth (producerWidth Q N W)) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (v : ℕ→Parts) (hw : WidthBank tensorBank W v) (q : Fin 3→ℚ) (j : Fin 3→ℕ)
    (hinputs : AxisInputs v q j) (hq : ∀i,|q i| ≤ Q) (hj : ∀i,j i<waveDegree (8*Q) N+1)
    (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W) (hW : 6 ≤ W)
    (hprecision : waveWorkBits (8*Q) N+7 ≤ W) (hgrid : (waveGrid (8*Q) N).bits.length ≤ W)
    (i : Fin 3) (oldIndex : ℕ) (hold : oldIndex.bits.length ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : FactorReady a Q N b v s) (hindex : Word s.val 1048 oldIndex) :
    ∃cost t w output,Executes input tape (axisCode i) cost s t ∧ cost ≤ axisCost Q N W (j i) ∧
      FactorReady a Q N output w t ∧ WidthBank tensorBank W w ∧ CacheTableMetadata output b ∧
      AxisInputs w q j ∧ w (25+2*i.val)=waveCacheReal (q i) Q N (j i) ∧
      w (26+2*i.val)=waveCacheImag (q i) Q N (j i) ∧
      (∀k,17 ≤ k → k≠25+2*i.val → k≠26+2*i.val → w k=v k) ∧ Word t.val 1048 (j i) := by
  have ilt := i.isLt
  have hf : 20+i.val∈tensorBank := by simp [tensorBank,Finset.mem_Ico];omega
  have hi : 17+i.val∈tensorBank := by simp [tensorBank,Finset.mem_Ico];omega
  obtain ⟨c0,s0,e0,h0,r0,w0,index0⟩ := factorLoad_executes a b W (20+i.val) (17+i.val) oldIndex (j i)
    hf (by omega) hi (by omega) v hw (hinputs i).2.2 hold input tape s hs hindex
  let u := Function.update v 10 (v (20+i.val))
  have u10 : u 10=v (20+i.val) := Function.update_self _ _ _
  obtain ⟨c1,t,w,output,e1,h1,r1,w1,m1,real1,imag1,_,keep,index1⟩ := factor_executes a Q N W b
    hm hsep hdisjoint hfit u w0 (by simpa only [u10] using (hinputs i).2.1)
    (by simpa only [u10,(hinputs i).1] using hq i) hQ hN hW hprecision hgrid (j i) (25+2*i.val)
    (hj i) (by omega) (by omega) input tape s0 r0 index0
  have hkeep (k : ℕ) (hk : 17 ≤ k) (hk0 : k≠25+2*i.val) (hk1 : k≠26+2*i.val) : w k=v k := by
    have h := keep k hk hk0 (by omega)
    simpa only [u,Function.update_of_ne (by omega : k≠10)] using h
  refine ⟨c0+c1,t,w,output,e0.seq e1,Nat.add_le_add h0 h1,r1,w1,m1,?_,?_,?_,hkeep,index1⟩
  · intro k
    have klt := k.isLt
    rw [hkeep (20+k.val) (by omega) (by omega) (by omega),
      hkeep (17+k.val) (by omega) (by omega) (by omega)]
    exact hinputs k
  · simpa only [u10,(hinputs i).1] using real1
  · simpa only [u10,(hinputs i).1,show 25+2*i.val+1=26+2*i.val by omega] using imag1

def axesCode : Code := .seq (axisCode 0) (.seq (axisCode 1) (axisCode 2))
def axesCost (Q N W : ℕ) (j : Fin 3→ℕ) : ℕ :=
  axisCost Q N W (j 0)+(axisCost Q N W (j 1)+axisCost Q N W (j 2))

theorem axes_executes {n : ℕ} (a : Table n) (Q N W : ℕ)
    (b : Table (2*(waveDegree (8*Q) N+1)))
    (hm : b.MetadataWidth (producerWidth Q N W)) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (v : ℕ→Parts) (hw : WidthBank tensorBank W v) (q : Fin 3→ℚ) (j : Fin 3→ℕ)
    (hinputs : AxisInputs v q j) (hq : ∀i,|q i| ≤ Q) (hj : ∀i,j i<waveDegree (8*Q) N+1)
    (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W) (hW : 6 ≤ W)
    (hprecision : waveWorkBits (8*Q) N+7 ≤ W) (hgrid : (waveGrid (8*Q) N).bits.length ≤ W)
    (oldIndex : ℕ) (hold : oldIndex.bits.length ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : FactorReady a Q N b v s) (hindex : Word s.val 1048 oldIndex) :
    ∃cost t w output,Executes input tape axesCode cost s t ∧ cost ≤ axesCost Q N W j ∧
      FactorReady a Q N output w t ∧ WidthBank tensorBank W w ∧ CacheTableMetadata output b ∧
      AxisInputs w q j ∧
      (∀i : Fin 3,w (25+2*i.val)=waveCacheReal (q i) Q N (j i) ∧
        w (26+2*i.val)=waveCacheImag (q i) Q N (j i)) ∧
      w 23=v 23 ∧ w 24=v 24 ∧ w 31=v 31 ∧ Word t.val 1048 (j 2) := by
  have jwidth (i : Fin 3) : (j i).bits.length ≤ W := by
    have hi : 17+i.val∈tensorBank := by have := i.isLt;simp [tensorBank,Finset.mem_Ico];omega
    simpa only [(hinputs i).2.2] using (hw (17+i.val) hi).1
  obtain ⟨c0,s0,v0,b0,e0,h0,r0,w0,m0,in0,re0,im0,k0,index0⟩ := axis_executes a Q N W b hm hsep
    hdisjoint hfit v hw q j hinputs hq hj hQ hN hW hprecision hgrid 0 oldIndex hold input tape s hs hindex
  obtain ⟨c1,s1,v1,b1,e1,h1,r1,w1,m1,in1,re1,im1,k1,index1⟩ := axis_executes a Q N W b0
    (m0.widthBound hm) (m0.separated hsep) (m0.separatedFrom hdisjoint) (by simpa only [m0.width] using hfit)
    v0 w0 q j in0 hq hj hQ hN hW hprecision hgrid 1 (j 0) (jwidth 0) input tape s0 r0 index0
  obtain ⟨c2,t,w,output,e2,h2,r2,w2,m2,in2,re2,im2,k2,index2⟩ := axis_executes a Q N W b1
    ((m1.trans m0).widthBound hm) ((m1.trans m0).separated hsep)
    ((m1.trans m0).separatedFrom hdisjoint) (by simpa only [m1.width,m0.width] using hfit)
    v1 w1 q j in1 hq hj hQ hN hW hprecision hgrid 2 (j 1) (jwidth 1) input tape s1 r1 index1
  refine ⟨c0+(c1+c2),t,w,output,e0.seq (e1.seq e2),Nat.add_le_add h0 (Nat.add_le_add h1 h2),
    r2,w2,m2.trans (m1.trans m0),in2,?_,?_,?_,?_,index2⟩
  · intro i
    fin_cases i
    · change w 25=waveCacheReal (q 0) Q N (j 0) ∧ w 26=waveCacheImag (q 0) Q N (j 0)
      rw [k2 25 (by decide) (by decide) (by decide),k2 26 (by decide) (by decide) (by decide),
        k1 25 (by decide) (by decide) (by decide),k1 26 (by decide) (by decide) (by decide)]
      exact ⟨re0,im0⟩
    · change w 27=waveCacheReal (q 1) Q N (j 1) ∧ w 28=waveCacheImag (q 1) Q N (j 1)
      rw [k2 27 (by decide) (by decide) (by decide),k2 28 (by decide) (by decide) (by decide)]
      exact ⟨re1,im1⟩
    · exact ⟨re2,im2⟩
  all_goals
    first
      | exact (k2 23 (by decide) (by decide) (by decide)).trans
          ((k1 23 (by decide) (by decide) (by decide)).trans (k0 23 (by decide) (by decide) (by decide)))
      | exact (k2 24 (by decide) (by decide) (by decide)).trans
          ((k1 24 (by decide) (by decide) (by decide)).trans (k0 24 (by decide) (by decide) (by decide)))
      | exact (k2 31 (by decide) (by decide) (by decide)).trans
          ((k1 31 (by decide) (by decide) (by decide)).trans (k0 31 (by decide) (by decide) (by decide)))

#print axioms axes_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
