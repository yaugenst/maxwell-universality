import Maxwell.Continuum.FourierTensorAliasLoop
import Maxwell.Continuum.CompactTemplateReal

/-! One fixed Boolean program generates the exact canonical integer
numerator of an output Chebyshev tensor coefficient. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
open scoped BigOperators
set_option maxHeartbeats 5500000
set_option maxRecDepth 16384

theorem aliasNumerator_sum {n B : ℕ} (q : Fin n→Fin 3→ℚ) (amp : Fin n→ComplexDyadic B)
    (Q N : ℕ) (j : Fin 3→Fin (waveDegree (8*Q) N)) :
    (∑r∈Finset.Ico 0 n,aliasNumerator q amp Q N (fun i => (j i).val) r)=
      ((realFourierTensorCoefficient Finset.univ q amp Q N j).numerator:ℚ) := by
  rw [←Finset.range_eq_Ico,←Fin.sum_univ_eq_sum_range]
  simp only [realFourierTensorCoefficient,fourierTensorCoefficient,complexDyadicSum,Int.cast_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [aliasNumerator,dite_eq_left r.isLt,tensorWaveCoefficient]

def generatedCoefficientCode : Code :=
  .seq (NatAssign.code (literalStage 32 (Parts.literal 0)))
    (.seq aliasLoopCode (IntegerCanonical.code 32 32))
def generatedCoefficientCost (Q N n W k : ℕ) (j : Fin 3→ℕ) : ℕ :=
  RationalDataflow.stageCost W+aliasLoopCost Q N n W k j+
    operationCost (aliasAccumulatorWidth n 0 W)

theorem generatedCoefficient_executes {n B : ℕ} (a : Table (5*n)) (Q N W : ℕ)
    (b : Table (2*(waveDegree (8*Q) N+1))) (hma : a.MetadataWidth W)
    (hm : b.MetadataWidth (producerWidth Q N W)) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (q : Fin n→Fin 3→ℚ) (amp : Fin n→ComplexDyadic B) (hrows : FourierRows a q amp)
    (hq : ∀r i,|q r i| ≤ Q) (j : Fin 3→Fin (waveDegree (8*Q) N))
    (v : ℕ→Parts) (hw : WidthBank termBank W v)
    (hindices : ∀i : Fin 3,(v (17+i.val)).positive=(j i).val)
    (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W) (hW : 6 ≤ W)
    (hprecision : waveWorkBits (8*Q) N+7 ≤ W) (hgrid : (waveGrid (8*Q) N).bits.length ≤ W)
    (oldIndex : ℕ) (hold : oldIndex.bits.length ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (hlen : xs.length ≤ W)
    (hn : addressValue xs=n) (s : Store) (hs : FactorReady a Q N b v s)
    (hr : Ready termBank v s) (hindex : Word s.val 1048 oldIndex)
    (hcount : s.val.tapes 1099=BitTape.shifted xs origin) :
    ∃cost t w output finalWord,Executes input tape generatedCoefficientCode cost s t ∧
      cost ≤ generatedCoefficientCost Q N n W xs.length (fun i => (j i).val) ∧
      FactorReady a Q N output w t ∧ Ready termBank w t ∧ WidthBank tensorBank W w ∧
      (w 32).Width (aliasAccumulatorWidth n 0 W+1) ∧ CacheTableMetadata output b ∧
      (∀i : Fin 3,(w (17+i.val)).positive=(j i).val) ∧
      w 32=Parts.literal ((realFourierTensorCoefficient Finset.univ q amp Q N j).numerator:ℚ) ∧
      t.val.tapes 1099=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      ∃query,query.bits.length ≤ W ∧ Word t.val 1048 query := by
  have hzero : (Parts.literal (0:ℚ)).Width W :=
    (show (Parts.literal (0:ℚ)).Width 1 by unfold Parts.Width Parts.literal;decide).mono (by omega)
  obtain ⟨c0,s0,e0,h0,r0,f0⟩ := literal_executes termBank 32 (by simp [termBank])
    (Parts.literal 0) v W hzero hw input tape s hr
  let start := Function.update v 32 (Parts.literal 0)
  have wstart : WidthBank termBank W start := hw.update 32 hzero
  have startFactor : FactorReady a Q N b start s0 := hs.term_frame f0 r0
  have hsmall : WidthBank tensorBank W start := fun i hi => wstart i (Finset.mem_insert_of_mem hi)
  have startIndices (i : Fin 3) : (start (17+i.val)).positive=(j i).val := by
    have hi := i.isLt
    simpa only [start,Function.update_of_ne (by omega : 17+i.val≠32)] using hindices i
  obtain ⟨c1,s1,finalWord,e1,h1,⟨state⟩,count1,length1⟩ := aliasLoop_executes a Q N W b hma hm hsep
    hdisjoint hfit q amp hrows hq (fun i => (j i).val) (fun i => by have := (j i).isLt;omega)
    start hsmall (wstart 32 (by simp [termBank])) (by exact Parts.literal_valid 0) rfl startIndices
    hQ hN hW hprecision hgrid oldIndex hold input tape xs origin hlen hn s0 startFactor r0
    (word_of_eq (f0.tapes 1048 (by decide)) hindex)
    ((f0.tapes 1099 (by decide)).trans hcount)
  have hWA : W ≤ aliasAccumulatorWidth n 0 W := by unfold aliasAccumulatorWidth;omega
  have wfull : WidthBank termBank (aliasAccumulatorWidth n 0 W) state.values := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact state.accumulatorWidth
    · exact (state.smallWidth i hi).mono hWA
  obtain ⟨c2,t,e2,h2,r2,f2⟩ := IntegerCanonical.executes termBank 32 32 (by simp [termBank])
    (by simp [termBank]) state.values (aliasAccumulatorWidth n 0 W) wfull input tape s1 state.fullReady
  let w := Function.update state.values 32 (IntegerCanonical.result (state.values 32))
  have he : w 32=Parts.literal ((realFourierTensorCoefficient Finset.univ q amp Q N j).numerator:ℚ) := by
    rw [show w 32=IntegerCanonical.result (state.values 32) from Function.update_self _ _ _,
      IntegerCanonical.result_eq_literal_value _ state.accumulatorDenominator,state.sumValue,
      aliasNumerator_sum]
    simp only [start,Function.update_self,Parts.literal_value,zero_add]
  refine ⟨c0+(c1+c2),t,w,state.table,finalWord,e0.seq (e1.seq e2),?_,
    state.ready.term_frame f2 r2,r2,?_,?_,state.metadata,?_,he,
    (f2.tapes 1099 (by decide)).trans count1,length1,
    state.queryIndex,state.queryWidth,word_of_eq (f2.tapes 1048 (by decide)) state.queryWord⟩
  · unfold generatedCoefficientCost
    omega
  · intro i hi
    have hi32 : i≠32 := by intro h;subst i;exact (by decide : 32∉tensorBank) hi
    simpa only [w,Function.update_of_ne hi32] using state.smallWidth i hi
  · simpa only [w,Function.update_self] using
      IntegerCanonical.result_width (aliasAccumulatorWidth n 0 W) (state.values 32) state.accumulatorWidth
  · intro i
    have hi := i.isLt
    simpa only [w,Function.update_of_ne (by omega : 17+i.val≠32)] using state.indices i

#print axioms generatedCoefficient_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
