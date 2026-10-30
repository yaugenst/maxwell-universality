import Maxwell.Continuum.FourierTensorCoefficientCost
import Maxwell.Continuum.FourierTensorOutputFrame
import Maxwell.Continuum.FourierTensorEmitFrame

/-! Complete fixed generation and emission of one tensor coefficient,
restoring the small reusable workspace for the next output coefficient. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

def emittedCoefficientCode : Code := .seq generatedCoefficientCode (IntegerEmit.code 32)
def emittedCoefficientCost (Q N n W k : ℕ) (j : Fin 3→ℕ) : ℕ :=
  generatedCoefficientCost Q N n W k j+20*W+30

theorem emittedCoefficient_executes {n B : ℕ} (a : Table (5*n)) (Q N W : ℕ)
    (b : Table (2*(waveDegree (8*Q) N+1))) (hma : a.MetadataWidth W)
    (hm : b.MetadataWidth (producerWidth Q N W)) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (q : Fin n→Fin 3→ℚ) (amp : Fin n→ComplexDyadic B) (hrows : FourierRows a q amp)
    (hq : ∀r i,|q r i| ≤ Q) (j : Fin 3→Fin (waveDegree (8*Q) N))
    (hbits : (realFourierTensorCoefficient Finset.univ q amp Q N j).numeratorBits ≤ W)
    (v : ℕ→Parts) (hw : WidthBank termBank W v)
    (hindices : ∀i : Fin 3,(v (17+i.val)).positive=(j i).val)
    (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W) (hW : 6 ≤ W)
    (hprecision : waveWorkBits (8*Q) N+7 ≤ W) (hgrid : (waveGrid (8*Q) N).bits.length ≤ W)
    (oldIndex : ℕ) (hold : oldIndex.bits.length ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (hlen : xs.length ≤ W)
    (hn : addressValue xs=n) (s : Store) (hs : FactorReady a Q N b v s)
    (hr : Ready termBank v s) (hindex : Word s.val 1048 oldIndex)
    (hcount : s.val.tapes 1099=BitTape.shifted xs origin) :
    ∃cost t w output finalWord,Executes input tape emittedCoefficientCode cost s t ∧
      cost ≤ emittedCoefficientCost Q N n W xs.length (fun i => (j i).val) ∧
      FactorReady a Q N output w t ∧ Ready termBank w t ∧ WidthBank termBank W w ∧
      CacheTableMetadata output b ∧ (∀i : Fin 3,(w (17+i.val)).positive=(j i).val) ∧
      t.val.output=(Codec.int (realFourierTensorCoefficient Finset.univ q amp Q N j).numerator).reverse++s.val.output ∧
      t.val.tapes 1099=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      ∃query,query.bits.length ≤ W ∧ Word t.val 1048 query := by
  obtain ⟨c0,s0,w,output,ys,e0,h0,f0,r0,w0,_,meta0,indices0,value0,count0,length0,query,hquery,word0⟩ :=
    generatedCoefficient_executes a Q N W b hma hm hsep hdisjoint hfit q amp hrows hq j
      v hw hindices hQ hN hW hprecision hgrid oldIndex hold input tape xs origin hlen hn s hs hr hindex hcount
  have width : WidthBank termBank W w := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · rw [value0]
      exact integer_literal_width _ W hbits (by omega)
    · exact w0 i hi
  obtain ⟨t,e1,ho,f1,r1,tapes⟩ := emitCoefficient_executes w _ value0 input tape s0 f0 r0
  have hnat : (realFourierTensorCoefficient Finset.univ q amp Q N j).numerator.natAbs.bits.length ≤ W := by
    unfold Dyadic.numeratorBits signedBitLength at hbits
    rw [Codec.unsignedBitLength_eq_size,←Nat.size_eq_bits_len] at hbits
    omega
  refine ⟨c0+(20*(realFourierTensorCoefficient Finset.univ q amp Q N j).numerator.natAbs.bits.length+30),
    t,w,output,ys,e0.seq e1,?_,f1,r1,width,meta0,indices0,?_,
    (congrFun tapes 1099).trans count0,length0,query,hquery,word_of_eq (congrFun tapes 1048) word0⟩
  · unfold emittedCoefficientCost
    omega
  · exact ho.trans (congrArg _ (generatedCoefficient_output e0))

#print axioms emittedCoefficient_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
