import Maxwell.Continuum.FourierTensorCoefficientOutput
import Maxwell.Continuum.FourierTensorExternalFrame
import Maxwell.Continuum.FourierTensorTraversalFootprint
import Maxwell.Continuum.FourierTensorBits
import Maxwell.Cost.WordReplace

/-! Concrete finite input data and the represented, reusable workspace of
the tensor compiler. The amplitude condition is an explicit finite sum. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
open scoped BigOperators
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

structure TensorInput (n B Q N W : ℕ) where
  source : Table (5*n)
  cache : Table (2*(waveDegree (8*Q) N+1))
  sourceWidth : source.MetadataWidth W
  cacheWidth : cache.MetadataWidth (producerWidth Q N W)
  cacheSeparated : cache.Separated
  disjoint : source.SeparatedFrom cache
  fit : waveWorkBits (8*Q) N+7 ≤ addressValue cache.width
  frequency : Fin n→Fin 3→ℚ
  amplitude : Fin n→ComplexDyadic B
  rows : FourierRows source frequency amplitude
  frequencyBound : ∀r i,|frequency r i| ≤ Q
  massExponent : ℕ
  mass : (∑r,‖complexDyadicValue (amplitude r)‖) ≤ (2:ℝ)^massExponent
  coefficientWidth : B+3*waveWorkBits (8*Q) N+massExponent+16 ≤ W
  qWidth : Q.bits.length ≤ W
  nWidth : N.bits.length ≤ W
  aliasWidth : n.bits.length ≤ W
  degreeWidth : (waveDegree (8*Q) N).bits.length ≤ W
  smallWidth : 6 ≤ W
  precisionWidth : waveWorkBits (8*Q) N+7 ≤ W
  gridWidth : (waveGrid (8*Q) N).bits.length ≤ W

namespace TensorInput
variable {n B Q N W : ℕ} (d : TensorInput n B Q N W)

def degree (_d : TensorInput n B Q N W) : ℕ := waveDegree (8*Q) N
def coefficient (j : Fin 3→Fin d.degree) : ℤ :=
  (realFourierTensorCoefficient Finset.univ d.frequency d.amplitude Q N j).numerator

theorem coefficient_bits (j : Fin 3→Fin d.degree) :
    (realFourierTensorCoefficient Finset.univ d.frequency d.amplitude Q N j).numeratorBits ≤ W := by
  exact (fourierTensorCoefficient_bits Finset.univ d.frequency d.amplitude Q N d.massExponent
    (fun r _ i => d.frequencyBound r i) (by simpa using d.mass) j).1.trans d.coefficientWidth

end TensorInput

def BoundedTape (W : ℕ) (s : Store) (port : ℕ) : Prop :=
  ∃xs : List Bool,xs.length ≤ W ∧ BankArray.Word s.val port xs

theorem BoundedTape.of_eq {W port : ℕ} {s t : Store}
    (h : BoundedTape W s port) (e : t.val.tapes port=s.val.tapes port) : BoundedTape W t port := by
  obtain ⟨xs,hx,hw⟩ := h
  exact ⟨xs,hx,BankArray.word_of_eq e hw⟩

structure TensorState {n B Q N W : ℕ} (d : TensorInput n B Q N W) (s : Store) where
  values : ℕ→Parts
  table : Table (2*(waveDegree (8*Q) N+1))
  factor : FactorReady d.source Q N table values s
  ready : Ready termBank values s
  width : WidthBank termBank W values
  metadata : CacheTableMetadata table d.cache
  query : ℕ
  queryWidth : query.bits.length ≤ W
  queryWord : Word s.val 1048 query
  aliasBuffer : BoundedTape W s 1099
  storedAliases : Word s.val 1100 n
  storedDegree : Word s.val 1110 d.degree

namespace TensorState
variable {n B Q N W : ℕ} {d : TensorInput n B Q N W} {s t : Store}

def external_frame (h : TensorState d s)
    (hm : t.val.memory=s.val.memory)
    (ht : ∀i,i<1101 ∨ i=1110 → t.val.tapes i=s.val.tapes i) : TensorState d t :=
  { h with
    factor := h.factor.low_frame hm (fun i hi => ht i (Or.inl (by omega)))
    ready := termReady_external h.ready (fun i hi => ht i (Or.inl (by omega)))
    queryWord := word_of_eq (ht 1048 (Or.inl (by decide))) h.queryWord
    aliasBuffer := h.aliasBuffer.of_eq (ht 1099 (Or.inl (by decide)))
    storedAliases := word_of_eq (ht 1100 (Or.inl (by decide))) h.storedAliases
    storedDegree := word_of_eq (ht 1110 (Or.inr rfl)) h.storedDegree }

def count_frame (h : TensorState d s) (i : Fin 3)
    (f : CountedShifted.Frame (1101+i.val) s t) : TensorState d t := by
  apply h.external_frame f.2.2.1
  intro k hk
  exact f.2.2.2.2.2.1 k (by have := i.isLt;omega)

end TensorState

#print axioms TensorInput.coefficient_bits
#print axioms TensorState.count_frame
end Maxwell.Continuum.Profile.WaveMachine.Runtime
