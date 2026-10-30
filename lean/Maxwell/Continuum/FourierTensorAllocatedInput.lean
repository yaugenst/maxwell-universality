import Maxwell.Continuum.FourierTensorCacheAllocated

/-! The allocated wave cache satisfies the tensor compiler's storage
contract from the actual source descriptors and finite word bounds. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorSetup
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
open scoped BigOperators
set_option maxHeartbeats 3500000

theorem canonical_bits (xs : List Bool) : (addressValue xs).bits.length≤xs.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact IndexedAddress.value_lt_pow_length xs

theorem buffer_metadata (Q N R W : ℕ) ( _hW : 1≤W)
    (a : Table (5*RowArithmetic.rowCount R)) (memory : ℕ→Bool)
    (ha : a.MetadataWidth W) (hn : (RowArithmetic.rowCount R).bits.length≤W)
    (hd : (waveDegree (8*Q) N).bits.length≤W) (hp : waveWorkBits (8*Q) N+7≤W) :
    (buffer Q N R a memory).MetadataWidth (producerWidth Q N W) := by
  have hw := (canonical_bits a.width).trans ha.width
  have hb := (canonical_bits a.basePositive).trans ha.basePositive
  have hc := (canonical_bits a.baseNegative).trans ha.baseNegative
  have he := (canonical_bits a.baseDenominator).trans ha.baseDenominator
  have h5 := RationalAccumulator.bits_mul_le 5 (RowArithmetic.rowCount R)
  have hprod := RationalAccumulator.bits_mul_le (5*RowArithmetic.rowCount R) (addressValue a.width)
  have hs1 := RationalAccumulator.bits_add_le (addressValue a.basePositive) (addressValue a.baseNegative)
  have hs2 := RationalAccumulator.bits_add_le (addressValue a.basePositive+addressValue a.baseNegative)
    (addressValue a.baseDenominator)
  have hs3 := RationalAccumulator.bits_add_le
    (addressValue a.basePositive+addressValue a.baseNegative+addressValue a.baseDenominator)
    (5*RowArithmetic.rowCount R*addressValue a.width)
  have hheap : (heap R (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)).bits.length≤2*W+4 := by
    rw [show (5:ℕ).bits.length=3 by decide] at h5
    unfold heap
    omega
  have hadd := RationalAccumulator.bits_add_le (waveDegree (8*Q) N) 1
  have hmul := RationalAccumulator.bits_mul_le 2 (waveDegree (8*Q) N+1)
  have hlength : (2*(waveDegree (8*Q) N+1)).bits.length≤W+4 := by
    rw [show (2:ℕ).bits.length=2 by decide] at hmul
    rw [show (1:ℕ).bits.length=1 by decide] at hadd
    omega
  have hslot : (slotWidth Q N).bits.length≤W :=
    (Machin.Runtime.nat_bits_le_self _).trans hp
  apply Profile.Runtime.memoryTable_metadata
  · unfold slotWidth producerWidth
    omega
  · unfold producerWidth dimensionWidth
    omega

def allocatedInput (R B Q N W : ℕ) (a : Table (5*RowArithmetic.rowCount R)) (memory : ℕ→Bool)
    (q : Fin (RowArithmetic.rowCount R)→Fin 3→ℚ) (amp : Fin (RowArithmetic.rowCount R)→ComplexDyadic B)
    (A : ℕ) (ha : a.MetadataWidth W) (hrows : FourierRows a q amp)
    (hq : ∀r i,|q r i|≤Q) (hmass : (∑r,‖complexDyadicValue (amp r)‖)≤(2:ℝ)^A)
    (hbits : B+3*waveWorkBits (8*Q) N+A+16≤W)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (hn : (RowArithmetic.rowCount R).bits.length≤W) (hd : (waveDegree (8*Q) N).bits.length≤W)
    (hW : 6≤W) (hp : waveWorkBits (8*Q) N+7≤W) (hg : (waveGrid (8*Q) N).bits.length≤W) :
    TensorInput (RowArithmetic.rowCount R) B Q N W where
  source := a
  cache := buffer Q N R a memory
  sourceWidth := ha
  cacheWidth := buffer_metadata Q N R W (by omega) a memory ha hn hd hp
  cacheSeparated := Profile.Runtime.memoryTable_separated _ _ _ _ _
  disjoint := source_separated Q N R a memory
  fit := by simp only [buffer,Profile.Runtime.memoryTable,addressValue_bits,slotWidth];exact le_rfl
  frequency := q
  amplitude := amp
  rows := hrows
  frequencyBound := hq
  massExponent := A
  mass := hmass
  coefficientWidth := hbits
  qWidth := hQ
  nWidth := hN
  aliasWidth := hn
  degreeWidth := hd
  smallWidth := hW
  precisionWidth := hp
  gridWidth := hg

#print axioms buffer_metadata
end Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorSetup
