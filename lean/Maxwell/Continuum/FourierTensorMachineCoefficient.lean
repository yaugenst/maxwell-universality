import Maxwell.Continuum.FourierTensorMachineCost
import Maxwell.Continuum.CompactTemplateReal

/-! The charged contraction computes the exact numerator occurring in
the emitted real tensor array. Cached rows contain literal signed
integer words of the Fourier amplitude and three rounded wave factors. -/

namespace Maxwell.Continuum.Profile.TensorMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def numeratorRow {B P : ℕ} (a : ComplexDyadic B) (b : Fin 3→ComplexDyadic P) : Fin 8→ℤ :=
  ![a.1.numerator,a.2.numerator,(b 0).1.numerator,(b 0).2.numerator,
    (b 1).1.numerator,(b 1).2.numerator,(b 2).1.numerator,(b 2).2.numerator]

def CachedRows {n B P : ℕ} (a : Table (8*n)) (amp : Fin n→ComplexDyadic B)
    (wave : Fin n→Fin 3→ComplexDyadic P) : Prop :=
  ∀r : Fin n,∀k : Fin 8,a.get ⟨8*r.val+k.val,by omega⟩=
    Parts.literal (numeratorRow (amp r) (wave r) k : ℚ)

theorem CachedRows.valid {n B P : ℕ} {a : Table (8*n)} {amp : Fin n→ComplexDyadic B}
    {wave : Fin n→Fin 3→ComplexDyadic P} (h : CachedRows a amp wave) :
    ∀i,(a.get i).Valid := by
  intro i
  let r : Fin n := ⟨i.val/8,by omega⟩
  let k : Fin 8 := ⟨i.val%8,Nat.mod_lt _ (by decide)⟩
  have he : (⟨8*r.val+k.val,by omega⟩ : Fin (8*n))=i := by
    apply Fin.ext
    dsimp [r,k]
    omega
  rw [←he,h r k]
  exact Parts.literal_valid _

theorem CachedRows.row_value {n B P : ℕ} {a : Table (8*n)} {amp : Fin n→ComplexDyadic B}
    {wave : Fin n→Fin 3→ComplexDyadic P} (h : CachedRows a amp wave) (r : Fin n) :
    rowTerm a r.val=((complexDyadicMul (amp r) (complexDyadicTriple (wave r))).1.numerator : ℚ) := by
  have lookup (k : ℕ) (hk : k<8) :
      (a.getD (8*r.val+k)).value=(numeratorRow (amp r) (wave r) ⟨k,hk⟩ : ℚ) := by
    rw [Table.getD,dite_eq_left (by omega),h r ⟨k,hk⟩,Parts.literal_value]
  have hz : (a.getD (8*r.val)).value=(numeratorRow (amp r) (wave r) 0 : ℚ) := by
    simpa only [Nat.add_zero,Fin.mk_zero] using lookup 0 (by decide)
  unfold rowTerm
  rw [hz,lookup 1 (by decide),lookup 2 (by decide),lookup 3 (by decide),lookup 4 (by decide),
    lookup 5 (by decide),lookup 6 (by decide),lookup 7 (by decide)]
  simpa [numeratorRow,complexDyadicTriple] using
    realProduct_numerators (amp r) (wave r 0) (wave r 1) (wave r 2)

theorem cached_tensor_numerator {n B : ℕ} (a : Table (8*n)) (q : Fin n→Fin 3→ℚ)
    (amp : Fin n→ComplexDyadic B) (Q N : ℕ) (j : Fin 3→Fin (waveDegree (8*Q) N))
    (h : CachedRows a amp (fun r i => waveRoundedCoefficient (q r i) Q N (j i))) :
    (∑i∈Finset.range n,rowTerm a i)=
      ((realFourierTensorCoefficient Finset.univ q amp Q N j).numerator : ℚ) := by
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [realFourierTensorCoefficient,fourierTensorCoefficient,complexDyadicSum,
    Int.cast_sum,tensorWaveCoefficient]
  exact Finset.sum_congr rfl (fun r _ => h.row_value r)

theorem cached_tensor_computes {n B : ℕ} (a : Table (8*n)) (q : Fin n→Fin 3→ℚ)
    (amp : Fin n→ComplexDyadic B) (Q N : ℕ) (j : Fin 3→Fin (waveDegree (8*Q) N))
    (hrows : CachedRows a amp (fun r i => waveRoundedCoefficient (q r i) Q N (j i)))
    (W : ℕ) (hW : 1≤W) (hmeta : a.MetadataWidth W)
    (v : ℕ→Parts) (hv : WidthBank ids W v) (hg : Good ids v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : Ready ids v s) (ha : a.Ready s)
    (hz : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ t output,
      (runPriced (coefficientCode.compile.next input tape) (coefficientCost n W xs.length+1)
        s.val).finished=some (t.place coefficientCode.size) ∧
      (runPriced (coefficientCode.compile.next input tape) (coefficientCost n W xs.length+1)
        s.val).instructions≤2^121*(n+1)^3*(W+1)^2 ∧ Ready ids output t ∧ a.Ready t ∧
      (output 0).value=((realFourierTensorCoefficient Finset.univ q amp Q N j).numerator : ℚ) := by
  obtain ⟨t,output,he,hc,hb,ha',hout⟩ := coefficient_computes a W hW hmeta hrows.valid
    v hv hg input tape xs origin hlen s hn hcount hs ha hz
  exact ⟨t,output,he,hc.trans (coefficientCost_uniform n W xs.length hlen),hb,ha',
    hout.trans (cached_tensor_numerator a q amp Q N j hrows)⟩

#print axioms cached_tensor_numerator
#print axioms cached_tensor_computes
end Maxwell.Continuum.Profile.TensorMachine
