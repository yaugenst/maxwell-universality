import Maxwell.Cost.PositiveGraph.Fold
import Mathlib.Data.Nat.Size

namespace Maxwell.Cost.PositiveGraph

def bitBudget (width dimension count base : ℕ) : ℕ :=
  width+4+base.bits.length+(4*count+1).bits.length+(2*dimension+count+1).bits.length

theorem bits_mono {a b : ℕ} (h : a ≤ b) : a.bits.length ≤ b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

theorem bank_cost_le (width index base payload : List Bool) (B : ℕ)
    (hw : width.length ≤ B) (hi : index.length ≤ B) (hb : base.length ≤ B)
    (hp : payload.length ≤ B) (ha : addressValue width ≤ B) :
    BankArray.costCap width index base payload ≤ 20000*(B+2)^2 := by
  unfold BankArray.costCap ArrayAccess.costCap
  have h1 : (width.length+index.length+base.length+5)^2 ≤ (3*B+5)^2 := by gcongr; omega
  have h2 : addressValue width*(15*(width.length+index.length+base.length+1+addressValue width)+24) ≤
      B*(15*(4*B+1)+24) := Nat.mul_le_mul ha (by omega)
  nlinarith

theorem pair_price_le (width : List Bool) (index : ℕ) (first mediator : List Bool) (B : ℕ)
    (hw : width.length ≤ B) (ha : addressValue width ≤ B)
    (hi : index.bits.length ≤ B) (hi' : (index+1).bits.length ≤ B) :
    PairWrite.price width index first mediator ≤ 41000*(B+2)^2 := by
  have h1 := bank_cost_le width index.bits [] (FixedWidth.bits (addressValue width) first) B
    hw hi (by simp) (by simpa only [FixedWidth.bits_length] using ha) ha
  have h2 := bank_cost_le width (index+1).bits [] (FixedWidth.bits (addressValue width) mediator) B
    hw hi' (by simp) (by simpa only [FixedWidth.bits_length] using ha) ha
  unfold PairWrite.price
  nlinarith

theorem diagonal_price_le (index clock : List Bool) (base value B : ℕ) (negative half mediator : Bool)
    (hB : 4 ≤ B) (hi : index.length ≤ B) (hb : base.bits.length ≤ B) (hc : clock.length = 4) :
    DiagonalUpdate.costCap index base clock value negative half mediator ≤ 40100*(B+2)^2 := by
  have h1 := bank_cost_le (4:ℕ).bits index base.bits clock B (by change 3 ≤ B; omega) hi hb
    (by omega) (by simpa only [RationalAccumulator.address_bits] using hB)
  have h2 := bank_cost_le (4:ℕ).bits index base.bits (DiagonalUpdate.payload value negative half mediator) B
    (by change 3 ≤ B; omega) hi hb (by simpa only [DiagonalUpdate.payload,FixedWidth.bits_length] using hB)
    (by simpa only [RationalAccumulator.address_bits] using hB)
  unfold DiagonalUpdate.costCap
  nlinarith

theorem step_price_le (width dimension count index base : ℕ) (e : BoundedEntry dimension)
    (clock : List Bool) (rv cv mv : ℕ) (hi : index < count) (hc : clock.length = 4) :
    Step.price width dimension count index base e.val clock rv cv mv ≤
      500000*(bitBudget width dimension count base+2)^2 := by
  let B := bitBudget width dimension count base
  have hB : 4 ≤ B := by dsimp [B,bitBudget]; omega
  have hwidth : width+3 ≤ B := by dsimp [B,bitBudget]; omega
  have hbase : base.bits.length ≤ B := by dsimp [B,bitBudget]; omega
  have hi0 : (2*index).bits.length ≤ B := (bits_mono (show 2*index ≤ 4*count+1 by omega)).trans (by dsimp [B,bitBudget]; omega)
  have hi1 : (2*index+1).bits.length ≤ B := (bits_mono (show 2*index+1 ≤ 4*count+1 by omega)).trans (by dsimp [B,bitBudget]; omega)
  have hj0 : (2*(count+index)).bits.length ≤ B := (bits_mono (show 2*(count+index) ≤ 4*count+1 by omega)).trans (by dsimp [B,bitBudget]; omega)
  have hj1 : (2*(count+index)+1).bits.length ≤ B := (bits_mono (show 2*(count+index)+1 ≤ 4*count+1 by omega)).trans (by dsimp [B,bitBudget]; omega)
  have hmed : (2*dimension+index).bits.length ≤ B :=
    (bits_mono (show 2*dimension+index ≤ 2*dimension+count+1 by omega)).trans (by dsimp [B,bitBudget]; omega)
  have hcol : (dimension+e.val.column).bits.length ≤ B :=
    (bits_mono (show dimension+e.val.column ≤ 2*dimension+count+1 by have := e.property.2; omega)).trans
      (by dsimp [B,bitBudget]; omega)
  have hwidthBits : (width+3).bits.length ≤ B := by
    rw [← WordLength.countBits_eq]
    exact (WordLength.countBits_length _).trans hwidth
  have hpair1 := pair_price_le (width+3).bits (2*index) (SourceCircuit.fixedWidth width e.val.row)
    (2*dimension+index).bits B hwidthBits (by simpa only [RationalAccumulator.address_bits] using hwidth) hi0 hi1
  have hpair2 := pair_price_le (width+3).bits (2*(count+index)) (dimension+e.val.column).bits
    (2*dimension+index).bits B hwidthBits (by simpa only [RationalAccumulator.address_bits] using hwidth) hj0 hj1
  have hdiag1 := diagonal_price_le (SourceCircuit.fixedWidth width e.val.row) clock base rv B
    (decide (e.val.value<0)) (decide (e.val.value=1/2 ∨ e.val.value= -1/2)) false hB
    (by simpa only [SourceCircuit.fixedWidth_length] using (show width ≤ B by omega)) hbase hc
  have hdiag2 := diagonal_price_le (dimension+e.val.column).bits clock base cv B
    (decide (e.val.value<0)) (decide (e.val.value=1/2 ∨ e.val.value= -1/2)) false hB hcol hbase hc
  have hdiag3 := diagonal_price_le (2*dimension+index).bits clock base mv B
    (decide (e.val.value<0)) (decide (e.val.value=1/2 ∨ e.val.value= -1/2)) true hB hmed hbase hc
  change Step.price width dimension count index base e.val clock rv cv mv ≤ 500000*(B+2)^2
  unfold Step.price EntryEndpoints.price TripleScatter.costCap
  nlinarith

theorem fold_price_le (width dimension count index base : ℕ) (clock : List Bool)
    (entries : List (BoundedEntry dimension)) (hfit : index+entries.length ≤ count)
    (tables : Tables dimension count) (hc : clock.length = 4) :
    foldPrice width dimension count index base clock entries hfit tables ≤
      entries.length*(500000*(bitBudget width dimension count base+2)^2+4)+1 := by
  induction entries generalizing index tables with
  | nil => simp [foldPrice]
  | cons e rest ih =>
    have hi : index < count := by simp only [List.length_cons] at hfit; omega
    have hs := step_price_le width dimension count index base e clock
      (codeAt tables.diagonal (rowIndex dimension count e.val e.property.1))
      (codeAt tables.diagonal (columnIndex dimension count e.val e.property.2))
      (codeAt tables.diagonal (mediatorIndex dimension count index hi)) hi hc
    have hr := ih (index+1) (by simp only [List.length_cons] at hfit; omega)
      (tables.next width dimension count index hi e)
    simp only [foldPrice,List.length_cons]
    nlinarith

end Maxwell.Cost.PositiveGraph
