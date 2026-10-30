import Maxwell.Continuum.RationalDataflowArrayOutput

/-! Bit-operation bound for all three indexed channel writes. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost
set_option maxHeartbeats 1500000

def Table.writeCost {n : ℕ} (a : Table n) (index : List Bool) (x : Parts) : ℕ :=
  BankArray.costCap a.width index a.basePositive (FixedWidth.bits (addressValue a.width) x.positive.bits)+
  BankArray.costCap a.width index a.baseNegative (FixedWidth.bits (addressValue a.width) x.negative.bits)+
  BankArray.costCap a.width index a.baseDenominator (FixedWidth.bits (addressValue a.width) x.denominator.bits)+
  300*addressValue a.width+300

theorem Table.writeCost_bound {n : ℕ} (a : Table n) (B : ℕ) (h : a.MetadataWidth B)
    (index : List Bool) (hi : index.length≤B) (x : Parts) :
    a.writeCost index x≤2^20*(B+5)^2 := by
  have hv : addressValue a.width≤B := by rw [← a.clock_length]; exact h.clock
  have hp := bankCost_bound a.width index a.basePositive
    (FixedWidth.bits (addressValue a.width) x.positive.bits) B h.width hi h.basePositive
    (by simpa only [FixedWidth.bits_length] using hv) hv
  have hn := bankCost_bound a.width index a.baseNegative
    (FixedWidth.bits (addressValue a.width) x.negative.bits) B h.width hi h.baseNegative
    (by simpa only [FixedWidth.bits_length] using hv) hv
  have hd := bankCost_bound a.width index a.baseDenominator
    (FixedWidth.bits (addressValue a.width) x.denominator.bits) B h.width hi h.baseDenominator
    (by simpa only [FixedWidth.bits_length] using hv) hv
  unfold Table.writeCost
  nlinarith only [hp,hn,hd,hv]

#print axioms Table.writeCost_bound
end Maxwell.Continuum.RationalDataflow.PartArray
