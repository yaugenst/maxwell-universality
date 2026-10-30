import Maxwell.Continuum.RationalDataflowArray

/-! Indexed memory access is charged in the same bit-width budget as rational arithmetic. -/

namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost
set_option maxHeartbeats 2000000

theorem bankCost_bound (width index base clock : List Bool) (B : ℕ)
    (hw : width.length≤B) (hi : index.length≤B) (hb : base.length≤B)
    (hc : clock.length≤B) (hv : addressValue width≤B) :
    BankArray.costCap width index base clock≤2^16*(B+5)^2 := by
  have hs : width.length+index.length+base.length+5≤3*(B+5) := by omega
  have hs2 := Nat.pow_le_pow_left hs 2
  have hp : 15*(width.length+index.length+base.length+1+addressValue width)+24≤60*B+39 := by omega
  have hm := Nat.mul_le_mul hv hp
  have ht : width.length+index.length+base.length+clock.length+addressValue width+3≤5*B+3 := by omega
  unfold BankArray.costCap ArrayAccess.costCap
  nlinarith only [hs2,hm,ht]

structure Table.MetadataWidth {n : ℕ} (a : Table n) (B : ℕ) : Prop where
  width : a.width.length≤B
  basePositive : a.basePositive.length≤B
  baseNegative : a.baseNegative.length≤B
  baseDenominator : a.baseDenominator.length≤B
  clock : a.clock.length≤B

theorem Table.MetadataWidth.mono {n : ℕ} {a : Table n} {B C : ℕ}
    (h : a.MetadataWidth B) (hBC : B≤C) : a.MetadataWidth C :=
  ⟨h.width.trans hBC,h.basePositive.trans hBC,h.baseNegative.trans hBC,
    h.baseDenominator.trans hBC,h.clock.trans hBC⟩

theorem Table.readCost_bound {n : ℕ} (a : Table n) (B : ℕ) (h : a.MetadataWidth B)
    (index : List Bool) (hi : index.length≤B) (old : Parts) (ho : old.Width B) :
    a.readCost index old≤2^20*(B+5)^2 := by
  have hv : addressValue a.width≤B := by rw [← a.clock_length]; exact h.clock
  have hp := bankCost_bound a.width index a.basePositive a.clock B h.width hi h.basePositive h.clock hv
  have hn := bankCost_bound a.width index a.baseNegative a.clock B h.width hi h.baseNegative h.clock hv
  have hd := bankCost_bound a.width index a.baseDenominator a.clock B h.width hi h.baseDenominator h.clock hv
  rcases ho with ⟨ho1,ho2,ho3⟩
  unfold Table.readCost
  nlinarith only [hp,hn,hd,ho1,ho2,ho3,hv]

#print axioms Table.readCost_bound

end Maxwell.Continuum.RationalDataflow.PartArray
