import Maxwell.Continuum.UniformEncoderBranch
import Maxwell.Continuum.VacuumDecoder
import Maxwell.Cost.MagnitudeMax.BranchBound
import Maxwell.Continuum.ParameterLogWidths

/-! Full source parsing is charged in the uniform vacuum branch, including
the source-zero case with arbitrarily many matrix entries. -/
noncomputable section
namespace Maxwell.Continuum.UniformEncoder
open Maxwell.Cost Maxwell.Composition.SelectedScaleWidth
set_option maxHeartbeats 1500000

def vacuumCoefficient (p : Source.Parameters) : ℕ :=
  MagnitudeMax.Branch.coefficient p+13500000261

theorem vacuum_cost (p : Source.Parameters) (S : Source.SparseSystem) (hp : Source.Promises p S) :
    vacuumFuel p S+(CompleteDecoder.vacuumCost (Realization.vacuumDecoder S)+1)≤
      vacuumCoefficient p*(S.nnz+1)*(Parameters.inputLog S.nnz)^3 := by
  let ℓ:=unsignedBitLength (2+S.nnz)
  let m:=S.nnz
  have hl : 1≤ℓ:=Maxwell.Realization.inputBitLength_pos S.nnz
  have hn : S.n≤m:=Source.dimension_le_nnz S hp.1
  have hmBits : m.bits.length≤ℓ := by
    change m.bits.length≤unsignedBitLength (2+m)
    simpa only [Codec.unsignedBitLength_eq_size,Nat.size_eq_bits_len] using
      Codec.unsignedBitLength_mono (show m≤2+m by omega)
  have hnBits : S.n.bits.length≤ℓ := by
    have mono : S.n.bits.length≤m.bits.length := by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hn
    exact mono.trans hmBits
  have hcub : ℓ≤ℓ^3:=le_self_pow₀ hl (by decide : (3:ℕ)≠0)
  have emit:=VacuumEncoder.fuel_le S.n m hn
  have emit' : VacuumEncoder.fuel S.n≤260*(m+1)*ℓ^3 := by
    have operand : 100*m.bits.length+160≤260*ℓ^3 := by omega
    exact emit.trans ((Nat.mul_le_mul_left (m+1) operand).trans_eq (by ring))
  have parse:=MagnitudeMax.Branch.price_polynomial p S hp
  have extra : vacuumFuel p S≤MagnitudeMax.Branch.price S (MagnitudeMax.inputWidth p S)+
      VacuumEncoder.fuel S.n+1 := by unfold vacuumFuel VacuumEncoder.fuel;omega
  have decode:=VacuumDecoder.cost_le S
  have enlarged : S.n.bits.length+2≤3*ℓ := by omega
  have decoder : CompleteDecoder.vacuumCost (Realization.vacuumDecoder S)+1≤
      13500000000*(m+1)*ℓ^3 := by
    exact decode.trans ((Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1))
      (Nat.pow_le_pow_left enlarged 3)).trans_eq (by ring))
  have positive : 1≤(m+1)*ℓ^3:=Nat.mul_pos (by omega) (pow_pos hl _)
  have total : vacuumFuel p S+(CompleteDecoder.vacuumCost (Realization.vacuumDecoder S)+1)≤
      vacuumCoefficient p*(m+1)*ℓ^3 := by
    unfold vacuumCoefficient
    nlinarith only [extra,emit',parse,decoder,positive]
  exact total.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Parameters.inputBits_le_log S.nnz) 3))

#print axioms vacuum_cost
end Maxwell.Continuum.UniformEncoder
