import Maxwell.Continuum.FourierTensorNormalizedCost
import Maxwell.Continuum.FourierTensorOutputParameters

/-! The actual compact-output parameters discharge tensor arithmetic,
iteration and normalization dimensions. Only the concrete calibration
initializer's raw channel width and allocated heap size remain inputs. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow PartArray Calibration Calibration.Supercell Calibration.FiniteAlgorithm
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] FiniteAlgorithm.mode FiniteAlgorithm.size MasterConstants.exponent
  FiniteAlgorithm.iterations FiniteAlgorithm.precision

def outputComponentCost {p : ℕ} (L r N : ℕ) (z : ℚ)
    (a : Table (2*aliasArraySize (FiniteAlgorithm.mode L r (N+2) z).radius)) (old : Table p) : ℕ :=
  computedComponentCost (FiniteAlgorithm.size L r (N+2))
    (compactNormalizationBits N (lengthBits (FiniteAlgorithm.size L r (N+2)))) L
    (FiniteAlgorithm.mode L r (N+2) z).radius
    (compactFourierBits N (lengthBits (FiniteAlgorithm.size L r (N+2))) (outputSupportBits L r N z))
    (outputFrequency L r N z) (outputTensorPrecision L r N z)
    (compactMassBits (outputSupportBits L r N z)) a old

def outputNormalizationCoefficient (C Bc : ℕ) : ℕ :=
  Bc+6*outputAliasCoefficient C+iterationCoefficient (C+2)+precisionCoefficient (C+2)+
    outputWorkspaceCoefficient C+2*outputLoopCoefficient C+1

theorem outputNormalizedCost_polylog {L r N C ell : ℕ} (z : ℚ)
    (B heap D den Bc H b d : ℕ)
    (a : CalibrationMatrix.Buffers (2*aliasArraySize (FiniteAlgorithm.mode L r (N+2) z).radius))
    (memory : ℕ→Bool) (hL0 : 0<L) (hell : 0<ell)
    (hL : L≤C*ell^6) (hr : r≤C*ell^7) (hN : N≤C*ell)
    (hb : 33≤b) (hbmax : b<2000) (hB : B≤Bc*ell^b) (hheap : heap≤H*ell^d) :
    let t := PowerMachine.BufferNorm.normalizedOutput a
      (PowerMachine.BufferNorm.Allocation.outputTable
        (2*aliasArraySize (FiniteAlgorithm.mode L r (N+2) z).radius)
        (FiniteAlgorithm.iterations (N+2)) (FiniteAlgorithm.precision L r (N+2)) B heap memory)
      D (FiniteAlgorithm.iterations (N+2)) (FiniteAlgorithm.precision L r (N+2)) den
    outputComponentCost L r N z t t≤
      computedTimeCoefficient (normalizationTensorCoefficient (outputNormalizationCoefficient C Bc) H b d)*ell^4096 := by
  have hL' := hL.trans (Nat.mul_le_mul_right (ell^6) (by omega : C≤C+2))
  have hr' := hr.trans (Nat.mul_le_mul_right (ell^7) (by omega : C≤C+2))
  have hN' : N+2≤(C+2)*ell := by nlinarith only [hN,hell]
  have hn := outputParameters_aliases hL0 hell hL hr hN z
  have hn' : 2*aliasArraySize (FiniteAlgorithm.mode L r (N+2) z).radius≤
      (6*outputAliasCoefficient C)*ell^33 := by
    change 2*(RowArithmetic.rowCount (FiniteAlgorithm.mode L r (N+2) z).radius*3)≤_
    nlinarith only [hn]
  have hK := iterations_linear hell hN'
  have hPn := precision_linear hell hL' hr' hN'
  have hw := outputParameters_work hL0 hell hL hr hN z
  have hl := outputParameters_loop hL0 hell hL hr hN z
  have lift {x c k : ℕ} (hx : x≤c*ell^k) (hc : c≤outputNormalizationCoefficient C Bc) :
      x≤outputNormalizationCoefficient C Bc*ell^k := hx.trans (Nat.mul_le_mul_right _ hc)
  have lift1 {x c : ℕ} (hx : x≤c*ell) (hc : c≤outputNormalizationCoefficient C Bc) :
      x≤outputNormalizationCoefficient C Bc*ell := hx.trans (Nat.mul_le_mul_right _ hc)
  exact normalizedComponentCost_polylog (FiniteAlgorithm.size L r (N+2))
    (compactNormalizationBits N (lengthBits (FiniteAlgorithm.size L r (N+2)))) L
    (FiniteAlgorithm.mode L r (N+2) z).radius
    (compactFourierBits N (lengthBits (FiniteAlgorithm.size L r (N+2))) (outputSupportBits L r N z))
    (outputFrequency L r N z) (outputTensorPrecision L r N z)
    (compactMassBits (outputSupportBits L r N z))
    (FiniteAlgorithm.iterations (N+2)) (FiniteAlgorithm.precision L r (N+2)) B heap D den
    (outputNormalizationCoefficient C Bc) H b d ell a memory hell hb hbmax
    (lift hn' (by unfold outputNormalizationCoefficient;omega))
    (lift1 hK (by unfold outputNormalizationCoefficient;omega))
    (lift1 hPn (by unfold outputNormalizationCoefficient;omega))
    (lift hB (by unfold outputNormalizationCoefficient;omega)) hheap
    (lift1 hw (by unfold outputNormalizationCoefficient;omega))
    (lift hl (by unfold outputNormalizationCoefficient;omega))

#print axioms outputNormalizedCost_polylog
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
