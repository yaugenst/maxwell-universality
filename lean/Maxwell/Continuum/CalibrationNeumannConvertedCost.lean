import Maxwell.Continuum.CalibrationNeumannConverted
import Maxwell.Continuum.RationalDataflowSharedTableCost

/-! Polynomial bit work for the whole executed table-conversion, copy,
descriptor-setup, and cached inverse pass. Fixed instruction lists only
contribute fixed constants. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem convertedCost_polynomial (n width heap D N W B rawWidth countWidth : ℕ)
    (hW : W ≤ width) (hB : B ≤ width) (hraw : rawWidth ≤ width) (hlen : countWidth ≤ width) :
    convertedCost n width heap D N W B rawWidth countWidth ≤
      2^520*(N+1)*(n+1)^6*(initializedWidth n width heap D N width+5)^2 := by
  let q := initializedWidth n width heap D N width
  let P := (N+1)*(n+1)^6*(q+5)^2
  have hwq : width ≤ q := by dsimp [q,initializedWidth,setupWidth]; omega
  have hnp : 1 ≤ (n+1)^6 := one_le_pow₀ (by omega)
  have hq : 1 ≤ (q+5)^2 := one_le_pow₀ (by omega)
  have hn2 : (n+1)^2 ≤ (n+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hqP : (q+5)^2 ≤ P := by
    dsimp [P]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hsize : (tableSize n+1)^3=(n+1)^6 := by unfold tableSize; ring
  have hT : tableSize n+1 ≤ (n+1)^6 := by
    have he : tableSize n+1=(n+1)^2 := by unfold tableSize; ring
    rw [he]
    exact hn2
  have hwidthP : width+1 ≤ P := by nlinarith only [hwq,hqP]
  have hconvert := PartArray.sharedTableCost_polynomial (tableSize n) W width countWidth hW hlen
  have hconvert' : PartArray.sharedTableCost (tableSize n) W width countWidth ≤ 2^116*P := by
    calc
      _ ≤ 2^116*(tableSize n+1)^3*(width+5)^2 := hconvert
      _ ≤ 2^116*(n+1)^6*(q+5)^2 := by rw [hsize]; gcongr
      _ ≤ 2^116*P := by dsimp [P]; nlinarith only [Nat.zero_le (2^116*(n+1)^6*(q+5)^2),
          Nat.mul_le_mul_right (2^116*(n+1)^6*(q+5)^2) (show 1≤N+1 by omega)]
  have hcopy : PartArray.copyCost (tableSize n) width ≤ 2^23*P := by
    unfold PartArray.copyCost
    calc
      _ ≤ 2^23*(n+1)^6*(q+5)^2 := by gcongr
      _ ≤ 2^23*P := by
        dsimp [P]
        have hh := Nat.mul_le_mul_right (2^23*(n+1)^6*(q+5)^2) (show 1≤N+1 by omega)
        nlinarith only [hh]
  have prepConstant : 3000*8^CopyPlan.plan.length ≤ 2^128 := by decide
  have setupConstant : 3000*8^Descriptors.plan.length ≤ 2^512 := by decide
  have hprep : 3000*8^CopyPlan.plan.length*(B+2)^2 ≤ 2^128*P := by
    calc
      _ ≤ 2^128*(q+5)^2 := Nat.mul_le_mul prepConstant (Nat.pow_le_pow_left (by omega) 2)
      _ ≤ 2^128*P := Nat.mul_le_mul_left _ hqP
  have hsetup : 3000*8^Descriptors.plan.length*(width+2)^2 ≤ 2^512*P := by
    calc
      _ ≤ 2^512*(q+5)^2 := Nat.mul_le_mul setupConstant (Nat.pow_le_pow_left (by omega) 2)
      _ ≤ 2^512*P := Nat.mul_le_mul_left _ hqP
  have hloop : costCap N n q ≤ 2^22*P := by
    calc
      _ ≤ 3600000*(N+1)*(n+1)^2*(q+2)^2 := costCap_le N n q
      _ ≤ 2^22*(N+1)*(n+1)^6*(q+5)^2 := by gcongr <;> norm_num
      _ = 2^22*P := by dsimp [P]; ring
  have hrest : 21*countWidth+21+256*(width+1)+6*rawWidth+30*width+42 ≤ 400*P := by
    nlinarith only [hwidthP,hlen,hraw]
  calc
    _ ≤ 2^520*P := by
      unfold convertedCost PartArray.sharedTableResetCost preparedCost copiedCost initializedCost
        copyPrepareCost setupCost
      change PartArray.sharedTableCost (tableSize n) W width countWidth+21*countWidth+21+
          256*(width+1)+(3000*8^CopyPlan.plan.length*(B+2)^2+6*rawWidth+15*width+21+
            (PartArray.copyCost (tableSize n) width+
              (3000*8^Descriptors.plan.length*(width+2)^2+15*width+21+costCap N n q))) ≤ _
      nlinarith only [hconvert',hcopy,hprep,hsetup,hloop,hrest,Nat.zero_le P]
    _ = _ := by dsimp [P,q]; ring

#print axioms convertedCost_polynomial

end Maxwell.Continuum.Calibration.NeumannMachine
