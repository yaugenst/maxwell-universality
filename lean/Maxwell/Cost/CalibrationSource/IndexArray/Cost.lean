import Maxwell.Cost.CalibrationSource.IndexArray.Pass

namespace Maxwell.Cost.CalibrationSource.IndexArray

theorem entryCost_le (B : ℕ) : entryCost B ≤ (4000*8^27+100000)*(B+2)^2 := by
  dsimp only [entryCost]
  norm_num
  nlinarith

theorem costCap_le (m B : ℕ) : costCap m B ≤ (m+1)*(4000*8^27+100001)*(B+2)^2 := by
  have h := Nat.mul_le_mul_left m (entryCost_le B)
  have hp : 1 ≤ (B+2)^2 := Nat.one_le_pow _ _ (by omega)
  have hm : 0 ≤ m*(B+2)^2 := Nat.zero_le _
  dsimp only [costCap]
  norm_num at h ⊢
  nlinarith only [h,hp,hm]

end Maxwell.Cost.CalibrationSource.IndexArray
