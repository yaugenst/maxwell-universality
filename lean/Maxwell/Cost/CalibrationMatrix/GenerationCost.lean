import Maxwell.Cost.CalibrationMatrix.GeneratedInitializer

namespace Maxwell.Cost.CalibrationMatrix.Generation
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice

/-- An explicit polynomial bound for the generated matrix program. The
finite material decision tree contributes only its fixed literal-code cost. -/
theorem loopCost_le (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ)
    (hbits : ((3*cubeWidth R^3)^2).bits.length ≤ B) :
    loopCost R material z D B ≤ ((3*cubeWidth R^3)^2+1)*
      (201000*(B+10)^2+MaterialEntry.costBound material z D) := by
  let count := (3*cubeWidth R^3)^2
  have hlocal : 13*count.bits.length+15+iterationCost material z D B+6*count.bits.length+4 ≤
      201000*(B+10)^2+MaterialEntry.costBound material z D := by
    change 13*count.bits.length+15+(200000*(B+10)^2+MaterialEntry.costBound material z D+12*B+18)+
      6*count.bits.length+4 ≤ _
    change count.bits.length ≤ B at hbits
    nlinarith only [hbits]
  calc
    loopCost R material z D B ≤ (count+1)*
        (13*count.bits.length+15+iterationCost material z D B+6*count.bits.length+4) := by
      change (count+1)*(13*count.bits.length+15)+count*iterationCost material z D B+
        6*count.bits.length+4 ≤ _
      nlinarith only [Nat.zero_le (count*(6*count.bits.length+4)),
        Nat.zero_le (iterationCost material z D B)]
    _ ≤ _ := Nat.mul_le_mul_left _ hlocal

theorem initCost_le (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ)
    (hR : R.bits.length ≤ B) (hbits : ((3*cubeWidth R^3)^2).bits.length ≤ B) :
    initCost R material z D B ≤ ((3*cubeWidth R^3)^2+1)*
      (202000*(B+10)^2+MaterialEntry.costBound material z D) := by
  have hp := Nat.pow_le_pow_left (show R.bits.length+8 ≤ B+10 by omega) 2
  have hl := loopCost_le R material z D B hbits
  have hn : 1 ≤ (3*cubeWidth R^3)^2+1 := by omega
  have hmult := Nat.mul_le_mul_right (1000*(B+10)^2) hn
  change 700*(R.bits.length+8)^2+loopCost R material z D B ≤ _
  nlinarith only [hp,hl,hmult]

theorem cells_le (R : ℕ) : (3*cubeWidth R^3)^2+1 ≤ 577*(R+1)^6 := by
  have hp := Nat.pow_le_pow_left (show 2*R+1 ≤ 2*(R+1) by omega) 6
  have hpow : (3*cubeWidth R^3)^2 = 9*(2*R+1)^6 := by unfold cubeWidth; ring
  have hscale : (2*(R+1))^6 = 64*(R+1)^6 := by ring
  have hpos : 1 ≤ (R+1)^6 := by
    have h : 0 < (R+1)^6 := by positivity
    omega
  rw [hscale] at hp
  rw [hpow]
  omega

theorem initCost_polynomial (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ)
    (hR : R.bits.length ≤ B) (hbits : ((3*cubeWidth R^3)^2).bits.length ≤ B) :
    initCost R material z D B ≤ 577*(R+1)^6*
      (202000*(B+10)^2+MaterialEntry.costBound material z D) :=
  (initCost_le R material z D B hR hbits).trans (Nat.mul_le_mul_right _ (cells_le R))

end Maxwell.Cost.CalibrationMatrix.Generation
