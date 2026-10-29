import Maxwell.Cost.SelectedParameters.GeometricAdapter
import Maxwell.Cost.SelectedParameters.GeometricBounds

namespace Maxwell.Cost.SelectedParameters.GeometricAdapter

private theorem square_bound (X A L : ℕ) (hX : X ≤ (A+2)*L) (hL : 1 ≤ L) :
    X^2 ≤ (A+2)^2*L^3 := by
  calc
    X^2 ≤ ((A+2)*L)^2 := Nat.pow_le_pow_left hX 2
    _ = (A+2)^2*L^2 := by ring
    _ ≤ (A+2)^2*L^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL (by decide))

def costCoefficient : ℕ :=
  3000*8^4+(3000*8^11+3000*8^5+2*8000+2)+3000*8^17

/-- The adapter, actual search, output transfer and complete cleanup have
cubic charged cost in the searched exponent and caller word width. -/
theorem costBound_polynomial (N A B : ℕ) :
    costBound N A B ≤ costCoefficient*(A+2)^2*(N+A+B+4)^3 := by
  have hl : 1 ≤ N+A+B+4 := by omega
  have hload := square_bound (inputWidth A B+2) A (N+A+B+4)
    (by dsimp [inputWidth];nlinarith) hl
  have hfinish := square_bound (Geometric.width N A (inputWidth A B)+2) A (N+A+B+4)
    (by dsimp [Geometric.width,inputWidth];nlinarith) hl
  have hgeo := Geometric.cost_polynomial N A (inputWidth A B)
  rw [show N+inputWidth A B+3=N+A+B+4 by dsimp [inputWidth];omega] at hgeo
  have hp := Nat.mul_le_mul_left (3000*8^4) hload
  have hf := Nat.mul_le_mul_left (3000*8^17) hfinish
  have h := Nat.add_le_add hp (Nat.add_le_add hgeo hf)
  simpa only [costBound,loadCost,finishCost,costCoefficient,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using h

theorem result_width_bound (N A B : ℕ) :
    Geometric.width N A (inputWidth A B) ≤ (A+2)*(N+A+B+4) := by
  dsimp [Geometric.width,inputWidth]
  nlinarith

end Maxwell.Cost.SelectedParameters.GeometricAdapter
