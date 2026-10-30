import Maxwell.Continuum.CalibrationRootGridStep

/-! Explicit polynomial charges for the complete decoded sample and
the accumulator update, including padded-counter import. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 4096

theorem sampleCost_polynomial (N W : ℕ) : sampleCost N W≤2^3072*(N+W+20)^56 := by
  generalize he : N+W+20=X
  have hX : 1≤X := by omega
  have h2 : X^2≤X^56 := Nat.pow_le_pow_right hX (by decide)
  have harg : N+sampleWidth W+20≤2^28*X := by
    unfold sampleWidth RootGridCenter.workWidth loadWidth
    omega
  have hlu : loadWidth W+3≤2^9*X := by unfold loadWidth;omega
  have hr : RootProduct.costBound N (sampleWidth W)≤2^3068*X^56 := by
    calc
      _≤2^1500*(N+sampleWidth W+20)^56 := RootProduct.costBound_polynomial _ _
      _≤2^1500*(2^28*X)^56 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 56)
      _=_ := by ring
  have hl : (2^105+2^145)*(loadWidth W+3)^2≤2^165*X^56 := by
    calc
      _≤(2^105+2^145)*(2^9*X)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlu 2)
      _=((2^105+2^145)*2^18)*X^2 := by ring
      _≤2^165*X^2 := Nat.mul_le_mul_right _ (by norm_num)
      _≤_ := Nat.mul_le_mul_left _ h2
  have h0 : 2^120*(W+2)^2≤2^120*X^56 := Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left (by omega : W+2≤X) 2).trans h2)
  unfold sampleCost
  calc
    _≤(2^120+2^165+2^3068)*X^56 := by nlinarith only [h0,hl,hr]
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

theorem stepCost_polynomial (N W C length : ℕ) (hC : C≤W) :
    stepCost N W C length≤2^3074*(N+W+length+20)^56 := by
  generalize he : N+W+length+20=X
  have hX : 1≤X := by omega
  have h1 : 1≤X^56 := one_le_pow₀ hX
  have hlin : X≤X^56 := Nat.le_self_pow (by decide) _
  have h2 : X^2≤X^56 := Nat.pow_le_pow_right hX (by decide)
  have hs : sampleCost N W≤2^3072*X^56 := (sampleCost_polynomial N W).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 56))
  have ha : operationCost (W+C+1)≤2^104*X^56 := by
    calc
      _≤2^100*(4*X)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _=2^104*X^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ h2
  have hm : 6*W+31*length+39≤64*X := by omega
  unfold stepCost
  calc
    _≤(64+2^3072+2*2^104+1)*X^56 := by nlinarith only [hm,hlin,hs,ha,h1]
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

#print axioms sampleCost_polynomial
#print axioms stepCost_polynomial
end Maxwell.Continuum.RationalDataflow.RootGrid
