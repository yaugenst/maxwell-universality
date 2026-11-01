import Maxwell.Continuum.StoredDecoderLoop

namespace Maxwell.Continuum.DecoderRow
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem stepCost_polynomial (B H : ℕ) (hH : H≤B):stepCost B H≤2^160*(B+5)^3:=by
  have prefixLength : rowPrefix.length=8:=by decide
  have planLength : plan.length=24:=rfl
  unfold stepCost cleanCost emissionCost costBound width
  rw [prefixLength,planLength]
  norm_num
  nlinarith only [hH,Nat.zero_le B,Nat.zero_le (B^2),Nat.zero_le (B^3)]

theorem loopCost_polynomial (count B H L : ℕ) (hH : H≤B) (hL : L≤B):
    (count+1)*(13*L+15)+count*stepCost B H≤2^162*(count+1)*(B+5)^3:=by
  have hc:=Nat.mul_le_mul_left count (stepCost_polynomial B H hH)
  have hl : 13*L+15≤2^160*(B+5)^3:=by
    nlinarith only [hL,Nat.zero_le B,Nat.zero_le (B^2),Nat.zero_le (B^3)]
  have hn:=Nat.mul_le_mul_left (count+1) hl
  have hs : count*(2^160*(B+5)^3)≤(count+1)*(2^160*(B+5)^3):=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith only [hc,hn,hs]

#print axioms loopCost_polynomial
end Maxwell.Continuum.DecoderRow
