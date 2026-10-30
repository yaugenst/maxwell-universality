import Maxwell.Continuum.CutoffMonomialPassMachine

/-! Polynomial bit cost of the actual cached monomial row traversal. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Profile
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem monomialWorkingWidth_polynomial (D W : ℕ) :
    monomialWorkingWidth D W+16≤2^9*(D+1)^2*(W+1) := by
  unfold monomialWorkingWidth monomialStorageWidth
  nlinarith only [Nat.zero_le D,Nat.zero_le W,Nat.zero_le (D*W),Nat.zero_le (D^2),Nat.zero_le (D^2*W)]

theorem monomialPassCost_polynomial (D W len : ℕ) (hlen : len≤monomialWorkingWidth D W) :
    (D+1)*(13*len+15)+D*(2^112*(monomialWorkingWidth D W+16)^2)≤
      2^140*(D+1)^5*(W+1)^2 := by
  have hb := monomialWorkingWidth_polynomial D W
  have inner : 13*len+15≤16*(monomialWorkingWidth D W+16) := by omega
  have hcount : (D+1)*(13*len+15)≤2^13*(D+1)^3*(W+1) := by
    calc
      _≤(D+1)*(16*(monomialWorkingWidth D W+16)) := Nat.mul_le_mul_left _ inner
      _≤(D+1)*(16*(2^9*(D+1)^2*(W+1))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
      _=2^13*(D+1)^3*(W+1) := by ring
  have hrow : D*(2^112*(monomialWorkingWidth D W+16)^2)≤2^130*(D+1)^5*(W+1)^2 := by
    calc
      _≤(D+1)*(2^112*(monomialWorkingWidth D W+16)^2) := Nat.mul_le_mul_right _ (Nat.le_succ _)
      _≤(D+1)*(2^112*(2^9*(D+1)^2*(W+1))^2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2))
      _=2^130*(D+1)^5*(W+1)^2 := by ring
  have hd : (D+1)^3≤(D+1)^5 := by gcongr;omega
  have hw : W+1≤(W+1)^2 := le_self_pow₀ (by omega) (by decide : (2:ℕ)≠0)
  have hsmall := Nat.mul_le_mul hd hw
  have hc : (D+1)*(13*len+15)≤2^13*((D+1)^5*(W+1)^2) :=
    hcount.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left (2^13) hsmall)
  nlinarith only [hc,hrow]

theorem monomialPassCost_precision (N len : ℕ)
    (hlen : len≤monomialWorkingWidth (profileDegree N) (272*(N+1))) :
    (profileDegree N+1)*(13*len+15)+profileDegree N*
      (2^112*(monomialWorkingWidth (profileDegree N) (272*(N+1))+16)^2)≤2^320*(N+1)^12 := by
  have hd := profileDegree_bound N
  have h1 : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hd' : profileDegree N+1≤2^31*(N+1)^2 := by nlinarith
  have hw : 272*(N+1)+1≤2^9*(N+1) := by omega
  calc
    _≤2^140*(profileDegree N+1)^5*(272*(N+1)+1)^2 := monomialPassCost_polynomial _ _ _ hlen
    _≤2^140*(2^31*(N+1)^2)^5*(2^9*(N+1))^2 := by gcongr
    _=2^313*(N+1)^12 := by ring
    _≤2^320*(N+1)^12 := Nat.mul_le_mul_right _ (by norm_num)

#print axioms monomialPassCost_precision
end Maxwell.Continuum.Calibration.RawCutoff
