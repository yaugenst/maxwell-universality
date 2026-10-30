import Maxwell.Continuum.RationalDataflowSharedTableMachine
import Maxwell.Continuum.RationalDataflowDenominatorMachine

/-! Closed polynomial bit cost of the two-pass shared-denominator conversion. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray

set_option maxHeartbeats 1000000

theorem sharedTableCost_polynomial (n W B wordLength : ℕ)
    (hW : W≤B) (hlen : wordLength≤B) :
    sharedTableCost n W B wordLength≤2^116*(n+1)^3*(B+5)^2 := by
  have hp : 1≤(n+1)^3 := one_le_pow₀ (by omega)
  have hn : n+1≤(n+1)^3 := le_self_pow₀ (by omega) (by decide : (3:ℕ)≠0)
  have hb : 1≤(B+5)^2 := one_le_pow₀ (by omega)
  have hBl : B≤(B+5)^2 := by nlinarith
  have hpoly : (n+1)*(13*wordLength+15)≤28*(n+1)^3*(B+5)^2 := by
    have hl : 13*wordLength+15≤28*(B+5)^2 := by nlinarith only [hlen,hBl,hb]
    have hh := Nat.mul_le_mul hn hl
    nlinarith only [hh]
  have hd := denominatorCost_polynomial n W wordLength
  have hdb : 2^110*(n+1)^3*(W+2)^2≤2^110*(n+1)^3*(B+5)^2 := by gcongr; omega
  have hm : n*2^105*(B+5)^2≤2^105*(n+1)^3*(B+5)^2 := by
    have hh := Nat.mul_le_mul_right (2^105*(B+5)^2) (show n≤(n+1)^3 by omega)
    nlinarith only [hh]
  have hsave : 36*wordLength+42≤78*(n+1)^3*(B+5)^2 := by
    have hsize : (B+5)^2≤(n+1)^3*(B+5)^2 := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith only [hlen,hBl,hb,hsize]
  unfold sharedTableCost sharedMapCost
  have hnon : 0≤(n+1)^3*(B+5)^2 := Nat.zero_le _
  nlinarith only [hd,hdb,hpoly,hm,hsave,hnon]

#print axioms sharedTableCost_polynomial
end Maxwell.Continuum.RationalDataflow.PartArray
