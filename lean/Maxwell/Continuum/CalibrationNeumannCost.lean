import Maxwell.Continuum.CalibrationNeumannMachine
import Maxwell.Continuum.CalibrationNeumannBitWidth

/-! Polynomial execution work for shared-denominator cached affine iteration. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
set_option maxHeartbeats 2000000

theorem costCap_commonWidth (N n W : ℕ) :
    costCap N n (commonWidth n N W)≤2^34*(N+2)^3*(n+1)^6*(W+1)^2 := by
  have hbase : 1≤(n+1)^2*(N+2)*(W+1) := Nat.succ_le_of_lt (by positivity)
  have hwidth : commonWidth n N W+2≤34*(n+1)^2*(N+2)*(W+1) := by
    unfold commonWidth
    nlinarith only [hbase]
  have hs := Nat.pow_le_pow_left hwidth 2
  have hn : N+1≤N+2 := by omega
  calc
    _ ≤ 3600000*(N+1)*(n+1)^2*(commonWidth n N W+2)^2 := costCap_le _ _ _
    _ ≤ 3600000*(N+2)*(n+1)^2*(34*(n+1)^2*(N+2)*(W+1))^2 := by gcongr
    _ ≤ _ := by nlinarith only [Nat.zero_le ((N+2)^3*(n+1)^6*(W+1)^2)]

theorem costCap_source_polynomial (N n W ell C k r w : ℕ) (hell : 1≤ell)
    (hN : N≤C*ell^k) (hn : n≤C*ell^r) (hW : W≤C*ell^w) :
    costCap N n (commonWidth n N W)≤2^34*(C+2)^11*ell^(3*k+6*r+2*w) := by
  have hp (p : ℕ) : 1≤ell^p := Nat.one_le_pow _ _ hell
  have hN' : N+2≤(C+2)*ell^k := by nlinarith only [hN,hp k]
  have hn' : n+1≤(C+2)*ell^r := by nlinarith only [hn,hp r]
  have hW' : W+1≤(C+2)*ell^w := by nlinarith only [hW,hp w]
  calc
    _ ≤ 2^34*(N+2)^3*(n+1)^6*(W+1)^2 := costCap_commonWidth N n W
    _ ≤ 2^34*((C+2)*ell^k)^3*((C+2)*ell^r)^6*((C+2)*ell^w)^2 := by gcongr
    _ = _ := by
      simp only [mul_pow,←pow_mul]
      ring_nf

#print axioms costCap_source_polynomial

end Maxwell.Continuum.Calibration.NeumannMachine
