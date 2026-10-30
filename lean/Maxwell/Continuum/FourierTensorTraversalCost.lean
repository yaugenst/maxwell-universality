import Maxwell.Continuum.FourierTensorTraversalCode

/-! The actual three outer runtime loops add three powers to the local
workspace bound. Alias accumulation remains a separate cubic factor. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 32768

def repeatedTimeCoefficient : ℕ := coefficientTimeCoefficient+128
def tensorTimeCoefficient : ℕ := 2^21*repeatedTimeCoefficient+2^125

theorem repeated_cost_combine (b T W : ℕ) (h : 21*W+21+20*W+30 ≤ 128*T) :
    (21*W+21)+(b*T+20*W+30) ≤ (b+128)*T := by
  rw [Nat.add_mul]
  omega

theorem repeatedCoefficientCost_polynomial (Q N n W : ℕ) :
    repeatedCoefficientCost Q N n W ≤
      repeatedTimeCoefficient*(n+1)^3*(Q+N+W+64)^240 := by
  let X := Q+N+W+64
  have hX : W+64 ≤ X := by dsimp [X];omega
  have hx : X ≤ X^240 := Nat.le_self_pow (by decide) X
  have hn : 1 ≤ (n+1)^3 := one_le_pow₀ (by omega)
  have ht : X ≤ (n+1)^3*X^240 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hn hx
  have he : 21*W+21+20*W+30 ≤ 128*((n+1)^3*X^240) := by
    omega
  simpa only [repeatedCoefficientCost,repeatedTimeCoefficient,Nat.mul_assoc] using
    repeated_cost_combine coefficientTimeCoefficient ((n+1)^3*X^240) W he

def runtimeLoopBound (b setup count advance D : ℕ) : ℕ→ℕ
  | 0 => b
  | k+1 => setup+(D+1)*count+D*(runtimeLoopBound b setup count advance D k+advance)

theorem runtimeLoopBound_three (b setup count advance D : ℕ) :
    runtimeLoopBound b setup count advance D 3=
      D^3*b+(D^2+D+1)*(setup+(D+1)*count+D*advance) := by
  simp only [runtimeLoopBound]
  ring

theorem tensorTraversalCost_eq (Q N n W D k : ℕ) :
    tensorTraversalCost Q N n W D k=
      runtimeLoopBound (repeatedCoefficientCost Q N n W)
        (stageCost W+(21*W+21)) (13*W+15) (2*operationCost W+1) D k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tensorTraversalCost,runtimeLoopBound,ih,Nat.add_assoc]

theorem runtimeLoopBound_three_polynomial (b setup count advance D T X C : ℕ)
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hD : D ≤ 128*X)
    (hb : b ≤ C*T*X^240) (hs : setup ≤ 2^102*X^2)
    (hc : count ≤ 32*X) (ha : advance ≤ 2^102*X^2) :
    runtimeLoopBound b setup count advance D 3 ≤ (2^21*C+2^125)*T*X^243 := by
  have hd1 : D+1 ≤ 129*X := by omega
  have hd2 := Nat.pow_le_pow_left hD 2
  have hd3 := Nat.pow_le_pow_left hD 3
  have hx2 : X ≤ X^2 := Nat.le_self_pow (by decide) X
  have hx3 : X^2 ≤ X^3 := Nat.pow_le_pow_right hX (by decide)
  have hsum : D^2+D+1 ≤ 2^15*X^2 := by nlinarith only [hd2,hD,hX,hx2]
  have hcount := Nat.mul_le_mul hd1 hc
  have hadv := Nat.mul_le_mul hD ha
  have htail : setup+(D+1)*count+D*advance ≤ 2^110*X^3 := by
    nlinarith only [hs,hcount,hadv,hx3]
  have hmain : D^3*b ≤ (2^21*C)*T*X^243 := by
    calc
      _ ≤ (128*X)^3*(C*T*X^240) := Nat.mul_le_mul hd3 hb
      _ = _ := by ring
  have hsmall : (D^2+D+1)*(setup+(D+1)*count+D*advance) ≤ 2^125*T*X^243 := by
    calc
      _ ≤ (2^15*X^2)*(2^110*X^3) := Nat.mul_le_mul hsum htail
      _ = 2^125*X^5 := by ring
      _ ≤ 2^125*(T*X^243) := Nat.mul_le_mul_left _ (by
        simpa only [Nat.one_mul] using Nat.mul_le_mul hT (Nat.pow_le_pow_right hX (by decide : 5 ≤ 243)))
      _ = _ := (Nat.mul_assoc _ _ _).symm
  rw [runtimeLoopBound_three]
  simpa only [Nat.add_mul] using Nat.add_le_add hmain hsmall

theorem tensorTraversalCost_polynomial (Q N n W : ℕ) :
    tensorTraversalCost Q N n W (waveDegree (8*Q) N) 3 ≤
      tensorTimeCoefficient*(n+1)^3*(Q+N+W+64)^243 := by
  let X := Q+N+W+64
  have hX : W+64 ≤ X := by dsimp [X];omega
  have hD : waveDegree (8*Q) N ≤ 128*X := by
    unfold waveDegree
    dsimp [X]
    omega
  have hstage : stageCost W ≤ 2^96*X^2 := by
    unfold stageCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hop : operationCost W ≤ 2^100*X^2 := by
    unfold operationCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have h1 : 1 ≤ X^2 := one_le_pow₀ (by omega)
  have hx2 : X ≤ X^2 := Nat.le_self_pow (by decide) X
  have hs : stageCost W+(21*W+21) ≤ 2^102*X^2 := by
    nlinarith only [hstage,hX,hx2]
  have ha : 2*operationCost W+1 ≤ 2^102*X^2 := by
    nlinarith only [hop,h1]
  rw [tensorTraversalCost_eq]
  exact runtimeLoopBound_three_polynomial _ _ _ _ _ _ _ _ (by omega)
    (one_le_pow₀ (by omega)) hD (repeatedCoefficientCost_polynomial Q N n W)
    hs (by omega) ha

theorem tensorTraversalCost_source_exponent (Q N n W C ell : ℕ) (hell : 1 ≤ ell)
    (hX : Q+N+W+64 ≤ C*ell^16) (hn : n+1 ≤ C*ell^33) :
    tensorTraversalCost Q N n W (waveDegree (8*Q) N) 3 ≤
      (tensorTimeCoefficient*C^246)*ell^4096 := by
  calc
    _ ≤ tensorTimeCoefficient*(n+1)^3*(Q+N+W+64)^243 := tensorTraversalCost_polynomial Q N n W
    _ ≤ tensorTimeCoefficient*(C*ell^33)^3*(C*ell^16)^243 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 3)) (Nat.pow_le_pow_left hX 243)
    _ = (tensorTimeCoefficient*C^246)*ell^3987 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hell (by decide))

#print axioms tensorTraversalCost_polynomial
#print axioms tensorTraversalCost_source_exponent
end Maxwell.Continuum.Profile.WaveMachine.Runtime
