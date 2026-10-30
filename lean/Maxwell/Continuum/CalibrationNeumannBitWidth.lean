import Maxwell.Continuum.CalibrationNeumannChannels

/-! Explicit polynomial raw-width budgets for a single shared denominator. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.CalibrationMatrix
set_option maxHeartbeats 2000000

theorem growth_le_pow (n a D d l b : ℕ)
    (hD : D≤2^d) (hn : n≤2^l) (ha : a≤2^b) :
    growth n a D≤2^(max d (1+l+b)+1) := by
  have hp : 2*n*a≤2^(1+l+b) := by
    calc
      _ ≤ 2*2^l*2^b := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) ha
      _ = _ := by simp only [pow_add,pow_one]
  have hm1 : 2^d≤2^(max d (1+l+b)) := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  have hm2 : 2^(1+l+b)≤2^(max d (1+l+b)) := Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  unfold growth
  calc
    _ ≤ 2^(max d (1+l+b))+2^(max d (1+l+b)) := Nat.add_le_add (hD.trans hm1) (hp.trans hm2)
    _ = _ := by rw [pow_succ]; omega

theorem uniformWidth_explicit (n a v D N d l b w : ℕ)
    (hD : D≤2^d) (hn : n≤2^l) (ha : a≤2^b) (hv : v≤2^w) :
    uniformWidth n a v D N≤(d+l+b+w+8)*(N+2) := by
  let g := max d (1+l+b)
  have hg : growth n a D≤2^(g+1) := growth_le_pow n a D d l b hD hn ha
  have hgsize : (growth n a D).size≤g+2 := by
    have h := Nat.size_le_size hg
    simpa only [Nat.size_pow,Nat.add_assoc] using h
  have hg1 : growth n a D+1≤2^(g+2) := by
    have hpos : 1≤2^(g+1) := Nat.succ_le_of_lt (by positivity)
    calc
      _ ≤ 2^(g+1)+2^(g+1) := Nat.add_le_add hg hpos
      _ = _ := by rw [show g+2=(g+1)+1 by omega,pow_succ]; omega
  have hp : (growth n a D+1)*v≤2^(g+2+w) := by
    calc
      _ ≤ 2^(g+2)*2^w := Nat.mul_le_mul hg1 hv
      _ = _ := (pow_add _ _ _).symm
  have hpsize : ((growth n a D+1)*v).size≤g+w+3 := by
    have h := Nat.size_le_size hp
    simp only [Nat.size_pow] at h
    omega
  have hgbound : g≤d+l+b+1 := by dsimp [g]; omega
  have hm := Nat.mul_le_mul_right (N+1) hgsize
  unfold uniformWidth
  nlinarith only [hpsize,hm,hgbound,Nat.zero_le (N*w)]

def commonWidth (n N W : ℕ) : ℕ := 32*(n+1)^2*(N+2)*(W+1)

theorem shared_uniformWidth (n N W tableSize D a v : ℕ) (ht : tableSize≤(n+1)^2)
    (hD : D≤2^(tableSize*W)) (ha : a≤2^((tableSize+1)*W))
    (hv : v≤2^((tableSize+1)*W)) : uniformWidth n a v D N≤commonWidth n N W := by
  have hn : n≤2^(n+1) := (show n<2^n from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hu := uniformWidth_explicit n a v D N (tableSize*W) (n+1)
    ((tableSize+1)*W) ((tableSize+1)*W) hD hn ha hv
  have hcoef : tableSize*W+(n+1)+(tableSize+1)*W+(tableSize+1)*W+8≤32*(n+1)^2*(W+1) := by
    have hm := Nat.mul_le_mul_right W ht
    have hn2 : n+1≤(n+1)^2 := by nlinarith
    nlinarith only [hm,hn2,Nat.zero_le ((n+1)^2*W)]
  calc
    _ ≤ _ := hu
    _ ≤ (32*(n+1)^2*(W+1))*(N+2) := Nat.mul_le_mul_right _ hcoef
    _ = _ := by unfold commonWidth; ring

#print axioms shared_uniformWidth

end Maxwell.Continuum.Calibration.NeumannMachine
