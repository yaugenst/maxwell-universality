import Maxwell.Continuum.ProfileMonomialCache
import Maxwell.Continuum.ProfileProducerCost

/-! Polynomial cost bounds for actual cache allocation, initialization and
recurrence, including raw arithmetic and every memory write. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 4096

theorem monomialSeedCost_cap (D B len X : ℕ) (hX : 1≤X)
    (hd : D+1≤X) (hb : B+18≤X) (hl : len≤4*X) :
    monomialSeedCost D B len≤2^100*X^3 := by
  have h23 : X^2≤X^3 := Nat.pow_le_pow_right hX (by decide)
  have h13 : X≤X^3 := le_self_pow₀ hX (by decide)
  have hs : 2*stageCost B≤2^97*X^2 := by
    unfold stageCost
    have h := Nat.pow_le_pow_left (show B+2≤X by omega) 2
    nlinarith only [h]
  have hc : (4*(D+1)+1)*(13*len+15)≤335*X^2 := by
    calc
      _≤(5*X)*(67*X) := Nat.mul_le_mul (by omega) (by omega)
      _=_ := by ring
  have hf : 4*(D+1)*(2^30*(B+6)^2)≤2^32*X^3 := by
    calc
      _≤4*X*(2^30*X^2) := by gcongr;omega
      _=_ := by ring
  have hr : rowPlanCost 0 4 B monomialSeedPlan≤2^32*X^2 := by
    unfold rowPlanCost monomialSeedPlan
    simp only [List.length_cons,List.length_nil,show (0:ℕ).bits.length=0 from rfl,Nat.add_zero]
    have h := Nat.pow_le_pow_left (show B+4+5≤X by omega) 2
    have hp : 1≤X^2 := one_le_pow₀ hX
    nlinarith only [h,hp]
  unfold monomialSeedCost
  nlinarith only [hs,hc,hf,hr,h23]

theorem monomialInitializeCost_cap (D B len X : ℕ) (hX : 1≤X)
    (hd : D+1≤X) (hb : B+18≤X) (hl : len≤X) :
    monomialInitializeCost D B len≤2^103*X^3 := by
  have hsize : (4*(D+1)).bits.length≤4*X :=
    (cache_nat_bits_le _).trans (Nat.mul_le_mul_left 4 hd)
  have hdegree : D.bits.length≤X := (cache_nat_bits_le D).trans (by omega)
  have seed := monomialSeedCost_cap D B (4*(D+1)).bits.length X hX hd hb hsize
  have htail : D*(2^32*(B+18)^2)≤2^32*X^3 := by
    calc
      _≤X*(2^32*X^2) := by gcongr;omega
      _=_ := by ring
  have hcounter : (D+1)*(13*D.bits.length+15)≤28*X^2 := by
    calc
      _≤X*(28*X) := Nat.mul_le_mul hd (by omega)
      _=_ := by ring
  have hcopy : 6*len+15*(4*(D+1)).bits.length+21+
      (6*(4*(D+1)).bits.length+15*D.bits.length+21)≤150*X := by omega
  have h13 : X≤X^3 := le_self_pow₀ hX (by decide)
  have h23 : X^2≤X^3 := Nat.pow_le_pow_right hX (by decide)
  unfold monomialInitializeCost
  nlinarith only [seed,htail,hcounter,hcopy,h13,h23]

theorem allocateInitialCost_cap (D W len X : ℕ) (hX : 1≤X)
    (hd : D+1≤X) (hb : monomialWorkingWidth D W+18≤X) (hl : len≤X) :
    allocateInitialCost D W len≤2^105*X^3 := by
  have init := monomialInitializeCost_cap D (monomialWorkingWidth D W) len X hX hd hb hl
  have h23 : X^2≤X^3 := Nat.pow_le_pow_right hX (by decide)
  have halloc : 2^60*(3*monomialWorkingWidth D W+3)^2≤2^64*X^2 := by
    have h := Nat.pow_le_pow_left (show 3*monomialWorkingWidth D W+3≤4*X by omega) 2
    calc
      _≤2^60*(4*X)^2 := Nat.mul_le_mul_left _ h
      _=_ := by ring
  unfold allocateInitialCost
  nlinarith only [init,halloc,h23]

theorem monomialWorkingWidth_quadratic (D W : ℕ) :
    monomialWorkingWidth D W+18≤2^10*(D+W+4)^2 := by
  unfold monomialWorkingWidth monomialStorageWidth
  nlinarith [Nat.zero_le (D*W),Nat.zero_le (D^2),Nat.zero_le (W^2)]

theorem cachePairCost_polynomial (D W : ℕ) :
    cachePairCost D W D.bits.length≤2^138*(D+W+4)^6 := by
  let Z := D+W+4
  let X := 2^10*Z^2
  have hZ : 1≤Z := by dsimp [Z];omega
  have h12 : Z≤Z^2 := le_self_pow₀ hZ (by decide)
  have hX : 1≤X := by dsimp [X];have := one_le_pow₀ hZ (n:=2);omega
  have hd : D+1≤X := by dsimp [X,Z] at *;omega
  have hb : monomialWorkingWidth D W+18≤X := monomialWorkingWidth_quadratic D W
  have hl : D.bits.length≤X := (cache_nat_bits_le D).trans (by omega)
  have ha := allocateInitialCost_cap D W D.bits.length X hX hd hb hl
  have halloc : allocateInitialCost D W D.bits.length≤2^135*Z^6 := by
    calc
      _≤2^105*X^3 := ha
      _=_ := by dsimp [X];ring
  have h26 : Z^2≤Z^6 := Nat.pow_le_pow_right hZ (by decide)
  have headers : 256*(monomialWorkingWidth D W+1)+1024*(monomialWorkingWidth D W+1)≤
      2^22*Z^2 := by dsimp [X] at hb;nlinarith only [hb]
  change _≤2^138*Z^6
  unfold cachePairCost
  nlinarith only [halloc,headers,h26]

end Maxwell.Continuum.Calibration.RawCutoff
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open Calibration.RawCutoff
attribute [local irreducible] profileDegree runtimeBudget

theorem cachePreparationCost_polynomial (W : ℕ) : cachePreparationCost W≤2^172*(W+4)^2 := by
  have hr := cacheRuntimePrepareCost_polynomial W
  have hm := Nat.pow_le_pow_left (show 256*(W+3)+3≤512*(W+4) by omega) 2
  have ho : operationCost (256*(W+3))≤2^118*(W+4)^2 := by
    unfold operationCost
    nlinarith only [hm]
  have hh : W+1≤(W+4)^2 := by nlinarith
  have hpow := Nat.pow_le_pow_left (show W+2≤W+4 by omega) 2
  have hpos : 1≤(W+4)^2 := one_le_pow₀ (by omega)
  unfold cachePreparationCost
  nlinarith only [hr,ho,hh,hpow,hpos]

theorem monomialCacheCost_polynomial (N : ℕ) :
    monomialCacheCost N≤2^176*(profileDegree N+cacheSourceWidth N+4)^8 := by
  let D := profileDegree N
  let W := cacheSourceWidth N
  let Z := D+W+4
  have hZ : 1≤Z := by dsimp [Z];omega
  have hp := cachePreparationCost_polynomial W
  have hp' : cachePreparationCost W≤2^172*Z^2 := hp.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [Z];omega) 2))
  have pair := cachePairCost_polynomial D W
  change cachePairCost D W D.bits.length≤2^138*Z^6 at pair
  have hlen : D.bits.length≤monomialWorkingWidth D W := by
    have hd := cache_nat_bits_le D
    unfold monomialWorkingWidth monomialStorageWidth
    omega
  have outer := monomialOuterCost_polynomial D W D.bits.length hlen
  have outer' : monomialOuterCost D W D.bits.length≤2^144*Z^8 := by
    calc
      _≤2^144*(D+1)^6*(W+1)^2 := outer
      _≤2^144*Z^6*Z^2 := by gcongr <;> dsimp [Z] <;> omega
      _=_ := by ring
  have start : 30*D.bits.length+2048≤2^12*Z^2 := by
    have hd := cache_nat_bits_le D
    have hz : D≤Z := by dsimp [Z];omega
    have hs : Z≤Z^2 := le_self_pow₀ hZ (by decide)
    have hp : 1≤Z^2 := one_le_pow₀ hZ
    nlinarith only [hd,hz,hs,hp]
  have h28 : Z^2≤Z^8 := Nat.pow_le_pow_right hZ (by decide)
  have h68 : Z^6≤Z^8 := Nat.pow_le_pow_right hZ (by decide)
  change _≤2^176*Z^8
  change cachePreparationCost W+(cachePairCost D W D.bits.length+
    (30*D.bits.length+2048+monomialOuterCost D W D.bits.length))≤_
  nlinarith only [hp',pair,outer',start,h28,h68]

#print axioms monomialCacheCost_polynomial
end Maxwell.Continuum.Profile.Runtime

