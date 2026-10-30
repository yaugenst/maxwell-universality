import Maxwell.Continuum.CalibrationFiniteAlgorithm
import Maxwell.Continuum.ParameterProfileResources

/-! Explicit polylogarithmic dimensions and linear precision bounds for
the literal finite calibration program. The master constant remains
symbolic; no physical-size array is evaluated by these proofs. -/

namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

attribute [local irreducible] MasterConstants.exponent

def lengthCoefficient (C : ℕ) : ℕ := Nat.clog 2 (C+1)+6
def iterationCoefficient (C : ℕ) : ℕ := 2^114*(C+5)
def workCoefficient (C : ℕ) : ℕ := 2^122*(C+5)
def windowCoefficient (C : ℕ) : ℕ := workCoefficient C+lengthCoefficient C+98
def sizeCoefficient (C : ℕ) : ℕ :=
  2*((2 : ℕ)^(4*MasterConstants.exponent)*C*(windowCoefficient C)^2+16*(2*C+1))
def rootLogCoefficient (C : ℕ) : ℕ := Nat.clog 2 (sizeCoefficient C+1)+9
def precisionCoefficient (C : ℕ) : ℕ :=
  workCoefficient C+2*lengthCoefficient C+4*rootLogCoefficient C+256
def inverseCoefficient (C : ℕ) : ℕ := precisionCoefficient C+16*lengthCoefficient C+2+2^20
def cutoffCoefficient (C : ℕ) : ℕ := precisionCoefficient C+2*lengthCoefficient C+6

theorem lengthBits_polynomial {x C ℓ : ℕ} (hℓ : 0<ℓ) (k : ℕ) (hx : x≤C*ℓ^k) :
    lengthBits x≤(Nat.clog 2 (C+1)+k)*ℓ := by
  have h1 : 1≤ℓ^k := one_le_pow₀ (by omega)
  have hc : x+1≤2^(Nat.clog 2 (C+1)+k*ℓ) := by
    calc
      _ ≤ (C+1)*ℓ^k := by nlinarith only [hx,h1]
      _ ≤ 2^(Nat.clog 2 (C+1))*(2^ℓ)^k :=
        Nat.mul_le_mul (Nat.le_pow_clog (by decide) _)
          (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := ℓ)).le k)
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; ring
  have hb := Nat.clog_le_of_le_pow hc
  have hh : Nat.clog 2 (C+1)≤Nat.clog 2 (C+1)*ℓ := Nat.le_mul_of_pos_right _ hℓ
  unfold lengthBits
  nlinarith only [hb,hh]

theorem iterations_linear {N C ℓ : ℕ} (hℓ : 0<ℓ) (hN : N≤C*ℓ) :
    iterations N≤ iterationCoefficient C*ℓ := by
  have h := Parameters.powerSteps_bound (targetPrecision N)
  have hn : targetPrecision N+1≤(C+5)*ℓ := by unfold targetPrecision; nlinarith only [hN,hℓ]
  exact h.trans ((Nat.mul_le_mul_left _ hn).trans_eq (by unfold iterationCoefficient; ring))

theorem workPrecision_linear {N C ℓ : ℕ} (hℓ : 0<ℓ) (hN : N≤C*ℓ) :
    workPrecision N≤workCoefficient C*ℓ := by
  have h := Parameters.powerWorkPrecision_bound (targetPrecision N)
  have hn : targetPrecision N+1≤(C+5)*ℓ := by unfold targetPrecision; nlinarith only [hN,hℓ]
  exact h.trans ((Nat.mul_le_mul_left _ hn).trans_eq (by unfold workCoefficient; ring))

private theorem size_polynomial_algebra {L r n b C ℓ W : ℕ} (A : ℕ) (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hwindow : n+96+b+2≤W*ℓ) :
    2*(A*L*(n+96+b+2)^2+16*(L+r+1))≤
      (2*(A*C*W^2+16*(2*C+1)))*ℓ^8 := by
  have hfirst := Nat.mul_le_mul hL (Nat.pow_le_pow_left hwindow 2)
  have hL7 := hL.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_right hℓ (by decide : 6≤7)))
  have h1 : 1≤ℓ^7 := one_le_pow₀ (by omega)
  have hlast : L+r+1≤(2*C+1)*ℓ^8 := by
    have h7 : L+r+1≤(2*C+1)*ℓ^7 := by nlinarith only [hL7,hr,h1]
    exact h7.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hℓ (by decide : 7≤8)))
  calc
    _ ≤ 2*(A*(C*ℓ^6*(W*ℓ)^2)+16*((2*C+1)*ℓ^8)) := by
      apply Nat.mul_le_mul_left
      apply Nat.add_le_add
      · rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hfirst
      · exact Nat.mul_le_mul_left _ hlast
    _ = _ := by ring

theorem size_polynomial {L r N C ℓ : ℕ} (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) :
    size L r N≤sizeCoefficient C*ℓ^8 := by
  have hw := workPrecision_linear hℓ hN
  have hl : lengthBits L≤lengthCoefficient C*ℓ := lengthBits_polynomial hℓ 6 hL
  have hwindow : workPrecision N+96+lengthBits L+2≤windowCoefficient C*ℓ := by
    unfold windowCoefficient
    nlinarith only [hw,hl,hℓ]
  exact size_polynomial_algebra ((2 : ℕ)^(4*MasterConstants.exponent)) hℓ hL hr hwindow

theorem rootBits_linear {L r N C ℓ : ℕ} (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) :
    rootBits L r N≤rootLogCoefficient C*ℓ := by
  have h := lengthBits_polynomial hℓ 8 (size_polynomial hℓ hL hr hN)
  unfold rootBits rootLogCoefficient
  nlinarith only [h,hℓ]

theorem precision_linear {L r N C ℓ : ℕ} (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) :
    precision L r N≤precisionCoefficient C*ℓ := by
  have hw := workPrecision_linear hℓ hN
  have hl : lengthBits L≤lengthCoefficient C*ℓ := lengthBits_polynomial hℓ 6 hL
  have hrb := rootBits_linear hℓ hL hr hN
  unfold precision precisionCoefficient
  nlinarith only [hw,hl,hrb,hℓ]

theorem inverseSteps_linear {L r N C ℓ : ℕ} (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) :
    inverseSteps L r N≤ inverseCoefficient C*ℓ := by
  have hw := precision_linear hℓ hL hr hN
  have hl : lengthBits L≤lengthCoefficient C*ℓ := lengthBits_polynomial hℓ 6 hL
  unfold inverseSteps aliasSteps inverseCoefficient
  nlinarith only [hw,hl,hℓ]

theorem cutoffBits_linear {L r N C ℓ : ℕ} (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) :
    cutoffBits L r N≤cutoffCoefficient C*ℓ := by
  have hw := precision_linear hℓ hL hr hN
  have hl : lengthBits L≤lengthCoefficient C*ℓ := lengthBits_polynomial hℓ 6 hL
  unfold cutoffBits cutoffWorkBits cutoffCoefficient
  nlinarith only [hw,hl,hℓ]

def linearCoefficient (C : ℕ) : ℕ := C+lengthCoefficient C+iterationCoefficient C+
  workCoefficient C+rootLogCoefficient C+precisionCoefficient C+inverseCoefficient C+cutoffCoefficient C

theorem parameters_linear {L r N C ℓ : ℕ} (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) :
    N≤linearCoefficient C*ℓ ∧ lengthBits L≤linearCoefficient C*ℓ ∧
    iterations N≤linearCoefficient C*ℓ ∧ workPrecision N≤linearCoefficient C*ℓ ∧
    rootBits L r N≤linearCoefficient C*ℓ ∧ precision L r N≤linearCoefficient C*ℓ ∧
    inverseSteps L r N≤linearCoefficient C*ℓ ∧ cutoffBits L r N≤linearCoefficient C*ℓ := by
  have lift {x a : ℕ} (hx : x≤a*ℓ) (ha : a≤linearCoefficient C) :
      x≤linearCoefficient C*ℓ := hx.trans (Nat.mul_le_mul_right _ ha)
  refine ⟨lift hN ?_,lift (lengthBits_polynomial hℓ 6 hL) ?_,
    lift (iterations_linear hℓ hN) ?_,lift (workPrecision_linear hℓ hN) ?_,
    lift (rootBits_linear hℓ hL hr hN) ?_,lift (precision_linear hℓ hL hr hN) ?_,
    lift (inverseSteps_linear hℓ hL hr hN) ?_,lift (cutoffBits_linear hℓ hL hr hN) ?_⟩ <;>
    unfold linearCoefficient lengthCoefficient <;> omega

#print axioms size_polynomial
#print axioms parameters_linear

end Maxwell.Continuum.Calibration.FiniteAlgorithm
