import Maxwell.Continuum.ParameterResources
import Maxwell.Codec.Bounds

/-! Literal reduced-rational widths of the selected detuning and of the
floor-exponential rational comparisons. These are representation bounds,
independent of any unit-cost arithmetic assumption. -/

namespace Maxwell.Continuum.Parameters
set_option exponentiation.threshold 4096

theorem inverse_two_pow_bits (a : ℕ) : rationalBitLength (((2 : ℚ)^a)⁻¹) = a+3 := by
  rw [show (2 : ℚ)^a = ((2^a : ℕ) : ℚ) by norm_cast]
  unfold rationalBitLength
  rw [Rat.inv_natCast_num_of_pos (by positivity), Rat.inv_natCast_den_of_pos (by positivity)]
  rw [Dyadic.denominator_bitLength]
  norm_num [signedBitLength, unsignedBitLength]
  omega

theorem rationalDecay_bits (t : ℕ) : rationalBitLength (rationalDecay t) = t/slowDivisor+3 := by
  unfold rationalDecay
  rw [one_div, inv_pow]
  exact inverse_two_pow_bits _

def tauBits (L d : ℕ) (hL : 0 < L) : ℕ :=
  Realization.precisionBits (tauBudget L d) (tauBudget_pos hL d)

theorem tau_bits_exact (L d : ℕ) (hL : 0 < L) :
    rationalBitLength (tau L d hL) = tauBits L d hL+3 := by
  change rationalBitLength (1/(2 : ℚ)^tauBits L d hL) = _
  rw [one_div]
  exact inverse_two_pow_bits _

theorem tauBits_le_binary {L a : ℕ} (hL : 0 < L) (hLa : L ≤ 2^a) (d : ℕ) :
    tauBits L d hL ≤ 25+4*a+4*d := by
  have hh := tau_inverse_binary hL hLa d
  change (1/(2 : ℚ)^tauBits L d hL)⁻¹ ≤ _ at hh
  rw [one_div, inv_inv] at hh
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp hh

theorem stageTau_bits (I : Input) (e k : ℕ) :
    rationalBitLength (stageTau I e k) ≤ 28+12*k+4*stageSpacing I e k := by
  rw [stageTau, tau_bits_exact]
  have h := tauBits_le_binary (stageLength_pos k)
    (show stageLength k ≤ 2^(3*k) by exact_mod_cast (stageLength_binary k).le) (stageSpacing I e k)
  omega

theorem selected_tau_bits {I : Input} {M e p base ℓ : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hb : base ≤ M) (hℓ : 0 < ℓ) :
    let k := selectedOuterExponent I e base ℓ hℓ
    rationalBitLength (stageTau I e k) ≤ (28+204*M+4*2^(9*M))*ℓ := by
  have hk := (selectedOuter_le_candidate hI hM he hp hb hℓ).trans
    (candidate_exponent_le (by omega) hℓ)
  have hd := (selected_scales hI hM he hp hb hℓ).2.1
  have h := stageTau_bits I e (selectedOuterExponent I e base ℓ hℓ)
  calc
    _ ≤ 28+12*(17*M*ℓ)+4*(2^(9*M)*ℓ) := h.trans
      (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 12 hk) 28)
        (Nat.mul_le_mul_left 4 hd))
    _ ≤ _ := by nlinarith

theorem selected_decay_bits {I : Input} {M e p base ℓ : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hb : base ≤ M) (hℓ : 0 < ℓ) :
    let k := selectedOuterExponent I e base ℓ hℓ
    rationalBitLength (rationalDecay (stageLength k)) ≤ 2^(6+45*M)*ℓ^6+3 ∧
    rationalBitLength (rationalDecay (2^k)) ≤ 2^(6+45*M)*ℓ^6+3 ∧
    rationalBitLength (rationalDecay (stageBuffer I e k)) ≤ 2^(11*M)*ℓ+3 := by
  have hs := selected_scales hI hM he hp hb hℓ
  have htwo : 2^selectedOuterExponent I e base ℓ hℓ ≤
      stageLength (selectedOuterExponent I e base ℓ hℓ) :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 8) _
  simp only [rationalDecay_bits]
  exact ⟨Nat.add_le_add_right ((Nat.div_le_self _ _).trans hs.1) 3,
    Nat.add_le_add_right ((Nat.div_le_self _ _).trans (htwo.trans hs.1)) 3,
    Nat.add_le_add_right ((Nat.div_le_self _ _).trans hs.2.2.1) 3⟩

#print axioms selected_tau_bits
#print axioms selected_decay_bits

end Maxwell.Continuum.Parameters
