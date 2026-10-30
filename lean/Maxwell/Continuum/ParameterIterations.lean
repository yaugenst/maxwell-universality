import Maxwell.Continuum.ParameterPrecision

/-! Uniform bounds include every failed outer candidate, not only the
returned one. The count includes all spacing, dyadic, buffer, and final tests. -/

namespace Maxwell.Continuum.Parameters
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

def stageChecks (I : Input) (e k : ℕ) : ℕ :=
  5*(stageSpacing I e k).bits.length+(stageBuffer I e k).bits.length+
    tauBits (stageLength k) (stageSpacing I e k) (stageLength_pos k)+3

def stageCheckCoefficient (M : ℕ) : ℕ := 40+260*M+4*2^(9*M)

theorem stage_checks_before_candidate {I : Input} {M e p ℓ k : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hℓ : 0 < ℓ)
    (hk : k ≤ outerCandidateExponent M ℓ) : stageChecks I e k ≤ stageCheckCoefficient M*ℓ := by
  have hk' := hk.trans (candidate_exponent_le (by omega) hℓ)
  have hd := spacing_before_candidate hI hM he hp hℓ hk
  have ht := buffer_before_candidate hI hM he hp hℓ hk
  have hdb := bits_le_polynomial_scale (r := 1) (by simpa only [pow_one] using hd)
  have htb := bits_le_polynomial_scale (r := 1) (by simpa only [pow_one] using ht)
  simp only [Nat.one_mul] at hdb htb
  have hτ := tauBits_le_binary (stageLength_pos k)
    (show stageLength k ≤ 2^(3*k) by exact_mod_cast (stageLength_binary k).le) (stageSpacing I e k)
  have hdl : (stageSpacing I e k).bits.length ≤ (9*M+2)*ℓ := by
    have hh := Nat.mul_le_mul_right (9*M+1) (show 1 ≤ ℓ by omega)
    nlinarith only [hdb, hh]
  have htl : (stageBuffer I e k).bits.length ≤ (11*M+2)*ℓ := by
    have hh := Nat.mul_le_mul_right (11*M+1) (show 1 ≤ ℓ by omega)
    nlinarith only [htb, hh]
  have hτl : tauBits (stageLength k) (stageSpacing I e k) (stageLength_pos k) ≤
      (25+204*M+4*2^(9*M))*ℓ := by
    have h25 := Nat.mul_le_mul_left 25 (show 1 ≤ ℓ by omega)
    nlinarith only [hτ, hk', hd, h25]
  have h3 := Nat.mul_le_mul_left 3 (show 1 ≤ ℓ by omega)
  unfold stageChecks stageCheckCoefficient
  nlinarith only [hdl, htl, hτl, h3]

def totalChecks (I : Input) (e base ℓ : ℕ) (hℓ : 0 < ℓ) : ℕ :=
  ∑ r ∈ Finset.range (selectedOuterSteps I e base ℓ hℓ+1),
    stageChecks I e (initialExponent base ℓ+r)

theorem totalChecks_bound {I : Input} {M e p base ℓ : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hb : base ≤ M) (hℓ : 0 < ℓ) :
    totalChecks I e base ℓ hℓ ≤ (17*M+1)*stageCheckCoefficient M*ℓ^2 := by
  have hk := selectedOuter_le_candidate hI hM he hp hb hℓ
  have hkn := hk.trans (candidate_exponent_le (by omega) hℓ)
  have hcount : selectedOuterSteps I e base ℓ hℓ+1 ≤ (17*M+1)*ℓ := by
    unfold selectedOuterExponent at hkn
    nlinarith only [hkn, hℓ]
  have hsum : totalChecks I e base ℓ hℓ ≤
      (selectedOuterSteps I e base ℓ hℓ+1)*(stageCheckCoefficient M*ℓ) := by
    unfold totalChecks
    calc
      _ ≤ ∑ _r ∈ Finset.range (selectedOuterSteps I e base ℓ hℓ+1), stageCheckCoefficient M*ℓ := by
        apply Finset.sum_le_sum
        intro r hr
        have hr' := Finset.mem_range.mp hr
        apply stage_checks_before_candidate hI hM he hp hℓ
        apply le_trans _ hk
        unfold selectedOuterExponent
        omega
      _ = _ := by simp
  calc
    _ ≤ (selectedOuterSteps I e base ℓ hℓ+1)*(stageCheckCoefficient M*ℓ) := hsum
    _ ≤ ((17*M+1)*ℓ)*(stageCheckCoefficient M*ℓ) := Nat.mul_le_mul_right _ hcount
    _ = _ := by ring

#print axioms stage_checks_before_candidate
#print axioms totalChecks_bound

end Maxwell.Continuum.Parameters
