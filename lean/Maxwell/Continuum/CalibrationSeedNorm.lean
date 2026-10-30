import Maxwell.Continuum.CalibrationSupercellSeedPhysical
import Maxwell.Continuum.CalibrationFiniteSeedError

/-! The actual well seed has a quantitative nonzero norm and its
normalization is exactly the continuum starting vector. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open FreeFiber EffectiveMass MasterConstants NormedSpace

attribute [local irreducible] startingEnvelope startingVector referencePhysicalMode
  Supercell.embedding Supercell.exactRootSeed CornerBridge.topState

theorem startingEnvelope_norm_lower {h : ℝ} (hh : 0 < h) (hsmall : h ≤ 1/(2 : ℝ)^1024) :
    (1/2 : ℝ)^39 ≤ ‖startingEnvelope hh‖ := by
  have hl := startingEnvelope_reference_overlap hh hsmall
  have hu := (Complex.re_le_norm (inner ℂ (startingEnvelope hh) (referencePhysicalMode hh))).trans
    ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (referencePhysicalMode_norm_le hh) (norm_nonneg _)))
  norm_num only [show (1/2 : ℝ)^39=1/(2 : ℝ)^39 by norm_num]
  norm_num at hl ⊢
  linarith

namespace Supercell

variable (M : ℕ) [NeZero M]

theorem exactRootSeed_physical {L : ℝ} (hL : Ls ≤ L) (hEven : Even M)
    (hM : 16*(L+1)≤(M : ℝ)) (s : ℝ) (hs : 4≤s) (hscale : s=2*(M : ℝ)/L) :
    embedding M (exactRootSeed M s hs)=((s^(-(3/2 : ℝ)) : ℝ) : ℂ) •
      startingEnvelope (inverse_length_pos hL) := by
  subst s
  rw [exactRootSeed]
  exact embedding_well_seed M hEven (length_ge_one hL) hM hs

theorem exactRootSeed_normalize {L : ℝ} (hL : Ls ≤ L) (hEven : Even M)
    (hM : 16*(L+1)≤(M : ℝ)) (s : ℝ) (hs : 4≤s) (hscale : s=2*(M : ℝ)/L) :
    embedding M (normalize (exactRootSeed M s hs))=startingVector (inverse_length_pos hL) := by
  rw [embedding_normalize,exactRootSeed_physical M hL hEven hM s hs hscale]
  have hsreal : (((s^(-(3/2 : ℝ)) : ℝ) : ℂ) • startingEnvelope (inverse_length_pos hL)) =
      (s^(-(3/2 : ℝ)) : ℝ) • startingEnvelope (inverse_length_pos hL) := by
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
  rw [hsreal,normalize_smul_of_pos (Real.rpow_pos_of_pos (by linarith : 0<s) _),startingVector]

theorem exactRootSeed_norm_lower {L : ℝ} (hL : Ls ≤ L) (hEven : Even M)
    (hM : 16*(L+1)≤(M : ℝ)) (s : ℝ) (hs : 4≤s) (hscale : s=2*(M : ℝ)/L)
    (ell : ℕ) (hlog : s≤(2 : ℝ)^ell) :
    (1/2 : ℝ)^(39+2*ell) ≤ ‖exactRootSeed M s hs‖ := by
  have hs0 : 0<s := by linarith
  have hsq : s^2 ≤ (2 : ℝ)^(2*ell) := by
    have h := pow_le_pow_left₀ hs0.le hlog 2
    simpa only [← pow_mul,Nat.mul_comm ell 2] using h
  have hp : s^(-(2 : ℝ)) ≤ s^(-(3/2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤s) (by norm_num)
  rw [Real.rpow_neg hs0.le,Real.rpow_two] at hp
  have hfactor : (1/2 : ℝ)^(2*ell) ≤ s^(-(3/2 : ℝ)) := by
    have h := (inv_le_inv₀ (by positivity : 0 < (2 : ℝ)^(2*ell)) (sq_pos_of_pos hs0)).mpr hsq
    have he : ((2 : ℝ)^(2*ell))⁻¹=(1/2 : ℝ)^(2*ell) := by rw [one_div,inv_pow]
    rw [he] at h
    exact h.trans hp
  rw [← embedding_norm M,exactRootSeed_physical M hL hEven hM s hs hscale,norm_smul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
  rw [pow_add]
  rw [mul_comm ((1/2 : ℝ)^39)]
  exact mul_le_mul hfactor
    (startingEnvelope_norm_lower (inverse_length_pos hL) (inverse_length_le_1024 hL))
    (by positivity) (Real.rpow_nonneg hs0.le _)

#print axioms exactRootSeed_norm_lower
#print axioms exactRootSeed_normalize

end Supercell
end Maxwell.Continuum.Calibration
