import Maxwell.Continuum.FiniteAuxiliaryDyadic
import Maxwell.Continuum.ParameterBinaryBounds
import Maxwell.Continuum.DyadicMagnitudeBits

/-! Linear binary precision for the actual reciprocal well tuning. The
selector's stopping bound follows from explicit lower bounds on its budget. -/

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Realization

theorem zeta_binary_lower (d : ℕ) : (1/2 : ℚ)^(2*d)≤Parameters.zeta d := by
  change (1/2 : ℚ)^(2*d)≤(1/3 : ℚ)^d
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) d

theorem coupling_precision_binary (d : ℕ) :
    precisionBits ((Parameters.zeta d)^2/16) (by have := Parameters.zeta_pos d; positivity) ≤ 4*d+4 := by
  apply Parameters.precisionBits_le_of_binary
  have hz := pow_le_pow_left₀ (by norm_num : (0 : ℚ)≤(1/2)^(2*d)) (zeta_binary_lower d) 2
  have hh := div_le_div_of_nonneg_right hz (by norm_num : (0 : ℚ)≤16)
  convert hh using 1
  simp only [← pow_mul]
  rw [show 4*d+4=2*d*2+4 by omega,pow_add]
  norm_num
  ring

def onsitePrecision (L d : ℕ) (hL : 0<L) : ℕ :=
  precisionBits (scalarBudget ((L : ℚ)⁻¹^2) (Parameters.zeta d) ((2 : ℚ)^128*(L : ℚ)⁻¹^2))
    (scalarBudget_pos _ _ _ (by positivity) (Parameters.zeta_pos d) (by positivity))

theorem onsite_precision_binary {L ell : ℕ} (hL : 0<L) (hLe : L≤2^ell) (d : ℕ) :
    onsitePrecision L d hL ≤ 4*ell+4*d+1 := by
  have hLeQ : (L : ℚ)≤(2 : ℚ)^ell := by exact_mod_cast hLe
  have hLQ : (0 : ℚ)<L := by exact_mod_cast hL
  have hi := (inv_le_inv₀ (by positivity : (0 : ℚ)<2^ell) hLQ).mpr hLeQ
  have hi' : (1/2 : ℚ)^ell≤(L : ℚ)⁻¹ := by simpa only [one_div,inv_pow] using hi
  have hlo : (1/2 : ℚ)^(2*ell)≤(L : ℚ)⁻¹^2 := by
    simpa only [← pow_mul,Nat.mul_comm ell 2] using
      pow_le_pow_left₀ (by positivity : (0 : ℚ)≤(1/2)^ell) hi' 2
  have hz := zeta_binary_lower d
  have hprod := mul_le_mul
    (pow_le_pow_left₀ (by positivity : (0 : ℚ)≤(1/2)^(2*ell)) hlo 2)
    (pow_le_pow_left₀ (by positivity : (0 : ℚ)≤(1/2)^(2*d)) hz 2)
    (by positivity) (by positivity)
  have hsmall : (1/2 : ℚ)^(4*ell+4*d+1)≤((L : ℚ)⁻¹^2)^2*(Parameters.zeta d)^2/2 := by
    have hh := div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℚ)≤2)
    apply le_trans _ hh
    rw [← pow_mul,← pow_mul,← pow_add]
    rw [show 4*ell+4*d+1=(2*ell*2+2*d*2)+1 by omega,pow_succ]
    ring_nf
    exact le_rfl
  have hlower : (1/2 : ℚ)^(4*ell+4*d+1)≤(L : ℚ)⁻¹^2 :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : 2*ell≤4*ell+4*d+1)).trans hlo
  apply Parameters.precisionBits_le_of_binary
  apply le_min hlower
  apply le_min hsmall
  calc
    _ ≤ (L : ℚ)⁻¹^2 := hlower
    _ ≤ (2*2^128)*(L : ℚ)⁻¹^2 :=
      le_mul_of_one_le_left (sq_nonneg _) (by norm_num)
    _ = 2*((2 : ℚ)^128*(L : ℚ)⁻¹^2) := by ring

#print axioms coupling_precision_binary
#print axioms onsite_precision_binary

end Maxwell.Continuum.FiniteAuxiliary
