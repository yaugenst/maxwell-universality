import Maxwell.Continuum.CalibrationBumpPolynomial
import Maxwell.Continuum.CalibrationFiniteAlgorithm
import Maxwell.Codec.NaturalLength

/-! Exact integer formulas for the requested root coefficient table.
The scale is represented by its actual nonnegative numerator and positive
denominator; no precomputed degree or sampling parameters are inputs. -/
namespace Maxwell.Continuum.Calibration.RootParameters
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] MasterConstants.exponent

local notation "multiplier" => (2^(3*MasterConstants.exponent):ℕ)
def numerator (a N ell : ℕ) : ℕ := multiplier*a*(N+ell+2)^2
def degree (a b N ell : ℕ) : ℕ := (numerator a N ell+b-1)/b
def grid (a b N ell : ℕ) : ℕ := 2*degree a b N ell+1
def bits (a b N ell : ℕ) : ℕ := N+3*(2*degree a b N ell).bits.length+8

theorem ceil_fraction (a b : ℕ) (hb : 0<b) :
    ⌈((a:ℚ)/b)⌉₊=(a+b-1)/b := by
  apply eq_of_forall_ge_iff
  intro n
  rw [Nat.ceil_le,div_le_iff₀ (Nat.cast_pos.mpr hb),←Nat.cast_mul,Nat.cast_le,
    Nat.div_le_iff_le_mul_add_pred hb]
  rw [Nat.mul_comm n b]
  omega

theorem degree_eq (a b N ell : ℕ) (hb : 0<b) :
    degree a b N ell=rootDegree ((a:ℚ)/b) N ell := by
  have value : rootDegreeValue ((a:ℚ)/b) N ell=(numerator a N ell:ℚ)/b := by
    unfold rootDegreeValue numerator
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    change (2:ℚ)^(3*MasterConstants.exponent)*(a/b)*((N+ell+2:ℕ):ℚ)^2 =
      (2:ℚ)^(3*MasterConstants.exponent)*a*((N+ell+2:ℕ):ℚ)^2/b
    simp only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
  rw [rootDegree,value,ceil_fraction _ _ hb]
  rfl

theorem grid_eq (a b N ell : ℕ) (hb : 0<b) :
    grid a b N ell=rootSamplingGrid ((a:ℚ)/b) N ell := by
  rw [grid,rootSamplingGrid,degree_eq _ _ _ _ hb]

theorem bits_eq (a b N ell : ℕ) (hb : 0<b) :
    bits a b N ell=rootSamplingBits ((a:ℚ)/b) N ell := by
  rw [bits,rootSamplingBits,rootCoefficientGuard,←degree_eq _ _ _ _ hb,
    Maxwell.Codec.clog_two_succ]

theorem selected_degree (L r N : ℕ) (hL : 0<L) :
    degree (2*FiniteAlgorithm.size L r N) L (FiniteAlgorithm.precision L r N)
      (FiniteAlgorithm.rootBits L r N)=rootDegree (FiniteAlgorithm.scale L r N)
        (FiniteAlgorithm.precision L r N) (FiniteAlgorithm.rootBits L r N) := by
  rw [degree_eq _ _ _ _ hL]
  simp only [FiniteAlgorithm.scale,torusScale,Nat.cast_mul,Nat.cast_ofNat]

#print axioms degree_eq
#print axioms grid_eq
#print axioms bits_eq
#print axioms selected_degree
end Maxwell.Continuum.Calibration.RootParameters
