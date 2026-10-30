import Maxwell.Continuum.ParameterPowerSearch
import Maxwell.Continuum.ParameterDyadic

/-! Literal five-test spacing search. The exponent of the fixed master
constant is an input, so executing the search never requires a compiled
closed expansion of an astronomical integer. -/

namespace Maxwell.Continuum.Parameters

set_option exponentiation.threshold 2048

structure SpacingTest (e L : ℕ) (K ε : ℚ) (d : ℕ) : Prop where
  spacing : (2^e)^8 ≤ d
  fifteenth : ((2 : ℚ)^e)^4*(L : ℚ) ≤ (d : ℚ)^15
  alpha_le : alpha L d ≤ 1
  first : ((2 : ℚ)^e)^4*(L : ℚ)^12*zeta d ≤ ε/2^24
  second : ((2 : ℚ)^e)^4*(L : ℚ)^12*(zeta d)^2 ≤ alpha L d*ε/(2^24*K)

instance spacingTestDecidable (e L : ℕ) (K ε : ℚ) (d : ℕ) :
    Decidable (SpacingTest e L K ε d) :=
  decidable_of_iff
    ((2^e)^8 ≤ d ∧ ((2 : ℚ)^e)^4*(L : ℚ) ≤ (d : ℚ)^15 ∧
      alpha L d ≤ 1 ∧ ((2 : ℚ)^e)^4*(L : ℚ)^12*zeta d ≤ ε/2^24 ∧
      ((2 : ℚ)^e)^4*(L : ℚ)^12*(zeta d)^2 ≤ alpha L d*ε/(2^24*K))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
      fun h => ⟨h.spacing, h.fifteenth, h.alpha_le, h.first, h.second⟩⟩

def spacingThreshold (e a b c : ℕ) : ℕ :=
  (2^e)^8 + 2^((4*e+a+14)/15) + 8*(1050+4*e+12*a+b+c+2)

private theorem binary_absorption {A c d : ℕ} (hd : A+c ≤ d) :
    (2 : ℚ)^A*(1/2)^d ≤ (1/2)^c := by
  calc
    _ ≤ (2 : ℚ)^A*(1/2)^(A+c) := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hd) (by positivity)
    _ = _ := by
      rw [pow_add, ← mul_assoc, ← mul_pow]
      norm_num

private theorem slow_geometric_bound {N d : ℕ} (hd : 8*N ≤ d) :
    (8/9 : ℚ)^d ≤ (1/2)^N := by
  calc
    _ ≤ (8/9 : ℚ)^(8*N) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
    _ = ((8/9 : ℚ)^8)^N := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by norm_num) N

private theorem coefficient_bound {L a : ℕ} (hL : L ≤ 2^a) (e n : ℕ) :
    ((2 : ℚ)^e)^4*(L : ℚ)^n ≤ (2 : ℚ)^(4*e+n*a) := by
  have hp : (L : ℚ) ≤ (2 : ℚ)^a := by exact_mod_cast hL
  calc
    _ ≤ ((2 : ℚ)^e)^4*((2 : ℚ)^a)^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp n) (by positivity)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring

private theorem zeta_square (d : ℕ) :
    (zeta d)^2 = (1/8 : ℚ)^d*(8/9 : ℚ)^d := by
  rw [zeta, ← mul_pow]
  calc
    ((1/3 : ℚ)^d)^2 = ((1/3 : ℚ)^2)^d := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = _ := by norm_num

private theorem second_spacing_of_reduced {e L d : ℕ} {K ε : ℚ} (hK : 0 < K)
    (h : (2 : ℚ)^1050*((2 : ℚ)^e)^4*(L : ℚ)^10*K*(8/9)^d ≤ ε) :
    ((2 : ℚ)^e)^4*(L : ℚ)^12*(zeta d)^2 ≤ alpha L d*ε/(2^24*K) := by
  apply (le_div_iff₀ (mul_pos (by positivity) hK)).mpr
  have ha : 0 ≤ alpha L d := by unfold alpha; positivity
  have hm := mul_le_mul_of_nonneg_left h ha
  convert hm using 1
  rw [zeta_square, alpha]
  have hp : (2 : ℚ)^1050 = (2 : ℚ)^1026*2^24 := by rw [← pow_add]
  rw [hp]
  ring

/-- An explicit integer threshold simultaneously passes all five rational
spacing tests. In particular no success premise is used to prove termination. -/
theorem spacingThreshold_spec {e L a b c d : ℕ} {K ε : ℚ}
    (hL : L ≤ 2^a) (hK : 0 < K) (hKb : K ≤ (2 : ℚ)^b)
    (hε : (1/2 : ℚ)^c ≤ ε) (hd : spacingThreshold e a b c ≤ d) :
    SpacingTest e L K ε d := by
  have hds : (2^e)^8 ≤ d :=
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hd)
  have hr : 2^((4*e+a+14)/15) ≤ d :=
    (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans hd)
  have hg : 8*(1050+4*e+12*a+b+c+2) ≤ d := (Nat.le_add_left _ _).trans hd
  refine ⟨hds, ?_, ?_, ?_, ?_⟩
  · have he : 4*e+a ≤ ((4*e+a+14)/15)*15 := by omega
    have hp : (2^e)^4*L ≤ d^15 := calc
      _ ≤ (2^e)^4*2^a := Nat.mul_le_mul_left _ hL
      _ = 2^(4*e+a) := by rw [← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ 2^(((4*e+a+14)/15)*15) := Nat.pow_le_pow_right (by omega) he
      _ = (2^((4*e+a+14)/15))^15 := pow_mul _ _ _
      _ ≤ _ := Nat.pow_le_pow_left hr _
    exact_mod_cast hp
  · have hp : (L : ℚ)^2 ≤ (2 : ℚ)^(2*a) := by
      have hh : (L : ℚ) ≤ (2 : ℚ)^a := by exact_mod_cast hL
      simpa only [← pow_mul, Nat.mul_comm a 2] using pow_le_pow_left₀ (by positivity) hh 2
    have hi : ((2 : ℚ)^1026)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hz : (1/8 : ℚ)^d ≤ (1/2 : ℚ)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc
      alpha L d ≤ (L : ℚ)^2*(1/8)^d := by
        unfold alpha
        exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (by positivity) hi) (by positivity)
      _ ≤ (2 : ℚ)^(2*a)*(1/2)^d := mul_le_mul hp hz (by positivity) (by positivity)
      _ ≤ (1/2 : ℚ)^0 := binary_absorption (by omega)
      _ = 1 := pow_zero _
  · apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2^24)).mpr
    have hz : zeta d ≤ (1/2 : ℚ)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc
      ((2 : ℚ)^e)^4*(L : ℚ)^12*zeta d*2^24
          ≤ (2 : ℚ)^(4*e+12*a)*(1/2)^d*2^24 :=
        mul_le_mul_of_nonneg_right (mul_le_mul (coefficient_bound hL e 12) hz
          (zeta_pos d).le (by positivity)) (by positivity)
      _ = (2 : ℚ)^(24+4*e+12*a)*(1/2)^d := by rw [pow_add, pow_add, pow_add]; ring
      _ ≤ (1/2 : ℚ)^c := binary_absorption (by omega)
      _ ≤ ε := hε
  · apply second_spacing_of_reduced hK
    have hcoef : (2 : ℚ)^1050*((2 : ℚ)^e)^4*(L : ℚ)^10*K ≤
        (2 : ℚ)^(1050+4*e+10*a+b) := by
      calc
        _ = (2 : ℚ)^1050*(((2 : ℚ)^e)^4*(L : ℚ)^10)*K := by ring
        _ ≤ (2 : ℚ)^1050*(2 : ℚ)^(4*e+10*a)*(2 : ℚ)^b :=
          mul_le_mul (mul_le_mul_of_nonneg_left (coefficient_bound hL e 10) (by positivity))
            hKb hK.le (by positivity)
        _ = _ := by rw [← pow_add, ← pow_add]; congr 1; ring
    calc
      _ ≤ (2 : ℚ)^(1050+4*e+10*a+b)*(1/2)^(1050+4*e+10*a+b+c) :=
        mul_le_mul hcoef (slow_geometric_bound (by omega)) (by positivity) (by positivity)
      _ ≤ (1/2 : ℚ)^c := binary_absorption le_rfl
      _ ≤ ε := hε

#print axioms spacingThreshold_spec

end Maxwell.Continuum.Parameters
