import Maxwell.Continuum.ParameterSpacingMachineData

namespace Maxwell.Continuum.Parameters.SpacingMachine
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048
attribute [local irreducible] values

theorem tests_iff (D : Data) (k : ℕ) :
    tests.any (Maxwell.Cost.SelectedParameters.AllComparisons.failed (values D k))=false ↔
      D.constant^8≤2^k ∧
      D.constant^4*D.length≤(2^k)^15 ∧
      (D.length:ℚ)^2/((2:ℚ)^1026*8^(2^k))≤1 ∧
      (D.constant:ℚ)^4*(D.length:ℚ)^12/3^(2^k)≤D.epsilonNum/(D.epsilonDen*2^24:ℚ) ∧
      (D.constant:ℚ)^4*(D.length:ℚ)^12/(3^(2^k):ℚ)^2≤
        ((D.length:ℚ)^2*D.epsilonNum*D.conditionDen)/
        (((2:ℚ)^1026*8^(2^k))*(D.epsilonDen*2^24)*D.conditionNum) := by
  obtain ⟨h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31⟩ := fields D k
  have h06 := input_fields D k 2006 (by decide)
  have h07 := input_fields D k 2007 (by decide)
  have h09 := input_fields D k 2009 (by decide)
  have h04 := input_fields D k 2004 (by decide)
  simp [inputs] at h06 h07 h09 h04
  simp only [tests,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_false_iff,
    Maxwell.Cost.SelectedParameters.AllComparisons.failed,decide_eq_false_iff_not,not_lt,
    h21,h31,h22,h24,h25,h26,h27,h28,h29,h30,h06,h07,h09,h04,
    Nat.cast_one,div_one,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
  norm_cast

theorem predicate (D : Data) (e k : ℕ) (hC : D.constant=2^e)
    (hKn : 0<D.conditionNum) (hKd : 0<D.conditionDen) (hEd : 0<D.epsilonDen) :
    tests.any (Maxwell.Cost.SelectedParameters.AllComparisons.failed (values D k))=false ↔
      SpacingTest e D.length ((D.conditionNum:ℚ)/D.conditionDen)
        ((D.epsilonNum:ℚ)/D.epsilonDen) (2^k) := by
  have hkn : (D.conditionNum:ℚ)≠0 := by exact_mod_cast hKn.ne'
  have hkd : (D.conditionDen:ℚ)≠0 := by exact_mod_cast hKd.ne'
  have hed : (D.epsilonDen:ℚ)≠0 := by exact_mod_cast hEd.ne'
  have ha : alpha D.length (2^k)=
      (D.length:ℚ)^2/((2:ℚ)^1026*8^(2^k)) := by
    simp only [alpha,one_div,inv_pow]
    ring
  have hz : zeta (2^k)=((3:ℚ)^(2^k))⁻¹ := by
    simp [zeta,one_div,inv_pow]
  have heps : (D.epsilonNum:ℚ)/(D.epsilonDen*2^24)=
      ((D.epsilonNum:ℚ)/D.epsilonDen)/2^24 := by ring
  have hsecond : ((D.length:ℚ)^2*D.epsilonNum*D.conditionDen)/
      (((2:ℚ)^1026*8^(2^k))*(D.epsilonDen*2^24)*D.conditionNum)=
      alpha D.length (2^k)*((D.epsilonNum:ℚ)/D.epsilonDen)/
        (2^24*((D.conditionNum:ℚ)/D.conditionDen)) := by
    rw [ha]
    field_simp
  rw [tests_iff,hC]
  simp only [Nat.cast_pow,Nat.cast_ofNat,← ha,heps,hsecond]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5⟩
    refine ⟨h1,by exact_mod_cast h2,h3,?_,?_⟩
    · simpa only [hz,div_eq_mul_inv] using h4
    · simpa only [hz,inv_pow,div_eq_mul_inv] using h5
  · intro h
    refine ⟨h.spacing,by exact_mod_cast h.fifteenth,h.alpha_le,?_,?_⟩
    · simpa only [hz,div_eq_mul_inv] using h.first
    · simpa only [hz,inv_pow,div_eq_mul_inv] using h.second

#print axioms predicate

end Maxwell.Continuum.Parameters.SpacingMachine
