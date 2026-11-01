import Maxwell.Continuum.ParameterBufferMachineData

namespace Maxwell.Continuum.Parameters.BufferMachine
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048
attribute [local irreducible] values

theorem tests_iff (D : Data) (k : ℕ) :
    tests.any (Maxwell.Cost.SelectedParameters.AllComparisons.failed (values D k))=false ↔
      (numerator D (2^k):ℚ)/denominator D  ≤  2^((2^k)/slowDivisor) := by
  obtain ⟨_,hn,hd⟩ := fields D k
  have hp := input_fields D k 2117 (by decide)
  have h1 := input_fields D k 2120 (by decide)
  simp [inputs] at hp h1
  simp only [tests,List.any_cons,List.any_nil,Bool.or_false,
    Maxwell.Cost.SelectedParameters.AllComparisons.failed,decide_eq_false_iff_not,not_lt,
    hn,hd,hp,h1,Nat.cast_one,div_one,Nat.cast_pow,Nat.cast_ofNat]

theorem ratio (D : Data) (e d t : ℕ) (hC : D.constant=2^e)
    (hKd : 0<D.conditionDen) (hAn : 0<D.alphaNum) (hAd : 0<D.alphaDen)
    (hTn : 0<D.tauNum) (hTd : 0<D.tauDen) (hEn : 0<D.epsilonNum) (hEd : 0<D.epsilonDen)
    (hA : (D.alphaNum:ℚ)/D.alphaDen=alpha D.length d) :
    (numerator D t:ℚ)/denominator D =
      stoppingRatio e D.wells D.sourceSize (boxCount D.span D.length t) D.length d
        ((D.conditionNum:ℚ)/D.conditionDen) ((D.epsilonNum:ℚ)/D.epsilonDen)
        ((D.tauNum:ℚ)/D.tauDen) := by
  have hkd : (D.conditionDen:ℚ)≠0 := by exact_mod_cast hKd.ne'
  have han : (D.alphaNum:ℚ)≠0 := by exact_mod_cast hAn.ne'
  have had : (D.alphaDen:ℚ)≠0 := by exact_mod_cast hAd.ne'
  have htn : (D.tauNum:ℚ)≠0 := by exact_mod_cast hTn.ne'
  have htd : (D.tauDen:ℚ)≠0 := by exact_mod_cast hTd.ne'
  have hen : (D.epsilonNum:ℚ)≠0 := by exact_mod_cast hEn.ne'
  have hed : (D.epsilonDen:ℚ)≠0 := by exact_mod_cast hEd.ne'
  rw [stoppingRatio_formula,← hA]
  have hk : 1+(D.conditionNum:ℚ)/D.conditionDen=
      (D.conditionDen+D.conditionNum:ℚ)/D.conditionDen := by field_simp
  have ha : 1+((D.alphaNum:ℚ)/D.alphaDen)⁻¹=
      (D.alphaNum+D.alphaDen:ℚ)/D.alphaNum := by
    simp only [inv_div]
    field_simp
  rw [hk,ha]
  simp only [numerator,denominator,hC,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat,div_pow]
  field_simp

theorem comparison_iff (D : Data) (e d t u : ℕ) (hC : D.constant=2^e)
    (hm : 0<D.sourceSize) (hKd : 0<D.conditionDen) (hAn : 0<D.alphaNum) (hAd : 0<D.alphaDen)
    (hTn : 0<D.tauNum) (hTd : 0<D.tauDen) (hEn : 0<D.epsilonNum) (hEd : 0<D.epsilonDen)
    (hA : (D.alphaNum:ℚ)/D.alphaDen=alpha D.length d) :
    (numerator D t:ℚ)/denominator D ≤ (2:ℚ)^(u/slowDivisor) ↔
      globalBudget e D.wells D.sourceSize (boxCount D.span D.length t) D.length d
        ((D.conditionNum:ℚ)/D.conditionDen)*rationalDecay u ≤
      errorBudget D.sourceSize (boxCount D.span D.length t)
        ((D.epsilonNum:ℚ)/D.epsilonDen) ((D.tauNum:ℚ)/D.tauDen)/4 := by
  rw [ratio D e d t hC hKd hAn hAd hTn hTd hEn hEd hA]
  have heps : 0<(D.epsilonNum:ℚ)/D.epsilonDen := by positivity
  have htau : 0<(D.tauNum:ℚ)/D.tauDen := by positivity
  have he := errorBudget_pos hm (boxCount_pos D.span D.length t) heps htau
  have hp : (0:ℚ)<2^(u/slowDivisor) := by positivity
  simp only [stoppingRatio,rationalDecay,one_div,inv_pow]
  rw [div_le_iff₀ he]
  rw [← div_eq_mul_inv,div_le_iff₀ hp]
  constructor <;> intro h <;> nlinarith

theorem predicate (D : Data) (e d k : ℕ) (hC : D.constant=2^e)
    (hm : 0<D.sourceSize) (hKd : 0<D.conditionDen) (hAn : 0<D.alphaNum) (hAd : 0<D.alphaDen)
    (hTn : 0<D.tauNum) (hTd : 0<D.tauDen) (hEn : 0<D.epsilonNum) (hEd : 0<D.epsilonDen)
    (hA : (D.alphaNum:ℚ)/D.alphaDen=alpha D.length d) :
    tests.any (Maxwell.Cost.SelectedParameters.AllComparisons.failed (values D k))=false ↔
      BufferTest e D.wells D.sourceSize D.length d D.span
        ((D.conditionNum:ℚ)/D.conditionDen) ((D.epsilonNum:ℚ)/D.epsilonDen)
        ((D.tauNum:ℚ)/D.tauDen) (2^k) := by
  rw [tests_iff]
  exact comparison_iff D e d (2^k) (2^k) hC hm hKd hAn hAd hTn hTd hEn hEd hA

#print axioms predicate
end Maxwell.Continuum.Parameters.BufferMachine
