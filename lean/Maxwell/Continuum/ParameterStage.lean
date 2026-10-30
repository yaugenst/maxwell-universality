import Maxwell.Continuum.ParameterBoxBounds
import Maxwell.Continuum.ParameterBufferSearch

/-! One literal outer-loop stage: spacing, dyadic detuning, even box sides,
and the buffer search. Its stopping exponents are derived from the formulas. -/

namespace Maxwell.Continuum.Parameters
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

structure Input where
  m : ℕ
  J : ℕ
  span : Fin 3 → ℕ
  K : ℚ
  epsilon : ℚ
  m_pos : 0 < m
  K_pos : 0 < K
  epsilon_pos : 0 < epsilon

structure Input.BinaryBudget (I : Input) (p ℓ : ℕ) : Prop where
  m : (I.m : ℚ) ≤ (2 : ℚ)^(p*ℓ)
  J : (I.J : ℚ) ≤ (2 : ℚ)^(p*ℓ)
  span : ∀ j, (I.span j : ℚ) ≤ (2 : ℚ)^(p*ℓ)
  K : I.K ≤ (2 : ℚ)^(p*ℓ)
  epsilon : I.epsilon⁻¹ ≤ (2 : ℚ)^(p*ℓ)

 def stageLength (k : ℕ) : ℕ := 8^k
 def stageSpacing (I : Input) (e k : ℕ) : ℕ :=
  selectedSpacing e (stageLength k) I.K I.epsilon I.K_pos I.epsilon_pos

attribute [local irreducible] stageSpacing

 theorem stageLength_pos (k : ℕ) : 0 < stageLength k := by unfold stageLength; positivity
 theorem stageLength_binary (k : ℕ) : (stageLength k : ℚ) = (2 : ℚ)^(3*k) := by
  simp only [stageLength, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (8 : ℚ) = 2^3 by norm_num, ← pow_mul]

 def stageTau (I : Input) (e k : ℕ) : ℚ :=
  tau (stageLength k) (stageSpacing I e k) (stageLength_pos k)

 theorem stageTau_pos (I : Input) (e k : ℕ) : 0 < stageTau I e k := tau_pos _ _ _

/-- Four extra units on each side provide the eight-unit fixed margin used
by the literal PEC localization cutoff. -/
 def stageSpan (I : Input) (e k : ℕ) (j : Fin 3) : ℕ :=
  scaledSpan I.span (stageLength k) (stageSpacing I e k) j+4

 theorem stageSpan_margin (I : Input) (e k t : ℕ) (j : Fin 3) :
    boxSide (stageSpan I e k) (stageLength k) t j =
      2*(scaledSpan I.span (stageLength k) (stageSpacing I e k) j+
        stageLength k+stageLength k*t+8) := by unfold boxSide stageSpan; ring

 def stageBuffer (I : Input) (e k : ℕ) : ℕ :=
  selectedBuffer e I.J I.m (stageLength k) (stageSpacing I e k) (stageSpan I e k)
    I.K I.epsilon (stageTau I e k) I.m_pos I.epsilon_pos (stageTau_pos I e k)

 theorem stageBuffer_spec (I : Input) (e k : ℕ) :
    BufferTest e I.J I.m (stageLength k) (stageSpacing I e k) (stageSpan I e k)
      I.K I.epsilon (stageTau I e k) (stageBuffer I e k) := selectedBuffer_spec _ _ _ _ _ _ _ _ _ _ _ _

attribute [local irreducible] stageBuffer

 theorem epsilon_lower_of_binary {I : Input} {p ℓ : ℕ} (hI : I.BinaryBudget p ℓ) :
    (1/2 : ℚ)^(p*ℓ) ≤ I.epsilon := by
  have h := (inv_le_inv₀ (by positivity : (0 : ℚ) < 2^(p*ℓ))
    (inv_pos.mpr I.epsilon_pos)).mpr hI.epsilon
  simpa only [inv_inv, ← inv_pow, one_div] using h

 def stageCountExponent (p ℓ k d t : ℕ) : ℕ := 37+27*k+3*d+3*p*ℓ+3*t
 def stageBudgetExponent (e p ℓ k d t : ℕ) : ℕ := 2235+32*e+393*k+19*d+19*p*ℓ+9*t

 theorem stageCountExponent_eq (p ℓ k d t : ℕ) :
    stageCountExponent p ℓ k d t = 1+3*((4+3*k+d+p*ℓ)+2*(3*k)+t+8) := by
  unfold stageCountExponent
  ring

 theorem stageBudgetExponent_eq (e p ℓ k d t : ℕ) :
    stageBudgetExponent e p ℓ k d t =
      stoppingExponent e (p*ℓ) (p*ℓ) (stageCountExponent p ℓ k d t) (p*ℓ)
        (1026+3*d) (3*k) (25+4*(3*k)+4*d) (p*ℓ) := by
  unfold stageBudgetExponent stoppingExponent globalExponent stageCountExponent
  ring

 theorem stageSpan_binary {I : Input} {p ℓ : ℕ} (hI : I.BinaryBudget p ℓ) (e k : ℕ) (j : Fin 3) :
    (stageSpan I e k j : ℚ) ≤ (2 : ℚ)^(4+3*k+stageSpacing I e k+p*ℓ) := by
  have hs := scaledSpan_binary hI.span (stageLength_binary k).le (nat_binary_self (stageSpacing I e k)) j
  have hh := binary_add hs (show (4 : ℚ) ≤ (2 : ℚ)^2 by norm_num)
  convert hh using 1
  · simp only [stageSpan, Nat.cast_add, Nat.cast_ofNat]
  · congr 1; omega

 theorem stageCount_binary {I : Input} {p ℓ : ℕ} (hI : I.BinaryBudget p ℓ) (e k t : ℕ) :
    (boxCount (stageSpan I e k) (stageLength k) t : ℚ) ≤
      (2 : ℚ)^stageCountExponent p ℓ k (stageSpacing I e k) t := by
  rw [stageCountExponent_eq]
  exact boxCount_binary (stageSpan_binary hI e k) (stageLength_binary k).le (nat_binary_self t)

 theorem stageBudget_binary {I : Input} {p ℓ : ℕ} (hI : I.BinaryBudget p ℓ) (e k t : ℕ) :
    stoppingRatio e I.J I.m (boxCount (stageSpan I e k) (stageLength k) t)
      (stageLength k) (stageSpacing I e k) I.K I.epsilon (stageTau I e k) ≤
        (2 : ℚ)^stageBudgetExponent e p ℓ k (stageSpacing I e k) t := by
  have hτ := tau_inverse_binary (stageLength_pos k)
    (show stageLength k ≤ 2^(3*k) by exact_mod_cast (stageLength_binary k).le) (stageSpacing I e k)
  have h := stoppingRatio_binary hI.J hI.m (stageCount_binary hI e k t) (stageLength_binary k).le
    I.K_pos.le hI.K (alpha_inverse_binary (stageLength_pos k) (stageSpacing I e k))
    I.epsilon_pos hI.epsilon (stageTau_pos I e k) hτ (e := e)
  rw [stageBudgetExponent_eq]
  exact h

 theorem stageBuffer_upper {I : Input} {p ℓ : ℕ} (hI : I.BinaryBudget p ℓ) (e k : ℕ) :
    stageBuffer I e k < 2^2049*(stageBudgetExponent e p ℓ k (stageSpacing I e k) 0+1) := by
  unfold stageBuffer
  exact selectedBuffer_upper I.m_pos I.epsilon_pos (stageTau_pos I e k) (stageBudget_binary hI e k 0)

#print axioms stageBudget_binary
#print axioms stageBuffer_upper

end Maxwell.Continuum.Parameters
