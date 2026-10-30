import Maxwell.Continuum.ParameterCandidateBudget
import Maxwell.Continuum.ParameterStoppingTests
import Maxwell.Continuum.ParameterInputBudget

/-! Terminating outer search with literal rational stopping tests. The
encoder starts at the least permitted power of eight and multiplies by
eight after a failed leakage or tail comparison. -/

namespace Maxwell.Continuum.Parameters

 def initialExponent (base ℓ : ℕ) : ℕ := max base (Nat.clog 8 (ℓ^6))
 def OuterTest (I : Input) (e k : ℕ) : Prop := LeakageTest I e k ∧ TailTest I e k

 instance outerTestDecidable (I : Input) (e k : ℕ) : Decidable (OuterTest I e k) :=
  inferInstanceAs (Decidable (_ ∧ _))

 theorem candidate_passes {I : Input} {M e p ℓ : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hℓ : 0 < ℓ) :
    OuterTest I e (outerCandidateExponent M ℓ) := by
  have hd := stageSpacing_candidate hI hM he hp hℓ
  have ht := stageBuffer_candidate hI hM he hp hℓ
  have hb := candidate_final_budget hM he hp hℓ hd ht
  have hf := hb.trans (candidate_floor_covers hM)
  exact ⟨leakage_of_budget hI hf, tail_of_budget hI hf⟩

 theorem initialExponent_le_candidate {M base ℓ : ℕ} (hb : base ≤ M) :
    initialExponent base ℓ ≤ outerCandidateExponent M ℓ := by
  apply max_le
  · unfold outerCandidateExponent
    omega
  · exact Nat.clog_le_of_le_pow (outerCandidate_lower M ℓ)

 theorem outerSearch_exists (I : Input) (e base ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ n : ℕ, OuterTest I e (initialExponent base ℓ+n) := by
  let M := 4096+e+base+I.binarySize
  have hM : 4096 ≤ M := by unfold M; omega
  have he : e ≤ M := by unfold M; omega
  have hp : I.binarySize ≤ M := by unfold M; omega
  have hb : base ≤ M := by unfold M; omega
  have hi := initialExponent_le_candidate (ℓ := ℓ) hb
  refine ⟨outerCandidateExponent M ℓ-initialExponent base ℓ, ?_⟩
  rw [Nat.add_sub_of_le hi]
  exact candidate_passes (I.binarySize_budget hℓ) hM he hp hℓ

 def selectedOuterSteps (I : Input) (e base ℓ : ℕ) (hℓ : 0 < ℓ) : ℕ :=
  Nat.find (outerSearch_exists I e base ℓ hℓ)

 def selectedOuterExponent (I : Input) (e base ℓ : ℕ) (hℓ : 0 < ℓ) : ℕ :=
  initialExponent base ℓ+selectedOuterSteps I e base ℓ hℓ

 theorem selectedOuter_spec (I : Input) (e base ℓ : ℕ) (hℓ : 0 < ℓ) :
    OuterTest I e (selectedOuterExponent I e base ℓ hℓ) :=
  Nat.find_spec (outerSearch_exists I e base ℓ hℓ)

 theorem selectedOuter_ge_base (I : Input) (e base ℓ : ℕ) (hℓ : 0 < ℓ) :
    base ≤ selectedOuterExponent I e base ℓ hℓ :=
  (le_max_left _ _).trans (Nat.le_add_right _ _)

 theorem selectedOuter_length_lower (I : Input) (e base ℓ : ℕ) (hℓ : 0 < ℓ) :
    ℓ^6 ≤ stageLength (selectedOuterExponent I e base ℓ hℓ) :=
  (Nat.le_pow_clog (by decide) (ℓ^6)).trans
    (Nat.pow_le_pow_right (by decide) ((le_max_right _ _).trans (Nat.le_add_right _ _)))

 theorem selectedOuter_le_candidate {I : Input} {M e p base ℓ : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hb : base ≤ M) (hℓ : 0 < ℓ) :
    selectedOuterExponent I e base ℓ hℓ ≤ outerCandidateExponent M ℓ := by
  have hi := initialExponent_le_candidate (ℓ := ℓ) hb
  have hs : OuterTest I e
      (initialExponent base ℓ+(outerCandidateExponent M ℓ-initialExponent base ℓ)) := by
    rw [Nat.add_sub_of_le hi]
    exact candidate_passes hI hM he hp hℓ
  have hfind := Nat.find_min' (outerSearch_exists I e base ℓ hℓ) hs
  change selectedOuterSteps I e base ℓ hℓ ≤ _ at hfind
  unfold selectedOuterExponent
  omega

#print axioms outerSearch_exists
#print axioms selectedOuter_spec
#print axioms selectedOuter_le_candidate

end Maxwell.Continuum.Parameters
