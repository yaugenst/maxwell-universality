import Maxwell.Continuum.ParameterBox
import Maxwell.Continuum.ParameterExponentialSearch
import Maxwell.Continuum.ParameterSpacingSearch

/-! The actual buffer doubling search recomputes the literal box count,
detuning inverse budget, and global error budget at every candidate. -/

namespace Maxwell.Continuum.Parameters

def BufferTest (e J m L d : ℕ) (s : Fin 3 → ℕ) (K ε τ : ℚ) (t : ℕ) : Prop :=
  globalBudget e J m (boxCount s L t) L d K*rationalDecay t ≤
    errorBudget m (boxCount s L t) ε τ/4

instance bufferTestDecidable (e J m L d : ℕ) (s : Fin 3 → ℕ) (K ε τ : ℚ) (t : ℕ) :
    Decidable (BufferTest e J m L d s K ε τ t) := inferInstanceAs (Decidable (_ ≤ _))

theorem bufferCandidate_spec {e J m L d a : ℕ} {s : Fin 3 → ℕ} {K ε τ : ℚ}
    (hm : 0 < m) (hε : 0 < ε) (hτ : 0 < τ)
    (ha : stoppingRatio e J m (boxCount s L 0) L d K ε τ ≤ (2 : ℚ)^a) :
    BufferTest e J m L d s K ε τ (bufferCandidate a) := by
  apply stoppingRatio_test hm (boxCount_pos _ _ _) hε hτ
  have hg := mul_le_mul_of_nonneg_right
    (stoppingRatio_growth e J m L d s K ε τ hε hτ (bufferCandidate a))
    (rationalDecay_pos (bufferCandidate a)).le
  exact hg.trans (bufferCandidate_passes ha)

theorem bufferSearch_exists (e J m L d : ℕ) (s : Fin 3 → ℕ) (K ε τ : ℚ)
    (hm : 0 < m) (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ k : ℕ, BufferTest e J m L d s K ε τ (2^k) :=
  ⟨bufferCandidateExponent (rationalUpperBits (stoppingRatio e J m (boxCount s L 0) L d K ε τ)),
    bufferCandidate_spec hm hε hτ (rationalUpperBits_spec _)⟩

def selectedBuffer (e J m L d : ℕ) (s : Fin 3 → ℕ) (K ε τ : ℚ)
    (hm : 0 < m) (hε : 0 < ε) (hτ : 0 < τ) : ℕ :=
  firstPower 2 (BufferTest e J m L d s K ε τ)
    (bufferSearch_exists e J m L d s K ε τ hm hε hτ)

theorem selectedBuffer_spec (e J m L d : ℕ) (s : Fin 3 → ℕ) (K ε τ : ℚ)
    (hm : 0 < m) (hε : 0 < ε) (hτ : 0 < τ) :
    BufferTest e J m L d s K ε τ (selectedBuffer e J m L d s K ε τ hm hε hτ) :=
  firstPower_spec _ _ _

theorem selectedBuffer_pos (e J m L d : ℕ) (s : Fin 3 → ℕ) (K ε τ : ℚ)
    (hm : 0 < m) (hε : 0 < ε) (hτ : 0 < τ) :
    0 < selectedBuffer e J m L d s K ε τ hm hε hτ := by
  unfold selectedBuffer firstPower
  positivity

theorem selectedBuffer_upper {e J m L d a : ℕ} {s : Fin 3 → ℕ} {K ε τ : ℚ}
    (hm : 0 < m) (hε : 0 < ε) (hτ : 0 < τ)
    (ha : stoppingRatio e J m (boxCount s L 0) L d K ε τ ≤ (2 : ℚ)^a) :
    selectedBuffer e J m L d s K ε τ hm hε hτ < 2^2049*(a+1) := by
  have hp := firstPower_le_candidate (by decide : 1 ≤ 2) (BufferTest e J m L d s K ε τ)
    (bufferSearch_exists e J m L d s K ε τ hm hε hτ) (bufferCandidate_spec hm hε hτ ha)
  exact hp.trans_lt (bufferCandidate_upper a)

theorem selectedBuffer_bits {e J m L d a : ℕ} {s : Fin 3 → ℕ} {K ε τ : ℚ}
    (hm : 0 < m) (hε : 0 < ε) (hτ : 0 < τ)
    (ha : stoppingRatio e J m (boxCount s L 0) L d K ε τ ≤ (2 : ℚ)^a) :
    (selectedBuffer e J m L d s K ε τ hm hε hτ).bits.length ≤ 2049+Nat.clog 2 (a+1) := by
  have hp := firstPower_exponent_le 2 (BufferTest e J m L d s K ε τ)
    (bufferSearch_exists e J m L d s K ε τ hm hε hτ) (bufferCandidate_spec hm hε hτ ha)
  rw [selectedBuffer, firstPower_binary_bits]
  unfold bufferCandidateExponent at hp
  omega

#print axioms bufferSearch_exists
#print axioms selectedBuffer_spec
#print axioms selectedBuffer_upper

end Maxwell.Continuum.Parameters
