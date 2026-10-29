import Maxwell.Cost.BitMachine

namespace Maxwell.Cost

/-- A list of actual capped executions. Each attempt includes whatever
construction, solver, decoder and verifier code the caller has installed
in its finite machine. Costs are summed from executed transitions. -/
def runAttempts {σ : Type} (next : σ → Option σ) (cap : ℕ) :
    List σ → List (CappedResult σ)
  | [] => []
  | state :: states => runCapped next cap state :: runAttempts next cap states

def attemptCost {σ : Type} (results : List (CappedResult σ)) : ℕ :=
  (results.map CappedResult.instructions).sum

theorem runAttempts_all_draws_bound {σ : Type} (next : σ → Option σ)
    (cap : ℕ) (states : List σ) :
    attemptCost (runAttempts next cap states) ≤ states.length * cap := by
  induction states with
  | nil => simp [runAttempts, attemptCost]
  | cons state states ih =>
    simp only [runAttempts, attemptCost, List.map_cons, List.sum_cons, List.length_cons]
    have h := runCapped_le next cap state
    change (runCapped next cap state).instructions +
      attemptCost (runAttempts next cap states) ≤ (states.length + 1) * cap
    nlinarith

/-- Acceptance is permitted only for a genuinely halted machine output.
Correctness belongs to the verifier's proved output invariant, and does not
require any condition-number or good-draw assumption on accepted runs. -/
theorem accepted_capped_output_sound {σ : Type} (next : σ → Option σ)
    (cap : ℕ) (initial output : σ) (valid : σ → Prop)
    (verifierSound : ∀ n final, Terminates next n initial final → valid final)
    (accepted : (runCapped next cap initial).finished = some output) :
    valid output :=
  verifierSound _ _ (runCapped_sound next cap accepted)

/-- Keeping construction, solve, decoding and verification costs in the
cap retains the construction floor on every draw, including timeouts. -/
theorem repeated_total_budget (construction solver decoding verification repetitions : ℕ)
    {σ : Type} (next : σ → Option σ) (states : List σ)
    (h : states.length = repetitions) :
    attemptCost (runAttempts next (construction + solver + decoding + verification) states) ≤
      repetitions * (construction + solver + decoding + verification) := by
  simpa [h] using runAttempts_all_draws_bound next
    (construction + solver + decoding + verification) states

/-- Fixed preprocessing is paid once and repeated input-dependent work is
paid at every attempt. None of the two summands is silently discarded. -/
theorem preprocessing_repeated_total_budget (fixed construction solver decoding verification : ℕ)
    {σ : Type} (next : σ → Option σ) (states : List σ) :
    fixed + attemptCost (runAttempts next
      (construction + solver + decoding + verification) states) ≤
      fixed + states.length * (construction + solver + decoding + verification) :=
  Nat.add_le_add_left (runAttempts_all_draws_bound next _ states) fixed

end Maxwell.Cost
