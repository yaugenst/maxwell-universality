import Maxwell.Continuum.PECBoxSpectrum
import Maxwell.Continuum.SelfAdjointResolventDetuning

/-! Uniform scalar detuning for the literal continuum PEC box. In particular,
no finite spectral cover or spectral-count hypothesis is supplied by a caller. -/

noncomputable section

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

open SelfAdjointResolvent

theorem box_spectralCountBudget_pos (N : ModeCount.BoxLengths) :
    0 < ModeCount.spectralCountBudget N := by
  unfold ModeCount.spectralCountBudget
  positivity

namespace ScalarDielectric

variable (ε : ScalarDielectric) (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j)

include hN in
/-- The genuine full-spectrum bad event has the paper's probability bound.
The physical mode construction supplies the count internally. -/
theorem box_detuning_probability (m : ℕ) (τ : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (hτupper : τ ≤ 1 / 64) :
    DetuningGrid.gridProbability (Detuning.gridSize m (ModeCount.spectralCountBudget N))
      (Detuning.grid_pos m _ _ hm (box_spectralCountBudget_pos N)
        (Detuning.gridSize_sufficient m _))
      (maxwellBadDraws (BoxModes.boxDomain (fun j => (N j : ℝ))) ε m
        (ModeCount.spectralCountBudget N) τ) ≤ 3 / (64 * (m : ℝ)) := by
  apply maxwell_detuning_probability _ ε (ε.boxWindowSpectrum N hN) m _ τ
    hm (box_spectralCountBudget_pos N) hτ hτupper (ε.boxWindowSpectrum_card_le N hN)
  intro eig heig hw
  exact ε.windowSpectrum_covers _ (BoxModes.boxTransverseCutoff N hN) eig heig hw

/-- Each successful draw gives the actual two-sided Maxwell inverse, with
the L² inverse, graph inverse, and condition-number budgets. -/
theorem box_sampled_resolvent (m j : ℕ) (τ : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (hτupper : τ ≤ 1 / 64)
    (hmargin : ∀ x, ε.coefficient x ≤ 24)
    (hj : j < Detuning.gridSize m (ModeCount.spectralCountBudget N))
    (hgood : j ∉ maxwellBadDraws (BoxModes.boxDomain (fun k => (N k : ℝ))) ε m
      (ModeCount.spectralCountBudget N) τ) :
    ∃ εσ : ScalarDielectric,
      (∀ x, εσ.coefficient x = ε.coefficient x +
        DetuningGrid.midpoint τ (Detuning.gridSize m (ModeCount.spectralCountBudget N)) j) ∧
      ∃ R : BoundedInverse
          (maxwellOperator (BoxModes.boxDomain (fun k => (N k : ℝ))) εσ),
        ‖R.map‖ ≤ Detuning.inverseBudget m (ModeCount.spectralCountBudget N) τ ∧
        ‖maxwellGraphInverse (BoxModes.boxDomain (fun k => (N k : ℝ))) εσ R‖ ≤
          27 * Detuning.inverseBudget m (ModeCount.spectralCountBudget N) τ ∧
        ‖maxwellGraphMap (BoxModes.boxDomain (fun k => (N k : ℝ))) εσ‖ *
          ‖maxwellGraphInverse (BoxModes.boxDomain (fun k => (N k : ℝ))) εσ R‖ ≤
            702 * Detuning.inverseBudget m (ModeCount.spectralCountBudget N) τ :=
  sampled_maxwell_resolvent _ ε m _ j τ hm (box_spectralCountBudget_pos N)
    hτ hτupper hmargin hj hgood

/-- The finite random seed budget for this physical box. -/
theorem box_detuning_randomBits (m : ℕ) :
    Detuning.randomBits m (ModeCount.spectralCountBudget N) ≤
      6 + Nat.clog 2 m + Nat.clog 2 (ModeCount.spectralCountBudget N) :=
  Detuning.randomBits_le _ _

/-- Every emitted shift has a literal dyadic encoding, with no real-number
oracle used to choose or represent the sample. -/
theorem box_detuning_dyadic (a : ℤ) (p m j : ℕ) :
    DetuningGrid.midpoint ((a : ℝ) / 2 ^ p)
      (Detuning.gridSize m (ModeCount.spectralCountBudget N)) j =
        (((2 * (j : ℤ) + 1) * a : ℤ) : ℝ) /
          2 ^ (p + Detuning.randomBits m (ModeCount.spectralCountBudget N) + 1) :=
  Detuning.sample_dyadic a p m _ j

end ScalarDielectric

end Maxwell.Continuum
