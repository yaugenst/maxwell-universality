import Maxwell.Cost.RealMidpoint

namespace Maxwell.Cost.RealMidpointRegister
open RealSparse (execute_sound)
open RealMidpoint

theorem finished_registers (s : RAMState) (x : ℝ) (p : ℕ)
    (h : RealRound.Ready s x p p) :
    (finished s x p).words 4 = (approximation x p : ℝ) ∧
    (finished s x p).indices 4 = (approximation x p).num.natAbs ∧
    (finished s x p).indices 5 = (approximation x p).den ∧ (finished s x p).words 7 = 0 := by
  rw [approximation_num, approximation_den, numerator_natAbs]
  rcases h with ⟨_, _, _, _, hn, hd, _, _, _, _, hnR, hdR, _, hwzero, _, _, _⟩
  by_cases hz : x = 0
  · rcases hz with rfl
    simp [finished, RAMState.setWord, RAMState.setIndex, hwzero]
  · by_cases hpos : 0 ≤ x
    all_goals simp [finished, arithmetic, hz, hpos, magnitude, denominator, hn, hd, hnR, hdR, approximation,
      numerator, RAMState.setWord, RAMState.setIndex, pow_succ, hwzero]
    all_goals repeat' constructor
    all_goals ring

theorem source_terminates (x : ℝ) (p : ℕ) (tape : ℕ → Bool) :
    ∃ cost : ℕ, ∃ t : RAMState,
      cost ≤ 13 * p + 32 ∧
      Terminates (RealMidpoint.program.next (RealRound.input x p) tape) cost RAMState.initial t ∧
      t.pc = 55 ∧ t.words 4 = (approximation x p : ℝ) ∧
      t.indices 4 = (approximation x p).num.natAbs ∧ t.indices 5 = (approximation x p).den ∧
      t.words 7 = 0 := by
  have hi := execute_sound _ (initialize_steps x p tape)
  obtain ⟨s, hs, hsr⟩ := scan x p tape p (RealRound.initialized x p) 0
    (RealRound.initialized_ready x p) (by omega)
  have hf := execute_sound _ (finish_steps x p tape s hsr)
  refine ⟨16 + 13 * p + finishCost x, finished s x p, by have := finishCost_le x; omega,
    ?_, rfl, finished_registers s x p hsr⟩
  exact ((hi.trans hs).trans hf).terminates
    (Terminates.halt _ (by simp [RealMidpoint.program, RealRound.program, Machine.next, finished]))

end Maxwell.Cost.RealMidpointRegister
