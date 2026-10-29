import Maxwell.Cost.Arithmetic.Kernel

namespace Maxwell.Cost

theorem tails_length_lt (xs ys : List Bool) (h : ¬(xs = [] ∧ ys = [])) :
    xs.tail.length + ys.tail.length < xs.length + ys.length := by
  cases xs <;> cases ys <;> simp_all
  all_goals omega

/-- All-width simulation of the *one fixed finite program*. The proof
recurses only to reason about executions; the program is independent of
operand lengths. Tape writes are exact, and every branch/bit read is paid. -/
theorem rippleAdder_simulation (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (hpc : s.pc = 0)
    (hx : TapeRepresents (s.tapes 0) xs) (hy : TapeRepresents (s.tapes 1) ys) :
    ∃ cost final, cost ≤ 18 * max xs.length ys.length + 28 ∧
      PricedSteps (rippleAdder.next input tape) cost s final ∧
      rippleAdder.next input tape final = none ∧
      TapeWrites (s.tapes 2) (final.tapes 2) (addBits (s.registers 2) xs ys) := by
  by_cases hempty : xs = [] ∧ ys = []
  · rcases hempty with ⟨rfl, rfl⟩
    simpa using ripple_empty_run input tape s hpc hx hy
  · have hn := rippleRound_cost_nonempty hx hy hempty
    have hr := executeInstructions_sound _ (rippleRound_execute input tape s hpc (Or.inl hn.1))
    rw [hn.2] at hr
    have hxy := rippleRound_inputs hx hy
    obtain ⟨cost, final, hcost, hsteps, hhalt, hwrites⟩ :=
      rippleAdder_simulation input tape (rippleRound s) xs.tail ys.tail rfl hxy.1 hxy.2
    have hlength : max xs.length ys.length = max xs.tail.length ys.tail.length + 1 := by
      cases xs <;> cases ys <;> simp_all
    refine ⟨18 + cost, final, ?_, hr.trans hsteps, hhalt, ?_⟩
    · calc
        18 + cost ≤ 18 + (18 * max xs.tail.length ys.tail.length + 28) :=
          Nat.add_le_add_left hcost 18
        _ = 18 * max xs.length ys.length + 28 := by rw [hlength]; omega
    · have hw := (rippleRound_writes s).trans hwrites
      rw [addBits_nonempty _ _ _ hempty]
      simpa [rippleRound_carry, rippleSumBit, rippleCarryBit, hx.read, hy.read] using hw
termination_by xs.length + ys.length
decreasing_by
  exact tails_length_lt _ _ hempty

/-- The concrete capped interpreter succeeds uniformly on all operand lengths.
The cap is a proved bit-operation bound, not supplied runtime metadata. -/
theorem rippleAdder_run (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (hpc : s.pc = 0)
    (hx : TapeRepresents (s.tapes 0) xs) (hy : TapeRepresents (s.tapes 1) ys) :
    ∃ final, (runPriced (rippleAdder.next input tape)
        (18 * max xs.length ys.length + 29) s).finished = some final ∧
      (runPriced (rippleAdder.next input tape)
        (18 * max xs.length ys.length + 29) s).instructions ≤
          18 * max xs.length ys.length + 28 ∧
      TapeWrites (s.tapes 2) (final.tapes 2) (addBits (s.registers 2) xs ys) := by
  obtain ⟨cost, final, hcost, hsteps, hhalt, hwrites⟩ :=
    rippleAdder_simulation input tape s xs ys hpc hx hy
  have hr := hsteps.runPriced_ge hhalt (18 * max xs.length ys.length + 29) (by omega)
  exact ⟨final, hr.1, by simpa [hr.2] using hcost, hwrites⟩

/-- The emitted magnitude represents exact integer addition (with the
initial carry), and its size is at most one bit beyond the larger operand. -/
theorem rippleAdder_output_value (carry : Bool) (xs ys : List Bool) :
    addressValue (addBits carry xs ys) = addressValue xs + addressValue ys + carry.toNat ∧
      (addBits carry xs ys).length ≤ max xs.length ys.length + 1 :=
  ⟨addBits_value _ _ _, addBits_length_le _ _ _⟩

end Maxwell.Cost
