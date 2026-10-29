import Maxwell.Cost.RealSimulation.StoreWriteFrame
import Maxwell.Cost.RealSimulation.ScratchClear
import Maxwell.Cost.RealSimulation.Simulation
import Maxwell.Cost.RealSimulation.PCBounds
import Maxwell.Cost.RealSimulation.VisitedSteps

namespace Maxwell.Cost.RealSimulation
open Control

def widthBody (M : BitRAM) : Code :=
  .seq (dispatch (footprint M.code) Address.code 0 M.code) clearScratch
def widthInterpreter (M : BitRAM) : Code := .loop oneRegister activeRegister (widthBody M)
def widthConstant (M : BitRAM) : ℕ := dispatchConstant M + 30

theorem dispatch_next_framed (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center : ℕ} {bits : List Bool} {source next : BitRAMState} {extra : ℕ}
    (hnext : M.next bits tape source = some ⟨next, extra⟩)
    (s : Store) (h : Ready (footprint M.code) origin center bits source s)
    (hinput : -(center : ℤ) < source.inputHead)
    (htapes : ∀ t, -(center : ℤ) < (source.tapes t).head) :
    ∃ cost t, cost ≤ dispatchConstant M * (extra + 1) ∧
      Executes input tape (dispatch (footprint M.code) Address.code 0 M.code) cost s t ∧
      Ready (footprint M.code) origin center bits next t ∧
      WriteFrame (footprint M.code) s.val t.val := by
  cases hc : M.code[source.pc]? with
  | none => simp [BitRAM.next, hc] at hnext
  | some op =>
    obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hc
    have hf := footprint_get_fits M.code source.pc op hc
    let R := fun u : Store => Ready (footprint M.code) origin center bits source u ∧
      WriteFrame (footprint M.code) s.val u.val
    let Q := fun u : Store => Ready (footprint M.code) origin center bits next u ∧
      WriteFrame (footprint M.code) s.val u.val
    obtain ⟨cost, t, hb, ht, hr⟩ := dispatch_selected (footprint M.code) Address.code input tape
      M.code 0 source.pc hj R Q (by
        intro u v hu
        exact ⟨hu.1.put_scratch _ _ (by decide) (by decide) (by decide) (by decide),
          hu.2.put_scalar _ _ (scalar_small _ _ (by decide))⟩)
      (instructionConstant (footprint M.code) * (extra + 1)) s ⟨h, WriteFrame.refl _ _⟩
      (by simpa using h.pc) (by
        intro u hu
        rw [he]
        obtain ⟨c, v, hb, ex, hv⟩ := instruction_next M input tape op hc hf hnext u hu.1
          hinput (fun t _ => htapes t)
        exact ⟨c, v, hb, ex, hv, hu.2.trans
          (instruction_frame input tape op hf u v hu.1 (fun t _ => le_of_lt (htapes t)) ex)⟩)
    refine ⟨cost, t, ?_, ht, hr⟩
    unfold dispatchConstant
    nlinarith

theorem source_extra_le {M : BitRAM} {bits : List Bool} {tape : ℕ → Bool}
    {s t : BitRAMState} {extra : ℕ} (h : M.next bits tape s = some ⟨t, extra⟩) :
    extra ≤ max 1 s.address.length := by
  cases hc : M.code[s.pc]? with
  | none => simp [BitRAM.next, hc] at h
  | some op =>
    cases op <;> simp only [BitRAM.next, hc, Option.some.injEq, PricedStep.mk.injEq] at h
    all_goals try contradiction
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals omega

theorem clearCells_random (s : Store) (js : List ℕ) :
    (clearedCells s js).val.randomCursor = s.val.randomCursor := by
  induction js generalizing s with
  | nil => rfl
  | cons j js ih => exact ih (s.put j 0)

theorem clearScratch_represents {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} (s : Store) (h : Represents L origin center bits source s.val) :
    Represents L origin center bits source (clearedScratch s).val := by
  apply h.congr
  · intro j hj
    rw [clearedScratch, clearedCells_indices, ite_eq_right]
    simp only [scratchCells, List.mem_cons, List.not_mem_nil, or_false]
    omega
  · exact clearCells_random s scratchCells

theorem width_terminal (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (halt : M.next bits tape source = none)
    (s : Store) (h : Ready (footprint M.code) origin center bits source s) :
    ∃ cost t, cost ≤ terminalConstant M + 27 ∧
      Executes input tape (widthInterpreter M) cost s t ∧
      Represents (footprint M.code) origin center bits source t.val := by
  have hh := source_halt_code M bits tape source halt
  rw [← h.pc] at hh
  obtain ⟨cost, t, hc, he, ha, hf⟩ := dispatch_finish (footprint M.code) Address.code input tape
    M.code s hh
  have hr : Represents (footprint M.code) origin center bits source t.val :=
    h.toRepresents.congr (fun j hj => hf.indices j
      (by unfold activeRegister; omega) (by unfold dispatchRegister; omega)) hf.randomCursor
  have one : (clearedScratch t).val.indices oneRegister = 1 := by
    rw [clearedScratch, clearedCells_indices]
    simpa only [scratchCells, oneRegister, List.mem_cons, List.not_mem_nil, or_false,
      Nat.reduceEqDiff, or_self, ite_false] using
      (hf.indices oneRegister (by decide) (by decide)).trans h.one
  have active : (clearedScratch t).val.indices activeRegister = 0 := by
    rw [clearedScratch, clearedCells_indices]
    simpa only [scratchCells, activeRegister, List.mem_cons, List.not_mem_nil, or_false,
      Nat.reduceEqDiff, or_self, ite_false] using ha
  refine ⟨1 + (cost + 27) + 1, clearedScratch t, by unfold terminalConstant; omega, ?_,
    clearScratch_represents t hr⟩
  exact Executes.more (by rw [h.one, h.active]) (he.seq (clearScratch_executes input tape t))
    (Executes.done (by rw [one, active]; omega))

/-- The source-side width promise is stated on all actual charged prefixes.
It is not inferred from total runtime. -/
def PrefixAddressBound (M : BitRAM) (bits : List Bool) (tape : ℕ → Bool)
    (start : BitRAMState) (fuel width : ℕ) : Prop :=
  ∀ n t, n ≤ fuel → PricedSteps (M.next bits tape) n start t → t.address.length ≤ width

theorem PrefixAddressBound.tail {M : BitRAM} {bits : List Bool} {tape : ℕ → Bool}
    {a b : BitRAMState} {extra n W : ℕ}
    (h : PrefixAddressBound M bits tape a (extra + 1 + n) W)
    (step : M.next bits tape a = some ⟨b, extra⟩) :
    PrefixAddressBound M bits tape b n W := by
  intro k t hk ht
  exact h (extra + 1 + k) t (by omega) (PricedSteps.step step ht)

end Maxwell.Cost.RealSimulation
