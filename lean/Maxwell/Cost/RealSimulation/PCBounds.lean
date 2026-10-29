import Maxwell.Cost.RealSimulation.SourceBounds

namespace Maxwell.Cost.RealSimulation

def jumpTargetCap : BitRAMInstruction → ℕ
  | .branch _ yes no => max yes no
  | .jump target => target
  | _ => 0

def jumpCap : List BitRAMInstruction → ℕ
  | [] => 0
  | op :: rest => max (jumpTargetCap op) (jumpCap rest)

def programPCCap (M : BitRAM) : ℕ := max M.code.length (jumpCap M.code)

theorem jumpCap_mem {ops : List BitRAMInstruction} {op : BitRAMInstruction}
    (h : op ∈ ops) : jumpTargetCap op ≤ jumpCap ops := by
  induction ops with
  | nil => simp at h
  | cons a rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem next_pc_bound {M : BitRAM} {bits : List Bool} {tape : ℕ → Bool}
    {s t : BitRAMState} {extra : ℕ} (h : M.next bits tape s = some ⟨t, extra⟩) :
    t.pc ≤ programPCCap M := by
  cases hc : M.code[s.pc]? with
  | none => simp [BitRAM.next, hc] at h
  | some op =>
    have hlen := (List.getElem?_eq_some_iff.mp hc).1
    have hjump : jumpTargetCap op ≤ programPCCap M := (jumpCap_mem (List.mem_of_getElem? hc)).trans
      (le_max_right M.code.length (jumpCap M.code))
    have hp : s.pc + 1 ≤ programPCCap M := by
      have := le_max_left M.code.length (jumpCap M.code)
      unfold programPCCap
      omega
    cases op <;> simp only [BitRAM.next, hc, Option.some.injEq, PricedStep.mk.injEq] at h
    all_goals try contradiction
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp only [BitRAMState.setRegister, BitRAMState.setTape]
    all_goals try exact hp
    all_goals simp only [jumpTargetCap] at hjump
    case branch register yes no => split_ifs <;> omega
    case jump target => exact hjump

theorem priced_pc_bound {M : BitRAM} {bits : List Bool} {tape : ℕ → Bool}
    {s t : BitRAMState} {n : ℕ} (steps : PricedSteps (M.next bits tape) n s t)
    (hs : s.pc ≤ programPCCap M) : t.pc ≤ programPCCap M := by
  induction steps with
  | refl => exact hs
  | step h _ ih => exact ih (next_pc_bound h)

end Maxwell.Cost.RealSimulation
