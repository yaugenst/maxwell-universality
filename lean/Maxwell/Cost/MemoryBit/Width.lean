import Maxwell.Cost.MemoryBit
import Maxwell.Cost.VisitedExecution.Composition

namespace Maxwell.Cost.MemoryBit

/-- Loading followed by a charged bit-memory read/write never exceeds the
larger of the caller's initial address and the loaded word. -/
theorem access_visited (addressTape : ℕ) (operation : BitRAMInstruction)
    (hop : operation=.readMemory 28 ∨ operation=.writeMemory 28)
    (input : List Bool) (randomTape : ℕ→Bool) (bits : List Bool) (origin : ℤ)
    (s : BitRAMState) (hpc : s.pc=0)
    (hword : s.tapes addressTape=BitTape.shiftedEnd bits origin) :
    ∃ t, VisitedPriced ((program addressTape operation).next input randomTape)
        (Address.Within (max s.address.length bits.length)) (7*bits.length+7) s t ∧
      t.pc=8 ∧ t.address=bits := by
  obtain ⟨loaded,hl,hp,ha⟩ := Address.load_visited addressTape input randomTape bits origin s hpc hword
  have hc := (contains_load addressTape operation).visited_call input randomTape hl
    (by simp [Address.load,hp])
  simp only [BitRAMState.relocate,Nat.zero_add] at hc
  rcases hop with rfl|rfl
  · let final := ({loaded with pc:=7}:BitRAMState).setRegister 28 (loaded.memory (addressValue bits))
    have hr : VisitedPriced ((program addressTape (.readMemory 28)).next input randomTape)
        (Address.Within (max s.address.length bits.length)) (bits.length+1)
        {loaded with pc:=7} final := by
      apply VisitedPriced.step (extra := bits.length) (rest := .refl (by
        simp [Address.Within,final,BitRAMState.setRegister,ha]))
      · exact hl.finish
      · simp [program,Address.load,BitRAMInstruction.relocate,BitRAM.next,ha,final]
    refine ⟨final,?_,rfl,ha⟩
    convert hc.trans hr using 1
    omega
  · let final := {loaded with pc:=8,memory:=Function.update loaded.memory (addressValue bits) (loaded.registers 28)}
    have hr : VisitedPriced ((program addressTape (.writeMemory 28)).next input randomTape)
        (Address.Within (max s.address.length bits.length)) (bits.length+1)
        {loaded with pc:=7} final := by
      apply VisitedPriced.step (extra := bits.length) (rest := .refl (by
        simp [Address.Within,final,ha]))
      · exact hl.finish
      · simp [program,Address.load,BitRAMInstruction.relocate,BitRAM.next,ha,final]
    refine ⟨final,?_,rfl,ha⟩
    convert hc.trans hr using 1
    omega

/-- Strengthen an existing exact execution without changing its endpoint. -/
theorem access_trace_visited (addressTape : ℕ) (operation : BitRAMInstruction)
    (hop : operation=.readMemory 28 ∨ operation=.writeMemory 28)
    (input : List Bool) (randomTape : ℕ→Bool) (bits : List Bool) (origin : ℤ)
    (s t : BitRAMState) (hpc : s.pc=0)
    (hword : s.tapes addressTape=BitTape.shiftedEnd bits origin)
    (h : PricedSteps ((program addressTape operation).next input randomTape) (7*bits.length+7) s t) :
    VisitedPriced ((program addressTape operation).next input randomTape)
      (Address.Within (max s.address.length bits.length)) (7*bits.length+7) s t := by
  obtain ⟨u,hu,_,_⟩ := access_visited addressTape operation hop input randomTape bits origin s hpc hword
  have he := hu.steps.endpoint_eq h rfl
  subst u
  exact hu

theorem access_prefix (addressTape : ℕ) (operation : BitRAMInstruction)
    (hop : operation=.readMemory 28 ∨ operation=.writeMemory 28)
    (input : List Bool) (randomTape : ℕ→Bool) (bits : List Bool) (origin : ℤ)
    (s : BitRAMState) (hpc : s.pc=0)
    (hword : s.tapes addressTape=BitTape.shiftedEnd bits origin)
    (n : ℕ) (u : BitRAMState) (hn : n≤7*bits.length+7)
    (hu : PricedSteps ((program addressTape operation).next input randomTape) n s u) :
    u.address.length≤max s.address.length bits.length := by
  obtain ⟨t,ht,_,_⟩ := access_visited addressTape operation hop input randomTape bits origin s hpc hword
  exact ht.prefix_bound hn hu

end Maxwell.Cost.MemoryBit
