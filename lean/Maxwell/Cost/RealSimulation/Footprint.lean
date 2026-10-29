import Maxwell.Cost.RealSimulation.Compiler

namespace Maxwell.Cost.RealSimulation

def registerCap : BitRAMInstruction → ℕ
  | .literal r _ | .readSequential r | .addressPeek r | .addressIsEmpty r |
      .addressPush r | .readInput r | .readMemory r | .writeMemory r |
      .branch r _ _ | .randomBit r | .output r | .writeTape _ r => r + 1
  | .bitXor dst left right | .bitAnd dst left right => max (dst + 1) (max (left + 1) (right + 1))
  | .bitNot dst src | .readTape _ dst src => max (dst + 1) (src + 1)
  | _ => 0

def tapeCap : BitRAMInstruction → ℕ
  | .readTape t _ _ | .writeTape t _ | .eraseTape t | .tapeLeft t | .tapeRight t => t + 1
  | _ => 0

def footprint : List BitRAMInstruction → Layout
  | [] => ⟨0, 0⟩
  | op :: rest => ⟨max (registerCap op) (footprint rest).registerCount,
      max (tapeCap op) (footprint rest).tapeCount⟩

def Fits (L : Layout) (op : BitRAMInstruction) : Prop :=
  registerCap op ≤ L.registerCount ∧ tapeCap op ≤ L.tapeCount

theorem footprint_fits (ops : List BitRAMInstruction) (op : BitRAMInstruction)
    (h : op ∈ ops) : Fits (footprint ops) op := by
  induction ops with
  | nil => simp at h
  | cons first rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩
    · obtain ⟨hr, ht⟩ := ih h
      exact ⟨hr.trans (Nat.le_max_right _ _), ht.trans (Nat.le_max_right _ _)⟩

theorem footprint_get_fits (ops : List BitRAMInstruction) (pc : ℕ)
    (op : BitRAMInstruction) (h : ops[pc]? = some op) : Fits (footprint ops) op := by
  obtain ⟨hp, he⟩ := List.getElem?_eq_some_iff.mp h
  apply footprint_fits
  rw [← he]
  exact List.getElem_mem hp

end Maxwell.Cost.RealSimulation
