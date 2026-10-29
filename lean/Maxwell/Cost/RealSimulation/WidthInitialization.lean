import Maxwell.Cost.RealSimulation.WidthTrajectory
import Maxwell.Cost.RealSimulation.Initialization
import Maxwell.Cost.RealSimulation.RandomOffset

namespace Maxwell.Cost.RealSimulation
open Control

theorem local_sequence {P : ℕ → Prop} (cs : List Code)
    (h : ∀ c ∈ cs, LocalCode P c) : LocalCode P (sequence cs) := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    cases cs with
    | nil => exact h c (by simp)
    | cons d ds =>
      exact ⟨h c (by simp), ih (fun e he => h e (by simp [he]))⟩

theorem local_initializeState (L : Layout) : LocalCode (ScalarCell L) (initializeState L) := by
  unfold initializeState
  apply local_sequence
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [LocalCode, literal, copy, LocalInstruction, ScalarCell, zeroRegister,
          oneRegister, activeRegister]
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
      simpa [LocalCode, literal, LocalInstruction] using scalar_bit L r (List.mem_range.mp hr)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    simpa [LocalCode, copy, LocalInstruction] using scalar_tape L t (List.mem_range.mp ht)

def widthPrefix (M : BitRAM) : Code := .seq (initializeState (footprint M.code)) clearScratch
def widthProgram (M : BitRAM) : Code := .seq (widthPrefix M) (widthInterpreter M)
def widthMachine (M : BitRAM) : Machine := (widthProgram M).compile
def widthInitializationCost (M : BitRAM) : ℕ :=
  2 * ((footprint M.code).registerCount + (footprint M.code).tapeCount + 7) + 27
def completeWidthConstant (M : BitRAM) : ℕ := widthInitializationCost M + widthConstant M

theorem width_initialization (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center randomBase W : ℕ} {bits : List Bool}
    (s : Store) (entry : Initialization.EntryAt (footprint M.code) origin center bits randomBase s)
    (bound : IndexWidth.IndexBound (2 ^ W) s.val) (hbase : randomBase ≤ center)
    (hcenter : 2 * center ≤ 2 ^ W) (two : 2 ≤ 2 ^ W) :
    ∃ t, Executes input tape (widthPrefix M) (widthInitializationCost M) s t ∧
      Ready (footprint M.code) origin center bits
        {BitRAMState.initial with randomCursor := randomBase} t ∧
      IndexWidth.IndexBound (2 ^ W) t.val := by
  obtain ⟨u, he, hu⟩ := initializeState_executes_at input tape s entry
  exact ⟨clearedScratch u, he.seq (clearScratch_executes input tape u),
    clearScratch_ready u hu, cleared_boundary_bound bound ((local_initializeState _).frame he)
      hu (SourceBounds.initial_at randomBase) hbase hcenter (by simp [BitRAMState.initial]) two⟩

end Maxwell.Cost.RealSimulation
