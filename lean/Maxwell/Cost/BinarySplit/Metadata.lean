import Maxwell.Cost.BinarySplit.Layout

namespace Maxwell.Cost.BinarySplit
open Structured
open BankArray (Word)

def Saved (layout : Layout) (s : BitRAMState) : Prop :=
  Word s 100 layout.forward.bits ∧ Word s 101 layout.backward.bits ∧
  Word s 102 layout.route.oldJump.bits ∧ Word s 103 layout.route.oldMinimum.bits ∧
  Word s 104 layout.route.newJump.bits ∧ Word s 105 layout.route.newMinimum.bits

def metadataIds : List ℕ := [80,81,82,83,84,85,86,98,99,100,101,102,103,104,105]

def savedWords (layout : Layout) (i : ℕ) : List Bool :=
  if i=100 then layout.forward.bits else if i=101 then layout.backward.bits else
  if i=102 then layout.route.oldJump.bits else if i=103 then layout.route.oldMinimum.bits else
  if i=104 then layout.route.newJump.bits else if i=105 then layout.route.newMinimum.bits else []

def metadata (layout : Layout) (current : DoublingPass.Layout) (clock : List Bool) : ℕ → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (savedWords layout)
      80 current.width.bits) 81 []) 82 current.oldJump.bits) 83 clock) 84 current.oldMinimum.bits)
      85 current.newJump.bits) 86 current.newMinimum.bits) 98 layout.pairing.bits) 99 layout.conjugated.bits

theorem metadata_bank (layout : Layout) (current : DoublingPass.Layout) (clock : List Bool) (s : BitRAMState)
    (cfg : DoublingInit.Config ⟨current,layout.pairing,layout.conjugated⟩ [] clock s)
    (saved : Saved layout s) : WordAssign.Bank metadataIds s (metadata layout current clock) := by
  intro i hi
  simp only [metadataIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [metadata, Function.update_apply]
  all_goals norm_num [savedWords]
  · exact cfg.route.width
  · exact cfg.route.index
  · exact cfg.route.oldJump
  · exact cfg.route.clock
  · exact cfg.route.oldMinimum
  · exact cfg.route.newJump
  · exact cfg.route.newMinimum
  · exact cfg.inputA
  · exact cfg.inputB
  · exact saved.1
  · exact saved.2.1
  · exact saved.2.2.1
  · exact saved.2.2.2.1
  · exact saved.2.2.2.2.1
  · exact saved.2.2.2.2.2

theorem metadata_config {layout : Layout} {current : DoublingPass.Layout} {clock : List Bool} {s : BitRAMState}
    (bank : WordAssign.Bank metadataIds s (metadata layout current clock)) :
    DoublingInit.Config ⟨current,layout.pairing,layout.conjugated⟩ [] clock s := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  all_goals first
  | exact (by simpa [metadata,savedWords] using bank 80 (by simp [metadataIds]))
  | exact (by simpa [metadata,savedWords] using bank 81 (by simp [metadataIds]))
  | exact (by simpa [metadata,savedWords] using bank 82 (by simp [metadataIds]))
  | exact (by simpa [metadata,savedWords] using bank 83 (by simp [metadataIds]))
  | exact (by simpa [metadata,savedWords] using bank 84 (by simp [metadataIds]))
  | exact (by simpa [metadata,savedWords] using bank 85 (by simp [metadataIds]))
  | exact (by simpa [metadata,savedWords] using bank 86 (by simp [metadataIds]))
  | exact (by simpa [metadata,savedWords] using bank 98 (by simp [metadataIds]))
  | exact (by simpa [metadata,savedWords] using bank 99 (by simp [metadataIds]))

theorem metadata_saved {layout : Layout} {current : DoublingPass.Layout} {clock : List Bool} {s : BitRAMState}
    (bank : WordAssign.Bank metadataIds s (metadata layout current clock)) : Saved layout s := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [metadata,savedWords] using bank 100 (by simp [metadataIds])
  · simpa [metadata,savedWords] using bank 101 (by simp [metadataIds])
  · simpa [metadata,savedWords] using bank 102 (by simp [metadataIds])
  · simpa [metadata,savedWords] using bank 103 (by simp [metadataIds])
  · simpa [metadata,savedWords] using bank 104 (by simp [metadataIds])
  · simpa [metadata,savedWords] using bank 105 (by simp [metadataIds])

def conjugateAssignments : List WordAssign.Assignment := [(100,82),(98,84),(101,85),(99,86)]
def cycleAssignments : List WordAssign.Assignment := [(102,82),(103,84),(104,85),(105,86)]

theorem conjugate_metadata (layout : Layout) (clock : List Bool) :
    WordAssign.values conjugateAssignments (metadata layout layout.half.route clock)=metadata layout layout.conjugate clock := by
  funext i
  by_cases h82 : i=82 <;> by_cases h84 : i=84 <;> by_cases h85 : i=85 <;> by_cases h86 : i=86 <;>
    simp [WordAssign.values,conjugateAssignments,metadata,savedWords,Layout.half,Layout.conjugate,
      Function.update_apply,h82,h84,h85,h86]

theorem cycle_metadata (layout : Layout) (clock : List Bool) :
    WordAssign.values cycleAssignments (metadata layout layout.conjugate clock)=metadata layout layout.route clock := by
  funext i
  by_cases h82 : i=82 <;> by_cases h84 : i=84 <;> by_cases h85 : i=85 <;> by_cases h86 : i=86 <;>
    simp [WordAssign.values,cycleAssignments,metadata,savedWords,Layout.conjugate,
      Function.update_apply,h82,h84,h85,h86]

end Maxwell.Cost.BinarySplit
