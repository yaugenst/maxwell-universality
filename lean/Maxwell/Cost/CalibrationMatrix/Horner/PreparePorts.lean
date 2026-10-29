import Maxwell.Cost.CalibrationMatrix.Horner.Step
import Maxwell.Cost.Structured.WordAssign

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured

/-- Copy the initialized persistent x/t descriptors into the four physical
ports used by the first matrix product. -/
def portAssignments : List WordAssign.Assignment :=
  [(122,112),(123,113),(130,114),(131,115)]

def portIds : List ℕ := [112,113,114,115,122,123,130,131]

def portWords {n : ℕ} (d : Data n) (old : Fin 4 → List Bool) (i : ℕ) : List Bool :=
  if i = 112 then old 0 else if i = 113 then old 1 else
  if i = 114 then old 2 else if i = 115 then old 3 else
  if i = 122 then d.bases 2 else if i = 123 then d.bases 3 else
  if i = 130 then d.bases 10 else if i = 131 then d.bases 11 else []

def preparePortsCode : Code := WordAssign.code portAssignments

theorem prepare_ports {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n)
    (B : ℕ) (hsized : d.Sized B) (old : Fin 4 → List Bool)
    (hold : ∀ i, (old i).length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool) (s : Store)
    (hw : WorkReady count B s.val) (hd : Stored d words s.val)
    (hp : ∀ i : Fin 4, BankArray.Word s.val (112+i.val) (old i)) :
    ∃ t : Store, Executes input tape preparePortsCode (WordAssign.price portAssignments (portWords d old)) s t ∧
      WordAssign.price portAssignments (portWords d old) ≤ 84*B+85 ∧
      (Snapshot.mk d words).Ready count B t.val ∧
      WordAssign.Frame portAssignments s.val t.val := by
  have valid : WordAssign.Valid portIds portAssignments := by
    simp [WordAssign.Valid,portIds,portAssignments]
  have bank : WordAssign.Bank portIds s.val (portWords d old) := by
    intro i hi
    simp only [portIds,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [portWords] using hp 0
    · simpa [portWords] using hp 1
    · simpa [portWords] using hp 2
    · simpa [portWords] using hp 3
    · simpa [portWords,baseBank] using hd.bases 2
    · simpa [portWords,baseBank] using hd.bases 3
    · simpa [portWords,baseBank] using hd.bases 10
    · simpa [portWords,baseBank] using hd.bases 11
  have lengths : ∀ i, i ∈ portIds → (portWords d old i).length ≤ B := by
    intro i hi
    simp only [portIds,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [portWords] using hold 0
    · simpa [portWords] using hold 1
    · simpa [portWords] using hold 2
    · simpa [portWords] using hold 3
    · simpa [portWords] using hsized.2.2.2.2.1 2
    · simpa [portWords] using hsized.2.2.2.2.1 3
    · simpa [portWords] using hsized.2.2.2.2.1 10
    · simpa [portWords] using hsized.2.2.2.2.1 11
  obtain ⟨t,he,hbank,hframe⟩ := WordAssign.executes portAssignments portIds input tape
    (portWords d old) valid s bank
  have keep (i : ℕ) (h112 : i ≠ 112) (h113 : i ≠ 113) (h114 : i ≠ 114) (h115 : i ≠ 115) :
      t.val.tapes i = s.val.tapes i :=
    hframe.2.2.2.2.2.1 i (by simp [portAssignments,h112,h113,h114,h115])
  refine ⟨t,he,?_,⟨hw.of_tapes (by
      intro i hi
      apply keep <;> dsimp [WorkTape] at hi <;> omega),
    hd.of_memory_tapes hframe.2.2.1 (by
      intro i hi
      apply keep <;> dsimp [Metadata] at hi <;> omega),?_,?_,?_,?_⟩,hframe⟩
  · have h := WordAssign.price_bound portAssignments portIds (portWords d old) B valid lengths
    simp only [portAssignments,List.length_cons,List.length_nil] at h
    simp only [portAssignments]
    omega
  · simpa [WordAssign.values,portAssignments,portWords] using hbank 112 (by decide)
  · simpa [WordAssign.values,portAssignments,portWords] using hbank 113 (by decide)
  · simpa [WordAssign.values,portAssignments,portWords] using hbank 114 (by decide)
  · simpa [WordAssign.values,portAssignments,portWords] using hbank 115 (by decide)

end Maxwell.Cost.CalibrationMatrix.Horner
