import Maxwell.Cost.SourceCircuit.AllocationPassData
import Maxwell.Cost.SourceCircuit.TraceBinding

namespace Maxwell.Cost.SourceCircuit.AllocationPass

def requests {n : ℕ} (records : List (Record n)) : List (Fin n) :=
  records.flatMap fun r => List.replicate (r.bits.count true) r.column

theorem requests_length {n : ℕ} (records : List (Record n)) :
    (requests records).length = occurrences records := by
  induction records with
  | nil => rfl
  | cons r rest ih => simp [requests, occurrences] at ih ⊢

theorem allocationFold_append {n : ℕ} (base width : ℕ) (a b : List (Fin n)) (d : AllocationData n) :
    allocationFold base width (a ++ b) d =
      allocationFold base width b (allocationFold base width a d) := by
  induction a generalizing d with
  | nil => rfl
  | cons i rest ih => simp [allocationFold, ih]

theorem allocate_eq {n : ℕ} (base width : ℕ) (records : List (Record n)) (d : AllocationData n) :
    allocate base width records d = allocationFold base width (requests records) d := by
  induction records generalizing d with
  | nil => rfl
  | cons r rest ih =>
    simp [allocate, requests, allocationFold_append, applyRecord, scanBits_fold_allocation, ih]

/-- The record pass performs the same chronological copy construction as
the logical compiler, with one distinct leaf for every true Horner bit. -/
theorem binding {n : ℕ} (base width : ℕ) (records : List (Record n))
    (bank : Logical.CopyBank n) (d : AllocationData n)
    (represented : d.Matches width bank)
    (room : bank.size + 2 * occurrences records < 2 ^ width) :
    (allocate base width records d).Matches width (bank.allocate (requests records)).bank ∧
      traceBytes width (bank.trace (requests records)) = some (copyArchive width bank (requests records)) ∧
      (allocate base width records d).gates = d.gates ++ copyArchive width bank (requests records) ∧
      (allocate base width records d).leaves = d.leaves ++
        ((bank.allocate (requests records)).outputs.map Fin.val).flatMap (fixedWidth width) := by
  rw [allocate_eq]
  obtain ⟨hm, hg, hl⟩ := allocationFold_binding base width bank (requests records) d represented
    (by simpa [requests_length] using room)
  exact ⟨hm, copyArchive_trace width bank _, hg, by simpa [copyLeaves_outputs] using hl⟩

end Maxwell.Cost.SourceCircuit.AllocationPass
