import Maxwell.Continuum.SourceRoutingPathWord

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

abbrev Entry := Fin 3×ℕ
def entryValue (v : ℕ→ℕ) (entry : Entry) : ℕ := v (axisBank entry.1)+entry.2
def cursorValues (v : ℕ→ℕ) (cursor : ℕ) : ℕ→ℕ := Function.update v 1234 cursor
def wordsCode : List Entry→Code
  | [] => .skip
  | entry::rest => .seq (wordCode entry.1 entry.2) (wordsCode rest)

def entryBits (width : ℕ) (v : ℕ→ℕ) (entries : List Entry) : List Bool :=
  entries.flatMap (fun e => IncidenceEncoding.word width (entryValue v e))

theorem entryBits_length (width : ℕ) (v : ℕ→ℕ) (entries : List Entry) :
    (entryBits width v entries).length=entries.length*width := by
  induction entries with
  | nil => simp [entryBits]
  | cons e es ih =>
    simp only [entryBits,List.flatMap_cons,List.length_append,IncidenceEncoding.word_length,
      List.length_cons] at ih ⊢
    rw [ih,Nat.add_mul]
    omega

theorem writeBits_append (memory : ℕ→Bool) (address : ℕ) (a b : List Bool) :
    MemoryWord.writeBits (MemoryWord.writeBits memory address a) (address+a.length) b=
      MemoryWord.writeBits memory address (a++b) := by
  induction a generalizing memory address with
  | nil => rfl
  | cons bit rest ih =>
    simpa only [List.length_cons,List.cons_append,MemoryWord.writeBits,Nat.add_assoc,Nat.add_comm,
      Nat.add_left_comm] using ih (Function.update memory address bit) (address+1)

theorem cursorValues_other (v : ℕ→ℕ) (cursor j : ℕ) (different : j≠1234) :
    cursorValues v cursor j=v j := Function.update_of_ne different _ _

theorem cursorValues_axis (v : ℕ→ℕ) (cursor : ℕ) (axis : Fin 3) :
    cursorValues v cursor (axisBank axis)=v (axisBank axis) :=
  cursorValues_other v cursor _ (by dsimp only [axisBank];have := axis.isLt;omega)

theorem cursorValues_width (v : ℕ→ℕ) (cursor B : ℕ)
    (width : ∀j∈GeometryArithmetic.ids,(v j).bits.length ≤ B) (cursorBound : cursor.bits.length ≤ B) :
    ∀j∈GeometryArithmetic.ids,(cursorValues v cursor j).bits.length ≤ B := by
  intro j hj
  by_cases same : j=1234
  · subst j;exact cursorBound
  · simpa only [cursorValues_other v cursor j same] using width j hj

theorem cursorValues_update (v : ℕ→ℕ) (cursor next : ℕ) :
    Function.update (cursorValues v cursor) 1234 next=cursorValues v next := by
  simp only [cursorValues,Function.update_idem]

#print axioms writeBits_append
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
