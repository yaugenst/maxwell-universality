import Maxwell.Continuum.RationalDataflowArraySquaresMachine
import Maxwell.Continuum.RationalDataflowArrayScale
import Maxwell.Continuum.RationalDataflowArrayTransfer
import Maxwell.Continuum.RationalSquareRootNormalizeScalar

/-! The array norm fold retains the square-root operands, output headers,
and saved array count. Its actual raw result supplies the root input. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray.Normalize
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration
set_option maxHeartbeats 2500000
set_option maxRecDepth 32768

def slots : Finset ℕ := {1,24}
def retained : List ℕ := [4,40,220,221,222,223,228,229,230,231,530,531,532,533,534,
  540,541,542,543,544,548,700,787,37,210,212,213,214,215]
def afterSquares {T : ℕ} (a : Table T) (v : ℕ→Parts) : ℕ→Parts :=
  iterate a 1 (squaresBody 24 1) (sumStart v 24) T
def squareNumbers (n : ℕ→ℕ) (v : ℕ→Parts) (i : ℕ) : ℕ :=
  if i∈cellPorts 24 then dataValues v i else if i∈RationalMagnitude.ids then 0 else n i

theorem squares_protects : retained.all
    (fun i=>(squaresCode 24 1).protectsTape i)=true := by decide
theorem squares_memory : (squaresCode 24 1).protectsMemory=true := by decide

theorem squares_keeps {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (e : Executes input tape (squaresCode 24 1) cost s t) (i : ℕ) (hi : i∈retained) :
    t.val.tapes i=s.val.tapes i :=
  e.protectsTape i (List.all_eq_true.mp squares_protects i hi)

theorem squareNumbers_bank (n : ℕ→ℕ) (v : ℕ→Parts)
    {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (e : Executes input tape (squaresCode 24 1) cost s t)
    (old : NatAssign.Bank (RationalRoot.Stored.ids 24) n s.val) (raw : Ready slots v t) :
    NatAssign.Bank (RationalRoot.Stored.ids 24) (squareNumbers n v) t.val := by
  intro i hi
  by_cases cell : i∈cellPorts 24
  · simpa only [squareNumbers,ite_eq_left cell] using raw.1 i (cell_mem (by simp [slots]) cell)
  by_cases mag : i∈RationalMagnitude.ids
  · have low : i<1000 := by
      simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at mag;omega
    simpa only [squareNumbers,ite_eq_right cell,ite_eq_left mag,dataValues_small v low]
      using raw.1 i (Finset.mem_union_right _ (Finset.mem_union_right _ mag))
  · simp only [squareNumbers,ite_eq_right cell,ite_eq_right mag]
    apply RationalAccumulator.word_of_eq (squares_keeps e i _) (old i hi)
    rcases Finset.mem_union.mp hi with hi|hi
    · have hraw := (Finset.mem_union.mp hi).resolve_right cell
      simp only [RationalRoot.Raw.ids,RationalRoot.ids,NaturalRoot.fullIds,NaturalRoot.ids,
        RationalCanonicalBank.ids,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hraw mag
      simp only [retained,List.mem_cons,List.not_mem_nil,or_false]
      omega
    · have eq : i=700 := by simpa using hi
      subst i
      simp [retained]

theorem squareNumbers_width (n : ℕ→ℕ) (v : ℕ→Parts) (B W : ℕ) (hBW : B≤W)
    (old : ∀i∈RationalRoot.Stored.ids 24,(n i).bits.length≤B) (raw : WidthBank slots W v) :
    ∀i∈RationalRoot.Stored.ids 24,(squareNumbers n v i).bits.length≤W := by
  intro i hi
  unfold squareNumbers
  split_ifs with cell mag
  · exact dataValues_width slots v W raw i (cell_mem (by simp [slots]) cell)
  · exact Nat.zero_le _
  · exact (old i hi).trans hBW

theorem squares_output {T U : ℕ} {a : Table T} {b : Table U}
    {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (e : Executes input tape (squaresCode 24 1) cost s t)
    (old : b.OutputReady s) (array : a.Ready t) : b.OutputReady t := by
  apply old.transfer (e.protectsMemory squares_memory) _ array.scratch array.seven
  intro i hi
  apply squares_keeps e i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [retained]

theorem root_arrays {T U : ℕ} {a : Table T} {b : Table U} {s t : Store}
    (array : a.Ready s) (output : b.OutputReady s)
    (frame : BinaryPrecision.Frame (RationalRoot.normalizeScalarChanged 24) s.val t.val)
    (scratch : NatAssign.Scratch t.val) : a.Ready t ∧ b.OutputReady t := by
  have z : BankArray.Scratch t.val :=
    ⟨scratch 0 (by decide),scratch 1 (by decide),scratch 2 (by decide),scratch 3 (by decide),
     RationalAccumulator.blank_of_eq (frame.tapes 5 (by decide)) array.scratch.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (frame.tapes 6 (by decide)) array.scratch.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (frame.tapes 8 (by decide)) array.scratch.2.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (frame.tapes 9 (by decide)) array.scratch.2.2.2.2.2.2.2⟩
  have seven := RationalAccumulator.blank_of_eq (frame.tapes 7 (by decide)) array.seven
  constructor
  · apply array.transfer frame.memory _ z seven
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> exact frame.tapes _ (by decide)
  · apply output.transfer frame.memory _ z seven
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> exact frame.tapes _ (by decide)

theorem shared_of_root {S : Finset ℕ} {v : ℕ→Parts} {s : Store} (raw : Ready S v s)
    (blank : ∀i∈({4,220,221,222,223}:Finset ℕ),RationalAccumulator.Blank s.val i) :
    SharedConversion.Ready S v s := by
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact raw.1 i hi
    · rw [SharedConversion.work_values_zero v i hi,RationalAccumulator.zero_word_iff_blank]
      apply blank i
      simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
  · intro i hi
    by_cases small : i<4
    · exact raw.2 i small
    · have eq : i=4 := by omega
      subst i
      exact blank 4 (by simp)

#print axioms squareNumbers_bank
#print axioms root_arrays
end Maxwell.Continuum.RationalDataflow.PartArray.Normalize
