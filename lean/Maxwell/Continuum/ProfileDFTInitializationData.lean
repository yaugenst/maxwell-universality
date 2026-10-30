import Maxwell.Continuum.ProfileDFTLoop

/-! Fixed register initialization for the stored-parameter profile DFT.
Only eleven registers are reset; the sample count and frequency remain
runtime data on external tapes. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def dftRegisters : Finset ℕ := Finset.range 11
def dftReset : List Instruction := (List.range 11).map (fun i => .literal i 0)
def dftResetValues (v : ℕ→Parts) : ℕ→Parts := evaluate dftReset v
def dftFrequency (negative : Bool) (j : ℕ) : ℤ := if negative then (j:ℤ) else -(j:ℤ)
def dftFrequencyChannel (negative : Bool) : NaturalChannel.Channel :=
  if negative then .negative else .positive
def dftArgumentValues (grid : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (dftResetValues v) 0 (gridArgument grid 0)
def dftInitialValues (negative : Bool) (grid j : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (dftArgumentValues grid v) 5 (integerArgument (-dftFrequency negative j))
def dftInitializeCode (negative : Bool) : Code := .seq (program dftReset)
  (.seq (NaturalChannel.code .denominator 664 0)
    (.seq (NaturalChannel.code (dftFrequencyChannel negative) 700 5)
      (WordReplace.code 664 201)))

private theorem reset_value (rs : List ℕ) (v : ℕ→Parts) (i : ℕ) :
    evaluate (rs.map (fun j => Instruction.literal j 0)) v i=
      if i∈rs then Parts.literal 0 else v i := by
  induction rs generalizing v with
  | nil => simp [evaluate]
  | cons j rs ih =>
    simp only [List.map_cons,evaluate]
    rw [ih]
    by_cases hir : i∈rs
    · simp [hir]
    · by_cases hij : i=j
      · subst i;simp [hir,Instruction.update]
      · simp [hir,hij,Instruction.update]

theorem dftResetValues_eq (v : ℕ→Parts) (i : ℕ) :
    dftResetValues v i=if i<11 then Parts.literal 0 else v i := by
  simpa only [dftResetValues,dftReset,List.mem_range] using reset_value (List.range 11) v i

private theorem reset_trace (rs : List ℕ) (S : Finset ℕ) (v : ℕ→Parts) (W : ℕ)
    (hW : 1≤W) (hw : WidthBank S W v) :
    WidthTrace S W (rs.map (fun i => Instruction.literal i 0)) v := by
  induction rs generalizing v with
  | nil => exact hw
  | cons i rs ih =>
    have hz : (Parts.literal 0).Width W := (show (Parts.literal 0).Width 1 by
      simp [Parts.Width,Parts.literal]).mono hW
    exact ⟨hw,hz,ih (Function.update v i (Parts.literal 0)) (hw.update i hz)⟩

theorem dftReset_width (v : ℕ→Parts) (W : ℕ) (hW : 1≤W) (hw : WidthBank dftRegisters W v) :
    WidthTrace dftRegisters W dftReset v := reset_trace _ _ _ _ hW hw

theorem dftReset_valid : ∀a∈dftReset,a.Valid dftRegisters := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  exact Finset.mem_range.mpr (List.mem_range.mp hi)

theorem dftResetValues_width (v : ℕ→Parts) : WidthBank dftRegisters 1 (dftResetValues v) := by
  intro i hi
  rw [dftResetValues_eq,ite_eq_left (Finset.mem_range.mp hi)]
  simp [Parts.Width,Parts.literal]

theorem dftInitialValues_width (negative : Bool) (grid j U : ℕ) (v : ℕ→Parts)
    (hg : grid≤U) (hj : j≤U) : WidthBank dftRegisters (U+1) (dftInitialValues negative grid j v) := by
  exact ((dftResetValues_width v).mono (by omega)).update 0
    (gridArgument_width grid 0 U hg (by omega)) |>.update 5
      (integerArgument_width _ U (by cases negative <;> simpa [dftFrequency] using hj))

theorem dftFrequency_abs (negative : Bool) (j : ℕ) : (dftFrequency negative j).natAbs=j := by
  cases negative <;> simp [dftFrequency]

theorem dftArgument_replace (grid : ℕ) (v : ℕ→Parts) :
    Function.update (dftResetValues v) 0
      (NaturalChannel.replace .denominator (dftResetValues v 0) grid)=dftArgumentValues grid v := by
  rw [dftResetValues_eq]
  rfl

theorem dftFrequency_replace (negative : Bool) (grid j : ℕ) (v : ℕ→Parts) :
    Function.update (dftArgumentValues grid v) 5
      (NaturalChannel.replace (dftFrequencyChannel negative) (dftArgumentValues grid v 5) j)=
        dftInitialValues negative grid j v := by
  have hv : dftArgumentValues grid v 5=Parts.literal 0 := by simp [dftArgumentValues,dftResetValues_eq]
  rw [hv]
  cases negative <;> simp [dftInitialValues,dftFrequency,dftFrequencyChannel,NaturalChannel.replace,
    integerArgument,Parts.literal]

theorem dftInitialValues_zero (negative : Bool) (grid j : ℕ) (v : ℕ→Parts) :
    dftInitialValues negative grid j v 0=gridArgument grid 0 := by
  simp [dftInitialValues,dftArgumentValues]

theorem dftInitialValues_frequency (negative : Bool) (grid j : ℕ) (v : ℕ→Parts) :
    dftInitialValues negative grid j v 5=integerArgument (-dftFrequency negative j) := by
  simp [dftInitialValues]

theorem dftInitialValues_accumulator (negative : Bool) (grid j : ℕ) (v : ℕ→Parts) :
    dftInitialValues negative grid j v 9=Parts.literal 0 := by
  simp [dftInitialValues,dftArgumentValues,dftResetValues_eq]

#print axioms dftInitialValues_width
end Maxwell.Continuum.Profile.Runtime
