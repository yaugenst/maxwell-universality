import Maxwell.Cost.CalibrationMatrix.Allocation.Layout
import Maxwell.Cost.Structured.NatAssign

namespace Maxwell.Cost.CalibrationMatrix.Allocation
open Structured
open RationalAccumulator (Word)
set_option maxRecDepth 65536
set_option maxHeartbeats 3500000

def setupPlan : List NatAssign.Instruction :=
  [.literal 110 0,.copy 122 248,.multiply 122 248,.multiply 100 248,
   .copy 248 111,.copy 122 249,.multiply 100 249,
   .copy 247 250,.multiply 100 250,.copy 248 251,.add 248 251]

def densePlan : List NatAssign.Instruction :=
  [.copy 251 230,.add 249 251,.copy 251 231,.add 249 251,
   .copy 251 232,.add 249 251,.copy 251 233,.add 249 251,
   .copy 251 234,.add 249 251,.copy 251 235,.add 249 251,
   .copy 251 236,.add 249 251,.copy 251 237,.add 249 251,
   .copy 251 238,.add 249 251,.copy 251 239,.add 249 251,
   .copy 251 240,.add 249 251,.copy 251 241,.add 249 251,
   .copy 251 242,.add 249 251,.copy 251 243,.add 249 251]

def sparsePlan : List NatAssign.Instruction :=
  [.copy 251 244,.add 250 251,.copy 251 245,.add 250 251,.copy 251 246,.add 250 251]

def plan : List NatAssign.Instruction :=
  setupPlan++densePlan++sparsePlan++[.literal 248 0,.literal 249 0,.literal 250 0]

def ids : Finset ℕ := {100,110,111,122} ∪ Finset.Icc 230 251

def initial (n width capacity i : ℕ) : ℕ :=
  if i = 100 then width else if i = 122 then n else if i = 247 then capacity else 0

def code : Code := NatAssign.code plan
def costCap (n width capacity : ℕ) : ℕ := NatAssign.price plan (initial n width capacity)

structure Stored (n width capacity : ℕ) (s : BitRAMState) : Prop where
  positive : Word s 110 0
  negative : Word s 111 (matrixSpan n width)
  dense : ∀ i : Fin 14, Word s (230+i.val) (denseBase n width i.val)
  sparse : ∀ i : Fin 3, Word s (244+i.val) (sparseBase n width capacity i.val)
  memoryEnd : Word s 251 (memoryEnd n width capacity)
  temporary : ∀ i, 248 ≤ i → i ≤ 250 → Word s i 0

theorem stored_of_bank (n width capacity : ℕ) (s : BitRAMState)
    (hb : NatAssign.Bank ids (NatAssign.values plan (initial n width capacity)) s) :
    Stored n width capacity s := by
  have getWord (i : ℕ) (hi : i ∈ ids) := hb i hi
  constructor
  · simpa [plan,setupPlan,densePlan,sparsePlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial] using getWord 110 (by simp [ids])
  · convert getWord 111 (by simp [ids]) using 1
    simp [plan,setupPlan,densePlan,sparsePlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial,matrixSpan]
    ring
  · intro i
    have hi : 230+i.val ∈ ids := by simp [ids]; omega
    convert getWord (230+i.val) hi using 1
    fin_cases i <;> simp [plan,setupPlan,densePlan,sparsePlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial,denseBase,matrixSpan,vectorSpan] <;> ring
  · intro i
    have hi : 244+i.val ∈ ids := by simp [ids]; omega
    convert getWord (244+i.val) hi using 1
    fin_cases i <;> simp [plan,setupPlan,densePlan,sparsePlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial,sparseBase,denseBase,matrixSpan,vectorSpan] <;> ring
  · convert getWord 251 (by simp [ids]) using 1
    simp [plan,setupPlan,densePlan,sparsePlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial,memoryEnd,sparseBase,denseBase,matrixSpan,vectorSpan]
    ring
  · intro i hi hj
    have h := getWord i (by simp [ids]; omega)
    interval_cases i <;> simpa [plan,setupPlan,densePlan,sparsePlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial] using h

/-- Actual additions and products allocate a sequential layout before
matrix construction; saved descriptors survive the generator's work tapes. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (n width capacity : ℕ) (s : Store)
    (hw : Word s.val 100 width) (hn : Word s.val 122 n) (hm : Word s.val 247 capacity)
    (hz : ∀ i ∈ ids, i ≠ 100 → i ≠ 122 → i ≠ 247 → Word s.val i 0)
    (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ costCap n width capacity ∧
      Stored n width capacity t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (NatAssign.changes plan) s.val t.val := by
  have hid : ∀ i ∈ ids, 4 ≤ i := by
    intro i hi
    simp only [ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
    omega
  have valid : ∀ a ∈ plan, a.Valid ids := by
    simp [plan,setupPlan,densePlan,sparsePlan,NatAssign.Instruction.Valid,ids]
  have bank : NatAssign.Bank ids (initial n width capacity) s.val := by
    intro i hi
    by_cases hiw : i = 100
    · subst i;simpa [initial] using hw
    · by_cases hin : i = 122
      · subst i;simpa [initial] using hn
      · by_cases him : i = 247
        · subst i;simpa [initial] using hm
        · simpa [initial,hiw,hin,him] using hz i hi hiw hin him
  obtain ⟨cost,t,he,hc,hb,ht,hf⟩ := NatAssign.executes ids hid plan valid (initial n width capacity)
    input tape s bank hs
  exact ⟨cost,t,he,hc,stored_of_bank n width capacity t.val hb,ht,hf⟩

end Maxwell.Cost.CalibrationMatrix.Allocation
