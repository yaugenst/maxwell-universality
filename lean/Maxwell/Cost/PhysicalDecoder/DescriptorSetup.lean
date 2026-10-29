import Maxwell.Cost.PhysicalMaterial.DescriptorRead
import Maxwell.Cost.Structured.NatAssign.Bounds

/-! Actual addressed loading of a decoder vertex's physical anchor and strength.
The index is the runtime word computed by `PhysicalDecoder.Indices`. -/
namespace Maxwell.Cost.PhysicalDecoder.DescriptorSetup
open Structured RationalAccumulator
open PhysicalMaterial

def target (i : Fin 5) : ℕ := ![340,341,342,352,353] i
def targets : Finset ℕ := {340,341,342,352,353}
def ids : Finset ℕ := {294,295,296,276,277,340,341,342,352,353}
def plan : List NatAssign.Instruction :=
  [.copy 294 340, .copy 295 341, .copy 296 342, .copy 276 352, .copy 277 353,
   .literal 294 0, .literal 295 0, .literal 296 0, .literal 276 0, .literal 277 0]
def initial (v : Fin 5 → ℕ) (j : ℕ) : ℕ :=
  if j=294 then v 0 else if j=295 then v 1 else if j=296 then v 2 else
    if j=276 then v 3 else if j=277 then v 4 else 0
def changed : Finset ℕ := {0,1,2,3,294,295,296,276,277,340,341,342,352,353}
def code : Code := .seq Descriptors.readCode (NatAssign.code plan)
def costBound (B : ℕ) : ℕ := (100000+3000*8^10)*(B+2)^2

theorem plan_valid : ∀ a ∈ plan, a.Valid ids := by
  simp [plan, NatAssign.Instruction.Valid, ids]

theorem changes : NatAssign.changes plan = changed := by
  ext j
  simp [NatAssign.changes, plan, NatAssign.Instruction.target, changed]
  tauto

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem executes {n : ℕ} (d : Descriptors.Data n) (row : Fin n) (B : ℕ) (hd : d.Sized B)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = row.val) (hil : index.length ≤ B) (s : Store)
    (hs : Descriptors.Ready s.val) (hdata : Descriptors.Stored d s.val) (hindex : BankArray.Word s.val 302 index)
    (hbank : Descriptors.Bank s.val (fun _ => 0)) (hz : ∀ i, Blank s.val (target i)) :
    ∃ cost t, cost ≤ costBound B ∧ Executes input tape code cost s t ∧
      Descriptors.Ready t.val ∧ Descriptors.Stored d t.val ∧ Descriptors.Bank t.val (fun _ => 0) ∧
      (∀ i, Word t.val (target i) (Descriptors.value d row i)) ∧ Descriptors.Frame changed s.val t.val := by
  obtain ⟨cr, r, hcr, er, rr, dr, br, fr⟩ :=
    Descriptors.read d row B hd input tape index hi hil s hs hdata hindex hbank
  have rz (i : Fin 5) : Blank r.val (target i) := blank_of_eq
    (fr.tapes (target i) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)) (hz i)
  let v := Descriptors.value d row
  have rb : NatAssign.Bank ids (initial v) r.val := by
    intro j hj
    simp only [ids, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact br 0
    · exact br 1
    · exact br 2
    · exact br 3
    · exact br 4
    · exact (zero_word_iff_blank _ _).mpr (rz 0)
    · exact (zero_word_iff_blank _ _).mpr (rz 1)
    · exact (zero_word_iff_blank _ _).mpr (rz 2)
    · exact (zero_word_iff_blank _ _).mpr (rz 3)
    · exact (zero_word_iff_blank _ _).mpr (rz 4)
  obtain ⟨ca, t, ea, hca, bt, rt, ft⟩ := NatAssign.executes ids (by decide) plan
    plan_valid (initial v) input tape r rb (fun j hj => rr j (by omega))
  have hbits (i : Fin 5) : (v i).bits.length ≤ B :=
    (Descriptors.value_bits d row i s.val hdata).trans hd.2.1
  have hb : ∀ j ∈ ids, (initial v j).bits.length ≤ B := by
    intro j _
    simp only [initial]
    split_ifs <;> first | exact hbits _ | simp
  have hp : NatAssign.price plan (initial v) ≤ 3000*8^10*(B+2)^2 := by
    simpa only [plan, List.length_cons, List.length_nil] using
      NatAssign.price_bound ids plan plan_valid (initial v) B hb (by
        intro a ha
        simp only [plan, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [NatAssign.Instruction.literalWidth])
  have frame : Descriptors.Frame changed s.val t.val := by
    refine ⟨ft.memory.trans fr.memory, ft.inputHead.trans fr.inputHead,
      ft.randomCursor.trans fr.randomCursor, ft.output.trans fr.output, ?_⟩
    intro j hj hn
    exact (ft.tapes j (changes ▸ hn)).trans (fr.tapes j hj (by
      simp only [changed, Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp only [Descriptors.targets, Finset.mem_insert, Finset.mem_singleton, not_or]
      omega))
  refine ⟨cr+ca, t, by unfold costBound; nlinarith, er.seq ea, ?_, ?_, ?_, ?_, frame⟩
  · intro j hj
    by_cases h4 : j<4
    · exact rt j h4
    · exact blank_of_eq (ft.tapes j (by
        rw [changes]
        simp only [changed, Finset.mem_insert, Finset.mem_singleton, not_or]; omega)) (rr j hj)
  · refine ⟨BankArray.word_of_eq (frame.tapes 300 (by decide) (by decide)) hdata.width,
      BankArray.word_of_eq (frame.tapes 301 (by decide) (by decide)) hdata.clock, ?_, ?_⟩
    · intro i
      exact BankArray.word_of_eq (frame.tapes (Descriptors.baseTape i)
        (by simp only [Descriptors.baseTape]; omega) (by
          simp only [Descriptors.baseTape, changed, Finset.mem_insert, Finset.mem_singleton, not_or]
          have := i.isLt
          omega)) (hdata.bases i)
    · intro i
      simpa only [frame.memory] using hdata.arrays i
  · intro i
    have h := bt (Descriptors.targetTape i) (by fin_cases i <;> decide)
    fin_cases i <;>
      simpa [Descriptors.targetTape, plan, NatAssign.values, NatAssign.Instruction.update,
        NatAssign.Instruction.target, NatAssign.Instruction.value] using h
  · intro i
    have h := bt (target i) (by fin_cases i <;> decide)
    fin_cases i <;>
      simpa [target, initial, plan, NatAssign.values, NatAssign.Instruction.update,
        NatAssign.Instruction.target, NatAssign.Instruction.value, v] using h

end Maxwell.Cost.PhysicalDecoder.DescriptorSetup
