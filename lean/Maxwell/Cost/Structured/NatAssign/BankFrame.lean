import Maxwell.Cost.Structured.NatAssign.Values

/-! Compose a checked subprogram with a larger natural-word bank. The
subprogram's stored words replace precisely its owned part of that bank. -/
namespace Maxwell.Cost.Structured.NatAssign
open RationalAccumulator (Word)

def overlay (owned : Finset ℕ) (new old : ℕ→ℕ) (i : ℕ) : ℕ :=
  if i∈owned then new i else old i

theorem Bank.overlay {all owned scratch : Finset ℕ} {v w : ℕ→ℕ} {s t : BitRAMState}
    (old : Bank all v s) (new : Bank owned w t)
    (separate : Disjoint all scratch) (frame : BinaryPrecision.Frame (owned∪scratch) s t) :
    Bank all (overlay owned w v) t := by
  intro i hi
  by_cases ho : i∈owned
  · simpa only [NatAssign.overlay,ite_eq_left ho] using new i ho
  · have hs : i∉scratch := fun hs=>Finset.disjoint_left.mp separate hi hs
    simpa only [NatAssign.overlay,ite_eq_right ho] using
      RationalAccumulator.word_of_eq (frame.tapes i (by simp [ho,hs])) (old i hi)

theorem overlay_width {all owned : Finset ℕ} {v w : ℕ→ℕ} {B W : ℕ}
    (old : ∀i∈all,(v i).bits.length ≤ B) (new : ∀i∈owned,(w i).bits.length ≤ W) :
    ∀i∈all,(overlay owned w v i).bits.length ≤ max B W := by
  intro i hi
  by_cases ho : i∈owned
  · simpa only [NatAssign.overlay,ite_eq_left ho] using (new i ho).trans (le_max_right B W)
  · simpa only [NatAssign.overlay,ite_eq_right ho] using (old i hi).trans (le_max_left B W)

theorem overlay_outside {owned : Finset ℕ} (v w : ℕ→ℕ) (i : ℕ) (hi : i∉owned) :
    overlay owned w v i=v i := ite_eq_right hi


theorem changes_subset (ids : Finset ℕ) (instructions : List Instruction)
    (hv : ∀a∈instructions,a.Valid ids) : changes instructions⊆{0,1,2,3}∪ids := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Finset.mem_union_left _ hi
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    apply Finset.mem_union_right
    have h := hv a ha
    cases a <;> first | exact h | exact h.2.1

/-- Carry additional scratch words unchanged beside a natural-word stage. -/
theorem executes_scratch (count : ℕ) (hcount : 4 ≤ count) (ids : Finset ℕ)
    (hids : ∀i∈ids,count ≤ i) (instructions : List Instruction)
    (hv : ∀a∈instructions,a.Valid ids) (v : ℕ→ℕ)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : Bank ids v s.val) (hs : ∀i,i<count→RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape (code instructions) cost s t ∧ cost ≤ price instructions v ∧
      Bank ids (values instructions v) t.val ∧ (∀i,i<count→RationalAccumulator.Blank t.val i) ∧
      BinaryPrecision.Frame (changes instructions) s.val t.val := by
  obtain ⟨cost,t,he,hc,bt,st,hf⟩ := executes ids (fun i hi=>hcount.trans (hids i hi))
    instructions hv v input tape s hb (fun i hi=>hs i (by omega))
  refine ⟨cost,t,he,hc,bt,?_,hf⟩
  have full := hf.mono (changes_subset ids instructions hv)
  intro i hi
  by_cases h4 : i<4
  · exact st i h4
  · have hout : i∉ids := fun hin=>by have := hids i hin;omega
    exact RationalAccumulator.blank_of_eq (full.tapes i (by simp [hout];omega)) (hs i hi)

#print axioms Bank.overlay
#print axioms executes_scratch
end Maxwell.Cost.Structured.NatAssign
