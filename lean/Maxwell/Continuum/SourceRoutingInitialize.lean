import Maxwell.Continuum.SourceRoutingInitializeRename
import Maxwell.Continuum.SourceRoutingOperations

/-! Fill either actual routing array with its sentinel, from arbitrary
memory. The public source-graph banks survive the fixed relocated program. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Initialize
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def work : Finset ℕ := {37,730,732,739}
def base {n : ℕ} (l : Layout n) (backward : Bool) : ℕ := if backward then l.backward else l.forward

theorem frame_renamed (backward : Bool) {s u : Store}
    (hf : PositiveGraph.Initialize.Frame (s.renameTapes (relocation backward).symm).val u.val) :
    Frame work s.val (u.renameTapes (relocation backward)).val := by
  refine ⟨hf.inputHead,hf.randomCursor,hf.output,?_,hf.registers⟩
  intro i hi hw
  have bound : shift backward i=4 ∨ 10 ≤ shift backward i := by
    rcases hi with rfl|hi
    · left
      exact shift_small backward 4 (by decide)
    · exact Or.inr (shift_large backward i hi)
  have not_shift (k : ℕ) (hk : i≠shift backward k) : shift backward i≠k := by
    intro he
    have := congrArg (shift backward) he
    rw [shift_involutive] at this
    exact hk this
  have hn (k : ℕ) (hk : k=37 ∨ k=160 ∨ k=161 ∨ k=162) : shift backward i≠k := by
    apply not_shift
    rcases hk with rfl|rfl|rfl|rfl
    all_goals
      cases backward <;>
        simp only [work,Finset.mem_insert,Finset.mem_singleton,not_or] at hw
      all_goals norm_num [shift,baseBank]
      all_goals omega
  have h := hf.tapes (shift backward i) bound (hn 37 (by simp))
    (hn 160 (by simp)) (hn 161 (by simp)) (hn 162 (by simp))
  change u.val.tapes (shift backward i)=s.val.tapes i
  simpa only [renamed_tape_symm,shift_involutive backward i] using h

theorem fill_array {n : ℕ} (l : Layout n) (backward : Bool)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready s.val) (hm : Metadata l s.val)
    (h730 : Blank s.val 730) (h732 : Blank s.val 732)
    (h739 : RationalAccumulator.Word s.val 739 n) :
    ∃cost t, Executes input tape (fillCode backward) cost s t ∧
      cost≤PositiveGraph.Initialize.fillCost n (scale l)+1 ∧
      Ready t.val ∧ Metadata l t.val ∧ Blank t.val 730 ∧ Blank t.val 732 ∧
      RationalAccumulator.Word t.val 739 n ∧
      BitArray.Represents t.val.memory (base l backward) n.bits.length (encode (Vector.replicate n n)) ∧
      PositiveGraph.Initialize.Outside (base l backward) n.bits.length n s.val t.val ∧
      Frame work s.val t.val := by
  let v := s.renameTapes (relocation backward).symm
  have hv : PositiveGraph.Initialize.Ready ports n.bits.length.bits (base l backward).bits l.clock n v.val := by
    constructor
    · cases backward <;> exact hs.scratch
    · cases backward <;> exact hs.seven
    · cases backward <;> exact hs.pack
    · cases backward <;> exact hm.width
    · cases backward
      · exact hm.forward
      · exact hm.backward
    · cases backward <;> exact hm.clock
    · cases backward <;> exact h739
  have h160 : Blank v.val 160 := by cases backward <;> exact h730
  have h161 : Blank v.val 161 := by cases backward <;> exact h732
  have hcount : RationalAccumulator.Word v.val ports.count n := by cases backward <;> exact hm.count
  have hw : n.bits.length.bits.length≤scale l := by
    have := natural_bits_length_le n.bits.length
    unfold scale
    omega
  have hb : (base l backward).bits.length≤scale l := by
    cases backward <;> simp only [base,Bool.false_eq_true,↓reduceIte] <;> unfold scale <;> omega
  have hn : n.bits.length≤scale l := by unfold scale; omega
  have hp : 0<n.bits.length := RationalAccumulator.bits_nonempty l.positive
  have hwp : 0<n.bits.length.bits.length := RationalAccumulator.bits_nonempty hp
  have hroom : n<2^scale l := by
    have hh : n<2^n.bits.length := by simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self n
    exact hh.trans_le (Nat.pow_le_pow_right (by decide) hn)
  obtain ⟨cost,u,hcost,eu,hu,hu160,hu161,harray,houtside,hframe⟩ :=
    PositiveGraph.Initialize.fill_executes ports n.bits.length.bits (base l backward).bits l.clock
      n n (scale l) hw hb hn hwp (by simpa only [addressValue_bits] using hp)
      (by simpa only [addressValue_bits] using hn) (by simpa only [addressValue_bits] using l.clock_length)
      (by simp only [addressValue_bits]; exact le_rfl) hroom input tape v hv h160 h161 hcount
  let t := u.renameTapes (relocation backward)
  have hf : Frame work s.val t.val := frame_renamed backward hframe
  have tr : Ready t.val := by
    refine ⟨?_,?_,?_,RationalAccumulator.blank_of_eq (hf.tapes 752 (by decide) (by decide)) hs.probe⟩
    · cases backward <;> exact hu.scratch
    · cases backward <;> exact hu.seven
    · cases backward <;> exact hu.temporary
  refine ⟨cost+1,t,?_,by omega,tr,
    hm.frame hf (by intro i hi; simp only [work,Finset.mem_insert,Finset.mem_singleton] at hi; omega),
    ?_,?_,?_,?_,?_,hf⟩
  · simpa only [fillCode,v,Store.renameTapes_symm] using eu.renamed_call (relocation backward)
  · cases backward <;> exact hu160
  · cases backward <;> exact hu161
  · cases backward <;> exact hu.valueWord
  · simp only [addressValue_bits] at harray
    change BitArray.Represents u.val.memory (base l backward) n.bits.length (encode (Vector.replicate n n))
    have he : encode (Vector.replicate n n)=
        Vector.ofFn (fun _ : Fin n => FixedWidth.bits n.bits.length n.bits) := by
      apply Vector.ext
      intro i hi
      simp [encode]
    rw [he]
    exact harray
  · intro a ha
    exact houtside a (by simpa only [addressValue_bits] using ha)

#print axioms fill_array

end Maxwell.Cost.RoutingPorts.Complete.Initialize
