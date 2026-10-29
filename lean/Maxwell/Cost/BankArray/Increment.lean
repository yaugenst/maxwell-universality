import Maxwell.Cost.BankArray.Common
import Maxwell.Cost.Increment
import Maxwell.Cost.FixedWidth

namespace Maxwell.Cost.BankArray
open Structured

def incrementCode (bank : ℕ) : Code :=
  .seq (.call (Increment.program bank)) (.call (Rewind.program bank))

/-- Increment the actual stored bank word, preserving all other tape cells
and returning the changed word to its first cell. -/
theorem increment_bank (bank : ℕ) (hbank : 10 ≤ bank)
    (input : List Bool) (randomTape : ℕ → Bool) (bits : List Bool) (s : Store)
    (hw : Word s.val bank bits) (hscratch : Scratch s.val) :
    ∃ cost, ∃ t : Store, cost ≤ 12*bits.length+18 ∧
      Executes input randomTape (incrementCode bank) cost s t ∧
      Word t.val bank (Increment.bits bits) ∧ Scratch t.val ∧
      t.val.memory = s.val.memory ∧ t.val.address = s.val.address ∧
      (∀ i, i ≠ bank → t.val.tapes i = s.val.tapes i) ∧ FrameExcept bank s.val t.val := by
  obtain ⟨origin,ho⟩ := hw
  obtain ⟨icost,i,hicost,hi,hip,hiw,hif⟩ := Increment.simulation bank input randomTape bits origin s.val s.property ho
  let iS := Store.ofState i
  have ei : Executes input randomTape (.call (Increment.program bank)) (icost+1) s iS :=
    .call _ _ _ _ hi (by rw [hip]; rfl)
  have hr := WordTransfer.rewind_shifted bank origin input randomTape (Increment.bits bits) iS.val iS.property hiw
  let r := Rewind.finishAt bank origin iS.val
  let rS := Store.ofState r
  have er : Executes input randomTape (.call (Rewind.program bank))
      (4*(Increment.bits bits).length+6) iS rS := .call _ _ _ _ hr.1 rfl
  have rf : WordTransfer.Frame bank bank iS.val rS.val :=
    WordTransfer.frame_rewind bank bank bank (Or.inl rfl) origin iS.val
  have keep (j : ℕ) (hj : j ≠ bank) : rS.val.tapes j = s.val.tapes j :=
    (rf.2.2.2.2.2.1 j hj hj).trans (hif.2.2.2.2.2.1 j hj)
  refine ⟨_,rS,?_,ei.seq er,⟨origin,hr.2⟩,?_,rf.2.2.1.trans hif.2.2.1,
    rf.1.trans hif.1,keep,?_⟩
  · have hlen := Increment.bits_length_le bits
    omega
  · rcases hscratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by omega)) h0,
      RationalAccumulator.blank_of_eq (keep 1 (by omega)) h1,
      RationalAccumulator.blank_of_eq (keep 2 (by omega)) h2,
      RationalAccumulator.blank_of_eq (keep 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by omega)) h9⟩
  · exact ⟨rf.2.1.trans hif.2.1,rf.2.2.2.1.trans hif.2.2.2.1,rf.2.2.2.2.1.trans hif.2.2.2.2.1,
      fun j _ hj => keep j hj,fun j _ h24 h25 h26 h27 h28 h29 =>
        (rf.2.2.2.2.2.2 j h24 h25 h26 h27).trans (hif.2.2.2.2.2.2 j h26 h27 h28 h29)⟩

private theorem carry_length_bound (carry : Bool) (word : List Bool) (B : ℕ)
    (hw : word.length ≤ B) (hv : addressValue word+carry.toNat < 2^B) :
    (Increment.carryBits carry word).length ≤ B := by
  induction word generalizing carry B with
  | nil =>
    cases B with
    | zero => cases carry <;> simp_all [Increment.carryBits,addressValue]
    | succ B => cases carry <;> simp [Increment.carryBits]
  | cons a word ih =>
    cases B with
    | zero => simp at hw
    | succ B =>
      have ht : word.length ≤ B := by simpa using hw
      have hval : addressValue word+(a && carry).toNat < 2^B := by
        cases a <;> cases carry <;> simp_all [addressValue,pow_succ] <;> omega
      simpa [Increment.carryBits] using Nat.add_le_add_right (ih (a && carry) B ht hval) 1

theorem increment_length_bound (word : List Bool) (B : ℕ)
    (hw : word.length ≤ B) (hv : addressValue word+1 < 2^B) :
    (Increment.bits word).length ≤ B := by
  simpa [Increment.bits] using carry_length_bound true word B hw hv

theorem increment_two_bits (r : ℕ) (hr : r < 3) :
    Increment.bits (FixedWidth.bits 2 r.bits) = FixedWidth.bits 2 (r+1).bits := by
  interval_cases r <;> rfl

theorem increment_run (bank : ℕ) (hbank : 10 ≤ bank)
    (input : List Bool) (randomTape : ℕ → Bool) (bits : List Bool) (s : Store)
    (hw : Word s.val bank bits) (hscratch : Scratch s.val) :
    ∃ t : Store,
      (runPriced ((incrementCode bank).compile.next input randomTape) (12*bits.length+19) s.val).finished =
        some (t.place (incrementCode bank).size) ∧
      (runPriced ((incrementCode bank).compile.next input randomTape) (12*bits.length+19) s.val).instructions ≤
        12*bits.length+18 ∧
      Word t.val bank (Increment.bits bits) ∧ Scratch t.val ∧
      t.val.memory = s.val.memory ∧ t.val.address = s.val.address ∧
      (∀ i, i ≠ bank → t.val.tapes i = s.val.tapes i) ∧ FrameExcept bank s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := increment_bank bank hbank input randomTape bits s hw hscratch
  have hr := he.compiled_run (12*bits.length+19) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.BankArray
