import Maxwell.Cost.CalibrationSource.IndexMachine

namespace Maxwell.Cost.CalibrationSource
open Structured

/-- Explicit size growth of every intermediate word in a fixed arithmetic
script. This also bounds the actual cleanup cost of its temporary words. -/
theorem values_width (ids : Finset ℕ) (instructions : List NatAssign.Instruction)
    (hv : ∀ a ∈ instructions, a.Valid ids) (values : ℕ → ℕ) (B : ℕ)
    (hb : ∀ i ∈ ids, (values i).bits.length ≤ B)
    (hc : ∀ a ∈ instructions, a.literalWidth ≤ B) :
    ∀ i ∈ ids, (NatAssign.values instructions values i).bits.length ≤ 2^instructions.length*(B+1) := by
  induction instructions generalizing values B with
  | nil => intro i hi; simpa only [NatAssign.values,List.length_nil,pow_zero,one_mul] using (hb i hi).trans (by omega)
  | cons a rest ih =>
    have h := ih (fun a h => hv a (by simp [h])) (a.update values) (2*B+1)
      (NatAssign.instruction_width ids a (hv a (by simp)) values B hb (hc a (by simp)))
      (fun a h => (hc a (by simp [h])).trans (by omega))
    intro i hi
    have hh := h i hi
    simp only [List.length_cons,pow_succ,NatAssign.values]
    convert hh using 1
    ring

end Maxwell.Cost.CalibrationSource
