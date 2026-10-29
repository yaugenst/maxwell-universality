import Maxwell.Cost.Structured.NatAssign.Bounds

/-! Split the exact RHS parser's sign/magnitude into two natural numerator
parts. The actual branch reads register360 and preserves the parsed words. -/
namespace Maxwell.Cost.PhysicalSource.SourceSign
open Structured RationalAccumulator
set_option maxHeartbeats 1000000

def ids : Finset ℕ := {360,366,367}
def negativeInstructions : List NatAssign.Instruction := [.literal 366 0,.copy 360 367]
def positiveInstructions : List NatAssign.Instruction := [.copy 360 366,.literal 367 0]
def code : Code := .branch 360 (NatAssign.code negativeInstructions) (NatAssign.code positiveInstructions)
def instructions (negative : Bool) : List NatAssign.Instruction :=
  if negative then negativeInstructions else positiveInstructions

theorem valid (negative : Bool) : ∀ a ∈ instructions negative, a.Valid ids := by
  intro a ha
  cases negative <;> simp [instructions,negativeInstructions,positiveInstructions] at ha <;>
    rcases ha with rfl|rfl <;> norm_num [NatAssign.Instruction.Valid,ids]

theorem positive_value (negative : Bool) (v : ℕ→ℕ) :
    NatAssign.values (instructions negative) v 366 = if negative then 0 else v 360 := by
  cases negative <;> simp [instructions,positiveInstructions,negativeInstructions,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update]

theorem negative_value (negative : Bool) (v : ℕ→ℕ) :
    NatAssign.values (instructions negative) v 367 = if negative then v 360 else 0 := by
  cases negative <;> simp [instructions,positiveInstructions,negativeInstructions,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update]

theorem executes (negative : Bool) (v : ℕ→ℕ) (B : ℕ)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hr : NatAssign.Scratch s.val)
    (hv : ∀ i ∈ ids, (v i).bits.length≤B) (hsign : s.val.registers 360=negative) :
    ∃ cost t, cost≤3000*8^2*(B+2)^2+1 ∧ Executes input tape code cost s t ∧
      Word t.val 366 (if negative then 0 else v 360) ∧
      Word t.val 367 (if negative then v 360 else 0) ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame {0,1,2,3,366,367} s.val t.val := by
  obtain ⟨c,t,he,hc,ht,hs,hf⟩ := NatAssign.executes ids
    (by intro i hi; simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega)
    (instructions negative) (valid negative) v input tape s hb hr
  have hp : c≤3000*8^2*(B+2)^2 := hc.trans (by
    have hl : ∀ a ∈ instructions negative, a.literalWidth≤B := by
      intro a ha
      cases negative <;> simp [instructions,negativeInstructions,positiveInstructions] at ha <;>
        rcases ha with rfl|rfl <;> exact Nat.zero_le _
    have hlen : (instructions negative).length=2 := by cases negative <;> rfl
    simpa only [hlen] using
      NatAssign.price_bound ids (instructions negative) (valid negative) v B hv hl)
  refine ⟨1+c,t,by omega,?_,by simpa only [positive_value] using ht 366 (by decide),
    by simpa only [negative_value] using ht 367 (by decide),hs,?_⟩
  · cases negative
    · exact Executes.no hsign he
    · exact Executes.yes hsign he
  · have hh : NatAssign.changes (instructions negative) = {0,1,2,3,366,367} := by
      cases negative <;> decide
    rw [hh] at hf
    exact hf

end Maxwell.Cost.PhysicalSource.SourceSign
