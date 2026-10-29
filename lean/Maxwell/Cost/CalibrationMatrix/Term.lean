import Maxwell.Cost.CalibrationMatrix.ReadOperand
import Maxwell.Cost.RationalAccumulator.Reset

namespace Maxwell.Cost.CalibrationMatrix

set_option maxHeartbeats 600000

open Structured RationalAccumulator

def clearOperandsCode : Code := .seq (.call (TapeOps.clear 32))
  (.seq (.call (TapeOps.clear 33)) (.seq (.call (TapeOps.clear 34)) (.call (TapeOps.clear 35))))

def clearOperands (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update v 32 0) 33 0) 34 0) 35 0

theorem clear_operands (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ t : Store, Executes input tape clearOperandsCode
      (6*((v 32).bits.length+(v 33).bits.length+(v 34).bits.length+(v 35).bits.length)+16) s t ∧
      Bank t.val (clearOperands v) ∧ Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  obtain ⟨a, ha, hab, har, haf⟩ := clear_bank 32 (by omega) (by omega) input tape v 0 s hbank hready
  obtain ⟨b, hb, hbb, hbr, hbf⟩ := clear_bank 33 (by omega) (by omega)
    input tape (Function.update v 32 0) 0 a hab har
  obtain ⟨c, hc, hcb, hcr, hcf⟩ := clear_bank 34 (by omega) (by omega)
    input tape (Function.update (Function.update v 32 0) 33 0) 0 b hbb hbr
  obtain ⟨t, ht, htb, htr, htf⟩ := clear_bank 35 (by omega) (by omega)
    input tape (Function.update (Function.update (Function.update v 32 0) 33 0) 34 0) 0 c hcb hcr
  refine ⟨t, ?_, htb, htr, ((haf.trans hbf).trans hcf).trans htf⟩
  have he := ha.seq (hb.seq (hc.seq ht))
  norm_num [Function.update_apply] at he
  convert he using 1 <;> first | rfl | omega

def termCode : Code := .seq signedMacCode clearOperandsCode

def dotValues (positive negative : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (fun _ => 0) 30 positive) 31 negative

def termValues (positive negative ap an xp xn : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update
    (dotValues positive negative) 32 ap) 33 an) 34 xp) 35 xn

/-- Four genuine products implement one signed dot-product term. Clearing
the four loaded operands makes the same fixed routine reusable next time. -/
theorem term (input : List Bool) (tape : ℕ → Bool)
    (positive negative ap an xp xn B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 35 → (termValues positive negative ap an xp xn i).bits.length ≤ B)
    (s : Store) (hready : Ready s.val (termValues positive negative ap an xp xn)) :
    ∃ cost, ∃ t : Store, cost ≤ 410000*(B+2)^2 ∧ Executes input tape termCode cost s t ∧
      Ready t.val (dotValues (positive+ap*xp+an*xn) (negative+ap*xn+an*xp)) ∧ StepFrame s.val t.val := by
  let v := termValues positive negative ap an xp xn
  obtain ⟨acost, a, hacost, ha, hab, har, haf⟩ := signed_mac input tape v B hbits s
    hready.1 hready.arithmetic (by simp [v, termValues, dotValues])
  obtain ⟨t, ht, htb, htr, htf⟩ := clear_operands input tape (signedAccumulated v) a hab har
  have hvalues : clearOperands (signedAccumulated v) =
      dotValues (positive+ap*xp+an*xn) (negative+ap*xn+an*xp) := by
    funext i
    by_cases hi : i < 30 ∨ 35 < i
    · simp [clearOperands, signedAccumulated, v, termValues, dotValues,
        show i ≠ 30 by omega, show i ≠ 31 by omega, show i ≠ 32 by omega,
        show i ≠ 33 by omega, show i ≠ 34 by omega, show i ≠ 35 by omega]
    · have h30 : 30 ≤ i := by omega
      have h35 : i ≤ 35 := by omega
      interval_cases i <;> simp [clearOperands, signedAccumulated, v, termValues, dotValues]
  refine ⟨acost+(6*(ap.bits.length+an.bits.length+xp.bits.length+xn.bits.length)+16), t,
    ?_, ?_, ?_, (stepFrame_of_arithmetic haf).trans (stepFrame_of_arithmetic htf)⟩
  · have h32 := hbits 32 (by omega) (by omega)
    have h33 := hbits 33 (by omega) (by omega)
    have h34 := hbits 34 (by omega) (by omega)
    have h35 := hbits 35 (by omega) (by omega)
    simp [termValues] at h32 h33 h34 h35
    nlinarith
  · simpa [termCode, signedAccumulated, v, termValues] using ha.seq ht
  · exact hvalues ▸ ready_of_arithmetic (ready_of_arithmetic hready hab har haf) htb htr htf

end Maxwell.Cost.CalibrationMatrix
