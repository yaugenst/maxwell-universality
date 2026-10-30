import Maxwell.Continuum.NaturalSquareRootMachine

/-! Complete polynomial bit cost for the fixed integer square-root program. -/

namespace Maxwell.Continuum.Calibration.NaturalRoot

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word)
set_option maxHeartbeats 2500000

theorem loopCost_polynomial (T : ℕ) :
    DyadicSqrt.loopBudget T (4^T.bits.length) T.bits.length≤
      (T.bits.length+1)*(14000000000*(6*T.bits.length+6)^2+250*(T.bits.length+5)) := by
  have hp := SelectedParameters.Geometric.power_bits 4 T.bits.length
  change (4^T.bits.length).bits.length≤T.bits.length*3+1 at hp
  have h := DyadicSqrt.upperBudget_le_polynomial T (4^T.bits.length) T.bits.length
  have hl : DyadicSqrt.loopBudget T (4^T.bits.length) T.bits.length≤
      DyadicSqrt.upperBudget T (4^T.bits.length) T.bits.length := by
    unfold DyadicSqrt.upperBudget
    omega
  apply (hl.trans h).trans
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left (by omega) 2

theorem costBound_polynomial (T : ℕ) : costBound T≤2^64*(T.bits.length+6)^5 := by
  have hp := powerCost_polynomial T.bits.length
  have hl := loopCost_polynomial T
  have hk := length_width T
  unfold costBound
  calc
    _ ≤ 2^32*(T.bits.length+6)^5+3000*8^5*(3*T.bits.length+6)^2+
        ((T.bits.length+1)*(14000000000*(6*T.bits.length+6)^2+250*(T.bits.length+5))+
          6*T.bits.length+4) := by omega
    _ ≤ _ := by ring_nf; omega

theorem compiled_run (T : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank fullIds (inputValues T) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (2^64*(T.bits.length+6)^5+1) s.val).finished=
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (2^64*(T.bits.length+6)^5+1) s.val).instructions≤
        2^64*(T.bits.length+6)^5 ∧
      Word t.val 32 (Nat.sqrt T) ∧ NatAssign.Bank fullIds (doneValues T) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨cost,t,run,hcost,out⟩ := executes T input tape s hs hz
  have bound := hcost.trans (costBound_polynomial T)
  have hr := run.compiled_run (2^64*(T.bits.length+6)^5+1) (by omega)
  exact ⟨t,hr.1,hr.2 ▸ bound,out⟩

#print axioms compiled_run

end Maxwell.Continuum.Calibration.NaturalRoot
