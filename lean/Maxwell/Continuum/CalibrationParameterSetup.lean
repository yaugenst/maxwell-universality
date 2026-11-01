import Maxwell.Continuum.CalibrationParameterInput

/-! Source-selected operands drive the complete natural calibration setup. -/
namespace Maxwell.Continuum.Calibration.ParameterSetup
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] MasterConstants.exponent MasterConstants.Cs
  RealizationParameters.analysisBits RealizationParameters.inputBits

def code (a b : ℕ) : Code := .seq (NatAssign.code (ParameterInput.instructions a b)) ParameterMachine.code
def inputValues (a b : ℕ) (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values (ParameterInput.instructions a b) v
def values (a b : ℕ) (v : ℕ→ℕ) : ℕ→ℕ := ParameterMachine.values (inputValues a b v)
def width (a b B : ℕ) : ℕ := max (ParameterInput.width a b B)
  (ParameterMachine.width (ParameterInput.width a b B))
def costBound (a b B : ℕ) : ℕ := ParameterInput.costBound a b B+
  ParameterMachine.costBound (ParameterInput.width a b B)

theorem machine_budget (v : ℕ→ℕ) (i : ℕ) (hi : 4425 ≤ i ∧ i ≤ 4429) :
    ParameterMachine.values v i=v i := by
  have keep (xs : List NatAssign.Instruction)
      (h : ∀q∈xs,q.target<4425 ∨ 4429<q.target) (w : ℕ→ℕ) :
      NatAssign.values xs w i=w i := by
    apply NatAssign.values_preserves
    intro q hq
    have := h q hq
    omega
  rw [ParameterMachine.values,keep _ (by decide +kernel)]
  rw [ParameterMachine.sizeMeasured,Function.update_of_ne (by omega : i≠4410)]
  rw [ParameterMachine.sized,keep _ (by decide +kernel)]
  rw [ParameterMachine.measured,Function.update_of_ne (by omega : i≠4407),
    Function.update_of_ne (by omega : i≠4404)]
  rw [ParameterMachine.prepared,keep _ (by decide +kernel)]

theorem machine_outside (v : ℕ→ℕ) (i : ℕ) (hi : i∉ParameterMachine.ids) :
    ParameterMachine.values v i=v i := by
  have h4 : i≠4404 := fun h=>hi (h ▸ (by decide))
  have h7 : i≠4407 := fun h=>hi (h ▸ (by decide))
  have h10 : i≠4410 := fun h=>hi (h ▸ (by decide))
  rw [ParameterMachine.values,NatAssign.values_outside _ _ ParameterMachine.valid_finish _ _ hi]
  rw [ParameterMachine.sizeMeasured,Function.update_of_ne h10]
  rw [ParameterMachine.sized,NatAssign.values_outside _ _ ParameterMachine.valid_size _ _ hi]
  rw [ParameterMachine.measured,Function.update_of_ne h7,Function.update_of_ne h4]
  rw [ParameterMachine.prepared,NatAssign.values_outside _ _ ParameterMachine.valid_prepare _ _ hi]

theorem executes (a b : ℕ) (v : ℕ→ℕ) (B : ℕ)
    (hw : ∀i∈ParameterInput.ids,(v i).bits.length≤B)
    (hC : v 2210=2^MasterConstants.exponent)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ParameterInput.ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (code a b) cost s t ∧ cost≤costBound a b B ∧
      NatAssign.Bank ParameterInput.ids (values a b v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ParameterInput.ids,(values a b v i).bits.length≤width a b B) ∧
      ParameterMachine.Outputs (v 2221) (couplingRadius (v 2221) (v 2227))
        (a*v 2200+4*v 2227+6*v 2206+18) (values a b v) ∧
      BinaryPrecision.Frame ParameterInput.workspace s.val t.val := by
  obtain ⟨c0,u,e0,h0,bu,su,wu,f0⟩ := ParameterInput.executes a b v B hw input tape s bank scratch
  have hp := ParameterInput.fields a b v
  dsimp only at hp
  have master : inputValues a b v 4403=2^(4*MasterConstants.exponent) := by
    rw [inputValues,hp.2.2.2.1,hC,←pow_mul,Nat.mul_comm]
  obtain ⟨c1,t,e1,h1,bt,st,wt,outputs,frame⟩ := ParameterMachine.executes (inputValues a b v)
    (ParameterInput.width a b B) (fun i hi=>wu i (Finset.mem_union_left _ hi)) master input tape u
    (fun i hi=>bu i (Finset.mem_union_left _ hi)) su
  have finalBank : NatAssign.Bank ParameterInput.ids (values a b v) t.val := by
    intro i hi
    by_cases hm : i∈ParameterMachine.ids
    · exact bt i hm
    · rw [values,machine_outside _ i hm]
      have hi4 : 4 ≤ i := by
        simp only [ParameterInput.ids,ParameterMachine.ids,Finset.mem_union,Finset.mem_Icc,
          Finset.mem_insert,Finset.mem_singleton] at hi
        omega
      exact RationalAccumulator.word_of_eq (frame.tapes i (by
        simp only [ParameterMachine.workspace,Finset.mem_union,not_or]
        exact ⟨by simp;omega,hm⟩)) (bu i hi)
  have finalWidth : ∀i∈ParameterInput.ids,(values a b v i).bits.length≤width a b B := by
    intro i hi
    by_cases hm : i∈ParameterMachine.ids
    · exact (wt i hm).trans (le_max_right _ _)
    · rw [values,machine_outside _ i hm]
      exact (wu i hi).trans (le_max_left _ _)
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,finalBank,st,finalWidth,?_,f0.trans frame⟩
  have hL : inputValues a b v 4400=v 2221 := hp.1
  have hr : inputValues a b v 4401=couplingRadius (v 2221) (v 2227) := hp.2.1
  have hN : inputValues a b v 4402=a*v 2200+4*v 2227+6*v 2206+18 := hp.2.2.1
  simpa only [values,hL,hr,hN] using outputs

#print axioms executes
end Maxwell.Continuum.Calibration.ParameterSetup
