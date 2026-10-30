import Maxwell.Continuum.CalibrationForcingEmission
import Maxwell.Continuum.CalibrationNeumannPaddedTable

/-! All three table-loop lengths are computed from the runtime Fourier
radius by fixed natural arithmetic, rather than supplied as counters. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def aliasCountPlan : List NatAssign.Instruction := prepare++[.copy 314 332,.multiply 313 332]
def matrixCountPlan : List NatAssign.Instruction :=
  aliasCountPlan++[.multiply 312 332,.copy 332 331,.multiply 331 332]
def paddedCountPlan : List NatAssign.Instruction := matrixCountPlan++[.add 331 332,.add 331 332]
def countTargets : Finset ℕ := {312,313,314,331,332}
def countWidth (B : ℕ) : ℕ := 2^13*(B+1)

theorem nat_values_append (a b : List NatAssign.Instruction) (n : ℕ→ℕ) :
    NatAssign.values (a++b) n=NatAssign.values b (NatAssign.values a n) := by
  induction a generalizing n with
  | nil => rfl
  | cons i rest ih => exact ih (i.update n)

theorem aliasCount_value (n : ℕ→ℕ) : NatAssign.values aliasCountPlan n 332=aliasRowCount (n 311) := by
  rw [aliasCountPlan,nat_values_append]
  change NatAssign.values [.copy 314 332,.multiply 313 332] (prepared n) 332=_
  simp only [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update_self,Function.update_of_ne (by decide : (313:ℕ)≠332),
    prepared_side,prepared_square,aliasRowCount]

theorem aliasCount_three (n : ℕ→ℕ) : NatAssign.values aliasCountPlan n 312=3 := by
  simp [aliasCountPlan,prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value]

theorem matrixCount_values (n : ℕ→ℕ) :
    NatAssign.values matrixCountPlan n 331=aliasArraySize (n 311) ∧
      NatAssign.values matrixCountPlan n 332=aliasArraySize (n 311)*aliasArraySize (n 311) := by
  rw [matrixCountPlan,nat_values_append]
  simp only [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update_self,Function.update_of_ne (by decide : (332:ℕ)≠331),
    Function.update_of_ne (by decide : (331:ℕ)≠332),aliasCount_value,aliasCount_three]
  have hn : 3*aliasRowCount (n 311)=aliasArraySize (n 311) := by
    unfold aliasRowCount aliasArraySize
    omega
  simp only [hn]
  exact ⟨trivial,trivial⟩

theorem paddedCount_value (n : ℕ→ℕ) :
    NatAssign.values paddedCountPlan n 332=NeumannMachine.tableSize (aliasArraySize (n 311)) := by
  rw [paddedCountPlan,nat_values_append]
  simp only [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update_self,Function.update_of_ne (by decide : (331:ℕ)≠332),
    (matrixCount_values n).1,(matrixCount_values n).2,NeumannMachine.tableSize]
  omega

theorem countPlans_valid (plan : List NatAssign.Instruction)
    (h : plan=aliasCountPlan ∨ plan=matrixCountPlan ∨ plan=paddedCountPlan) :
    (∀ a∈plan, a.Valid emissionIds) ∧ (∀ a∈plan, a.target∈countTargets) ∧ plan.length≤13 := by
  rcases h with rfl | rfl | rfl <;>
    simp [aliasCountPlan,matrixCountPlan,paddedCountPlan,prepare,NatAssign.Instruction.Valid,
      NatAssign.Instruction.target,emissionIds,countTargets]

theorem countPlans_literals (plan : List NatAssign.Instruction)
    (h : plan=aliasCountPlan ∨ plan=matrixCountPlan ∨ plan=paddedCountPlan) (B : ℕ) (hB : 2≤B) :
    ∀ a∈plan, a.literalWidth≤B := by
  rcases h with rfl | rfl | rfl <;>
    simp [aliasCountPlan,matrixCountPlan,paddedCountPlan,prepare,NatAssign.Instruction.literalWidth,
      show (3:ℕ).bits.length=2 by decide] <;> omega

theorem nat_values_keep (plan : List NatAssign.Instruction) (n : ℕ→ℕ) (k : ℕ)
    (hk : ∀ a∈plan, k≠a.target) : NatAssign.values plan n k=n k := by
  induction plan generalizing n with
  | nil => rfl
  | cons a rest ih =>
    rw [NatAssign.values,ih _ (fun x hx => hk x (by simp [hx])),NatAssign.Instruction.update,
      Function.update_of_ne (hk a (by simp))]

theorem countPlans_keep (plan : List NatAssign.Instruction)
    (h : plan=aliasCountPlan ∨ plan=matrixCountPlan ∨ plan=paddedCountPlan) (n : ℕ→ℕ)
    (k : ℕ) (hk : k∉countTargets) : NatAssign.values plan n k=n k := by
  apply nat_values_keep
  intro a ha he
  exact hk (he ▸ (countPlans_valid plan h).2.1 a ha)

theorem countPlans_agrees (plan : List NatAssign.Instruction)
    (h : plan=aliasCountPlan ∨ plan=matrixCountPlan ∨ plan=paddedCountPlan) (n : ℕ→ℕ) (v : ℕ→Parts)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k) :
    ∀ k∈ids RawFree.neighborRegisters, NatAssign.values plan n k=dataValues v k := by
  intro k hk
  have hd : Disjoint countTargets (ids RawFree.neighborRegisters) := by decide
  rw [countPlans_keep plan h n k (fun hmem => Finset.disjoint_left.mp hd hmem hk),hn k hk]

theorem countPlans_width (plan : List NatAssign.Instruction)
    (h : plan=aliasCountPlan ∨ plan=matrixCountPlan ∨ plan=paddedCountPlan) (n : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤B) :
    ∀ k∈emissionIds, (NatAssign.values plan n k).bits.length≤countWidth B := by
  have hp := countPlans_valid plan h
  have hbound := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hp.2.2
  intro k hk
  exact (nat_values_width emissionIds plan hp.1 n B hw (countPlans_literals plan h B hB) k hk).trans
    (Nat.mul_le_mul_right (B+1) hbound)

#print axioms aliasCount_value
#print axioms matrixCount_values
#print axioms paddedCount_value

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
