import Maxwell.Continuum.NaturalSquareRootMachineCost
import Maxwell.Continuum.RationalSquareRootEvaluation

/-! Literal arithmetic for the existing rational square-root evaluator.
Its numerator and denominator are the canonical rational input channels;
normalization of a raw pair is charged separately. -/

namespace Maxwell.Continuum.Calibration.RationalRoot

open Maxwell.Cost Maxwell.Cost.Structured

def ids : Finset ℕ := NaturalRoot.fullIds∪{542,543,544,548}
def changed : Finset ℕ := NaturalRoot.changed∪{540,548}
def inputValues (A D N : ℕ) (i : ℕ) : ℕ :=
  if i=542 then A else if i=543 then D else if i=544 then N else 0
def powerPlan : List NatAssign.Instruction :=
  [.literal 530 4,.literal 531 2,.copy 544 534]
def powerValues (A D N : ℕ) (i : ℕ) : ℕ :=
  if i=530 then 4 else if i=531 then 2 else if i=532 then 4^N else
    if i=533 then 2^N else inputValues A D N i
def radicandPlan : List NatAssign.Instruction :=
  [.copy 542 540,.multiply 543 540,.multiply 532 540,
   .copy 543 548,.multiply 533 548,
   .literal 530 0,.literal 531 0,.literal 532 0,.literal 533 0,.literal 534 0]
def radicand (A D N : ℕ) : ℕ := A*D*4^N
def preparedValues (A D N : ℕ) (i : ℕ) : ℕ :=
  if i=540 then radicand A D N else if i=548 then D*2^N else inputValues A D N i

theorem ids_ge : ∀ i∈ids, 4 ≤ i := by
  intro i hi
  simp only [ids,NaturalRoot.fullIds,NaturalRoot.ids,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem powerPlan_valid : ∀ a∈powerPlan, a.Valid ids := by
  simp [powerPlan,NatAssign.Instruction.Valid,ids,NaturalRoot.fullIds,NaturalRoot.ids]

theorem radicandPlan_valid : ∀ a∈radicandPlan, a.Valid ids := by
  simp [radicandPlan,NatAssign.Instruction.Valid,ids,NaturalRoot.fullIds,NaturalRoot.ids]

theorem powerPlan_values (A D N : ℕ) (i : ℕ) :
    NatAssign.values powerPlan (inputValues A D N) i=
      (if i=530 then 4 else if i=531 then 2 else if i=534 then N else inputValues A D N i) := by
  by_cases h530 : i=530
  · subst i; simp [powerPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,inputValues]
  by_cases h531 : i=531
  · subst i; simp [powerPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,inputValues]
  by_cases h534 : i=534
  · subst i; simp [powerPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,inputValues]
  simp [powerPlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,inputValues,h530,h531,h534]

theorem radicandPlan_values (A D N : ℕ) :
    NatAssign.values radicandPlan (powerValues A D N)=preparedValues A D N := by
  ext i
  by_cases small : 530 ≤ i ∧ i ≤ 548
  · obtain ⟨hlo,hhi⟩ := small
    interval_cases i <;>
      simp [radicandPlan,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.value,NatAssign.Instruction.target,powerValues,inputValues,
        preparedValues,radicand,Nat.mul_comm,Nat.mul_assoc]
  · have h530 : i≠530 := by omega
    have h531 : i≠531 := by omega
    have h532 : i≠532 := by omega
    have h533 : i≠533 := by omega
    have h534 : i≠534 := by omega
    have h540 : i≠540 := by omega
    have h548 : i≠548 := by omega
    simp [radicandPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,powerValues,
      preparedValues,h530,h531,h532,h533,h534,h540,h548]

theorem radicand_bits (A D N W : ℕ) (hA : A.bits.length≤W) (hD : D.bits.length≤W) :
    (radicand A D N).bits.length≤2*W+3*N+1 := by
  have hp := SelectedParameters.Geometric.power_bits 4 N
  change (4^N).bits.length≤N*3+1 at hp
  have h1 := RationalAccumulator.bits_mul_le A D
  have h2 := RationalAccumulator.bits_mul_le (A*D) (4^N)
  unfold radicand
  omega

theorem literal_value (r : ℚ) (N : ℕ) :
    (Nat.sqrt (radicand r.num.natAbs r.den N):ℚ)/(r.den*2^N)=sqrtRationalCenter r N := by
  have hp : (4:ℕ)^N=2^(2*N) := by rw [pow_mul]; norm_num
  simp only [sqrtRationalCenter,sqrtNaturalCenter,sqrtNaturalWord,radicand,hp]
  rw [div_div]
  congr 1
  ring

#print axioms literal_value

end Maxwell.Continuum.Calibration.RationalRoot
