import Maxwell.Continuum.CalibrationRootParameterData
import Maxwell.Continuum.NaturalBankQuotient
import Maxwell.Continuum.NatAssignOutputWidth
import Maxwell.Cost.PhysicalMaterial.FixedSubtract

/-! Fixed natural-word instructions for the root degree and sampling data. -/
namespace Maxwell.Continuum.Calibration.RootParameters
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000
attribute [local irreducible] MasterConstants.exponent
local notation "multiplier" => (2^(3*MasterConstants.exponent):ℕ)

def ids : Finset ℕ := NaturalQuotient.workPorts∪Finset.Icc 330 349∪{640}
def workspace : Finset ℕ := {0,1,2,3,4}∪ids

def preparation (M : ℕ) : List NatAssign.Instruction :=
  [.literal 336 2,.add 333 336,.add 334 336,.copy 336 337,.multiply 336 337,
   .copy 330 338,.multiply 337 338,.literal 339 M,.multiply 339 338,.add 332 338]
def prepare : List NatAssign.Instruction := preparation multiplier
def gridPlan : List NatAssign.Instruction :=
  [.copy 335 336,.literal 339 2,.multiply 339 336,.copy 336 331,
   .literal 339 1,.add 339 331,.literal 340 0]
def precisionPlan : List NatAssign.Instruction :=
  [.copy 340 640,.literal 339 3,.multiply 339 640,.add 333 640,.literal 339 8,.add 339 640]

def prepared (v : ℕ→ℕ) := NatAssign.values prepare v
def decremented (v : ℕ→ℕ) := Function.update (prepared v) 338 (prepared v 338-1)
def divided (v : ℕ→ℕ) := Function.update (decremented v) 335 (decremented v 338/decremented v 332)
def gridded (v : ℕ→ℕ) := NatAssign.values gridPlan (divided v)
def measured (v : ℕ→ℕ) := Function.update (gridded v) 340 (gridded v 336).bits.length
def values (v : ℕ→ℕ) := NatAssign.values precisionPlan (measured v)

theorem ids_lower (i : ℕ) (hi : i ∈ ids) : 10 ≤ i := by
  simp only [ids,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem prepare_valid : ∀a∈prepare,a.Valid ids := by
  simp [prepare,preparation,NatAssign.Instruction.Valid,ids]
theorem gridPlan_valid : ∀a∈gridPlan,a.Valid ids := by
  simp [gridPlan,NatAssign.Instruction.Valid,ids]
theorem precisionPlan_valid : ∀a∈precisionPlan,a.Valid ids := by
  simp [precisionPlan,NatAssign.Instruction.Valid,ids]

theorem prepare_length : prepare.length=10 := rfl
theorem gridPlan_length : gridPlan.length=7 := rfl
theorem precisionPlan_length : precisionPlan.length=6 := rfl

private theorem power_width (e : ℕ) : (2^e:ℕ).bits.length=e+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_pow]

theorem multiplier_width : (multiplier).bits.length=3*MasterConstants.exponent+1 :=
  power_width (3*MasterConstants.exponent)

theorem prepare_literals (B : ℕ) (hB : 3*MasterConstants.exponent+2≤B) :
    ∀a∈prepare,a.literalWidth≤B := by
  simp only [prepare,preparation,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    NatAssign.Instruction.literalWidth,multiplier_width,show (2:ℕ).bits.length=2 by rfl]
  omega

theorem gridPlan_literals (B : ℕ) (hB : 2≤B) : ∀a∈gridPlan,a.literalWidth≤B := by
  simp only [gridPlan,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    NatAssign.Instruction.literalWidth,show (2:ℕ).bits.length=2 by rfl,
    show (1:ℕ).bits.length=1 by rfl,show (0:ℕ).bits.length=0 by rfl]
  omega

theorem precisionPlan_literals (B : ℕ) (hB : 4≤B) : ∀a∈precisionPlan,a.literalWidth≤B := by
  simp only [precisionPlan,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    NatAssign.Instruction.literalWidth,show (3:ℕ).bits.length=2 by rfl,
    show (8:ℕ).bits.length=4 by rfl]
  omega

private theorem preparation_output (M : ℕ) (v : ℕ→ℕ) :
    NatAssign.values (preparation M) v 338=M*v 330*(v 333+v 334+2)^2+v 332 := by
  simp [preparation,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]
  ring

theorem prepared_numerator (v : ℕ→ℕ) :
    prepared v 338=numerator (v 330) (v 333) (v 334)+v 332 :=
  preparation_output _ v

theorem prepared_other (v : ℕ→ℕ) (i : ℕ)
    (hi : i≠336 ∧ i≠337 ∧ i≠338 ∧ i≠339) : prepared v i=v i :=
  values_unchanged prepare v i (by
    simp only [prepare,preparation,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      NatAssign.Instruction.target]
    omega)

theorem divided_degree (v : ℕ→ℕ) : divided v 335=degree (v 330) (v 332) (v 333) (v 334) := by
  simp only [divided,Function.update_self,decremented,prepared_numerator,
    Function.update_of_ne (by decide : (332:ℕ)≠338),prepared_other v 332 (by decide),degree]

theorem divided_other (v : ℕ→ℕ) (i : ℕ)
    (hi : i≠335 ∧ i≠336 ∧ i≠337 ∧ i≠338 ∧ i≠339) : divided v i=v i := by
  rw [divided,Function.update_of_ne hi.1,decremented,Function.update_of_ne hi.2.2.2.1,
    prepared_other v i hi.2]

theorem gridded_outputs (v : ℕ→ℕ) :
    gridded v 331=grid (v 330) (v 332) (v 333) (v 334) ∧
    gridded v 336=2*degree (v 330) (v 332) (v 333) (v 334) ∧ gridded v 340=0 := by
  simp [gridded,gridPlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,divided_degree,grid,Nat.add_comm]

theorem gridded_other (v : ℕ→ℕ) (i : ℕ) (hi : i≠331 ∧ i≠336 ∧ i≠339 ∧ i≠340) :
    gridded v i=divided v i :=
  values_unchanged gridPlan (divided v) i (by
    simp only [gridPlan,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      NatAssign.Instruction.target]
    omega)

theorem values_outputs (v : ℕ→ℕ) :
    values v 335=degree (v 330) (v 332) (v 333) (v 334) ∧
    values v 331=grid (v 330) (v 332) (v 333) (v 334) ∧
    values v 640=bits (v 330) (v 332) (v 333) (v 334) := by
  simp [values,precisionPlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,measured,
    gridded_outputs v,gridded_other v 335 (by decide),divided_degree,
    gridded_other v 333 (by decide),divided_other v 333 (by decide),bits]
  omega

theorem values_keep (v : ℕ→ℕ) (i : ℕ)
    (hi : i≠331 ∧ i≠335 ∧ i≠336 ∧ i≠337 ∧ i≠338 ∧ i≠339 ∧ i≠340 ∧ i≠640) :
    values v i=v i := by
  have hp := values_unchanged precisionPlan (measured v) i (by
    simp only [precisionPlan,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      NatAssign.Instruction.target]
    omega)
  rw [values,hp,measured,Function.update_of_ne hi.2.2.2.2.2.2.1,
    gridded_other v i (by omega),divided_other v i (by omega)]

theorem values_work_zero (v : ℕ→ℕ) (hz : ∀i∈NaturalQuotient.workPorts,v i=0) :
    ∀i∈NaturalQuotient.workPorts,values v i=0 := by
  intro i hi
  have hh := hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
  rw [values_keep v i (by omega)]
  exact hz i hi

#print axioms values_outputs
end Maxwell.Continuum.Calibration.RootParameters
