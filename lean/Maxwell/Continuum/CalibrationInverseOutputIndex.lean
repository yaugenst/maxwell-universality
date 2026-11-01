import Maxwell.Continuum.CalibrationInverseOutputPrepare
import Maxwell.Continuum.CalibrationArrayIndex

/-! Compute an inverse-array address from the actual retained countdown.
All six neighbors of a central corner have coordinates between -2 and 1,
so the shifted coordinates use addition of fixed nonnegative offsets. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine.OutputIndex
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def offset (ν : Alias) (j : Fin 3) : ℕ := (ν j+3).toNat
def plan (ν : Alias) (j : Fin 3) : List NatAssign.Instruction :=
  [.literal 530 (offset ν 0),.add 304 530,.literal 531 (offset ν 1),.add 304 531,
   .literal 533 7,.copy 304 534,.add 304 534,.add 534 533,
   .multiply 533 530,.add 531 530,.literal 531 (offset ν 2),.add 304 531,
   .multiply 533 530,.add 531 530,.literal 533 3,.multiply 533 530,
   .literal 531 j.val,.add 531 530,.copy 530 140]
def code (ν : Alias) (j : Fin 3) : Code := NatAssign.code (plan ν j)
def changed : Finset ℕ := {0,1,2,3,140,530,531,533,534}
def indexValue (N : ℕ) (ν : Alias) (j : Fin 3) : ℕ :=
  (((N+offset ν 0)*(2*N+7)+(N+offset ν 1))*(2*N+7)+(N+offset ν 2))*3+j.val

theorem in_cube (N : ℕ) (ν : Alias) (bounds:∀j,|ν j|≤2) : aliasInCube (N+3) ν := by
  intro j
  have h:=bounds j
  omega

def index (N : ℕ) (ν : Alias) (bounds:∀j,|ν j|≤2) (j : Fin 3) : Fin (aliasArraySize (N+3)) :=
  aliasArrayEquiv (N+3) (arrayAliasIndex (N+3) ν (in_cube N ν bounds),j)

theorem index_value (N : ℕ) (ν : Alias) (bounds:∀j,|ν j|≤2) (j : Fin 3) :
    (index N ν bounds j).val=indexValue N ν j := by
  have coord (k : Fin 3) : (ν k+((N+3:ℕ):ℤ)).toNat=N+offset ν k := by
    have h:=abs_le.mp (bounds k)
    unfold offset
    omega
  change j.val+3*((ν 2+((N+3:ℕ):ℤ)).toNat+aliasSide (N+3)*(ν 1+((N+3:ℕ):ℤ)).toNat+
    (aliasSide (N+3)*aliasSide (N+3))*(ν 0+((N+3:ℕ):ℤ)).toNat)=_
  rw [coord 0,coord 1,coord 2]
  unfold indexValue aliasSide
  ring

theorem valid (ν : Alias) (j : Fin 3) : ∀a∈plan ν j,a.Valid OutputPrepare.indexIds := by
  simp [plan,NatAssign.Instruction.Valid,OutputPrepare.indexIds]

theorem value (ν : Alias) (j : Fin 3) (v : ℕ→ℕ) :
    NatAssign.values (plan ν j) v 140=indexValue (v 304) ν j := by
  simp only [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update_apply]
  norm_num
  unfold indexValue
  ring

theorem executes (ν : Alias) (bounds:∀j,|ν j|≤2) (j : Fin 3) (v : ℕ→ℕ) (B : ℕ) (hB:3≤B)
    (hw : ∀k∈OutputPrepare.indexIds,(v k).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank OutputPrepare.indexIds v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t, Executes input tape (code ν j) cost s t ∧ cost≤3000*8^19*(B+2)^2 ∧
      NatAssign.Bank OutputPrepare.indexIds (NatAssign.values (plan ν j) v) t.val ∧
      NatAssign.Scratch t.val ∧
      RationalAccumulator.Word t.val 140 (index (v 304) ν bounds j).val ∧
      (∀k∈OutputPrepare.indexIds,(NatAssign.values (plan ν j) v k).bits.length≤2^19*(B+1)) ∧
      BinaryPrecision.Frame changed s.val t.val := by
  have idsGe:∀k∈OutputPrepare.indexIds,4≤k:=by
    intro k hk
    simp only [OutputPrepare.indexIds,Finset.mem_insert,Finset.mem_singleton] at hk
    omega
  have offsetWidth (k : Fin 3) : (offset ν k).bits.length≤B := by
    have h:=abs_le.mp (bounds k)
    have hb:offset ν k≤5:=by unfold offset;omega
    have hs:=Nat.size_le_size hb
    rw [←Nat.size_eq_bits_len] at hs
    have five:Nat.size 5=3:=rfl
    omega
  have polWidth:j.val.bits.length≤B:=by
    have hs:=Nat.size_le_size (by omega : j.val≤2)
    rw [←Nat.size_eq_bits_len] at hs
    have two:Nat.size 2=2:=rfl
    omega
  have literal:∀a∈plan ν j,a.literalWidth≤B:=by
    simp [plan,NatAssign.Instruction.literalWidth,offsetWidth,polWidth,
      show (7:ℕ).bits.length=3 by rfl,show (3:ℕ).bits.length=2 by rfl]
    omega
  obtain ⟨cost,t,executes,costBound,output,zero,frame⟩:=
    NatAssign.executes OutputPrepare.indexIds idsGe (plan ν j) (valid ν j) v input tape s bank scratch
  refine ⟨cost,t,executes,?_,output,zero,?_,?_,?_⟩
  · simpa only [plan,List.length_cons,List.length_nil] using
      costBound.trans (NatAssign.price_bound _ _ (valid ν j) v B hw literal)
  · rw [index_value]
    simpa only [value] using output 140 (by decide)
  · intro k hk
    have h:=NatAssign.values_width_bound _ _ (valid ν j) v B hw literal k hk
    change (NatAssign.values (plan ν j) v k).bits.length+1≤2^19*(B+1) at h
    omega
  · apply frame.mono
    simp [NatAssign.changes,plan,NatAssign.Instruction.target,changed]
    decide

#print axioms executes
#print axioms index_value
end Maxwell.Continuum.Calibration.NeumannMachine.OutputIndex
