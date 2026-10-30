import Maxwell.Continuum.CalibrationMatrixEntryStore
import Maxwell.Continuum.NaturalBankImportWord

/-! The matrix dimension, row, column, and padded-table offset are computed
from the radius and an actual runtime flat index. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem nat_values_width (S : Finset ℕ) (ins : List NatAssign.Instruction)
    (hi : ∀ a∈ins, a.Valid S) (n : ℕ→ℕ) (B : ℕ)
    (hn : ∀ k∈S, (n k).bits.length≤B)
    (hl : ∀ a∈ins, a.literalWidth≤B) :
    ∀ k∈S, (NatAssign.values ins n k).bits.length≤2^ins.length*(B+1) := by
  induction ins generalizing n B with
  | nil =>
    intro k hk
    simpa only [NatAssign.values,List.length_nil,pow_zero,one_mul] using (hn k hk).trans (by omega)
  | cons a rest ih =>
    have step := NatAssign.instruction_width S a (hi a (by simp)) n B hn (hl a (by simp))
    have tail := ih (fun x hx => hi x (by simp [hx])) (a.update n) (2*B+1) step
      (fun x hx => (hl x (by simp [hx])).trans (by omega))
    intro k hk
    simpa only [NatAssign.values,List.length_cons,pow_succ,
      show 2*B+1+1=2*(B+1) by ring,mul_assoc] using tail k hk

def flatPrepare : List NatAssign.Instruction := prepare ++
  [.copy 314 331,.multiply 313 331,.multiply 312 331,.copy 331 332,.add 330 332]
def flatPrepared (n : ℕ→ℕ) : ℕ→ℕ := NatAssign.values flatPrepare n
def flatNaturals (n : ℕ→ℕ) : ℕ→ℕ := divModValues (flatPrepared n) 330 331 321 310
def flatCode : Code := .seq (NatAssign.code flatPrepare) (NaturalDivMod.code 330 331 321 310)

theorem flatPrepared_values (n : ℕ→ℕ) : flatPrepared n=
    Function.update (Function.update (prepared n) 331 (aliasArraySize (n 311)))
      332 (aliasArraySize (n 311)+n 330) := by
  funext k
  simp [flatPrepared,flatPrepare,prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,aliasArraySize,aliasSide,
    Nat.mul_comm,Nat.add_comm]
  rw [show n 311+(1+n 311)=1+2*n 311 by omega]

theorem flatPrepared_valid : ∀ a∈flatPrepare, a.Valid emissionIds := by
  simp [flatPrepare,prepare,NatAssign.Instruction.Valid,emissionIds,ids,RawFree.neighborRegisters,
    workPorts]

theorem flatPrepared_other (n : ℕ→ℕ) (k : ℕ)
    (hk : k≠312 ∧ k≠313 ∧ k≠314 ∧ k≠331 ∧ k≠332) : flatPrepared n k=n k := by
  rw [flatPrepared_values,Function.update_of_ne hk.2.2.2.2,Function.update_of_ne hk.2.2.2.1,
    prepared_other n k hk.1 hk.2.1 hk.2.2.1]

theorem flatNaturals_indices (n : ℕ→ℕ) :
    flatNaturals n 311=n 311 ∧
    flatNaturals n 321=n 330/aliasArraySize (n 311) ∧
    flatNaturals n 310=n 330%aliasArraySize (n 311) ∧
    flatNaturals n 332=aliasArraySize (n 311)+n 330 := by
  simp [flatNaturals,divModValues,flatPrepared_values,
    prepared_other n 330 (by decide) (by decide) (by decide),
    prepared_other n 311 (by decide) (by decide) (by decide)]

theorem flatNaturals_other (n : ℕ→ℕ) (k : ℕ)
    (hk : k≠310 ∧ k≠312 ∧ k≠313 ∧ k≠314 ∧ k≠321 ∧ k≠331 ∧ k≠332) :
    flatNaturals n k=n k := by
  rw [flatNaturals,divModValues,Function.update_of_ne hk.1,Function.update_of_ne hk.2.2.2.2.1,
    flatPrepared_other n k ⟨hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2.2.1,hk.2.2.2.2.2.2⟩]

theorem flat_width (n : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤B) :
    ∀ k∈emissionIds, (flatNaturals n k).bits.length≤2^11*(B+1) := by
  have literals : ∀ a∈flatPrepare, a.literalWidth≤B := by
    simp only [flatPrepare,prepare,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc]
    rintro a (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [NatAssign.Instruction.literalWidth,show (3:ℕ).bits.length=2 by decide] <;> omega
  have pw := nat_values_width emissionIds flatPrepare flatPrepared_valid n B hw literals
  change ∀ k∈emissionIds, (divModValues (flatPrepared n) 330 331 321 310 k).bits.length≤_
  exact divModValues_width (flatPrepared n) emissionIds 330 331 321 310 (2^11*(B+1))
    (by decide) (by simpa only [flatPrepared,show flatPrepare.length=11 by decide] using pw)

theorem flat_executes (n : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤B)
    (hzero : ∀ k∈NaturalQuotient.workPorts, n k=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k) :
    ∃ cost t, Executes input tape flatCode cost s t ∧ cost≤2^126*(B+2)^2 ∧
      NatAssign.Bank emissionIds (flatNaturals n) t.val ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      BinaryPrecision.Frame emissionChanged s.val t.val := by
  have literals : ∀ a∈flatPrepare, a.literalWidth≤B := by
    simp only [flatPrepare,prepare,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc]
    rintro a (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [NatAssign.Instruction.literalWidth,show (3:ℕ).bits.length=2 by decide] <;> omega
  obtain ⟨c0,u,e0,hc0,bank,z0,f0⟩ := fixedBankStage_executes emissionIds
    (fun k hk => by have := emissionIds_ge k hk; omega) flatPrepare flatPrepared_valid
    (by decide) n B hw literals input tape s hs (fun k hk => hz k (by omega))
  have blank : ∀ k, k<5 → RationalAccumulator.Blank u.val k := by
    intro k hk
    by_cases h4 : k<4
    · exact z0 k h4
    · have he : k=4 := by omega
      subst k
      exact RationalAccumulator.blank_of_eq (f0.tapes 4 (by decide)) (hz 4 (by decide))
  have zero : ∀ k∈NaturalQuotient.workPorts, flatPrepared n k=0 := by
    intro k hk
    have he := hk
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at he
    rw [flatPrepared_other n k (by omega)]
    exact hzero k hk
  have positive : 0<flatPrepared n 331 := by
    rw [flatPrepared_values,Function.update_of_ne (by decide : (331:ℕ)≠332),Function.update_self]
    exact aliasArraySize_pos _
  have width := nat_values_width emissionIds flatPrepare flatPrepared_valid n B hw literals
  have pw : ∀ k∈emissionIds, (flatPrepared n k).bits.length≤2^11*(B+1) := by
    simpa only [flatPrepared,show flatPrepare.length=11 by decide] using width
  obtain ⟨c1,t,e1,hc1,bank1,z1,f1⟩ := NaturalDivMod.executes emissionIds emissionIds_ge emissionIds_work
    330 331 321 310 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (flatPrepared n) zero positive (2^11*(B+1)) pw input tape u bank blank
  refine ⟨c0+c1,t,e0.seq e1,?_,bank1,z1,(f0.mono ?_).trans f1⟩
  · unfold stageCost at hc0
    have hsquare : (2^11*(B+1)+2)^2≤2^22*(B+2)^2 := by nlinarith [Nat.zero_le B]
    nlinarith only [hc0,hc1,hsquare,Nat.zero_le ((B+2)^2)]
  · intro k hk
    simp only [emissionChanged,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    tauto

#print axioms flat_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
