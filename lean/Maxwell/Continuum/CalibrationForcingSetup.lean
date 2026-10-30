import Maxwell.Continuum.CalibrationMatrixRuntimeReset
import Maxwell.Continuum.CalibrationMatrixFlatIndex
import Maxwell.Continuum.CalibrationForcingIndex

/-! A runtime alias counter is turned into the actual stride-three Fourier
index before the already verified quotient/remainder coordinate decoder. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def forcingSetup : List NatAssign.Instruction :=
  [.literal 312 3,.copy 330 310,.multiply 312 310,.copy 310 321]
def forcingSetupNaturals (n : ℕ→ℕ) : ℕ→ℕ := NatAssign.values forcingSetup n

theorem forcingSetup_valid : ∀ a∈forcingSetup, a.Valid emissionIds := by
  simp [forcingSetup,NatAssign.Instruction.Valid,emissionIds]

theorem forcingSetup_values (n : ℕ→ℕ) : forcingSetupNaturals n=
    Function.update (Function.update (Function.update n 312 3) 310 (3*n 330)) 321 (3*n 330) := by
  simp only [forcingSetupNaturals,forcingSetup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_of_ne (by decide : (330:ℕ)≠312),
    Function.update_of_ne (by decide : (312:ℕ)≠310),Function.update_self]
  rw [Function.update_idem]

theorem forcingSetup_other (n : ℕ→ℕ) (k : ℕ) (hk : k≠310 ∧ k≠312 ∧ k≠321) :
    forcingSetupNaturals n k=n k := by
  rw [forcingSetup_values,Function.update_of_ne hk.2.2,Function.update_of_ne hk.1,
    Function.update_of_ne hk.2.1]

theorem forcingSetup_indices (n : ℕ→ℕ) :
    forcingSetupNaturals n 311=n 311 ∧ forcingSetupNaturals n 310=3*n 330 ∧
      forcingSetupNaturals n 321=3*n 330 := by simp [forcingSetup_values]

theorem forcingSetup_agrees (n : ℕ→ℕ) (v : ℕ→Parts)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k) :
    ∀ k∈ids RawFree.neighborRegisters, forcingSetupNaturals n k=dataValues v k := by
  intro k hk
  have ho := rational_port_outside_all RawFree.neighborRegisters k hk
  have h321 : k≠321 := by
    intro h; subst k; exact (by decide : 321∉ids RawFree.neighborRegisters) hk
  rw [forcingSetup_other n k ⟨fun h => ho (h ▸ (by decide)),
    fun h => ho (h ▸ (by decide)),h321⟩,hn k hk]

theorem forcingSetup_work (n : ℕ→ℕ) (hn : ∀ k∈NaturalQuotient.workPorts, n k=0) :
    ∀ k∈NaturalQuotient.workPorts, forcingSetupNaturals n k=0 := by
  intro k hk
  have h := hk
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at h
  rw [forcingSetup_other n k (by omega),hn k hk]

theorem forcingSetup_literals (B : ℕ) (hB : 2≤B) :
    ∀ a∈forcingSetup, a.literalWidth≤B := by
  simp only [forcingSetup,List.mem_cons,List.not_mem_nil,or_false]
  rintro a (rfl | rfl | rfl | rfl) <;>
    norm_num [NatAssign.Instruction.literalWidth,show (3:ℕ).bits.length=2 by decide]
  omega

theorem forcingSetup_width (n : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤B) :
    ∀ k∈emissionIds, (forcingSetupNaturals n k).bits.length≤16*(B+1) := by
  simpa only [forcingSetupNaturals,show forcingSetup.length=4 by decide,show (2:ℕ)^4=16 by decide] using
    nat_values_width emissionIds forcingSetup forcingSetup_valid n B hw (forcingSetup_literals B hB)

theorem forcingSetup_executes (n : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k) :
    ∃ cost t, Executes input tape (NatAssign.code forcingSetup) cost s t ∧
      cost≤2^102*(B+2)^2 ∧ NatAssign.Bank emissionIds (forcingSetupNaturals n) t.val ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      BinaryPrecision.Frame emissionChanged s.val t.val := by
  obtain ⟨cost,t,he,hc,hbank,hz',hf⟩ := fixedBankStage_executes emissionIds
    (fun k hk => by have := emissionIds_ge k hk; omega) forcingSetup forcingSetup_valid
    (by decide) n B hw (forcingSetup_literals B hB) input tape s hs (fun k hk => hz k (by omega))
  refine ⟨cost,t,he,?_,hbank,?_,hf.mono ?_⟩
  · unfold stageCost at hc
    nlinarith only [hc,Nat.zero_le ((B+2)^2)]
  · intro k hk
    by_cases h4 : k<4
    · exact hz' k h4
    · have heq : k=4 := by omega
      subst k
      exact RationalAccumulator.blank_of_eq (hf.tapes 4 (by decide)) (hz 4 (by decide))
  · intro k hk
    simp only [emissionChanged,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    tauto

#print axioms forcingSetup_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
