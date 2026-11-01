import Maxwell.Continuum.CalibrationBasisForcingTable
import Maxwell.Continuum.RationalDataflowWordReplace
import Maxwell.Continuum.NatAssignOutputWidth

/-! Compute the source-array length from the runtime radius and install the
actual countdown word. No array length or decrement trace is supplied. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow PartArray
open ArrayDecodeMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048
attribute [local irreducible] bank

def counterPlan : List NatAssign.Instruction :=
  prepare++[.copy 314 315,.multiply 313 315,.multiply 312 315]
def counterValues (n : ℕ → ℕ) : ℕ → ℕ := NatAssign.values counterPlan n
def counterCode : Code := .seq (NatAssign.code counterPlan) (WordReplace.code 315 201)
def counterWidth (B : ℕ) : ℕ := 2^9*(B+1)

theorem counterPlan_valid : ∀a∈counterPlan,a.Valid naturalIds := by
  have h311 := naturalIds_decode (by decide : 311∈ArrayDecodeMachine.ports)
  have h312 := naturalIds_decode (by decide : 312∈ArrayDecodeMachine.ports)
  have h313 := naturalIds_decode (by decide : 313∈ArrayDecodeMachine.ports)
  have h314 := naturalIds_decode (by decide : 314∈ArrayDecodeMachine.ports)
  have h315 := naturalIds_decode (by decide : 315∈ArrayDecodeMachine.ports)
  simp [counterPlan,prepare,NatAssign.Instruction.Valid,h311,h312,h313,h314,h315]

theorem counterValue (n : ℕ → ℕ) : counterValues n 315=aliasArraySize (n 311) := by
  simp [counterValues,counterPlan,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,aliasArraySize,aliasSide]
  ring

theorem counterValues_keep (n : ℕ → ℕ) (k : ℕ) (hk : k≠312 ∧ k≠313 ∧ k≠314 ∧ k≠315) :
    counterValues n k=n k := by
  apply values_unchanged
  simp [counterPlan,prepare,NatAssign.Instruction.target,Ne.symm hk.1,Ne.symm hk.2.1,
    Ne.symm hk.2.2.1,Ne.symm hk.2.2.2]

theorem counterValues_agrees (n : ℕ → ℕ) (v : ℕ → Parts)
    (agree : ∀k∈ids bank,n k=dataValues v k) (k : ℕ) (hk : k∈ids bank) :
    counterValues n k=dataValues v k := by
  have hout (i : ℕ) (hi : i=312 ∨ i=313 ∨ i=314 ∨ i=315) : k≠i := by
    intro he
    subst k
    rcases hi with rfl|rfl|rfl|rfl <;> exact (outside_bank _ (by decide) (by decide)) hk
  rw [counterValues_keep n k ⟨hout _ (Or.inl rfl),hout _ (Or.inr (Or.inl rfl)),
    hout _ (Or.inr (Or.inr (Or.inl rfl))),hout _ (Or.inr (Or.inr (Or.inr rfl)))⟩,agree k hk]

theorem counter_literals (B : ℕ) (hB : 2≤B) : ∀a∈counterPlan,a.literalWidth≤B := by
  simp [counterPlan,prepare,NatAssign.Instruction.literalWidth,
    show (3:ℕ).bits.length=2 by decide,hB]
  omega

theorem counter_width (n : ℕ → ℕ) (B : ℕ) (hB : 2≤B)
    (hw : ∀k∈naturalIds,(n k).bits.length≤B) :
    ∀k∈naturalIds,(counterValues n k).bits.length≤counterWidth B := by
  have h := NatAssign.values_width_bound naturalIds counterPlan counterPlan_valid n B hw (counter_literals B hB)
  intro k hk
  have hh := h k hk
  change (counterValues n k).bits.length+1≤2^9*(B+1) at hh
  unfold counterWidth
  omega

theorem counter_executes {T : ℕ} (a : Table T) (n : ℕ → ℕ) (v : ℕ → Parts)
    (agree : ∀k∈ids bank,n k=dataValues v k) (B : ℕ) (hB : 2≤B)
    (hw : ∀k∈naturalIds,(n k).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (s : Store)
    (hs : NatAssign.Bank naturalIds n s.val) (hz : ∀k,k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.OutputReady s) (hword : BankArray.Word s.val 201 xs) :
    ∃cost t,Executes input tape counterCode cost s t ∧ cost≤2^120*(B+xs.length+10)^2 ∧
      NatAssign.Bank naturalIds (counterValues n) t.val ∧ Ready bank v t ∧
      a.OutputReady t ∧ (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧
      BankArray.Word t.val 201 (aliasArraySize (n 311)).bits ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output := by
  obtain ⟨c0,u,e0,hc0,b0,r0,z0,f0⟩ := naturalStage_parts bank naturalIds naturalIds_parts naturalIds_ge
    counterPlan counterPlan_valid (by decide) n v B hw (counter_literals B hB)
    (counterValues_agrees n v agree) input tape s hs (fun k hk => hz k (by omega)) (hz 4 (by decide))
  have output0 := output_frame a s u ha v r0 f0
  have source := b0 315 (naturalIds_decode (by decide))
  obtain ⟨t,e1,word,f1⟩ := WordReplace.executes 315 201 (by decide) input tape
    (counterValues n 315).bits xs u source
      (BankArray.word_of_eq (f0.tapes 201 (protected_external 201 (by simp [protectedPorts]))) hword)
  have outside : 201∉workspace bank := by
    simp only [workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨by omega,fun h => naturalIds_counter (naturalIds_parts h)⟩
  have ready := r0.wordReplace_frame outside f1
  have scratch : BankArray.Scratch t.val := by
    rcases output0.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 0 (by decide)) h0,
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 1 (by decide)) h1,
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 2 (by decide)) h2,
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 3 (by decide)) h3,
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 5 (by decide)) h5,
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 6 (by decide)) h6,
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 8 (by decide)) h8,
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 9 (by decide)) h9⟩
  have output := output0.copy_frame (Or.inl rfl) f1 scratch
    (RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 7 (by decide)) output0.seven)
  refine ⟨c0+(6*xs.length+15*(counterValues n 315).bits.length+21),t,e0.seq e1,?_,?_,ready,output,
    fun k hk => RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 k (by omega)) (z0 k hk),?_,
    f1.2.1.trans f0.inputHead,f1.2.2.2.1.trans f0.randomCursor,f1.2.2.2.2.1.trans f0.output⟩
  · have width := counter_width n B hB hw 315 (naturalIds_decode (by decide))
    have sq : (B+2)^2≤(B+xs.length+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have linear : B+xs.length+1≤(B+xs.length+10)^2 :=
      (by omega : B+xs.length+1≤B+xs.length+10).trans (le_self_pow (by omega) (by decide : (2:ℕ)≠0))
    unfold stageCost at hc0
    unfold counterWidth at width
    nlinarith only [hc0,width,sq,linear,Nat.zero_le B,Nat.zero_le xs.length]
  · intro k hk
    exact RationalAccumulator.word_of_eq (f1.2.2.2.2.2.1 k (fun he => naturalIds_counter (he ▸ hk))) (b0 k hk)
  · simpa only [counterValue] using word

#print axioms counter_executes
end Maxwell.Continuum.Calibration.BasisForcing
