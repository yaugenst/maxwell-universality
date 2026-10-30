import Maxwell.Continuum.CalibrationForcingSetup
import Maxwell.Continuum.CalibrationForcingVectorExecution

/-! Complete runtime preparation for a forcing row: import the padded alias
counter, reset temporaries, and decode the literal Fourier coordinates. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def forcingBaseWidth (B : ℕ) : ℕ := 128*(B+1)
def forcingEmissionWidth (B : ℕ) : ℕ := RawFree.forcingVectorWidth (forcingBaseWidth B)
def forcingInput (v : ℕ→Parts) (n : ℕ→ℕ) (row : ℕ) : ℕ→ℕ :=
  forcingSetupNaturals (cleanNaturals v (Function.update n 330 row))
def forcingDecodedParts (v : ℕ→Parts) (n : ℕ→ℕ) (row : ℕ) : ℕ→Parts :=
  matrixParts (resetParts v) (forcingInput v n row)
def forcingDecodedNaturals (v : ℕ→Parts) (n : ℕ→ℕ) (row : ℕ) : ℕ→ℕ :=
  matrixNaturals (forcingInput v n row)
def forcingPrepareCode : Code := .seq (NaturalImport.code 201 330)
  (.seq runtimeResetCode (.seq (NatAssign.code forcingSetup) matrixDecodeCode))

theorem forcingBaseWidth_ge (B : ℕ) : B≤forcingBaseWidth B := by unfold forcingBaseWidth; omega
theorem forcingEmissionWidth_ge (B : ℕ) : forcingBaseWidth B≤forcingEmissionWidth B := by
  unfold forcingEmissionWidth RawFree.forcingVectorWidth; omega

theorem forcingInput_agrees (v : ℕ→Parts) (n : ℕ→ℕ) (row : ℕ) :
    ∀ k∈ids RawFree.neighborRegisters, forcingInput v n row k=dataValues (resetParts v) k :=
  forcingSetup_agrees _ _ (cleanNaturals_agrees v _)

theorem forcingInput_indices (v : ℕ→Parts) (n : ℕ→ℕ) (row : ℕ) :
    forcingInput v n row 311=n 311 ∧ forcingInput v n row 310=3*row ∧
      forcingInput v n row 321=3*row := by
  simpa only [forcingInput,(cleanNaturals_parameters v (Function.update n 330 row)).1,
    (cleanNaturals_parameters v (Function.update n 330 row)).2.1,Function.update_self,
    Function.update_of_ne (by decide : (311:ℕ)≠330)] using
      forcingSetup_indices (cleanNaturals v (Function.update n 330 row))

theorem forcingInput_work (v : ℕ→Parts) (n : ℕ→ℕ) (row : ℕ) :
    ∀ k∈NaturalQuotient.workPorts, forcingInput v n row k=0 :=
  forcingSetup_work _ (cleanNaturals_parameters v _).2.2

theorem forcingDecoded_parameter (v : ℕ→Parts) (n : ℕ→ℕ) (row k : ℕ)
    (hk : k∈matrixParameters) : forcingDecodedParts v n row k=v k := by
  have cases : k=0 ∨ k=1 ∨ k=16 ∨ k=17 ∨ k=18 := by
    simpa only [matrixParameters,Finset.mem_insert,Finset.mem_singleton] using hk
  rw [forcingDecodedParts,matrixParts_input _ _ k (by omega),reset_keeps_parameter v k hk]

theorem forcingDecoded_radius (v : ℕ→Parts) (n : ℕ→ℕ) (row : ℕ) :
    forcingDecodedNaturals v n row 311=n 311 := by
  rw [forcingDecodedNaturals,matrixNaturals,coordinateLoad_small _ 311 (by decide),output_radius,
    rowStart_radius]
  exact (forcingInput_indices v n row).1

theorem forcingDecoded_work (v : ℕ→Parts) (n : ℕ→ℕ) (row k : ℕ)
    (hk : k∈NaturalQuotient.workPorts) : forcingDecodedNaturals v n row k=0 := by
  have h := hk
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at h
  rw [forcingDecodedNaturals,matrixNaturals_external _ k (by omega) (by
    simp only [ports,Finset.mem_Icc]; omega)]
  exact forcingInput_work v n row k hk

theorem forcingPrepare_executes (v : ℕ→Parts) (n : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤forcingEmissionWidth B)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid)
    (hR : (n 311).bits.length≤B) (R : ℕ) (row : Fin (aliasRowCount R)) (hradius : n 311=R)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (hlen : xs.length≤B)
    (hindex : addressValue xs=row.val) (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k) (hcounter : BankArray.Word s.val 201 xs) :
    ∃ cost t, Executes input tape forcingPrepareCode cost s t ∧
      cost≤2^140*(forcingEmissionWidth B+10)^2 ∧
      NatAssign.Bank emissionIds (forcingDecodedNaturals v n row.val) t.val ∧
      RationalDataflow.Ready RawFree.neighborRegisters (forcingDecodedParts v n row.val) t ∧
      Good RawFree.neighborRegisters (forcingDecodedParts v n row.val) ∧
      WidthBank RawFree.neighborRegisters (forcingBaseWidth B) (forcingDecodedParts v n row.val) ∧
      (∀ k∈emissionIds, (forcingDecodedNaturals v n row.val k).bits.length≤forcingBaseWidth B) ∧
      (∀ k, (RawFree.coordinates (forcingDecodedParts v n row.val) k).value=
        (arrayAliasAt R (polarizationRow R row 0) k:ℚ)) ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      BinaryPrecision.Frame emissionChanged s.val t.val := by
  let U := forcingEmissionWidth B
  have hBU : B≤U := (forcingBaseWidth_ge B).trans (forcingEmissionWidth_ge B)
  have indexWidth : row.val.bits.length≤B := by
    rw [← hindex,Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length xs)).trans hlen
  obtain ⟨c0,u0,e0,hc0,bank0,f0⟩ := NaturalImport.executes emissionIds 201 330 (by decide)
    (by decide) n xs input tape s hs hcounter
  rw [hindex] at bank0
  let n0 := Function.update n 330 row.val
  have agree0 : ∀ k∈ids RawFree.neighborRegisters, n0 k=dataValues v k := by
    intro k hk
    have hne : k≠330 := by intro he; subst k; exact (by decide : 330∉ids RawFree.neighborRegisters) hk
    simpa only [n0,Function.update_of_ne hne] using hn k hk
  have width0 : ∀ k∈emissionIds, (n0 k).bits.length≤U :=
    nat_update_width n emissionIds U 330 row.val hw (indexWidth.trans hBU)
  have blank0 (k : ℕ) (hk : k<5) : RationalAccumulator.Blank u0.val k :=
    RationalAccumulator.blank_of_eq (f0.tapes k (by simp only [Finset.mem_singleton]; omega)) (hz k hk)
  obtain ⟨c1,u1,e1,hc1,bank1,_,good1,width1,z1,f1⟩ := runtimeReset_executes v n0 agree0 U B
    (by omega) hBU width0 hp (by simpa only [n0,Function.update_of_ne (by decide : (311:ℕ)≠330)] using hR)
    (by simpa only [n0,Function.update_self] using indexWidth) input tape u0 bank0 blank0
  obtain ⟨c2,u2,e2,hc2,bank2,z2,f2⟩ := forcingSetup_executes (cleanNaturals v n0) B hB width1
    input tape u1 bank1 z1
  have width2 := forcingSetup_width (cleanNaturals v n0) B hB width1
  have indices := forcingInput_indices v n row.val
  have hindex0 : (polarizationRow R row 0).val=3*row.val := by simp [polarizationRow]
  obtain ⟨c3,t,e3,hc3,bank3,ready3,good3,width3,coord,_,_,_,f3,z34⟩ := matrixDecode_executes
    emissionIds emissionIds_ge emissionIds_decode emissionIds_work emissionIds_parts (by decide)
    (forcingInput v n row.val) (resetParts v) (forcingInput_agrees v n row.val)
    (forcingInput_work v n row.val) good1 (16*(B+1)) (by omega) width2 R
    (polarizationRow R row 0) (polarizationRow R row 0) (indices.1.trans hradius)
    (indices.2.2.trans hindex0.symm) (indices.2.1.trans hindex0.symm) input tape u2 bank2 z2
  have hwidth : 4*(16*(B+1))+24≤forcingBaseWidth B := by unfold forcingBaseWidth; omega
  have widthNatural := matrixNaturals_width emissionIds emissionIds_decode (by decide)
    (forcingInput v n row.val) (16*(B+1)) width2
  have importFrame : BinaryPrecision.Frame emissionChanged s.val u0.val := f0.mono (by
    intro k hk
    have he : k=330 := by simpa only [Finset.mem_singleton] using hk
    subst k
    decide)
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,bank3,ready3,good3,
    (fun k hk => (width3 k hk).mono hwidth),
    (fun k hk => (widthNatural k hk).trans hwidth),?_,?_,importFrame.trans (f1.trans (f2.trans f3))⟩
  · have hold := hw 330 (by decide)
    have hs0 : 1≤(U+10)^2 := one_le_pow₀ (by omega)
    have hs1 : (U+3)^2≤(U+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have hs2 : (B+2)^2≤(U+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have hs3 : (16*(B+1)+10)^2≤(U+10)^2 := Nat.pow_le_pow_left (by
      have hb := forcingEmissionWidth_ge B
      unfold forcingBaseWidth at hb
      dsimp only [U]
      omega) 2
    have hs4 : U≤(U+10)^2 := by nlinarith only [Nat.zero_le U]
    nlinarith only [hc0,hc1,hc2,hc3,hold,hlen,hBU,hs0,hs1,hs2,hs3,hs4]
  · intro k
    rw [forcingDecodedParts,coord k,RawFree.coordinatePart_value]
  · intro k hk
    by_cases h4 : k<4
    · exact ready3.2 k h4
    · have he : k=4 := by omega
      exact he ▸ z34

#print axioms forcingPrepare_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
