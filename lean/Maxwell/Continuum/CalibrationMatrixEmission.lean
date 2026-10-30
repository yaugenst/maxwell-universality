import Maxwell.Continuum.CalibrationMatrixRuntimeReset
import Maxwell.Continuum.CalibrationMatrixFlatIndex
import Maxwell.Continuum.CalibrationMatrixEntryParameters

/-! One iteration of the literal matrix-table generator. A padded runtime
counter is imported, all temporary words are reset, the actual row and column
are decoded, and the computed coefficient is written into raw memory. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def emissionBaseWidth (B : ℕ) : ℕ := 2^11*(B+1)
def emissionWidth (B : ℕ) : ℕ := matrixEntryWordBound (emissionBaseWidth B)
def emissionCode : Code := .seq (NaturalImport.code 201 330)
  (.seq runtimeResetCode (.seq flatCode matrixStoreCode))
def emissionInput (v : ℕ→Parts) (n : ℕ→ℕ) (index : ℕ) : ℕ→ℕ :=
  flatNaturals (cleanNaturals v (Function.update n 330 index))
def emissionParts (v : ℕ→Parts) (n : ℕ→ℕ) (index : ℕ) : ℕ→Parts :=
  matrixEntryOutput (resetParts v) (emissionInput v n index)
def emissionNaturals (v : ℕ→Parts) (n : ℕ→ℕ) (index : ℕ) : ℕ→ℕ :=
  matrixEntryNaturals (resetParts v) (emissionInput v n index)

theorem emission_width_ge (B : ℕ) : B≤emissionWidth B := by
  unfold emissionWidth matrixEntryWordBound emissionBaseWidth RawFree.matrixEntryWidth
  omega

theorem emissionInput_agrees (v : ℕ→Parts) (n : ℕ→ℕ) (index k : ℕ)
    (hk : k∈ids RawFree.neighborRegisters) :
    emissionInput v n index k=dataValues (resetParts v) k := by
  have disjoint : Disjoint (ids RawFree.neighborRegisters) (Finset.Icc 310 332) := by decide
  have hout : k<310 ∨ 332<k := by
    have hn : k∉Finset.Icc 310 332 := fun hc => Finset.disjoint_left.mp disjoint hk hc
    simp only [Finset.mem_Icc,not_and] at hn
    omega
  rw [emissionInput,flatNaturals_other _ k (by omega),cleanNaturals_agrees v _ k hk]

theorem emissionInput_indices (v : ℕ→Parts) (n : ℕ→ℕ) (index : ℕ) :
    emissionInput v n index 311=n 311 ∧
    emissionInput v n index 321=index/aliasArraySize (n 311) ∧
    emissionInput v n index 310=index%aliasArraySize (n 311) ∧
    emissionInput v n index 332=aliasArraySize (n 311)+index := by
  have h := flatNaturals_indices (cleanNaturals v (Function.update n 330 index))
  simpa only [emissionInput,(cleanNaturals_parameters v (Function.update n 330 index)).1,
    (cleanNaturals_parameters v (Function.update n 330 index)).2.1,
    Function.update_self,Function.update_of_ne (by decide : (311:ℕ)≠330)] using h

theorem emissionInput_work (v : ℕ→Parts) (n : ℕ→ℕ) (index k : ℕ)
    (hk : k∈NaturalQuotient.workPorts) : emissionInput v n index k=0 := by
  have hk' := hk
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk'
  rw [emissionInput,flatNaturals_other _ k (by omega)]
  exact (cleanNaturals_parameters v _).2.2 k hk

theorem emissionParts_parameter (v : ℕ→Parts) (n : ℕ→ℕ) (index k : ℕ)
    (hk : k∈matrixParameters) : emissionParts v n index k=v k := by
  rw [emissionParts,matrixEntry_parameter _ _ k hk,reset_keeps_parameter v k hk]

theorem emissionNaturals_radius (v : ℕ→Parts) (n : ℕ→ℕ) (index : ℕ) :
    emissionNaturals v n index 311=n 311 := by
  rw [emissionNaturals,matrixEntryNaturals,ite_eq_right (by decide : 311∉ids RawFree.neighborRegisters)]
  rw [matrixNaturals,coordinateLoad_small _ 311 (by decide),output_radius,rowStart_radius]
  exact (emissionInput_indices v n index).1

theorem emission_executes {T : ℕ} (a : PartArray.Table T) (target : Fin T)
    (v : ℕ→Parts) (n : ℕ→ℕ) (B W : ℕ) (hB : 101≤B)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤emissionWidth B)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid)
    (hR : (n 311).bits.length≤B) (hmeta : a.MetadataWidth W)
    (hfit : emissionWidth B≤addressValue a.width) (hsep : a.Separated)
    (R : ℕ) (i j : Fin (aliasArraySize R)) (index : ℕ) (hradius : n 311=R)
    (hi : index/aliasArraySize R=i.val) (hj : index%aliasArraySize R=j.val)
    (htarget : aliasArraySize R+index=target.val)
    (htbox : (3:ℝ)≤(v 0).value)
    (hEbox : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hrbox : ∀ k, |((RawFree.quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (hlen : xs.length≤B)
    (hindex : addressValue xs=index) (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.OutputReady s) (hcounter : BankArray.Word s.val 201 xs) :
    ∃ cost t, Executes input tape emissionCode cost s t ∧
      cost≤2^600*(emissionWidth B+W+10)^2 ∧
      NatAssign.Bank emissionIds (emissionNaturals v n index) t.val ∧
      RationalDataflow.Ready RawFree.neighborRegisters (emissionParts v n index) t ∧
      Good RawFree.neighborRegisters (emissionParts v n index) ∧
      (∀ k∈emissionIds, (emissionNaturals v n index k).bits.length≤emissionWidth B) ∧
      (a.set target (emissionParts v n index 12)).OutputReady t ∧
      (emissionParts v n index 12).value=cachedTransitionMatrix (v 0).value (v 1).value
        (fun k => (RawFree.quasiParts v k).value) R i j ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      t.val.tapes 201=s.val.tapes 201 ∧
      (∀ k∈([200,202,203,204,205]:List ℕ), t.val.tapes k=s.val.tapes k) ∧
      ContinuationFrame s.val t.val := by
  let U := emissionWidth B
  have hBU : B≤U := emission_width_ge B
  have indexWidth : index.bits.length≤B := by
    rw [← hindex,Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length xs)).trans hlen
  obtain ⟨c0,u0,e0,hc0,bank0,f0⟩ := NaturalImport.executes emissionIds 201 330 (by decide)
    (by decide) n xs input tape s hs hcounter
  rw [hindex] at bank0
  let n0 := Function.update n 330 index
  have agree0 : ∀ k∈ids RawFree.neighborRegisters, n0 k=dataValues v k := by
    intro k hk
    have hne : k≠330 := by intro he; subst k; exact (by decide : 330∉ids RawFree.neighborRegisters) hk
    simpa only [n0,Function.update_of_ne hne] using hn k hk
  have width0 : ∀ k∈emissionIds, (n0 k).bits.length≤U :=
    nat_update_width n emissionIds U 330 index hw (indexWidth.trans hBU)
  have blank0 (k : ℕ) (hk : k<5) : RationalAccumulator.Blank u0.val k :=
    RationalAccumulator.blank_of_eq (f0.tapes k (by simp only [Finset.mem_singleton]; omega)) (hz k hk)
  obtain ⟨c1,u1,e1,hc1,bank1,ready1,good1,width1,z1,f1⟩ := runtimeReset_executes v n0 agree0 U B
    (by omega) hBU width0 hp (by simpa only [n0,Function.update_of_ne (by decide : (311:ℕ)≠330)] using hR)
    (by simpa only [n0,Function.update_self] using indexWidth) input tape u0 bank0 blank0
  obtain ⟨c2,u2,e2,hc2,bank2,z2,f2⟩ := flat_executes (cleanNaturals v n0) B (by omega) width1
    (cleanNaturals_parameters v n0).2.2 input tape u1 bank1 z1
  have importFrame : BinaryPrecision.Frame emissionChanged s.val u0.val := f0.mono (by
    intro k hk
    have he : k=330 := by simpa only [Finset.mem_singleton] using hk
    subst k
    decide)
  have preframe : BinaryPrecision.Frame emissionChanged s.val u2.val := importFrame.trans (f1.trans f2)
  have ready2 : RationalDataflow.Ready RawFree.neighborRegisters (resetParts v) u2 := by
    refine ⟨?_,fun k hk => z2 k (by omega)⟩
    intro k hk
    have h := bank2 k (emissionIds_parts hk)
    change RationalAccumulator.Word u2.val k (emissionInput v n index k) at h
    simpa only [emissionInput_agrees v n index k hk] using h
  have a2 := outputReady_emission_frame a s u2 ha _ ready2 preframe
  have width2 : ∀ k∈emissionIds, (emissionInput v n index k).bits.length≤emissionBaseWidth B :=
    flat_width (cleanNaturals v n0) B (by omega) width1
  have hb2 : 101≤emissionBaseWidth B := by unfold emissionBaseWidth; omega
  have indices := emissionInput_indices v n index
  have param0 := reset_keeps_parameter v 0 (by decide)
  have param1 := reset_keeps_parameter v 1 (by decide)
  have quasi : RawFree.quasiParts (resetParts v)=RawFree.quasiParts v := by
    funext k
    fin_cases k
    · exact reset_keeps_parameter v 16 (by decide)
    · exact reset_keeps_parameter v 17 (by decide)
    · exact reset_keeps_parameter v 18 (by decide)
  obtain ⟨c3,t,e3,hc3,ready3,outReady,_,value,_,bank3,good3,width3,z3,count,headers,continuation⟩ := matrixStore_executes a target
    (emissionInput v n index) (resetParts v) (emissionInput_agrees v n index)
    (emissionInput_work v n index) good1 (emissionBaseWidth B) W hb2 width2 hmeta
    (by rw [indices.2.2.2,hradius]; exact htarget) hfit hsep R i j
    (indices.1.trans hradius) (by rw [indices.2.1,hradius]; exact hi)
    (by rw [indices.2.2.1,hradius]; exact hj)
    (by simpa only [param0] using htbox) (by simpa only [param1] using hEbox)
    (by simpa only [quasi] using hrbox) input tape u2 bank2 z2 a2
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,bank3,ready3,good3,
    matrixEntry_natural_width emissionIds emissionIds_decode (by decide) _ _ _ width2 width3,
    outReady,?_,z3,count.trans (preframe.tapes 201 (by decide)),?_,(continuation_of_frame preframe).trans continuation⟩
  · have hbase : emissionBaseWidth B≤U := by
      dsimp [U,emissionWidth,matrixEntryWordBound,RawFree.matrixEntryWidth]
      omega
    have hold := hw 330 (by decide)
    have hs0 : 1≤(U+W+10)^2 := one_le_pow₀ (by omega)
    have hs1 : (U+3)^2≤(U+W+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have hs2 : (B+2)^2≤(U+W+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have hs3 : (emissionBaseWidth B+10)^2≤(U+W+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have hs4 : (max (emissionBaseWidth B) W+5)^2≤(U+W+10)^2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hs5 : U≤(U+W+10)^2 := by nlinarith only [Nat.zero_le U,Nat.zero_le W]
    nlinarith only [hc0,hc1,hc2,hc3,hold,hlen,hBU,hs0,hs1,hs2,hs3,hs4,hs5]
  · simpa only [emissionParts,param0,param1,quasi] using value

  · intro k hk
    exact (headers k hk).trans (preframe.tapes k (emission_protected k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      tauto)))

#print axioms emission_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
