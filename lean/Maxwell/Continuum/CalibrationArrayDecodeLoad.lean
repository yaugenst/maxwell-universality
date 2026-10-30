import Maxwell.Continuum.CalibrationArrayCoordinateLoad

/-! Runtime index decoding followed by the charged transfer to the actual
rational coordinate registers. All unsigned coordinates and polarization
values in the final bank are derived from the input index. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def decodeLoadCode : Code := .seq code (NatAssign.code coordinateLoad)

theorem output_outside (n : ℕ → ℕ) (k : ℕ) (hk : k ∉ ports) : output n k=n k := by
  have hh : k<310 ∨ 320<k := by simp only [ports,Finset.mem_Icc,not_and_or,not_le] at hk; exact hk
  simp only [output,second,first,divModValues,
    Function.update_of_ne (show k≠320 by omega),Function.update_of_ne (show k≠319 by omega),
    Function.update_of_ne (show k≠318 by omega),Function.update_of_ne (show k≠317 by omega),
    Function.update_of_ne (show k≠316 by omega),Function.update_of_ne (show k≠315 by omega)]
  exact prepared_other n k (by omega) (by omega) (by omega)

theorem output_radius (n : ℕ → ℕ) : output n 311=n 311 := by
  simp only [output,second,first,divModValues,Function.update_of_ne (by decide : (311:ℕ)≠320),
    Function.update_of_ne (by decide : (311:ℕ)≠319),Function.update_of_ne (by decide : (311:ℕ)≠318),
    Function.update_of_ne (by decide : (311:ℕ)≠317),Function.update_of_ne (by decide : (311:ℕ)≠316),
    Function.update_of_ne (by decide : (311:ℕ)≠315)]
  exact prepared_other n 311 (by decide) (by decide) (by decide)

theorem rational_port_outside (k : ℕ) (hk : k ∈ ids RawFree.stageRegisters) : k ∉ ports := by
  rcases Finset.mem_union.mp hk with hp | hw
  · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    have h0 := positivePort_ge i
    have h1 := negativePort_ge i
    have h2 := denominatorPort_ge i
    simp only [ports,Finset.mem_Icc]
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hw
    simp only [ports,Finset.mem_Icc]
    omega

theorem output_agrees (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀ k ∈ ids RawFree.stageRegisters, n k=dataValues v k) :
    ∀ k ∈ ids RawFree.stageRegisters, output n k=dataValues v k := by
  intro k hk
  rw [output_outside n k (rational_port_outside k hk),hn k hk]

theorem output_width (n : ℕ → ℕ) (allIds : Finset ℕ) (hports : ports ⊆ allIds) (B : ℕ)
    (hw : ∀ k ∈ allIds, (n k).bits.length≤B) :
    ∀ k ∈ allIds, (output n k).bits.length≤2*B+8 := by
  have hp := prepared_width n allIds hports B hw
  have h1 := divModValues_width (prepared n) allIds 310 312 315 316 (2*B+8) (hports (by decide)) hp
  have h2 := divModValues_width (first n) allIds 315 314 317 318 (2*B+8) (hports (by decide)) h1
  exact divModValues_width (second n) allIds 318 313 319 320 (2*B+8) (hports (by decide)) h2

theorem loadedParts_good (v : ℕ → Parts) (n : ℕ → ℕ) (hg : Good RawFree.stageRegisters v) :
    Good RawFree.stageRegisters (loadedParts v n) :=
  (((hg.update 13 (by change 0<1; decide : (⟨n 317,n 311,1⟩:Parts).Valid)).update
    14 (by change 0<1; decide : (⟨n 319,n 311,1⟩:Parts).Valid)).update
    15 (by change 0<1; decide : (⟨n 320,n 311,1⟩:Parts).Valid)).update
    23 (by change 0<1; decide : (⟨n 316,0,1⟩:Parts).Valid)

theorem loadedParts_width (v : ℕ → Parts) (n : ℕ → ℕ) (B : ℕ) (hB : 1≤B)
    (hv : WidthBank RawFree.stageRegisters B v)
    (hn : ∀ k ∈ ports, (n k).bits.length≤B) :
    WidthBank RawFree.stageRegisters B (loadedParts v n) := by
  have h (a b : ℕ) (ha : a ∈ ports) (hb : b ∈ ports) :
      (⟨n a,n b,1⟩:Parts).Width B := ⟨hn a ha,hn b hb,by simpa using hB⟩
  have hp : (⟨n 316,0,1⟩:Parts).Width B := ⟨hn 316 (by decide),by simp,by simpa using hB⟩
  exact (((hv.update 13 (h 317 311 (by decide) (by decide))).update
    14 (h 319 311 (by decide) (by decide))).update
    15 (h 320 311 (by decide) (by decide))).update 23 hp

theorem data_width (n : ℕ → ℕ) (v : ℕ → Parts) (B : ℕ)
    (hn : ∀ k ∈ ids RawFree.stageRegisters, n k=dataValues v k)
    (hw : ∀ k ∈ ids RawFree.stageRegisters, (n k).bits.length≤B) :
    WidthBank RawFree.stageRegisters B v := by
  intro i hi
  have hp := hw (positivePort i) (cell_mem hi (by simp [cellPorts]))
  have hm := hw (negativePort i) (cell_mem hi (by simp [cellPorts]))
  have hd := hw (denominatorPort i) (cell_mem hi (by simp [cellPorts]))
  rw [hn _ (cell_mem hi (by simp [cellPorts])),dataValues_positive] at hp
  rw [hn _ (cell_mem hi (by simp [cellPorts])),dataValues_negative] at hm
  rw [hn _ (cell_mem hi (by simp [cellPorts])),dataValues_denominator] at hd
  exact ⟨hp,hm,hd⟩

theorem decodeLoad_executes (allIds : Finset ℕ) (hIds : ∀ k ∈ allIds, 10≤k)
    (hdecode : ports ⊆ allIds) (hwork : NaturalQuotient.workPorts ⊆ allIds)
    (hparts : ids RawFree.stageRegisters ⊆ allIds)
    (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀ k ∈ ids RawFree.stageRegisters, n k=dataValues v k)
    (hzwork : ∀ k ∈ NaturalQuotient.workPorts, n k=0)
    (hg : Good RawFree.stageRegisters v) (B : ℕ) (hB : 2≤B)
    (hw : ∀ k ∈ allIds, (n k).bits.length≤B)
    (R : ℕ) (i : Fin (aliasArraySize R)) (hR : n 311=R) (hi : n 310=i.val)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank allIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k) :
    ∃ cost t, Executes input tape decodeLoadCode cost s t ∧ cost≤2^112*(B+5)^2 ∧
      NatAssign.Bank allIds (NatAssign.values coordinateLoad (output n)) t.val ∧
      RationalDataflow.Ready RawFree.stageRegisters (loadedParts v (output n)) t ∧
      Good RawFree.stageRegisters (loadedParts v (output n)) ∧
      WidthBank RawFree.stageRegisters (2*B+8) (loadedParts v (output n)) ∧
      (∀ k, RawFree.coordinates (loadedParts v (output n)) k=RawFree.coordinatePart R i k) ∧
      (loadedParts v (output n) 23).value=((arrayPolarizationAt R i).val : ℚ) ∧
      BinaryPrecision.Frame ({0,1,2,3,4} ∪ allIds) s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := executes allIds hIds hdecode hwork n hzwork B hB hw input tape s hs hz
  have w0 := output_width n allIds hdecode B hw
  obtain ⟨c1,t,e1,hc1,b1,ready,f1⟩ := coordinateLoad_executes allIds
    (fun k hk => by have := hIds k hk; omega) hdecode hparts (output n) v (output_agrees n v hn)
    (2*B+8) (by omega) w0 input tape u b0 (fun k hk => z0 k (by omega))
  have f1' : BinaryPrecision.Frame ({0,1,2,3,4} ∪ allIds) u.val t.val :=
    f1.mono (by intro k hk; simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk ⊢; tauto)
  have vw := data_width n v B hn (fun k hk => hw k (hparts hk))
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,ready,loadedParts_good v _ hg,
    loadedParts_width v _ _ (by omega) (vw.mono (by omega)) (fun k hk => w0 k (hdecode hk)),
    loadedParts_coordinates v _ R i (by rw [output_radius,hR])
      (fun k => by simpa only [hR,hi] using output_coordinates n k),
    loadedParts_polarization v _ R i (by rw [output_polarization,hi]),f0.trans f1'⟩
  have hsq : (2*B+8+2)^2=4*(B+5)^2 := by ring
  rw [hsq] at hc1
  nlinarith only [hc0,hc1,Nat.zero_le ((B+5)^2)]

#print axioms decodeLoad_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
