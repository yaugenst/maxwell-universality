import Maxwell.Continuum.CalibrationMatrixDecodeExecution

/-! Runtime row/column decoding and scalar arithmetic are one fixed
Boolean-machine program for the actual cached transition matrix. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def matrixEntryCode : Code := .seq matrixDecodeCode RawFree.matrixControl.code
def matrixEntryOutput (v : ℕ → Parts) (n : ℕ → ℕ) : ℕ → Parts :=
  RawFree.matrixControl.evaluate (matrixParts v n)
def matrixEntryWordBound (B : ℕ) : ℕ := RawFree.matrixEntryWidth (4*B+24)
def matrixEntryNaturals (v : ℕ → Parts) (n : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k∈ids RawFree.neighborRegisters then dataValues (matrixEntryOutput v n) k else matrixNaturals n k

theorem matrixEntry_executes (allIds : Finset ℕ) (hIds : ∀ k ∈ allIds, 10≤k)
    (hdecode : ports ⊆ allIds) (hwork : NaturalQuotient.workPorts ⊆ allIds)
    (hparts : ids RawFree.neighborRegisters ⊆ allIds) (hrow : 321∈allIds)
    (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀ k ∈ ids RawFree.neighborRegisters, n k=dataValues v k)
    (hzwork : ∀ k ∈ NaturalQuotient.workPorts, n k=0)
    (hg : Good RawFree.neighborRegisters v) (B : ℕ) (hB : 101≤B)
    (hw : ∀ k ∈ allIds, (n k).bits.length≤B)
    (R : ℕ) (i j : Fin (aliasArraySize R)) (hR : n 311=R) (hi : n 321=i.val) (hj : n 310=j.val)
    (htbox : (3 : ℝ) ≤ (v 0).value)
    (hEbox : (7 : ℝ) ≤ (v 1).value ∧ ((v 1).value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((RawFree.quasiParts v k).value : ℝ)| ≤ 1/16)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank allIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k) :
    ∃ cost t, Executes input tape matrixEntryCode cost s t ∧ cost≤2^510*(B+10)^2 ∧
      NatAssign.Bank allIds (matrixEntryNaturals v n) t.val ∧
      RationalDataflow.Ready RawFree.neighborRegisters (matrixEntryOutput v n) t ∧
      Good RawFree.neighborRegisters (matrixEntryOutput v n) ∧
      WidthBank RawFree.neighborRegisters (matrixEntryWordBound B) (matrixEntryOutput v n) ∧
      (matrixEntryOutput v n 12).value=cachedTransitionMatrix (v 0).value (v 1).value
        (fun k => (RawFree.quasiParts v k).value) R i j ∧
      BinaryPrecision.Frame ({0,1,2,3,4} ∪ allIds) s.val t.val ∧
      RationalAccumulator.Blank t.val 4 := by
  obtain ⟨c0,u,e0,hc0,bank0,ready,gout,wout,rowc,rowp,colc,colp,f0,z04⟩ := matrixDecode_executes
    allIds hIds hdecode hwork hparts hrow n v hn hzwork hg B (by omega) hw R i j hR hi hj input tape s hs hz
  have h0 : matrixParts v n 0=v 0 := matrixParts_input n v 0 (by omega)
  have h1 : matrixParts v n 1=v 1 := matrixParts_input n v 1 (by omega)
  have hr : RawFree.quasiParts (matrixParts v n)=RawFree.quasiParts v := by
    funext k
    fin_cases k
    · exact matrixParts_input n v 16 (by omega)
    · exact matrixParts_input n v 17 (by omega)
    · exact matrixParts_input n v 18 (by omega)
  obtain ⟨c1,t,e1,hc1,ready1,gout1,wout1,value,f1⟩ := RawFree.matrixEntry_executes
    RawFree.neighborRegisters (fun _ h => h) (matrixParts v n) (4*B+24) (by omega) wout gout
    (arrayAliasAt R i) (arrayAliasAt R j)
    (fun k => by rw [rowc k]; exact RawFree.coordinatePart_value R i k)
    (fun k => by rw [colc k]; exact RawFree.coordinatePart_value R j k)
    (by simpa only [h0] using htbox) (by simpa only [h1] using hEbox)
    (by simpa only [hr] using hrbox) (arrayPolarizationAt R i) (arrayPolarizationAt R j) rowp colp
    input tape u ready
  have f1' : BinaryPrecision.Frame ({0,1,2,3,4} ∪ allIds) u.val t.val := by
    apply f1.mono
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      tauto
    · exact Finset.mem_union_right _ (hparts hk)
  have bank : NatAssign.Bank allIds (matrixEntryNaturals v n) t.val := by
    intro k hk
    by_cases hp : k∈ids RawFree.neighborRegisters
    · simpa only [matrixEntryNaturals,hp,ite_true,matrixEntryOutput] using ready1.1 k hp
    · have hn : k∉workspace RawFree.neighborRegisters := by
        have hge := hIds k hk
        intro hmem
        rcases Finset.mem_union.mp hmem with hsmall | hlarge
        · simp only [Finset.mem_insert,Finset.mem_singleton] at hsmall
          omega
        · exact hp hlarge
      simpa only [matrixEntryNaturals,hp,ite_false] using RationalAccumulator.word_of_eq
        (f1.tapes k hn) (bank0 k hk)
  refine ⟨c0+c1,t,e0.seq e1,?_,bank,ready1,gout1,wout1,?_,f0.trans f1',
    RationalAccumulator.blank_of_eq (f1.tapes 4 (by decide)) z04⟩
  · have hc := hc1.trans (RawFree.matrixEntryCost_bound (4*B+24))
    have hsq : (4*B+24+3)^2≤16*(B+10)^2 := by nlinarith [Nat.zero_le B]
    nlinarith only [hc0,hc,hsq,Nat.zero_le ((B+10)^2)]
  · simpa only [matrixEntryOutput,h0,h1,hr,cachedTransitionMatrix_entry] using value

theorem matrixEntry_natural_width (allIds : Finset ℕ) (hdecode : ports ⊆ allIds) (hrow : 321∈allIds)
    (n : ℕ → ℕ) (v : ℕ → Parts) (B : ℕ) (hw : ∀ k∈allIds, (n k).bits.length≤B)
    (hv : WidthBank RawFree.neighborRegisters (matrixEntryWordBound B) (matrixEntryOutput v n)) :
    ∀ k∈allIds, (matrixEntryNaturals v n k).bits.length≤matrixEntryWordBound B := by
  intro k hk
  by_cases hp : k∈ids RawFree.neighborRegisters
  · rw [matrixEntryNaturals,ite_eq_left hp]
    exact dataValues_width _ _ _ hv k hp
  · rw [matrixEntryNaturals,ite_eq_right hp]
    apply (matrixNaturals_width allIds hdecode hrow n B hw k hk).trans
    unfold matrixEntryWordBound RawFree.matrixEntryWidth
    omega

#print axioms matrixEntry_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
