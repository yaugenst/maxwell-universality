import Maxwell.Continuum.CalibrationMatrixDecodeValues
import Maxwell.Continuum.RationalDataflowArray

/-! Generic lifting of runtime alias-index decoding to a larger rational bank.
Only coordinate registers change, and all five arithmetic scratch tapes return blank. -/
namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

private theorem ids_subset {S T : Finset ℕ} (h : S⊆T) : ids S⊆ids T := by
  intro k hk
  rcases Finset.mem_union.mp hk with hp|hw
  · obtain ⟨i,hi,hk⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,h hi,hk⟩)
  · exact Finset.mem_union_right _ hw

theorem decodeLoad_all_executes (S allIds : Finset ℕ)
    (hIds : ∀k∈allIds,10≤k) (hdecode : ports⊆allIds)
    (hwork : NaturalQuotient.workPorts⊆allIds) (hparts : ids S⊆allIds)
    (stage : RawFree.stageRegisters⊆S) (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀k∈ids S,n k=dataValues v k)
    (hzwork : ∀k∈NaturalQuotient.workPorts,n k=0) (hg : Good S v)
    (B : ℕ) (hB : 2≤B) (hw : ∀k∈allIds,(n k).bits.length≤B)
    (R : ℕ) (i : Fin (aliasArraySize R)) (hR : n 311=R) (hi : n 310=i.val)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank allIds n s.val)
    (hz : ∀k,k<5 → RationalAccumulator.Blank s.val k) :
    ∃cost t,Executes input tape decodeLoadCode cost s t ∧ cost≤2^112*(B+5)^2 ∧
      NatAssign.Bank allIds (NatAssign.values coordinateLoad (output n)) t.val ∧
      Ready S (loadedParts v (output n)) t ∧ Good S (loadedParts v (output n)) ∧
      WidthBank S (2*B+8) (loadedParts v (output n)) ∧
      (∀k∈allIds,(NatAssign.values coordinateLoad (output n) k).bits.length≤2*B+8) ∧
      ((loadedParts v (output n) 13).value=(arrayAliasAt R i 0:ℚ) ∧
        (loadedParts v (output n) 14).value=(arrayAliasAt R i 1:ℚ) ∧
        (loadedParts v (output n) 15).value=(arrayAliasAt R i 2:ℚ)) ∧
      (loadedParts v (output n) 23).value=((arrayPolarizationAt R i).val:ℚ) ∧
      RationalAccumulator.Blank t.val 4 ∧ BinaryPrecision.Frame ({0,1,2,3,4} ∪ allIds) s.val t.val := by
  have stageIds := ids_subset stage
  obtain ⟨cd,ud,ed,hcd,bd,zd,fd⟩ := ArrayDecodeMachine.executes allIds hIds
    hdecode hwork n hzwork B (by omega) hw input tape s hs hz
  have widthDecoded := output_width n allIds hdecode B hw
  obtain ⟨cl,u,el,hcl,b0,r0,fl⟩ := coordinateLoad_executes allIds
    (fun k hk => by have := hIds k hk;omega) hdecode
    (fun _ hk => hparts (stageIds hk)) (output n) v
    (fun k hk => output_agrees_all S n v hn k (stageIds hk)) (2*B+8) (by omega)
    widthDecoded input tape ud bd (fun k hk => zd k (by omega))
  have e0 : Executes input tape decodeLoadCode (cd+cl) s u := by
    unfold decodeLoadCode
    exact ed.seq el
  have hc0 : cd+cl≤2^112*(B+5)^2 := by
    have hsquare : (2*B+8+2)^2=4*(B+5)^2 := by ring
    rw [hsquare] at hcl
    nlinarith only [hcd,hcl,Nat.zero_le ((B+5)^2)]
  have fl' : BinaryPrecision.Frame ({0,1,2,3,4} ∪ allIds) ud.val u.val := fl.mono (by
    intro k hk
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    tauto)
  have f0 : BinaryPrecision.Frame ({0,1,2,3,4} ∪ allIds) s.val u.val := fd.trans fl'
  have four : RationalAccumulator.Blank u.val 4 := RationalAccumulator.blank_of_eq
    (fl.tapes 4 (by
      have hn : 4∉allIds := fun h => by have := hIds 4 h;omega
      simp [hn])) (zd 4 (by decide))
  have coord := loadedParts_coordinates v (output n) R i (by rw [output_radius,hR])
    (fun k => by simpa only [hR,hi] using output_coordinates n k)
  have pol := loadedParts_polarization v (output n) R i (by rw [output_polarization,hi])
  let w := loadedParts v (output n)
  let nn := NatAssign.values coordinateLoad (output n)
  have agree : ∀k∈ids S,nn k=dataValues w k :=
    coordinateLoad_agrees (output n) v S (output_agrees_all S n v hn)
  have widthNat : ∀k∈allIds,(nn k).bits.length≤2*B+8 :=
    coordinateLoad_width _ allIds hdecode _ (by omega)
      (output_width n allIds hdecode B hw)
  have width : WidthBank S (2*B+8) w := data_width_all S nn w _ agree
    (fun k hk => widthNat k (hparts hk))
  have good : Good S w := by
    apply Good.update (Good.update (Good.update (Good.update hg 13 ?_) 14 ?_) 15 ?_) 23 ?_
    all_goals change 0<1; decide
  have ready : Ready S w u := ⟨fun k hk => by
    have hb := b0 k (hparts hk)
    change RationalAccumulator.Word u.val k (nn k) at hb
    rw [agree k hk] at hb
    exact hb,r0.2⟩
  have coordinates : (w 13).value=(arrayAliasAt R i 0:ℚ) ∧
      (w 14).value=(arrayAliasAt R i 1:ℚ) ∧ (w 15).value=(arrayAliasAt R i 2:ℚ) := by
    have h (j : Fin 3) := (congrArg Parts.value (coord j)).trans (RawFree.coordinatePart_value R i j)
    exact ⟨h 0,h 1,h 2⟩
  exact ⟨cd+cl,u,e0,hc0,b0,ready,good,width,widthNat,coordinates,pol,four,f0⟩


#print axioms decodeLoad_all_executes
end Maxwell.Continuum.Calibration.ArrayDecodeMachine
