import Maxwell.Continuum.CalibrationMatrixEntryReset
import Maxwell.Continuum.CalibrationMatrixEntryStore

/-! A complete reset between matrix-table entries retains only the radius,
flat index, and five rational parameters. Its output widths are independent
of the previously computed entry. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def cleanupList : List ℕ :=
  ((List.range' 310 23).filter (fun k => decide (k≠311 ∧ k≠330))) ++ [220,221,222,223]
def cleanupSlots : Finset ℕ := cleanupList.toFinset
def cleanupInstructions : List NatAssign.Instruction := cleanupList.map (fun k => .literal k 0)
def rawResetNaturals (v : ℕ→Parts) (n : ℕ→ℕ) (k : ℕ) : ℕ :=
  if k∈ids RawFree.neighborRegisters then dataValues (resetParts v) k else n k
def cleanNaturals (v : ℕ→Parts) (n : ℕ→ℕ) : ℕ→ℕ :=
  NatAssign.values cleanupInstructions (rawResetNaturals v n)
def runtimeResetCode : Code := .seq resetCode (NatAssign.code cleanupInstructions)

theorem cleanup_disjoint : Disjoint cleanupSlots (ids RawFree.neighborRegisters) := by decide
theorem cleanup_valid : ∀ a∈cleanupInstructions, a.Valid emissionIds := by
  intro a ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  exact (show cleanupSlots⊆emissionIds by decide) (List.mem_toFinset.mpr hk)

theorem natural_zero_list (xs : List ℕ) (n : ℕ→ℕ) (k : ℕ) :
    NatAssign.values (xs.map (fun i => NatAssign.Instruction.literal i 0)) n k=
      if k∈xs then 0 else n k := by
  induction xs generalizing n with
  | nil => simp [NatAssign.values]
  | cons a rest ih =>
    rw [List.map_cons,NatAssign.values,ih]
    by_cases hr : k∈rest <;> by_cases ha : k=a <;>
      simp [hr,ha,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem cleanNaturals_apply (v : ℕ→Parts) (n : ℕ→ℕ) (k : ℕ) :
    cleanNaturals v n k=if k∈cleanupSlots then 0 else rawResetNaturals v n k := by
  simpa only [cleanNaturals,cleanupInstructions,cleanupSlots,List.mem_toFinset] using
    natural_zero_list cleanupList (rawResetNaturals v n) k

theorem cleanNaturals_agrees (v : ℕ→Parts) (n : ℕ→ℕ) (k : ℕ)
    (hk : k∈ids RawFree.neighborRegisters) : cleanNaturals v n k=dataValues (resetParts v) k := by
  have ho : k∉cleanupSlots := fun hc => Finset.disjoint_left.mp cleanup_disjoint hc hk
  rw [cleanNaturals_apply,ite_eq_right ho,rawResetNaturals,ite_eq_left hk]

theorem cleanup_external (k : ℕ) (hk : k∈emissionIds)
    (hp : k∉ids RawFree.neighborRegisters) (hc : k∉cleanupSlots) : k=311 ∨ k=330 := by
  have hc' : k∉cleanupList := by simpa only [cleanupSlots,List.mem_toFinset] using hc
  simp only [cleanupList,List.mem_append,List.mem_filter,List.mem_range',List.mem_cons,
    List.not_mem_nil,or_false,decide_eq_true_eq] at hc'
  have hk' : (310≤k ∧ k≤332) ∨ k∈NaturalQuotient.workPorts := by
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact False.elim (hp hk)
      · exact Or.inl (Finset.mem_Icc.mp hk)
    · exact Or.inr hk
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk'
  by_contra he
  have he' : k≠311 ∧ k≠330 := by simpa only [not_or] using he
  apply hc'
  rcases hk' with hr | hr
  · exact Or.inl ⟨⟨k-310,by omega,by omega⟩,he'⟩
  · exact Or.inr hr

theorem cleanNaturals_width (v : ℕ→Parts) (n : ℕ→ℕ) (B : ℕ) (hB : 1≤B)
    (hp : ∀ k∈matrixParameters, (v k).Width B)
    (hR : (n 311).bits.length≤B) (hindex : (n 330).bits.length≤B) :
    ∀ k∈emissionIds, (cleanNaturals v n k).bits.length≤B := by
  intro k hk
  by_cases hc : k∈cleanupSlots
  · rw [cleanNaturals_apply,ite_eq_left hc]
    simp
  · by_cases hr : k∈ids RawFree.neighborRegisters
    · rw [cleanNaturals_agrees v n k hr]
      exact dataValues_width _ _ _ (reset_width v B hB hp) k hr
    · rw [cleanNaturals_apply,ite_eq_right hc,rawResetNaturals,ite_eq_right hr]
      rcases cleanup_external k hk hr hc with rfl | rfl
      · exact hR
      · exact hindex

theorem cleanNaturals_parameters (v : ℕ→Parts) (n : ℕ→ℕ) :
    cleanNaturals v n 311=n 311 ∧ cleanNaturals v n 330=n 330 ∧
      ∀ k∈NaturalQuotient.workPorts, cleanNaturals v n k=0 := by
  refine ⟨?_,?_,?_⟩
  · rw [cleanNaturals_apply,ite_eq_right (by decide : 311∉cleanupSlots),rawResetNaturals,
      ite_eq_right (by decide : 311∉ids RawFree.neighborRegisters)]
  · rw [cleanNaturals_apply,ite_eq_right (by decide : 330∉cleanupSlots),rawResetNaturals,
      ite_eq_right (by decide : 330∉ids RawFree.neighborRegisters)]
  · intro k hk
    rw [cleanNaturals_apply,ite_eq_left ((show NaturalQuotient.workPorts⊆cleanupSlots by decide) hk)]

theorem runtimeReset_executes (v : ℕ→Parts) (n : ℕ→ℕ)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k)
    (U B : ℕ) (hB : 1≤B) (hBU : B≤U)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤U)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid)
    (hR : (n 311).bits.length≤B) (hindex : (n 330).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k) :
    ∃ cost t, Executes input tape runtimeResetCode cost s t ∧ cost≤2^108*(U+3)^2 ∧
      NatAssign.Bank emissionIds (cleanNaturals v n) t.val ∧
      RationalDataflow.Ready RawFree.neighborRegisters (resetParts v) t ∧
      Good RawFree.neighborRegisters (resetParts v) ∧
      (∀ k∈emissionIds, (cleanNaturals v n k).bits.length≤B) ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      BinaryPrecision.Frame emissionChanged s.val t.val := by
  have ready : RationalDataflow.Ready RawFree.neighborRegisters v s := by
    refine ⟨?_,fun k hk => hz k (by omega)⟩
    intro k hk
    simpa only [hn k hk] using hs k (emissionIds_parts hk)
  have rawWidth : WidthBank RawFree.neighborRegisters U v :=
    data_width_all _ n v U hn (fun k hk => hw k (emissionIds_parts hk))
  obtain ⟨c0,u,e0,hc0,ready0,width0,good0,f0⟩ := reset_executes v U B (by omega) hB rawWidth hp
    input tape s ready
  have bank0 : NatAssign.Bank emissionIds (rawResetNaturals v n) u.val := by
    intro k hk
    by_cases hr : k∈ids RawFree.neighborRegisters
    · simpa only [rawResetNaturals,hr,ite_true] using ready0.1 k hr
    · have ho : k∉workspace RawFree.neighborRegisters := by
        have hge := emissionIds_ge k hk
        simp only [workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨by omega,hr⟩
      simpa only [rawResetNaturals,hr,ite_false] using
        RationalAccumulator.word_of_eq (f0.tapes k ho) (hs k hk)
  have width : ∀ k∈emissionIds, (rawResetNaturals v n k).bits.length≤U := by
    intro k hk
    by_cases hr : k∈ids RawFree.neighborRegisters
    · rw [rawResetNaturals,ite_eq_left hr]
      exact (dataValues_width _ _ _ width0 k hr).trans hBU
    · simpa only [rawResetNaturals,hr,ite_false] using hw k hk
  obtain ⟨c1,t,e1,hc1,bank1,z1,f1⟩ := fixedBankStage_executes emissionIds
    (fun k hk => by have := emissionIds_ge k hk; omega) cleanupInstructions cleanup_valid
    (by decide) (rawResetNaturals v n) U width
    (by intro a ha; obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha; simp [NatAssign.Instruction.literalWidth])
    input tape u bank0 ready0.2
  have ready1 : RationalDataflow.Ready RawFree.neighborRegisters (resetParts v) t := by
    refine ⟨?_,z1⟩
    intro k hk
    have hb := bank1 k (emissionIds_parts hk)
    change RationalAccumulator.Word t.val k (cleanNaturals v n k) at hb
    simpa only [cleanNaturals_agrees v n k hk] using hb
  have blank : ∀ k, k<5 → RationalAccumulator.Blank t.val k := by
    intro k hk
    by_cases h4 : k<4
    · exact z1 k h4
    · have he : k=4 := by omega
      subst k
      exact RationalAccumulator.blank_of_eq ((f1.tapes 4 (by decide)).trans
        (f0.tapes 4 (outside_workspace _ 4 (by decide)))) (hz 4 (by decide))
  have lift0 : BinaryPrecision.Frame emissionChanged s.val u.val := f0.mono (by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · simp only [emissionChanged,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
      tauto
    · exact Finset.mem_union_right _ (emissionIds_parts hk))
  have lift1 : BinaryPrecision.Frame emissionChanged u.val t.val := f1.mono (by
    intro k hk
    simp only [emissionChanged,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    tauto)
  refine ⟨c0+c1,t,e0.seq e1,?_,bank1,ready1,good0,
    cleanNaturals_width v n B hB (fun k hk => (hp k hk).1) hR hindex,blank,lift0.trans lift1⟩
  unfold stageCost at hc1
  have hsq : (U+2)^2≤(U+3)^2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith only [hc0,hc1,hsq,Nat.zero_le ((U+3)^2)]

#print axioms runtimeReset_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
