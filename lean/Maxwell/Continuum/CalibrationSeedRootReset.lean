import Maxwell.Continuum.CalibrationSeedRootRowMachine
import Maxwell.Continuum.CalibrationSeedRootEmission
import Maxwell.Continuum.RationalDataflowResetInvariant

/-! Charged reset of one output producer's temporary banks. Only geometry,
row coordinates and seed components survive, so entry widths do not recur. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def fixedFields : Finset ℕ := {750,751,752,753,754,755,780,785,786,787,788}
def resetTargets : List ℕ := [30,31,32,33,34,35,36,220,221,222,223,310,311,312,313,314,315,316,317,318,319,320]++
  ((List.range 50).map (750+·)).filter (fun i=>i∉fixedFields)
def resetPlan : List NatAssign.Instruction := resetTargets.map (fun i=>.literal i 0)
def resetNumbers (n : ℕ→ℕ) := NatAssign.values resetPlan n
def resetParts (v : ℕ→Parts) := (resetList [24,25,26,27]).evaluate v
def resetCode : Code := .seq (NatAssign.code resetPlan) (resetList [24,25,26,27]).code
def resetCost (U : ℕ) : ℕ := 3000*8^resetPlan.length*(U+2)^2+(4*operationCost U+1)

theorem resetTargets_set : resetTargets.toFinset=rowIds\fixedFields := by decide
theorem resetTargets_mem (i : ℕ) : i∈resetTargets ↔ i∈rowIds ∧ i∉fixedFields := by
  rw [←List.mem_toFinset,resetTargets_set,Finset.mem_sdiff]
theorem resetPlan_valid : ∀a∈resetPlan,a.Valid rowIds := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  exact (resetTargets_mem i).mp hi |>.1
theorem resetNumbers_value (n : ℕ→ℕ) (i : ℕ) :
    resetNumbers n i=if i∈rowIds ∧ i∉fixedFields then 0 else n i := by
  simp only [resetNumbers,resetPlan,NatAssign.values_literals,resetTargets_mem]
theorem resetNumbers_keep (n : ℕ→ℕ) (i : ℕ) (hi : i∈fixedFields) : resetNumbers n i=n i := by
  simp [resetNumbers_value,hi]
theorem resetNumbers_width (n : ℕ→ℕ) (B : ℕ) (h : ∀i∈fixedFields,(n i).bits.length≤B) :
    ∀i∈rowIds,(resetNumbers n i).bits.length≤B := by
  intro i hi
  by_cases hf : i∈fixedFields
  · rw [resetNumbers_keep n i hf]
    exact h i hf
  · simp [resetNumbers_value,hi,hf]

theorem rational_ready_after_row {v : ℕ→Parts} {s t : Store}
    (ready : Ready slots v s) (frame : BinaryPrecision.Frame rowWorkspace s.val t.val)
    (scratch : NatAssign.Scratch t.val)
    (zero : ∀i∈RationalMagnitude.ids,RationalAccumulator.Word t.val i 0) :
    Ready slots v t := by
  refine ⟨?_,scratch⟩
  intro i hi
  by_cases hm : i∈RationalMagnitude.ids
  · have lower : i<1000 := by
      simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hm
      omega
    rw [dataValues_small v lower]
    exact zero i hm
  have outside : i∉rowWorkspace := by
    have disjoint : Disjoint rowWorkspace (RationalDataflow.ids slots\RationalMagnitude.ids) := by decide
    exact fun hin=>Finset.disjoint_left.mp disjoint hin (Finset.mem_sdiff.mpr ⟨hi,hm⟩)
  exact RationalAccumulator.word_of_eq (frame.tapes i outside) (ready.1 i hi)

theorem reset_executes (n : ℕ→ℕ) (v : ℕ→Parts) (U B : ℕ) (hB : 1≤B) (hBU : B≤U)
    (nw : ∀i∈rowIds,(n i).bits.length≤U) (rw : WidthBank slots U v) (good : Good slots v)
    (fixed : ∀i∈fixedFields,(n i).bits.length≤B)
    (seed : ∀i∈slots,i∉([24,25,26,27]:List ℕ)→(v i).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (natural : NatAssign.Bank rowIds n s.val) (ready : Ready slots v s) :
    ∃cost t,Executes input tape resetCode cost s t ∧ cost≤resetCost U ∧
      NatAssign.Bank rowIds (resetNumbers n) t.val ∧
      (∀i∈rowIds,(resetNumbers n i).bits.length≤B) ∧
      Ready slots (resetParts v) t ∧ Good slots (resetParts v) ∧ WidthBank slots B (resetParts v) ∧
      BinaryPrecision.Frame (rowWorkspace∪RationalDataflow.workspace slots) s.val t.val ∧
      t.val.tapes 4=s.val.tapes 4 := by
  obtain ⟨c0,u,e0,h0,nu,zu,f0⟩ := NatAssign.executes rowIds
    (fun i hi=>(by decide : 4≤10).trans (rowIds_lower i hi)) resetPlan resetPlan_valid n
    input tape s natural ready.2
  change NatAssign.Bank rowIds (resetNumbers n) u.val at nu
  have f0' : BinaryPrecision.Frame rowWorkspace s.val u.val :=
    f0.mono ((NatAssign.changes_subset rowIds resetPlan resetPlan_valid).trans (by decide))
  have zero (i : ℕ) (hi : i∈RationalMagnitude.ids) : RationalAccumulator.Word u.val i 0 := by
    have hr : i∈rowIds := (by decide : RationalMagnitude.ids⊆rowIds) hi
    have hf : i∉fixedFields := fun hh=>(Finset.disjoint_left.mp
      (by decide : Disjoint RationalMagnitude.ids fixedFields)) hi hh
    simpa [resetNumbers_value,hr,hf] using nu i hr
  have ru := rational_ready_after_row ready f0' zu zero
  obtain ⟨c1,t,e1,h1,rt,f1⟩ := resetList_executes slots [24,25,26,27] (by decide)
    v U (by omega) rw good input tape u ru
  have nt : NatAssign.Bank rowIds (resetNumbers n) t.val := by
    intro i hi
    by_cases hm : i∈RationalMagnitude.ids
    · have lo : i<1000 := by
        simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hm
        omega
      have hf : i∉fixedFields := by
        simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hm
        simp only [fixedFields,Finset.mem_insert,Finset.mem_singleton]
        omega
      rw [resetNumbers_value,ite_eq_left ⟨hi,hf⟩]
      have hh := rt.1 i (Finset.mem_union_right _ (Finset.mem_union_right _ hm))
      rwa [dataValues_small _ lo] at hh
    · have outside : i∉RationalDataflow.workspace slots := by
        have bounds := hi
        simp only [rowIds,ids,extra,SelectedParameters.Compare.ids,ArrayDecodeMachine.ports,
          NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,
          Finset.mem_singleton] at bounds
        simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton,not_or] at hm
        apply outside_workspace slots i
        omega
      exact RationalAccumulator.word_of_eq (f1.tapes i outside) (nu i hi)
  have literalWidth : ∀a∈resetPlan,a.literalWidth≤U := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    simp [NatAssign.Instruction.literalWidth]
  have price := NatAssign.price_bound rowIds resetPlan resetPlan_valid n U nw literalWidth
  exact ⟨c0+c1,t,e0.seq e1,Nat.add_le_add (h0.trans price) h1,nt,resetNumbers_width n B fixed,rt,
    resetList_result_good slots _ v (fun i hi _=>good i hi),
    resetList_result_width slots _ v B hB seed,
    (f0'.mono (Finset.subset_union_left)).trans (f1.mono Finset.subset_union_right),
    (f1.tapes 4 (by decide)).trans (f0.tapes 4 (by decide))⟩

#print axioms reset_executes
end Maxwell.Continuum.Calibration.SeedRoot
