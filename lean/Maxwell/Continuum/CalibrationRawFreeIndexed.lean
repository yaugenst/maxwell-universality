import Maxwell.Continuum.CalibrationRawFreeStaging

/-! A fixed scalar program for every entry of every actual free Fourier
block, from raw coordinates and runtime polarization indices. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def indexedFreeControl : Control := stageControl.andThen freeControl
def indexedFreeWidth (B : ℕ) : ℕ := 2^49*(B+1)
def indexedFreeCost (B : ℕ) : ℕ := 49*operationCost (indexedFreeWidth B)+1

theorem indexedFree_valid : indexedFreeControl.Valid stageRegisters := by
  apply Control.andThen_valid _ _ _ stageControl_valid
  simp [freeControl,freeTail,centralInstructions,entryControl,entryInstructions,
    Control.prepend,Control.Valid,Instruction.Valid,stageRegisters]

theorem indexedFree_steps : indexedFreeControl.steps=49 := by
  rw [indexedFreeControl,Control.andThen_steps,stageControl_steps,freeControl_steps]

theorem staged_control_keep (v : ℕ → Parts) (i j : Fin 3)
    (hg : Good stageRegisters v) (hi : (v 23).value=(i.val : ℚ))
    (hj : (v 24).value=(j.val : ℚ)) (k : ℕ)
    (hk : k≠2 ∧ k≠3 ∧ k≠4 ∧ k≠5 ∧ k≠6 ∧ k≠7 ∧ k≠19 ∧ k≠20 ∧ k≠25 ∧ k≠26 ∧ k≠27) :
    stageControl.evaluate v k=v k := by
  rw [stageControl_evaluate v i j hg hi hj]
  simp only [Function.update_of_ne hk.2.2.2.2.2.1,Function.update_of_ne hk.2.2.2.2.1,
    Function.update_of_ne hk.2.2.2.1]
  exact staged_keep v k ⟨hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.2.2.2⟩

theorem staged_control_directions (v : ℕ → Parts) (i j : Fin 3)
    (hg : Good stageRegisters v) (hi : (v 23).value=(i.val : ℚ))
    (hj : (v 24).value=(j.val : ℚ)) :
    directions (stageControl.evaluate v)=direction (coordinates v) (quasiParts v) := by
  rw [stageControl_evaluate v i j hg hi hj]
  change ![staged v 2,staged v 3,staged v 4]=_
  exact staged_directions v

theorem staged_control_selected (v : ℕ → Parts) (i j : Fin 3)
    (hg : Good stageRegisters v) (hi : (v 23).value=(i.val : ℚ))
    (hj : (v 24).value=(j.val : ℚ)) :
    stageControl.evaluate v 5=directions (stageControl.evaluate v) i ∧
    stageControl.evaluate v 6=directions (stageControl.evaluate v) j ∧
    stageControl.evaluate v 7=Parts.literal (if i=j then 1 else 0) := by
  rw [stageControl_evaluate v i j hg hi hj]
  simp [directions]

theorem indexedFree_literals (B : ℕ) (hB : 2≤B) : indexedFreeControl.LiteralsFit B := by
  apply Control.andThen_literals
  · simp [stageControl,stageTail,stageInstructions,selectDirection,selectDelta,
      Control.andThen,Control.prepend,Control.LiteralsFit,Instruction.LiteralFits,Parts.Width,Parts.literal]
    norm_num [Int.sign]
    rw [show (2:ℕ).bits.length=2 by decide]
    omega
  · simp [freeControl,freeTail,centralInstructions,entryControl,entryInstructions,
      Control.prepend,Control.LiteralsFit,Instruction.LiteralFits,Parts.Width,Parts.literal]
    omega

theorem indexedFreeCost_bound (B : ℕ) : indexedFreeCost B ≤ 2^210*(B+3)^2 := by
  have h : 2^49*(B+1)+3 ≤ 2^49*(B+3) := by omega
  have hs := Nat.pow_le_pow_left h 2
  dsimp [indexedFreeCost,indexedFreeWidth,operationCost]
  nlinarith only [hs,Nat.zero_le ((B+3)^2)]

theorem indexedFree_contract (v : ℕ → Parts) (hg : Good stageRegisters v)
    (ν : Alias) (hcoord : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (htbox : (3 : ℝ) ≤ (v 0).value)
    (hEbox : (7 : ℝ) ≤ (v 1).value ∧ ((v 1).value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((quasiParts v k).value : ℝ)| ≤ 1/16)
    (i j : Fin 3) (hi : (v 23).value=(i.val : ℚ)) (hj : (v 24).value=(j.val : ℚ)) :
    indexedFreeControl.AdmissibleTrace v ∧
      (indexedFreeControl.evaluate v 12).value=
        rationalFreeInverseMatrix (v 0).value (v 1).value (fun k => (quasiParts v k).value) ν i j := by
  let w := stageControl.evaluate v
  have goodw : Good stageRegisters w :=
    stageControl.evaluate_good stageRegisters stageControl_valid v hg (stageControl_admissible v)
  have keep (k : ℕ)
      (hk : k≠2 ∧ k≠3 ∧ k≠4 ∧ k≠5 ∧ k≠6 ∧ k≠7 ∧ k≠19 ∧ k≠20 ∧ k≠25 ∧ k≠26 ∧ k≠27) :
      w k=v k := staged_control_keep v i j hg hi hj k hk
  have h0 : w 0=v 0 := keep 0 (by omega)
  have h1 : w 1=v 1 := keep 1 (by omega)
  have coords : coordinates w=coordinates v := by
    funext k
    fin_cases k <;> simp only [coordinates]
    all_goals exact keep _ (by omega)
  have hc (k : Fin 3) : (coordinates v k).Valid := by fin_cases k <;> exact hg _ (by decide)
  have hr (k : Fin 3) : (quasiParts v k).Valid := by fin_cases k <;> exact hg _ (by decide)
  have hadir (k : Fin 3) : (directions w k).value=
      rationalDirection (fun l => (quasiParts v l).value) ν k := by
    rw [staged_control_directions v i j hg hi hj]
    exact direction_value (coordinates v) (quasiParts v) ν hc hr hcoord k
  have hEn : (w 1).value≠0 := by
    rw [h1]
    intro hz
    have hh := hEbox.1
    rw [hz,Rat.cast_zero] at hh
    norm_num at hh
  have branch : 0<(centralMetric (coordinates w)).value ↔ ¬IsCentralAlias ν := by
    rw [coords]
    exact centralMetric_pos (coordinates v) hc ν hcoord
  have hd (hp : 0<(centralMetric (coordinates w)).value) :
      (denominator (w 0) (w 1) (directions w)).value≠0 := by
    have ha (k : Fin 3) : (directions w k).Valid := by fin_cases k <;> exact goodw _ (by decide)
    rw [denominator_value _ _ _ (goodw 0 (by decide)) (goodw 1 (by decide)) ha]
    simp_rw [hadir,h0,h1]
    exact (actual_denominator_pos _ _ _ ν htbox hEbox.2 hrbox (branch.mp hp)).ne'
  have admissible := Control.andThen_admissible stageControl freeControl v
    (stageControl_admissible v) (freeControl_admissible w hEn hd)
  refine ⟨admissible,?_⟩
  rw [indexedFreeControl,Control.andThen_evaluate]
  change (freeControl.evaluate w 12).value=_
  obtain ⟨hleft,hright,hdelta⟩ := staged_control_selected v i j hg hi hj
  change w 7=Parts.literal (if i=j then 1 else 0) at hdelta
  rw [freeControl_output w i j hleft hright hdelta]
  by_cases hcentral : IsCentralAlias ν
  · have hn : ¬0<(centralMetric (coordinates w)).value := fun h => branch.mp h hcentral
    have hcheck := (rationalCentralCheck_true ν).mpr hcentral
    simp only [hn,ite_false,Parts.mul_value,hdelta,Parts.literal_value,mul_one,
      rationalFreeInverseMatrix,hcheck,ite_true,Matrix.one_apply]
  · have hp := branch.mpr hcentral
    rw [ite_eq_left hp]
    have ha (k : Fin 3) : (directions w k).Valid := by fin_cases k <;> exact goodw _ (by decide)
    simpa only [h0,h1] using (actual_entry (w 0) (w 1) (directions w) _ ν
      (goodw 0 (by decide)) (goodw 1 (by decide)) ha hadir
      (by simpa only [h0] using htbox) (by simpa only [h1] using hEbox) hrbox hcentral i j).2

theorem indexedFree_executes (v : ℕ → Parts) (B : ℕ) (hB : 2≤B)
    (hv : WidthBank stageRegisters B v) (hg : Good stageRegisters v)
    (ν : Alias) (hcoord : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (htbox : (3 : ℝ) ≤ (v 0).value)
    (hEbox : (7 : ℝ) ≤ (v 1).value ∧ ((v 1).value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((quasiParts v k).value : ℝ)| ≤ 1/16)
    (i j : Fin 3) (hi : (v 23).value=(i.val : ℚ)) (hj : (v 24).value=(j.val : ℚ))
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready stageRegisters v s) :
    ∃ cost t, Executes input tape indexedFreeControl.code cost s t ∧
      cost ≤ indexedFreeCost B ∧ Ready stageRegisters (indexedFreeControl.evaluate v) t ∧
      Good stageRegisters (indexedFreeControl.evaluate v) ∧
      WidthBank stageRegisters (indexedFreeWidth B) (indexedFreeControl.evaluate v) ∧
      (indexedFreeControl.evaluate v 12).value=
        rationalFreeInverseMatrix (v 0).value (v 1).value (fun k => (quasiParts v k).value) ν i j ∧
      BinaryPrecision.Frame (workspace stageRegisters) s.val t.val := by
  obtain ⟨admissible,value⟩ := indexedFree_contract v hg ν hcoord htbox hEbox hrbox i j hi hj
  have trace : indexedFreeControl.WidthTrace stageRegisters (indexedFreeWidth B) v := by
    simpa only [indexedFree_steps,indexedFreeWidth] using
      indexedFreeControl.automatic_widthTrace stageRegisters indexedFree_valid v B hv
        (indexedFree_literals B hB)
  obtain ⟨cost,t,he,hcost,ready,frame⟩ := indexedFreeControl.executes stageRegisters indexedFree_valid
    v _ trace hg admissible input tape s hs
  exact ⟨cost,t,he,by simpa only [indexedFreeCost,indexedFree_steps] using hcost,ready,
    indexedFreeControl.evaluate_good stageRegisters indexedFree_valid v hg admissible,
    trace.result,value,frame⟩

#print axioms indexedFree_contract
#print axioms indexedFree_executes

end Maxwell.Continuum.Calibration.RawFree
