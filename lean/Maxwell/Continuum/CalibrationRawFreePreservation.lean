import Maxwell.Continuum.CalibrationRawFreeIndexed
import Maxwell.Continuum.RationalDataflowSubbank

/-! The fixed free-entry fragment preserves its physical input registers,
and can be embedded in a larger coefficient-table register bank. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def instructionTarget : Instruction → ℕ
  | .literal target _ => target
  | .binary _ target _ _ => target
  | .inverse target _ => target

theorem evaluate_untouched (ins : List Instruction) (v : ℕ → Parts) (k : ℕ)
    (hk : ∀ a ∈ ins, instructionTarget a≠k) : RationalDataflow.evaluate ins v k=v k := by
  induction ins generalizing v with
  | nil => rfl
  | cons a rest ih =>
    rw [RationalDataflow.evaluate,ih (a.update v) (fun b hb => hk b (by simp [hb]))]
    have ha := hk a (by simp)
    cases a <;> exact Function.update_of_ne ha.symm _ _

theorem selectDirection_other (v : ℕ → Parts) (target index minusOne k : ℕ) (hk : k≠target) :
    (selectDirection target index minusOne).evaluate v k=v k := by
  simp only [selectDirection,Control.evaluate,Instruction.update]
  split_ifs <;> exact Function.update_of_ne hk _ _

theorem selectDelta_other (v : ℕ → Parts) (k : ℕ) (hk : k≠7) :
    selectDelta.evaluate v k=v k := by
  simp only [selectDelta,Control.evaluate,Instruction.update]
  split_ifs <;> exact Function.update_of_ne hk _ _

theorem stageControl_other (v : ℕ → Parts) (k : ℕ)
    (hk : k<2 ∨ 12<k ∧ k<19 ∨ 22<k ∧ k<25 ∨ 27<k) :
    stageControl.evaluate v k=v k := by
  rw [stageControl,Control.prepend_evaluate]
  change stageTail.evaluate (staged v) k=_
  rw [stageTail,Control.andThen_evaluate,Control.andThen_evaluate,
    selectDelta_other _ k (by omega),selectDirection_other _ 6 24 26 k (by omega),
    selectDirection_other _ 5 23 25 k (by omega)]
  exact staged_keep v k (by omega)

theorem centralAfter_other (v : ℕ → Parts) (k : ℕ) (hk : k≠20 ∧ k≠21 ∧ k≠22) :
    centralAfter v k=v k := by
  simp [centralAfter,centralInstructions,RationalDataflow.evaluate,Instruction.update,hk.1,hk.2.1,hk.2.2]

theorem entryControl_other (v : ℕ → Parts) (k : ℕ) (hk : k<8 ∨ 12<k) :
    entryControl.evaluate v k=v k := by
  rw [entryControl,Control.prepend_evaluate]
  apply evaluate_untouched
  simp [entryInstructions,instructionTarget]
  omega

theorem freeControl_other (v : ℕ → Parts) (k : ℕ)
    (hk : k<8 ∨ 12<k ∧ k<20 ∨ 22<k) : freeControl.evaluate v k=v k := by
  rw [freeControl,Control.prepend_evaluate]
  change freeTail.evaluate (centralAfter v) k=_
  by_cases hp : 0<(centralAfter v 21).value
  · rw [freeTail,Control.evaluate,ite_eq_left hp,
      entryControl_other _ k (by omega),centralAfter_other v k (by omega)]
  · rw [freeTail,Control.evaluate,ite_eq_right hp]
    simp only [Control.evaluate,Instruction.update,Function.update_of_ne (show k≠12 by omega)]
    exact centralAfter_other v k (by omega)

theorem indexedFree_other (v : ℕ → Parts) (k : ℕ)
    (hk : k<2 ∨ 12<k ∧ k<19 ∨ 22<k ∧ k<25 ∨ 27<k) :
    indexedFreeControl.evaluate v k=v k := by
  rw [indexedFreeControl,Control.andThen_evaluate,freeControl_other _ k (by omega),stageControl_other v k hk]

theorem indexedFree_extended (S : Finset ℕ) (hS : stageRegisters ⊆ S)
    (v : ℕ → Parts) (B : ℕ) (hB : 2≤B) (hv : WidthBank S B v) (hg : Good S v)
    (ν : Alias) (hcoord : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (htbox : (3 : ℝ) ≤ (v 0).value)
    (hEbox : (7 : ℝ) ≤ (v 1).value ∧ ((v 1).value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((quasiParts v k).value : ℝ)| ≤ 1/16)
    (i j : Fin 3) (hi : (v 23).value=(i.val : ℚ)) (hj : (v 24).value=(j.val : ℚ))
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape indexedFreeControl.code cost s t ∧
      cost ≤ indexedFreeCost B ∧ Ready S (indexedFreeControl.evaluate v) t ∧
      Good S (indexedFreeControl.evaluate v) ∧
      WidthBank S (indexedFreeWidth B) (indexedFreeControl.evaluate v) ∧
      (indexedFreeControl.evaluate v 12).value=
        rationalFreeInverseMatrix (v 0).value (v 1).value (fun k => (quasiParts v k).value) ν i j ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨admissible,value⟩ := indexedFree_contract v (fun k hk => hg k (hS hk))
    ν hcoord htbox hEbox hrbox i j hi hj
  have valid := indexedFree_valid.mono hS
  have trace : indexedFreeControl.WidthTrace S (indexedFreeWidth B) v := by
    simpa only [indexedFree_steps,indexedFreeWidth] using
      indexedFreeControl.automatic_widthTrace S valid v B hv (indexedFree_literals B hB)
  obtain ⟨cost,t,he,hcost,ready,frame⟩ := indexedFreeControl.executes S valid v _ trace hg admissible input tape s hs
  exact ⟨cost,t,he,by simpa only [indexedFreeCost,indexedFree_steps] using hcost,ready,
    indexedFreeControl.evaluate_good S valid v hg admissible,trace.result,value,frame⟩

#print axioms indexedFree_extended

end Maxwell.Continuum.Calibration.RawFree
