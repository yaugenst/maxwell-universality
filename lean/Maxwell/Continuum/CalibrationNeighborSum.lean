import Maxwell.Continuum.CalibrationNeighborControl

/-! The literal six-neighbor weight is evaluated by fixed runtime tests,
with each accepted direction added to a raw signed-pair accumulator. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def neighborLoop : List (Fin 3 × Bool) → Control
  | [] => .done
  | p::rest => (neighborControl p.1 p.2).andThen (neighborLoop rest)

def neighborPairs : List (Fin 3 × Bool) :=
  [(0,true),(0,false),(1,true),(1,false),(2,true),(2,false)]
def neighborSumControl : Control := .step (.literal 36 0) (neighborLoop neighborPairs)

theorem neighborLoop_valid (pairs : List (Fin 3 × Bool)) :
    (neighborLoop pairs).Valid neighborRegisters := by
  induction pairs with
  | nil => trivial
  | cons p rest ih => exact Control.andThen_valid _ _ _ (neighborControl_valid p.1 p.2) ih

theorem neighborLoop_admissible (pairs : List (Fin 3 × Bool)) (v : ℕ → Parts) :
    (neighborLoop pairs).AdmissibleTrace v := by
  induction pairs generalizing v with
  | nil => trivial
  | cons p rest ih =>
    exact Control.andThen_admissible _ _ v (neighborControl_admissible p.1 p.2 v) (ih _)

theorem neighborLoop_steps (pairs : List (Fin 3 × Bool)) :
    (neighborLoop pairs).steps=17*pairs.length := by
  induction pairs with
  | nil => simp [neighborLoop,Control.steps]
  | cons p rest ih => rw [neighborLoop,Control.andThen_steps,neighborControl_steps,ih,List.length_cons]; omega

theorem neighborLoop_literals (pairs : List (Fin 3 × Bool)) (B : ℕ) (hB : 2≤B) :
    (neighborLoop pairs).LiteralsFit B := by
  induction pairs with
  | nil => trivial
  | cons p rest ih => exact Control.andThen_literals _ _ B (neighborControl_literals p.1 p.2 B hB) ih

theorem neighborLoop_other (pairs : List (Fin 3 × Bool)) (v : ℕ → Parts) (k : ℕ)
    (hk : k≠32 ∧ k≠33 ∧ k≠34 ∧ k≠35 ∧ k≠36 ∧ k≠40) :
    (neighborLoop pairs).evaluate v k=v k := by
  induction pairs generalizing v with
  | nil => rfl
  | cons p rest ih =>
    rw [neighborLoop,Control.andThen_evaluate,ih,neighborControl_other p.1 p.2 v k hk]

theorem neighborLoop_value (pairs : List (Fin 3 × Bool)) (v : ℕ → Parts)
    (hg : Good neighborRegisters v) (ν μ : Alias)
    (hν : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (hμ : ∀ k, (columnCoordinates v k).value=(μ k : ℚ)) :
    ((neighborLoop pairs).evaluate v 36).value=(v 36).value+
      (pairs.map (fun p => if shiftedAlias ν p.1 p.2=μ then rationalWeight p.1 else 0)).sum := by
  induction pairs generalizing v with
  | nil => simp [neighborLoop,Control.evaluate]
  | cons p rest ih =>
    let w := (neighborControl p.1 p.2).evaluate v
    have gw : Good neighborRegisters w := (neighborControl p.1 p.2).evaluate_good
      neighborRegisters (neighborControl_valid p.1 p.2) v hg (neighborControl_admissible p.1 p.2 v)
    have hνw (k : Fin 3) : (coordinates w k).value=(ν k : ℚ) := by
      have he : coordinates w k=coordinates v k := by
        fin_cases k <;> exact neighborControl_other p.1 p.2 v _ (by omega)
      rw [he]; exact hν k
    have hμw (k : Fin 3) : (columnCoordinates w k).value=(μ k : ℚ) := by
      have he : columnCoordinates w k=columnCoordinates v k := by
        fin_cases k <;> exact neighborControl_other p.1 p.2 v _ (by omega)
      rw [he]; exact hμ k
    rw [neighborLoop,Control.andThen_evaluate,ih w gw hνw hμw]
    rw [neighborControl_value p.1 p.2 v hg ν μ hν hμ]
    simp only [List.map_cons,List.sum_cons]
    ring

theorem neighborPairs_value (ν μ : Alias) :
    (neighborPairs.map (fun p => if shiftedAlias ν p.1 p.2=μ then rationalWeight p.1 else 0)).sum=
      neighborWeight ν μ := by
  simp only [neighborPairs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    shiftedAlias,Bool.false_eq_true,ite_false,ite_true,
    neighborWeight,Fin.sum_univ_three]
  split_ifs <;> ring

theorem neighborSum_valid : neighborSumControl.Valid neighborRegisters :=
  ⟨by change 36∈Finset.range 41; decide,neighborLoop_valid _⟩
theorem neighborSum_admissible (v : ℕ → Parts) : neighborSumControl.AdmissibleTrace v :=
  ⟨trivial,neighborLoop_admissible _ _⟩
theorem neighborSum_steps : neighborSumControl.steps=103 := by
  rw [neighborSumControl,Control.steps,neighborLoop_steps]
  rfl
theorem neighborSum_literals (B : ℕ) (hB : 2≤B) : neighborSumControl.LiteralsFit B :=
  ⟨by norm_num [Instruction.LiteralFits,Parts.Width,Parts.literal]; omega,neighborLoop_literals _ B hB⟩

theorem neighborSum_other (v : ℕ → Parts) (k : ℕ)
    (hk : k≠32 ∧ k≠33 ∧ k≠34 ∧ k≠35 ∧ k≠36 ∧ k≠40) :
    neighborSumControl.evaluate v k=v k := by
  rw [neighborSumControl,Control.evaluate,neighborLoop_other _ _ k hk]
  exact Function.update_of_ne hk.2.2.2.2.1 _ _

theorem neighborSum_value (v : ℕ → Parts) (hg : Good neighborRegisters v) (ν μ : Alias)
    (hν : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (hμ : ∀ k, (columnCoordinates v k).value=(μ k : ℚ)) :
    (neighborSumControl.evaluate v 36).value=neighborWeight ν μ := by
  rw [neighborSumControl,Control.evaluate,Instruction.update]
  rw [neighborLoop_value _ _ (hg.update 36 (Parts.literal_valid 0)) ν μ
    (by intro k; fin_cases k <;> exact hν _) (by intro k; fin_cases k <;> exact hμ _)]
  simp only [Function.update_self,Parts.literal_value,zero_add,neighborPairs_value]

#print axioms neighborSum_value

end Maxwell.Continuum.Calibration.RawFree
