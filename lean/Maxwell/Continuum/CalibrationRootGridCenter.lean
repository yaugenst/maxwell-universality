import Maxwell.Continuum.CalibrationRootProductMachine
import Maxwell.Continuum.CalibrationFractionWord

/-! Exact centering of the three rational grid coordinates.  The half-grid
point follows the paper's positive-half convention, including equality. -/
namespace Maxwell.Continuum.RationalDataflow.RootGridCenter
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def inputs : Finset ℕ := RootProduct.inputs∪{9}
def centeredPart (x : Parts) : Parts := if (1/2:ℚ)<x.value then x.sub (Parts.literal 1) else x
def center (i : ℕ) : Control := .step (.literal 3 (1/2))
  (.step (.binary .sub 4 i 3)
    (.positive 4 (.step (.literal 3 1) (.step (.binary .sub i i 3) .done)) .done))
def first (v : ℕ→Parts) := (center 0).evaluate v
def second (v : ℕ→Parts) := (center 1).evaluate (first v)
def centered (v : ℕ→Parts) := (center 2).evaluate (second v)
def scale : Control := Control.prepend
  [.binary .mul 0 0 9,.binary .mul 1 1 9,.binary .mul 2 2 9] .done
def values (v : ℕ→Parts) := scale.evaluate (centered v)
def code : Code := .seq (center 0).code
  (.seq (center 1).code (.seq (center 2).code scale.code))

theorem centeredPart_valid (x : Parts) (hx : x.Valid) : (centeredPart x).Valid := by
  unfold centeredPart
  split_ifs
  · exact Parts.sub_valid hx (Parts.literal_valid 1)
  · exact hx

theorem centeredPart_value (x : Parts) (hx : x.Valid) :
    (centeredPart x).value=if (1/2:ℚ)<x.value then x.value-1 else x.value := by
  unfold centeredPart
  split_ifs
  · rw [Parts.sub_value _ _ hx (Parts.literal_valid 1),Parts.literal_value]
  · rfl

theorem centeredPart_width (x : Parts) (B : ℕ) (hx : x.Width B) :
    (centeredPart x).Width (B+2) := by
  unfold centeredPart
  split_ifs
  · exact hx.sub (show (Parts.literal 1).Width 1 by change 1≤1 ∧ 0≤1 ∧ 1≤1;omega)
  · exact hx.mono (by omega)

theorem center_valid (S : Finset ℕ) (hS : inputs⊆S) (i : Fin 3) : (center i).Valid S := by
  have hi := hS (Finset.mem_union_left _ (RootProduct.coordinate_mem i))
  have h3 := hS (show 3∈inputs by decide)
  have h4 := hS (show 4∈inputs by decide)
  simp [center,Control.Valid,Instruction.Valid,hi,h3,h4]

theorem center_admissible (i : ℕ) (v : ℕ→Parts) : (center i).AdmissibleTrace v := by
  simp [center,Control.AdmissibleTrace,Instruction.Admissible]

theorem center_literals (i W : ℕ) (hW : 2≤W) : (center i).LiteralsFit W := by
  have hh : (Parts.literal (1/2:ℚ)).Width 2 := by norm_num [Parts.Width,Parts.literal];decide
  have ho : (Parts.literal 1).Width 1 := by change 1≤1 ∧ 0≤1 ∧ 1≤1;omega
  simpa only [center,Control.LiteralsFit,Instruction.LiteralFits,and_true,true_and] using
    And.intro (hh.mono hW) (ho.mono (by omega : 1≤W))

theorem center_steps (i : ℕ) : (center i).steps=5 := rfl

theorem positive_true (source : ℕ) (yes no : Control) (v : ℕ→Parts)
    (h : 0<(v source).value) : (Control.positive source yes no).evaluate v=yes.evaluate v :=
  ite_eq_left h

theorem positive_false (source : ℕ) (yes no : Control) (v : ℕ→Parts)
    (h : ¬0<(v source).value) : (Control.positive source yes no).evaluate v=no.evaluate v :=
  ite_eq_right h

theorem center_output (i : Fin 3) (v : ℕ→Parts) (hx : (v i).Valid) :
    (center i).evaluate v i=centeredPart (v i) := by
  have hi3 : i.val≠3 := by omega
  have hi4 : i.val≠4 := by omega
  let v0 := (Instruction.literal 3 (1/2)).update v
  let v1 := (Instruction.binary .sub 4 i 3).update v0
  let yes : Control := .step (.literal 3 1) (.step (.binary .sub i i 3) .done)
  have ht : (v1 4).value=(v i).value-1/2 := by
    simp only [v1,v0,Instruction.update,BinaryOp.eval,Function.update_self,Function.update_of_ne hi3,
      Parts.sub_value _ _ hx (Parts.literal_valid (1/2)),Parts.literal_value]
  change (Control.positive 4 yes .done).evaluate v1 i=centeredPart (v i)
  by_cases hp : 0<(v1 4).value
  · rw [positive_true 4 yes .done v1 hp]
    have hc : (1/2:ℚ)<(v i).value := by rw [ht] at hp;exact sub_pos.mp hp
    simp only [yes,Control.evaluate,v1,v0,Instruction.update,BinaryOp.eval,Function.update_self,
      Function.update_of_ne hi3,Function.update_of_ne hi4,centeredPart,ite_eq_left hc]
  · rw [positive_false 4 yes .done v1 hp]
    have hc : ¬(1/2:ℚ)<(v i).value := by rw [ht,sub_pos] at hp;exact hp
    simp only [Control.evaluate,v1,v0,Instruction.update,Function.update_of_ne hi3,
      Function.update_of_ne hi4,centeredPart,ite_eq_right hc]

theorem center_other (i j : ℕ) (v : ℕ→Parts) (hj : j≠i ∧ j≠3 ∧ j≠4) :
    (center i).evaluate v j=v j := by
  let v0 := (Instruction.literal 3 (1/2)).update v
  let v1 := (Instruction.binary .sub 4 i 3).update v0
  let yes : Control := .step (.literal 3 1) (.step (.binary .sub i i 3) .done)
  change (Control.positive 4 yes .done).evaluate v1 j=v j
  by_cases hp : 0<(v1 4).value
  · rw [positive_true 4 yes .done v1 hp]
    simp only [yes,Control.evaluate,v1,v0,Instruction.update,Function.update_of_ne hj.1,
      Function.update_of_ne hj.2.1,Function.update_of_ne hj.2.2]
  · rw [positive_false 4 yes .done v1 hp]
    simp only [Control.evaluate,v1,v0,Instruction.update,Function.update_of_ne hj.2.1,
      Function.update_of_ne hj.2.2]

theorem centered_coordinates (v : ℕ→Parts) (hv : ∀i:Fin 3,(v i).Valid) (i : Fin 3) :
    centered v i=centeredPart (v i) := by
  have h01 : first v 1=v 1 := center_other 0 1 v (by decide)
  have h02 : first v 2=v 2 := center_other 0 2 v (by decide)
  have h12 : second v 2=v 2 := (center_other 1 2 (first v) (by decide)).trans h02
  have h0 : first v 0=centeredPart (v 0) := center_output 0 v (hv 0)
  have h1 : second v 1=centeredPart (v 1) := by
    have hg1 : (first v 1).Valid := by rw [h01];exact hv 1
    have hh := center_output 1 (first v) hg1
    change second v 1=centeredPart (first v 1) at hh
    exact hh.trans (congrArg centeredPart h01)
  have h2 : centered v 2=centeredPart (v 2) := by
    have hg2 : (second v 2).Valid := by rw [h12];exact hv 2
    have hh := center_output 2 (second v) hg2
    change centered v 2=centeredPart (second v 2) at hh
    exact hh.trans (congrArg centeredPart h12)
  fin_cases i
  · exact (center_other 2 0 (second v) (by decide)).trans
      ((center_other 1 0 (first v) (by decide)).trans h0)
  · exact (center_other 2 1 (second v) (by decide)).trans h1
  · exact h2

theorem centered_other (v : ℕ→Parts) (i : ℕ) (hi : 5 ≤ i) : centered v i=v i := by
  rw [centered,center_other 2 i _ (by omega),second,center_other 1 i _ (by omega),
    first,center_other 0 i _ (by omega)]

theorem values_coordinates (v : ℕ→Parts) (hv : ∀i:Fin 3,(v i).Valid) (i : Fin 3) :
    values v i=(centeredPart (v i)).mul (v 9) := by
  have hc := centered_coordinates v hv i
  have hs := centered_other v 9 (by omega)
  fin_cases i <;> simp only [values,scale,Control.prepend,List.foldr_cons,List.foldr_nil,
    Control.evaluate,Instruction.update,BinaryOp.eval,Function.update_self,
    Function.update_of_ne (by decide : (0:ℕ)≠1),Function.update_of_ne (by decide : (0:ℕ)≠2),
    Function.update_of_ne (by decide : (1:ℕ)≠0),Function.update_of_ne (by decide : (1:ℕ)≠2),
    Function.update_of_ne (by decide : (2:ℕ)≠0),Function.update_of_ne (by decide : (2:ℕ)≠1),
    Function.update_of_ne (by decide : (9:ℕ)≠0),Function.update_of_ne (by decide : (9:ℕ)≠1),
    hc,hs]

theorem values_other (v : ℕ→Parts) (i : ℕ) (hi : 5 ≤ i) : values v i=v i := by
  simp (disch := omega) [values,scale,Control.prepend,Control.evaluate,Instruction.update,
    centered_other v i hi]

theorem grid_condition (grid : ℕ) [NeZero grid] (j : ZMod grid) :
    (1/2:ℚ)<Calibration.gridTurn grid j ↔ ¬2*j.val≤grid := by
  have hg : (0:ℚ)<grid := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne grid)
  rw [Calibration.gridTurn,lt_div_iff₀ hg]
  have hc : (1/2:ℚ)*grid<(j.val:ℚ) ↔ (grid:ℚ)<2*j.val := by constructor <;> intro h <;> linarith
  rw [hc]
  exact_mod_cast (show grid<2*j.val ↔ ¬2*j.val≤grid by omega)

theorem values_centeredGrid (grid : ℕ) [NeZero grid] (j : Fin 3→ZMod grid)
    (scaleValue : ℚ) (v : ℕ→Parts) (hv : ∀i:Fin 3,(v i).Valid)
    (hj : ∀i:Fin 3,(v i).value=Calibration.gridTurn grid (j i)) (hs : (v 9).value=scaleValue)
    (i : Fin 3) : (values v i).value=scaleValue*Calibration.centeredGrid grid (j i) := by
  rw [values_coordinates v hv i,Parts.mul_value,centeredPart_value _ (hv i),hj i,hs]
  simp only [grid_condition]
  unfold Calibration.centeredGrid
  split_ifs <;> ring

#print axioms values_centeredGrid
end Maxwell.Continuum.RationalDataflow.RootGridCenter
