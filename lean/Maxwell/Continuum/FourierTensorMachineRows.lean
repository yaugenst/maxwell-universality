import Maxwell.Continuum.FourierTensorMachineWidths
import Maxwell.Continuum.RationalDataflowRowFold
import Maxwell.Continuum.RationalDataflowArraySum

/-! The eight stored numerators of each tensor summand are loaded by a
literal fixed-stride row plan. Validity and widths are proved from the
stored table, rather than supplied for the running accumulator. -/

namespace Maxwell.Continuum.Profile.TensorMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def readPlan : List (ℕ×ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8)]

theorem readPlan_valid : ∀x∈readPlan,x.2∈ids := by simp [readPlan,ids]
theorem readPlan_offsets : ∀x∈readPlan,x.1.bits.length≤3 := by simp [readPlan];decide

def rowLoad {m : ℕ} (a : Table m) (row : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  rowPlanValues a 8 row readPlan v

def rowTerm {m : ℕ} (a : Table m) (row : ℕ) : ℚ :=
  realProduct ((a.getD (8*row)).value,(a.getD (8*row+1)).value)
    ((a.getD (8*row+2)).value,(a.getD (8*row+3)).value)
    ((a.getD (8*row+4)).value,(a.getD (8*row+5)).value)
    ((a.getD (8*row+6)).value,(a.getD (8*row+7)).value)

theorem rowLoad_accumulator {m : ℕ} (a : Table m) (row : ℕ) (v : ℕ→Parts) :
    rowLoad a row v 0=v 0 := by simp [rowLoad,readPlan,rowPlanValues]

theorem rowLoad_input {m : ℕ} (a : Table m) (row : ℕ) (v : ℕ→Parts)
    (i : ℕ) (hi : 1 ≤ i) (hi8 : i≤8) : rowLoad a row v i=a.getD (8*row+(i-1)) := by
  interval_cases i <;> simp [rowLoad,readPlan,rowPlanValues]

private theorem plan_good {m : ℕ} (a : Table m) (S : Finset ℕ) (row stride : ℕ)
    (plan : List (ℕ×ℕ)) (ha : ∀i,(a.get i).Valid) (v : ℕ→Parts) (hv : Good S v) :
    Good S (rowPlanValues a stride row plan v) := by
  induction plan generalizing v with
  | nil => exact hv
  | cons x rest ih =>
    exact ih (Function.update v x.2 (a.getD (stride*row+x.1)))
      (hv.update x.2 (a.getD_valid ha _))

private theorem plan_width {m : ℕ} (a : Table m) (S : Finset ℕ) (row stride : ℕ)
    (plan : List (ℕ×ℕ)) (B : ℕ) (hB : 1≤B) (ha : ∀i,(a.get i).Width B)
    (v : ℕ→Parts) (hv : WidthBank S B v) :
    WidthBank S B (rowPlanValues a stride row plan v) := by
  induction plan generalizing v with
  | nil => exact hv
  | cons x rest ih =>
    exact ih (Function.update v x.2 (a.getD (stride*row+x.1)))
      (hv.update x.2 (a.getD_width B hB ha _))

theorem rowLoad_good {m : ℕ} (a : Table m) (row : ℕ)
    (ha : ∀i,(a.get i).Valid) (v : ℕ→Parts) (hv : Good ids v) :
    Good ids (rowLoad a row v) := plan_good a ids row 8 readPlan ha v hv

theorem rowLoad_width {m : ℕ} (a : Table m) (row B W : ℕ) (hW : 1≤W) (hWB : W≤B)
    (ha : ∀i,(a.get i).Width W) (v : ℕ→Parts) (hv : WidthBank ids B v) :
    WidthBank ids B (rowLoad a row v) :=
  plan_width a ids row 8 readPlan B (hW.trans hWB) (fun i => (ha i).mono hWB) v hv

theorem rowLoad_inputs_width {m : ℕ} (a : Table m) (row W : ℕ) (hW : 1≤W)
    (ha : ∀i,(a.get i).Width W) (v : ℕ→Parts) :
    ∀i,1 ≤ i → i≤8 → (rowLoad a row v i).Width W := by
  intro i hi hi8
  rw [rowLoad_input a row v i hi hi8]
  exact a.getD_width W hW ha _

theorem body_row_value {m : ℕ} (a : Table m) (row : ℕ)
    (ha : ∀i,(a.get i).Valid) (v : ℕ→Parts) (hv : Good ids v) :
    (body.evaluate (rowLoad a row v) 0).value=(v 0).value+rowTerm a row := by
  rw [body_value _ (rowLoad_good a row ha v hv),rowLoad_accumulator]
  simp only [rowLoad_input a row v 1 (by decide) (by decide),
    rowLoad_input a row v 2 (by decide) (by decide),rowLoad_input a row v 3 (by decide) (by decide),
    rowLoad_input a row v 4 (by decide) (by decide),rowLoad_input a row v 5 (by decide) (by decide),
    rowLoad_input a row v 6 (by decide) (by decide),rowLoad_input a row v 7 (by decide) (by decide),
    rowLoad_input a row v 8 (by decide) (by decide),Nat.reduceSub,Nat.add_zero,rowTerm]

def accumulatorWidth (k W : ℕ) : ℕ := W+k*(22*W+22)

theorem tensor_iterate_good {m : ℕ} (a : Table m) (n : ℕ)
    (ha : ∀i,(a.get i).Valid) (v : ℕ→Parts) (hv : Good ids v) (k : ℕ) :
    Good ids (rowIterate a 8 readPlan body n v k) := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    exact body.evaluate_good ids body_valid _ (rowLoad_good a _ ha _ ih) (body_admissible _)

theorem tensor_iterate_width {m : ℕ} (a : Table m) (n W : ℕ) (hW : 1≤W)
    (ha : ∀i,(a.get i).Width W) (v : ℕ→Parts) (hv : WidthBank ids W v) (k : ℕ) :
    WidthBank ids (accumulatorWidth k W) (rowIterate a 8 readPlan body n v k) := by
  induction k with
  | zero => simpa only [accumulatorWidth,Nat.zero_mul,Nat.add_zero,rowIterate] using hv
  | succ k ih =>
    have he : accumulatorWidth k W+22*W+22=accumulatorWidth (k+1) W := by
      unfold accumulatorWidth;ring
    rw [←he]
    exact body_output_width _ _ W
      (rowLoad_width a _ _ W hW (by unfold accumulatorWidth;omega) ha _ ih)
      (rowLoad_inputs_width a _ W hW ha _)

theorem tensor_iterate_value {m : ℕ} (a : Table m) (n : ℕ)
    (ha : ∀i,(a.get i).Valid) (v : ℕ→Parts) (hv : Good ids v) (k : ℕ) :
    (rowIterate a 8 readPlan body n v k 0).value=
      (v 0).value+∑i∈Finset.range k,rowTerm a (n-1-i) := by
  induction k with
  | zero => simp only [rowIterate,Finset.range_zero,Finset.sum_empty,add_zero]
  | succ k ih =>
    change (body.evaluate (rowLoad a (n-1-k) (rowIterate a 8 readPlan body n v k)) 0).value=_
    rw [body_row_value a _ ha _ (tensor_iterate_good a n ha v hv k),ih,Finset.sum_range_succ]
    ring

#print axioms tensor_iterate_width
#print axioms tensor_iterate_value
end Maxwell.Continuum.Profile.TensorMachine
