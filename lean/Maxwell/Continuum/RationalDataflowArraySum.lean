import Maxwell.Continuum.RationalDataflowArrayLoop
import Maxwell.Continuum.RationalDataflowTrace
import Maxwell.Continuum.CutoffRawArithmetic

/-! A fixed runtime program sums an input rational array, with automatic raw-width control. -/

namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration.RawCutoff (sum sum_valid sum_value sum_width)
open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def sumBody (accumulator entry : ℕ) : Control :=
  .step (.binary .add accumulator accumulator entry) .done

def sumWidth (n W : ℕ) : ℕ := (n+1)*(W+1)+1

def sumStart (v : ℕ→Parts) (accumulator : ℕ) : ℕ→Parts :=
  Function.update v accumulator (Parts.literal 0)

theorem Table.getD_valid {n : ℕ} (a : Table n) (ha : ∀ i, (a.get i).Valid) (i : ℕ) :
    (a.getD i).Valid := by
  unfold Table.getD
  split_ifs with hi
  · exact ha ⟨i,hi⟩
  · exact Parts.literal_valid 0

theorem Table.getD_width {n : ℕ} (a : Table n) (W : ℕ) (hW : 1≤W)
    (ha : ∀ i, (a.get i).Width W) (i : ℕ) : (a.getD i).Width W := by
  unfold Table.getD
  split_ifs with hi
  · exact ha ⟨i,hi⟩
  · exact (Parts.literal_width RationalWords.width_zero').mono hW

theorem sum_iterate_accumulator {n : ℕ} (a : Table n) (accumulator entry : ℕ)
    (hne : accumulator≠entry) (v : ℕ→Parts) (k : ℕ) :
    iterate a entry (sumBody accumulator entry) (sumStart v accumulator) k accumulator=
      sum (fun j => a.getD (n-1-j)) k := by
  induction k with
  | zero => simp only [iterate,sumStart,Function.update_self,sum]
  | succ k ih =>
    simp only [iterate,sumBody,Control.evaluate,Instruction.update,BinaryOp.eval,
      Function.update_self,Function.update_of_ne hne,sum]
    exact congrArg (fun x : Parts => x.add (a.getD (n-1-k))) ih

theorem sum_iterate_good {n : ℕ} (a : Table n) (S : Finset ℕ) (accumulator entry : ℕ)
    (ha : ∀ i, (a.get i).Valid) (v : ℕ→Parts) (hv : Good S v)
    (hacc : accumulator∈S) (hentry : entry∈S) (k : ℕ) :
    Good S (iterate a entry (sumBody accumulator entry) (sumStart v accumulator) k) := by
  induction k with
  | zero => exact hv.update accumulator (Parts.literal_valid 0)
  | succ k ih =>
    exact (sumBody accumulator entry).evaluate_good S ⟨⟨hacc,hacc,hentry⟩,trivial⟩ _
      (ih.update entry (a.getD_valid ha _)) ⟨trivial,trivial⟩

theorem sum_iterate_width {n : ℕ} (a : Table n) (S : Finset ℕ) (accumulator entry : ℕ)
    (hne : accumulator≠entry) (W : ℕ) (hW : 1≤W) (ha : ∀ i, (a.get i).Width W)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hacc : accumulator∈S) (k : ℕ) :
    WidthBank S (sumWidth k W) (iterate a entry (sumBody accumulator entry) (sumStart v accumulator) k) := by
  have hbase (k : ℕ) : W≤sumWidth k W := by unfold sumWidth; nlinarith
  have hmono (k : ℕ) : sumWidth k W≤sumWidth (k+1) W := by unfold sumWidth; nlinarith
  induction k with
  | zero =>
    exact (hv.mono (hbase 0)).update accumulator
      ((Parts.literal_width RationalWords.width_zero').mono (by unfold sumWidth; omega))
  | succ k ih =>
    let state := iterate a entry (sumBody accumulator entry) (sumStart v accumulator) k
    have hinput := a.getD_width W hW ha (n-1-k)
    have hw := (ih.mono (hmono k)).update entry (hinput.mono (hbase (k+1)))
    have hac : ((Function.update state entry (a.getD (n-1-k))) accumulator).Width (sumWidth k W) := by
      simpa only [Function.update_of_ne hne] using ih accumulator hacc
    have he : ((Function.update state entry (a.getD (n-1-k))) entry).Width W := by
      simpa only [Function.update_self] using hinput
    have hr := hac.add he
    have heq : sumWidth k W+W+1=sumWidth (k+1) W := by unfold sumWidth; ring
    rw [heq] at hr
    exact hw.update accumulator hr

theorem sum_loaded_width {n : ℕ} (a : Table n) (S : Finset ℕ) (accumulator entry : ℕ)
    (hne : accumulator≠entry) (W : ℕ) (hW : 1≤W) (ha : ∀ i, (a.get i).Width W)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hacc : accumulator∈S) (k : ℕ) (hk : k≤n) :
    WidthBank S (sumWidth n W) (loaded a entry (sumBody accumulator entry) (sumStart v accumulator) k) := by
  have hmono : sumWidth k W≤sumWidth n W := by
    unfold sumWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right (W+1) (by omega)) 1
  exact ((sum_iterate_width a S accumulator entry hne W hW ha v hv hacc k).mono hmono).update entry
    ((a.getD_width W hW ha _).mono (by unfold sumWidth; nlinarith))

theorem sum_widthTrace {n : ℕ} (a : Table n) (S : Finset ℕ) (accumulator entry : ℕ)
    (hne : accumulator≠entry) (W : ℕ) (hW : 1≤W) (ha : ∀ i, (a.get i).Width W)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hacc : accumulator∈S) (k : ℕ) (hk : k<n) :
    (sumBody accumulator entry).WidthTrace S (sumWidth n W)
      (loaded a entry (sumBody accumulator entry) (sumStart v accumulator) k) := by
  refine ⟨sum_loaded_width a S accumulator entry hne W hW ha v hv hacc k hk.le,trivial,?_⟩
  have hmono : sumWidth (k+1) W≤sumWidth n W := by
    unfold sumWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right (W+1) (by omega)) 1
  exact (sum_iterate_width a S accumulator entry hne W hW ha v hv hacc (k+1)).mono hmono

theorem sum_iterate_value {n : ℕ} (a : Table n) (accumulator entry : ℕ)
    (hne : accumulator≠entry) (ha : ∀ i, (a.get i).Valid) (v : ℕ→Parts) :
    (iterate a entry (sumBody accumulator entry) (sumStart v accumulator) n accumulator).value=
      ∑ i : Fin n, (a.get i).value := by
  rw [sum_iterate_accumulator a accumulator entry hne v n,
    sum_value _ n (fun j _ => a.getD_valid ha _)]
  rw [Finset.sum_range_reflect (fun j => (a.getD j).value) n]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Table.getD,dite_eq_left i.isLt]

#print axioms sum_iterate_value
#print axioms sum_widthTrace

end Maxwell.Continuum.RationalDataflow.PartArray
