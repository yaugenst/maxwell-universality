import Maxwell.Continuum.RationalDataflowArraySum

/-! A rational-array fold computes the sum of squares with linear raw-word
growth. Its two arithmetic steps reuse the ordinary charged array fold. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration.RawCutoff (sum sum_valid sum_value)
open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def squaresBody (accumulator entry : ℕ) : Control :=
  .step (.binary .mul entry entry entry) (sumBody accumulator entry)

def squaresWidth (n W : ℕ) : ℕ := sumWidth n (2*W+1)

theorem squares_iterate_accumulator {n : ℕ} (a : Table n) (accumulator entry : ℕ)
    (hne : accumulator≠entry) (v : ℕ→Parts) (k : ℕ) :
    iterate a entry (squaresBody accumulator entry) (sumStart v accumulator) k accumulator=
      sum (fun j => (a.getD (n-1-j)).mul (a.getD (n-1-j))) k := by
  induction k with
  | zero => simp only [iterate,sumStart,Function.update_self,sum]
  | succ k ih =>
    simp only [iterate,squaresBody,sumBody,Control.evaluate,Instruction.update,BinaryOp.eval,
      Function.update_self,Function.update_of_ne hne,sum]
    exact congrArg (fun x : Parts => x.add ((a.getD (n-1-k)).mul (a.getD (n-1-k)))) ih

theorem squares_iterate_good {n : ℕ} (a : Table n) (S : Finset ℕ) (accumulator entry : ℕ)
    (ha : ∀ i, (a.get i).Valid) (v : ℕ→Parts) (hv : Good S v)
    (hacc : accumulator∈S) (hentry : entry∈S) (k : ℕ) :
    Good S (iterate a entry (squaresBody accumulator entry) (sumStart v accumulator) k) := by
  induction k with
  | zero => exact hv.update accumulator (Parts.literal_valid 0)
  | succ k ih =>
    exact (squaresBody accumulator entry).evaluate_good S
      ⟨⟨hentry,hentry,hentry⟩,⟨⟨hacc,hacc,hentry⟩,trivial⟩⟩ _
      (ih.update entry (a.getD_valid ha _)) ⟨trivial,⟨trivial,trivial⟩⟩

theorem squares_iterate_width {n : ℕ} (a : Table n) (S : Finset ℕ) (accumulator entry : ℕ)
    (hne : accumulator≠entry) (W : ℕ) (hW : 1≤W) (ha : ∀ i, (a.get i).Width W)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hacc : accumulator∈S) (k : ℕ) :
    WidthBank S (squaresWidth k W)
      (iterate a entry (squaresBody accumulator entry) (sumStart v accumulator) k) := by
  have hbase (k : ℕ) : 2*W+1≤squaresWidth k W := by unfold squaresWidth sumWidth; nlinarith
  have hmono (k : ℕ) : squaresWidth k W≤squaresWidth (k+1) W := by
    unfold squaresWidth sumWidth; nlinarith
  induction k with
  | zero =>
    exact (hv.mono (by have := hbase 0; omega)).update accumulator
      ((Parts.literal_width RationalWords.width_zero').mono (by have := hbase 0; omega))
  | succ k ih =>
    let state := iterate a entry (squaresBody accumulator entry) (sumStart v accumulator) k
    have he := a.getD_width W hW ha (n-1-k)
    have squared : ((a.getD (n-1-k)).mul (a.getD (n-1-k))).Width (2*W+1) := by
      simpa only [two_mul] using he.mul he
    have bank := ((ih.mono (hmono k)).update entry (he.mono (by have := hbase (k+1); omega))).update
      entry (squared.mono (hbase (k+1)))
    have total := (ih accumulator hacc).add squared
    have eq : squaresWidth k W+(2*W+1)+1=squaresWidth (k+1) W := by
      unfold squaresWidth sumWidth; ring
    rw [eq] at total
    simpa only [iterate,squaresBody,sumBody,Control.evaluate,Instruction.update,BinaryOp.eval,
      Function.update_self,Function.update_of_ne hne,state] using bank.update accumulator total

theorem squares_widthTrace {n : ℕ} (a : Table n) (S : Finset ℕ) (accumulator entry : ℕ)
    (hne : accumulator≠entry) (W : ℕ) (hW : 1≤W) (ha : ∀ i, (a.get i).Width W)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hacc : accumulator∈S) (k : ℕ) (hk : k<n) :
    (squaresBody accumulator entry).WidthTrace S (squaresWidth n W)
      (loaded a entry (squaresBody accumulator entry) (sumStart v accumulator) k) := by
  have mono {j : ℕ} (hj : j≤n) : squaresWidth j W≤squaresWidth n W := by
    unfold squaresWidth sumWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1
  have base : 2*W+1≤squaresWidth n W := by unfold squaresWidth sumWidth; nlinarith
  have he := a.getD_width W hW ha (n-1-k)
  have before := ((squares_iterate_width a S accumulator entry hne W hW ha v hv hacc k).mono
    (mono hk.le)).update entry (he.mono (by omega))
  have square : ((a.getD (n-1-k)).mul (a.getD (n-1-k))).Width (squaresWidth n W) :=
    (he.mul he).mono (by omega)
  refine ⟨before,trivial,?_,trivial,?_⟩
  · simpa only [loaded,Instruction.update,BinaryOp.eval,Function.update_self]
      using before.update entry square
  · exact (squares_iterate_width a S accumulator entry hne W hW ha v hv hacc (k+1)).mono
      (mono (by omega))

theorem squares_iterate_value {n : ℕ} (a : Table n) (accumulator entry : ℕ)
    (hne : accumulator≠entry) (ha : ∀ i, (a.get i).Valid) (v : ℕ→Parts) :
    (iterate a entry (squaresBody accumulator entry) (sumStart v accumulator) n accumulator).value=
      ∑ i : Fin n, (a.get i).value^2 := by
  rw [squares_iterate_accumulator a accumulator entry hne v n,
    sum_value _ n (fun j _ => Parts.mul_valid (a.getD_valid ha _) (a.getD_valid ha _))]
  simp only [Parts.mul_value,←pow_two]
  rw [Finset.sum_range_reflect (fun j => (a.getD j).value^2) n,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Table.getD,dite_eq_left i.isLt]

#print axioms squares_iterate_value
#print axioms squares_widthTrace
end Maxwell.Continuum.RationalDataflow.PartArray
