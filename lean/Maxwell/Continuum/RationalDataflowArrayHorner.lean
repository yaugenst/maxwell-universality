import Maxwell.Continuum.RationalDataflowArraySum

/-! A uniform Horner loop over a literal stored coefficient table. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def hornerBody : Control :=
  .step (.binary .mul 0 0 2) (.step (.binary .add 0 0 1) .done)

def hornerWidth (n W : ℕ) : ℕ := (n+1)*(2*W+2)+1

def reverseHorner {n : ℕ} (a : Table n) (x : Parts) : ℕ→Parts
  | 0 => Parts.literal 0
  | k+1 => ((reverseHorner a x k).mul x).add (a.getD (n-1-k))

theorem reverseHorner_valid {n : ℕ} (a : Table n) (x : Parts)
    (ha : ∀ i, (a.get i).Valid) (hx : x.Valid) (k : ℕ) :
    (reverseHorner a x k).Valid := by
  induction k with
  | zero => exact Parts.literal_valid 0
  | succ k ih => exact Parts.add_valid (Parts.mul_valid ih hx) (a.getD_valid ha _)

theorem reverseHorner_width {n : ℕ} (a : Table n) (x : Parts)
    (W : ℕ) (hW : 1≤W) (ha : ∀ i, (a.get i).Width W) (hx : x.Width W) (k : ℕ) :
    (reverseHorner a x k).Width (k*(2*W+2)+1) := by
  induction k with
  | zero => simpa only [reverseHorner,zero_mul,zero_add] using
      Parts.literal_width RationalWords.width_zero'
  | succ k ih =>
    change (((reverseHorner a x k).mul x).add (a.getD (n-1-k))).Width _
    convert (ih.mul hx).add (a.getD_width W hW ha _) using 1
    ring

theorem reverseHorner_value_partial {n : ℕ} (a : Table n) (x : Parts)
    (ha : ∀ i, (a.get i).Valid) (hx : x.Valid) (k : ℕ) :
    (reverseHorner a x k).value=
      ∑ j∈Finset.range k, (a.getD (n-1-j)).value*x.value^(k-1-j) := by
  induction k with
  | zero => simp only [reverseHorner,Parts.literal_value,Finset.range_zero,Finset.sum_empty]
  | succ k ih =>
    rw [reverseHorner,Parts.add_value _ _
      (Parts.mul_valid (reverseHorner_valid a x ha hx k) hx) (a.getD_valid ha _),
      Parts.mul_value,ih,Finset.sum_mul,Finset.sum_range_succ]
    have hs : ∑ j∈Finset.range k, (a.getD (n-1-j)).value*x.value^(k-1-j)*x.value=
        ∑ j∈Finset.range k, (a.getD (n-1-j)).value*x.value^(k+1-1-j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjk := Finset.mem_range.mp hj
      have he : k+1-1-j=(k-1-j)+1 := by omega
      rw [he,pow_succ,mul_assoc]
    rw [hs]
    simp only [Nat.add_sub_cancel,Nat.sub_self,pow_zero,mul_one]

theorem reverseHorner_value {n : ℕ} (a : Table n) (x : Parts)
    (ha : ∀ i, (a.get i).Valid) (hx : x.Valid) :
    (reverseHorner a x n).value=∑ i : Fin n, (a.get i).value*x.value^i.val := by
  rw [reverseHorner_value_partial a x ha hx n,
    Finset.sum_range_reflect (fun j => (a.getD j).value*x.value^j) n]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Table.getD,dite_eq_left i.isLt]

theorem horner_iterate_source {n : ℕ} (a : Table n) (v : ℕ→Parts) (k : ℕ) :
    iterate a 1 hornerBody (sumStart v 0) k 2=v 2 := by
  induction k with
  | zero => simp only [iterate,sumStart,Function.update_of_ne (by decide : (2:ℕ)≠0)]
  | succ k ih =>
    simpa only [iterate,hornerBody,Control.evaluate,Instruction.update,
      Function.update_of_ne (by decide : (2:ℕ)≠0),
      Function.update_of_ne (by decide : (2:ℕ)≠1)] using ih

theorem horner_iterate_keep {n : ℕ} (a : Table n) (v : ℕ→Parts) (k i : ℕ)
    (h0 : i≠0) (h1 : i≠1) :
    iterate a 1 hornerBody (sumStart v 0) k i=v i := by
  induction k with
  | zero => simp only [iterate,sumStart,Function.update_of_ne h0]
  | succ k ih =>
    simpa only [iterate,hornerBody,Control.evaluate,Instruction.update,
      Function.update_of_ne h0,Function.update_of_ne h1] using ih

theorem horner_iterate_accumulator {n : ℕ} (a : Table n) (v : ℕ→Parts) (k : ℕ) :
    iterate a 1 hornerBody (sumStart v 0) k 0=reverseHorner a (v 2) k := by
  induction k with
  | zero => simp only [iterate,sumStart,Function.update_self,reverseHorner]
  | succ k ih =>
    simp only [iterate,hornerBody,Control.evaluate,Instruction.update,BinaryOp.eval,
      Function.update_self,Function.update_of_ne (by decide : (0:ℕ)≠1),
      Function.update_of_ne (by decide : (1:ℕ)≠0),
      Function.update_of_ne (by decide : (2:ℕ)≠1),reverseHorner]
    change ((iterate a 1 hornerBody (sumStart v 0) k 0).mul
      (iterate a 1 hornerBody (sumStart v 0) k 2)).add _ = _
    rw [ih,horner_iterate_source]

theorem horner_iterate_good {n : ℕ} (a : Table n) (S : Finset ℕ) (h0 : 0∈S)
    (h1 : 1∈S) (h2 : 2∈S) (ha : ∀ i, (a.get i).Valid)
    (v : ℕ→Parts) (hv : Good S v) (k : ℕ) :
    Good S (iterate a 1 hornerBody (sumStart v 0) k) := by
  induction k with
  | zero => exact hv.update 0 (Parts.literal_valid 0)
  | succ k ih =>
    exact hornerBody.evaluate_good S ⟨⟨h0,h0,h2⟩,⟨h0,h0,h1⟩,trivial⟩ _
      (ih.update 1 (a.getD_valid ha _)) ⟨trivial,trivial,trivial⟩

theorem horner_iterate_width {n : ℕ} (a : Table n) (S : Finset ℕ) (_h0 : 0∈S)
    (h2 : 2∈S) (W : ℕ) (hW : 1≤W) (ha : ∀ i, (a.get i).Width W)
    (v : ℕ→Parts) (hv : WidthBank S W v) (k : ℕ) :
    WidthBank S (hornerWidth k W) (iterate a 1 hornerBody (sumStart v 0) k) := by
  have hbase (k : ℕ) : W≤hornerWidth k W := by unfold hornerWidth; nlinarith
  have hmono (k : ℕ) : hornerWidth k W≤hornerWidth (k+1) W := by unfold hornerWidth; nlinarith
  induction k with
  | zero =>
    exact (hv.mono (hbase 0)).update 0
      ((Parts.literal_width RationalWords.width_zero').mono (by unfold hornerWidth; omega))
  | succ k ih =>
    let state := iterate a 1 hornerBody (sumStart v 0) k
    let loaded := Function.update state 1 (a.getD (n-1-k))
    have initial : WidthBank S (hornerWidth (k+1) W) loaded :=
      (ih.mono (hmono k)).update 1 ((a.getD_width W hW ha _).mono (hbase (k+1)))
    have accum : (loaded 0).Width (k*(2*W+2)+1) := by
      dsimp only [loaded,state]
      rw [Function.update_of_ne (by decide : (0:ℕ)≠1),horner_iterate_accumulator]
      exact reverseHorner_width a (v 2) W hW ha (hv 2 h2) k
    have source : (loaded 2).Width W := by
      dsimp only [loaded,state]
      rw [Function.update_of_ne (by decide : (2:ℕ)≠1),horner_iterate_source]
      exact hv 2 h2
    have entry : (loaded 1).Width W := by
      simpa only [loaded,Function.update_self] using a.getD_width W hW ha (n-1-k)
    have product := accum.mul source
    have result := product.add entry
    have hp : k*(2*W+2)+1+W+1≤hornerWidth (k+1) W := by unfold hornerWidth; nlinarith
    have hr : k*(2*W+2)+1+W+1+W+1≤hornerWidth (k+1) W := by unfold hornerWidth; nlinarith
    have one := initial.update 0 (product.mono hp)
    have two := one.update 0 (result.mono hr)
    simpa only [loaded,state,iterate,hornerBody,Control.evaluate,Instruction.update,BinaryOp.eval,
      Function.update_self,Function.update_of_ne (by decide : (1:ℕ)≠0)] using two

theorem horner_widthTrace {n : ℕ} (a : Table n) (S : Finset ℕ) (h0 : 0∈S)
    (h2 : 2∈S) (W : ℕ) (hW : 1≤W) (ha : ∀ i, (a.get i).Width W)
    (v : ℕ→Parts) (hv : WidthBank S W v) (k : ℕ) (hk : k<n) :
    hornerBody.WidthTrace S (hornerWidth n W)
      (loaded a 1 hornerBody (sumStart v 0) k) := by
  have hkn : hornerWidth k W≤hornerWidth n W := by
    unfold hornerWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1
  have hbase : W≤hornerWidth n W := by unfold hornerWidth; nlinarith
  have initial := ((horner_iterate_width a S h0 h2 W hW ha v hv k).mono hkn).update 1
    ((a.getD_width W hW ha (n-1-k)).mono hbase)
  have acc : ((loaded a 1 hornerBody (sumStart v 0) k) 0).Width (k*(2*W+2)+1) := by
    simp only [loaded,Function.update_of_ne (by decide : (0:ℕ)≠1),horner_iterate_accumulator]
    exact reverseHorner_width a (v 2) W hW ha (hv 2 h2) k
  have source : ((loaded a 1 hornerBody (sumStart v 0) k) 2).Width W := by
    simp only [loaded,Function.update_of_ne (by decide : (2:ℕ)≠1),horner_iterate_source]
    exact hv 2 h2
  have hp : k*(2*W+2)+1+W+1≤hornerWidth n W := by unfold hornerWidth; nlinarith
  refine ⟨initial,trivial,initial.update 0 ((acc.mul source).mono hp),trivial,?_⟩
  have hm : hornerWidth (k+1) W≤hornerWidth n W := by
    unfold hornerWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1
  exact (horner_iterate_width a S h0 h2 W hW ha v hv (k+1)).mono hm

#print axioms reverseHorner_value
#print axioms horner_widthTrace
end Maxwell.Continuum.RationalDataflow.PartArray
