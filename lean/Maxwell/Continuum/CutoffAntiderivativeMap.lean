import Maxwell.Continuum.RationalDataflowArrayMap
import Maxwell.Continuum.CutoffAntiderivativeTable

/-! A fixed five-operation recurrence converts stored monomial coefficients
to the antiderivative coefficients used by the cutoff query program. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def antiderivativeScaleControl : Control :=
  .step (.inverse 4 3) (.step (.binary .mul 0 1 2)
    (.step (.binary .mul 0 0 4) (.step (.binary .mul 2 2 5)
      (.step (.binary .sub 3 3 6) .done))))

def scaleSlots : Finset ℕ := Finset.range 7

def descendingPower (n : ℕ) : ℕ→Parts
  | 0 => power (Parts.literal 4) (n-1)
  | k+1 => (descendingPower n k).mul (Parts.literal (1/4))

def descendingOdd (n : ℕ) : ℕ→Parts
  | 0 => Parts.literal (2*((n-1:ℕ):ℚ)+1)
  | k+1 => (descendingOdd n k).sub (Parts.literal 2)

def scaleInitial (n : ℕ) : ℕ→Parts :=
  Function.update (Function.update (Function.update (Function.update
    (fun _ => Parts.literal 0) 2 (descendingPower n 0)) 3 (descendingOdd n 0))
      5 (Parts.literal (1/4))) 6 (Parts.literal 2)

theorem antiderivativeScaleControl_valid : antiderivativeScaleControl.Valid scaleSlots := by
  simp [antiderivativeScaleControl,Control.Valid,Instruction.Valid,scaleSlots]

theorem antiderivativeScaleControl_steps : antiderivativeScaleControl.steps=5 := rfl

theorem antiderivativeScaleControl_state (v : ℕ→Parts) :
    antiderivativeScaleControl.evaluate v=
      Function.update (Function.update (Function.update (Function.update v 4 (v 3).inverse)
        0 (((v 1).mul (v 2)).mul (v 3).inverse)) 2 ((v 2).mul (v 5))) 3 ((v 3).sub (v 6)) := by
  funext i
  simp [antiderivativeScaleControl,Control.evaluate,Instruction.update,BinaryOp.eval]

theorem descendingPower_valid (n k : ℕ) : (descendingPower n k).Valid := by
  induction k with
  | zero => exact power_valid _ (Parts.literal_valid _) _
  | succ k ih => exact Parts.mul_valid ih (Parts.literal_valid _)

theorem descendingOdd_valid (n k : ℕ) : (descendingOdd n k).Valid := by
  induction k with
  | zero => exact Parts.literal_valid _
  | succ k ih => exact Parts.sub_valid ih (Parts.literal_valid _)

theorem descendingPower_value (n k : ℕ) :
    (descendingPower n k).value=(4:ℚ)^(n-1)*(1/4)^k := by
  induction k with
  | zero => simp [descendingPower,power_value,Parts.literal_value]
  | succ k ih =>
    rw [descendingPower,Parts.mul_value,ih,Parts.literal_value,pow_succ,mul_assoc]

theorem descendingOdd_value (n k : ℕ) :
    (descendingOdd n k).value=2*((n-1:ℕ):ℚ)+1-2*(k:ℚ) := by
  induction k with
  | zero => simp [descendingOdd,Parts.literal_value]
  | succ k ih =>
    rw [descendingOdd,Parts.sub_value _ _ (descendingOdd_valid n k) (Parts.literal_valid _),
      ih,Parts.literal_value]
    push_cast
    ring

theorem descendingPower_value_index (n k : ℕ) (hk : k<n) :
    (descendingPower n k).value=(4:ℚ)^(n-1-k) := by
  rw [descendingPower_value,one_div,inv_pow,←div_eq_mul_inv]
  apply (div_eq_iff (pow_ne_zero k (by norm_num : (4:ℚ)≠0))).2
  rw [←pow_add,Nat.sub_add_cancel (by omega)]

theorem descendingOdd_value_index (n k : ℕ) (hk : k<n) :
    (descendingOdd n k).value=2*((n-1-k:ℕ):ℚ)+1 := by
  rw [descendingOdd_value,Nat.cast_sub (by omega : k≤n-1)]
  ring

theorem scale_iterate_state {n : ℕ} (a : Table n) (k : ℕ) :
    iterate a 1 antiderivativeScaleControl (scaleInitial n) k 2=descendingPower n k ∧
    iterate a 1 antiderivativeScaleControl (scaleInitial n) k 3=descendingOdd n k ∧
    iterate a 1 antiderivativeScaleControl (scaleInitial n) k 5=Parts.literal (1/4) ∧
    iterate a 1 antiderivativeScaleControl (scaleInitial n) k 6=Parts.literal 2 := by
  induction k with
  | zero => simp [iterate,scaleInitial]
  | succ k ih =>
    simp only [iterate,antiderivativeScaleControl_state]
    simpa only [Function.update_self,Function.update_of_ne (by decide : (2:ℕ)≠3),
      Function.update_of_ne (by decide : (2:ℕ)≠1),Function.update_of_ne (by decide : (3:ℕ)≠1),
      Function.update_of_ne (by decide : (5:ℕ)≠1),Function.update_of_ne (by decide : (6:ℕ)≠1),
      Function.update_of_ne (by decide : (5:ℕ)≠3),Function.update_of_ne (by decide : (5:ℕ)≠2),
      Function.update_of_ne (by decide : (5:ℕ)≠0),Function.update_of_ne (by decide : (5:ℕ)≠4),
      Function.update_of_ne (by decide : (6:ℕ)≠3),Function.update_of_ne (by decide : (6:ℕ)≠2),
      Function.update_of_ne (by decide : (6:ℕ)≠0),Function.update_of_ne (by decide : (6:ℕ)≠4),
      ih.1,ih.2.1,ih.2.2.1,ih.2.2.2,descendingPower,descendingOdd] using
      (show True∧True∧True∧True from ⟨trivial,trivial,trivial,trivial⟩)

theorem scale_output_value {n : ℕ} (a : Table n) (k : ℕ) (hk : k<n) :
    (iterate a 1 antiderivativeScaleControl (scaleInitial n) (k+1) 0).value=
      (a.get ⟨n-1-k,by omega⟩).value*(4:ℚ)^(n-1-k)/(2*((n-1-k:ℕ):ℚ)+1) := by
  have state := scale_iterate_state a k
  have hne : (descendingOdd n k).value≠0 := by rw [descendingOdd_value_index n k hk]; positivity
  simp only [iterate,antiderivativeScaleControl_state,Function.update_of_ne (by decide : (0:ℕ)≠3),
    Function.update_of_ne (by decide : (0:ℕ)≠2),Function.update_self,
    Function.update_of_ne (by decide : (2:ℕ)≠1),Function.update_of_ne (by decide : (3:ℕ)≠1),
    state.1,state.2.1,Parts.mul_value]
  rw [Parts.inverse_value _ (descendingOdd_valid n k) hne,descendingPower_value_index n k hk,
    descendingOdd_value_index n k hk]
  simp only [Table.getD,dite_eq_left (show n-1-k<n by omega),div_eq_mul_inv]

theorem scale_map_value (N : ℕ) (a : Table (Profile.profileDegree N))
    (hcoeff : ∀ i, (a.get i).value=(monomialCoefficient N i).value)
    (i : Fin (Profile.profileDegree N)) :
    (mapValues a antiderivativeScaleControl 0 (scaleInitial (Profile.profileDegree N)) i).value=
      (antiderivativeCoefficient N i).value := by
  have hi := i.isLt
  let n := Profile.profileDegree N
  have hk : n-1-i.val<n := by dsimp [n]; omega
  have he : n-i.val=(n-1-i.val)+1 := by dsimp [n]; omega
  unfold mapValues
  change (iterate a 1 antiderivativeScaleControl (scaleInitial n) (n-i.val) 0).value=_
  rw [he,scale_output_value a _ hk]
  have hidx : n-1-(n-1-i.val)=i.val := by dsimp [n]; omega
  dsimp only [n] at hidx ⊢
  simp only [hidx,hcoeff,antiderivativeCoefficient,Parts.mul_value,power_value,Parts.literal_value]
  rw [Parts.inverse_value _ (Parts.literal_valid _) (by rw [Parts.literal_value]; positivity)]
  simp only [Parts.literal_value,div_eq_mul_inv]

#print axioms scale_map_value
end Maxwell.Continuum.Calibration.RawCutoff
