import Maxwell.Continuum.ChebyshevWaveMachineProduct

/-! Literal runtime preparation and accumulation of the finite wave transform.
The frequency, reciprocal grid size, Fourier index, and running sample index
are ordinary stored rational words. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def prepareInstructions : List RationalDataflow.Instruction :=
  [.binary .mul 0 10 15,.binary .mul 1 13 11,
   .binary .mul 5 1 12,.binary .mul 5 5 14]
def accumulateInstructions : List RationalDataflow.Instruction :=
  [.binary .add 8 8 0,.binary .add 9 9 1,.binary .add 13 13 15]
def prepared (v : ℕ→Parts) : ℕ→Parts := evaluate prepareInstructions v
def summand (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts := productValues Q P (prepared v)
def sumStep (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  evaluate accumulateInstructions (summand Q P v)
def sumValues (Q P : ℕ) (v : ℕ→Parts) : ℕ→(ℕ→Parts)
  | 0 => v
  | k+1 => sumStep Q P (sumValues Q P v k)

theorem prepareInstructions_valid : ∀a∈prepareInstructions,a.Valid ids := by
  simp [prepareInstructions,RationalDataflow.Instruction.Valid,ids]
theorem accumulateInstructions_valid : ∀a∈accumulateInstructions,a.Valid ids := by
  simp [accumulateInstructions,RationalDataflow.Instruction.Valid,ids]

theorem productValues_unchanged (Q P : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : 8 ≤ i) :
    productValues Q P v i=v i := by
  have h0 : i≠0 := by omega
  have h1 : i≠1 := by omega
  have h2 : i≠2 := by omega
  have h3 : i≠3 := by omega
  have h4 : i≠4 := by omega
  have h5 : i≠5 := by omega
  have h6 : i≠6 := by omega
  have h7 : i≠7 := by omega
  simp [productValues,productInstructions,evaluate,RationalDataflow.Instruction.update,
    state7,state6,state5,state4,sampleValues,state3,state2,state1,h0,h1,h2,h3,h4,h5,h6,h7]

theorem prepared_unchanged (v : ℕ→Parts) (i : ℕ) (hi : 8 ≤ i) : prepared v i=v i := by
  have h0 : i≠0 := by omega
  have h1 : i≠1 := by omega
  have h5 : i≠5 := by omega
  simp [prepared,prepareInstructions,evaluate,RationalDataflow.Instruction.update,h0,h1,h5]

theorem summand_unchanged (Q P : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : 8 ≤ i) :
    summand Q P v i=v i := by
  rw [summand,productValues_unchanged Q P _ i hi,prepared_unchanged v i hi]

theorem sumStep_good (Q P : ℕ) (v : ℕ→Parts) (hv : Good ids v) : Good ids (sumStep Q P v) := by
  have hp := evaluate_good ids prepareInstructions prepareInstructions_valid v hv
    (by simp [prepareInstructions,AdmissibleTrace,RationalDataflow.Instruction.Admissible])
  have hs := (product_states_good Q P (prepared v) hp).2.2.2.2
  exact evaluate_good ids accumulateInstructions accumulateInstructions_valid _ hs
    (by simp [accumulateInstructions,AdmissibleTrace,RationalDataflow.Instruction.Admissible])

theorem sumValues_good (Q P : ℕ) (v : ℕ→Parts) (hv : Good ids v) (k : ℕ) :
    Good ids (sumValues Q P v k) := by
  induction k with
  | zero => exact hv
  | succ k ih => exact sumStep_good Q P _ ih

structure SumInput (grid : ℕ) (q : ℚ) (n : ℤ) (k : ℕ) (v : ℕ→Parts) : Prop where
  frequency : (v 10).value=q
  reciprocal : (v 11).value=(grid:ℚ)⁻¹
  index : (v 12).value=n
  counter : (v 13).value=k
  negativeOne : (v 14).value= -1
  one : (v 15).value=1

theorem prepared_input (grid : ℕ) [NeZero grid] (q : ℚ) (n : ℤ) (k : ℕ)
    (v : ℕ→Parts) (hi : SumInput grid q n k v) (hk : k<grid) :
    (prepared v 0).value=q ∧ (prepared v 1).value=Calibration.gridTurn grid (k:ZMod grid) ∧
      (prepared v 5).value= -((k:ZMod grid).val:ℚ)*(n:ℚ)/grid := by
  have he : (k:ZMod grid).val=k := by simp [ZMod.val_natCast,Nat.mod_eq_of_lt hk]
  simp only [prepared,prepareInstructions,evaluate,RationalDataflow.Instruction.update,
    BinaryOp.eval,Function.update_self]
  simp [Parts.mul_value,hi.frequency,hi.reciprocal,hi.index,hi.counter,hi.negativeOne,hi.one,
    Calibration.gridTurn,he,div_eq_mul_inv]
  ring

theorem sumStep_input (Q P grid : ℕ) (q : ℚ) (n : ℤ) (k : ℕ) (v : ℕ→Parts)
    (hv : Good ids v) (hi : SumInput grid q n k v) :
    SumInput grid q n (k+1) (sumStep Q P v) := by
  have hg := (product_states_good Q P (prepared v)
    (evaluate_good ids prepareInstructions prepareInstructions_valid v hv
      (by simp [prepareInstructions,AdmissibleTrace,RationalDataflow.Instruction.Admissible]))).2.2.2.2
  change Good ids (summand Q P v) at hg
  have hc : (sumStep Q P v 13).value=(k:ℚ)+1 := by
    simp only [sumStep,accumulateInstructions,evaluate,RationalDataflow.Instruction.update,
      BinaryOp.eval,Function.update_self]
    simp only [Function.update_of_ne (by decide : (13:ℕ)≠9),
      Function.update_of_ne (by decide : (13:ℕ)≠8),
      Function.update_of_ne (by decide : (15:ℕ)≠9),
      Function.update_of_ne (by decide : (15:ℕ)≠8)]
    rw [Parts.add_value _ _ (hg 13 (by decide)) (hg 15 (by decide)),
      summand_unchanged Q P v 13 (by decide),summand_unchanged Q P v 15 (by decide),hi.counter,hi.one]
  have keep (i : ℕ) (h10 : 10 ≤ i) (h13 : i≠13) : sumStep Q P v i=v i := by
    have h8 : i≠8 := by omega
    have h9 : i≠9 := by omega
    simp only [sumStep,accumulateInstructions,evaluate,RationalDataflow.Instruction.update,
      Function.update_of_ne h8,Function.update_of_ne h9,Function.update_of_ne h13]
    exact summand_unchanged Q P v i (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [keep 10 (by decide) (by decide)]; exact hi.frequency
  · rw [keep 11 (by decide) (by decide)]; exact hi.reciprocal
  · rw [keep 12 (by decide) (by decide)]; exact hi.index
  · simpa only [Nat.cast_add,Nat.cast_one] using hc
  · rw [keep 14 (by decide) (by decide)]; exact hi.negativeOne
  · rw [keep 15 (by decide) (by decide)]; exact hi.one

theorem sumStep_values (grid : ℕ) [NeZero grid] (q : ℚ) (n : ℤ) (Q P k : ℕ)
    (v : ℕ→Parts) (hv : Good ids v) (hi : SumInput grid q n k v) (hk : k<grid) :
    (sumStep Q P v 8).value=(v 8).value+(waveProductSample grid q Q P n (k:ZMod grid)).re.center ∧
    (sumStep Q P v 9).value=(v 9).value+(waveProductSample grid q Q P n (k:ZMod grid)).im.center := by
  have hp := evaluate_good ids prepareInstructions prepareInstructions_valid v hv
    (by simp [prepareInstructions,AdmissibleTrace,RationalDataflow.Instruction.Admissible])
  have hinput := prepared_input grid q n k v hi hk
  have hc := productValues_correct grid Q P (k:ZMod grid) n (prepared v) hp hinput.2.1 hinput.2.2
  rw [hinput.1] at hc
  have hg := (product_states_good Q P (prepared v) hp).2.2.2.2
  have hv0 : (summand Q P v 0).Valid := hg 0 (by decide)
  have hv1 : (summand Q P v 1).Valid := hg 1 (by decide)
  change (summand Q P v 0).value=_ ∧ (summand Q P v 1).value=_ at hc
  simp only [sumStep,accumulateInstructions,evaluate,RationalDataflow.Instruction.update,BinaryOp.eval]
  simp only [Function.update_self,Function.update_of_ne (by decide : (8:ℕ)≠13),
    Function.update_of_ne (by decide : (8:ℕ)≠9),Function.update_of_ne (by decide : (9:ℕ)≠13),
    Function.update_of_ne (by decide : (9:ℕ)≠8),Function.update_of_ne (by decide : (1:ℕ)≠8)]
  rw [summand_unchanged Q P v 8 (by decide),summand_unchanged Q P v 9 (by decide),
    Parts.add_value _ _ (hv 8 (by decide)) hv0,Parts.add_value _ _ (hv 9 (by decide)) hv1,hc.1,hc.2]
  exact ⟨rfl,rfl⟩

#print axioms prepared_input
#print axioms sumStep_input
#print axioms sumStep_values
end Maxwell.Continuum.Profile.WaveMachine
