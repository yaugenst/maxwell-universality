import Maxwell.Continuum.CalibrationElementaryFrames
import Maxwell.Continuum.CalibrationBumpDFT
import Maxwell.Continuum.PhaseDataflowCost

/-! The exact raw real and imaginary summands used by the root-grid DFT.
The phase is reduced to one turn before this call. -/
namespace Maxwell.Continuum.RationalDataflow.RootProduct
open Maxwell.Cost Maxwell.Cost.Structured RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def inputs : Finset ℕ := {0,1,2,3,4,5,6,7}
def root (N : ℕ) (v : ℕ→Parts) : Parts := Glue.result N (RootSample.rawArgument (RootSample.coordinates v))
def cosine (N : ℕ) (v : ℕ→Parts) : Parts := Phase.result cosineSigns 1 N (v 5)
def sine (N : ℕ) (v : ℕ→Parts) : Parts := Phase.result sineSigns 1 N (v 5)
def afterCos (N : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update (RootSample.values N v) 6 (cosine N v)
def afterSin (N : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update (afterCos N v) 7 (sine N v)
def multiply : Control := Control.prepend [.binary .mul 6 6 4,.binary .mul 7 7 4] .done
def values (N : ℕ) (v : ℕ→Parts) : ℕ→Parts := multiply.evaluate (afterSin N v)
def code : Code := .seq RootSample.code
  (.seq (Phase.Runtime.code Runtime.cosineCycle 6 5)
    (.seq (Phase.Runtime.code Runtime.sineCycle 7 5) multiply.code))

theorem root_inputs : RootSample.inputs⊆inputs := by decide
theorem multiply_valid (S : Finset ℕ) (hS : inputs⊆S) : multiply.Valid S := by
  have h4 := hS (show 4∈inputs by decide)
  have h6 := hS (show 6∈inputs by decide)
  have h7 := hS (show 7∈inputs by decide)
  simp [multiply,Control.prepend,Control.Valid,Instruction.Valid,h4,h6,h7]
theorem multiply_admissible (v : ℕ→Parts) : multiply.AdmissibleTrace v := by
  simp [multiply,Control.prepend,Control.AdmissibleTrace,Instruction.Admissible]
theorem multiply_literals (W : ℕ) : multiply.LiteralsFit W := by
  simp [multiply,Control.prepend,Control.LiteralsFit,Instruction.LiteralFits]
theorem multiply_steps : multiply.steps=2 := rfl

theorem root_value (N : ℕ) (v : ℕ→Parts) (hv : ∀i,(RootSample.coordinates v i).Valid) :
    (root N v).value=(Calibration.rootApprox (fun i => (RootSample.coordinates v i).value) N).center :=
  RootSample.values_value N v hv

theorem values_real (N : ℕ) (v : ℕ→Parts) : values N v 6=(cosine N v).mul (root N v) := by
  simp [values,multiply,Control.prepend,Control.evaluate,Instruction.update,BinaryOp.eval,
    afterSin,afterCos,root,RootSample.values]
theorem values_imag (N : ℕ) (v : ℕ→Parts) : values N v 7=(sine N v).mul (root N v) := by
  simp [values,multiply,Control.prepend,Control.evaluate,Instruction.update,BinaryOp.eval,
    afterSin,afterCos,root,RootSample.values]

theorem values_unchanged (N : ℕ) (v : ℕ→Parts) (i : ℕ)
    (hi : i≠3 ∧ i≠4 ∧ i≠6 ∧ i≠7) : values N v i=v i := by
  simp only [values,multiply,Control.prepend,List.foldr_cons,List.foldr_nil,Control.evaluate,
    Instruction.update,Function.update_of_ne hi.2.2.1,Function.update_of_ne hi.2.2.2,
    afterSin,afterCos]
  exact RootSample.values_unchanged N v i ⟨hi.1,hi.2.1⟩

theorem rootProductSample_values (grid : ℕ) [NeZero grid] (N : ℕ) (scale : ℚ)
    (frequency : Fin 3→ℤ) (j : Fin 3→ZMod grid) (v : ℕ→Parts)
    (hv : ∀i,(RootSample.coordinates v i).Valid) (hp : (v 5).Valid)
    (hcoord : ∀i,(RootSample.coordinates v i).value=scale*Calibration.centeredGrid grid (j i))
    (hphase : (v 5).value=Calibration.gridTurn grid
      (∑i, (-(PeriodicSampling.Product.frequency grid frequency)) i*j i)) :
    (values N v 6).value=(Calibration.rootProductSample grid scale N frequency j).re.center ∧
    (values N v 7).value=(Calibration.rootProductSample grid scale N frequency j).im.center := by
  have hr := root_value N v hv
  have hcoords : (fun i => (RootSample.coordinates v i).value)=
      (fun i => scale*Calibration.centeredGrid grid (j i)) := funext hcoord
  rw [hcoords] at hr
  have hc : (cosine N v).value=(Calibration.cosTurnApprox
      (Calibration.gridTurn grid (∑i, (-(PeriodicSampling.Product.frequency grid frequency)) i*j i)) 1 N).center := by
    rw [cosine,Phase.result_cos _ _ _ hp,hphase]
  have hs : (sine N v).value=(Calibration.sinTurnApprox
      (Calibration.gridTurn grid (∑i, (-(PeriodicSampling.Product.frequency grid frequency)) i*j i)) 1 N).center := by
    rw [sine,Phase.result_sin _ _ _ hp,hphase]
  rw [values_real,values_imag,Parts.mul_value,Parts.mul_value,hc,hs,hr]
  simp only [Calibration.rootProductSample,Calibration.productCharacterApprox,
    Calibration.gridCharacterApprox,Calibration.rootSample,Maxwell.Certificate.ComplexRectangle.mul,
    Maxwell.Certificate.Ball.add,Maxwell.Certificate.Ball.mul,Maxwell.Certificate.Ball.neg,
    mul_zero,neg_zero,add_zero,zero_add,and_self]

def coefficientWidth (N B : ℕ) : ℕ := 2^70*(N+6*B+20)^4

theorem values_coefficient_width (N B : ℕ) (v : ℕ→Parts)
    (hv : ∀i,(RootSample.coordinates v i).Width B) (hp : (v 5).Width B) :
    (values N v 6).Width (coefficientWidth N B) ∧
      (values N v 7).Width (coefficientWidth N B) := by
  have hr : (root N v).Width (2^28*(N+6*B+19)^4) := RootSample.values_width N B v hv
  have hc := Phase.result_width cosineSigns 1 N B (v 5) hp
  have hs := Phase.result_width sineSigns 1 N B (v 5) hp
  have hphase : 2^68*(1+N+B+12)^4≤2^68*(N+6*B+20)^4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have hroot : 2^28*(N+6*B+19)^4≤2^28*(N+6*B+20)^4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have h1 : 1≤(N+6*B+20)^4 := one_le_pow₀ (by omega)
  have ht : 2^68*(1+N+B+12)^4+2^28*(N+6*B+19)^4+1≤coefficientWidth N B := by
    unfold coefficientWidth
    nlinarith only [hphase,hroot,h1]
  rw [values_real,values_imag]
  exact ⟨(hc.mul hr).mono ht,(hs.mul hr).mono ht⟩

#print axioms rootProductSample_values
#print axioms values_coefficient_width
end Maxwell.Continuum.RationalDataflow.RootProduct
