import Maxwell.Continuum.DyadicFloorFrame
import Maxwell.Continuum.ChebyshevWaveMachineSample

/-! Exact reduction modulo one for the finite Fourier character. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem gridTurn_intCast (grid : ℕ) [NeZero grid] (n : ℤ) :
    Calibration.gridTurn grid (n : ZMod grid)=(n:ℚ)/grid-((roundDyadic 0 ((n:ℚ)/grid)).numerator:ℚ) := by
  simp only [roundDyadic,pow_zero,mul_one,Rat.floor_intCast_div_natCast]
  have hv : ((n:ZMod grid).val:ℚ)=((n%(grid:ℤ):ℤ):ℚ) := by
    exact_mod_cast (ZMod.val_intCast n)
  have hd : (grid:ℚ)≠0 := by exact_mod_cast NeZero.ne grid
  unfold Calibration.gridTurn
  rw [hv,Int.emod_def]
  push_cast
  field_simp

theorem characterTurn (grid : ℕ) [NeZero grid] (j : ZMod grid) (n : ℤ) :
    Calibration.gridTurn grid (-(j*(n:ZMod grid)))=
      -(j.val:ℚ)*(n:ℚ)/grid-((roundDyadic 0 (-(j.val:ℚ)*(n:ℚ)/grid)).numerator:ℚ) := by
  have he : -(j*(n:ZMod grid))=(-((j.val:ℤ)*n):ℤ) := by simp
  rw [he,gridTurn_intCast]
  push_cast
  simp only [neg_mul]

def fractionalValue (x : Parts) : Parts := x.sub (DyadicFloor.result 0 x)
def fractionCode (source target scratch : ℕ) : Code :=
  .seq (DyadicFloor.code 0 scratch source) (NatAssign.code (binaryStage .sub target source scratch))

theorem fractionalValue_value (x : Parts) (hx : x.Valid) :
    (fractionalValue x).value=x.value-((roundDyadic 0 x.value).numerator:ℚ) := by
  rw [fractionalValue,Parts.sub_value x _ hx (DyadicFloor.result_valid _ _),DyadicFloor.result_value _ _ hx]

theorem fractionalValue_gridTurn (grid : ℕ) [NeZero grid] (j : ZMod grid) (n : ℤ)
    (x : Parts) (hx : x.Valid) (hvalue : x.value= -(j.val:ℚ)*(n:ℚ)/grid) :
    (fractionalValue x).value=Calibration.gridTurn grid (-(j*(n:ZMod grid))) := by
  rw [fractionalValue_value x hx,hvalue,characterTurn]

#print axioms characterTurn
#print axioms fractionalValue_gridTurn
end Maxwell.Continuum.Profile.WaveMachine
