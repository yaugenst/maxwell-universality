import Maxwell.Continuum.GlueDataflowCost
import Maxwell.Continuum.DyadicFloorRuntime
import Maxwell.Continuum.PhaseDataflowCost
import Maxwell.Continuum.CutoffRawArithmetic
import Maxwell.Continuum.ProfileEncoded

/-! Literal unreduced arithmetic for the profile-table producer. These
identities connect the runtime phase/glue/floor outputs to the existing
encoded coefficients; execution and operation counts are separate leaves. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def gridArgument (grid j : ℕ) : Parts := ⟨j,0,grid⟩
def integerArgument (k : ℤ) : Parts := ⟨k.toNat,(-k).toNat,1⟩
def dftArgument (grid j : ℕ) (k : ℤ) : Parts := (gridArgument grid j).mul (integerArgument (-k))
def angularParts (P : ℕ) (x : Parts) : Parts :=
  Glue.result (P+4) ((Parts.literal 1).sub (Phase.result cosineSigns 1 (P+4) x))
def dftTerm (grid D P : ℕ) (k : ℤ) (j : ℕ) : Parts :=
  (angularParts P (gridArgument grid j)).mul
    (Phase.result cosineSigns (D+1) P (dftArgument grid j k))
def dftParts (grid D P : ℕ) (k : ℤ) : Parts :=
  (gridArgument grid 1).mul (Calibration.RawCutoff.sum (dftTerm grid D P k) grid)
def sampledParts (grid D P j : ℕ) : Parts :=
  if j=0 then dftParts grid D P 0
  else (dftParts grid D P (j:ℤ)).add (dftParts grid D P (-(j:ℤ)))
def roundedIntegerParts (N j : ℕ) : Parts :=
  DyadicFloor.result (profileWorkBits N)
    (sampledParts (profileGrid N) (profileDegree N) (profileWorkBits N) j)
def endpointInteger (N : ℕ) : Parts := Calibration.RawCutoff.sum (roundedIntegerParts N) (profileDegree N)
def slopeInteger (N : ℕ) : Parts := Calibration.RawCutoff.sum
  (fun j => (roundedIntegerParts N j).mul (integerArgument ((j:ℤ)^2))) (profileDegree N)
def encodedIntegerParts (N j : ℕ) : Parts :=
  ((roundedIntegerParts N j).add
    (if j=0 then (slopeInteger N).sub (endpointInteger N) else Parts.literal 0)).sub
    (if j=1 then slopeInteger N else Parts.literal 0)
def encodedParts (N j : ℕ) : Parts :=
  (encodedIntegerParts N j).mul (gridArgument (2^profileWorkBits N) 1)

theorem gridArgument_valid (grid j : ℕ) (hg : 0<grid) : (gridArgument grid j).Valid := hg
theorem gridArgument_value (grid j : ℕ) : (gridArgument grid j).value=(j:ℚ)/grid := by
  simp [gridArgument,Parts.value]
theorem integerArgument_valid (k : ℤ) : (integerArgument k).Valid := Nat.zero_lt_one

theorem integerArgument_value (k : ℤ) : (integerArgument k).value=(k:ℚ) := by
  unfold integerArgument Parts.value
  simp only [Nat.cast_one,div_one]
  exact_mod_cast Int.toNat_sub_toNat_neg k

theorem dftArgument_valid (grid j : ℕ) (k : ℤ) (hg : 0<grid) : (dftArgument grid j k).Valid :=
  Parts.mul_valid (gridArgument_valid _ _ hg) (integerArgument_valid _)

theorem dftArgument_value (grid j : ℕ) (k : ℤ) :
    (dftArgument grid j k).value=-(j:ℚ)*k/grid := by
  rw [dftArgument,Parts.mul_value,gridArgument_value,integerArgument_value]
  push_cast
  ring

theorem angularParts_valid (P : ℕ) (x : Parts) (hx : x.Valid) : (angularParts P x).Valid :=
  Glue.result_valid _ _ (Parts.sub_valid (Parts.literal_valid _) (Phase.result_valid _ _ _ _ hx))

theorem angularParts_value (P : ℕ) (x : Parts) (hx : x.Valid) :
    (angularParts P x).value=(angularApprox x.value P).center := by
  rw [angularParts,Glue.result_value _ _
    (Parts.sub_valid (Parts.literal_valid _) (Phase.result_valid _ _ _ _ hx)),
    Parts.sub_value _ _ (Parts.literal_valid _) (Phase.result_valid _ _ _ _ hx),
    Parts.literal_value,Phase.result_cos _ _ _ hx]
  rfl

theorem dftTerm_valid (grid D P : ℕ) (k : ℤ) (j : ℕ) (hg : 0<grid) :
    (dftTerm grid D P k j).Valid :=
  Parts.mul_valid (angularParts_valid _ _ (gridArgument_valid _ _ hg))
    (Phase.result_valid _ _ _ _ (dftArgument_valid _ _ _ hg))

theorem dftTerm_value (grid D P : ℕ) (k : ℤ) (j : ℕ) (hg : 0<grid) :
    (dftTerm grid D P k j).value=(angularApprox ((j:ℚ)/grid) P).center*
      (Calibration.cosTurnApprox (-(j:ℚ)*k/grid) (D+1) P).center := by
  rw [dftTerm,Parts.mul_value,angularParts_value _ _ (gridArgument_valid _ _ hg),
    gridArgument_value,Phase.result_cos _ _ _ (dftArgument_valid _ _ _ hg),dftArgument_value]

theorem zmod_sum_val (grid : ℕ) [NeZero grid] (f : ℕ→ℚ) :
    (∑j:ZMod grid,f j.val)=∑j∈Finset.range grid,f j := by
  cases grid with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact Fin.sum_univ_eq_sum_range f (n+1)

theorem dftParts_valid (grid D P : ℕ) (k : ℤ) (hg : 0<grid) : (dftParts grid D P k).Valid :=
  Parts.mul_valid (gridArgument_valid _ _ hg)
    (Calibration.RawCutoff.sum_valid _ _ (fun j _ => dftTerm_valid _ _ _ _ j hg))

theorem dftParts_value (grid D P : ℕ) [NeZero grid] (k : ℤ) :
    (dftParts grid D P k).value=rationalSampleCoefficient grid D P k := by
  have hg : 0<grid := Nat.pos_of_ne_zero (NeZero.ne grid)
  rw [dftParts,Parts.mul_value,gridArgument_value,
    Calibration.RawCutoff.sum_value _ _ (fun j _ => dftTerm_valid _ _ _ _ j hg),
    rationalSampleCoefficient]
  rw [zmod_sum_val grid (fun j => (angularApprox ((j:ℚ)/grid) P).center *
    (Calibration.cosTurnApprox (-(j:ℚ)*k/grid) (D+1) P).center)]
  simp_rw [dftTerm_value _ _ _ _ _ hg]
  simp only [Nat.cast_one,one_div]

theorem sampledParts_valid (grid D P j : ℕ) (hg : 0<grid) : (sampledParts grid D P j).Valid := by
  unfold sampledParts
  split_ifs
  · exact dftParts_valid _ _ _ _ hg
  · exact Parts.add_valid (dftParts_valid _ _ _ _ hg) (dftParts_valid _ _ _ _ hg)

theorem sampledParts_value (grid D P j : ℕ) [NeZero grid] :
    (sampledParts grid D P j).value=sampledCosineCoefficient grid D P j := by
  have hg : 0<grid := Nat.pos_of_ne_zero (NeZero.ne grid)
  unfold sampledParts sampledCosineCoefficient
  split_ifs
  · exact dftParts_value _ _ _ _
  · rw [Parts.add_value _ _ (dftParts_valid _ _ _ _ hg) (dftParts_valid _ _ _ _ hg),
      dftParts_value,dftParts_value]

theorem roundedIntegerParts_valid (N j : ℕ) : (roundedIntegerParts N j).Valid :=
  DyadicFloor.result_valid _ _

theorem roundedIntegerParts_value (N j : ℕ) :
    (roundedIntegerParts N j).value=((roundedCoefficient N j).numerator:ℚ) := by
  rw [roundedIntegerParts,DyadicFloor.result_value _ _
    (sampledParts_valid _ _ _ _ (profileGrid_pos N)),sampledParts_value]
  rfl

theorem endpointInteger_valid (N : ℕ) : (endpointInteger N).Valid :=
  Calibration.RawCutoff.sum_valid _ _ (fun j _ => roundedIntegerParts_valid N j)
theorem slopeInteger_valid (N : ℕ) : (slopeInteger N).Valid :=
  Calibration.RawCutoff.sum_valid _ _ (fun j _ => Parts.mul_valid
    (roundedIntegerParts_valid N j) (integerArgument_valid _))

theorem endpointInteger_value (N : ℕ) :
    (endpointInteger N).value=(endpointValueNumerator (profileDegree N) (roundedCoefficient N):ℚ) := by
  rw [endpointInteger,Calibration.RawCutoff.sum_value _ _ (fun j _ => roundedIntegerParts_valid N j)]
  simp only [endpointValueNumerator,Int.cast_sum,roundedIntegerParts_value]

theorem slopeInteger_value (N : ℕ) :
    (slopeInteger N).value=(endpointSlopeNumerator (profileDegree N) (roundedCoefficient N):ℚ) := by
  rw [slopeInteger,Calibration.RawCutoff.sum_value _ _ (fun j _ => Parts.mul_valid
    (roundedIntegerParts_valid N j) (integerArgument_valid _))]
  simp only [endpointSlopeNumerator,Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
    Parts.mul_value,roundedIntegerParts_value,integerArgument_value]

theorem encodedIntegerParts_valid (N j : ℕ) : (encodedIntegerParts N j).Valid := by
  unfold encodedIntegerParts
  apply Parts.sub_valid
  · apply Parts.add_valid (roundedIntegerParts_valid N j)
    split_ifs
    · exact Parts.sub_valid (slopeInteger_valid N) (endpointInteger_valid N)
    · exact Parts.literal_valid 0
  · split_ifs
    · exact slopeInteger_valid N
    · exact Parts.literal_valid 0

theorem encodedIntegerParts_value (N j : ℕ) :
    (encodedIntegerParts N j).value=((encodedCoefficient N j).numerator:ℚ) := by
  have hsum : (if j=0 then (slopeInteger N).sub (endpointInteger N) else Parts.literal 0).Valid := by
    split_ifs
    · exact Parts.sub_valid (slopeInteger_valid N) (endpointInteger_valid N)
    · exact Parts.literal_valid 0
  have hsub : (if j=1 then slopeInteger N else Parts.literal 0).Valid := by
    split_ifs
    · exact slopeInteger_valid N
    · exact Parts.literal_valid 0
  rw [encodedIntegerParts,Parts.sub_value _ _ (Parts.add_valid (roundedIntegerParts_valid N j) hsum) hsub,
    Parts.add_value _ _ (roundedIntegerParts_valid N j) hsum,roundedIntegerParts_value]
  unfold encodedCoefficient matchedCoefficient
  split_ifs <;> simp only [Parts.sub_value _ _ (slopeInteger_valid N) (endpointInteger_valid N),
    slopeInteger_value,endpointInteger_value,Parts.literal_value,Int.cast_add,Int.cast_neg,Int.cast_zero] <;> ring

theorem encodedParts_valid (N j : ℕ) : (encodedParts N j).Valid :=
  Parts.mul_valid (encodedIntegerParts_valid N j) (gridArgument_valid _ _ (by positivity))

theorem encodedParts_value (N j : ℕ) : (encodedParts N j).value=(encodedCoefficient N j).value := by
  rw [encodedParts,Parts.mul_value,encodedIntegerParts_value,gridArgument_value]
  simp only [Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,Dyadic.value]
  ring

#print axioms encodedParts_value
#print axioms encodedParts_valid
end Maxwell.Continuum.Profile.Runtime
