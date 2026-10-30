import Maxwell.Continuum.ProfileRawProducer
import Maxwell.Continuum.GlueDataflowWidth
import Maxwell.Continuum.DyadicFloorOutputWidth

/-! Explicit polynomial bounds on every unreduced profile-producer value.
These are stored-channel bounds, including the denominators of the finite
DFT sums and the two signed channels retained by exact floor. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor
set_option maxHeartbeats 4000000

def angularPhaseWidth (U : ℕ) : ℕ := 2^68*(1+(U+4)+(U+1)+12)^4
def angularRawWidth (U : ℕ) : ℕ := 2^28*((U+4)+(angularPhaseWidth U+2)+9)^4
def dftPhaseWidth (U : ℕ) : ℕ := 2^68*((U+1)+U+(2*(U+1)+1)+12)^4
def dftTermWidth (U : ℕ) : ℕ := angularRawWidth U+dftPhaseWidth U+1
def dftRawWidth (U : ℕ) : ℕ := (U+1)+(U*(dftTermWidth U+1)+1)+1
def sampledRawWidth (U : ℕ) : ℕ := 2*dftRawWidth U+1
def roundedRawWidth (U : ℕ) : ℕ := 2*sampledRawWidth U+U+2
def endpointRawWidth (U : ℕ) : ℕ := U*(roundedRawWidth U+1)+1
def slopeRawWidth (U : ℕ) : ℕ := U*((roundedRawWidth U+(U^2+1)+1)+1)+1
def encodedRawWidth (U : ℕ) : ℕ :=
  roundedRawWidth U+2*slopeRawWidth U+endpointRawWidth U+U+5

theorem bits_le_of_le {j U : ℕ} (hj : j≤U) : j.bits.length≤U+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact lt_of_le_of_lt (hj.trans (Nat.le_succ _)) (Nat.lt_two_pow_self (n := U+1))

theorem gridArgument_width (grid j U : ℕ) (hg : grid≤U) (hj : j≤U) :
    (gridArgument grid j).Width (U+1) :=
  ⟨bits_le_of_le hj,by simp [gridArgument],bits_le_of_le hg⟩

theorem integerArgument_width (k : ℤ) (U : ℕ) (hk : k.natAbs≤U) :
    (integerArgument k).Width (U+1) := by
  have he := Int.toNat_add_toNat_neg_eq_natAbs k
  refine ⟨?_,?_,?_⟩
  · change k.toNat.bits.length≤U+1
    exact bits_le_of_le (by omega)
  · change (-k).toNat.bits.length≤U+1
    exact bits_le_of_le (by omega)
  · simpa only [integerArgument,Nat.one_bits,List.length_singleton] using (show 1≤U+1 by omega)

theorem angularParts_width (P U : ℕ) (x : Parts) (hP : P≤U) (hx : x.Width (U+1)) :
    (angularParts P x).Width (angularRawWidth U) := by
  have hp := Phase.result_width cosineSigns 1 (P+4) (U+1) x hx
  have hp' : (Phase.result cosineSigns 1 (P+4) x).Width (angularPhaseWidth U) :=
    hp.mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
  have hi := (Parts.literal_width RationalWords.width_one).sub hp'
  have hi' : ((Parts.literal 1).sub (Phase.result cosineSigns 1 (P+4) x)).Width
      (angularPhaseWidth U+2) := hi.mono (by omega)
  exact (Glue.result_width (P+4) _ _ hi').mono
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))

theorem dftTerm_width (grid D P U : ℕ) (k : ℤ) (j : ℕ)
    (hg : grid≤U) (hD : D≤U) (hP : P≤U) (hk : k.natAbs≤U) (hj : j≤U) :
    (dftTerm grid D P k j).Width (dftTermWidth U) := by
  have ha := angularParts_width P U _ hP (gridArgument_width grid j U hg hj)
  have hx := (gridArgument_width grid j U hg hj).mul
    (integerArgument_width (-k) U (by simpa only [Int.natAbs_neg] using hk))
  have hx' : (dftArgument grid j k).Width (2*(U+1)+1) := hx.mono (by omega)
  have hb := Phase.result_width cosineSigns (D+1) P (2*(U+1)+1) _ hx'
  have hb' : (Phase.result cosineSigns (D+1) P (dftArgument grid j k)).Width (dftPhaseWidth U) :=
    hb.mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
  exact ha.mul hb'

theorem dftParts_width (grid D P U : ℕ) (k : ℤ)
    (h1 : 1≤U) (hg : grid≤U) (hD : D≤U) (hP : P≤U) (hk : k.natAbs≤U) :
    (dftParts grid D P k).Width (dftRawWidth U) := by
  have hs := Calibration.RawCutoff.sum_width (dftTerm grid D P k) grid (dftTermWidth U)
    (fun j hj => dftTerm_width grid D P U k j hg hD hP hk (by omega))
  have hs' := hs.mono (Nat.add_le_add_right (Nat.mul_le_mul_right _ hg) 1)
  exact (gridArgument_width grid 1 U hg h1).mul hs'

theorem sampledParts_width (grid D P U j : ℕ)
    (h1 : 1≤U) (hg : grid≤U) (hD : D≤U) (hP : P≤U) (hj : j≤U) :
    (sampledParts grid D P j).Width (sampledRawWidth U) := by
  unfold sampledParts
  split_ifs
  · exact (dftParts_width grid D P U 0 h1 hg hD hP (by simp)).mono (by unfold sampledRawWidth;omega)
  · exact ((dftParts_width grid D P U (j:ℤ) h1 hg hD hP (by simpa using hj)).add
      (dftParts_width grid D P U (-(j:ℤ)) h1 hg hD hP (by simpa using hj))).mono
      (by unfold sampledRawWidth;omega)

theorem roundedIntegerParts_width (N j U : ℕ) (h1 : 1≤U)
    (hg : profileGrid N≤U) (hD : profileDegree N≤U) (hP : profileWorkBits N≤U) (hj : j≤U) :
    (roundedIntegerParts N j).Width (roundedRawWidth U) := by
  exact (DyadicFloor.result_raw_width _ _ _ (sampledParts_width _ _ _ _ _ h1 hg hD hP hj)).mono
    (by unfold roundedRawWidth;omega)

theorem endpointInteger_width (N U : ℕ) (h1 : 1≤U)
    (hg : profileGrid N≤U) (hD : profileDegree N≤U) (hP : profileWorkBits N≤U) :
    (endpointInteger N).Width (endpointRawWidth U) := by
  exact (Calibration.RawCutoff.sum_width _ _ _ (fun j hj =>
    roundedIntegerParts_width N j U h1 hg hD hP (by omega))).mono
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hD) 1)

theorem slopeInteger_width (N U : ℕ) (h1 : 1≤U)
    (hg : profileGrid N≤U) (hD : profileDegree N≤U) (hP : profileWorkBits N≤U) :
    (slopeInteger N).Width (slopeRawWidth U) := by
  have ht (j : ℕ) (hj : j<profileDegree N) :
      ((roundedIntegerParts N j).mul (integerArgument ((j:ℤ)^2))).Width
        (roundedRawWidth U+(U^2+1)+1) := by
    apply (roundedIntegerParts_width N j U h1 hg hD hP (by omega)).mul
    apply integerArgument_width
    simpa only [Int.natAbs_pow,Int.natAbs_natCast] using Nat.pow_le_pow_left (show j≤U by omega) 2
  exact (Calibration.RawCutoff.sum_width _ _ _ ht).mono
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hD) 1)

theorem encodedParts_width (N j U : ℕ) (h1 : 1≤U)
    (hg : profileGrid N≤U) (hD : profileDegree N≤U) (hP : profileWorkBits N≤U) (hj : j≤U) :
    (encodedParts N j).Width (encodedRawWidth U) := by
  have hs := slopeInteger_width N U h1 hg hD hP
  have he := endpointInteger_width N U h1 hg hD hP
  have hz : (Parts.literal 0).Width 1 := Parts.literal_width RationalWords.width_zero'
  have ha : (if j=0 then (slopeInteger N).sub (endpointInteger N) else Parts.literal 0).Width
      (slopeRawWidth U+endpointRawWidth U+1) := by
    split_ifs
    · exact hs.sub he
    · exact hz.mono (by omega)
  have hb : (if j=1 then slopeInteger N else Parts.literal 0).Width (slopeRawWidth U) := by
    split_ifs
    · exact hs
    · exact hz.mono (by unfold slopeRawWidth;omega)
  have hd : (gridArgument (2^profileWorkBits N) 1).Width (U+1) := by
    refine ⟨?_,by simp [gridArgument],?_⟩
    · simpa only [gridArgument,Nat.one_bits,List.length_singleton] using (show 1≤U+1 by omega)
    · simpa only [gridArgument,Nat.size_eq_bits_len,Nat.size_pow] using Nat.add_le_add_right hP 1
  exact ((((roundedIntegerParts_width N j U h1 hg hD hP hj).add ha).sub hb).mul hd).mono
    (by unfold encodedRawWidth;omega)

#print axioms encodedParts_width
end Maxwell.Continuum.Profile.Runtime
