import Maxwell.Continuum.CalibrationNeumannActual
import Maxwell.Continuum.RawSharedDenominator

/-! Cached calibration from unreduced runtime coefficient channels. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 2000000

abbrev CoefficientIndex (n : ℕ) := Fin n⊕(Fin n×Fin n)

def rawSource {n : ℕ} (a : CoefficientIndex n→Parts) : Channels n :=
  ⟨fun i => (SharedTable.integerParts a (.inl i)).positive,
   fun i => (SharedTable.integerParts a (.inl i)).negative⟩

def rawMatrix {n : ℕ} (a : CoefficientIndex n→Parts) : ChannelMatrix n :=
  ⟨fun i j => (SharedTable.integerParts a (.inr (i,j))).positive,
   fun i j => (SharedTable.integerParts a (.inr (i,j))).negative⟩

def rawCoefficientBound (n W : ℕ) : ℕ := 2^((n+n*n+1)*(W+1))

theorem coefficientIndex_card (n : ℕ) : Fintype.card (CoefficientIndex n)=n+n*n := by
  simp [CoefficientIndex]

theorem rawSource_bounded {n : ℕ} (a : CoefficientIndex n→Parts) (W : ℕ)
    (ha : ∀ i, (a i).Width W) : (rawSource a).Bounded (rawCoefficientBound n W) := by
  intro i
  have hw := SharedTable.integerParts_width a W ha (.inl i)
  rw [coefficientIndex_card] at hw
  have hwidth : (n+n*n+1)*W+1≤(n+n*n+1)*(W+1) := by nlinarith
  exact ⟨SharedTable.bits_power_bound _ _ (hw.1.trans hwidth),
    SharedTable.bits_power_bound _ _ (hw.2.1.trans hwidth)⟩

theorem rawMatrix_bounded {n : ℕ} (a : CoefficientIndex n→Parts) (W : ℕ)
    (ha : ∀ i, (a i).Width W) : (rawMatrix a).Bounded (rawCoefficientBound n W) := by
  intro i j
  have hw := SharedTable.integerParts_width a W ha (.inr (i,j))
  rw [coefficientIndex_card] at hw
  have hwidth : (n+n*n+1)*W+1≤(n+n*n+1)*(W+1) := by nlinarith
  exact ⟨SharedTable.bits_power_bound _ _ (hw.1.trans hwidth),
    SharedTable.bits_power_bound _ _ (hw.2.1.trans hwidth)⟩

theorem rawTable_uniformWidth {n : ℕ} (a : CoefficientIndex n→Parts) (W N : ℕ)
    (ha : ∀ i, (a i).Width W) :
    uniformWidth n (rawCoefficientBound n W) (rawCoefficientBound n W)
      (SharedTable.denominator a) N≤commonWidth n N (W+1) := by
  apply shared_uniformWidth n N (W+1) (n+n*n)
  · nlinarith
  · have hd := SharedTable.denominator_bound a W ha
    rw [coefficientIndex_card] at hd
    exact hd.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))
  · exact le_rfl
  · exact le_rfl

theorem rawTable_iteration {n : ℕ} (a : CoefficientIndex n→Parts)
    (ha : ∀ i, (a i).Valid) (K : ℕ) (i : Fin n) :
    sharedRationalIteration (SharedTable.denominator a) (rawMatrix a).value (rawSource a).value K i=
      rationalAffineIteration (fun i j => (a (.inr (i,j))).value) (fun i => (a (.inl i)).value) K i := by
  have source (i : Fin n) : ((rawSource a).value i:ℚ)/(SharedTable.denominator a:ℚ)=(a (.inl i)).value :=
    SharedTable.integerValue_sound a ha (.inl i)
  have matrix (i j : Fin n) : ((rawMatrix a).value i j:ℚ)/(SharedTable.denominator a:ℚ)=(a (.inr (i,j))).value :=
    SharedTable.integerValue_sound a ha (.inr (i,j))
  induction K generalizing i with
  | zero => rfl
  | succ K ih =>
    simp only [sharedRationalIteration,rationalAffineIteration,Pi.add_apply,Matrix.mulVec,dotProduct]
    rw [source]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [matrix,ih]

theorem rawTable_cached (t E : ℚ) (r : Fin 3→ℚ) (R : ℕ) (f : RationalRealField)
    (a : CoefficientIndex (aliasArraySize R)→Parts) (ha : ∀ i, (a i).Valid)
    (hvalue : ∀ i, (a i).value=cachedCoefficientTable t E r R f i) (K : ℕ)
    (i : Fin (aliasArraySize R)) :
    sharedRationalIteration (SharedTable.denominator a) (rawMatrix a).value (rawSource a).value K i=
      (cachedInverseApply t E r R f K).get i := by
  rw [rawTable_iteration a ha]
  have hmat : (fun i j => (a (.inr (i,j))).value)=cachedTransitionMatrix t E r R := by
    funext i j
    exact hvalue (.inr (i,j))
  have hsrc : (fun i => (a (.inl i)).value)=cachedForcing t E r R f := by
    funext i
    exact hvalue (.inl i)
  rw [hmat,hsrc]
  exact (congrFun (cachedInverseApply_affine t E r R f K) i).symm

#print axioms rawTable_uniformWidth
#print axioms rawTable_cached
end Maxwell.Continuum.Calibration.NeumannMachine
