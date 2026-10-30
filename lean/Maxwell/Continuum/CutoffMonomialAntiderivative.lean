import Maxwell.Continuum.RationalDataflowRowMap
import Maxwell.Continuum.CutoffAntiderivativeMapWidths

/-! The antiderivative conversion reads the total lane of the generated
Chebyshev cache directly. The sampled table below is only a semantic view;
execution reads the original cache, and no separately stored view is assumed. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def monomialTotalIndex {n : ℕ} (i : Fin n) : Fin (4*(n+1)) :=
  ⟨4*i.val+6,by omega⟩

def monomialTotalTable {n : ℕ} (a : Table (4*(n+1))) : Table n where
  width := a.width
  basePositive := a.basePositive
  baseNegative := a.baseNegative
  baseDenominator := a.baseDenominator
  clock := a.clock
  positive := Vector.ofFn (fun i => a.positive.get (monomialTotalIndex i))
  negative := Vector.ofFn (fun i => a.negative.get (monomialTotalIndex i))
  denominator := Vector.ofFn (fun i => a.denominator.get (monomialTotalIndex i))
  width_pos := a.width_pos
  clock_length := a.clock_length

theorem monomialTotalTable_get {n : ℕ} (a : Table (4*(n+1))) (i : Fin n) :
    (monomialTotalTable a).get i=a.getD (4*i.val+6) := by
  simp only [monomialTotalTable,Table.get,vector_get_ofFn,Table.getD,
    dite_eq_left (show 4*i.val+6<4*(n+1) by omega),monomialTotalIndex]

theorem monomialTotalTable_getD {n : ℕ} (a : Table (4*(n+1))) (i : ℕ) (hi : i<n) :
    (monomialTotalTable a).getD i=a.getD (4*i+6) := by
  rw [Table.getD,dite_eq_left hi,monomialTotalTable_get]

theorem monomialTotal_iterate {n : ℕ} (a : Table (4*(n+1))) (v : ℕ→Parts)
    (k : ℕ) (hk : k≤n) :
    rowIterate a 4 [(6,1)] antiderivativeScaleControl n v k=
      iterate (monomialTotalTable a) 1 antiderivativeScaleControl v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rowIterate,rowPlanValues,iterate,ih (by omega),
      monomialTotalTable_getD a (n-1-k) (by omega)]

theorem monomialTotal_loaded {n : ℕ} (a : Table (4*(n+1))) (v : ℕ→Parts)
    (k : ℕ) (hk : k<n) :
    rowLoaded a 4 [(6,1)] antiderivativeScaleControl n v k=
      loaded (monomialTotalTable a) 1 antiderivativeScaleControl v k := by
  simp only [rowLoaded,rowPlanValues,loaded,monomialTotal_iterate a v k hk.le,
    monomialTotalTable_getD a (n-1-k) (by omega)]

def monomialAntiderivativeCode : Code :=
  rowMapCode 4 [(6,1)] antiderivativeScaleControl 0

def monomialAntiderivativeValues {n : ℕ} (a : Table (4*(n+1))) : Fin n→Parts :=
  rowMapValues a 4 [(6,1)] antiderivativeScaleControl n 0 (scaleInitial n)

theorem monomialAntiderivativeValues_eq {n : ℕ} (a : Table (4*(n+1))) (i : Fin n) :
    monomialAntiderivativeValues a i=
      mapValues (monomialTotalTable a) antiderivativeScaleControl 0 (scaleInitial n) i := by
  unfold monomialAntiderivativeValues rowMapValues mapValues
  rw [monomialTotal_iterate a _ _ (Nat.sub_le _ _)]

theorem monomialAntiderivativeValues_width {n : ℕ} (a : Table (4*(n+1))) (W : ℕ)
    (hw : ∀i:Fin n,(a.getD (4*i.val+6)).Width W) (i : Fin n) :
    (monomialAntiderivativeValues a i).Width (scaleStateWidth n W) := by
  rw [monomialAntiderivativeValues_eq]
  apply scale_iterate_width (monomialTotalTable a) W
    (fun i => by rw [monomialTotalTable_get];exact hw i) (n-i.val) (Nat.sub_le _ _) 0
  decide

theorem monomialAntiderivativeValues_valid {n : ℕ} (a : Table (4*(n+1)))
    (hv : ∀i:Fin n,(a.getD (4*i.val+6)).Valid) (i : Fin n) :
    (monomialAntiderivativeValues a i).Valid := by
  rw [monomialAntiderivativeValues_eq]
  apply scale_iterate_good (monomialTotalTable a)
    (fun i => by rw [monomialTotalTable_get];exact hv i) (n-i.val) (Nat.sub_le _ _) 0
  decide

theorem monomialAntiderivativeValues_value (N : ℕ)
    (a : Table (4*(Profile.profileDegree N+1)))
    (hc : ∀i:Fin (Profile.profileDegree N),
      (a.getD (4*i.val+6)).value=(monomialCoefficient N i).value)
    (i : Fin (Profile.profileDegree N)) :
    (monomialAntiderivativeValues a i).value=(antiderivativeCoefficient N i).value := by
  rw [monomialAntiderivativeValues_eq]
  exact scale_map_value N (monomialTotalTable a)
    (fun i => by rw [monomialTotalTable_get];exact hc i) i

#print axioms monomialAntiderivativeValues_value
end Maxwell.Continuum.Calibration.RawCutoff
