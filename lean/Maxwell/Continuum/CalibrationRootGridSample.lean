import Maxwell.Continuum.CalibrationRootGridEnumeration
import Maxwell.Continuum.CalibrationRootGridLoad
import Maxwell.Continuum.CalibrationRootProductMachine

/-! Exact semantics of the executed grid decoder, fraction loads, centering,
and elementary evaluations. No sample table is an input to this program. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def sampleParts (N : ℕ) (n : ℕ→ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  RootProduct.values N (RootGridCenter.values (loadParts (values n) v))

def sampleCode : Code := .seq code (.seq loadCode (.seq RootGridCenter.code RootProduct.code))

theorem loaded_coordinate_valid (n : ℕ→ℕ) (v : ℕ→Parts) (hg : 0<n 331) (i : Fin 3) :
    (loadParts (values n) v i).Valid := by
  rw [loadParts_coordinate]
  change 0<values n 331
  rw [values_keep n 331 (by decide)]
  exact hg

theorem loaded_coordinate_turn (grid : ℕ) [NeZero grid] (index : ℕ)
    (n : ℕ→ℕ) (v : ℕ→Parts) (hg : n 331=grid) (hk : n 330=index) (i : Fin 3) :
    (loadParts (values n) v i).value=Calibration.gridTurn grid (point grid index i) := by
  rw [loadParts_coordinate,values_coordinates,values_keep n 331 (by decide),hg,hk]
  simp only [FractionWord.part,Parts.value,Nat.cast_zero,sub_zero,Calibration.gridTurn,point_val]

theorem loaded_phase_turn (grid : ℕ) [NeZero grid] (index : ℕ) (a : Fin 3→ZMod grid)
    (n : ℕ→ℕ) (v : ℕ→Parts) (hg : n 331=grid) (hk : n 330=index)
    (ha : ∀i,![n 336,n 337,n 338] i=(a i).val) :
    (loadParts (values n) v 5).value=Calibration.gridTurn grid (∑i,a i*point grid index i) := by
  have he : (∑i:Fin 3,(![n 336,n 337,n 338] i)*digits (n 331) (n 330) i)%n 331=
      (∑i,a i*point grid index i).val := by
    simp only [hg,hk,ha]
    exact phase_remainder grid index a
  rw [loadParts_phase,values_phase,he,values_keep n 331 (by decide),hg]
  simp only [FractionWord.part,Parts.value,Nat.cast_zero,sub_zero,Calibration.gridTurn]

theorem sampleParts_exact (grid : ℕ) [NeZero grid] (N index : ℕ)
    (scale : ℚ) (frequency : Fin 3→ℤ) (n : ℕ→ℕ) (v : ℕ→Parts)
    (hg : n 331=grid) (hk : n 330=index)
    (ha : ∀i,![n 336,n 337,n 338] i=
      ((-(PeriodicSampling.Product.frequency grid frequency)) i).val)
    (hv : (v 9).Valid) (hs : (v 9).value=scale) :
    (sampleParts N n v 6).value=(Calibration.rootProductSample grid scale N frequency (point grid index)).re.center ∧
    (sampleParts N n v 7).value=(Calibration.rootProductSample grid scale N frequency (point grid index)).im.center := by
  have hpos : 0<n 331 := hg ▸ Nat.pos_of_ne_zero (NeZero.ne grid)
  have hcoords := loaded_coordinate_valid n v hpos
  have hscale : loadParts (values n) v 9=v 9 := loadParts_other _ _ _ (by omega)
  have hvc (i : Fin 3) : (RootSample.coordinates (RootGridCenter.values (loadParts (values n) v)) i).Valid := by
    change (RootGridCenter.values (loadParts (values n) v) i).Valid
    rw [RootGridCenter.values_coordinates _ hcoords i,hscale]
    exact Parts.mul_valid (RootGridCenter.centeredPart_valid _ (hcoords i)) hv
  have hp : (RootGridCenter.values (loadParts (values n) v) 5).Valid := by
    rw [RootGridCenter.values_other _ 5 (by omega),loadParts_phase]
    change 0<values n 331
    rw [values_keep n 331 (by decide)]
    exact hpos
  apply RootProduct.rootProductSample_values grid N scale frequency (point grid index) _ hvc hp
  · intro i
    exact RootGridCenter.values_centeredGrid grid (point grid index) scale _ hcoords
      (loaded_coordinate_turn grid index n v hg hk) (hscale ▸ hs) i
  · rw [RootGridCenter.values_other _ 5 (by omega)]
    exact loaded_phase_turn grid index _ n v hg hk ha

theorem sampleParts_other (N : ℕ) (n : ℕ→ℕ) (v : ℕ→Parts) (i : ℕ)
    (hi : 8 ≤ i) : sampleParts N n v i=v i := by
  rw [sampleParts,RootProduct.values_unchanged _ _ i (by omega),
    RootGridCenter.values_other _ i (by omega),loadParts_other _ _ i (by omega)]

#print axioms sampleParts_exact
#print axioms sampleParts_other
end Maxwell.Continuum.RationalDataflow.RootGrid
