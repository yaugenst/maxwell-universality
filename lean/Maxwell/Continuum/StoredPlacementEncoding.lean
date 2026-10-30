import Maxwell.Continuum.StoredPlacementArray
import Maxwell.Continuum.ContinuumDescription

/-! The executed placement stream is the continuum description's literal
readout-record format, in its existing original-coordinate order. -/
namespace Maxwell.Continuum.RationalDataflow.StoredPlacement
open Maxwell.Cost
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem range_flatMap_finRange {α : Type*} (J : ℕ) (f : ℕ→List α) :
    (List.range J).flatMap f=(List.finRange J).flatMap (fun i=>f i.val) := by
  have hm : (List.finRange J).map Fin.val=List.range J := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [←hm,List.flatMap_map]

theorem arrayBits_finRange {J L : ℕ} (z : ℕ→ℤ) (center : Fin J→Fin 3→ℤ)
    (hz : ∀i k,z (3*i.val+k.val)=center i k) :
    arrayBits z L J=Codec.list (fun i=>Codec.int (center i 0)++Codec.int (center i 1)++
      Codec.int (center i 2)++Codec.nat L) (List.finRange J) := by
  unfold arrayBits stream Codec.list
  rw [List.length_finRange,range_flatMap_finRange]
  congr 1
  apply List.flatMap_congr
  intro i _
  simp only [recordBits,←hz i 0,←hz i 1,←hz i 2]
  rfl

theorem arrayBits_readout (p : Maxwell.Source.Parameters)
    (S : Maxwell.Source.SparseSystem) (hm : 0<S.nnz) (z : ℕ→ℤ)
    (hz : ∀(i:Fin S.n) (k:Fin 3),z (3*i.val+k.val)=
      RealizationParameters.integerCenter p S hm
        (Sum.inl (Maxwell.Composition.SourceRouting.inputCoordinate S
          (RealizationParameters.precision p S hm) i)) k) :
    arrayBits z (RealizationParameters.length p S hm) S.n=
      RealizationParameters.readoutPlacementStream p S hm := by
  unfold RealizationParameters.readoutPlacementStream RealizationParameters.readoutPlacementBits
    RealizationParameters.placementBits
  exact arrayBits_finRange z (fun i k=>RealizationParameters.integerCenter p S hm
      (Sum.inl (Maxwell.Composition.SourceRouting.inputCoordinate S
        (RealizationParameters.precision p S hm) i)) k) hz

#print axioms arrayBits_readout
end Maxwell.Continuum.RationalDataflow.StoredPlacement
