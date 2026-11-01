import Maxwell.Continuum.SourceRoutingGeometryEmission
import Maxwell.Continuum.SourceGeometryCursorCount
import Maxwell.Cost.ArrayWrite

/-! The exact produced memory satisfies the serializer's geometry boundary;
the count remains the actual canonical cursor word. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical Maxwell.Logical.Routing
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

theorem stored_of_write {v e : ℕ} (saved : SourceEmission.Geometry v e) (memory : ℕ→Bool)
    (base width : ℕ) (positive : 0<width)
    (fits : ∀i,((packedVector saved).get i).bits.length≤width) :
    StoredGeometry saved base width
      (MemoryWord.writeBits memory base ((packed saved).flatMap (IncidenceEncoding.word width))) := by
  have listEq : List.ofFn (packedVector saved).get=packed saved := by
    apply List.ext_getElem
    · simp only [List.length_ofFn,packed_length]
    · intro i hi hj
      simp only [List.getElem_ofFn,packedVector,Vector.get,List.getElem_toArray,Fin.val_cast]
  have h:=BitArray.represents_flatMap (packedVector saved) (IncidenceEncoding.word width) width
    (fun _=>IncidenceEncoding.word_length _ _) memory base
  rw [listEq] at h
  exact ⟨positive,fits,h⟩

theorem source_executes (S : Source.SparseSystem) (precision : ℕ)
    (p : Plan (2*portHalfSide ((sourceCircuit S precision).size+(sourceCircuit S precision).size+
      (sourceSquareEntries S precision).length)))
    (n : ℕ)
    (fits₀ : GeometrySort.Fits p.path.history.width (PhaseKeys.first (SourceRouting.indexedData S precision).colors))
    (fits₁ : GeometrySort.Fits p.path.history.width (PhaseKeys.middle (SourceRouting.indexedData S precision).colors))
    (fits₂ : GeometrySort.Fits p.path.history.width (PhaseKeys.last (SourceRouting.indexedData S precision).colors))
    (room : packedLength (SourceEmission.geometry S precision)+1+
      3072*(2*portHalfSide ((sourceCircuit S precision).size+(sourceCircuit S precision).size+
        (sourceSquareEntries S precision).length))≤n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : State (SourceRouting.indexedData S precision) p 0 0 s) (counterBlank : Blank s.val 1258)
    (totalWord : Word s.val 141 ((sourceCircuit S precision).size+(sourceCircuit S precision).size+
      (sourceSquareEntries S precision).length))
    (leftWord : Word s.val 154 ((sourceCircuit S precision).size+(sourceCircuit S precision).size))
    (edgeWord : Word s.val 153 ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length)) :
    ∃steps t,Executes input tape code steps s t ∧
      steps≤price p n ((sourceCircuit S precision).size+(sourceCircuit S precision).size+
        (sourceSquareEntries S precision).length)
        ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length)
        ((sourceCircuit S precision).size+(sourceCircuit S precision).size) ∧
      State (SourceRouting.indexedData S precision) p (packedLength (SourceEmission.geometry S precision))
        ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length) t ∧
      Blank t.val 1258 ∧ StoredGeometry (SourceEmission.geometry S precision) p.path.base p.path.width t.val.memory ∧
      Represents S precision (SourceEmission.geometry S precision) ∧
      ArchiveFrame work s.val t.val ∧
      Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory t.val.memory := by
  let data:=SourceRouting.indexedData S precision
  have vertices:=Fintype.card_le_of_injective _ data.tile_injective
  have edges:=Fintype.card_le_of_injective _ data.pair_injective
  simp only [Fintype.card_fin,Fintype.card_prod] at vertices edges
  obtain ⟨steps,t,he,hc,ts,zt,mt,ft,tm⟩:=executes data p vertices edges
    (fun _=>rfl) (fun _=>rfl) ((sourceCircuit S precision).size+(sourceCircuit S precision).size) (by omega)
    (fun i hi=>by
      change decide ((sourceCircuit S precision).size+(sourceCircuit S precision).size ≤ i.val)=false
      exact decide_eq_false (by omega))
    (fun i hi=>by
      change decide ((sourceCircuit S precision).size+(sourceCircuit S precision).size ≤ i.val)=true
      exact decide_eq_true hi)
    (SourceEmission.geometry S precision)
    (fun _=>by simp only [SourceEmission.geometry,SortArrays.get_ofFn,data])
    (fun _=>by simp only [SourceEmission.geometry,SortArrays.get_ofFn,data])
    n fits₀ fits₁ fits₂ room input tape s state counterBlank totalWord leftWord edgeWord
  have represented:=geometry_represents S precision
  have width : ∀i,((packedVector (SourceEmission.geometry S precision)).get i).bits.length≤p.path.width:=by
    intro i
    apply (Represents.packed_width S precision represented i).trans
    have side : SourceRouting.side S precision=
        2*portHalfSide ((sourceCircuit S precision).size+(sourceCircuit S precision).size+
          (sourceSquareEntries S precision).length):=by
      unfold SourceRouting.side
      rw [SourceEnumeration.vertex_count]
      rfl
    rw [side]
    exact p.path.coordinate_width
  exact ⟨steps,t,he,hc,ts,zt,by rw [mt];exact stored_of_write _ _ _ _ p.path.positive width,
    represented,ft,tm⟩

#print axioms source_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
