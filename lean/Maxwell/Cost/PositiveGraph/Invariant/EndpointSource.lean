import Maxwell.Cost.PositiveGraph.Invariant.Endpoints
import Maxwell.Cost.PositiveGraph.Invariant.SourceRecords

namespace Maxwell.Cost.PositiveGraph.Invariant
open Maxwell.Logical

def sourceTables (W : ℕ) (S : Source.SparseSystem) (p : ℕ)
    (initial : Tables (sourceCircuit S p).size (sourceSquareEntries S p).length) :
    Tables (sourceCircuit S p).size (sourceSquareEntries S p).length :=
  foldTables W (sourceCircuit S p).size (sourceSquareEntries S p).length 0 (sourceRecords S p)
    (by simp) initial

theorem pad_fixedWidth (W n : ℕ) (hn : n<2^W) :
    FixedWidth.bits (W+3) (SourceCircuit.fixedWidth W n) = FixedWidth.bits (W+3) n.bits := by
  apply SourceCircuit.fixedWidth_eq (FixedWidth.bits_length _ _)
  rw [FixedWidth.bits_value _ _ (by simp),SourceCircuit.fixedWidth_value W n hn]

theorem source_endpoint_slot (W : ℕ) (S : Source.SparseSystem) (p : ℕ)
    (hd : (sourceCircuit S p).size<2^W)
    (initial : Tables (sourceCircuit S p).size (sourceSquareEntries S p).length)
    (k : Fin (sourceSquareEntries S p).length) (right side : Bool) :
    (sourceTables W S p initial).endpoints.get
      (slot (sourceSquareEntries S p).length k.val k.isLt right side) =
    FixedWidth.bits (W+3) (Composition.SourceCached.positiveEndpoint S p
      (finSumFinEquiv (if right then Sum.inr k else Sum.inl k)) side).val.bits := by
  have h := fold_endpoints_hit W (sourceCircuit S p).size (sourceSquareEntries S p).length 0
    (sourceRecords S p) (by simp) initial k.val (by simp) right side
  simp only [Nat.zero_add,sourceRecords_get] at h
  rw [sourceTables,h]
  have hr : (sourceSquareEntries S p)[k.val].row<(sourceCircuit S p).size :=
    ((sourceCircuit_rational S p).code.squareEntries_bounded (sourceOutput S p) _
      (List.getElem_mem k.isLt)).1
  cases right <;> cases side
  all_goals simp only [endpointPayload,Bool.false_eq_true,↓reduceIte,
    Composition.SourceCached.positiveEndpoint,Composition.SourceCached.endpointFromPairs,
    Equiv.symm_apply_apply]
  · change FixedWidth.bits (W+3) (SourceCircuit.fixedWidth W _) = _
    rw [pad_fixedWidth W _ (hr.trans hd)]
    rfl
  · simp [finSumFinEquiv,two_mul,Nat.add_comm]
  · rfl
  · simp [finSumFinEquiv,two_mul,Nat.add_comm]

private theorem incidence_card (K : ℕ) : Fintype.card (Fin (K+K) × Bool)=4*K := by
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  omega

theorem source_endpoint_incidence (W : ℕ) (S : Source.SparseSystem) (p : ℕ)
    (hd : (sourceCircuit S p).size<2^W)
    (initial : Tables (sourceCircuit S p).size (sourceSquareEntries S p).length)
    (edge : Fin ((sourceSquareEntries S p).length+(sourceSquareEntries S p).length)) (side : Bool) :
    (sourceTables W S p initial).endpoints.get (Fin.cast (incidence_card _)
      (Routing.Gluing.incidenceIndex _ (edge,side))) =
    FixedWidth.bits (W+3) (Composition.SourceCached.positiveEndpoint S p edge side).val.bits := by
  obtain ⟨e,rfl⟩ := finSumFinEquiv.surjective edge
  cases e with
  | inl k =>
    have he : Fin.cast (incidence_card _) (Routing.Gluing.incidenceIndex _ (finSumFinEquiv (.inl k),side)) =
        slot (sourceSquareEntries S p).length k.val k.isLt false side := by
      apply Fin.ext
      simp only [Fin.val_cast,incidence_slot,slot,Bool.false_eq_true,↓reduceIte,zero_add]
      rfl
    rw [he]
    exact source_endpoint_slot W S p hd initial k false side
  | inr k =>
    have he : Fin.cast (incidence_card _) (Routing.Gluing.incidenceIndex _ (finSumFinEquiv (.inr k),side)) =
        slot (sourceSquareEntries S p).length k.val k.isLt true side := by
      apply Fin.ext
      simp only [Fin.val_cast,incidence_slot,slot,↓reduceIte]
      congr 1
    rw [he]
    exact source_endpoint_slot W S p hd initial k true side

def sourceEndpointWords (W : ℕ) (S : Source.SparseSystem) (p : ℕ) :
    Vector (List Bool) (4*(sourceSquareEntries S p).length) :=
  Vector.ofFn fun i => FixedWidth.bits (W+3)
    (Composition.SourceRouting.flatEndpoint S p (Fin.cast (incidence_card _).symm i)).val.bits

theorem source_endpoints_exact (W : ℕ) (S : Source.SparseSystem) (p : ℕ)
    (hd : (sourceCircuit S p).size<2^W)
    (initial : Tables (sourceCircuit S p).size (sourceSquareEntries S p).length) :
    (sourceTables W S p initial).endpoints=sourceEndpointWords W S p := by
  apply Vector.ext
  intro i hi
  let j : Fin (4*(sourceSquareEntries S p).length) := ⟨i,hi⟩
  obtain ⟨⟨edge,side⟩,he⟩ := (Routing.Gluing.incidenceIndex _).surjective (Fin.cast (incidence_card _).symm j)
  have hh := source_endpoint_incidence W S p hd initial edge side
  have hj : Fin.cast (incidence_card _) (Routing.Gluing.incidenceIndex _ (edge,side))=j := by rw [he]; rfl
  rw [hj] at hh
  change (sourceTables W S p initial).endpoints.get j = (sourceEndpointWords W S p).get j
  rw [hh]
  have hg : (sourceEndpointWords W S p).get j = FixedWidth.bits (W+3)
      (Composition.SourceRouting.flatEndpoint S p (Fin.cast (incidence_card _).symm j)).val.bits := by
    simp [sourceEndpointWords,Vector.get,Fin.cast]
  rw [hg]
  rw [←he]
  simp only [Composition.SourceRouting.flatEndpoint,Equiv.symm_apply_apply]

end Maxwell.Cost.PositiveGraph.Invariant
