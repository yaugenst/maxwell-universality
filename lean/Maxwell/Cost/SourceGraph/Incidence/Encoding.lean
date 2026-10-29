import Maxwell.Cost.SourceGraph.Correctness
import Maxwell.Cost.GraphIncidence.Pass

namespace Maxwell.Cost.SourceGraph.Incidence
open Structured PositiveGraph Maxwell.Cost.SourceGraph.Positive
open Maxwell.Logical.Routing

theorem incidence_count (S : Source.SparseSystem) (p : ℕ) :
    Fintype.card (Fin ((Logical.sourceSquareEntries S p).length+(Logical.sourceSquareEntries S p).length) × Bool)=
      4*count S p := by
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,count]
  omega

theorem vertex_count (S : Source.SparseSystem) (p : ℕ) :
    (Logical.sourceCircuit S p).size+(Logical.sourceCircuit S p).size+(Logical.sourceSquareEntries S p).length =
      2*dimension S p+count S p := by dsimp [dimension,count]; omega

def endpoint (S : Source.SparseSystem) (p : ℕ) : Fin (4*count S p) → Fin (2*dimension S p+count S p) :=
  fun i => Fin.cast (vertex_count S p)
    (Composition.SourceRouting.flatEndpoint S p (Fin.cast (incidence_count S p).symm i))

theorem endpoint_degree (S : Source.SparseSystem) (p : ℕ) :
    IncidenceRanks.DegreeBound (endpoint S p) := by
  intro v
  let e := finCongr (incidence_count S p).symm
  let v0 := Fin.cast (vertex_count S p).symm v
  have eqv := e.subtypeEquiv (p := fun i => endpoint S p i=v)
    (q := fun i => Composition.SourceRouting.flatEndpoint S p i=v0) (by
      intro i
      dsimp [endpoint,e,v0]
      constructor
      · intro h
        have hh := congrArg (Fin.cast (vertex_count S p).symm) h
        simpa using hh
      · intro h
        have hh := congrArg (Fin.cast (vertex_count S p)) h
        simpa using hh)
  have hc := Fintype.card_congr eqv
  rw [Fintype.card_subtype,Fintype.card_subtype] at hc
  rw [hc]
  exact Composition.SourceRouting.flatEndpoint_degree S p v0

theorem endpoint_words (S : Source.SparseSystem) (p : ℕ) :
    IncidenceEncoding.words (width S p+3) (IncidenceEncoding.endpointValues (endpoint S p)) =
      Invariant.sourceEndpointWords (width S p) S p := by
  unfold IncidenceEncoding.words IncidenceEncoding.endpointValues Invariant.sourceEndpointWords
  rw [Vector.map_ofFn]
  congr 1

theorem zero_words (n w : ℕ) :
    IncidenceEncoding.words w (Vector.replicate n 0)=Initialize.constantWords n w 0 := by
  apply Vector.ext
  intro i hi
  simp [IncidenceEncoding.words,IncidenceEncoding.word,Initialize.constantWords]

theorem initial_representation {S : Source.SparseSystem} {p : ℕ} {s : Store}
    (h : Positive.Result S p s) :
    IncidenceEncoding.Represents (GraphIncidence.layout (width S p) (dimension S p) (count S p))
      s.val.memory (endpoint S p) (IncidenceRanks.initial (2*dimension S p+count S p) (4*count S p)) := by
  refine ⟨?_,?_,?_⟩
  · change BitArray.Represents _ 0 (width S p+3)
      (IncidenceEncoding.words (width S p+3) (IncidenceEncoding.endpointValues (endpoint S p)))
    rw [endpoint_words]
    exact h.endpoints
  · change BitArray.Represents _ (4*count S p*(width S p+3)) 2 _
    rw [IncidenceRanks.initial,zero_words]
    exact h.counters
  · change BitArray.Represents _ (4*count S p*(width S p+3)+2*(2*dimension S p+count S p)) 2 _
    rw [IncidenceRanks.initial,zero_words]
    exact h.ranks

theorem vertex_fit {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Positive.Result S p s) :
    2*dimension S p+count S p ≤ 2^(width S p+3) := by
  have hd := h.room
  have hk : count S p ≤ 3*dimension S p := Logical.sourceSquareEntries_length_le S p
  rw [pow_add]
  norm_num
  omega

end Maxwell.Cost.SourceGraph.Incidence
