import Maxwell.Composition.SourcePositive
import Maxwell.Logical.Routing.GraphData
import Maxwell.Logical.Routing.Subdivision
import Maxwell.Composition.SourceEnumeration
import Maxwell.Logical.Routing.IndexedData
import Maxwell.Logical.Routing.IncidenceRanks
import Maxwell.Composition.SourceCached

/-! The actual positive source graph supplies every local hypothesis of
the cubic-routing construction. Finite placement and port assignment are
derived from the compiled graph, rather than supplied as realization data. -/

namespace Maxwell.Composition

open Maxwell.Logical
open Maxwell.Logical.Routing
open Maxwell.Logical.Routing.Gluing

namespace SignedIncidence

def endpoint {V E : Type*} (G : SignedIncidence V E) (e : E) (side : Bool) : V :=
  if side then G.head e else G.tail e

theorem incidence_fiber_card {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : SignedIncidence V E) (v : V) :
    (Fintype.card (Fiber (fun p : E × Bool => G.endpoint p.1 p.2) v) : ℝ) = G.degree v := by
  rw [Fintype.card_subtype]
  rw [Finset.natCast_card_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, endpoint, Bool.false_eq_true, ↓reduceIte,
    SignedIncidence.degree]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : v = G.tail e
  · subst v
    simp [G.distinct e, Ne.symm (G.distinct e)]
  · by_cases hh : v = G.head e
    · simp [hh, G.distinct e]
    · simp [ht, hh, eq_comm]

end SignedIncidence

namespace SourceRouting

abbrev Edge (S : Source.SparseSystem) (precision : ℕ) :=
  PositiveEdges.Edge (SourcePositive.sourceH S precision) ⊕
    PositiveEdges.Edge (SourcePositive.sourceH S precision)

def part (S : Source.SparseSystem) (precision : ℕ) : SourcePositive.Vertex S precision → Bool
  | .inl _ => false
  | .inr _ => true

theorem endpoint_part (S : Source.SparseSystem) (precision : ℕ)
    (e : Edge S precision) (b : Bool) :
    part S precision ((SourcePositive.graph S precision).endpoint e b) = b := by
  cases b <;> cases e <;> rfl

theorem incidence_fiber_card_le_three (S : Source.SparseSystem) (precision : ℕ)
    (v : SourcePositive.Vertex S precision) :
    Fintype.card (Fiber (fun p : Edge S precision × Bool =>
      (SourcePositive.graph S precision).endpoint p.1 p.2) v) ≤ 3 := by
  have h := SourcePositive.degree_le_three S precision v
  rw [← SignedIncidence.incidence_fiber_card] at h
  exact_mod_cast h

def indexedPart (S : Source.SparseSystem) (precision : ℕ) :
    Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length) → Bool :=
  SourceEnumeration.positivePart S precision

theorem indexed_endpoint_part (S : Source.SparseSystem) (precision : ℕ)
    (e : Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length))
    (b : Bool) : indexedPart S precision (SourceEnumeration.positiveEndpoint S precision e b) = b := by
  exact SourceEnumeration.positivePart_endpoint S precision e b

theorem indexed_incidence_fiber_card_le_three (S : Source.SparseSystem) (precision : ℕ)
    (v : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) :
    Fintype.card (Fiber (fun p :
      Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length) × Bool =>
        SourceEnumeration.positiveEndpoint S precision p.1 p.2) v) ≤ 3 := by
  let eqv := (SourceEnumeration.positiveEdgeEquiv S precision).symm.prodCongr (Equiv.refl Bool)
  let vf := SourceEnumeration.vertexEquiv S precision
  let ef : Fiber (fun p :
      Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length) × Bool =>
        SourceEnumeration.positiveEndpoint S precision p.1 p.2) v ≃
    Fiber (fun p : Edge S precision × Bool => (SourcePositive.graph S precision).endpoint p.1 p.2)
      (vf.symm v) := eqv.subtypeEquiv (by
        intro p
        change SourceEnumeration.positiveEndpoint S precision p.1 p.2 = v ↔
          (SourcePositive.graph S precision).endpoint
            ((SourceEnumeration.positiveEdgeEquiv S precision).symm p.1) p.2 = vf.symm v
        rw [SourceEnumeration.positiveEndpoint_correct]
        exact vf.eq_symm_apply.symm)
  rw [Fintype.card_congr ef]
  exact incidence_fiber_card_le_three S precision _

def flatEndpoint (S : Source.SparseSystem) (precision : ℕ) :
    Fin (Fintype.card (Fin ((sourceSquareEntries S precision).length +
      (sourceSquareEntries S precision).length) × Bool)) →
      Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
        (sourceSquareEntries S precision).length) :=
  let endpoint := SourceCached.positiveEndpoint S precision
  fun i =>
    let p := (Gluing.incidenceIndex _).symm i
    endpoint p.1 p.2

theorem flatEndpoint_degree (S : Source.SparseSystem) (precision : ℕ)
    (v : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) :
    (Finset.univ.filter (fun i => flatEndpoint S precision i = v)).card ≤ 3 := by
  let eqv := (Gluing.incidenceIndex ((sourceSquareEntries S precision).length +
    (sourceSquareEntries S precision).length)).symm
  have he := Fintype.card_congr (eqv.subtypeEquiv (p := fun i => flatEndpoint S precision i = v)
    (q := fun p => SourceEnumeration.positiveEndpoint S precision p.1 p.2 = v)
    (by intro i; simp only [flatEndpoint, SourceCached.positiveEndpoint_eq]; rfl))
  rw [Fintype.card_subtype] at he
  rw [he]
  exact indexed_incidence_fiber_card_le_three S precision v

def indexedData (S : Source.SparseSystem) (precision : ℕ) :
    Gluing.Data (Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length))
      (Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length))
      (portHalfSide ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
        (sourceSquareEntries S precision).length)) := by
  let ranks := IncidenceRanks.ranks (flatEndpoint S precision) (flatEndpoint_degree S precision)
  let index := Gluing.incidenceIndex ((sourceSquareEntries S precision).length +
    (sourceSquareEntries S precision).length)
  let arm := fun e b => ranks.get (index (e, b))
  apply Gluing.indexedGraphData (indexedPart S precision) (SourceCached.positiveEndpoint S precision)
    (by intro e b; rw [SourceCached.positiveEndpoint_eq]; exact indexed_endpoint_part S precision e b) arm
  intro a b h
  apply index.injective
  apply IncidenceRanks.endpoint_rank_injective (flatEndpoint S precision) (flatEndpoint_degree S precision)
  simpa only [flatEndpoint, index, arm, ranks, Equiv.symm_apply_apply] using h

theorem indexedData_endpoint (S : Source.SparseSystem) (precision : ℕ)
    (e : Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length))
    (b : Bool) : (indexedData S precision).endpoint e b =
      SourceEnumeration.positiveEndpoint S precision e b := SourceCached.positiveEndpoint_eq S precision e b

def castDataHalf {V E : Type*} {a b : ℕ} (h : a = b) (d : Gluing.Data V E a) : Gluing.Data V E b :=
  h ▸ d

theorem castDataHalf_endpoint {V E : Type*} {a b : ℕ} (h : a = b) (d : Gluing.Data V E a)
    (e : E) (side : Bool) : (castDataHalf h d).endpoint e side = d.endpoint e side := by
  subst b
  rfl

noncomputable def data (S : Source.SparseSystem) (precision : ℕ) :
    Gluing.Data (SourcePositive.Vertex S precision) (Edge S precision)
      (portHalfSide (Fintype.card (SourcePositive.Vertex S precision))) :=
  castDataHalf (congrArg portHalfSide (SourceEnumeration.vertex_count S precision).symm)
    (Gluing.transportData (SourceEnumeration.vertexEquiv S precision)
      (SourceEnumeration.positiveEdgeEquiv S precision) (indexedData S precision))

theorem data_endpoint (S : Source.SparseSystem) (precision : ℕ) (e : Edge S precision) (b : Bool) :
    (data S precision).endpoint e b = (SourcePositive.graph S precision).endpoint e b := by
  rw [data, castDataHalf_endpoint]
  simp only [Gluing.transportData, indexedData_endpoint]
  rw [SourceEnumeration.positiveEndpoint_correct, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

abbrev Vertex (S : Source.SparseSystem) (precision : ℕ) := Subdivision.Vertex (data S precision)

noncomputable def embedding (S : Source.SparseSystem) (precision : ℕ) : Vertex S precision → Point :=
  Subdivision.embedding (data S precision)

theorem embedding_injective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Injective (embedding S precision) := Subdivision.embedding_injective _

def inputCoordinate (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    Vertex S precision := Sum.inl (SourcePositive.inputCoordinate S precision i)

theorem inputCoordinate_injective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Injective (inputCoordinate S precision) := by
  intro i j h
  exact SourcePositive.inputCoordinate_injective S precision (Sum.inl.inj h)

theorem internal_count_wire_form (S : Source.SparseSystem) (precision : ℕ)
    (e : Edge S precision) :
    ∃ j : ℕ, 0 < j ∧ (EdgeWalk.edgeWalk (data S precision) e).length - 1 = 4 * j :=
  Subdivision.internal_count_positive_wire_form _ _

noncomputable def side (S : Source.SparseSystem) (precision : ℕ) : ℕ :=
  portSide (Fintype.card (SourcePositive.Vertex S precision))

theorem side_pos (S : Source.SparseSystem) (precision : ℕ) : 0 < side S precision := by
  rw [side, portSide_power_two]
  positivity

theorem edge_length_le (S : Source.SparseSystem) (precision : ℕ) (e : Edge S precision) :
    (EdgeWalk.edgeWalk (data S precision) e).length ≤ 1024 * side S precision :=
  EdgeWalk.edgeWalk_length_bound _ _

noncomputable def boxIndex (S : Source.SparseSystem) (precision : ℕ) : Vertex S precision →
    Fin (boxSideXY (side S precision)) × Fin (boxSideXY (side S precision)) ×
      Fin (boxSideZ (side S precision)) := Subdivision.boxIndex (data S precision)

theorem boxIndex_injective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Injective (boxIndex S precision) := Subdivision.boxIndex_injective _

theorem vertex_card_le_box (S : Source.SparseSystem) (precision : ℕ) :
    Fintype.card (Vertex S precision) ≤ boxSites (side S precision) :=
  Subdivision.vertex_card_le_box _

theorem box_volume_le_cube (S : Source.SparseSystem) (precision : ℕ) :
    boxSites (side S precision) ≤ 80625 * side S precision ^ 3 :=
  box_sites_le _ (side_pos S precision)

theorem original_vertices_le (S : Source.SparseSystem) (precision : ℕ) (hn : S.n ≤ S.nnz) :
    Fintype.card (SourcePositive.Vertex S precision) ≤ 30 * S.nnz * (precision + 1) := by
  have hg := SourcePositive.vertex_count_le S precision
  have hc := sourceCircuit_size S precision hn
  nlinarith

end SourceRouting
end Maxwell.Composition
