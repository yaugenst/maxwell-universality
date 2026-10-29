import Maxwell.Composition.SourceSegmentList
import Maxwell.Logical.Routing.InternalSamples

/-! A finite Γ vertex list with exact rational diagonals. Original vertices
are emitted from their saved arrays and every path contributes only its
internal samples, so shared endpoints are never duplicated. -/
namespace Maxwell.Composition.SourceVertexList
open Maxwell.Logical Maxwell.Logical.Routing

def entries (S : Source.SparseSystem) (precision : ℕ) : List (Point × ℚ) :=
  let saved := SourceEmission.geometry S precision
  List.ofFn (fun i => (saved.original.get i, saved.diagonal.get i)) ++
    (List.finRange ((sourceSquareEntries S precision).length +
      (sourceSquareEntries S precision).length)).flatMap
      (fun e => (InternalSamples.ofList (saved.paths.get e)).map (fun p => (p, 0)))

noncomputable section
variable (S : Source.SparseSystem) (precision : ℕ)

def originalList : List (SourcePositive.Vertex S precision) :=
  List.ofFn (SourceEnumeration.vertexEquiv S precision).symm

def internalList : List (SubdivisionSchur.Internal (SourceRouting.data S precision)) :=
  (SourceSegmentList.edgeList S precision).sigma (fun e => List.finRange
    ((EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length - 1))

def vertexList : List (SourceRouting.Vertex S precision) :=
  (originalList S precision).map (fun v => (Sum.inl v : SourceRouting.Vertex S precision)) ++
    (internalList S precision).map (fun v => (Sum.inr v : SourceRouting.Vertex S precision))

def diagonal : SourceRouting.Vertex S precision → ℚ
  | .inl v => (SourceEmission.geometry S precision).diagonal.get
      (SourceEnumeration.vertexEquiv S precision v)
  | .inr _ => 0

def record (v : SourceRouting.Vertex S precision) : Point × ℚ :=
  (SourceRouting.embedding S precision v, diagonal S precision v)

theorem originalList_nodup : (originalList S precision).Nodup :=
  List.nodup_ofFn.mpr (SourceEnumeration.vertexEquiv S precision).symm.injective

theorem internalList_nodup : (internalList S precision).Nodup :=
  (SourceSegmentList.edgeList_nodup S precision).sigma (fun _ => List.nodup_finRange _)

theorem vertexList_nodup : (vertexList S precision).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(originalList_nodup S precision).map Sum.inl_injective,
    (internalList_nodup S precision).map Sum.inr_injective, ?_⟩
  intro a ha b hb he
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hb
  cases he

theorem vertexList_complete (v : SourceRouting.Vertex S precision) : v ∈ vertexList S precision := by
  cases v with
  | inl v =>
    apply List.mem_append.mpr
    apply Or.inl
    apply List.mem_map.mpr
    refine ⟨v, ?_, rfl⟩
    exact List.mem_ofFn.mpr ⟨SourceEnumeration.vertexEquiv S precision v,
      (SourceEnumeration.vertexEquiv S precision).symm_apply_apply v⟩
  | inr v =>
    apply List.mem_append.mpr
    apply Or.inr
    apply List.mem_map.mpr
    exact ⟨v, List.mem_sigma.mpr ⟨SourceSegmentList.edgeList_complete S precision v.1,
      List.mem_finRange _⟩, rfl⟩

theorem entries_eq : entries S precision = (vertexList S precision).map (record S precision) := by
  unfold entries vertexList
  erw [List.map_append]
  apply congrArg₂ List.append
  · unfold originalList
    erw [List.map_map]
    refine Eq.trans ?_ List.map_ofFn.symm
    congr 1
    funext i
    have ho := SourceEmission.original_eq S precision
      ((SourceEnumeration.vertexEquiv S precision).symm i)
    rw [(SourceEnumeration.vertexEquiv S precision).apply_symm_apply] at ho
    apply Prod.ext
    · exact ho
    · change _ = (SourceEmission.geometry S precision).diagonal.get
        ((SourceEnumeration.vertexEquiv S precision)
          ((SourceEnumeration.vertexEquiv S precision).symm i))
      rw [(SourceEnumeration.vertexEquiv S precision).apply_symm_apply]
  · unfold internalList SourceSegmentList.edgeList List.sigma
    erw [List.flatMap_map, List.map_map, List.map_flatMap]
    simp only [List.map_map]
    congr 1
    funext e
    have hp := SourceEmission.path_eq S precision
      ((SourceEnumeration.positiveEdgeEquiv S precision).symm e)
    rw [(SourceEnumeration.positiveEdgeEquiv S precision).apply_symm_apply] at hp
    rw [hp, InternalSamples.of_points, List.ofFn_eq_map, List.map_map]
    apply List.map_congr_left
    intro t _
    rfl

theorem diagonal_cast (v : SourceRouting.Vertex S precision) :
    (diagonal S precision v : ℝ) = SourceSubdivision.matrix S precision v v := by
  cases v with
  | inl v =>
    rw [show (diagonal S precision (.inl v) : ℝ) =
        PositiveEdges.diagonal (SourcePositive.sourceH S precision) v from
      SourceEmission.diagonal_eq S precision v]
    exact (Matrix.diagonal_apply_eq _ _).symm
  | inr v =>
    rcases v with ⟨e, t⟩
    change ((0 : ℚ) : ℝ) = SubdivisionSchur.matrix (SourceRouting.data S precision)
      (SourcePositive.graph S precision) (PositiveEdges.diagonal (SourcePositive.sourceH S precision))
      (.inr ⟨e, t⟩) (.inr ⟨e, t⟩)
    rw [SubdivisionSchur.matrix_internal_same]
    have hn : ¬(t.val + 1 = t.val ∨ t.val + 1 = t.val) := by omega
    rw [ite_eq_right hn]
    exact Rat.cast_zero

theorem coordinates_nodup : ((entries S precision).map Prod.fst).Nodup := by
  rw [entries_eq, List.map_map]
  exact (vertexList_nodup S precision).map (SourceRouting.embedding_injective S precision)

/-- Exact emitted positions and rational diagonal coefficients for every Γ vertex. -/
theorem mem_entries_iff (p : Point × ℚ) : p ∈ entries S precision ↔
    ∃ v : SourceRouting.Vertex S precision, record S precision v = p := by
  rw [entries_eq, List.mem_map]
  constructor
  · rintro ⟨v, _, hv⟩; exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩; exact ⟨v, vertexList_complete S precision v, hv⟩

end
end Maxwell.Composition.SourceVertexList
