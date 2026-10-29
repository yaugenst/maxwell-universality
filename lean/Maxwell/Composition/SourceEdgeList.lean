import Maxwell.Composition.SourceSegmentList
import Maxwell.Composition.SourceEdgeEnumeration

/-! Actual finite canonical Γ edge coordinates, emitted by adjacent-pair scans
and integer comparisons. The semantic correspondence proves completeness
and uniqueness independently of the list's executable construction. -/
namespace Maxwell.Composition.SourceEdgeList
open Maxwell.Logical Maxwell.Logical.Routing

/-- The stored Γ edge list, in path order and with increasing integer height. -/
def edges (S : Source.SparseSystem) (precision : ℕ) : List (Point × Point) :=
  (SourceSegmentList.raw S precision).map Segments.orient

noncomputable section
variable (S : Source.SparseSystem) (precision : ℕ)

def coordinate (e : SourceIncidence.E S precision) : Point × Point :=
  (SourceRouting.embedding S precision e.val.1, SourceRouting.embedding S precision e.val.2)

theorem position_height (v : SourceRouting.Vertex S precision) :
    SourceIncidence.height (SourceIncidence.position S precision v) =
      Segments.height (SourceRouting.embedding S precision v) + 24 := by
  rw [SourceIncidence.position_eq]
  change (SourceRouting.embedding S precision v).1 + 4 +
    ((SourceRouting.embedding S precision v).2.1 + 4) +
    ((SourceRouting.embedding S precision v).2.2 + 16) =
    (SourceRouting.embedding S precision v).1 + (SourceRouting.embedding S precision v).2.1 +
      (SourceRouting.embedding S precision v).2.2 + 24
  ring

theorem coordinate_toEdge (s : SourceSteps.Step S precision) :
    coordinate S precision (SourceEdgeEnumeration.toEdge S precision s) =
      Segments.orient (SourceSegmentList.pair S precision s) := by
  have hlt : (SourceIncidence.height (SourceIncidence.position S precision (SourceSteps.left S precision s)) <
      SourceIncidence.height (SourceIncidence.position S precision (SourceSteps.right S precision s))) ↔
      Segments.height (SourceRouting.embedding S precision (SourceSteps.left S precision s)) <
        Segments.height (SourceRouting.embedding S precision (SourceSteps.right S precision s)) := by
    rw [position_height, position_height, add_lt_add_iff_right]
  unfold coordinate SourceEdgeEnumeration.toEdge
  by_cases h : Segments.height (SourceRouting.embedding S precision (SourceSteps.left S precision s)) <
      Segments.height (SourceRouting.embedding S precision (SourceSteps.right S precision s))
  · simp only [hlt.mpr h, ↓reduceDIte, SourceSegmentList.pair, Segments.orient, h, ↓reduceIte]
  · simp only [show ¬SourceIncidence.height (SourceIncidence.position S precision (SourceSteps.left S precision s)) <
        SourceIncidence.height (SourceIncidence.position S precision (SourceSteps.right S precision s)) from
        fun hh => h (hlt.mp hh), ↓reduceDIte, SourceSegmentList.pair, Segments.orient, h, ↓reduceIte]

theorem coordinate_injective : Function.Injective (coordinate S precision) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext (SourceRouting.embedding_injective S precision (congrArg Prod.fst h))
    (SourceRouting.embedding_injective S precision (congrArg Prod.snd h))

theorem edges_eq : edges S precision = (SourceSegmentList.stepList S precision).map
    (fun s => coordinate S precision (SourceEdgeEnumeration.toEdge S precision s)) := by
  rw [edges, SourceSegmentList.raw_eq, List.map_map]
  apply List.map_congr_left
  intro s _
  exact (coordinate_toEdge S precision s).symm

theorem edges_nodup : (edges S precision).Nodup := by
  rw [edges_eq]
  exact (SourceSegmentList.stepList_nodup S precision).map
    ((coordinate_injective S precision).comp (SourceEdgeEnumeration.toEdge_injective S precision))

/-- An emitted pair is exactly one canonical edge of the actual Γ matrix. -/
theorem mem_edges_iff (p : Point × Point) : p ∈ edges S precision ↔
    ∃ e : SourceIncidence.E S precision, coordinate S precision e = p := by
  rw [edges_eq, List.mem_map]
  constructor
  · rintro ⟨s, _, hs⟩; exact ⟨SourceEdgeEnumeration.toEdge S precision s, hs⟩
  · rintro ⟨e, he⟩
    obtain ⟨s, rfl⟩ := SourceEdgeEnumeration.toEdge_surjective S precision e
    exact ⟨s, SourceSegmentList.stepList_complete S precision s, he⟩

end
end Maxwell.Composition.SourceEdgeList
