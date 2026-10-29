import Maxwell.Composition.SourceEmission
import Maxwell.Composition.SourceSteps
import Maxwell.Logical.Routing.Segments

/-! Sparse chronological edge emission from the already materialized paths.
No semantic vertex-pair scan appears in the executable list constructor. -/
namespace Maxwell.Composition.SourceSegmentList
open Maxwell.Logical Maxwell.Logical.Routing SourceSteps

/-- Each stored path is scanned once for adjacent point pairs. -/
def raw (S : Source.SparseSystem) (precision : ℕ) : List (Point × Point) :=
  let saved := SourceEmission.geometry S precision
  (List.finRange ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length)).flatMap
    (fun e => Segments.ofList (saved.paths.get e))

noncomputable section
variable (S : Source.SparseSystem) (precision : ℕ)

def edgeList : List (SourceRouting.Edge S precision) :=
  (List.finRange ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length)).map
    (SourceEnumeration.positiveEdgeEquiv S precision).symm

def stepList : List (Step S precision) :=
  (edgeList S precision).sigma (fun e => List.finRange
    (EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length)

theorem edgeList_nodup : (edgeList S precision).Nodup :=
  (List.nodup_finRange _).map (SourceEnumeration.positiveEdgeEquiv S precision).symm.injective

theorem edgeList_complete (e : SourceRouting.Edge S precision) : e ∈ edgeList S precision := by
  apply List.mem_map.mpr
  exact ⟨SourceEnumeration.positiveEdgeEquiv S precision e, List.mem_finRange _,
    (SourceEnumeration.positiveEdgeEquiv S precision).symm_apply_apply e⟩

theorem stepList_nodup : (stepList S precision).Nodup :=
  (edgeList_nodup S precision).sigma (fun _ => List.nodup_finRange _)

theorem stepList_complete (s : Step S precision) : s ∈ stepList S precision :=
  List.mem_sigma.mpr ⟨edgeList_complete S precision s.1, List.mem_finRange _⟩

def pair (s : Step S precision) : Point × Point :=
  (SourceRouting.embedding S precision (left S precision s),
    SourceRouting.embedding S precision (right S precision s))

theorem pair_apply (e : SourceRouting.Edge S precision)
    (t : Fin (EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length) :
    pair S precision ⟨e, t⟩ =
      ((EdgeWalk.edgeWalk (SourceRouting.data S precision) e).point t.val,
        (EdgeWalk.edgeWalk (SourceRouting.data S precision) e).point (t.val + 1)) := by
  simp only [pair, left, right, SubdivisionSteps.left, SubdivisionSteps.right,
    SubdivisionSteps.vertexAt, SourceRouting.embedding, Subdivision.embedding_edgeVertex,
    Fin.val_castSucc, Fin.val_succ]

theorem raw_eq : raw S precision = (stepList S precision).map (pair S precision) := by
  unfold raw stepList edgeList
  simp only [List.sigma, List.flatMap_map, List.map_flatMap, List.map_map]
  congr 1
  funext e
  have hp := SourceEmission.path_eq S precision
    ((SourceEnumeration.positiveEdgeEquiv S precision).symm e)
  rw [(SourceEnumeration.positiveEdgeEquiv S precision).apply_symm_apply] at hp
  rw [hp, Segments.of_points, List.ofFn_eq_map]
  apply List.map_congr_left
  intro t _
  exact (pair_apply S precision _ t).symm

theorem pair_injective : Function.Injective (pair S precision) := by
  intro a b he
  have ht := congrArg Prod.fst he
  have hh := congrArg Prod.snd he
  apply unordered_injective S precision a b
  exact Or.inl ⟨SourceRouting.embedding_injective S precision ht,
    SourceRouting.embedding_injective S precision hh⟩

theorem raw_nodup : (raw S precision).Nodup := by
  rw [raw_eq]
  exact (stepList_nodup S precision).map (pair_injective S precision)

theorem mem_raw_iff (p : Point × Point) : p ∈ raw S precision ↔
    ∃ s : Step S precision, pair S precision s = p := by
  rw [raw_eq, List.mem_map]
  constructor
  · rintro ⟨s, _, hs⟩; exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩; exact ⟨s, stepList_complete S precision s, hs⟩

end
end Maxwell.Composition.SourceSegmentList
