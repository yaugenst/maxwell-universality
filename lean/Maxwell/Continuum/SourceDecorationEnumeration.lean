import Maxwell.Composition.SourceVertexList
import Maxwell.Composition.SourceDecoration
import Maxwell.Composition.SourceEdgeEnumeration

/-! An arithmetic order for all physical wells. Original samples come first,
then each path's internal samples, then its consecutive-pair mediators.
The constructor consumes the saved chronological paths and performs no search
over pairs of vertices. -/
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Spectral.Lattice
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def shiftedPoint (p : Point) : Site := ![p.1+4,p.2.1+4,p.2.2+16]

def terminalPoint (p : Point) : Site := fun k => 2*shiftedPoint p k

def mediatorPoint (p : Point×Point) : Site := shiftedPoint p.1+shiftedPoint p.2

def terminalSamples {v e : ℕ} (saved : SourceEmission.Geometry v e) : List Point :=
  List.ofFn saved.original.get ++ (List.finRange e).flatMap
    (fun i => InternalSamples.ofList (saved.paths.get i))

def stepSamples {v e : ℕ} (saved : SourceEmission.Geometry v e) : List (Point×Point) :=
  (List.finRange e).flatMap (fun i => Segments.ofList (saved.paths.get i))

def sites {v e : ℕ} (saved : SourceEmission.Geometry v e) : List Site :=
  (terminalSamples saved).map terminalPoint ++ (stepSamples saved).map mediatorPoint

/-- The count is computed by one scan of the saved path lengths. -/
def siteCount {v e : ℕ} (saved : SourceEmission.Geometry v e) : ℕ :=
  v+((List.finRange e).map (fun i => (saved.paths.get i).length-2)).sum+
    ((List.finRange e).map (fun i => (saved.paths.get i).length-1)).sum

theorem sites_length {v e : ℕ} (saved : SourceEmission.Geometry v e) :
    (sites saved).length=siteCount saved := by
  simp only [sites,terminalSamples,stepSamples,siteCount,List.length_append,List.length_map,
    List.length_ofFn,List.length_flatMap,InternalSamples.length,Segments.length]

noncomputable section
variable (S : Source.SparseSystem) (precision : ℕ)

def vertexList : List (SourceDecoration.Vertex S precision) :=
  (SourceVertexList.vertexList S precision).map Sum.inl ++
    (SourceSegmentList.stepList S precision).map
      (fun s => Sum.inr (SourceEdgeEnumeration.toEdge S precision s))

theorem vertexList_nodup : (vertexList S precision).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(SourceVertexList.vertexList_nodup S precision).map Sum.inl_injective,
    (SourceSegmentList.stepList_nodup S precision).map
      (Sum.inr_injective.comp (SourceEdgeEnumeration.toEdge_injective S precision)), ?_⟩
  intro a ha b hb he
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hb
  cases he

theorem vertexList_complete (v : SourceDecoration.Vertex S precision) :
    v∈vertexList S precision := by
  cases v with
  | inl v => exact List.mem_append_left _ (List.mem_map.mpr
      ⟨v,SourceVertexList.vertexList_complete S precision v,rfl⟩)
  | inr e =>
    obtain ⟨s,rfl⟩ := SourceEdgeEnumeration.toEdge_surjective S precision e
    exact List.mem_append_right _ (List.mem_map.mpr
      ⟨s,SourceSegmentList.stepList_complete S precision s,rfl⟩)

theorem vertexList_length : (vertexList S precision).length=
    Fintype.card (SourceDecoration.Vertex S precision) := by
  classical
  have hset : (vertexList S precision).toFinset=Finset.univ := by
    ext v
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact vertexList_complete S precision v
  rw [←List.toFinset_card_of_nodup (vertexList_nodup S precision),hset,Finset.card_univ]

theorem terminalPoint_embedding (v : SourceRouting.Vertex S precision) :
    terminalPoint (SourceRouting.embedding S precision v)=SourceDecoration.site S precision (.inl v) := by
  change (fun k => 2*shiftedPoint _ k)=DecoratedLattice.terminal _
  rw [SourceIncidence.position_eq]
  rfl

theorem mediatorPoint_pair (s : SourceSteps.Step S precision) :
    mediatorPoint (SourceSegmentList.pair S precision s)=
      SourceDecoration.site S precision (.inr (SourceEdgeEnumeration.toEdge S precision s)) := by
  rcases SourceEdgeEnumeration.toEdge_endpoints S precision s with h | h
  · simp only [SourceDecoration.site,h.1,h.2,SourceIncidence.position_eq,
      mediatorPoint,SourceSegmentList.pair,shiftedPoint]
  · simp only [SourceDecoration.site,h.1,h.2,SourceIncidence.position_eq,
      mediatorPoint,SourceSegmentList.pair,shiftedPoint]
    exact add_comm _ _

theorem terminalSamples_geometry : terminalSamples (SourceEmission.geometry S precision)=
    (SourceVertexList.entries S precision).map Prod.fst := by
  simp only [terminalSamples,SourceVertexList.entries,List.map_append,List.map_ofFn,
    List.map_flatMap,List.map_map,Function.comp_def]
  apply congrArg₂ List.append
  · rfl
  · congr 1
    funext i
    exact (List.map_id _).symm

theorem sites_geometry : sites (SourceEmission.geometry S precision)=
    (vertexList S precision).map (SourceDecoration.site S precision) := by
  rw [sites,terminalSamples_geometry,SourceVertexList.entries_eq,
    show stepSamples (SourceEmission.geometry S precision)=SourceSegmentList.raw S precision from rfl,
    SourceSegmentList.raw_eq]
  simp only [vertexList,List.map_append,List.map_map]
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro v _
    exact terminalPoint_embedding S precision v
  · apply List.map_congr_left
    intro s _
    exact mediatorPoint_pair S precision s

/-- The concrete contract for an independently executed routing producer.
Only sample values are required; diagonal coefficients are irrelevant here. -/
structure Represents (saved : SourceEmission.Geometry
    ((sourceCircuit S precision).size+(sourceCircuit S precision).size+
      (sourceSquareEntries S precision).length)
    ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length)) : Prop where
  original : ∀v, saved.original.get (SourceEnumeration.vertexEquiv S precision v)=
    SourceRouting.embedding S precision (.inl v)
  path : ∀e, saved.paths.get (SourceEnumeration.positiveEdgeEquiv S precision e)=
    EdgeEmission.points (EdgeWalk.edgeWalk (SourceRouting.data S precision) e)

theorem geometry_represents : Represents S precision (SourceEmission.geometry S precision) :=
  ⟨SourceEmission.original_eq S precision,SourceEmission.path_eq S precision⟩

theorem Represents.original_eq {saved} (h : Represents S precision saved) :
    saved.original=(SourceEmission.geometry S precision).original := by
  apply Vector.ext
  intro i hi
  let j : Fin ((sourceCircuit S precision).size+(sourceCircuit S precision).size+
      (sourceSquareEntries S precision).length) := ⟨i,hi⟩
  have h₁ := h.original ((SourceEnumeration.vertexEquiv S precision).symm j)
  have h₂ := SourceEmission.original_eq S precision ((SourceEnumeration.vertexEquiv S precision).symm j)
  rw [(SourceEnumeration.vertexEquiv S precision).apply_symm_apply] at h₁ h₂
  exact h₁.trans h₂.symm

theorem Represents.paths_eq {saved} (h : Represents S precision saved) :
    saved.paths=(SourceEmission.geometry S precision).paths := by
  apply Vector.ext
  intro i hi
  let j : Fin ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length) := ⟨i,hi⟩
  have h₁ := h.path ((SourceEnumeration.positiveEdgeEquiv S precision).symm j)
  have h₂ := SourceEmission.path_eq S precision ((SourceEnumeration.positiveEdgeEquiv S precision).symm j)
  rw [(SourceEnumeration.positiveEdgeEquiv S precision).apply_symm_apply] at h₁ h₂
  exact h₁.trans h₂.symm

theorem Represents.sites_eq {saved} (h : Represents S precision saved) :
    sites saved=(vertexList S precision).map (SourceDecoration.site S precision) := by
  rw [←sites_geometry]
  simp only [sites,terminalSamples,stepSamples,h.original_eq,h.paths_eq]

theorem Represents.sites_nodup {saved} (h : Represents S precision saved) :
    (sites saved).Nodup := by
  rw [h.sites_eq]
  exact (vertexList_nodup S precision).map (SourceDecoration.site_injective S precision)

theorem Represents.mem_sites_iff {saved} (h : Represents S precision saved) (x : Site) :
    x∈sites saved ↔ ∃v,SourceDecoration.site S precision v=x := by
  rw [h.sites_eq,List.mem_map]
  exact ⟨fun ⟨v,_,hx⟩ => ⟨v,hx⟩,
    fun ⟨v,hx⟩ => ⟨v,vertexList_complete S precision v,hx⟩⟩

theorem Represents.siteCount_eq {saved} (h : Represents S precision saved) :
    siteCount saved=Fintype.card (SourceDecoration.Vertex S precision) := by
  rw [←sites_length,h.sites_eq,List.length_map,vertexList_length]

#print axioms Represents.sites_eq
#print axioms Represents.sites_nodup
#print axioms Represents.mem_sites_iff
#print axioms Represents.siteCount_eq
end
end Maxwell.Composition.SourceDecorationEnumeration
