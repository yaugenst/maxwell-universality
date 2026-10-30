import Maxwell.Continuum.SourceDecorationCenters
import Maxwell.Cost.BankArray.ReadCanonical
import Maxwell.Cost.RoutingPorts.Complete.Common

/-! The producer/serializer boundary is a single fixed-width natural array:
original shifted triples, followed by a count and chronological shifted
triples for each path. No list of all vertex pairs is materialized. -/
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Spectral.Lattice Maxwell.Cost
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def pointWords (p : Point) : List ℕ :=
  [(p.1+4).toNat,(p.2.1+4).toNat,(p.2.2+16).toNat]

def pathWords (xs : List Point) : List ℕ := xs.length::xs.flatMap pointWords

def packed {v e : ℕ} (saved : SourceEmission.Geometry v e) : List ℕ :=
  (List.ofFn saved.original.get).flatMap pointWords ++
    (List.finRange e).flatMap (fun i => pathWords (saved.paths.get i))

def packedLength {v e : ℕ} (saved : SourceEmission.Geometry v e) : ℕ :=
  3*v+e+3*((List.finRange e).map (fun i => (saved.paths.get i).length)).sum

theorem pointWords_length (p : Point) : (pointWords p).length=3 := rfl

theorem triples_length (xs : List Point) : (xs.flatMap pointWords).length=3*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons,List.length_append,pointWords_length,
      List.length_cons,ih];omega

theorem pathWords_length (xs : List Point) : (pathWords xs).length=1+3*xs.length := by
  simp only [pathWords,List.length_cons,triples_length]
  omega

theorem pathArray_length {α : Type*} (is : List α) (f : α→List Point) :
    (is.flatMap (fun i => pathWords (f i))).length=is.length+3*(is.map (fun i => (f i).length)).sum := by
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.flatMap_cons,List.length_append,pathWords_length,List.length_cons,
      List.map_cons,List.sum_cons,ih]
    omega

theorem packed_length {v e : ℕ} (saved : SourceEmission.Geometry v e) :
    (packed saved).length=packedLength saved := by
  simp only [packed,List.length_append,triples_length,List.length_ofFn,pathArray_length,
    List.length_finRange,packedLength]
  omega

def packedVector {v e : ℕ} (saved : SourceEmission.Geometry v e) : Vector ℕ (packedLength saved) :=
  ⟨(packed saved).toArray,by simp only [List.size_toArray,packed_length]⟩

def packedBits {v e : ℕ} (saved : SourceEmission.Geometry v e) (width : ℕ) :
    Vector (List Bool) (packedLength saved) :=
  (packedVector saved).map (fun n => FixedWidth.bits width n.bits)

structure StoredGeometry {v e : ℕ} (saved : SourceEmission.Geometry v e)
    (base width : ℕ) (memory : ℕ→Bool) : Prop where
  positive : 0<width
  fits : ∀i,((packedVector saved).get i).bits.length≤width
  stored : BitArray.Represents memory base width (packedBits saved width)

theorem packedBits_value {v e : ℕ} (saved : SourceEmission.Geometry v e) (width : ℕ)
    (h : ∀i,((packedVector saved).get i).bits.length≤width) (i : Fin (packedLength saved)) :
    addressValue ((packedBits saved width).get i)=(packedVector saved).get i := by
  have hg : (packedBits saved width).get i=FixedWidth.bits width ((packedVector saved).get i).bits := by
    simp [packedBits,Vector.get,Fin.cast]
  rw [hg]
  rw [FixedWidth.bits_value, addressValue_bits]
  exact h i

theorem pointWords_value (p : Point) (h : ∀k,0≤shiftedPoint p k) (k : Fin 3) :
    (((pointWords p)[k.val]'(by rw [pointWords_length];exact k.isLt):ℕ):ℤ)=shiftedPoint p k := by
  fin_cases k
  · exact Int.toNat_of_nonneg (h 0)
  · exact Int.toNat_of_nonneg (h 1)
  · exact Int.toNat_of_nonneg (h 2)

theorem centerPoint_even (B : Fin 3→ℤ) {L d t : ℕ} (hL : Even L) (x : Site) (k : Fin 3) :
    centerPoint B L d t x k=(L+L*t+8:ℕ)+(2:ℤ)*L*d*B k*x k := by
  obtain ⟨l,hl⟩ := hL
  have hh : 2*((L+L*t+8+1)/2)=L+L*t+8 := by
    have he : L+L*t+8=2*(l+l*t+4) := by rw [hl];ring
    rw [he]
    omega
  have hh' : (2:ℤ)*(((L+L*t+8+1)/2:ℕ):ℤ)=(L+L*t+8:ℕ) := by exact_mod_cast hh
  dsimp only [centerPoint]
  rw [mul_add,hh']
  ring

noncomputable section
variable (S : Source.SparseSystem) (precision : ℕ)

theorem shiftedPoint_embedding (v : SourceRouting.Vertex S precision) :
    shiftedPoint (SourceRouting.embedding S precision v)=SourceIncidence.position S precision v :=
  (SourceIncidence.position_eq S precision v).symm

theorem shiftedPoint_embedding_nonnegative (v : SourceRouting.Vertex S precision) (k : Fin 3) :
    0≤shiftedPoint (SourceRouting.embedding S precision v) k := by
  have h := (SourceDecoration.site_inside S precision (.inl v) k).1
  change 0≤2*SourceIncidence.position S precision v k at h
  rw [shiftedPoint_embedding]
  omega

theorem Represents.original_nonnegative {saved} (h : Represents S precision saved)
    (i : Fin ((sourceCircuit S precision).size+(sourceCircuit S precision).size+
      (sourceSquareEntries S precision).length)) (k : Fin 3) :
    0≤shiftedPoint (saved.original.get i) k := by
  have he := h.original ((SourceEnumeration.vertexEquiv S precision).symm i)
  rw [(SourceEnumeration.vertexEquiv S precision).apply_symm_apply] at he
  rw [he]
  exact shiftedPoint_embedding_nonnegative S precision _ k

theorem Represents.path_nonnegative {saved} (h : Represents S precision saved)
    (i : Fin ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length))
    (x : Point) (hx : x∈saved.paths.get i) (k : Fin 3) : 0≤shiftedPoint x k := by
  let e := (SourceEnumeration.positiveEdgeEquiv S precision).symm i
  have he := h.path e
  rw [show SourceEnumeration.positiveEdgeEquiv S precision e=i from
    (SourceEnumeration.positiveEdgeEquiv S precision).apply_symm_apply i] at he
  rw [he,EdgeEmission.points,List.mem_map] at hx
  obtain ⟨j,hj,rfl⟩ := hx
  have hj' : j<(EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length+1 := List.mem_range.mp hj
  have hh := shiftedPoint_embedding_nonnegative S precision
    (Subdivision.edgeVertex (SourceRouting.data S precision) e ⟨j,hj'⟩) k
  simpa only [SourceRouting.embedding,Subdivision.embedding_edgeVertex] using hh

#print axioms Represents.path_nonnegative
#print axioms centerPoint_even
end
end Maxwell.Composition.SourceDecorationEnumeration
