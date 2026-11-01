import Maxwell.Continuum.SourceRoutingAddressWidths
import Maxwell.Continuum.SourceRoutingSourcePlanWidth

/-! The complete source geometry uses a linear word envelope in the source
graph's binary widths, including all history and output addresses. -/
namespace Maxwell.Cost.RoutingPorts.Complete
open RationalAccumulator SourceGraph.Positive Maxwell.Composition
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

private theorem bits_le_self (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

private theorem bits_sum (a b : ℕ) : (a+b).bits.length≤a.bits.length+b.bits.length+1 :=
  (bits_add_le a b).trans (by omega)

theorem SourcePhase.side_eq (S : Source.SparseSystem) (p : ℕ) :
    side S p=SourceRouting.side S p := by
  unfold SourceRouting.side
  rw [SourceEnumeration.vertex_count]
  rfl

theorem Tree.runWidth_start (depth backward : ℕ) :
    runWidth (TreeStartup.heap depth backward) depth depth ≤ backward.bits.length+16*depth+40 := by
  let n:=2^(depth+depth)
  let w:=depth+depth+1
  let h:=backward+w*n
  have count : n.bits.length=depth+depth+1:=by rw [Nat.size_eq_bits_len,Nat.size_pow]
  have word:=bits_le_self w
  have slab:=bits_mul_le w n
  have heap:=bits_sum backward (w*n)
  have stride:=bits_mul_le n w
  have stride11:=bits_mul_le 11 (n*w)
  have a:=bits_sum h (11*(n*w))
  have b:=bits_sum (h+11*(n*w)) n
  have c:=bits_sum (h+11*(n*w)+n) w
  have d:=bits_sum (h+11*(n*w)+n+w) (2^depth)
  have e:=bits_sum (h+11*(n*w)+n+w+2^depth) 4
  have power : (2^depth).bits.length=depth+1:=by rw [Nat.size_eq_bits_len,Nat.size_pow]
  simp only [show (11:ℕ).bits.length=4 by decide] at stride11
  simp only [show (4:ℕ).bits.length=3 by decide] at e
  change (h+11*(n*w)+n+w+2^depth+4).bits.length≤_
  change h.bits.length≤backward.bits.length+(w*n).bits.length+1 at heap
  dsimp only [n,w,h] at *
  omega

namespace SourceGeometry

theorem basic_widths (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) :
    (SourcePhase.side S p).bits.length≤SourcePlan.wordBound S p room+2 ∧
    (SourcePhase.layout S p).forward.bits.length≤SourcePlan.wordBound S p room ∧
    (SourcePhase.layout S p).backward.bits.length≤SourcePlan.wordBound S p room ∧
    (GeometryProducer.vertices S p).bits.length≤SourcePlan.wordBound S p room ∧
    (GeometryProducer.edges S p).bits.length≤SourcePlan.wordBound S p room+2 := by
  let B:=SourcePlan.wordBound S p room
  have power:=congrArg (fun n:ℕ=>n.bits.length) (side_power S p)
  rw [Nat.size_eq_bits_len,Nat.size_pow] at power
  have vertexEq : GeometryProducer.vertices S p=SourcePlan.vertices S p:=by
    simp only [GeometryProducer.vertices,SourcePlan.vertices,dimension,count,Nat.two_mul]
  have vertices : (GeometryProducer.vertices S p).bits.length≤B:=by
    rw [vertexEq]
    unfold B SourcePlan.wordBound Startup.sourceWidth
    omega
  have countBound : (count S p).bits.length≤B:=by
    apply (Maxwell.Continuum.RationalWords.bits_mono (show count S p≤SourcePlan.vertices S p by
      unfold SourcePlan.vertices;omega)).trans
    simpa only [vertexEq] using vertices
  have edges:=bits_mul_le 2 (count S p)
  simp only [show (2:ℕ).bits.length=2 by decide] at edges
  have edgeEq : GeometryProducer.edges S p=2*count S p:=by
    simp only [GeometryProducer.edges,count,Nat.two_mul]
  rw [←edgeEq] at edges
  refine ⟨?_,?_,?_,vertices,by omega⟩
  · unfold SourcePlan.depth at power
    unfold SourcePlan.wordBound
    omega
  · change (Startup.gridLayout (SourcePlan.vertices S p) (base S p)).forward.bits.length≤_
    unfold SourcePlan.wordBound scale
    omega
  · change (Startup.gridLayout (SourcePlan.vertices S p) (base S p)).backward.bits.length≤_
    unfold SourcePlan.wordBound scale
    omega

theorem capacity_width (q v e : ℕ) :
    (GeometryEmission.capacity q v e).bits.length ≤ v.bits.length+e.bits.length+2*q.bits.length+33 := by
  have a:=bits_mul_le 3 v
  have b:=bits_mul_le 3072 q
  have c:=bits_sum 1 (3072*q)
  have d:=bits_mul_le e (1+3072*q)
  have f:=bits_sum (3*v) (e*(1+3072*q))
  have g:=bits_sum (3*v+e*(1+3072*q)) 1
  have h:=bits_sum (3*v+e*(1+3072*q)+1) (3072*q)
  simp only [show (3:ℕ).bits.length=2 by decide] at a
  simp only [show (3072:ℕ).bits.length=12 by decide] at b
  simp only [show (1:ℕ).bits.length=1 by decide] at c g
  unfold GeometryEmission.capacity
  omega

theorem wordBound_plan (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) :
    wordBound S p room ≤ 1000*(SourcePlan.wordBound S p room+10) := by
  let B:=SourcePlan.wordBound S p room
  let q:=SourcePhase.side S p
  let f:=(SourcePhase.layout S p).forward
  let b:=(SourcePhase.layout S p).backward
  obtain ⟨side,forward,backward,vertices,edges⟩:=basic_widths S p room
  have depth : SourcePlan.depth S p≤B+1:=by unfold SourcePlan.depth B SourcePlan.wordBound;omega
  have tree:=Tree.runWidth_start (SourcePlan.depth S p) b
  have square:=bits_mul_le q q
  have nested:=bits_le_self (q*q).bits.length
  have half:=Maxwell.Continuum.RationalWords.bits_mono
    (show SourcePhase.half S p≤q by change _≤2*SourcePhase.half S p;omega)
  have startup : PhaseStartup.inputWidth (SourcePhase.half S p) f b≤7*B+30:=by
    change (q*q).bits.length+(SourcePhase.half S p).bits.length+
      (q*q).bits.length.bits.length+f.bits.length+b.bits.length+16≤_
    dsimp only [q,f,b,B] at *
    omega
  have bases : ∀ i,((SourcePhase.plan S p).base i).bits.length≤17*B+49:=by
    intro i
    have h:=PhaseStartup.bases_width q f b i
    change ((SourcePhase.plan S p).base i).bits.length≤_ at h
    dsimp only [q,f,b,B] at *
    omega
  have histories:=GeometryHistories.address_bound (SourcePhase.plan S p) (17*B+49) bases
  have first : (history S p).base.bits.length≤17*B+49:=bases 2
  have capacity:=capacity_width q (GeometryProducer.vertices S p) (GeometryProducer.edges S p)
  have address:=GeometryProducer.addressWidth_bound (history S p) b
    (GeometryEmission.capacity q (GeometryProducer.vertices S p) (GeometryProducer.edges S p))
  unfold wordBound SourceTree.wordBound
  change B+Tree.runWidth (Tree.TreeStartup.heap (SourcePlan.depth S p) b)
    (SourcePlan.depth S p) (SourcePlan.depth S p)+
    PhaseStartup.inputWidth (SourcePhase.half S p) f b+GeometryHistories.bound (SourcePhase.plan S p)+
    GeometryProducer.addressWidth (history S p) b
      (GeometryEmission.capacity q (GeometryProducer.vertices S p) (GeometryProducer.edges S p))≤_
  dsimp only [q,f,b,B] at *
  omega

#print axioms wordBound_plan
end SourceGeometry

namespace CountedGeometry
open SourceDecorationEnumeration

theorem wordBound_plan (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) :
    wordBound S p room ≤ 2000*(SourcePlan.wordBound S p room+10) := by
  let B:=SourcePlan.wordBound S p room
  let q:=SourcePhase.side S p
  let h:=SourceGeometry.history S p
  obtain ⟨side,forward,backward,vertices,edges⟩:=SourceGeometry.basic_widths S p room
  have geometry:=SourceGeometry.wordBound_plan S p room
  have bases:=PhaseStartup.bases_width q (SourcePhase.layout S p).forward
    (SourcePhase.layout S p).backward 2
  change h.base.bits.length≤_ at bases
  have history:=h.address_bound
  have layer:=h.layer_bound 0 (by omega)
  change (h.layer 0).bound 1≤h.bound at layer
  have capacity:=SourceGeometry.capacity_width q (GeometryProducer.vertices S p) (GeometryProducer.edges S p)
  have capacityRoom:=GeometryEmission.capacity_room (SourceRouting.indexedData S p) (SourcePhase.side_pos S p)
    (SourceEmission.geometry S p) (fun _=>by simp only [SourceEmission.geometry,Maxwell.Logical.Routing.SortArrays.get_ofFn])
  change packedLength (SourceEmission.geometry S p)+1+3072*q≤
    GeometryEmission.capacity q (GeometryProducer.vertices S p) (GeometryProducer.edges S p) at capacityRoom
  have packed : (packedLength (SourceEmission.geometry S p)).bits.length≤
      (GeometryEmission.capacity q (GeometryProducer.vertices S p) (GeometryProducer.edges S p)).bits.length:=
    Maxwell.Continuum.RationalWords.bits_mono (by omega)
  unfold wordBound countWidth
  change SourceGeometry.wordBound S p room+((h.layer 0).bound 1+
    (packedLength (SourceEmission.geometry S p)).bits.length+
    (GeometryProducer.vertices S p).bits.length+(GeometryProducer.edges S p).bits.length+4)≤_
  dsimp only [q,h,B] at *
  omega

theorem wordBound_source (S : Source.SparseSystem) (p : ℕ) (dimension_le : S.n≤S.nnz)
    (room : dimension S p<2^width S p) :
    wordBound S p room+10 ≤ 2^25*(S.nnz.bits.length+p+1) := by
  have a:=wordBound_plan S p room
  have b:=SourcePlan.wordBound_input S p room
  have c:=SourcePlan.inputWidth_source S p dimension_le
  omega

#print axioms wordBound_source
end CountedGeometry
end Maxwell.Cost.RoutingPorts.Complete
