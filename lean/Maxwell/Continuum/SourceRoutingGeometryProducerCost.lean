import Maxwell.Continuum.SourceRoutingGeometryCost

/-! A cubic routing-size cost for initialization and the complete packed geometry
producer. The remaining factor is quadratic in the actual history/address widths. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryProducer
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Composition
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024

def wordBound (S : Source.SparseSystem) (precision : ℕ) (h : GeometryHistory.Plan (side S precision))
    (backward : ℕ) (start : h.base=backward+12*h.stride) : ℕ :=
  GeometryStartup.inputWidth h backward+
    GeometryEmission.wordBound (GeometryStartup.plan h backward start)
      (GeometryEmission.capacity (side S precision) (vertices S precision) (edges S precision))

theorem price_bound (S : Source.SparseSystem) (precision : ℕ)
    (h : GeometryHistory.Plan (side S precision)) (backward : ℕ)
    (start : h.base=backward+12*h.stride) :
    price S precision h backward start≤
      2^264*(side S precision+1)^3*(wordBound S precision h backward start+3)^2 := by
  let B:=wordBound S precision h backward start
  let Q:=(B+3)^2
  let data:=SourceRouting.indexedData S precision
  have vertices:=Fintype.card_le_of_injective _ data.tile_injective
  have edges:=Fintype.card_le_of_injective _ data.pair_injective
  simp only [Fintype.card_fin,Fintype.card_prod] at vertices edges
  have traversal:=GeometryEmission.price_bound (GeometryStartup.plan h backward start)
    (GeometryEmission.capacity (side S precision) (GeometryProducer.vertices S precision)
      (GeometryProducer.edges S precision)) (GeometryProducer.vertices S precision)
    (GeometryProducer.edges S precision) ((sourceCircuit S precision).size+(sourceCircuit S precision).size)
    B (by unfold B wordBound;omega) (by unfold GeometryProducer.vertices side; nlinarith)
    (by unfold GeometryProducer.edges side; nlinarith)
    (by unfold GeometryProducer.vertices;omega)
  have startup : GeometryStartup.cost h backward≤2^74*Q:=by
    unfold GeometryStartup.cost Q
    gcongr
    unfold B wordBound
    omega
  change GeometryEmission.price _ _ _ _ _≤2^263*(side S precision+1)^3*Q at traversal
  have one : 1≤(side S precision+1)^3:=by
    have positive : 0<(side S precision+1)^3:=by positivity
    omega
  unfold price
  calc
    _≤2^74*Q+2^263*(side S precision+1)^3*Q:=Nat.add_le_add startup traversal
    _=(2^74+2^263*(side S precision+1)^3)*Q:=by ring
    _≤2^264*(side S precision+1)^3*Q:=Nat.mul_le_mul_right _ (by omega)

private theorem history_bound_mono {q : ℕ} (h : GeometryHistory.Plan q) :
    h.bound≤h.following.bound := by
  have address : h.slab (2*q+1)≤h.following.slab (2*q+1):=by
    simp only [GeometryHistory.Plan.following,GeometryHistory.Plan.slab,GeometryHistory.Plan.stride,
      GeometryHistory.Plan.width]
    omega
  have bits:=Maxwell.Continuum.RationalWords.bits_mono address
  unfold GeometryHistory.Plan.bound
  change h.width+q.bits.length+(2*q+1).bits.length+2*(h.slab (2*q+1)).bits.length+32≤
    h.width+q.bits.length+(2*q+1).bits.length+2*(h.following.slab (2*q+1)).bits.length+32
  omega

def addressWidth {q : ℕ} (h : GeometryHistory.Plan q) (backward capacity : ℕ) : ℕ :=
  h.following.following.bound+capacity.bits.length+backward.bits.length+16

theorem startup_word_bound {q : ℕ} (h : GeometryHistory.Plan q) (backward n : ℕ)
    (start : h.base=backward+12*h.stride) :
    GeometryStartup.inputWidth h backward+
      GeometryEmission.wordBound (GeometryStartup.plan h backward start) n≤16*addressWidth h backward n := by
  have first:=(history_bound_mono h).trans (history_bound_mono h.following)
  have second:=history_bound_mono h.following
  have width : h.width≤h.following.following.bound:=by
    unfold GeometryHistory.Plan.bound
    change h.width≤h.width+q.bits.length+(2*q+1).bits.length+
      2*(h.following.following.slab (2*q+1)).bits.length+32
    omega
  have widthBits : h.width.bits.length≤h.width:=by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n:=h.width))
  have qBits : q.bits.length≤h.following.following.bound:=by
    unfold GeometryHistory.Plan.bound;omega
  have output : (GeometryStartup.outputBase h).bits.length≤h.following.following.bound:=by
    unfold GeometryStartup.outputBase GeometryHistory.Plan.bound;omega
  have times:=RationalAccumulator.bits_mul_le 6 q
  have plus:=RationalAccumulator.bits_add_le (6*q) 1
  have six : (6:ℕ).bits.length=3:=by decide
  rw [six] at times
  norm_num at plus
  have level : (6*q+1).bits.length≤h.following.following.bound+4:=by omega
  simp only [GeometryStartup.inputWidth,GeometryEmission.wordBound,GeometryEmission.secondPlan,
    GeometryEmission.thirdPlan,GeometryStartup.plan,GeometryPathPhase.Plan.following,
    GeometryPathPhase.Plan.bound,GeometryStartup.outputWidth,addressWidth]
  omega

theorem price_address_bound (S : Source.SparseSystem) (precision : ℕ)
    (h : GeometryHistory.Plan (side S precision)) (backward : ℕ)
    (start : h.base=backward+12*h.stride) :
    price S precision h backward start≤2^272*(side S precision+1)^3*
      (addressWidth h backward
        (GeometryEmission.capacity (side S precision) (vertices S precision) (edges S precision))+3)^2 := by
  have words:=startup_word_bound h backward
    (GeometryEmission.capacity (side S precision) (vertices S precision) (edges S precision)) start
  change wordBound S precision h backward start≤16*addressWidth h backward
    (GeometryEmission.capacity (side S precision) (vertices S precision) (edges S precision)) at words
  apply (price_bound S precision h backward start).trans
  calc
    _≤2^264*(side S precision+1)^3*
        (16*(addressWidth h backward
          (GeometryEmission.capacity (side S precision) (vertices S precision) (edges S precision))+3))^2:=by
      gcongr
      omega
    _=2^272*(side S precision+1)^3*
        (addressWidth h backward
          (GeometryEmission.capacity (side S precision) (vertices S precision) (edges S precision))+3)^2:=by ring

#print axioms price_address_bound
end Maxwell.Cost.RoutingPorts.Complete.GeometryProducer
