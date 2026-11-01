import Maxwell.Continuum.SourceRoutingGeometryProducer

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open GeometryPath GeometryPathPhase
set_option maxHeartbeats 2600000
set_option maxRecDepth 20000

theorem count_width {q : ℕ} (p : GeometryPathPhase.Plan q) (n : ℕ) :
    (2*q).bits.length≤p.bound n := by
  have h:=Maxwell.Continuum.RationalWords.bits_mono (show 2*q≤6*q+1 by omega)
  unfold GeometryPathPhase.Plan.bound
  omega

theorem terminal_width {q : ℕ} (p : GeometryPathPhase.Plan q) (n k : ℕ) (hk : k≤2*q) :
    terminalBound (p.history.layer k) (k+1) p.width p.base n≤p.bound n := by
  have h:=p.history.layer_bound k hk
  unfold terminalBound GeometryPathPhase.Plan.bound
  omega

theorem forward_phase_cost {q : ℕ} (p : GeometryPathPhase.Plan q) (n B : ℕ) (bound : p.bound n≤B) :
    GeometryPathPhase.phaseCost p n≤2^249*(q+1)*(B+3)^2 := by
  let Q:=(B+3)^2
  have cq:=count_width p n
  have small : B≤Q:=by dsimp only [Q];nlinarith
  have one : 1≤Q:=by dsimp only [Q];nlinarith
  have quad : (p.bound n+3)^2≤Q:=by dsimp only [Q];gcongr
  have counter : 13*(2*q).bits.length+15≤28*Q:=by omega
  have clear : 6*(2*q).bits.length+4≤10*Q:=by omega
  calc
    GeometryPathPhase.phaseCost p n≤2^32*Q+(2*q+1)*(28*Q)+2*q*(2^244*Q)+10*Q := by
      have a:=Nat.mul_le_mul_left (2^32) quad
      have b:=Nat.mul_le_mul_left (2*q+1) counter
      have c:=Nat.mul_le_mul_left (2*q) (Nat.mul_le_mul_left (2^244) quad)
      unfold GeometryPathPhase.phaseCost GeometryPathPhase.loopCost
      omega
    _≤2^249*(q+1)*Q:=by nlinarith

theorem reverse_phase_cost {q : ℕ} (p : GeometryPathPhase.Plan q) (n B : ℕ) (bound : p.bound n≤B) :
    GeometryPathReverse.phaseCost p n≤2^249*(q+1)*(B+3)^2 := by
  apply (show GeometryPathReverse.phaseCost p n≤GeometryPathPhase.phaseCost p n from ?_).trans
    (forward_phase_cost p n B bound)
  unfold GeometryPathReverse.phaseCost GeometryPathReverse.loopCost GeometryPathPhase.phaseCost GeometryPathPhase.loopCost
  gcongr
  norm_num

theorem boundary_width {q : ℕ} (p : GeometryPathPhase.Plan q)
    (separated : p.history.following.slab (2*q+1)≤p.base) (n : ℕ) :
    (p.history.layer (2*q+1)).bound (2*q+2)≤(p.following separated).bound n := by
  have h:=(p.history.following.layer_bound 0 (Nat.zero_le _))
  have hr:=Maxwell.Continuum.RationalWords.bits_mono
    (show 2*q+2≤6*q+1 by have hq:=p.history.positive;omega)
  have address : (p.history.layer (2*q+1)).destination=(p.history.following.layer 0).destination:=by
    simp only [GeometryHistory.Plan.layer,GeometryHistory.Plan.slab,GeometryHistory.Plan.following,
      GeometryHistory.Plan.stride,GeometryHistory.Plan.width]
    ring
  have source : (p.history.layer (2*q+1)).source=(p.history.following.layer 0).source:=by
    simp only [GeometryHistory.Plan.layer,GeometryHistory.Plan.slab,GeometryHistory.Plan.following,Nat.zero_mul,Nat.add_zero]
  unfold GeometrySort.Plan.bound at h ⊢
  rw [address,source]
  rw [show (p.history.layer (2*q+1)).width=(p.history.following.layer 0).width from rfl]
  change _≤p.history.following.bound+(6*q+1).bits.length+2*n.bits.length+p.width+p.base.bits.length+64
  omega

theorem forward_append_cost {q : ℕ} (p : GeometryPathPhase.Plan q)
    (separated : p.history.following.slab (2*q+1)≤p.base) (n B : ℕ)
    (bound : p.bound n≤B) (next : (p.following separated).bound n≤B) :
    GeometryPathPhase.appendCost p separated n≤2^251*(q+1)*(B+3)^2 := by
  have history : p.history.bound≤B:=by unfold GeometryPathPhase.Plan.bound at bound;omega
  have following : (p.history.following.layer 0).bound 1≤B:=
    (p.history.following.layer_bound 0 (Nat.zero_le _)).trans (by
      change p.history.following.bound+(6*q+1).bits.length+2*n.bits.length+p.width+p.base.bits.length+64≤B at next
      omega)
  have first : (p.history.bound+3)^2≤(B+3)^2:=by gcongr
  have second : ((p.history.following.layer 0).bound 1+2)^2≤(B+3)^2:=by gcongr;omega
  have phase:=forward_phase_cost (p.following separated) n B next
  unfold GeometryPathPhase.appendCost
  calc
    _≤2^40*(B+3)^2+2^128*(B+3)^2+2^249*(q+1)*(B+3)^2:=by gcongr
    _≤2^251*(q+1)*(B+3)^2:=by nlinarith

theorem reverse_append_cost {q : ℕ} (p : GeometryPathPhase.Plan q)
    (separated : p.history.following.slab (2*q+1)≤p.base) (n B : ℕ)
    (bound : p.bound n≤B) (next : (p.following separated).bound n≤B) :
    GeometryPathReverse.appendCost p n≤2^252*(q+1)*(B+3)^2 := by
  have history : p.history.bound≤B:=by unfold GeometryPathPhase.Plan.bound at bound;omega
  have following : (p.history.following.layer 0).bound 1≤B:=
    (p.history.following.layer_bound 0 (Nat.zero_le _)).trans (by
      change p.history.following.bound+(6*q+1).bits.length+2*n.bits.length+p.width+p.base.bits.length+64≤B at next
      omega)
  have boundary:=(boundary_width p separated n).trans next
  have finalRound:=((p.history.layer_bound (2*q) le_rfl).trans history)
  have phase:=reverse_phase_cost p n B bound
  have a : ((p.history.following.layer 0).bound 1+3)^2≤(B+3)^2:=by gcongr
  have b : ((p.history.layer (2*q+1)).bound (2*q+2)+2)^2≤(B+3)^2:=by gcongr;omega
  have c : ((p.history.layer (2*q)).bound (2*q+1)+2)^2≤(B+3)^2:=by gcongr;omega
  unfold GeometryPathReverse.appendCost GeometryPathReverse.restartCost
  calc
    _≤2^24*(B+3)^2+2^152*(B+3)^2+2^128*(B+3)^2+2^249*(q+1)*(B+3)^2:=by gcongr
    _≤2^252*(q+1)*(B+3)^2:=by nlinarith

#print axioms reverse_append_cost
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
