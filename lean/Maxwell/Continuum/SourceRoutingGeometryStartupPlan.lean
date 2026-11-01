import Maxwell.Continuum.SourceRoutingGeometryStored
import Maxwell.Cost.Structured.WordCopyAppend

/-! The output buffer starts immediately after the third routing history.
Its clock is the retained history clock extended by twelve actual cells. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryStartup
open Structured GeometryArithmetic Maxwell.Logical.Routing
set_option maxHeartbeats 3200000
set_option maxRecDepth 20000

def outputBase {q : ℕ} (h : GeometryHistory.Plan q) : ℕ := h.following.following.slab (2*q+1)
def outputWidth {q : ℕ} (h : GeometryHistory.Plan q) : ℕ := h.width+12
def outputClock {q : ℕ} (h : GeometryHistory.Plan q) : List Bool := h.clock++List.replicate 12 false

theorem coordinate_width {q : ℕ} (h : GeometryHistory.Plan q) :
    (1024*q+1).bits.length≤outputWidth h := by
  have hq:=Maxwell.Continuum.RationalWords.bits_mono (show q≤q*q by nlinarith [h.positive])
  have hm:=RationalAccumulator.bits_mul_le 1024 q
  have ha:=RationalAccumulator.bits_add_le (1024*q) 1
  have literal : (1024:ℕ).bits.length=11:=by decide
  norm_num at hm ha
  dsimp only [outputWidth,GeometryHistory.Plan.width]
  omega

theorem outputBase_eq {q : ℕ} (h : GeometryHistory.Plan q) :
    outputBase h=h.base+3*(2*q+1)*h.stride := by
  simp only [outputBase,GeometryHistory.Plan.following,GeometryHistory.Plan.slab,GeometryHistory.Plan.stride,
    GeometryHistory.Plan.width]
  ring

def plan {q : ℕ} (h : GeometryHistory.Plan q) (backward : ℕ)
    (start : h.base=backward+12*h.stride) : GeometryEmission.Plan q where
  path := {
    history := h
    base := outputBase h
    width := outputWidth h
    clock := outputClock h
    positive := by unfold outputWidth;omega
    clock_length := by simp only [outputClock,List.length_append,List.length_replicate,h.clock_length];rfl
    coordinate_width := coordinate_width h
    separated := by rw [outputBase_eq];unfold GeometryHistory.Plan.slab;nlinarith }
  secondBefore := by
    change h.following.slab (2*q+1)≤outputBase h
    rw [outputBase_eq]
    simp only [GeometryHistory.Plan.following,GeometryHistory.Plan.slab,GeometryHistory.Plan.stride,
      GeometryHistory.Plan.width]
    rw [Nat.mul_assoc 3 (2*q+1)]
    omega
  thirdBefore := le_rfl
  backward := backward
  backwardBefore := by
    change backward+h.stride≤outputBase h
    rw [outputBase_eq,start]
    omega

def ports : Finset ℕ := {711,717,1250,1252,1260}
def ids : Finset ℕ := GeometryArithmetic.ids∪ports
def work : Finset ℕ := GeometryArithmetic.work∪{1250,1251,1252,1260}
def instructions : List NatAssign.Instruction :=
  [.copy 1216 1252,.copy 711 1250,.literal 1230 12,.add 1230 1250,.copy 717 1260,
   .copy 1200 1231,.multiply 1200 1231,.multiply 1217 1231,
   .literal 1232 12,.multiply 1231 1232,.add 717 1232,
   .copy 1232 1215,.copy 1232 1216,.add 1231 1216,
   .literal 1202 1,.literal 1230 0,.literal 1231 0,.literal 1232 0]

def initial {q : ℕ} (h : GeometryHistory.Plan q) (backward i : ℕ) : ℕ :=
  if i∈GeometryArithmetic.ids then GeometrySort.seed (h.following.following.layer (2*q)) (2*q+1) 0 i
  else if i=711 then h.width else if i=717 then backward else 0

theorem valid : ∀a∈instructions,a.Valid ids := by
  simp [instructions,NatAssign.Instruction.Valid,ids,ports,GeometryArithmetic.ids,controls]

theorem values_seed {q : ℕ} (h : GeometryHistory.Plan q) (backward : ℕ)
    (start : h.base=backward+12*h.stride) (i : ℕ) (hi : i∈GeometryArithmetic.ids) :
    NatAssign.values instructions (initial h backward) i=GeometrySort.seed (h.layer 0) 1 0 i := by
  simp only [GeometryArithmetic.ids,controls,Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
    Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with hi|hi
  · obtain ⟨lo,high⟩:=hi
    interval_cases i
    all_goals simp [instructions,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial,GeometrySort.seed,GeometryArithmetic.ids,controls,
      Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,GeometryHistory.Plan.layer,
      GeometryHistory.Plan.slab,GeometryHistory.Plan.stride,GeometryHistory.Plan.width,
      GeometrySort.Plan.width,start]
    all_goals ring
  · rcases hi with rfl|rfl|rfl|rfl
    all_goals simp [instructions,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial,GeometrySort.seed,GeometryArithmetic.ids,controls,
      Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts]

theorem values_outputs {q : ℕ} (h : GeometryHistory.Plan q) (backward : ℕ) :
    NatAssign.values instructions (initial h backward) 1250=outputWidth h ∧
    NatAssign.values instructions (initial h backward) 1252=outputBase h ∧
    NatAssign.values instructions (initial h backward) 1260=backward := by
  simp [instructions,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,initial,GeometrySort.seed,GeometryArithmetic.ids,controls,
    Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,outputWidth,outputBase,
    GeometryHistory.Plan.layer,Nat.add_comm]

#print axioms values_seed
end Maxwell.Cost.RoutingPorts.Complete.GeometryStartup
