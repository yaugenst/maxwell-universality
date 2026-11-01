import Maxwell.Continuum.SourceRoutingHistoriesLayout
import Maxwell.Cost.Structured.NatAssign.Values

/-! Layout and fixed arithmetic for building the three geometry histories
after a routing tree has produced its permutation and root-color arrays. -/

namespace Maxwell.Cost.RoutingPorts.Complete.PhaseStartup
open Structured Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def bases (q forward backward : ℕ) : Fin 5→ℕ :=
  let slab := q*q*(q*q).bits.length
  let labels := backward+11*slab
  let first := labels+slab
  let step := (2*q+1)*slab
  ![forward,labels,first,first+step,first+step+step]

def plan (q : ℕ) (hq : 0<q) (l : Layout (q*q))
    (ordered : l.forward+q*q*(q*q).bits.length≤l.backward) : GeometryPhase.Plan q where
  base := bases q l.forward l.backward
  clock := l.clock
  positive := hq
  clock_length := l.clock_length
  separated := by
    have step : q*q*(q*q).bits.length≤(2*q+1)*(q*q*(q*q).bits.length) :=
      Nat.le_mul_of_pos_left _ (by omega)
    intro a b hab
    fin_cases a <;> fin_cases b <;> try contradiction
    all_goals norm_num [bases]
    all_goals first | (left;omega) | (right;omega)

theorem sequential (q : ℕ) (hq : 0<q) (l : Layout (q*q))
    (ordered : l.forward+q*q*(q*q).bits.length≤l.backward) :
    GeometryHistories.Sequential (plan q hq l ordered) := by
  constructor <;> rfl

def sourcePorts : Finset ℕ := {709,710,711,716,717}
def ids : Finset ℕ := GeometryArithmetic.ids∪sourcePorts
def instructions : List NatAssign.Instruction :=
  (List.range 40).map (fun j => .literal (1200+j) 0)++
  [.copy 710 1200,.add 710 1200,
   .copy 709 1215,.multiply 711 1215,.copy 1215 1216,
   .literal 1239 11,.multiply 1239 1215,.add 717 1215,.add 1215 1216,
   .copy 1200 1217,.add 1200 1217,.literal 1219 1,.add 1219 1217,
   .multiply 709 1217,.multiply 711 1217,
   .copy 1217 1218,.add 1216 1217,.add 1217 1218,.literal 1239 0]

def initial (half forward backward i : ℕ) : ℕ :=
  if i=709 then (2*half)*(2*half) else if i=710 then half else
  if i=711 then ((2*half)*(2*half)).bits.length else if i=716 then forward else
  if i=717 then backward else 0

theorem valid : ∀ a∈instructions,a.Valid ids := by
  simp [instructions,List.range_succ,NatAssign.Instruction.Valid,ids,sourcePorts,
    GeometryArithmetic.ids,GeometryArithmetic.controls]

theorem values (half : ℕ) (hh : 0<half) (l : Layout ((2*half)*(2*half)))
    (ordered : l.forward+(2*half)*(2*half)*((2*half)*(2*half)).bits.length≤l.backward)
    (i : ℕ) (hi : i∈GeometryArithmetic.ids) :
    NatAssign.values instructions (initial half l.forward l.backward) i=
      GeometryPhase.seed (plan (2*half) (by positivity) l ordered) 0 i := by
  simp only [GeometryArithmetic.ids,GeometryArithmetic.controls,
    Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_union,
    Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with hi|hi
  · obtain ⟨hlo,hhi⟩ := hi
    interval_cases i
    all_goals simp [instructions,List.range_succ,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,initial,
      GeometryPhase.seed,plan,bases]
    all_goals ring
  · rcases hi with rfl|rfl|rfl|rfl
    all_goals simp [instructions,List.range_succ,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,initial,GeometryPhase.seed]

#print axioms values

end Maxwell.Cost.RoutingPorts.Complete.PhaseStartup
