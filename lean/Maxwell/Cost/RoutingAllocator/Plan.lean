import Maxwell.Cost.RoutingAllocator.Layout
import Maxwell.Cost.Structured.NatAssign.Bounds

namespace Maxwell.Cost.RoutingAllocator
open Structured

/-- The only runtime inputs are heap, count, width and the two existing bases.
Other canonical words may contain values from an earlier recursive node. -/
def ids : Finset ℕ := {80,81,82,84,85,86,96,98,99,100,101,102,103,104,105,
  122,123,124,125,190,191,192,193,194,195,196}

def statements : List NatAssign.Instruction :=
  [.copy 191 196,.multiply 192 196,
   .copy 190 98,.add 196 190,.copy 190 99,.add 196 190,
   .copy 190 102,.add 196 190,.copy 190 103,.add 196 190,
   .copy 190 104,.add 196 190,.copy 190 105,.add 196 190,
   .copy 190 122,.add 196 190,.copy 190 123,.add 196 190,
   .copy 190 124,.add 196 190,.copy 190 125,.add 196 190,
   .copy 190 195,.add 196 190,
   .copy 193 100,.copy 194 101,.copy 192 80,.copy 191 96,
   .copy 102 82,.copy 103 84,.copy 104 85,.copy 98 86,.literal 81 0]

def code : Code := NatAssign.code statements

def price (v : ℕ → ℕ) : ℕ := NatAssign.price statements v

def work : Finset ℕ := NatAssign.changes statements

def outputValues (v : ℕ → ℕ) (i : ℕ) : ℕ :=
  let h := v 190
  let n := v 191
  let w := v 192
  if i=80 then w else if i=81 then 0 else if i=82 then slab h n w 2 else
  if i=84 then slab h n w 3 else if i=85 then slab h n w 4 else if i=86 then h else
  if i=96 then n else if i=98 then h else if i=99 then slab h n w 1 else
  if i=100 then v 193 else if i=101 then v 194 else
  if i=102 then slab h n w 2 else if i=103 then slab h n w 3 else
  if i=104 then slab h n w 4 else if i=105 then slab h n w 5 else
  if i=122 then slab h n w 6 else if i=123 then slab h n w 7 else
  if i=124 then slab h n w 8 else if i=125 then slab h n w 9 else
  if i=190 then nextFrontier h n w else if i=195 then parentOutput h n w else
  if i=196 then n*w else v i

theorem ids_lower : ∀ i ∈ ids, 4 ≤ i := by decide

theorem valid : ∀ a ∈ statements, a.Valid ids := by
  simp [statements,NatAssign.Instruction.Valid,ids]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem values_at (v : ℕ → ℕ) (i : ℕ) (hi : i ∈ ids) :
    NatAssign.values statements v i=outputValues v i := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals dsimp [statements,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,outputValues,slab,nextFrontier,parentOutput,
    Function.update]
  all_goals ring

/-- The finite arithmetic program has quadratic cost in canonical input-word
length; its instruction list and constant are independent of the routed graph. -/
theorem price_bound (v : ℕ → ℕ) (B : ℕ) (hv : ∀i∈ids,(v i).bits.length ≤ B) :
    price v ≤ 3000*8^statements.length*(B+2)^2 := by
  exact NatAssign.price_bound ids statements valid v B hv
    (by simp [statements,NatAssign.Instruction.literalWidth])

end Maxwell.Cost.RoutingAllocator
