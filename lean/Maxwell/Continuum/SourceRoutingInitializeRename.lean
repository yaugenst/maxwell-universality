import Maxwell.Cost.PositiveGraph.Initialize.Fill
import Maxwell.Cost.Structured.Rename

/-! A fixed tape relocation reuses the verified constant-array initializer
without disturbing the source graph's public metadata banks. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Initialize
open Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def baseBank (backward : Bool) : ℕ := if backward then 717 else 716

def shift (backward : Bool) (i : ℕ) : ℕ :=
  if i=140 then 711 else if i=711 then 140 else
  if i=141 then baseBank backward else if i=baseBank backward then 141 else
  if i=142 then 718 else if i=718 then 142 else
  if i=143 then 709 else if i=709 then 143 else
  if i=160 then 730 else if i=730 then 160 else
  if i=161 then 732 else if i=732 then 161 else
  if i=162 then 739 else if i=739 then 162 else i

def moved (backward : Bool) : Finset ℕ :=
  {140,711,141,baseBank backward,142,718,143,709,160,730,161,732,162,739}

theorem shift_fixed (backward : Bool) (i : ℕ) (hi : i∉moved backward) : shift backward i=i := by
  simp only [moved,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  simp only [shift,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.1,hi.2.2.2.2.2.1,
    hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2.2.1,
    hi.2.2.2.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2.2.2.2.1,
    hi.2.2.2.2.2.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hi.2.2.2.2.2.2.2.2.2.2.2.2.2,↓reduceIte]

theorem shift_involutive (backward : Bool) : Function.Involutive (shift backward) := by
  intro i
  by_cases hi : i∈moved backward
  · simp only [moved,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases backward <;> rfl
  · rw [shift_fixed backward i hi,shift_fixed backward i hi]

def relocation (backward : Bool) : Equiv.Perm ℕ :=
  ⟨shift backward,shift backward,shift_involutive backward,shift_involutive backward⟩

theorem renamed_tape (backward : Bool) (s : Store) (i : ℕ) :
    (s.renameTapes (relocation backward)).val.tapes i=s.val.tapes (shift backward i) := rfl

theorem renamed_tape_symm (backward : Bool) (s : Store) (i : ℕ) :
    (s.renameTapes (relocation backward).symm).val.tapes i=s.val.tapes (shift backward i) := rfl

theorem shift_small (backward : Bool) (i : ℕ) (hi : i<10) : shift backward i=i := by
  apply shift_fixed
  cases backward <;> simp only [moved,baseBank,Bool.false_eq_true,↓reduceIte,
    Finset.mem_insert,Finset.mem_singleton]
  all_goals omega

theorem shift_large (backward : Bool) (i : ℕ) (hi : 10 ≤ i) : 10 ≤ shift backward i := by
  by_cases hm : i∈moved backward
  · simp only [moved,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases backward <;> decide
  · rw [shift_fixed backward i hm]
    exact hi

def ports : PositiveGraph.Initialize.Ports := ⟨140,141,142,143,by
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega⟩

def fillCode (backward : Bool) : Code :=
  .call ((PositiveGraph.Initialize.fillCode ports).compile.renameTapes (relocation backward))

#print axioms shift_involutive

end Maxwell.Cost.RoutingPorts.Complete.Initialize
