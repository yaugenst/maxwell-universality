import Maxwell.Cost.GraphIncidence.Run

namespace Maxwell.Cost.GraphIncidence
open Structured

def budget (width dimension count : ℕ) (clock : List Bool) : ℕ :=
  IncidencePass.budget (layout width dimension count) (4*count).bits+clock.length+5

theorem privatePrice_bound (width dimension count : ℕ) (clock : List Bool) :
    privatePrice width dimension count clock≤252*budget width dimension count clock+267 := by
  have hl : ∀ i∈ids, (initial width dimension count clock (fun _ => []) i).length≤budget width dimension count clock := by
    intro i hi
    simp only [ids,destinations,sources,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with hi | hi
    · rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals norm_num [initial,budget,IncidencePass.budget,layout,show (Nat.bits 2).length=2 from rfl]
    · rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals norm_num [initial,budget,IncidencePass.budget,layout,show (Nat.bits 2).length=2 from rfl]
      all_goals omega
  have h := WordAssign.price_bound assignments ids (initial width dimension count clock (fun _ => []))
    (budget width dimension count clock) valid hl
  change WordAssign.price assignments (initial width dimension count clock (fun _ => []))≤
    12*(21*budget width dimension count clock+21)+1 at h
  dsimp only [privatePrice,price]
  omega

theorem passCost_bound (width dimension count : ℕ) (clock : List Bool) :
    passCost width dimension count clock≤400000*(4*count+1)*(budget width dimension count clock+1)^2 := by
  let b := budget width dimension count clock
  have h := privatePrice_bound width dimension count clock
  have hb : IncidencePass.budget (layout width dimension count) (4*count).bits≤b := by dsimp [b,budget]; omega
  have hl : (4*count).bits.length≤b := by
    dsimp [b,budget,IncidencePass.budget]
    omega
  have hs : b+1≤(b+1)^2 := by nlinarith
  have hp : (IncidencePass.budget (layout width dimension count) (4*count).bits+1)^2≤(b+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul_left (4*count*300000) hp
  change privatePrice width dimension count clock≤252*b+267 at h
  change _≤400000*(4*count+1)*(b+1)^2
  dsimp only [passCost,IncidencePass.loopCost]
  nlinarith

end Maxwell.Cost.GraphIncidence
