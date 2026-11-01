import Maxwell.Cost.Structured.WordCleanup
import Maxwell.Cost.Structured.NatAssign

/-! Compose measured cleanup budgets independently of the computation that
produced the words. Canonical natural banks are one source of such budgets. -/
namespace Maxwell.Cost.Structured.WordCleanup

theorem Bounded.mono {words : List ℕ} {B C : ℕ} {s : BitRAMState}
    (bounded : Bounded words B s) (le : B≤C) : Bounded words C s := by
  intro k hk
  obtain ⟨bits,width,stored⟩:=bounded k hk
  exact ⟨bits,width.trans le,stored⟩

theorem Bounded.append {left right : List ℕ} {B C : ℕ} {s : BitRAMState}
    (first : Bounded left B s) (second : Bounded right C s) :
    Bounded (left++right) (max B C) s := by
  intro k hk
  rcases List.mem_append.mp hk with h | h
  · exact first.mono (le_max_left _ _) k h
  · exact second.mono (le_max_right _ _) k h

theorem Bounded.of_bank {S : Finset ℕ} {n : ℕ→ℕ} {B : ℕ} {s : BitRAMState}
    (stored : NatAssign.Bank S n s) (width : ∀k∈S,(n k).bits.length≤B) :
    Bounded (S.sort (·≤·)) B s := by
  intro k hk
  have member : k∈S := (Finset.mem_sort _).mp hk
  exact ⟨(n k).bits,width k member,stored k member⟩

#print axioms Bounded.of_bank
end Maxwell.Cost.Structured.WordCleanup
