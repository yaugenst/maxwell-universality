import Maxwell.Continuum.SourceRoutingPhaseKeys
import Maxwell.Cost.IncidenceEncoding

/-! Prefix semantics for an increasing scatter pass. The initial contents
are arbitrary; bijective writes fill the whole target without a zeroing oracle. -/

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryScatter
open Maxwell.Logical.Routing
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

def run {n : ℕ} (address : Fin n→Fin n) (value : Fin n→ℕ) (width : ℕ)
    (initial : Vector (List Bool) n) : (k : ℕ)→k ≤ n→Vector (List Bool) n
  | 0,_ => initial
  | k+1,h =>
      let i : Fin n:=⟨k,by omega⟩
      (run address value width initial k (by omega)).set (address i)
        (IncidenceEncoding.word width (value i))

theorem run_zero {n : ℕ} (address : Fin n→Fin n) (value : Fin n→ℕ) (width : ℕ)
    (initial : Vector (List Bool) n) (h : 0 ≤ n) : run address value width initial 0 h=initial := rfl

theorem run_succ {n : ℕ} (address : Fin n→Fin n) (value : Fin n→ℕ) (width : ℕ)
    (initial : Vector (List Bool) n) (k : ℕ) (h : k+1 ≤ n) :
    run address value width initial (k+1) h=
      (run address value width initial k (by omega)).set (address ⟨k,by omega⟩)
        (IncidenceEncoding.word width (value ⟨k,by omega⟩)) := rfl

theorem run_visited {n : ℕ} (address : Fin n→Fin n) (injective : Function.Injective address)
    (value : Fin n→ℕ) (width : ℕ) (initial : Vector (List Bool) n)
    (k : ℕ) (hk : k ≤ n) (i : Fin n) (hi : i.val<k) :
    (run address value width initial k hk).get (address i)=IncidenceEncoding.word width (value i) := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [run_succ,DummyFill.get_set]
      by_cases he : i.val=k
      · have same : (⟨k,by omega⟩ : Fin n)=i := Fin.ext he.symm
        simp only [same,↓reduceIte]
      · have different : address (⟨k,by omega⟩ : Fin n)≠address i := by
          intro h
          have same:=congrArg Fin.val (injective h)
          exact he same.symm
        simp only [different,↓reduceIte]
        exact ih (by omega) (by omega)

theorem run_lengths {n : ℕ} (address : Fin n→Fin n) (value : Fin n→ℕ) (width : ℕ)
    (initial : Vector (List Bool) n) (lengths : ∀i,(initial.get i).length=width)
    (k : ℕ) (hk : k ≤ n) : ∀i,((run address value width initial k hk).get i).length=width := by
  induction k with
  | zero => exact lengths
  | succ k ih =>
      intro i
      rw [run_succ,DummyFill.get_set]
      split
      · exact IncidenceEncoding.word_length _ _
      · exact ih (by omega) i

theorem run_complete {n : ℕ} (address : Fin n→Fin n) (injective : Function.Injective address)
    (value : Fin n→ℕ) (width : ℕ) (initial : Vector (List Bool) n) (desired : Vector ℕ n)
    (specification : ∀i,desired.get (address i)=value i) :
    run address value width initial n le_rfl=IncidenceEncoding.words width desired := by
  apply Vector.ext
  intro j hj
  let index : Fin n:=⟨j,hj⟩
  obtain ⟨i,he⟩:=Finite.surjective_of_injective injective index
  change (run address value width initial n le_rfl).get index=(IncidenceEncoding.words width desired).get index
  rw [←he,run_visited address injective value width initial n le_rfl i i.isLt,
    IncidenceEncoding.words_get,specification]

#print axioms run_complete

end Maxwell.Cost.RoutingPorts.Complete.GeometryScatter
