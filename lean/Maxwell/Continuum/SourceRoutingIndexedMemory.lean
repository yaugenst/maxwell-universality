import Maxwell.Continuum.SourceRoutingColorData
import Maxwell.Cost.Array

/-! Index-independent array semantics keep harmless finite-size casts out
of the recursive tree invariant. The conversion to actual bit arrays is exact. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.IndexedMemory
open Maxwell.Logical.Routing.Coloring.NumericSplit
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def Represents {α : Type*} {n : ℕ} (idx : α≃Fin n) (value : α→ℕ)
    (memory : ℕ→Bool) (base width : ℕ) : Prop :=
  ∀p j (hj : j<width),memory (base+(idx p).val*width+j)=
    (IncidenceEncoding.word width (value p))[j]'(by simpa only [IncidenceEncoding.word_length] using hj)

theorem numeric {α : Type*} {n : ℕ} (idx : α≃Fin n) (target : Equiv.Perm α)
    (memory : ℕ→Bool) (base width : ℕ) :
    Represents idx (fun p => (idx (target p)).val) memory base width ↔
      BitArray.Represents memory base width (DoublingPass.words width (Vector.ofFn (numericPerm idx target))) := by
  constructor
  · intro h
    refine ⟨fun i => by simp,?_⟩
    intro i j hj
    have hh:=h (idx.symm i) j hj
    simpa [DoublingPass.words,IncidenceEncoding.words,Vector.get,Fin.cast,numericPerm] using hh
  · intro h p j hj
    have hh:=h.bits (idx p) j hj
    simpa [DoublingPass.words,IncidenceEncoding.words,Vector.get,Fin.cast,numericPerm] using hh

theorem cast_index {α : Type*} {n m : ℕ} (h : n=m) (idx : α≃Fin n) (value : α→ℕ)
    (memory : ℕ→Bool) (base width : ℕ) :
    Represents (idx.trans (finCongr h)) value memory base width ↔ Represents idx value memory base width := by
  subst m
  rfl

theorem congr_index {α : Type*} {n m : ℕ} (idx : α≃Fin n) (other : α≃Fin m)
    (hi : ∀p,(idx p).val=(other p).val) (value : α→ℕ) (memory : ℕ→Bool) (base width : ℕ) :
    Represents idx value memory base width ↔ Represents other value memory base width := by
  simp only [Represents,hi]

theorem congr_value {α : Type*} {n : ℕ} (idx : α≃Fin n) (f g : α→ℕ) (he : ∀p,f p=g p)
    (memory : ℕ→Bool) (base width : ℕ) :
    Represents idx f memory base width ↔ Represents idx g memory base width := by
  simp only [Represents,he]

theorem same_memory {α : Type*} {n : ℕ} (idx : α≃Fin n) (value : α→ℕ)
    (before after : ℕ→Bool) (base width : ℕ)
    (hf : ∀p,base ≤ p → p<base+n*width → after p=before p)
    (h : Represents idx value before base width) : Represents idx value after base width := by
  intro p j hj
  rw [hf _ (by omega) (by
    have hh:=Nat.mul_le_mul_right width (Nat.succ_le_of_lt (idx p).isLt)
    nlinarith only [hh,hj])]
  exact h p j hj

#print axioms numeric
#print axioms same_memory
end Maxwell.Cost.RoutingPorts.Complete.Tree.IndexedMemory
