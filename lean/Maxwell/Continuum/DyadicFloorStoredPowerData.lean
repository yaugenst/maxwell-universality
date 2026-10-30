import Maxwell.Continuum.DyadicFloorExecution
import Maxwell.Continuum.NatAssignExternalWord

/-! The floor evaluator can read its scale from a stored power-of-two word.
Its finite instruction list then depends only on static register addresses. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor.StoredPower
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def allIds (S : Finset ℕ) : Finset ℕ := insert 144 (DyadicFloor.allIds S)
def workspace (S : Finset ℕ) : Finset ℕ := insert 144 (DyadicFloor.workspace S)
def withPower (P : ℕ) (v : ℕ→ℕ) : ℕ→ℕ := Function.update v 144 (2^P)
def prepare (source : ℕ) : List NatAssign.Instruction :=
  .copy 144 143::(DyadicFloor.prepare 0 source).tail
def code (target source : ℕ) : Code :=
  .seq (NatAssign.code (prepare source))
    (.seq RationalMagnitude.program
      (.seq (NaturalQuotient.code 34 142 140) (NatAssign.code (DyadicFloor.finish target))))

theorem power_outside (S : Finset ℕ) : 144∉DyadicFloor.allIds S := by
  intro hi
  rcases Finset.mem_union.mp hi with hi | hi
  · rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hi
        have hp := positivePort_ge r
        have hn := negativePort_ge r
        have hd := denominatorPort_ge r
        simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
        omega
      · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton] at hi
        omega
    · simp only [extraIds,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
  · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    omega

theorem allIds_ge (S : Finset ℕ) (i : ℕ) (hi : i∈allIds S) : 10 ≤ i := by
  rcases Finset.mem_insert.mp hi with rfl | hi
  · decide
  · exact DyadicFloor.allIds_ge S i hi

theorem prepare_valid (S : Finset ℕ) (source : ℕ) (hs : source∈S) :
    ∀a∈prepare source,a.Valid (allIds S) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact ⟨Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (extra_mem S 143 (by decide)),by decide⟩
  · have hv := DyadicFloor.prepare_valid S 0 source hs a (List.mem_of_mem_tail ha)
    cases a <;> first
      | exact Finset.mem_insert_of_mem hv
      | exact ⟨Finset.mem_insert_of_mem hv.1,Finset.mem_insert_of_mem hv.2.1,hv.2.2⟩

theorem prepare_values (P : ℕ) (v : ℕ→Parts) (source : ℕ) :
    NatAssign.values (prepare source) (withPower P (dataValues v))=
      withPower P (beforeMagnitude P v source) := by
  let tail := (DyadicFloor.prepare P source).tail
  have he : (DyadicFloor.prepare 0 source).tail=tail := rfl
  have hv : ∀a∈tail,a.Valid (DyadicFloor.allIds {source}) := by
    intro a ha
    exact DyadicFloor.prepare_valid {source} P source (by simp) a (List.mem_of_mem_tail ha)
  have hh := NatAssign.values_update_outside (DyadicFloor.allIds {source}) tail hv
    (Function.update (dataValues v) 143 (2^P)) 144 (2^P) (power_outside {source})
  have hinit : NatAssign.Instruction.update (.copy 144 143) (withPower P (dataValues v))=
      withPower P (Function.update (dataValues v) 143 (2^P)) := by
    simp only [NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      withPower,Function.update_self]
    exact (Function.update_comm (by decide : (143:ℕ)≠144) _ _ _).symm
  rw [prepare,NatAssign.values,hinit,he]
  change NatAssign.values tail (withPower P (Function.update (dataValues v) 143 (2^P)))=
    withPower P (NatAssign.values tail (Function.update (dataValues v) 143 (2^P))) at hh
  rw [hh]
  change withPower P (NatAssign.values (DyadicFloor.prepare P source) (dataValues v))=_
  rw [DyadicFloor.prepare_values]

theorem finish_values (S : Finset ℕ) (P : ℕ) (v : ℕ→Parts) (target source : ℕ) (ht : target∈S) :
    NatAssign.values (DyadicFloor.finish target) (withPower P (divided P v source))=
      withPower P (dataValues (Function.update v target (result P (v source)))) := by
  rw [withPower,NatAssign.values_update_outside (DyadicFloor.allIds S) _
    (DyadicFloor.finish_valid S target ht) _ 144 (2^P) (power_outside S),DyadicFloor.finish_values]
  rfl

theorem initial_bank (S : Finset ℕ) (P : ℕ) (v : ℕ→Parts) (s : Store)
    (hs : Ready S v s) (hz : Clean s.val) (hp : RationalAccumulator.Word s.val 144 (2^P)) :
    NatAssign.Bank (allIds S) (withPower P (dataValues v)) s.val := by
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · simpa only [withPower,Function.update_self] using hp
  · have hne : i≠144 := fun h => power_outside S (h ▸ hi)
    simpa only [withPower,Function.update_of_ne hne] using DyadicFloor.initial_bank S v s hs hz i hi

theorem initial_width (S : Finset ℕ) (P : ℕ) (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v)
    (i : ℕ) (hi : i∈allIds S) : (withPower P (dataValues v) i).bits.length≤P+W+1 := by
  rcases Finset.mem_insert.mp hi with rfl | hi
  · simp only [withPower,Function.update_self,Nat.size_eq_bits_len,Nat.size_pow]
    omega
  · have hne : i≠144 := fun h => power_outside S (h ▸ hi)
    simp only [withPower,Function.update_of_ne hne]
    exact (DyadicFloor.initial_width S v W hw i hi).trans (by omega)

#print axioms prepare_values
#print axioms finish_values
end Maxwell.Continuum.RationalDataflow.DyadicFloor.StoredPower
