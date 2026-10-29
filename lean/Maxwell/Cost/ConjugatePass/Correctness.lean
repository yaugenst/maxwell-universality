import Maxwell.Cost.ConjugatePass.Pass
import Maxwell.Cost.DoublingInit.Encoding

namespace Maxwell.Cost.ConjugatePass
open Structured DoublingPass
open RationalAccumulator (Blank)

def permutationTables {n : ℕ} (target pairing : Equiv.Perm (Fin n)) : Tables n :=
  ⟨Vector.ofFn target,Vector.ofFn pairing,Vector.ofFn target.symm⟩

@[simp] theorem composed_permutations {n : ℕ} (target pairing : Equiv.Perm (Fin n)) :
    composed (permutationTables target pairing) = Vector.ofFn (target.symm * pairing * target) := by
  apply Vector.ext
  intro i hi
  simp [composed,value,permutationTables,Vector.get,Fin.cast]

/-- Materialize the conjugated pairing from arbitrary destination memory.
All three source tables remain intact, and the index and private counter
are physically cleared for the following split. -/
theorem prepares {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (target pairing : Equiv.Perm (Fin n)) (clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hclock : clock.length = layout.width) (hsep : Separated layout n)
    (s : Store) (hnword : BankArray.Word s.val 96 n.bits) (h94 : Blank s.val 94)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (hf : BitArray.Represents s.val.memory layout.oldJump layout.width (words layout.width (Vector.ofFn target)))
    (ha : BitArray.Represents s.val.memory layout.oldMinimum layout.width (words layout.width (Vector.ofFn pairing)))
    (hb : BitArray.Represents s.val.memory layout.newJump layout.width (words layout.width (Vector.ofFn target.symm))) :
    ∃ cost t, cost ≤ passCost layout n ∧ Executes input tape passCode cost s t ∧
      Config layout [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      BitArray.Represents t.val.memory layout.oldJump layout.width (words layout.width (Vector.ofFn target)) ∧
      BitArray.Represents t.val.memory layout.oldMinimum layout.width (words layout.width (Vector.ofFn pairing)) ∧
      BitArray.Represents t.val.memory layout.newJump layout.width (words layout.width (Vector.ofFn target.symm)) ∧
      BitArray.Represents t.val.memory layout.newMinimum layout.width
        (words layout.width (Vector.ofFn (target.symm * pairing * target))) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,he,tc,tw,t94,rep,frame,memoryFrame⟩ := pass_executes input tape layout
    (permutationTables target pairing) (BitArray.snapshot s.val.memory layout.newMinimum layout.width n)
    clock hw hn hclock hsep s hnword h94 cfg work
    ⟨hf,ha,hb,BitArray.snapshot_represents _ _ _ _⟩
  exact ⟨cost,t,hcost,he,tc,tw,t94,rep.forward,rep.pairing,rep.backward,
    by simpa only [composed_permutations] using rep.output,frame,memoryFrame⟩

theorem run {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (target pairing : Equiv.Perm (Fin n)) (clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hclock : clock.length = layout.width) (hsep : Separated layout n)
    (s : Store) (hnword : BankArray.Word s.val 96 n.bits) (h94 : Blank s.val 94)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (hf : BitArray.Represents s.val.memory layout.oldJump layout.width (words layout.width (Vector.ofFn target)))
    (ha : BitArray.Represents s.val.memory layout.oldMinimum layout.width (words layout.width (Vector.ofFn pairing)))
    (hb : BitArray.Represents s.val.memory layout.newJump layout.width (words layout.width (Vector.ofFn target.symm))) :
    ∃ t : Store,
      (runPriced (passCode.compile.next input tape) (passCost layout n+1) s.val).finished = some (t.place passCode.size) ∧
      (runPriced (passCode.compile.next input tape) (passCost layout n+1) s.val).instructions ≤ passCost layout n ∧
      Config layout [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      BitArray.Represents t.val.memory layout.oldJump layout.width (words layout.width (Vector.ofFn target)) ∧
      BitArray.Represents t.val.memory layout.oldMinimum layout.width (words layout.width (Vector.ofFn pairing)) ∧
      BitArray.Represents t.val.memory layout.newJump layout.width (words layout.width (Vector.ofFn target.symm)) ∧
      BitArray.Represents t.val.memory layout.newMinimum layout.width
        (words layout.width (Vector.ofFn (target.symm * pairing * target))) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,he,ht⟩ := prepares input tape layout target pairing clock hw hn hclock hsep s hnword h94 cfg work hf ha hb
  have hr := he.compiled_run (passCost layout n+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.ConjugatePass
