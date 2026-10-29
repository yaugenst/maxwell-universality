import Maxwell.Cost.ChildPermutation.Common

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing.Coloring.NumericSplit

def selectPairCode : Code := .seq (.atom (.readTape 88 30 31)) selectCode

/-- The branch reads the stored color bit itself; both returned words are
exact labels of the logical child permutations. -/
theorem select_pair (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : Data k) (index clock childClock : List Bool) (i : Fin (2^k))
    (hw : layout.parentWidth=k+2) (s : Store) (cfg : Config layout index clock childClock s.val)
    (h88 : Word s.val 88 [data.colors.get (lower i)])
    (h89 : Word s.val 89 (IncidenceEncoding.word layout.parentWidth (data.target (lower i)).val))
    (h91 : Word s.val 91 (IncidenceEncoding.word layout.parentWidth (data.target (upper i)).val))
    (h92 : Blank s.val 92) (ss : BankArray.Scratch s.val) (h7 : Blank s.val 7) :
    ∃ cost t, cost≤100*(k+3)+3 ∧ Executes input tape selectPairCode cost s t ∧
      Word t.val 89 (IncidenceEncoding.word layout.childWidth (data.left i).val) ∧
      Word t.val 91 (IncidenceEncoding.word layout.childWidth (data.right i).val) ∧
      Blank t.val 92 ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory=s.val.memory ∧ Config layout index clock childClock t.val ∧
      (∀ j, j≠89 → j≠91 → j≠92 → t.val.tapes j=s.val.tapes j) ∧ Frame s.val t.val := by
  let color := data.colors.get (lower i)
  obtain ⟨origin,ho⟩ := h88
  have hr : (s.val.tapes 88).read=some color := by simp [ho,BitTape.read,BitTape.shifted,color]
  let raw : BitRAMState := {s.val with pc:=1,registers:=Function.update (Function.update s.val.registers 30 color) 31 true}
  let a : Store := Store.ofState raw
  have ea : Executes input tape (.atom (.readTape 88 30 31)) 3 s a := by
    apply Executes.atom (extra:=1)
    · simp [BitRAM.next,s.property,hr,raw,BitRAMState.setRegister]
    · rfl
  have fa : Frame s.val a.val := by
    refine ⟨rfl,rfl,rfl,fun _ _ _ => rfl,?_⟩
    intro j _ hj
    simp only [a,Store.ofState,raw,Function.update_apply]
    have h30 : j≠30 := by omega
    have h31 : j≠31 := by omega
    simp [h30,h31]
  obtain ⟨cost,t,hcost,et,tl,tr,t92,tf⟩ := select_executes k (data.target (lower i)) (data.target (upper i)) color
    input tape a (by simp [a,Store.ofState,raw])
    (by simpa only [hw] using (BankArray.word_of_eq (show a.val.tapes 89=s.val.tapes 89 from rfl) h89))
    (by simpa only [hw] using (BankArray.word_of_eq (show a.val.tapes 91=s.val.tapes 91 from rfl) h91)) h92
  have hl : (if color then data.target (upper i) else data.target (lower i)).val%2^k=(data.left i).val := by
    rw [data.left_law]
    dsimp [color,selected]
    by_cases he : data.colors.get (lower i)=true
    · simp [he]
    · have hf : data.colors.get (lower i)=false := Bool.eq_false_iff.mpr he
      simp [hf]
  have hu : (if color then data.target (lower i) else data.target (upper i)).val%2^k=(data.right i).val := by
    rw [data.right_law]
    dsimp [color,selected]
    by_cases he : data.colors.get (lower i)=true
    · simp [he]
    · have hf : data.colors.get (lower i)=false := Bool.eq_false_iff.mpr he
      simp [hf]
  have hcw : layout.childWidth=k+1 := by simp [Layout.childWidth,hw]
  refine ⟨3+cost,t,by omega,ea.seq et,?_,?_,t92,
    scratch_of_tapes (fun j hj => tf.2.2.2.2.2.1 j (by omega) (by omega) (by omega)) ss,
    RationalAccumulator.blank_of_eq (tf.2.2.2.2.2.1 7 (by omega) (by omega) (by omega)) h7,
    tf.2.2.1,cfg.of_frame (fa.trans (Frame.of_select tf)),tf.2.2.2.2.2.1,fa.trans (Frame.of_select tf)⟩
  · simpa only [hl,hcw] using tl
  · simpa only [hu,hcw] using tr

end Maxwell.Cost.ChildPermutation
