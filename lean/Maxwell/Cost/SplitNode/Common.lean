import Maxwell.Cost.BinarySplit
import Maxwell.Cost.ChildPermutation.Complexity
import Maxwell.Cost.ChildPermutation.Prepare

namespace Maxwell.Cost.SplitNode

structure Layout where
  split : BinarySplit.Layout
  childBases : Fin 4 → ℕ

def Layout.child (layout : Layout) (n : ℕ) : ChildPermutation.Layout :=
  ⟨layout.split.route.width,layout.split.forward,(BinarySplit.finalLayout layout.split n).newJump,
    layout.childBases 0,layout.childBases 1,layout.childBases 2,layout.childBases 3⟩

@[simp] theorem Layout.child_outputBase (layout : Layout) (n : ℕ) (i : Fin 4) :
    (layout.child n).outputBase i=layout.childBases i := by fin_cases i <;> rfl

def Private (i : ℕ) : Prop := DoublingPass.RoundPrivate i ∨ i=37 ∨ i=97 ∨ ChildPermutation.MetadataPrivate i ∨ i=126

def Frame (s t : BitRAMState) : Prop :=
  t.inputHead=s.inputHead ∧ t.randomCursor=s.randomCursor ∧ t.output=s.output ∧
  (∀ i, i=4 ∨ 10 ≤ i → ¬Private i → t.tapes i=s.tapes i) ∧
  (∀ i, 15 ≤ i → i<24 ∨ 31 < i → t.registers i=s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (j : Frame t u) : Frame s u :=
  ⟨j.1.trans h.1,j.2.1.trans h.2.1,j.2.2.1.trans h.2.2.1,
   fun i hi hp => (j.2.2.2.1 i hi hp).trans (h.2.2.2.1 i hi hp),
   fun i hi hr => (j.2.2.2.2 i hi hr).trans (h.2.2.2.2 i hi hr)⟩

theorem Frame.of_split {s t : BitRAMState} (h : CycleSplit.Frame s t) : Frame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi hp => h.2.2.2.1 i hi (fun he => hp (Or.inl he))
    (fun he => hp (Or.inr (Or.inl he))) (fun he => hp (Or.inr (Or.inr (Or.inl he)))),h.2.2.2.2⟩

theorem Frame.of_prepare {s t : BitRAMState} (h : ChildPermutation.MetadataFrame s t) : Frame s t :=
  ⟨h.1,h.2.2.1,h.2.2.2.1,fun i _ hp => h.2.2.2.2.1 i
    (fun he => hp (Or.inr (Or.inr (Or.inr (Or.inl he))))),h.2.2.2.2.2⟩

theorem Frame.of_child {s t : BitRAMState} (h : ChildPermutation.LoopFrame s t) : Frame s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_,h.2.2.2.2⟩
  intro i hi hp
  apply h.2.2.2.1 i hi
  · intro he; exact hp (Or.inl (by simp [DoublingPass.RoundPrivate,he]))
  · intro he; exact hp (Or.inr (Or.inr (Or.inr (Or.inr he))))
  · intro he
    rcases he with he | he
    · exact hp (Or.inr (Or.inl he))
    · exact hp (Or.inl (by simp only [DoublingPass.RoundPrivate]; tauto))

def MemoryFrame (layout : Layout) (k : ℕ) (before after : ℕ → Bool) : Prop :=
  ∀ p, BinarySplit.Outside layout.split (2*(2^k)) p →
    (∀ i, p<(layout.child (2*(2^k))).outputBase i ∨
      (layout.child (2*(2^k))).outputBase i+2^k*(layout.child (2*(2^k))).childWidth≤p) → after p=before p

end Maxwell.Cost.SplitNode
