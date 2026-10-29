import Maxwell.Cost.ChildPermutation.Cleanup

namespace Maxwell.Cost.ColorAssemble
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open ChildPermutation (Workspace Frame scratch_of_tapes)

def cleanupCode : Code := ChildPermutation.cleanupCode

theorem cleanup_executes (input : List Bool) (tape : ℕ → Bool) (color label index : List Bool)
    (s : Store) (h88 : Word s.val 88 color) (h90 : Word s.val 90 label) (h37 : Word s.val 37 index)
    (h89 : Blank s.val 89) (h91 : Blank s.val 91) (h92 : Blank s.val 92)
    (ss : BankArray.Scratch s.val) (h7 : Blank s.val 7) :
    ∃ t, Executes input tape cleanupCode (6*(color.length+label.length+index.length)+24) s t ∧
      Workspace t.val ∧ t.val.memory=s.val.memory ∧ Frame s.val t.val := by
  have empty {j : ℕ} (h : Blank s.val j) : Word s.val j [] := by
    obtain ⟨o,ho⟩ := h
    exact ⟨o,by simpa [BitTape.shifted,BitTape.blank] using ho⟩
  obtain ⟨p,ep,pw,pm,pf⟩ := DoublingPass.cleanup_executes input tape color [] label [] [] s
    h88 (empty h89) h90 (empty h91) (empty h92) ss h7
  obtain ⟨o,ho⟩ := h37
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 37 input tape index o p
    ((pf.2.2.2.1 37 (by omega) (by simp [DoublingPass.Private])).trans ho)
  have keep (j : ℕ) (hj : j≠37) := tf.2.2.2.2.2.1 j hj hj
  have firstFrame : Frame s.val p.val :=
    ⟨pf.1,pf.2.1,pf.2.2.1,fun j hj hp => pf.2.2.2.1 j hj (fun he => hp (Or.inr he)),
      fun j hj hr => pf.2.2.2.2 j hj (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  refine ⟨t,?_,⟨⟨scratch_of_tapes (fun j hj => keep j (by omega)) pw.1,
    RationalAccumulator.blank_of_eq (keep 7 (by omega)) pw.2.1,?_⟩,
    ⟨o+index.length,by simp [tt]⟩⟩,tf.2.2.1.trans pm,
    firstFrame.trans (Frame.of_transfer (Or.inl rfl) (Or.inl rfl) (WordTransfer.frame_of_copy tf))⟩
  · convert ep.seq et using 1 <;> first | rfl | simp; omega
  · intro j hj
    exact RationalAccumulator.blank_of_eq (keep j (by dsimp [DoublingPass.Private] at hj; omega)) (pw.2.2 j hj)

end Maxwell.Cost.ColorAssemble
