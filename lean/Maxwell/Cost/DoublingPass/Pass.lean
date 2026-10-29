import Maxwell.Cost.DoublingPass.RoundsEncoding

namespace Maxwell.Cost.DoublingPass
open Structured
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing

/-- Load the exact array length from its saved bank, run one traversal, and
physically clear the index word for the next traversal. -/
def passCode : Code := .seq (.call (WordTransfer.clone 96 94))
  (.seq loopCode (.call (TapeOps.clear 81)))

def passCost (layout : Layout) (n : ℕ) : ℕ := loopCost layout n + 21*n.bits.length+21

@[simp] theorem passCost_flip (layout : Layout) (n : ℕ) : passCost layout.flip n = passCost layout n := by
  simp only [passCost,loopCost_flip]

@[simp] theorem passCost_layoutAfter (layout : Layout) (k n : ℕ) :
    passCost (layoutAfter layout k) n = passCost layout n := by simp only [passCost,loopCost_layoutAfter]

theorem pass_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved output : State n) (clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hclock : clock.length = layout.width) (hsep : layout.Separated n)
    (s : Store) (hnword : BankArray.Word s.val 96 n.bits) (h94 : Blank s.val 94)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ passCost layout n ∧ Executes input tape passCode cost s t ∧
      Config layout [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory saved (Doubling.step (Equiv.refl (Fin n)) saved) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨no,hnw⟩ := hnword
  obtain ⟨co,hcount⟩ := h94
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 96 94 (by omega) input tape n.bits no co s hnw hcount
  have keep (i : ℕ) (hi : i ≠ 94) : a.val.tapes i = s.val.tapes i := by simp [atapes,hi]
  have aw : Workspace a.val := by
    rcases work with ⟨⟨w0,w1,w2,w3,w5,w6,w8,w9⟩,w7,wp⟩
    refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
    all_goals first
    | exact RationalAccumulator.blank_of_eq (keep _ (by omega)) (by assumption)
    | exact fun i hi => RationalAccumulator.blank_of_eq (keep i (by simp_all [Private]; omega)) (wp i hi)
  have ac : Config layout [] clock a.val :=
    ⟨BankArray.word_of_eq (keep 80 (by omega)) cfg.width,
     BankArray.word_of_eq (keep 81 (by omega)) cfg.index,
     BankArray.word_of_eq (keep 82 (by omega)) cfg.oldJump,
     BankArray.word_of_eq (keep 83 (by omega)) cfg.clock,
     BankArray.word_of_eq (keep 84 (by omega)) cfg.oldMinimum,
     BankArray.word_of_eq (keep 85 (by omega)) cfg.newJump,
     BankArray.word_of_eq (keep 86 (by omega)) cfg.newMinimum⟩
  have ar : Represents layout a.val.memory saved output := by simpa only [af.2.2.1] using rep
  obtain ⟨pcost,p,index,hpcost,ep,hindex,hlen,pc,pw,p94,pr,pf,pmemory⟩ :=
    loop_executes input tape layout saved output [] clock hw hn hclock hsep rfl (by simp)
      co a (by simp [atapes]) ac aw ar
  obtain ⟨io,hiword⟩ := pc.index
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 81 input tape index io p hiword
  have tkeep (i : ℕ) (hi : i ≠ 81) : t.val.tapes i = p.val.tapes i := by simp [tt,hi]
  have tc : Config layout [] clock t.val :=
    ⟨BankArray.word_of_eq (tkeep 80 (by omega)) pc.width,
     ⟨io+index.length,by simp [tt,BitTape.shifted,BitTape.blank]⟩,
     BankArray.word_of_eq (tkeep 82 (by omega)) pc.oldJump,
     BankArray.word_of_eq (tkeep 83 (by omega)) pc.clock,
     BankArray.word_of_eq (tkeep 84 (by omega)) pc.oldMinimum,
     BankArray.word_of_eq (tkeep 85 (by omega)) pc.newJump,
     BankArray.word_of_eq (tkeep 86 (by omega)) pc.newMinimum⟩
  have tw : Workspace t.val := by
    rcases pw with ⟨⟨w0,w1,w2,w3,w5,w6,w8,w9⟩,w7,wp⟩
    refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
    all_goals first
    | exact RationalAccumulator.blank_of_eq (tkeep _ (by omega)) (by assumption)
    | exact fun i hi => RationalAccumulator.blank_of_eq (tkeep i (by simp_all [Private]; omega)) (wp i hi)
  have frameA : LoopFrame s.val a.val :=
    ⟨af.2.1,af.2.2.2.1,af.2.2.2.2.1,fun i _ _ _ hi => keep i hi,
     fun i _ h24 h25 h26 h27 _ _ => af.2.2.2.2.2.2 i h24 h25 h26 h27⟩
  have frameT : LoopFrame p.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,fun i _ hi _ _ => tkeep i hi,
     fun i _ _ _ h26 h27 _ _ => tf.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨15*n.bits.length+17+(pcost+(6*index.length+4)),t,?_,ea.seq (ep.seq et),tc,tw,
    RationalAccumulator.blank_of_eq (tkeep 94 (by omega)) p94,?_,frameA.trans (pf.trans frameT),?_⟩
  · dsimp [passCost]; omega
  · simpa only [tf.2.2.1] using pr
  · simpa only [tf.2.2.1,af.2.2.1] using pmemory

end Maxwell.Cost.DoublingPass
