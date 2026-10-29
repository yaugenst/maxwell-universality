import Maxwell.Cost.DoublingInit.Loop

namespace Maxwell.Cost.DoublingInit
open Structured
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing

/-- Load the exact array length from its saved bank, run one traversal, and
physically clear the index word for the next traversal. -/
def passCode : Code := .seq (.call (WordTransfer.clone 96 94))
  (.seq loopCode (.call (TapeOps.clear 81)))

def passCost (layout : Layout) (n : ℕ) : ℕ := loopCost layout n + 21*n.bits.length+21

theorem pass_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (a b : Equiv.Perm (Fin n)) (clock : List Bool)
    (hw : 0 < layout.route.width) (hn : n ≤ 2^layout.route.width)
    (hfit : n.bits.length ≤ layout.route.width)
    (hclock : clock.length = layout.route.width) (hsep : layout.Separated n)
    (s : Store) (hnword : BankArray.Word s.val 96 n.bits) (h94 : Blank s.val 94)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory a b 0) :
    ∃ cost t, cost ≤ passCost layout n ∧ Executes input tape passCode cost s t ∧
      Config layout [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory a b n ∧
      LoopFrame s.val t.val ∧
      DoublingPass.MemoryFrame layout.route n s.val.memory t.val.memory := by
  obtain ⟨no,hnw⟩ := hnword
  obtain ⟨co,hcount⟩ := h94
  obtain ⟨loaded,ea,atapes,af⟩ := WordCall.clone 96 94 (by omega) input tape n.bits no co s hnw hcount
  have keep (i : ℕ) (hi : i ≠ 94) : loaded.val.tapes i = s.val.tapes i := by simp [atapes,hi]
  have aw : Workspace loaded.val := by
    rcases work with ⟨⟨⟨w0,w1,w2,w3,w5,w6,w8,w9⟩,w7,wp⟩,w37⟩
    refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩,?_⟩
    all_goals first
    | exact RationalAccumulator.blank_of_eq (keep _ (by omega)) (by assumption)
    | exact fun i hi => RationalAccumulator.blank_of_eq (keep i (by simp_all [DoublingPass.Private]; omega)) (wp i hi)
  have ac : Config layout [] clock loaded.val :=
    ⟨⟨BankArray.word_of_eq (keep 80 (by omega)) cfg.route.width,
     BankArray.word_of_eq (keep 81 (by omega)) cfg.route.index,
     BankArray.word_of_eq (keep 82 (by omega)) cfg.route.oldJump,
     BankArray.word_of_eq (keep 83 (by omega)) cfg.route.clock,
     BankArray.word_of_eq (keep 84 (by omega)) cfg.route.oldMinimum,
     BankArray.word_of_eq (keep 85 (by omega)) cfg.route.newJump,
     BankArray.word_of_eq (keep 86 (by omega)) cfg.route.newMinimum⟩,
     BankArray.word_of_eq (keep 98 (by omega)) cfg.inputA,
     BankArray.word_of_eq (keep 99 (by omega)) cfg.inputB⟩
  have ar : Represents layout loaded.val.memory a b 0 := by simpa only [af.2.2.1] using rep
  obtain ⟨pcost,p,index,hpcost,ep,hindex,hlen,pc,pw,p94,pr,pf,pm⟩ :=
    loop_executes input tape layout a b [] clock hw hn hfit hclock hsep rfl (by simp)
      co loaded (by simp [atapes]) ac aw ar
  obtain ⟨io,hiword⟩ := pc.route.index
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 81 input tape index io p hiword
  have tkeep (i : ℕ) (hi : i ≠ 81) : t.val.tapes i = p.val.tapes i := by simp [tt,hi]
  have tc : Config layout [] clock t.val :=
    ⟨⟨BankArray.word_of_eq (tkeep 80 (by omega)) pc.route.width,
     ⟨io+index.length,by simp [tt,BitTape.shifted,BitTape.blank]⟩,
     BankArray.word_of_eq (tkeep 82 (by omega)) pc.route.oldJump,
     BankArray.word_of_eq (tkeep 83 (by omega)) pc.route.clock,
     BankArray.word_of_eq (tkeep 84 (by omega)) pc.route.oldMinimum,
     BankArray.word_of_eq (tkeep 85 (by omega)) pc.route.newJump,
     BankArray.word_of_eq (tkeep 86 (by omega)) pc.route.newMinimum⟩,
     BankArray.word_of_eq (tkeep 98 (by omega)) pc.inputA,
     BankArray.word_of_eq (tkeep 99 (by omega)) pc.inputB⟩
  have tw : Workspace t.val := by
    rcases pw with ⟨⟨⟨w0,w1,w2,w3,w5,w6,w8,w9⟩,w7,wp⟩,w37⟩
    refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩,?_⟩
    all_goals first
    | exact RationalAccumulator.blank_of_eq (tkeep _ (by omega)) (by assumption)
    | exact fun i hi => RationalAccumulator.blank_of_eq (tkeep i (by simp_all [DoublingPass.Private]; omega)) (wp i hi)
  have frameA : LoopFrame s.val loaded.val :=
    ⟨af.2.1,af.2.2.2.1,af.2.2.2.2.1,fun i _ _ _ hi => keep i hi,
     fun i _ h24 h25 h26 h27 _ _ => af.2.2.2.2.2.2 i h24 h25 h26 h27⟩
  have frameT : LoopFrame p.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,fun i _ hi _ _ => tkeep i hi,
     fun i _ _ _ h26 h27 _ _ => tf.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨15*n.bits.length+17+(pcost+(6*index.length+4)),t,?_,ea.seq (ep.seq et),tc,tw,
    RationalAccumulator.blank_of_eq (tkeep 94 (by omega)) p94,?_,frameA.trans (pf.trans frameT),?_⟩
  · dsimp [passCost]; omega
  · simpa only [tf.2.2.1] using pr
  · simpa only [tf.2.2.1,af.2.2.1] using pm

end Maxwell.Cost.DoublingInit
