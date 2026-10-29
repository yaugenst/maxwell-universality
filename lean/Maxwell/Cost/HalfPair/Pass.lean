import Maxwell.Cost.HalfPair.Loop

namespace Maxwell.Cost.HalfPair
open Structured DoublingInit
open RationalAccumulator (Blank)

/-- Load the saved length, execute the fixed traversal, and clear its index. -/
def passCode : Code := .seq (.call (WordTransfer.clone 96 94))
  (.seq HalfPair.loopCode (.call (TapeOps.clear 81)))

def passCost (layout : Layout) (n : ℕ) : ℕ := loopCost layout n + 21*n.bits.length+21

theorem pass_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (output : Vector (List Bool) (2*(2^k))) (clock : List Bool)
    (hwidth : layout.route.width = k+2) (hclock : clock.length = layout.route.width)
    (s : Store) (hnword : BankArray.Word s.val 96 (2*(2^k)).bits) (h94 : Blank s.val 94)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory output) :
    ∃ cost t, cost ≤ passCost layout (2*(2^k)) ∧ Executes input tape passCode cost s t ∧
      Config layout [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory (array k) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨no,hnw⟩ := hnword
  obtain ⟨co,hcount⟩ := h94
  obtain ⟨loaded,ea,atapes,af⟩ := WordCall.clone 96 94 (by omega) input tape (2*(2^k)).bits no co s hnw hcount
  have keep (i : ℕ) (hi : i ≠ 94) : loaded.val.tapes i = s.val.tapes i := by simp [atapes,hi]
  have aw : Workspace loaded.val := workspace_of_tapes (fun i hi => keep i
    (by rcases hi with hi | hi <;> simp_all [Private,DoublingPass.Private] <;> omega)) work
  have ac : Config layout [] clock loaded.val := config_of_tapes (fun i hi => keep i (by omega)) cfg
  have ar : Represents layout loaded.val.memory output := by simpa only [af.2.2.1] using rep
  obtain ⟨pcost,p,index,hpcost,ep,hindex,hlen,pc,pw,p94,pr,pf,pm⟩ :=
    loop_executes k input tape layout output [] clock hwidth hclock rfl (by simp)
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
  have tw : Workspace t.val := workspace_of_tapes (fun i hi => tkeep i
    (by rcases hi with hi | hi <;> simp_all [Private,DoublingPass.Private] <;> omega)) pw
  have frameA : LoopFrame s.val loaded.val :=
    ⟨af.2.1,af.2.2.2.1,af.2.2.2.2.1,fun i _ _ _ hi => keep i hi,
      fun i _ h24 h25 h26 h27 _ _ => af.2.2.2.2.2.2 i h24 h25 h26 h27⟩
  have frameT : LoopFrame p.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,fun i _ hi _ _ => tkeep i hi,
      fun i _ _ _ h26 h27 _ _ => tf.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨15*(2*(2^k)).bits.length+17+(pcost+(6*index.length+4)),t,?_,?_,tc,tw,
    RationalAccumulator.blank_of_eq (tkeep 94 (by omega)) p94,?_,frameA.trans (pf.trans frameT),?_⟩
  · dsimp [passCost]; omega
  · simpa only [passCode] using ea.seq (ep.seq et)
  · simpa only [tf.2.2.1] using pr
  · simpa only [tf.2.2.1,af.2.2.1] using pm

/-- The old output memory is arbitrary; its snapshot is only a proof witness,
never an input assembled by the host. -/
theorem prepares (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (clock : List Bool)
    (hwidth : layout.route.width = k+2) (hclock : clock.length = layout.route.width)
    (s : Store) (hnword : BankArray.Word s.val 96 (2*(2^k)).bits) (h94 : Blank s.val 94)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val) :
    ∃ cost t, cost ≤ passCost layout (2*(2^k)) ∧ Executes input tape passCode cost s t ∧
      Config layout [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory (array k) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory :=
  pass_executes k input tape layout
    (BitArray.snapshot s.val.memory layout.route.newMinimum layout.route.width (2*(2^k)))
    clock hwidth hclock s hnword h94 cfg work (BitArray.snapshot_represents _ _ _ _)

theorem run (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (clock : List Bool)
    (hwidth : layout.route.width = k+2) (hclock : clock.length = layout.route.width)
    (s : Store) (hnword : BankArray.Word s.val 96 (2*(2^k)).bits) (h94 : Blank s.val 94)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val) :
    ∃ t : Store,
      (runPriced (passCode.compile.next input tape) (passCost layout (2*(2^k))+1) s.val).finished =
        some (t.place passCode.size) ∧
      (runPriced (passCode.compile.next input tape) (passCost layout (2*(2^k))+1) s.val).instructions ≤
        passCost layout (2*(2^k)) ∧
      Config layout [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory (array k) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,he,ht⟩ := prepares k input tape layout clock hwidth hclock s hnword h94 cfg work
  have hr := he.compiled_run (passCost layout (2*(2^k))+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.HalfPair
