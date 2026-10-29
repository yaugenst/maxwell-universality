import Maxwell.Cost.DoublingPass.Round

namespace Maxwell.Cost.DoublingPass
open Structured
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing
open scoped BigOperators

def RunFrame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → ¬RoundPrivate i → i ≠ 97 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem RunFrame.refl (s : BitRAMState) : RunFrame s s := by simp [RunFrame]

theorem RunFrame.trans {s t u : BitRAMState} (h : RunFrame s t) (k : RunFrame t u) : RunFrame s u := by
  rcases h with ⟨hi,hr,ho,ht,hg⟩
  rcases k with ⟨ki,kr,ko,kt,kg⟩
  exact ⟨ki.trans hi,kr.trans hr,ko.trans ho,
    fun i hi hp h97 => (kt i hi hp h97).trans (ht i hi hp h97),
    fun i hi h24 h25 h26 h27 h28 h29 =>
      (kg i hi h24 h25 h26 h27 h28 h29).trans (hg i hi h24 h25 h26 h27 h28 h29)⟩

theorem RunFrame.of_round {s t : BitRAMState} (h : RoundFrame s t) : RunFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi hp _ => h.2.2.2.1 i hi hp,h.2.2.2.2⟩

theorem RunFrame.of_counter {s t : Store} (h : CountedShifted.Frame 97 s t) : RunFrame s.val t.val := by
  rcases h with ⟨_,hi,_,hr,ho,ht,hg⟩
  exact ⟨hi,hr,ho,fun i _ _ h97 => ht i h97,
    fun i hi h24 h25 _ _ _ h29 => hg i (by omega) h24 h25 h29⟩

private theorem config_of_tapes {layout : Layout} {index clock : List Bool}
    {s t : BitRAMState} (h : ∀ i, 80 ≤ i → i ≤ 86 → t.tapes i = s.tapes i)
    (c : Config layout index clock s) : Config layout index clock t := by
  exact ⟨BankArray.word_of_eq (h 80 (by omega) (by omega)) c.width,
    BankArray.word_of_eq (h 81 (by omega) (by omega)) c.index,
    BankArray.word_of_eq (h 82 (by omega) (by omega)) c.oldJump,
    BankArray.word_of_eq (h 83 (by omega) (by omega)) c.clock,
    BankArray.word_of_eq (h 84 (by omega) (by omega)) c.oldMinimum,
    BankArray.word_of_eq (h 85 (by omega) (by omega)) c.newJump,
    BankArray.word_of_eq (h 86 (by omega) (by omega)) c.newMinimum⟩

private theorem workspace_of_tapes {s t : BitRAMState}
    (h : ∀ i, i < 10 ∨ Private i → t.tapes i = s.tapes i)
    (w : Workspace s) : Workspace t := by
  rcases w with ⟨⟨h0,h1,h2,h3,h5,h6,h8,h9⟩,h7,hp⟩
  exact ⟨⟨RationalAccumulator.blank_of_eq (h 0 (by omega)) h0,
    RationalAccumulator.blank_of_eq (h 1 (by omega)) h1,
    RationalAccumulator.blank_of_eq (h 2 (by omega)) h2,
    RationalAccumulator.blank_of_eq (h 3 (by omega)) h3,
    RationalAccumulator.blank_of_eq (h 5 (by omega)) h5,
    RationalAccumulator.blank_of_eq (h 6 (by omega)) h6,
    RationalAccumulator.blank_of_eq (h 8 (by omega)) h8,
    RationalAccumulator.blank_of_eq (h 9 (by omega)) h9⟩,
    RationalAccumulator.blank_of_eq (h 7 (by omega)) h7,
    fun i hi => RationalAccumulator.blank_of_eq (h i (Or.inr hi)) (hp i hi)⟩

/-- The physical descriptors track the parity of the completed passes. -/
def RunInvariant {n : ℕ} (layout : Layout) (saved : State n) (rounds : ℕ)
    (clock : List Bool) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ rounds ∧
  Config (layoutAfter layout (rounds-remaining)) [] clock s.val ∧ Workspace s.val ∧
  Blank s.val 94 ∧ Blank s.val 95 ∧ BankArray.Word s.val 96 n.bits ∧
  (∃ output, Represents (layoutAfter layout (rounds-remaining)) s.val.memory
    (stateAfter saved (rounds-remaining)) output) ∧ RunFrame initial s.val ∧ MemoryFrame layout n initial.memory s.val.memory

private theorem invariant_stable {n : ℕ} (layout : Layout) (saved : State n)
    (rounds : ℕ) (clock : List Bool) (initial : BitRAMState)
    (r : ℕ) (s t : Store) (hf : CountedShifted.Frame 97 s t)
    (h : RunInvariant layout saved rounds clock initial r s) :
    RunInvariant layout saved rounds clock initial r t := by
  obtain ⟨hr,cfg,work,h94,h95,h96,⟨output,rep⟩,frame,hmemory⟩ := h
  refine ⟨hr,config_of_tapes (fun i hi hi' => hf.2.2.2.2.2.1 i (by omega)) cfg,
    workspace_of_tapes (fun i hi => hf.2.2.2.2.2.1 i (by rcases hi with hi | hi <;> simp_all [Private] <;> omega)) work,
    RationalAccumulator.blank_of_eq (hf.2.2.2.2.2.1 94 (by omega)) h94,
    RationalAccumulator.blank_of_eq (hf.2.2.2.2.2.1 95 (by omega)) h95,
    BankArray.word_of_eq (hf.2.2.2.2.2.1 96 (by omega)) h96,⟨output,?_⟩,
    frame.trans (RunFrame.of_counter hf),?_⟩
  · simpa only [hf.2.2.1] using rep
  · simpa only [hf.2.2.1] using hmemory

def roundsCode : Code := .seq (CountedShifted.code 97 roundCode) (.call (TapeOps.clear 97))
def roundsCost (layout : Layout) (n rounds : ℕ) : ℕ :=
  (rounds+1)*(13*rounds.bits.length+15)+rounds*roundCost layout n+6*rounds.bits.length+4

/-- Execute any number of pointer-doubling passes with one finite program.
All descriptors, both loop counters and every scratch word are handled by
actual instructions; no round-dependent host code is installed. -/
theorem rounds_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved output : State n) (clock : List Bool) (rounds : ℕ)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hclock : clock.length = layout.width) (hsep : layout.PingPong n)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 97 = BitTape.shifted rounds.bits countOrigin)
    (hnword : BankArray.Word s.val 96 n.bits) (h94 : Blank s.val 94) (h95 : Blank s.val 95)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory saved output) :
    ∃ cost t finalOutput, cost ≤ roundsCost layout n rounds ∧
      Executes input tape roundsCode cost s t ∧
      Config (layoutAfter layout rounds) [] clock t.val ∧ Workspace t.val ∧
      Blank t.val 94 ∧ Blank t.val 95 ∧ Blank t.val 97 ∧
      BankArray.Word t.val 96 n.bits ∧
      Represents (layoutAfter layout rounds) t.val.memory (stateAfter saved rounds) finalOutput ∧
      RunFrame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  let invariant := RunInvariant layout saved rounds clock s.val
  have bodyCorrect : ∀ r xs u, invariant (r+1) u →
      u.val.tapes 97 = BitTape.shifted xs countOrigin → addressValue xs = r →
      ∃ bodyCost t, Executes input tape roundCode bodyCost u t ∧
        invariant r t ∧ t.val.tapes 97 = BitTape.shifted xs countOrigin ∧ bodyCost ≤ roundCost layout n := by
    intro r xs u hu hcounter _
    obtain ⟨hr,cfgU,workU,u94,u95,u96,⟨out,repU⟩,frameU,hmemory⟩ := hu
    obtain ⟨cost,t,hcost,et,cfgT,workT,t94,t95,repT,frameT,tmemory⟩ := round_executes input tape
      (layoutAfter layout (rounds-(r+1))) (stateAfter saved (rounds-(r+1))) out clock
      (by simpa using hw) (by simpa using hn) (by simpa using hclock)
      (hsep.after (rounds-(r+1))).forward u u96 u94 u95 cfgU workU repU
    have hprefix : rounds-r = (rounds-(r+1))+1 := by omega
    refine ⟨cost,t,et,?_,?_,by simpa using hcost⟩
    · refine ⟨by omega,?_,workT,t94,t95,
        BankArray.word_of_eq (frameT.2.2.2.1 96 (by omega) (by simp [RoundPrivate,Private])) u96,
        ⟨stateAfter saved (rounds-(r+1)),?_⟩,frameU.trans (RunFrame.of_round frameT),
        hmemory.trans (by simpa only [memoryFrame_layoutAfter] using tmemory)⟩
      · simpa only [hprefix,layoutAfter] using cfgT
      · simpa only [hprefix,layoutAfter,stateAfter] using repT
    · exact (frameT.2.2.2.1 97 (by omega) (by simp [RoundPrivate,Private])).trans hcounter
  have initial : invariant rounds s := by
    simpa only [invariant,RunInvariant,Nat.sub_self,layoutAfter,stateAfter] using
      (show rounds ≤ rounds ∧ Config layout [] clock s.val ∧ Workspace s.val ∧
        Blank s.val 94 ∧ Blank s.val 95 ∧ BankArray.Word s.val 96 n.bits ∧
        (∃ out,Represents layout s.val.memory saved out) ∧ RunFrame s.val s.val ∧ MemoryFrame layout n s.val.memory s.val.memory from
       ⟨le_rfl,cfg,work,h94,h95,hnword,⟨output,rep⟩,RunFrame.refl _,MemoryFrame.refl _ _ _⟩)
  obtain ⟨lcost,l,finalCount,el,hinv,hltape,hlength,_,hlcost⟩ :=
    CountedShifted.executes 97 countOrigin roundCode input tape invariant (fun _ => roundCost layout n)
      (invariant_stable layout saved rounds clock s.val) bodyCorrect rounds rounds.bits s
      (RationalAccumulator.address_bits rounds) hcount initial
  obtain ⟨_,lc,lw,l94,l95,l96,⟨finalOutput,lr⟩,lf,hmemory⟩ := hinv
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 97 input tape finalCount countOrigin l hltape
  have keep (i : ℕ) (hi : i ≠ 97) : t.val.tapes i = l.val.tapes i := tf.2.2.2.2.2.1 i hi hi
  have tframe : RunFrame l.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,fun i _ _ hi => keep i hi,
     fun i _ _ _ h26 h27 _ _ => tf.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨_,t,finalOutput,?_,el.seq et,?_,
    workspace_of_tapes (fun i hi => keep i (by rcases hi with hi | hi <;> simp_all [Private] <;> omega)) lw,
    RationalAccumulator.blank_of_eq (keep 94 (by omega)) l94,
    RationalAccumulator.blank_of_eq (keep 95 (by omega)) l95,
    ⟨countOrigin+finalCount.length,by simp [tt]⟩,
    BankArray.word_of_eq (keep 96 (by omega)) l96,?_,lf.trans tframe,?_⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hlcost
    dsimp [roundsCost]; rw [hlength]; nlinarith
  · simpa only [Nat.sub_zero] using config_of_tapes (fun i hi hi' => keep i (by omega)) lc
  · simpa only [tf.2.2.1,Nat.sub_zero] using lr
  · simpa only [tf.2.2.1] using hmemory

theorem rounds_run {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved output : State n) (clock : List Bool) (rounds : ℕ)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hclock : clock.length = layout.width) (hsep : layout.PingPong n)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 97 = BitTape.shifted rounds.bits countOrigin)
    (hnword : BankArray.Word s.val 96 n.bits) (h94 : Blank s.val 94) (h95 : Blank s.val 95)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory saved output) :
    ∃ t : Store, ∃ finalOutput,
      (runPriced (roundsCode.compile.next input tape) (roundsCost layout n rounds+1) s.val).finished =
        some (t.place roundsCode.size) ∧
      (runPriced (roundsCode.compile.next input tape) (roundsCost layout n rounds+1) s.val).instructions ≤ roundsCost layout n rounds ∧
      Config (layoutAfter layout rounds) [] clock t.val ∧ Workspace t.val ∧
      Blank t.val 94 ∧ Blank t.val 95 ∧ Blank t.val 97 ∧ BankArray.Word t.val 96 n.bits ∧
      Represents (layoutAfter layout rounds) t.val.memory (stateAfter saved rounds) finalOutput ∧
      RunFrame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨cost,t,out,hcost,he,ht⟩ := rounds_executes input tape layout saved output clock rounds
    hw hn hclock hsep countOrigin s hcount hnword h94 h95 cfg work rep
  have hr := he.compiled_run (roundsCost layout n rounds+1) (by omega)
  exact ⟨t,out,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.DoublingPass
