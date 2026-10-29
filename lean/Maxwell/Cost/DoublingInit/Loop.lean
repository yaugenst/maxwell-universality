import Maxwell.Cost.DoublingInit.Step
import Maxwell.Cost.BankArray.Increment
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.DoublingInit
open Structured
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing
open scoped BigOperators

def LoopFrame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → i ≠ 81 → ¬Private i → i ≠ 94 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem LoopFrame.refl (s : BitRAMState) : LoopFrame s s := by simp [LoopFrame]

theorem LoopFrame.trans {s t u : BitRAMState} (h : LoopFrame s t) (k : LoopFrame t u) : LoopFrame s u := by
  rcases h with ⟨hi,hr,ho,ht,hg⟩
  rcases k with ⟨ki,kr,ko,kt,kg⟩
  exact ⟨ki.trans hi,kr.trans hr,ko.trans ho,
    fun i hi h81 hp h94 => (kt i hi h81 hp h94).trans (ht i hi h81 hp h94),
    fun i hi h24 h25 h26 h27 h28 h29 =>
      (kg i hi h24 h25 h26 h27 h28 h29).trans (hg i hi h24 h25 h26 h27 h28 h29)⟩

theorem LoopFrame.of_step {s t : BitRAMState} (h : Frame s t) : LoopFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi _ hp _ => h.2.2.2.1 i hi hp,h.2.2.2.2⟩

theorem LoopFrame.of_increment {s t : BitRAMState} (h : BankArray.FrameExcept 81 s t) : LoopFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi h81 _ _ => h.2.2.2.1 i hi h81,h.2.2.2.2⟩

theorem LoopFrame.of_counter {s t : Store} (h : CountedShifted.Frame 94 s t) : LoopFrame s.val t.val := by
  rcases h with ⟨_,hi,_,hr,ho,ht,hg⟩
  exact ⟨hi,hr,ho,fun i _ _ _ h94 => ht i h94,
    fun i hi h24 h25 _ _ _ h29 => hg i (by omega) h24 h25 h29⟩

theorem config_of_tapes {layout : Layout} {index clock : List Bool}
    {s t : BitRAMState} (h : ∀ i, (80 ≤ i ∧ i ≤ 86) ∨ i = 98 ∨ i = 99 → t.tapes i=s.tapes i)
    (c : Config layout index clock s) : Config layout index clock t := by
  exact ⟨⟨BankArray.word_of_eq (h 80 (by omega)) c.route.width,
    BankArray.word_of_eq (h 81 (by omega)) c.route.index,
    BankArray.word_of_eq (h 82 (by omega)) c.route.oldJump,
    BankArray.word_of_eq (h 83 (by omega)) c.route.clock,
    BankArray.word_of_eq (h 84 (by omega)) c.route.oldMinimum,
    BankArray.word_of_eq (h 85 (by omega)) c.route.newJump,
    BankArray.word_of_eq (h 86 (by omega)) c.route.newMinimum⟩,
    BankArray.word_of_eq (h 98 (by omega)) c.inputA,
    BankArray.word_of_eq (h 99 (by omega)) c.inputB⟩

theorem workspace_of_tapes {s t : BitRAMState}
    (h : ∀ i, i < 10 ∨ Private i → t.tapes i = s.tapes i)
    (w : Workspace s) : Workspace t := by
  rcases w with ⟨⟨⟨h0,h1,h2,h3,h5,h6,h8,h9⟩,h7,hp⟩,h37⟩
  exact ⟨⟨⟨RationalAccumulator.blank_of_eq (h 0 (by omega)) h0,
    RationalAccumulator.blank_of_eq (h 1 (by omega)) h1,
    RationalAccumulator.blank_of_eq (h 2 (by omega)) h2,
    RationalAccumulator.blank_of_eq (h 3 (by omega)) h3,
    RationalAccumulator.blank_of_eq (h 5 (by omega)) h5,
    RationalAccumulator.blank_of_eq (h 6 (by omega)) h6,
    RationalAccumulator.blank_of_eq (h 8 (by omega)) h8,
    RationalAccumulator.blank_of_eq (h 9 (by omega)) h9⟩,
    RationalAccumulator.blank_of_eq (h 7 (by omega)) h7,
    fun i hi => RationalAccumulator.blank_of_eq (h i (Or.inr (Or.inr hi))) (hp i hi)⟩,
    RationalAccumulator.blank_of_eq (h 37 (Or.inr (Or.inl rfl))) h37⟩

theorem config_increment {layout : Layout} {index clock : List Bool}
    {s t : BitRAMState} (h : ∀ i, i≠81 → t.tapes i=s.tapes i)
    (c : Config layout index clock s) (hi : BankArray.Word t 81 (Increment.bits index)) :
    Config layout (Increment.bits index) clock t := by
  exact ⟨⟨BankArray.word_of_eq (h 80 (by omega)) c.route.width,
    hi,
    BankArray.word_of_eq (h 82 (by omega)) c.route.oldJump,
    BankArray.word_of_eq (h 83 (by omega)) c.route.clock,
    BankArray.word_of_eq (h 84 (by omega)) c.route.oldMinimum,
    BankArray.word_of_eq (h 85 (by omega)) c.route.newJump,
    BankArray.word_of_eq (h 86 (by omega)) c.route.newMinimum⟩,
    BankArray.word_of_eq (h 98 (by omega)) c.inputA,
    BankArray.word_of_eq (h 99 (by omega)) c.inputB⟩

/-- The four output buffers are initialized one slot at a time. -/
def LoopInvariant {n : ℕ} (layout : Layout) (a b : Equiv.Perm (Fin n))
    (clock : List Bool) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ n ∧ ∃ index : List Bool,
    addressValue index = n-remaining ∧ index.length ≤ n.bits.length ∧ Config layout index clock s.val ∧
    Workspace s.val ∧ Represents layout s.val.memory a b (n-remaining) ∧ LoopFrame initial s.val ∧
    DoublingPass.MemoryFrame layout.route n initial.memory s.val.memory

private theorem invariant_stable {n : ℕ} (layout : Layout)
    (a b : Equiv.Perm (Fin n)) (clock : List Bool) (initial : BitRAMState)
    (r : ℕ) (s t : Store) (hf : CountedShifted.Frame 94 s t)
    (h : LoopInvariant layout a b clock initial r s) :
    LoopInvariant layout a b clock initial r t := by
  obtain ⟨hr,index,hindex,hlen,hconfig,hwork,hrep,hframe,hmem⟩ := h
  refine ⟨hr,index,hindex,hlen,config_of_tapes (fun i hi => hf.2.2.2.2.2.1 i (by omega)) hconfig,
    workspace_of_tapes (fun i hi => hf.2.2.2.2.2.1 i (by rcases hi with hi | hi <;> simp_all [Private,DoublingPass.Private] <;> omega)) hwork,?_,
    hframe.trans (LoopFrame.of_counter hf),?_⟩
  · simpa only [hf.2.2.1] using hrep
  · simpa only [hf.2.2.1] using hmem

def loopBody : Code := .seq stepCode (BankArray.incrementCode 81)
def loopCode : Code := .seq (CountedShifted.code 94 loopBody) (.call (TapeOps.clear 94))

def loopCost (layout : Layout) (n : ℕ) : ℕ :=
  (n+1)*(13*n.bits.length+15) + n*(300000*(budget layout n.bits+1)^2) + 6*n.bits.length+4

/-- The actual finite traversal constructs the composed permutation and
all three identity arrays, with no precondition on their previous contents. -/
theorem loop_executes {n : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (layout : Layout) (a b : Equiv.Perm (Fin n)) (index clock : List Bool)
    (hw : 0 < layout.route.width) (hn : n ≤ 2^layout.route.width)
    (hfit : n.bits.length ≤ layout.route.width)
    (hclock : clock.length = layout.route.width) (hsep : layout.Separated n)
    (hindex : addressValue index = 0) (hlen : index.length ≤ n.bits.length)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 94 = BitTape.shifted n.bits countOrigin)
    (hconfig : Config layout index clock s.val) (hwork : Workspace s.val)
    (hrep : Represents layout s.val.memory a b 0) :
    ∃ cost, ∃ t : Store, ∃ finalIndex : List Bool,
      cost ≤ loopCost layout n ∧ Executes input randomTape loopCode cost s t ∧
      addressValue finalIndex = n ∧ finalIndex.length ≤ n.bits.length ∧
      Config layout finalIndex clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory a b n ∧
      LoopFrame s.val t.val ∧
      DoublingPass.MemoryFrame layout.route n s.val.memory t.val.memory := by
  let invariant := LoopInvariant layout a b clock s.val
  let bound := 300000*(budget layout n.bits+1)^2
  have hnPower : n < 2^n.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self n
  have bodyCorrect : ∀ r xs u, invariant (r+1) u →
      u.val.tapes 94 = BitTape.shifted xs countOrigin → addressValue xs = r →
      ∃ bodyCost t, Executes input randomTape loopBody bodyCost u t ∧
        invariant r t ∧ t.val.tapes 94 = BitTape.shifted xs countOrigin ∧ bodyCost ≤ bound := by
    intro r xs u hu hcounter _
    obtain ⟨hr,idx,hidx,hlen',hcfg,hworkspace,hrepresented,hframe,hmem⟩ := hu
    have hlt : n-(r+1) < n := by omega
    let j : Fin n := ⟨n-(r+1),hlt⟩
    obtain ⟨scost,middle,hscost,es,hac,haw,har,haf,ham⟩ := step_executes input randomTape layout a b
      j idx clock hw hn (hlen'.trans hfit) hidx hclock hsep
      u hcfg hworkspace hrepresented
    obtain ⟨icost,t,hicost,ei,hti,_,htm,_,htapes,htf⟩ := BankArray.increment_bank 81 (by omega)
      input randomTape idx middle hac.route.index haw.1.1
    have hnew : addressValue (Increment.bits idx) = n-r := by rw [Increment.bits_value,hidx]; omega
    have hnewlen : (Increment.bits idx).length ≤ n.bits.length :=
      BankArray.increment_length_bound idx n.bits.length hlen' (by omega)
    have hprefix : n-r = (n-(r+1))+1 := by omega
    have hrepresented' : Represents layout t.val.memory a b (n-r) := by
      rw [htm]
      simpa only [hprefix] using har
    refine ⟨scost+icost,t,es.seq ei,?_,?_,?_⟩
    · exact ⟨by omega,Increment.bits idx,hnew,hnewlen,config_increment htapes hac hti,
        workspace_of_tapes (fun i hi => htapes i (by rcases hi with hi | hi <;> simp_all [Private,DoublingPass.Private] <;> omega)) haw,
        hrepresented',hframe.trans ((LoopFrame.of_step haf).trans (LoopFrame.of_increment htf)),
        by simpa only [htm] using hmem.trans ham⟩
    · exact (htapes 94 (by omega)).trans
        ((haf.2.2.2.1 94 (by omega) (by simp [Private,DoublingPass.Private])).trans hcounter)
    · have hb : budget layout idx ≤ budget layout n.bits := by dsimp [budget,DoublingPass.budget]; omega
      have hs : scost ≤ 250000*(budget layout n.bits+1)^2 := hscost.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      have hl : n.bits.length+10 ≤ budget layout n.bits := by dsimp [budget,DoublingPass.budget]; omega
      dsimp [bound]
      nlinarith
  have hinit : invariant n s := by
    refine ⟨le_rfl,index,?_,hlen,hconfig,hwork,?_,LoopFrame.refl _,DoublingPass.MemoryFrame.refl _ _ _⟩
    · simpa using hindex
    · simpa only [Nat.sub_self] using hrep
  obtain ⟨lcost,l,finalCount,el,hinv,hltape,hlength,_,hlcost⟩ :=
    CountedShifted.executes 94 countOrigin loopBody input randomTape invariant (fun _ => bound)
      (invariant_stable layout a b clock s.val) bodyCorrect n n.bits s
      (RationalAccumulator.address_bits n) hcount hinit
  obtain ⟨_,finalIndex,hval,hlen',hc,hw',hr,hf,hm⟩ := hinv
  obtain ⟨t,et,htapes,tf⟩ := WordCall.clear 94 input randomTape finalCount countOrigin l hltape
  have keep (i : ℕ) (hi : i ≠ 94) : t.val.tapes i = l.val.tapes i := tf.2.2.2.2.2.1 i hi hi
  have tframe : LoopFrame l.val t.val := by
    rcases tf with ⟨_,hi,_,hr,ho,ht,hg⟩
    exact ⟨hi,hr,ho,fun i _ _ _ h94 => ht i h94 h94,
      fun i _ _ _ h26 h27 _ _ => hg i h26 h27⟩
  refine ⟨_,t,finalIndex,?_,el.seq et,by simpa using hval,hlen',
    config_of_tapes (fun i hi => keep i (by omega)) hc,
    workspace_of_tapes (fun i hi => keep i (by rcases hi with hi | hi <;> simp_all [Private,DoublingPass.Private] <;> omega)) hw',
    ⟨countOrigin+finalCount.length,by simp [htapes]⟩,?_,hf.trans tframe,?_⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hlcost
    dsimp [loopCost]
    rw [hlength]
    dsimp [bound] at hlcost
    omega
  · simpa only [tf.2.2.1,Nat.sub_zero] using hr
  · simpa only [tf.2.2.1] using hm

theorem loop_run {n : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (layout : Layout) (a b : Equiv.Perm (Fin n)) (index clock : List Bool)
    (hw : 0 < layout.route.width) (hn : n ≤ 2^layout.route.width)
    (hfit : n.bits.length ≤ layout.route.width)
    (hclock : clock.length = layout.route.width) (hsep : layout.Separated n)
    (hindex : addressValue index = 0) (hlen : index.length ≤ n.bits.length)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 94 = BitTape.shifted n.bits countOrigin)
    (hconfig : Config layout index clock s.val) (hwork : Workspace s.val)
    (hrep : Represents layout s.val.memory a b 0) :
    ∃ t : Store, ∃ finalIndex : List Bool,
      (runPriced (loopCode.compile.next input randomTape) (loopCost layout n+1) s.val).finished =
        some (t.place loopCode.size) ∧
      (runPriced (loopCode.compile.next input randomTape) (loopCost layout n+1) s.val).instructions ≤ loopCost layout n ∧
      addressValue finalIndex = n ∧ finalIndex.length ≤ n.bits.length ∧
      Config layout finalIndex clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory a b n ∧
      LoopFrame s.val t.val ∧
      DoublingPass.MemoryFrame layout.route n s.val.memory t.val.memory := by
  obtain ⟨cost,t,finalIndex,hcost,he,ht⟩ := loop_executes input randomTape layout a b index clock
    hw hn hfit hclock hsep hindex hlen countOrigin s hcount hconfig hwork hrep
  have hr := he.compiled_run (loopCost layout n+1) (by omega)
  exact ⟨t,finalIndex,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.DoublingInit
