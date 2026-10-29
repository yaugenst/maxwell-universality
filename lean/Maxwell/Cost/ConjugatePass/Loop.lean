import Maxwell.Cost.ConjugatePass.Step
import Maxwell.Cost.DoublingPass.Loop
import Maxwell.Cost.BankArray.Increment
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.ConjugatePass
open Structured DoublingPass
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing
open scoped BigOperators

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

private theorem config_increment {layout : Layout} {index clock : List Bool}
    {s t : BitRAMState} (h : ∀ i, i ≠ 81 → t.tapes i = s.tapes i)
    (c : Config layout index clock s) (hi : BankArray.Word t 81 (Increment.bits index)) :
    Config layout (Increment.bits index) clock t := by
  exact ⟨BankArray.word_of_eq (h 80 (by omega)) c.width,hi,
    BankArray.word_of_eq (h 82 (by omega)) c.oldJump,
    BankArray.word_of_eq (h 83 (by omega)) c.clock,
    BankArray.word_of_eq (h 84 (by omega)) c.oldMinimum,
    BankArray.word_of_eq (h 85 (by omega)) c.newJump,
    BankArray.word_of_eq (h 86 (by omega)) c.newMinimum⟩

/-- Saved input arrays are immutable while successive output slots are filled. -/
def LoopInvariant {n : ℕ} (layout : Layout) (saved : Tables n) (output : Vector (List Bool) n)
    (clock : List Bool) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ n ∧ ∃ index : List Bool,
    addressValue index = n-remaining ∧ index.length ≤ n.bits.length ∧ Config layout index clock s.val ∧
    Workspace s.val ∧ Represents layout s.val.memory saved
      (fill layout.width saved output (n-remaining) (Nat.sub_le _ _)) ∧ LoopFrame initial s.val ∧ MemoryFrame layout n initial.memory s.val.memory

private theorem invariant_stable {n : ℕ} (layout : Layout)
    (saved : Tables n) (output : Vector (List Bool) n) (clock : List Bool) (initial : BitRAMState)
    (r : ℕ) (s t : Store) (hf : CountedShifted.Frame 94 s t)
    (h : LoopInvariant layout saved output clock initial r s) :
    LoopInvariant layout saved output clock initial r t := by
  obtain ⟨hr,index,hindex,hlen,hconfig,hwork,hrep,hframe,hmemory⟩ := h
  refine ⟨hr,index,hindex,hlen,config_of_tapes (fun i hi hi' => hf.2.2.2.2.2.1 i (by omega)) hconfig,
    workspace_of_tapes (fun i hi => hf.2.2.2.2.2.1 i (by rcases hi with hi | hi <;> simp_all [Private] <;> omega)) hwork,?_,
    hframe.trans (LoopFrame.of_counter hf),?_⟩
  · simpa only [hf.2.2.1] using hrep
  · simpa only [hf.2.2.1] using hmemory

def loopBody : Code := .seq stepCode (BankArray.incrementCode 81)
def loopCode : Code := .seq (CountedShifted.code 94 loopBody) (.call (TapeOps.clear 94))

def loopCost (layout : Layout) (n : ℕ) : ℕ :=
  (n+1)*(13*n.bits.length+15) + n*(250000*(budget layout n.bits+1)^2) + 6*n.bits.length+4

/-- The actual finite traversal realizes the conjugated pairing array.
Neither the program nor its loop body depends on array size or contents. -/
theorem loop_executes {n : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (layout : Layout) (saved : Tables n) (output : Vector (List Bool) n) (index clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hclock : clock.length = layout.width) (hsep : Separated layout n)
    (hindex : addressValue index = 0) (hlen : index.length ≤ n.bits.length)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 94 = BitTape.shifted n.bits countOrigin)
    (hconfig : Config layout index clock s.val) (hwork : Workspace s.val)
    (hrep : Represents layout s.val.memory saved output) :
    ∃ cost, ∃ t : Store, ∃ finalIndex : List Bool,
      cost ≤ loopCost layout n ∧ Executes input randomTape loopCode cost s t ∧
      addressValue finalIndex = n ∧ finalIndex.length ≤ n.bits.length ∧
      Config layout finalIndex clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory saved (words layout.width (composed saved)) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  let invariant := LoopInvariant layout saved output clock s.val
  let bound := 250000*(budget layout n.bits+1)^2
  have hnPower : n < 2^n.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self n
  have bodyCorrect : ∀ r xs u, invariant (r+1) u →
      u.val.tapes 94 = BitTape.shifted xs countOrigin → addressValue xs = r →
      ∃ bodyCost t, Executes input randomTape loopBody bodyCost u t ∧
        invariant r t ∧ t.val.tapes 94 = BitTape.shifted xs countOrigin ∧ bodyCost ≤ bound := by
    intro r xs u hu hcounter _
    obtain ⟨hr,idx,hidx,hlen',hcfg,hworkspace,hrepresented,hframe,hmemory⟩ := hu
    have hlt : n-(r+1) < n := by omega
    let j : Fin n := ⟨n-(r+1),hlt⟩
    obtain ⟨scost,a,hscost,es,haw,hac,har,haf,ham⟩ := step_executes input randomTape layout saved
      (fill layout.width saved output (n-(r+1)) (Nat.sub_le _ _)) j idx clock hw hn hidx hclock hsep
      u hcfg hworkspace hrepresented
    obtain ⟨icost,t,hicost,ei,hti,_,htm,_,htapes,htf⟩ := BankArray.increment_bank 81 (by omega)
      input randomTape idx a hac.index haw.1
    have hnew : addressValue (Increment.bits idx) = n-r := by rw [Increment.bits_value,hidx]; omega
    have hnewlen : (Increment.bits idx).length ≤ n.bits.length :=
      BankArray.increment_length_bound idx n.bits.length hlen' (by omega)
    have hprefix : n-r = (n-(r+1))+1 := by omega
    have hrepresented' : Represents layout t.val.memory saved
        (fill layout.width saved output (n-r) (Nat.sub_le _ _)) := by
      rw [htm]
      simpa only [hprefix,fill] using har
    refine ⟨scost+icost,t,es.seq ei,?_,?_,?_⟩
    · exact ⟨by omega,Increment.bits idx,hnew,hnewlen,config_increment htapes hac hti,
        workspace_of_tapes (fun i hi => htapes i (by rcases hi with hi | hi <;> simp_all [Private] <;> omega)) haw,
        hrepresented',hframe.trans ((LoopFrame.of_step haf).trans (LoopFrame.of_increment htf)),
        by simpa only [htm] using hmemory.trans ham⟩
    · exact (htapes 94 (by omega)).trans
        ((haf.2.2.2.1 94 (by omega) (by simp [Private])).trans hcounter)
    · have hb : budget layout idx ≤ budget layout n.bits := by dsimp [budget]; omega
      have hs : scost ≤ 200000*(budget layout n.bits+1)^2 := hscost.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      have hl : n.bits.length+10 ≤ budget layout n.bits := by dsimp [budget]; omega
      dsimp [bound]
      nlinarith
  have hinit : invariant n s := by
    refine ⟨le_rfl,index,?_,hlen,hconfig,hwork,?_,LoopFrame.refl _,MemoryFrame.refl _ _ _⟩
    · simpa using hindex
    · simpa only [Nat.sub_self,fill] using hrep
  obtain ⟨lcost,l,finalCount,el,hinv,hltape,hlength,_,hlcost⟩ :=
    CountedShifted.executes 94 countOrigin loopBody input randomTape invariant (fun _ => bound)
      (invariant_stable layout saved output clock s.val) bodyCorrect n n.bits s
      (RationalAccumulator.address_bits n) hcount hinit
  obtain ⟨_,finalIndex,hval,hlen',hc,hw',hr,hf,hmemory⟩ := hinv
  obtain ⟨t,et,htapes,tf⟩ := WordCall.clear 94 input randomTape finalCount countOrigin l hltape
  have keep (i : ℕ) (hi : i ≠ 94) : t.val.tapes i = l.val.tapes i := tf.2.2.2.2.2.1 i hi hi
  have tframe : LoopFrame l.val t.val := by
    rcases tf with ⟨_,hi,_,hr,ho,ht,hg⟩
    exact ⟨hi,hr,ho,fun i _ _ _ h94 => ht i h94 h94,
      fun i _ _ _ h26 h27 _ _ => hg i h26 h27⟩
  refine ⟨_,t,finalIndex,?_,el.seq et,by simpa using hval,hlen',
    config_of_tapes (fun i hi hi' => keep i (by omega)) hc,
    workspace_of_tapes (fun i hi => keep i (by rcases hi with hi | hi <;> simp_all [Private] <;> omega)) hw',
    ⟨countOrigin+finalCount.length,by simp [htapes]⟩,?_,hf.trans tframe,?_⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hlcost
    dsimp [loopCost]
    rw [hlength]
    dsimp [bound] at hlcost
    omega
  · simpa only [tf.2.2.1,Nat.sub_zero,fill_complete] using hr
  · simpa only [tf.2.2.1] using hmemory

theorem loop_run {n : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (layout : Layout) (saved : Tables n) (output : Vector (List Bool) n) (index clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hclock : clock.length = layout.width) (hsep : Separated layout n)
    (hindex : addressValue index = 0) (hlen : index.length ≤ n.bits.length)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 94 = BitTape.shifted n.bits countOrigin)
    (hconfig : Config layout index clock s.val) (hwork : Workspace s.val)
    (hrep : Represents layout s.val.memory saved output) :
    ∃ t : Store, ∃ finalIndex : List Bool,
      (runPriced (loopCode.compile.next input randomTape) (loopCost layout n+1) s.val).finished =
        some (t.place loopCode.size) ∧
      (runPriced (loopCode.compile.next input randomTape) (loopCost layout n+1) s.val).instructions ≤ loopCost layout n ∧
      addressValue finalIndex = n ∧ finalIndex.length ≤ n.bits.length ∧
      Config layout finalIndex clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory saved (words layout.width (composed saved)) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨cost,t,finalIndex,hcost,he,ht⟩ := loop_executes input randomTape layout saved output index clock
    hw hn hclock hsep hindex hlen countOrigin s hcount hconfig hwork hrep
  have hr := he.compiled_run (loopCost layout n+1) (by omega)
  exact ⟨t,finalIndex,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.ConjugatePass
