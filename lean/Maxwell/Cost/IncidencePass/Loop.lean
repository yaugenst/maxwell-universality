import Maxwell.Cost.IncidencePass.Step
import Maxwell.Cost.BankArray.Increment
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.IncidencePass
open Structured
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing
open scoped BigOperators

/-- The traversal changes its index, remaining-count word and three private
words. The descriptor banks and all unrelated persistent tapes survive. -/
def LoopFrame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → i ≠ 81 → i ≠ 88 → i ≠ 89 → i ≠ 90 → i ≠ 92 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem LoopFrame.refl (s : BitRAMState) : LoopFrame s s := by simp [LoopFrame]

theorem LoopFrame.trans {s t u : BitRAMState} (h : LoopFrame s t) (k : LoopFrame t u) : LoopFrame s u := by
  rcases h with ⟨hi,hr,ho,ht,hg⟩
  rcases k with ⟨ki,kr,ko,kt,kg⟩
  exact ⟨ki.trans hi,kr.trans hr,ko.trans ho,
    fun i hi h81 h88 h89 h90 h92 => (kt i hi h81 h88 h89 h90 h92).trans (ht i hi h81 h88 h89 h90 h92),
    fun i hi h24 h25 h26 h27 h28 h29 =>
      (kg i hi h24 h25 h26 h27 h28 h29).trans (hg i hi h24 h25 h26 h27 h28 h29)⟩

theorem LoopFrame.of_step {s t : BitRAMState} (h : Frame s t) : LoopFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi _ h88 h89 h90 _ => h.2.2.2.1 i hi h88 h89 h90,h.2.2.2.2⟩

theorem LoopFrame.of_increment {s t : BitRAMState} (h : BankArray.FrameExcept 81 s t) : LoopFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi h81 _ _ _ _ => h.2.2.2.1 i hi h81,h.2.2.2.2⟩

theorem LoopFrame.of_counter {s t : Store} (h : CountedShifted.Frame 92 s t) : LoopFrame s.val t.val := by
  rcases h with ⟨_,hi,_,hr,ho,ht,hg⟩
  exact ⟨hi,hr,ho,fun i _ _ _ _ _ h92 => ht i h92,
    fun i hi h24 h25 _ _ _ h29 => hg i (by omega) h24 h25 h29⟩

private theorem config_of_tapes {layout : IncidenceEncoding.Layout} {index clock : List Bool}
    {s t : BitRAMState} (h : ∀ i, 80 ≤ i → i ≤ 87 → t.tapes i = s.tapes i)
    (c : Config layout index clock s) : Config layout index clock t := by
  constructor
  · exact BankArray.word_of_eq (h 80 (by omega) (by omega)) c.width
  · exact BankArray.word_of_eq (h 81 (by omega) (by omega)) c.index
  · exact BankArray.word_of_eq (h 82 (by omega) (by omega)) c.endpoints
  · exact BankArray.word_of_eq (h 83 (by omega) (by omega)) c.clock
  · exact BankArray.word_of_eq (h 84 (by omega) (by omega)) c.two
  · exact BankArray.word_of_eq (h 85 (by omega) (by omega)) c.counters
  · exact BankArray.word_of_eq (h 86 (by omega) (by omega)) c.ranks
  · exact BankArray.word_of_eq (h 87 (by omega) (by omega)) c.twoClock

private theorem workspace_of_tapes {s t : BitRAMState}
    (h : ∀ i, i < 10 ∨ i = 88 ∨ i = 89 ∨ i = 90 → t.tapes i = s.tapes i)
    (w : Workspace s) : Workspace t := by
  rcases w with ⟨⟨h0,h1,h2,h3,h5,h6,h8,h9⟩,h7,h88,h89,h90⟩
  exact ⟨⟨RationalAccumulator.blank_of_eq (h 0 (by omega)) h0,
    RationalAccumulator.blank_of_eq (h 1 (by omega)) h1,
    RationalAccumulator.blank_of_eq (h 2 (by omega)) h2,
    RationalAccumulator.blank_of_eq (h 3 (by omega)) h3,
    RationalAccumulator.blank_of_eq (h 5 (by omega)) h5,
    RationalAccumulator.blank_of_eq (h 6 (by omega)) h6,
    RationalAccumulator.blank_of_eq (h 8 (by omega)) h8,
    RationalAccumulator.blank_of_eq (h 9 (by omega)) h9⟩,
    RationalAccumulator.blank_of_eq (h 7 (by omega)) h7,
    RationalAccumulator.blank_of_eq (h 88 (by omega)) h88,
    RationalAccumulator.blank_of_eq (h 89 (by omega)) h89,
    RationalAccumulator.blank_of_eq (h 90 (by omega)) h90⟩

private theorem config_increment {layout : IncidenceEncoding.Layout} {index clock : List Bool}
    {s t : BitRAMState} (h : ∀ i, i ≠ 81 → t.tapes i = s.tapes i)
    (c : Config layout index clock s) (hi : BankArray.Word t 81 (Increment.bits index)) :
    Config layout (Increment.bits index) clock t := by
  exact ⟨BankArray.word_of_eq (h 80 (by omega)) c.width,hi,
    BankArray.word_of_eq (h 82 (by omega)) c.endpoints,
    BankArray.word_of_eq (h 83 (by omega)) c.clock,
    BankArray.word_of_eq (h 84 (by omega)) c.two,
    BankArray.word_of_eq (h 85 (by omega)) c.counters,
    BankArray.word_of_eq (h 86 (by omega)) c.ranks,
    BankArray.word_of_eq (h 87 (by omega)) c.twoClock⟩

/-- A countdown invariant records the exact prefix already processed. -/
def LoopInvariant {V I : ℕ} (layout : IncidenceEncoding.Layout) (endpoint : Fin I → Fin V)
    (clock : List Bool) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ I ∧ ∃ index : List Bool,
    addressValue index = I-remaining ∧ index.length ≤ I.bits.length ∧ Config layout index clock s.val ∧
    Workspace s.val ∧ IncidenceEncoding.Represents layout s.val.memory endpoint
      (IncidenceRanks.run endpoint (I-remaining) (Nat.sub_le _ _)) ∧ LoopFrame initial s.val ∧
      MemoryFrame layout V I initial.memory s.val.memory

private theorem invariant_stable {V I : ℕ} (layout : IncidenceEncoding.Layout)
    (endpoint : Fin I → Fin V) (clock : List Bool) (initial : BitRAMState)
    (n : ℕ) (s t : Store) (hf : CountedShifted.Frame 92 s t)
    (h : LoopInvariant layout endpoint clock initial n s) : LoopInvariant layout endpoint clock initial n t := by
  obtain ⟨hn,index,hindex,hlen,hconfig,hwork,hrep,hframe,hmem⟩ := h
  refine ⟨hn,index,hindex,hlen,config_of_tapes (fun i hi hi' => hf.2.2.2.2.2.1 i (by omega)) hconfig,
    workspace_of_tapes (fun i hi => hf.2.2.2.2.2.1 i (by omega)) hwork,?_,
    hframe.trans (LoopFrame.of_counter hf),hmem.trans (MemoryFrame.of_eq hf.2.2.1)⟩
  simpa only [hf.2.2.1] using hrep


def loopBody : Code := .seq stepCode (BankArray.incrementCode 81)
def loopCode : Code := .seq (CountedShifted.code 92 loopBody) (.call (TapeOps.clear 92))

def loopCost (layout : IncidenceEncoding.Layout) (I : ℕ) : ℕ :=
  (I+1)*(13*I.bits.length+15) + I*(300000*(budget layout I.bits+1)^2) + 6*I.bits.length+4

/-- Execute the incidence pass over actual encoded arrays. Each iteration
uses the same finite body, with its index and countdown held in bit tapes. -/
theorem loop_executes {V I : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (layout : IncidenceEncoding.Layout) (endpoint : Fin I → Fin V) (index clock : List Bool)
    (hw : 0 < layout.endpointWidth) (hv : V ≤ 2^layout.endpointWidth)
    (hclock : clock.length = layout.endpointWidth) (hsep : layout.Separated V I)
    (hdegree : IncidenceRanks.DegreeBound endpoint)
    (hindex : addressValue index = 0) (hlen : index.length ≤ I.bits.length)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 92 = BitTape.shifted I.bits countOrigin)
    (hconfig : Config layout index clock s.val) (hwork : Workspace s.val)
    (hrep : IncidenceEncoding.Represents layout s.val.memory endpoint (IncidenceRanks.initial V I)) :
    ∃ cost, ∃ t : Store, ∃ finalIndex : List Bool,
      cost ≤ loopCost layout I ∧ Executes input randomTape loopCode cost s t ∧
      addressValue finalIndex = I ∧ finalIndex.length ≤ I.bits.length ∧
      Config layout finalIndex clock t.val ∧ Workspace t.val ∧ Blank t.val 92 ∧
      IncidenceEncoding.Represents layout t.val.memory endpoint (IncidenceRanks.run endpoint I le_rfl) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout V I s.val.memory t.val.memory := by
  let invariant := LoopInvariant layout endpoint clock s.val
  let bound := 300000*(budget layout I.bits+1)^2
  have hiPower : I < 2^I.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self I
  have bodyCorrect : ∀ n xs u, invariant (n+1) u →
      u.val.tapes 92 = BitTape.shifted xs countOrigin → addressValue xs = n →
      ∃ bodyCost t, Executes input randomTape loopBody bodyCost u t ∧
        invariant n t ∧ t.val.tapes 92 = BitTape.shifted xs countOrigin ∧ bodyCost ≤ bound := by
    intro n xs u hu hcounter _
    obtain ⟨hn,idx,hidx,hlen',hcfg,hworkspace,hrepresented,hframe,hmem⟩ := hu
    have hlt : I-(n+1) < I := by omega
    let incidence : Fin I := ⟨I-(n+1),hlt⟩
    have hrank := IncidenceEncoding.run_current_counter_lt_three endpoint hdegree (I-(n+1)) hlt
    obtain ⟨scost,a,hscost,es,haw,hac,har,haf,ham⟩ := step_executes input randomTape layout endpoint
      (IncidenceRanks.run endpoint (I-(n+1)) (Nat.sub_le _ _)) incidence idx clock hw hv hidx hclock hsep
      hrank u hcfg hworkspace hrepresented
    obtain ⟨icost,t,hicost,ei,hti,_,htm,_,htapes,htf⟩ := BankArray.increment_bank 81 (by omega)
      input randomTape idx a hac.index haw.1
    have hnew : addressValue (Increment.bits idx) = I-n := by rw [Increment.bits_value,hidx]; omega
    have hnewlen : (Increment.bits idx).length ≤ I.bits.length :=
      BankArray.increment_length_bound idx I.bits.length hlen' (by omega)
    have hprefix : I-n = (I-(n+1))+1 := by omega
    have hrepresented' : IncidenceEncoding.Represents layout t.val.memory endpoint
        (IncidenceRanks.run endpoint (I-n) (Nat.sub_le _ _)) := by
      rw [htm]
      simpa only [hprefix,IncidenceRanks.run] using har
    refine ⟨scost+icost,t,es.seq ei,?_,?_,?_⟩
    · exact ⟨by omega,Increment.bits idx,hnew,hnewlen,config_increment htapes hac hti,
        workspace_of_tapes (fun i hi => htapes i (by omega)) haw,hrepresented',
        hframe.trans ((LoopFrame.of_step haf).trans (LoopFrame.of_increment htf)),
        hmem.trans (ham.trans (MemoryFrame.of_eq htm))⟩
    · exact (htapes 92 (by omega)).trans
        ((haf.2.2.2.1 92 (by omega) (by omega) (by omega) (by omega)).trans hcounter)
    · have hb : budget layout idx ≤ budget layout I.bits := by dsimp [budget]; omega
      have hs : scost ≤ 250000*(budget layout I.bits+1)^2 := hscost.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      have hl : I.bits.length+10 ≤ budget layout I.bits := by dsimp [budget]; omega
      dsimp [bound]
      nlinarith
  have hinit : invariant I s := by
    refine ⟨le_rfl,index,?_,hlen,hconfig,hwork,?_,LoopFrame.refl _,MemoryFrame.refl _ _ _ _⟩
    · simpa using hindex
    · simpa only [Nat.sub_self,IncidenceRanks.run] using hrep
  obtain ⟨lcost,l,finalCount,el,hinv,hltape,hlength,_,hlcost⟩ :=
    CountedShifted.executes 92 countOrigin loopBody input randomTape invariant (fun _ => bound)
      (invariant_stable layout endpoint clock s.val) bodyCorrect I I.bits s
      (RationalAccumulator.address_bits I) hcount hinit
  obtain ⟨_,finalIndex,hval,hlen',hc,hw',hr,hf,hm⟩ := hinv
  obtain ⟨t,et,htapes,tf⟩ := WordCall.clear 92 input randomTape finalCount countOrigin l hltape
  have keep (i : ℕ) (hi : i ≠ 92) : t.val.tapes i = l.val.tapes i := tf.2.2.2.2.2.1 i hi hi
  have tframe : LoopFrame l.val t.val := by
    rcases tf with ⟨_,hi,_,hr,ho,ht,hg⟩
    exact ⟨hi,hr,ho,fun i _ _ _ _ _ h92 => ht i h92 h92,
      fun i _ _ _ h26 h27 _ _ => hg i h26 h27⟩
  refine ⟨_,t,finalIndex,?_,el.seq et,by simpa using hval,hlen',
    config_of_tapes (fun i hi hi' => keep i (by omega)) hc,
    workspace_of_tapes (fun i hi => keep i (by omega)) hw',
    ⟨countOrigin+finalCount.length,by simp [htapes]⟩,?_,hf.trans tframe,hm.trans (MemoryFrame.of_eq tf.2.2.1)⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hlcost
    dsimp [loopCost]
    rw [hlength]
    dsimp [bound] at hlcost
    omega
  · simpa only [tf.2.2.1,Nat.sub_zero] using hr

theorem loop_run {V I : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (layout : IncidenceEncoding.Layout) (endpoint : Fin I → Fin V) (index clock : List Bool)
    (hw : 0 < layout.endpointWidth) (hv : V ≤ 2^layout.endpointWidth)
    (hclock : clock.length = layout.endpointWidth) (hsep : layout.Separated V I)
    (hdegree : IncidenceRanks.DegreeBound endpoint)
    (hindex : addressValue index = 0) (hlen : index.length ≤ I.bits.length)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 92 = BitTape.shifted I.bits countOrigin)
    (hconfig : Config layout index clock s.val) (hwork : Workspace s.val)
    (hrep : IncidenceEncoding.Represents layout s.val.memory endpoint (IncidenceRanks.initial V I)) :
    ∃ t : Store, ∃ finalIndex : List Bool,
      (runPriced (loopCode.compile.next input randomTape) (loopCost layout I+1) s.val).finished =
        some (t.place loopCode.size) ∧
      (runPriced (loopCode.compile.next input randomTape) (loopCost layout I+1) s.val).instructions ≤ loopCost layout I ∧
      addressValue finalIndex = I ∧ finalIndex.length ≤ I.bits.length ∧
      Config layout finalIndex clock t.val ∧ Workspace t.val ∧ Blank t.val 92 ∧
      IncidenceEncoding.Represents layout t.val.memory endpoint (IncidenceRanks.run endpoint I le_rfl) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout V I s.val.memory t.val.memory := by
  obtain ⟨cost,t,finalIndex,hcost,he,ht⟩ := loop_executes input randomTape layout endpoint index clock
    hw hv hclock hsep hdegree hindex hlen countOrigin s hcount hconfig hwork hrep
  have hr := he.compiled_run (loopCost layout I+1) (by omega)
  exact ⟨t,finalIndex,hr.1,hr.2.symm ▸ hcost,ht⟩

/-- The returned saved rank bits carry the concrete prefix rank, so the
logical injectivity theorem applies to the array produced by this pass. -/
theorem read_final_rank {V I : ℕ} (layout : IncidenceEncoding.Layout)
    (endpoint : Fin I → Fin V) (hdegree : IncidenceRanks.DegreeBound endpoint)
    (memory : ℕ → Bool)
    (hrep : IncidenceEncoding.Represents layout memory endpoint (IncidenceRanks.run endpoint I le_rfl))
    (incidence : Fin I) :
    addressValue (MemoryWord.readBits memory (layout.baseRank+incidence.val*2) 2) =
      IncidenceRanks.priorCount endpoint incidence.val (endpoint incidence) := by
  have h := hrep.read_rank incidence
    (Nat.le_of_lt (IncidenceEncoding.run_ranks_lt_three endpoint hdegree I le_rfl incidence))
  simpa only [IncidenceRanks.rank_eq endpoint I le_rfl incidence incidence.isLt] using h

end Maxwell.Cost.IncidencePass
