import Maxwell.Cost.HalfPair.Step
import Maxwell.Cost.DoublingInit.Loop
import Maxwell.Cost.BankArray.Increment
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.HalfPair
open Structured DoublingInit
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing
open scoped BigOperators

/-- Successive slots receive the exact numeric source-pair permutation. -/
def LoopInvariant (k : ℕ) (layout : Layout) (output : Vector (List Bool) (2*(2^k)))
    (clock : List Bool) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ 2*(2^k) ∧ ∃ index : List Bool,
    addressValue index = 2*(2^k)-remaining ∧ index.length ≤ (2*(2^k)).bits.length ∧ Config layout index clock s.val ∧
    Workspace s.val ∧ Represents layout s.val.memory
      (fill k output (2*(2^k)-remaining) (Nat.sub_le _ _)) ∧ LoopFrame initial s.val ∧ MemoryFrame layout k initial.memory s.val.memory

private theorem invariant_stable (k : ℕ) (layout : Layout)
    (output : Vector (List Bool) (2*(2^k))) (clock : List Bool) (initial : BitRAMState)
    (r : ℕ) (s t : Store) (hf : CountedShifted.Frame 94 s t)
    (h : LoopInvariant k layout output clock initial r s) :
    LoopInvariant k layout output clock initial r t := by
  obtain ⟨hr,index,hindex,hlen,hconfig,hwork,hrep,hframe,hmemory⟩ := h
  refine ⟨hr,index,hindex,hlen,config_of_tapes (fun i hi => hf.2.2.2.2.2.1 i (by omega)) hconfig,
    workspace_of_tapes (fun i hi => hf.2.2.2.2.2.1 i (by rcases hi with hi | hi <;> simp_all [Private,DoublingPass.Private] <;> omega)) hwork,?_,
    hframe.trans (LoopFrame.of_counter hf),?_⟩
  · simpa only [hf.2.2.1] using hrep
  · simpa only [hf.2.2.1] using hmemory

def loopBody : Code := .seq stepCode (BankArray.incrementCode 81)
def loopCode : Code := .seq (CountedShifted.code 94 loopBody) (.call (TapeOps.clear 94))

def loopCost (layout : Layout) (n : ℕ) : ℕ :=
  (n+1)*(13*n.bits.length+15) + n*(150000*(budget layout n.bits+1)^2) + 6*n.bits.length+4

/-- The actual finite traversal constructs the source-pair array.
Neither the program nor its loop body depends on array size or contents. -/
theorem loop_executes (k : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (layout : Layout) (output : Vector (List Bool) (2*(2^k))) (index clock : List Bool)
    (hwidth : layout.route.width = k+2)
    (hclock : clock.length = layout.route.width)
    (hindex : addressValue index = 0) (hlen : index.length ≤ (2*(2^k)).bits.length)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 94 = BitTape.shifted (2*(2^k)).bits countOrigin)
    (hconfig : Config layout index clock s.val) (hwork : Workspace s.val)
    (hrep : Represents layout s.val.memory output) :
    ∃ cost, ∃ t : Store, ∃ finalIndex : List Bool,
      cost ≤ loopCost layout (2*(2^k)) ∧ Executes input randomTape loopCode cost s t ∧
      addressValue finalIndex = 2*(2^k) ∧ finalIndex.length ≤ (2*(2^k)).bits.length ∧
      Config layout finalIndex clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory (array k) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  let n := 2*(2^k)
  have hfit : n.bits.length ≤ layout.route.width := by
    dsimp [n]
    rw [array_bits_length,hwidth]
  let invariant := LoopInvariant k layout output clock s.val
  let bound := 150000*(budget layout (2*(2^k)).bits+1)^2
  have hnPower : n < 2^(2*(2^k)).bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self n
  have bodyCorrect : ∀ r xs u, invariant (r+1) u →
      u.val.tapes 94 = BitTape.shifted xs countOrigin → addressValue xs = r →
      ∃ bodyCost t, Executes input randomTape loopBody bodyCost u t ∧
        invariant r t ∧ t.val.tapes 94 = BitTape.shifted xs countOrigin ∧ bodyCost ≤ bound := by
    intro r xs u hu hcounter _
    obtain ⟨hr,idx,hidx,hlen',hcfg,hworkspace,hrepresented,hframe,hmemory⟩ := hu
    have hlt : n-(r+1) < n := by omega
    let j : Fin n := ⟨n-(r+1),hlt⟩
    obtain ⟨scost,a,hscost,es,hac,haw,har,haf,ham⟩ := step_executes k input randomTape layout
      (fill k output (n-(r+1)) (Nat.sub_le _ _)) j idx clock hwidth (hlen'.trans hfit) hidx hclock
      u hcfg hworkspace hrepresented
    obtain ⟨icost,t,hicost,ei,hti,_,htm,_,htapes,htf⟩ := BankArray.increment_bank 81 (by omega)
      input randomTape idx a hac.route.index haw.1.1
    have hnew : addressValue (Increment.bits idx) = n-r := by rw [Increment.bits_value,hidx]; omega
    have hnewlen : (Increment.bits idx).length ≤ (2*(2^k)).bits.length :=
      BankArray.increment_length_bound idx (2*(2^k)).bits.length hlen' (by omega)
    have hprefix : n-r = (n-(r+1))+1 := by omega
    have hrepresented' : Represents layout t.val.memory
        (fill k output (n-r) (Nat.sub_le _ _)) := by
      rw [htm]
      simpa only [hprefix,fill] using har
    refine ⟨scost+icost,t,es.seq ei,?_,?_,?_⟩
    · exact ⟨by omega,Increment.bits idx,hnew,hnewlen,config_increment htapes hac hti,
        workspace_of_tapes (fun i hi => htapes i (by rcases hi with hi | hi <;> simp_all [Private,DoublingPass.Private] <;> omega)) haw,
        hrepresented',hframe.trans ((LoopFrame.of_step haf).trans (LoopFrame.of_increment htf)),
        by simpa only [htm] using hmemory.trans ham⟩
    · exact (htapes 94 (by omega)).trans
        ((haf.2.2.2.1 94 (by omega) (by simp [Private,DoublingPass.Private])).trans hcounter)
    · have hb : budget layout idx ≤ budget layout (2*(2^k)).bits := by dsimp [budget,DoublingPass.budget]; omega
      have hs : scost ≤ 100000*(budget layout (2*(2^k)).bits+1)^2 := hscost.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      have hl : (2*(2^k)).bits.length+10 ≤ budget layout (2*(2^k)).bits := by dsimp [budget,DoublingPass.budget]; omega
      dsimp [bound]
      nlinarith
  have hinit : invariant n s := by
    refine ⟨le_rfl,index,?_,hlen,hconfig,hwork,?_,LoopFrame.refl _,ConjugatePass.MemoryFrame.refl _ _ _⟩
    · simpa [n] using hindex
    · simpa only [n,Nat.sub_self,fill] using hrep
  obtain ⟨lcost,l,finalCount,el,hinv,hltape,hlength,_,hlcost⟩ :=
    CountedShifted.executes 94 countOrigin loopBody input randomTape invariant (fun _ => bound)
      (invariant_stable k layout output clock s.val) bodyCorrect n (2*(2^k)).bits s
      (RationalAccumulator.address_bits n) hcount hinit
  obtain ⟨_,finalIndex,hval,hlen',hc,hw',hr,hf,hmemory⟩ := hinv
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
    dsimp [bound,n] at hlcost
    omega
  · simpa only [tf.2.2.1,Nat.sub_zero,fill_complete] using hr
  · simpa only [tf.2.2.1] using hmemory

theorem loop_run (k : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (layout : Layout) (output : Vector (List Bool) (2*(2^k))) (index clock : List Bool)
    (hwidth : layout.route.width = k+2)
    (hclock : clock.length = layout.route.width)
    (hindex : addressValue index = 0) (hlen : index.length ≤ (2*(2^k)).bits.length)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 94 = BitTape.shifted (2*(2^k)).bits countOrigin)
    (hconfig : Config layout index clock s.val) (hwork : Workspace s.val)
    (hrep : Represents layout s.val.memory output) :
    ∃ t : Store, ∃ finalIndex : List Bool,
      (runPriced (loopCode.compile.next input randomTape) (loopCost layout (2*(2^k))+1) s.val).finished =
        some (t.place loopCode.size) ∧
      (runPriced (loopCode.compile.next input randomTape) (loopCost layout (2*(2^k))+1) s.val).instructions ≤ loopCost layout (2*(2^k)) ∧
      addressValue finalIndex = 2*(2^k) ∧ finalIndex.length ≤ (2*(2^k)).bits.length ∧
      Config layout finalIndex clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      Represents layout t.val.memory (array k) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨cost,t,finalIndex,hcost,he,ht⟩ := loop_executes k input randomTape layout output index clock
    hwidth hclock hindex hlen countOrigin s hcount hconfig hwork hrep
  have hr := he.compiled_run (loopCost layout (2*(2^k))+1) (by omega)
  exact ⟨t,finalIndex,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.HalfPair
