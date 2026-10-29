import Maxwell.Cost.DoublingPass.Pass
import Maxwell.Cost.WordSwap

namespace Maxwell.Cost.DoublingPass
open Structured
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing

def RoundPrivate (i : ℕ) : Prop :=
  i = 81 ∨ i = 82 ∨ i = 84 ∨ i = 85 ∨ i = 86 ∨ Private i ∨ i = 94 ∨ i = 95

def RoundFrame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → ¬RoundPrivate i → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem RoundFrame.refl (s : BitRAMState) : RoundFrame s s := by simp [RoundFrame]

theorem RoundFrame.trans {s t u : BitRAMState} (h : RoundFrame s t) (k : RoundFrame t u) : RoundFrame s u := by
  rcases h with ⟨hi,hr,ho,ht,hg⟩
  rcases k with ⟨ki,kr,ko,kt,kg⟩
  exact ⟨ki.trans hi,kr.trans hr,ko.trans ho,
    fun i hi hp => (kt i hi hp).trans (ht i hi hp),
    fun i hi h24 h25 h26 h27 h28 h29 =>
      (kg i hi h24 h25 h26 h27 h28 h29).trans (hg i hi h24 h25 h26 h27 h28 h29)⟩

theorem RoundFrame.of_loop {s t : BitRAMState} (h : LoopFrame s t) : RoundFrame s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_,h.2.2.2.2⟩
  intro i hi hp
  simp only [RoundPrivate,not_or] at hp
  exact h.2.2.2.1 i hi hp.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1

theorem RoundFrame.of_swap {left right temp : ℕ} {s t : BitRAMState}
    (hl : RoundPrivate left) (hr : RoundPrivate right) (ht : RoundPrivate temp)
    (h : WordSwap.Frame left right temp s t) : RoundFrame s t := by
  refine ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,?_,?_⟩
  · intro i _ hp
    exact h.2.2.2.2.2.1 i (by intro he; exact hp (he ▸ hl))
      (by intro he; exact hp (he ▸ hr)) (by intro he; exact hp (he ▸ ht))
  · intro i _ h24 h25 h26 h27 _ _
    exact h.2.2.2.2.2.2 i h24 h25 h26 h27

def swapCode : Code := .seq (WordSwap.code 82 85 95) (WordSwap.code 84 86 95)
def swapCost (layout : Layout) : ℕ :=
  36*(layout.oldJump.bits.length+layout.oldMinimum.bits.length+
      layout.newJump.bits.length+layout.newMinimum.bits.length)+66

@[simp] theorem swapCost_flip (layout : Layout) : swapCost layout.flip = swapCost layout := by
  simp only [swapCost,Layout.flip]; omega

@[simp] theorem swapCost_layoutAfter (layout : Layout) (k : ℕ) :
    swapCost (layoutAfter layout k) = swapCost layout := by induction k <;> simp_all [layoutAfter]

theorem swap_executes (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (clock : List Bool) (s : Store)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (h94 : Blank s.val 94) (h95 : Blank s.val 95) :
    ∃ cost t, cost ≤ swapCost layout ∧ Executes input tape swapCode cost s t ∧
      Config layout.flip [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧ Blank t.val 95 ∧
      t.val.memory = s.val.memory ∧ RoundFrame s.val t.val := by
  obtain ⟨a,ea,a82,a85,a95,af⟩ := WordSwap.executes 82 85 95
    (by omega) (by omega) (by omega) input tape layout.oldJump.bits layout.newJump.bits
    s cfg.oldJump cfg.newJump h95
  obtain ⟨t,et,t84,t86,t95,tf⟩ := WordSwap.executes 84 86 95
    (by omega) (by omega) (by omega) input tape layout.oldMinimum.bits layout.newMinimum.bits
    a (BankArray.word_of_eq (af.2.2.2.2.2.1 84 (by omega) (by omega) (by omega)) cfg.oldMinimum)
    (BankArray.word_of_eq (af.2.2.2.2.2.1 86 (by omega) (by omega) (by omega)) cfg.newMinimum) a95
  have keep (i : ℕ) (h82 : i ≠ 82) (h84 : i ≠ 84) (h85 : i ≠ 85) (h86 : i ≠ 86) (h95' : i ≠ 95) :
      t.val.tapes i = s.val.tapes i :=
    (tf.2.2.2.2.2.1 i h84 h86 h95').trans (af.2.2.2.2.2.1 i h82 h85 h95')
  have tc : Config layout.flip [] clock t.val :=
    ⟨BankArray.word_of_eq (keep 80 (by omega) (by omega) (by omega) (by omega) (by omega)) cfg.width,
     BankArray.word_of_eq (keep 81 (by omega) (by omega) (by omega) (by omega) (by omega)) cfg.index,
     BankArray.word_of_eq (tf.2.2.2.2.2.1 82 (by omega) (by omega) (by omega)) a82,
     BankArray.word_of_eq (keep 83 (by omega) (by omega) (by omega) (by omega) (by omega)) cfg.clock,
     t84,BankArray.word_of_eq (tf.2.2.2.2.2.1 85 (by omega) (by omega) (by omega)) a85,t86⟩
  have tw : Workspace t.val := by
    rcases work with ⟨⟨w0,w1,w2,w3,w5,w6,w8,w9⟩,w7,wp⟩
    refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
    all_goals first
    | exact RationalAccumulator.blank_of_eq (keep _ (by omega) (by omega) (by omega) (by omega) (by omega)) (by assumption)
    | exact fun i hi => RationalAccumulator.blank_of_eq
        (keep i (by simp_all [Private]; omega) (by simp_all [Private]; omega)
          (by simp_all [Private]; omega) (by simp_all [Private]; omega) (by simp_all [Private]; omega)) (wp i hi)
  refine ⟨_,t,?_,ea.seq et,tc,tw,
    RationalAccumulator.blank_of_eq (keep 94 (by omega) (by omega) (by omega) (by omega) (by omega)) h94,
    t95,tf.2.2.1.trans af.2.2.1,
    (RoundFrame.of_swap (by simp [RoundPrivate]) (by simp [RoundPrivate]) (by simp [RoundPrivate]) af).trans
      (RoundFrame.of_swap (by simp [RoundPrivate]) (by simp [RoundPrivate]) (by simp [RoundPrivate]) tf)⟩
  dsimp [swapCost]; omega

def roundCode : Code := .seq passCode swapCode

def roundCost (layout : Layout) (n : ℕ) : ℕ := passCost layout n + swapCost layout

@[simp] theorem roundCost_flip (layout : Layout) (n : ℕ) : roundCost layout.flip n = roundCost layout n := by
  simp only [roundCost,passCost_flip,swapCost_flip]

@[simp] theorem roundCost_layoutAfter (layout : Layout) (k n : ℕ) :
    roundCost (layoutAfter layout k) n = roundCost layout n := by simp only [roundCost,passCost_layoutAfter,swapCost_layoutAfter]

/-- Compute one saved-array pass and exchange the four physical descriptor
words. The next invocation therefore reads the arrays just produced. -/
theorem round_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved output : State n) (clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hclock : clock.length = layout.width) (hsep : layout.Separated n)
    (s : Store) (hnword : BankArray.Word s.val 96 n.bits) (h94 : Blank s.val 94) (h95 : Blank s.val 95)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ roundCost layout n ∧ Executes input tape roundCode cost s t ∧
      Config layout.flip [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧ Blank t.val 95 ∧
      Represents layout.flip t.val.memory (Doubling.step (Equiv.refl (Fin n)) saved) saved ∧
      RoundFrame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨pc,p,hpc,ep,cfgP,workP,p94,repP,pf,pmemory⟩ :=
    pass_executes input tape layout saved output clock hw hn hclock hsep s hnword h94 cfg work rep
  obtain ⟨sc,t,hsc,es,cfgT,workT,t94,t95,tm,tf⟩ := swap_executes input tape layout clock p cfgP workP p94
    (RationalAccumulator.blank_of_eq (pf.2.2.2.1 95 (by omega) (by omega) (by simp [Private]) (by omega)) h95)
  refine ⟨pc+sc,t,by dsimp [roundCost]; omega,ep.seq es,cfgT,workT,t94,t95,?_,(RoundFrame.of_loop pf).trans tf,?_⟩
  · simpa only [tm] using repP.flip
  · simpa only [tm] using pmemory

end Maxwell.Cost.DoublingPass
