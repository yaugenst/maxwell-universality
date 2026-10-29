import Maxwell.Cost.DoublingPass.Rounds
import Maxwell.Cost.WordLength

namespace Maxwell.Cost.DoublingPass
open Structured
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing

/-- The program itself computes the number of rounds by scanning the binary
array-size word. Thus no input-dependent host integer enters its control flow. -/
def computedCode : Code := .seq (WordLength.code 96 97) roundsCode

def computedCost (layout : Layout) (n : ℕ) : ℕ :=
  48*(n.bits.length+1)^2+1+roundsCost layout n n.bits.length

def CompleteFrame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → ¬RoundPrivate i → i ≠ 97 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i < 24 ∨ 31 < i → t.registers i = s.registers i)

theorem computed_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved output : State n) (clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hclock : clock.length = layout.width) (hsep : layout.PingPong n)
    (s : Store) (hnword : BankArray.Word s.val 96 n.bits)
    (h94 : Blank s.val 94) (h95 : Blank s.val 95) (h97 : Blank s.val 97)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory saved output) :
    ∃ cost t finalOutput, cost ≤ computedCost layout n ∧
      Executes input tape computedCode cost s t ∧
      Config (layoutAfter layout n.bits.length) [] clock t.val ∧ Workspace t.val ∧
      Blank t.val 94 ∧ Blank t.val 95 ∧ Blank t.val 97 ∧ BankArray.Word t.val 96 n.bits ∧
      Represents (layoutAfter layout n.bits.length) t.val.memory (stateAfter saved n.bits.length) finalOutput ∧
      CompleteFrame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨no,hnw⟩ := hnword
  obtain ⟨co,hcw⟩ := h97
  obtain ⟨lc,l,el,hlc,l96,l97,lf⟩ := WordLength.executes 96 97 (by omega) input tape n.bits no co s hnw hcw
  have keep (i : ℕ) (hi : i ≠ 97) : l.val.tapes i = s.val.tapes i := by
    by_cases he : i = 96
    · subst i; exact l96.trans hnw.symm
    · exact lf.2.2.2.2.2.1 i he hi
  have cfgL : Config layout [] clock l.val :=
    ⟨BankArray.word_of_eq (keep 80 (by omega)) cfg.width,
     BankArray.word_of_eq (keep 81 (by omega)) cfg.index,
     BankArray.word_of_eq (keep 82 (by omega)) cfg.oldJump,
     BankArray.word_of_eq (keep 83 (by omega)) cfg.clock,
     BankArray.word_of_eq (keep 84 (by omega)) cfg.oldMinimum,
     BankArray.word_of_eq (keep 85 (by omega)) cfg.newJump,
     BankArray.word_of_eq (keep 86 (by omega)) cfg.newMinimum⟩
  have workL : Workspace l.val := by
    rcases work with ⟨⟨w0,w1,w2,w3,w5,w6,w8,w9⟩,w7,wp⟩
    refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
    all_goals first
    | exact RationalAccumulator.blank_of_eq (keep _ (by omega)) (by assumption)
    | exact fun i hi => RationalAccumulator.blank_of_eq (keep i (by simp_all [Private]; omega)) (wp i hi)
  have repL : Represents layout l.val.memory saved output := by simpa only [lf.2.2.1] using rep
  obtain ⟨rc,t,out,hrc,er,cfgT,workT,t94,t95,t97,t96,repT,tf,tmemory⟩ :=
    rounds_executes input tape layout saved output clock n.bits.length hw hn hclock hsep co l l97
      ⟨no,l96⟩ (RationalAccumulator.blank_of_eq (keep 94 (by omega)) h94)
      (RationalAccumulator.blank_of_eq (keep 95 (by omega)) h95) cfgL workL repL
  refine ⟨lc+rc,t,out,by dsimp [computedCost]; omega,el.seq er,cfgT,workT,t94,t95,t97,t96,repT,?_,by simpa only [lf.2.2.1] using tmemory⟩
  refine ⟨tf.1.trans lf.2.1,tf.2.1.trans lf.2.2.2.1,tf.2.2.1.trans lf.2.2.2.2.1,
    fun i hi hp h97' => (tf.2.2.2.1 i hi hp h97').trans (keep i h97'),?_⟩
  intro i hi hr
  exact (tf.2.2.2.2 i hi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    (lf.2.2.2.2.2.2 i hr)

theorem computed_run {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved output : State n) (clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hclock : clock.length = layout.width) (hsep : layout.PingPong n)
    (s : Store) (hnword : BankArray.Word s.val 96 n.bits)
    (h94 : Blank s.val 94) (h95 : Blank s.val 95) (h97 : Blank s.val 97)
    (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory saved output) :
    ∃ t : Store, ∃ finalOutput,
      (runPriced (computedCode.compile.next input tape) (computedCost layout n+1) s.val).finished =
        some (t.place computedCode.size) ∧
      (runPriced (computedCode.compile.next input tape) (computedCost layout n+1) s.val).instructions ≤ computedCost layout n ∧
      Config (layoutAfter layout n.bits.length) [] clock t.val ∧ Workspace t.val ∧
      Blank t.val 94 ∧ Blank t.val 95 ∧ Blank t.val 97 ∧ BankArray.Word t.val 96 n.bits ∧
      Represents (layoutAfter layout n.bits.length) t.val.memory (stateAfter saved n.bits.length) finalOutput ∧
      CompleteFrame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨cost,t,out,hcost,he,ht⟩ := computed_executes input tape layout saved output clock
    hw hn hclock hsep s hnword h94 h95 h97 cfg work rep
  have hr := he.compiled_run (computedCost layout n+1) (by omega)
  exact ⟨t,out,hr.1,hr.2.symm ▸ hcost,ht⟩

/-- The stored minimum bits after this program are the true finite-cycle
minima, using the computed binary-size iteration count. -/
theorem computed_minimum {n : ℕ} (layout : Layout) (p : Equiv.Perm (Fin n))
    (memory : ℕ → Bool) (output : State n) (hn : n ≤ 2^layout.width)
    (rep : Represents (layoutAfter layout n.bits.length) memory
      (stateAfter (Doubling.initial (Equiv.refl (Fin n)) p) n.bits.length) output) (i : Fin n) :
    addressValue (MemoryWord.readBits memory
      ((layoutAfter layout n.bits.length).oldMinimum+i.val*layout.width) layout.width) =
      (CycleColor.orbitMin p i).val := by
  have hr := rep.oldMinimum.read i
  rw [layoutAfter_width,words_get] at hr
  have hv := lt_of_lt_of_le
    ((stateAfter (Doubling.initial (Equiv.refl (Fin n)) p) n.bits.length).minimum.get i).isLt hn
  rw [hr,IncidenceEncoding.word_value _ _ hv]
  have hsize : n ≤ 2^n.bits.length := by
    exact Nat.le_of_lt (by simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self n)
  have hm := Doubling.run_minimum_eq_orbitMin (Equiv.refl (Fin n)) p n.bits.length hsize i
  simpa only [stateAfter_run,Doubling.minAt,Equiv.refl_apply] using congrArg Fin.val hm

end Maxwell.Cost.DoublingPass
