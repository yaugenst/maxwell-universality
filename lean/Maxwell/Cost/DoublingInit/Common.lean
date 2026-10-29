import Maxwell.Cost.DoublingInit.Encoding

namespace Maxwell.Cost.DoublingInit
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

structure Config (layout : Layout) (index clock : List Bool) (s : BitRAMState) : Prop where
  route : DoublingPass.Config layout.route index clock s
  inputA : Word s 98 layout.inputA.bits
  inputB : Word s 99 layout.inputB.bits

def Private (i : ℕ) : Prop := i = 37 ∨ DoublingPass.Private i

def Frame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → ¬Private i → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨hi,hr,ho,ht,hg⟩
  rcases k with ⟨ki,kr,ko,kt,kg⟩
  exact ⟨ki.trans hi,kr.trans hr,ko.trans ho,
    fun i hi hp => (kt i hi hp).trans (ht i hi hp),
    fun i hi h24 h25 h26 h27 h28 h29 =>
      (kg i hi h24 h25 h26 h27 h28 h29).trans (hg i hi h24 h25 h26 h27 h28 h29)⟩

theorem Frame.of_bank {s t : BitRAMState} (h : BankArray.Frame s t) : Frame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi _ => h.2.2.2.1 i hi,h.2.2.2.2⟩

theorem Frame.of_except {bank : ℕ} {s t : BitRAMState}
    (hb : Private bank) (h : BankArray.FrameExcept bank s t) : Frame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi hp => h.2.2.2.1 i hi (by intro he; exact hp (he ▸ hb)),h.2.2.2.2⟩

theorem Frame.of_clear {bank : ℕ} {s t : BitRAMState}
    (hb : Private bank) (h : TapeOps.Frame bank bank s t) : Frame s t :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i _ hp => h.2.2.2.2.2.1 i (by intro he; exact hp (he ▸ hb)) (by intro he; exact hp (he ▸ hb)),
    fun i _ _ _ h26 h27 _ _ => h.2.2.2.2.2.2 i h26 h27⟩

theorem Config.of_frame {layout : Layout} {index clock : List Bool}
    {s t : BitRAMState} (h : Frame s t) (c : Config layout index clock s) : Config layout index clock t := by
  have keep (i : ℕ) (hi : i = 4 ∨ 10 ≤ i) (hp : ¬Private i) := h.2.2.2.1 i hi hp
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · exact BankArray.word_of_eq (keep 80 (by omega) (by simp [Private,DoublingPass.Private])) c.route.width
  · exact BankArray.word_of_eq (keep 81 (by omega) (by simp [Private,DoublingPass.Private])) c.route.index
  · exact BankArray.word_of_eq (keep 82 (by omega) (by simp [Private,DoublingPass.Private])) c.route.oldJump
  · exact BankArray.word_of_eq (keep 83 (by omega) (by simp [Private,DoublingPass.Private])) c.route.clock
  · exact BankArray.word_of_eq (keep 84 (by omega) (by simp [Private,DoublingPass.Private])) c.route.oldMinimum
  · exact BankArray.word_of_eq (keep 85 (by omega) (by simp [Private,DoublingPass.Private])) c.route.newJump
  · exact BankArray.word_of_eq (keep 86 (by omega) (by simp [Private,DoublingPass.Private])) c.route.newMinimum
  · exact BankArray.word_of_eq (keep 98 (by omega) (by simp [Private,DoublingPass.Private])) c.inputA
  · exact BankArray.word_of_eq (keep 99 (by omega) (by simp [Private,DoublingPass.Private])) c.inputB

def Workspace (s : BitRAMState) : Prop := DoublingPass.Workspace s ∧ Blank s 37

def budget (layout : Layout) (index : List Bool) : ℕ :=
  DoublingPass.budget layout.route index + layout.inputA.bits.length+layout.inputB.bits.length

theorem array_cost_bound (layout : Layout) (index lookup payload : List Bool) (base : ℕ)
    (hl : lookup.length ≤ budget layout index) (hb : base.bits.length ≤ budget layout index)
    (hp : payload.length ≤ layout.route.width) :
    BankArray.costCap layout.route.width.bits lookup base.bits payload ≤ 30000*(budget layout index+1)^2 := by
  apply IncidencePass.array_cost_le
  · dsimp [budget,DoublingPass.budget]; omega
  · exact hl
  · exact hb
  · dsimp [budget,DoublingPass.budget]; omega
  · simp only [addressValue_bits]; dsimp [budget,DoublingPass.budget]; omega

end Maxwell.Cost.DoublingInit
