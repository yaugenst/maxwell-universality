import Maxwell.Cost.DoublingInit.Common

namespace Maxwell.Cost.DoublingInit
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

private theorem read_one {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (index clock lookup : List Bool) (values : Vector (Fin n) n)
    (base indexBank baseBank target : ℕ) (j : Fin n)
    (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank) (ht : DoublingPass.Private target)
    (hw : 0 < layout.route.width) (hl : addressValue lookup = j.val) (hc : clock.length = layout.route.width)
    (hll : lookup.length ≤ budget layout index) (hbl : base.bits.length ≤ budget layout index)
    (s : Store) (cfg : Config layout index clock s.val) (scratch : BankArray.Scratch s.val)
    (empty7 : Blank s.val 7) (emptyTarget : Blank s.val target)
    (hlookup : Word s.val indexBank lookup) (hbase : Word s.val baseBank base.bits)
    (harray : BitArray.Represents s.val.memory base layout.route.width (DoublingPass.words layout.route.width values)) :
    ∃ cost t, cost ≤ 35000*(budget layout index+1)^2 ∧
      Executes input tape (BankArray.readBankCode 80 indexBank baseBank 83 target) cost s t ∧
      Word t.val target (IncidenceEncoding.word layout.route.width (values.get j).val) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ t.val.memory=s.val.memory ∧
      Config layout index clock t.val ∧ BankArray.FrameExcept target s.val t.val := by
  obtain ⟨cost,t,hcost,he,hword,hs,h7,hm,_,hf⟩ := BankArray.read_bank
    80 indexBank baseBank 83 target (by omega) hi hb (by omega) (by dsimp [DoublingPass.Private] at ht; omega)
    input tape layout.route.width.bits lookup base.bits clock (DoublingPass.words layout.route.width values) j
    (RationalAccumulator.bits_nonempty hw) hl (by simpa using hc) s scratch empty7 emptyTarget
    cfg.route.width hlookup hbase cfg.route.clock (by simpa using harray)
  refine ⟨cost,t,?_,he,by simpa using hword,hs,h7,hm,cfg.of_frame (Frame.of_except (Or.inr ht) hf),hf⟩
  have hcap := array_cost_bound layout index lookup clock base hll hbl (by omega)
  have hwidth : layout.route.width ≤ budget layout index := by dsimp [budget,DoublingPass.budget]; omega
  simp only [addressValue_bits] at hcost
  nlinarith

def readCode : Code := .seq (BankArray.readBankCode 80 81 99 83 88) (BankArray.readBankCode 80 88 98 83 89)

theorem read_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (a b : Equiv.Perm (Fin n)) (i : Fin n) (index clock : List Bool)
    (hw : 0 < layout.route.width) (hn : n ≤ 2^layout.route.width)
    (hi : addressValue index=i.val) (hc : clock.length=layout.route.width)
    (s : Store) (cfg : Config layout index clock s.val) (work : Workspace s.val)
    (ra : BitArray.Represents s.val.memory layout.inputA layout.route.width (DoublingPass.words layout.route.width (permutation a)))
    (rb : BitArray.Represents s.val.memory layout.inputB layout.route.width (DoublingPass.words layout.route.width (permutation b))) :
    ∃ cost t, cost ≤ 70000*(budget layout index+1)^2 ∧ Executes input tape readCode cost s t ∧
      Word t.val 88 (IncidenceEncoding.word layout.route.width (b i).val) ∧
      Word t.val 89 (IncidenceEncoding.word layout.route.width (a (b i)).val) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      (∀ k, k=37 ∨ (90≤k ∧ k≤92) → Blank t.val k) ∧
      t.val.memory=s.val.memory ∧ Config layout index clock t.val ∧ Frame s.val t.val := by
  obtain ⟨bc,bstate,hbc,eb,b88,bss,b7,bm,bcfg,bf⟩ := read_one input tape layout index clock index
    (permutation b) layout.inputB 81 99 88 i (by omega) (by omega) (by simp [DoublingPass.Private])
    hw hi hc (by dsimp [budget,DoublingPass.budget]; omega) (by dsimp [budget]; omega)
    s cfg work.1.1 work.1.2.1 (work.1.2.2 88 (by simp [DoublingPass.Private])) cfg.route.index cfg.inputB rb
  have b88' : Word bstate.val 88 (IncidenceEncoding.word layout.route.width (b i).val) := by simpa using b88
  obtain ⟨ac,t,hac,ea,t89,tss,t7,tm,tcfg,tf⟩ := read_one input tape layout index clock
    (IncidenceEncoding.word layout.route.width (b i).val) (permutation a) layout.inputA 88 98 89 (b i)
    (by omega) (by omega) (by simp [DoublingPass.Private]) hw
    (IncidenceEncoding.word_value _ _ ((b i).isLt.trans_le hn)) hc
    (by simp only [IncidenceEncoding.word_length]; dsimp [budget,DoublingPass.budget]; omega)
    (by dsimp [budget]; omega) bstate bcfg bss b7
    (RationalAccumulator.blank_of_eq (bf.2.2.2.1 89 (by omega) (by omega)) (work.1.2.2 89 (by simp [DoublingPass.Private])))
    b88' bcfg.inputA (by simpa only [bm] using ra)
  refine ⟨bc+ac,t,by omega,eb.seq ea,
    BankArray.word_of_eq (tf.2.2.2.1 88 (by omega) (by omega)) b88',by simpa using t89,tss,t7,?_,
    tm.trans bm,tcfg,(Frame.of_except (by simp [Private,DoublingPass.Private]) bf).trans
      (Frame.of_except (by simp [Private,DoublingPass.Private]) tf)⟩
  intro k hk
  apply RationalAccumulator.blank_of_eq
    ((tf.2.2.2.1 k (by omega) (by omega)).trans (bf.2.2.2.1 k (by omega) (by omega)))
  rcases hk with rfl | hk
  · exact work.2
  · exact work.1.2.2 k (by dsimp [DoublingPass.Private]; omega)

end Maxwell.Cost.DoublingInit
