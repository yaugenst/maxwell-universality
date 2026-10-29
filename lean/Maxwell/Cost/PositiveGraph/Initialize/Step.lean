import Maxwell.Cost.PositiveGraph.Initialize.Common

namespace Maxwell.Cost.PositiveGraph.Initialize
open Structured
open RationalAccumulator (Blank)

private theorem Ports.width_range (p : Ports) : 140 ≤ p.width ∧ p.width ≤ 154 := p.valid _ (by simp)
private theorem Ports.base_range (p : Ports) : 140 ≤ p.base ∧ p.base ≤ 154 := p.valid _ (by simp)
private theorem Ports.clock_range (p : Ports) : 140 ≤ p.clock ∧ p.clock ≤ 154 := p.valid _ (by simp)

def rowCode (p : Ports) : Code :=
  .seq (BankArray.writeCanonicalCode p.width 160 p.base p.clock 162) (BankArray.incrementCode 160)

theorem row {n : ℕ} (p : Ports) (width base clock index : List Bool) (value B : ℕ)
    (words : Vector (List Bool) n) (i : Fin n)
    (hw : width.length ≤ B) (hb : base.length ≤ B) (hi : index.length ≤ B)
    (hwp : 0<width.length) (hvp : 0<addressValue width) (hv : addressValue width ≤ B)
    (hc : clock.length=addressValue width) (hfit : value.bits.length ≤ addressValue width)
    (hn : n<2^B) (hindex : addressValue index=i.val)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hr : Ready p width base clock value s.val) (h160 : BankArray.Word s.val 160 index)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words) :
    ∃ cost t, cost ≤ 20000*(B+2)^2 ∧ Executes input tape (rowCode p) cost s t ∧
      Ready p width base clock value t.val ∧
      BankArray.Word t.val 160 (Increment.bits index) ∧ (Increment.bits index).length ≤ B ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width)
        (words.set i (FixedWidth.bits (addressValue width) value.bits)) ∧
      Outside (addressValue base) (addressValue width) n s.val t.val ∧ Frame s.val t.val ∧
      t.val.tapes 161=s.val.tapes 161 := by
  have pw := p.width_range
  have pb := p.base_range
  have pc := p.clock_range
  obtain ⟨ac,a,hac,ea,am,aa,asc,a7,a37,af⟩ := BankArray.write_canonical
    p.width 160 p.base p.clock 162 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) input tape width index base clock words i value
    hwp hindex hc hvp hfit s hr.scratch hr.seven hr.temporary hr.widthWord h160 hr.baseWord
    hr.clockWord hr.valueWord harray
  have a160 : BankArray.Word a.val 160 index := BankArray.word_of_eq
    (af.2.2.2.1 160 (by omega) (by omega)) h160
  obtain ⟨bc,t,hbc,eb,t160,ts,tm,_ta,tk,tf⟩ := BankArray.increment_bank 160 (by omega)
    input tape index a a160 asc
  have keep (j : ℕ) (hj : j=4 ∨ 10 ≤ j) (h37 : j ≠ 37) (h160 : j ≠ 160) :
      t.val.tapes j=s.val.tapes j := (tk j h160).trans (af.2.2.2.1 j hj h37)
  refine ⟨ac+bc,t,(Nat.add_le_add hac hbc).trans (write_cost_le width index base value B hw hi hb hv),
    ea.seq eb,?_,t160,?_,?_,?_,(Frame.of_bank (Or.inl rfl) af).trans
      (Frame.of_bank (Or.inr (Or.inl rfl)) tf),keep 161 (by omega) (by omega) (by omega)⟩
  · exact ⟨ts,RationalAccumulator.blank_of_eq (tk 7 (by omega)) a7,
      RationalAccumulator.blank_of_eq (tk 37 (by omega)) a37,
      BankArray.word_of_eq (keep p.width (by omega) (by omega) (by omega)) hr.widthWord,
      BankArray.word_of_eq (keep p.base (by omega) (by omega) (by omega)) hr.baseWord,
      BankArray.word_of_eq (keep p.clock (by omega) (by omega) (by omega)) hr.clockWord,
      RationalAccumulator.word_of_eq (keep 162 (by omega) (by omega) (by omega)) hr.valueWord⟩
  · apply BankArray.increment_length_bound index B hi
    rw [hindex]
    omega
  · simpa only [tm] using aa
  · intro addr ha
    rw [tm,am]
    apply MemoryWord.writeBits_outside
    simp only [FixedWidth.bits_length]
    rcases ha with ha | ha
    · left; omega
    · right
      have him := Nat.mul_le_mul_right (addressValue width) (show i.val+1 ≤ n by omega)
      simp only [Nat.add_mul,Nat.one_mul] at him
      omega

end Maxwell.Cost.PositiveGraph.Initialize
