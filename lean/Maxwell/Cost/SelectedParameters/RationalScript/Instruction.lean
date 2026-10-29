import Maxwell.Cost.SelectedParameters.RationalScript.Literal

namespace Maxwell.Cost.SelectedParameters.RationalScript
open Structured Rational

theorem Instruction.update_clean (a : Instruction) (v : ℕ → ℕ) : Clean (a.update v) :=
  fun i hi => after_common v a.numerator a.denominator (a.result v) i hi

theorem Instruction.nextWidth_ge (a : Instruction) (B : ℕ) : B ≤ a.nextWidth B := by
  cases a with | mk op num den => cases op <;> dsimp [nextWidth] <;> nlinarith

theorem Instruction.nextWidth_growth (a : Instruction) (B : ℕ) :
    a.nextWidth B+2 ≤ a.growth*(B+2) := by
  cases a with | mk op num den => cases op <;> dsimp [nextWidth,growth] <;> nlinarith

theorem Instruction.width (extra : Finset ℕ) (a : Instruction) (hv : a.Valid extra)
    (v : ℕ → ℕ) (B : ℕ) (hw : ∀ i ∈ ids extra, (v i).bits.length ≤ B) :
    ∀ i ∈ ids extra, (a.update v i).bits.length ≤ a.nextWidth B := by
  rcases a with ⟨op,num,den⟩
  rcases hv with ⟨_,_,_,ports⟩
  apply after_width extra v num den _ B _ hw (Instruction.nextWidth_ge _ B)
  have hp (i : ℕ) (hi : i ∈ extra) := hw i (Finset.mem_union_left _ hi)
  cases op with
  | literal n d => dsimp [Instruction.result,Instruction.nextWidth]; constructor <;> omega
  | basic op a b c d =>
    exact pair_width op (v a) (v b) (v c) (v d) B
      (hp a ports.1) (hp b ports.2.1) (hp c ports.2.2.1) (hp d ports.2.2.2)
  | choice op a b c d =>
    exact choice_width op (v a) (v b) (v c) (v d) B
      (hp a ports.1) (hp b ports.2.1) (hp c ports.2.2.1) (hp d ports.2.2.2)
  | power k a b =>
    have h := power_width k (v a) (v b) B (hp a ports.1) (hp b ports.2.1)
    dsimp [Instruction.result,Instruction.nextWidth]
    constructor <;> nlinarith [h.1,h.2]

theorem instruction_executes (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i)
    (a : Instruction) (hv : a.Valid extra) (v : ℕ → ℕ) (B : ℕ)
    (hw : ∀ i ∈ ids extra, (v i).bits.length ≤ B) (he : a.Enabled v) (hc : Clean v)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank (ids extra) v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape a.code cost s t ∧ cost ≤ a.coefficient*(B+2)^2 ∧
      NatAssign.Bank (ids extra) (a.update v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (Rational.workspace a.numerator a.denominator) s.val t.val := by
  rcases a with ⟨op,num,den⟩
  rcases hv with ⟨hn,hd,hne,ports⟩
  cases op with
  | literal n d => exact literal_executes extra hextra num den n d hn hd v B hw input tape s hb hs
  | basic op a b c d =>
    exact basic_executes extra hextra op a b c d num den
      ports.1 ports.2.1 ports.2.2.1 ports.2.2.2 hn hd hne v B hw input tape s hb hs
  | choice op a b c d =>
    obtain ⟨cost,t,et,hcost,ht,hst,hf⟩ := choice_executes extra hextra op a b c d num den
      ports.1 ports.2.1 ports.2.2.1 ports.2.2.2 hn hd hne v B hw he.1 he.2
      (hc 35 (by simp [common])) (hc 36 (by simp [common])) input tape s hb hs
    refine ⟨cost,t,et,hcost.trans ?_,ht,hst,hf⟩
    have hq : 1 ≤ (B+2)^2 := Nat.one_le_pow _ _ (by omega)
    dsimp [choiceCostBound,Instruction.coefficient]
    nlinarith
  | power k a b =>
    obtain ⟨cost,t,et,hcost,ht,hst,hf⟩ := power_executes extra hextra k a b num den
      ports.1 ports.2.1 hn hd ports.2.2.1 ports.2.2.2.1 ports.2.2.2.2.1 ports.2.2.2.2.2
      hne v B hw input tape s hb hs
    refine ⟨cost,t,et,hcost.trans ?_,ht,hst,hf⟩
    have hq : (B+3)^2 ≤ 4*(B+2)^2 := by
      calc
        (B+3)^2 ≤ (2*(B+2))^2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4*(B+2)^2 := by ring
    calc
      powerCostBound k B = 3000*8^(2*k+9)*(B+3)^2 := rfl
      _  ≤  3000*8^(2*k+9)*(4*(B+2)^2) := Nat.mul_le_mul_left _ hq
      _ = _ := by dsimp [Instruction.coefficient]; ring

end Maxwell.Cost.SelectedParameters.RationalScript
