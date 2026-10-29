import Maxwell.Cost.PositiveGraph.Initialize.Loop

namespace Maxwell.Cost.PositiveGraph.Initialize
open Structured
open RationalAccumulator (Blank)

def fillCode (p : Ports) : Code := .seq (.call (WordTransfer.clone p.count 161)) (loopCode p)
def fillCost (n B : ℕ) : ℕ := 22000*(n+1)*(B+2)^2

theorem fill_executes (p : Ports) (width base clock : List Bool) (n value B : ℕ)
    (hw : width.length ≤ B) (hb : base.length ≤ B) (hnb : n.bits.length ≤ B)
    (hwp : 0<width.length) (hvp : 0<addressValue width) (hv : addressValue width ≤ B)
    (hc : clock.length=addressValue width) (hfit : value.bits.length ≤ addressValue width)
    (hn : n<2^B) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hr : Ready p width base clock value s.val) (h160 : Blank s.val 160) (h161 : Blank s.val 161)
    (hcount : RationalAccumulator.Word s.val p.count n) :
    ∃ cost t, cost ≤ fillCost n B ∧ Executes input tape (fillCode p) cost s t ∧
      Ready p width base clock value t.val ∧ Blank t.val 160 ∧ Blank t.val 161 ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width)
        (Vector.ofFn fun _ : Fin n => FixedWidth.bits (addressValue width) value.bits) ∧
      Outside (addressValue base) (addressValue width) n s.val t.val ∧ Frame s.val t.val := by
  have pc := p.valid p.count (by simp)
  obtain ⟨co,hco⟩ := hcount
  obtain ⟨io,hio⟩ := h161
  obtain ⟨a,ea,hat,af⟩ := WordCall.clone p.count 161 (by omega) input tape n.bits co io s hco hio
  have keep (j : ℕ) (hj : j ≠ 161) : a.val.tapes j=s.val.tapes j := by simp [hat,hj]
  have ar : Ready p width base clock value a.val := ready_transfer p width base clock value
    s.val a.val hr (fun j _ hj => keep j hj)
  have a160 : BankArray.Word a.val 160 [] := by
    have hz := (RationalAccumulator.zero_word_iff_blank s.val 160).mpr h160
    exact BankArray.word_of_eq (keep 160 (by omega)) hz
  have aa : BitArray.Represents a.val.memory (addressValue base) (addressValue width)
      (snapshot s.val.memory (addressValue base) (addressValue width) n) := by
    rw [af.2.2.1]
    exact snapshot_represents _ _ _ _
  obtain ⟨lc,t,hlc,et,ht⟩ := loop_executes p width base clock [] n.bits value B
    (snapshot s.val.memory (addressValue base) (addressValue width) n)
    hw hb (by simp) hnb hwp hvp hv hc hfit hn rfl (addressValue_bits n) input tape io a
    ar a160 (by simp [hat]) aa
  obtain ⟨tr,t160,t161,ta,hto,tf⟩ := ht
  have fa : Frame s.val a.val := ⟨af.2.1,af.2.2.2.1,af.2.2.2.2.1,
    fun j _ _ _ hj _ => keep j hj,
    fun j _ h24 h25 h26 h27 _ _ => af.2.2.2.2.2.2 j h24 h25 h26 h27⟩
  refine ⟨15*n.bits.length+17+lc,t,?_,ea.seq et,tr,t160,t161,ta,
    (Outside.of_memory af.2.2.1).trans hto,fa.trans tf⟩
  dsimp [loopCost] at hlc
  dsimp [fillCost]
  have hq : B+2 ≤ (B+2)^2 := Nat.le_self_pow (by decide) _
  nlinarith

end Maxwell.Cost.PositiveGraph.Initialize
