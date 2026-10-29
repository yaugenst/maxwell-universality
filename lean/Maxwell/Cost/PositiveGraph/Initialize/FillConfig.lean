import Maxwell.Cost.PositiveGraph.Initialize.Config

namespace Maxwell.Cost.PositiveGraph.Initialize
open Structured
open RationalAccumulator (Word Blank)

theorem fill_config {W d K value : ℕ} {clock : List Bool}
    (p : Ports) (w b n B : ℕ) (c : List Bool)
    (hw : w.bits.length ≤ B) (hb : b.bits.length ≤ B) (hn : n.bits.length ≤ B)
    (hwp : 0<w) (hwb : w ≤ B) (hc : c.length=w) (hfit : value.bits.length ≤ w)
    (hnp : n<2^B) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Config W d K value clock s.val)
    (hwidth : Word s.val p.width w) (hbase : Word s.val p.base b)
    (hclock : BankArray.Word s.val p.clock c) (hcount : Word s.val p.count n) :
    ∃ cost t, cost ≤ fillCost n B ∧ Executes input tape (fillCode p) cost s t ∧
      Config W d K value clock t.val ∧
      BitArray.Represents t.val.memory b w (Vector.ofFn fun _ : Fin n => FixedWidth.bits w value.bits) ∧
      Outside b w n s.val t.val ∧ Frame s.val t.val := by
  have hpos : 0<w.bits.length := by
    by_contra h
    have hz : w.bits=[] := List.length_eq_zero_iff.mp (by omega)
    have hv := addressValue_bits w
    rw [hz] at hv
    change 0=w at hv
    omega
  obtain ⟨cost,t,hcost,he,hr,h160,h161,ha,ho,hf⟩ := fill_executes p w.bits b.bits c n value B
    hw hb hn hpos (by simpa only [addressValue_bits] using hwp)
    (by simpa only [addressValue_bits] using hwb) (by simpa only [addressValue_bits] using hc)
    (by simpa only [addressValue_bits] using hfit) hnp input tape s
    ⟨hs.scratch,hs.seven,hs.temporary,hwidth,hbase,hclock,hs.valueWord⟩ hs.cursor hs.count hcount
  exact ⟨cost,t,hcost,he,hs.after_fill p w.bits b.bits c hr h160 h161 hf,
    by simpa only [addressValue_bits] using ha,by simpa only [addressValue_bits] using ho,hf⟩

end Maxwell.Cost.PositiveGraph.Initialize
