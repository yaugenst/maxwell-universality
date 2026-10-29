import Maxwell.Cost.SparseEmission.ReadSelector
import Maxwell.Cost.SparseEmission.Entry

namespace Maxwell.Cost.SparseEmission.Selector
open Structured

def code : Code := .seq ReadSelector.code (Entry.code 112 false false)
def work : Finset ℕ := {105,110,111,112,114}

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (row parent pre clock preceding : List Bool) (origin rowOrigin clockOrigin : ℤ) (s : Store)
    (hp : parent.length = row.length) (hc : clock.length = row.length)
    (h105 : s.val.tapes 105 = BitTape.atEnd (pre++parent))
    (h110 : s.val.tapes 110 = BitTape.shifted preceding origin)
    (h111 : s.val.tapes 111 = BitTape.blank) (h112 : s.val.tapes 112 = BitTape.blank)
    (h114 : s.val.tapes 114 = BitTape.blank)
    (hrow : s.val.tapes 113 = BitTape.shifted row rowOrigin)
    (hclock : s.val.tapes 93 = BitTape.shifted clock clockOrigin) :
    ∃ t, Executes input randomTape code (82*row.length+79) s t ∧
      t.val.tapes 105 = BitTape.atEnd pre ∧
      t.val.tapes 110 = BitTape.shifted (row++parent++[false,false]++preceding)
        (origin-(2*row.length+2)) ∧
      t.val.tapes 111 = BitTape.blank ∧ t.val.tapes 112 = BitTape.blank ∧ t.val.tapes 114 = BitTape.blank ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      SourceCircuit.Frame work s.val t.val ∧
      (∀ i, i ∉ work → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨a,ea,a105,a111,a112,aa,am,af,ak⟩ := ReadSelector.executes input randomTape parent pre clock
    clockOrigin s (hc.trans hp.symm) h105 h111 h112 hclock
  obtain ⟨t,et,t110,t112,t114,ta,tm,tf,tk⟩ := Entry.executes 112 (Or.inr rfl) false false
    input randomTape row parent clock preceding origin rowOrigin clockOrigin a hp hc
    ((ak 110 (by decide)).trans h110) ((ak 113 (by decide)).trans hrow) a112
    ((ak 93 (by decide)).trans hclock) ((ak 114 (by decide)).trans h114)
  refine ⟨t,?_,(tk 105 (by decide)).trans a105,t110,(tk 111 (by decide)).trans a111,t112,t114,
    ta.trans aa,tm.trans am,(af.mono (by decide)).trans (tf.mono (by decide)),?_⟩
  · convert ea.seq et using 1 <;> first | rfl | omega
  · intro i hi
    exact (tk i (by simp_all [work,Entry.work])).trans (ak i (by simp_all [work,ReadSelector.work]))

end Maxwell.Cost.SparseEmission.Selector
