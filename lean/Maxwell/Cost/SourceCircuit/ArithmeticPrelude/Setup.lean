import Maxwell.Cost.SourceCircuit.ArithmeticReady
import Maxwell.Cost.SourceCircuit.AllocateSource.Correspondence

namespace Maxwell.Cost.SourceCircuit.ArithmeticPrelude
open Structured
open RationalAccumulator (Blank Word word_of_eq blank_of_eq)

def work : Finset ℕ := {24,85,98,100}

def code : Code := .seq (.call (TapeOps.clear 100))
  (.seq (.call (WordTransfer.clone 79 100))
    (.seq (.call (Rewind.program 85))
      (.seq (.call (Rewind.program 98)) (.call (Rewind.program 24)))))

def price (m : ℕ) (archive leaves flags : List Bool) : ℕ :=
  21*m.bits.length+4*(archive.length+leaves.length+flags.length)+39

theorem rewind (target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (bits : List Bool) (s : Store) (hs : s.val.tapes target = BitTape.atEnd bits) :
    ∃ t, Executes input tape (.call (Rewind.program target)) (4*bits.length+6) s t ∧
      t.val.tapes target = BitTape.ofList bits ∧ BinaryPrecision.Frame {target} s.val t.val := by
  have he := Rewind.atEnd_steps target input tape bits s.val s.property hs
  let t := Store.ofState (Rewind.finish target s.val)
  refine ⟨t,.call _ s _ _ he (by simp [Rewind.program,Rewind.finish]),
    Rewind.finish_tape target bits s.val hs,⟨rfl,rfl,rfl,rfl,rfl,?_⟩⟩
  intro i hi
  simp only [Finset.mem_singleton] at hi
  simp [t,Store.ofState,Rewind.finish,hi]

set_option maxRecDepth 8192 in
theorem setup (input : List Bool) (tape : ℕ → Bool) (m : ℕ)
    (archive leaves flags counter : List Bool) (co : ℤ) (s : Store)
    (hm : Word s.val 79 m) (h100 : s.val.tapes 100 = BitTape.shifted counter co)
    (hlen : counter.length = m.bits.length)
    (h85 : s.val.tapes 85 = BitTape.atEnd archive)
    (h98 : s.val.tapes 98 = BitTape.atEnd leaves)
    (h24 : s.val.tapes 24 = BitTape.atEnd flags) :
    ∃ t, Executes input tape code (price m archive leaves flags) s t ∧
      Word t.val 100 m ∧ t.val.tapes 85 = BitTape.ofList archive ∧
      t.val.tapes 98 = BitTape.ofList leaves ∧ t.val.tapes 24 = BitTape.ofList flags ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨a,ea,ta,fa⟩ := WordCall.clear 100 input tape counter co s h100
  have a79 : Word a.val 79 m := word_of_eq (by simp [ta]) hm
  obtain ⟨mo,hmo⟩ := a79
  obtain ⟨b,eb,tb,fb⟩ := WordCall.clone 79 100 (by decide) input tape m.bits mo
    (co+counter.length) a hmo (by simp [ta])
  have frame : BinaryPrecision.Frame work s.val b.val := by
    refine ⟨fb.1.trans fa.1,fb.2.1.trans fa.2.1,fb.2.2.1.trans fa.2.2.1,
      fb.2.2.2.1.trans fa.2.2.2.1,fb.2.2.2.2.1.trans fa.2.2.2.2.1,?_⟩
    intro i hi
    have hn : i ≠ 100 := by simp only [work,Finset.mem_insert,Finset.mem_singleton,not_or] at hi; omega
    simp [tb,ta,hn]
  have bkeep (i : ℕ) (hi : i ≠ 100) : b.val.tapes i = s.val.tapes i := by simp [tb,ta,hi]
  have b100 : Word b.val 100 m := ⟨co+counter.length,by simp [tb]⟩
  obtain ⟨c,ec,hc85,fc⟩ := rewind 85 input tape archive b ((bkeep 85 (by decide)).trans h85)
  obtain ⟨d,ed,hd98,fd⟩ := rewind 98 input tape leaves c
    ((fc.tapes 98 (by decide)).trans ((bkeep 98 (by decide)).trans h98))
  obtain ⟨t,et,ht24,ft⟩ := rewind 24 input tape flags d
    ((fd.tapes 24 (by decide)).trans ((fc.tapes 24 (by decide)).trans ((bkeep 24 (by decide)).trans h24)))
  refine ⟨t,?_,word_of_eq ((ft.tapes 100 (by decide)).trans
    ((fd.tapes 100 (by decide)).trans (fc.tapes 100 (by decide)))) b100,
    (ft.tapes 85 (by decide)).trans ((fd.tapes 85 (by decide)).trans hc85),
    (ft.tapes 98 (by decide)).trans hd98,ht24,
    frame.trans ((fc.mono (by decide)).trans ((fd.mono (by decide)).trans (ft.mono (by decide))))⟩
  convert ea.seq (eb.seq (ec.seq (ed.seq et))) using 1 <;> first | rfl | dsimp [price]; omega

theorem ready_transport {clock : List Bool} {p : ℕ} {d : ArithmeticPass.Data} {s t : Store}
    (h : ArithmeticPass.Ready clock p d s) (f : BinaryPrecision.Frame work s.val t.val) :
    ArithmeticPass.Ready clock p d t := by
  exact ⟨scratch_of_tapes h.scratch (fun j hj => f.tapes j (by
      simp only [work,Finset.mem_insert,Finset.mem_singleton,not_or]; omega)),
    blank_of_eq (f.tapes 7 (by decide)) h.blank7,
    blank_of_eq (f.tapes 94 (by decide)) h.blank94,
    blank_of_eq (f.tapes 96 (by decide)) h.blank96,
    blank_of_eq (f.tapes 99 (by decide)) h.blank99,
    (f.tapes 103 (by decide)).trans h.blank103,
    BankArray.word_of_eq (f.tapes 95 (by decide)) h.next,
    (f.tapes 97 (by decide)).trans h.gates,
    (f.tapes 104 (by decide)).trans h.terms,
    (f.tapes 105 (by decide)).trans h.outputs,
    BankArray.word_of_eq (f.tapes 106 (by decide)) h.counter,
    BankArray.word_of_eq (f.tapes 93 (by decide)) h.clock,
    BankArray.word_of_eq (f.tapes 82 (by decide)) h.power,
    (f.tapes 10 (by decide)).trans h.blank10,
    (f.tapes 15 (by decide)).trans h.blank15,
    (f.tapes 16 (by decide)).trans h.blank16,
    blank_of_eq (f.tapes 83 (by decide)) h.blank83⟩

end Maxwell.Cost.SourceCircuit.ArithmeticPrelude
