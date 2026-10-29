import Maxwell.Cost.WeightedSource.WeightSetup

namespace Maxwell.Cost.WeightedSource.Weight
open Structured RationalAccumulator

/-- Full external frame, including the caller's sign register358. -/
def Frame (s t : BitRAMState) : Prop :=
  t.address=s.address  ∧  t.inputHead=s.inputHead  ∧  t.memory=s.memory  ∧ 
  t.randomCursor=s.randomCursor  ∧  t.output=s.output  ∧ 
  (∀ i, (4 ≤ i  ∧  i<30  ∨  37 ≤ i  ∧  i ≠ 40) → i ≠ 410 → i ≠ 411 → t.tapes i=s.tapes i)  ∧ 
  (∀ i, 36 ≤ i → t.registers i=s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1,k.2.2.2.2.1.trans h.2.2.2.2.1,
    fun i hi h410 h411 => (k.2.2.2.2.2.1 i hi h410 h411).trans (h.2.2.2.2.2.1 i hi h410 h411),
    fun i hi => (k.2.2.2.2.2.2 i hi).trans (h.2.2.2.2.2.2 i hi)⟩

theorem Frame.of_loop {s t : BitRAMState} (h : DyadicSqrt.LoopFrame s t) : Frame s t :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,fun i hi _ _=>h.2.2.2.2.2.1 i hi,h.2.2.2.2.2.2⟩

def exportCode : Code := .seq (.call (WordTransfer.clone 32 410))
  (.seq (.call (WordTransfer.clone 33 411)) RationalNormalize.clearAllCode)

theorem export_executes (input : List Bool) (tape : ℕ→Bool) (v : ℕ→ℕ) (W : ℕ)
    (hv : DyadicSqrt.Width v W) (s : Store) (hb : Bank s.val v) (hr : Scratch s.val 0)
    (h410 : Blank s.val 410) (h411 : Blank s.val 411) :
    ∃ cost t, cost ≤ 100*(W+1)  ∧  Executes input tape exportCode cost s t  ∧ 
      Word t.val 410 (v 32)  ∧  Word t.val 411 (v 33)  ∧  Bank t.val (fun _=>0)  ∧ 
      Scratch t.val 0  ∧  t.val.tapes 40=s.val.tapes 40  ∧  Frame s.val t.val := by
  obtain ⟨o32,h32⟩ := hb 32 (by decide) (by decide)
  obtain ⟨o410,h410⟩ := h410
  obtain ⟨a,ea,ha,fa⟩ := WordCall.clone 32 410 (by decide) input tape (v 32).bits o32 o410 s h32 h410
  have keepa (i : ℕ) (hi : i ≠ 410) : a.val.tapes i=s.val.tapes i := by simp [ha,hi]
  obtain ⟨o33,h33⟩ := word_of_eq (keepa 33 (by decide)) (hb 33 (by decide) (by decide))
  obtain ⟨o411,ha411⟩ := blank_of_eq (keepa 411 (by decide)) h411
  obtain ⟨b,eb,hbt,fb⟩ := WordCall.clone 33 411 (by decide) input tape (v 33).bits o33 o411 a h33 ha411
  have keepb (i : ℕ) (hi : i ≠ 410) (hj : i ≠ 411) : b.val.tapes i=s.val.tapes i := by simp [hbt,ha,hi,hj]
  have bb : Bank b.val v := fun i hi hi' => word_of_eq (keepb i (by omega) (by omega)) (hb i hi hi')
  have rb : Scratch b.val 0 :=
    ⟨blank_of_eq (keepb 0 (by decide) (by decide)) hr.1,
      word_of_eq (keepb 1 (by decide) (by decide)) hr.2.1,
      blank_of_eq (keepb 2 (by decide) (by decide)) hr.2.2.1,
      blank_of_eq (keepb 3 (by decide) (by decide)) hr.2.2.2⟩
  obtain ⟨c,t,hc,et,bt,rt,ft⟩ := RationalNormalize.clear_all input tape v W hv b bb rb
  refine ⟨15*(v 32).bits.length+17+(15*(v 33).bits.length+17+c),t,?_,ea.seq (eb.seq et),?_,?_,bt,rt,?_,?_⟩
  · have h32b := hv 32 (by decide) (by decide)
    have h33b := hv 33 (by decide) (by decide)
    omega
  · exact word_of_eq (ft.2.2.2.2.2.1 410 (by decide)) ⟨o410,by simp [hbt,ha]⟩
  · exact word_of_eq (ft.2.2.2.2.2.1 411 (by decide)) ⟨o411,by simp [hbt]⟩
  · exact (ft.2.2.2.2.2.1 40 (by decide)).trans (keepb 40 (by decide) (by decide))
  · refine ⟨ft.1.trans (fb.1.trans fa.1),ft.2.1.trans (fb.2.1.trans fa.2.1),
      ft.2.2.1.trans (fb.2.2.1.trans fa.2.2.1),ft.2.2.2.1.trans (fb.2.2.2.1.trans fa.2.2.2.1),
      ft.2.2.2.2.1.trans (fb.2.2.2.2.1.trans fa.2.2.2.2.1),?_,?_⟩
    · intro i hi h410 h411
      exact (ft.2.2.2.2.2.1 i (by omega)).trans (keepb i h410 h411)
    · intro i hi
      exact (ft.2.2.2.2.2.2 i hi).trans
        ((fb.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)).trans
          (fa.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)))

end Maxwell.Cost.WeightedSource.Weight
