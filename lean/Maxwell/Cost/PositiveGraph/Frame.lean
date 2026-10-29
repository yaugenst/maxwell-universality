import Maxwell.Cost.PositiveGraph.CountStep
import Maxwell.Cost.PositiveGraph.DiagonalUpdate

namespace Maxwell.Cost.PositiveGraph

/-- The graph pass keeps every persistent descriptor outside its explicit
work banks. Its literal parser and four-bit update scratch registers are free. -/
structure Frame (changed : Finset ℕ) (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, (i = 4 ∨ 10 ≤ i) → i ∉ changed → t.tapes i = s.tapes i
  sign : t.registers 23 = s.registers 23
  control : ∀ i, 30 ≤ i → i ≠ 44 → i ≠ 45 → i ≠ 46 → i ≠ 47 →
    (i < 50 ∨ 55 < i) → t.registers i = s.registers i

theorem Frame.refl (changed : Finset ℕ) (s : BitRAMState) : Frame changed s s := by
  constructor <;> intros <;> rfl

theorem Frame.trans {changed : Finset ℕ} {s t u : BitRAMState}
    (h : Frame changed s t) (k : Frame changed t u) : Frame changed s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi hc => (k.tapes i hi hc).trans (h.tapes i hi hc),k.sign.trans h.sign,
    fun i a b c d e f => (k.control i a b c d e f).trans (h.control i a b c d e f)⟩

theorem Frame.mono {a b : Finset ℕ} {s t : BitRAMState} (h : Frame a s t) (hab : a ⊆ b) :
    Frame b s t :=
  ⟨h.inputHead,h.randomCursor,h.output,fun i hi hn => h.tapes i hi (fun hm => hn (hab hm)),
    h.sign,h.control⟩

theorem Frame.of_source {changed : Finset ℕ} {s t : BitRAMState} (h : SourceCircuit.Frame changed s t) :
    Frame changed s t :=
  ⟨h.inputHead,h.randomCursor,h.output,h.tapes,h.sign,fun i hi _ _ _ _ _ => h.control i hi⟩

theorem Frame.of_parse {s t : BitRAMState} (h : Parse.Frame s t) : Frame {110,111,112} s t :=
  ⟨h.inputHead,h.randomCursor,h.output,
    fun i _ hi => h.tapes i (by simp_all) (by simp_all) (by simp_all),h.sign,
    fun i a b c d _ _ => h.control i a b c d⟩

theorem Frame.of_diagonal {s t : BitRAMState} (h : DiagonalUpdate.Frame s t) : Frame {120} s t :=
  ⟨h.inputHead,h.randomCursor,h.output,fun i hi hn => h.tapes i hi (by simpa using hn),
    h.registers 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    fun i hi _ _ _ _ hr => h.registers i (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hr⟩

theorem Frame.of_transfer {source target : ℕ} {changed : Finset ℕ} {s t : BitRAMState}
    (h : WordTransfer.Frame source target s t)
    (ht : ∀ i ∉ changed, t.tapes i = s.tapes i) : Frame changed s t :=
  Frame.of_source (SourceCircuit.frame_transfer h ht)

end Maxwell.Cost.PositiveGraph
