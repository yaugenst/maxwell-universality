import Maxwell.Cost.RealSaddleBuffer.Memory

namespace Maxwell.Cost.RealSaddleBuffer
open RealSparseOrder (Buffer)

/-- Scratch-only instructions preserve all addressed record storage. -/
structure Scratch (s t : RAMState) : Prop where
  words : ∀ i, 1 ≤ i → t.words i = s.words i
  indices : ∀ i, 20 ≤ i → t.indices i = s.indices i
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput
  randomCursor : t.randomCursor = s.randomCursor

theorem Scratch.frame {s t : RAMState} (h : Scratch s t) (b : Buffer) (n : ℕ) : Frame b n s t :=
  ⟨fun i hi _ => h.words i hi, fun i hi _ => h.indices i hi, h.output, h.indexOutput, h.randomCursor⟩

theorem Frame.trans {b : Buffer} {n : ℕ} {s t u : RAMState}
    (h : Frame b n s t) (k : Frame b n t u) : Frame b n s u :=
  ⟨fun i hi ho => (k.words i hi ho).trans (h.words i hi ho),
    fun i hi ho => (k.indices i hi ho).trans (h.indices i hi ho),
    k.output.trans h.output, k.indexOutput.trans h.indexOutput, k.randomCursor.trans h.randomCursor⟩

theorem Written.before {b : Buffer} {es : List SparseEntry} {s t u : RAMState}
    (hw : Written b t u es) (hs : Scratch s t) : Written b s u es :=
  ⟨hw.stored, (hs.frame b es.length).trans hw.frame⟩

theorem Written.after {b : Buffer} {es : List SparseEntry} {s t u : RAMState}
    (hw : Written b s t es) (hs : Scratch t u)
    (hb : 100 ≤ b.coefficients ∧ 100 ≤ b.coordinates) : Written b s u es := by
  refine ⟨?_, hw.frame.trans (hs.frame b es.length)⟩
  intro j hj
  obtain ⟨hr, hc, hv⟩ := hw.stored j hj
  exact ⟨(hs.indices (b.row j) (by dsimp [Buffer.row]; omega)).trans hr,
    (hs.indices (b.column j) (by dsimp [Buffer.column]; omega)).trans hc,
    (hs.words (b.value j) (by dsimp [Buffer.value]; omega)).trans hv⟩

end Maxwell.Cost.RealSaddleBuffer
