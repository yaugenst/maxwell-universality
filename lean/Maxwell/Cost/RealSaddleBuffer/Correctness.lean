import Maxwell.Cost.RealSaddleBuffer.Program

namespace Maxwell.Cost.RealSaddleBuffer
open RealSparseOrder (Buffer Stored)
open RealSimulation.Control
set_option maxRecDepth 20000

theorem Scratch.stored {src : Buffer} {s t : RAMState} {es : List SparseEntry}
    (hf : Scratch s t) (hb : 100 ≤ src.coefficients ∧ 100 ≤ src.coordinates)
    (hs : Stored src s es) : Stored src t es := by
  intro j hj
  obtain ⟨hr, hc, hv⟩ := hs j hj
  exact ⟨(hf.indices (src.row j) (by dsimp [Buffer.row]; omega)).trans hr,
    (hf.indices (src.column j) (by dsimp [Buffer.column]; omega)).trans hc,
    (hf.words (src.value j) (by dsimp [Buffer.value]; omega)).trans hv⟩

/-- The saddle is assembled in actual addressed memory. All source
records survive, and every destination outside the emitted interval is framed. -/
theorem executes (input : RAMInput) (tape : ℕ → Bool) (src dst : Buffer)
    (rows columns padding : ℕ) (es : List SparseEntry) (s : Store)
    (hsrc : 100 ≤ src.coefficients ∧ 100 ≤ src.coordinates)
    (hdst : 100 ≤ dst.coefficients ∧ 100 ≤ dst.coordinates)
    (hsep : src.coefficients + es.length ≤ dst.coefficients ∧ src.coordinates + 2 * es.length ≤ dst.coordinates)
    (hstored : Stored src s.val es)
    (hr : s.val.indices 70 = rows) (hc : s.val.indices 71 = columns)
    (hp : s.val.indices 72 = padding) (hm : s.val.indices 73 = es.length)
    (hsc : s.val.indices 74 = src.coordinates) (hsv : s.val.indices 75 = src.coefficients)
    (hdc : s.val.indices 76 = dst.coordinates) (hdv : s.val.indices 77 = dst.coefficients) :
    ∃ t : Store, Executes input tape code (29 * es.length + 15 * rows + 15 * padding + 18) s t ∧
      Written dst s.val t.val (RealSaddle.entries rows columns padding es) ∧ Stored src t.val es := by
  let a := initialized s
  have hready₀ : DiagonalReady dst a 0 rows := by
    constructor <;> simp [a, initialized, Store.ofState, RAMState.setIndex, hr, hdc, hdv]
  obtain ⟨b, heb, hrb, hwb⟩ := diagonal_executes input tape dst 0 rows a hdst hready₀
  have hw₁ := hwb.before (initialized_scratch s)
  have metadata₁ (i : ℕ) (hi : 20 ≤ i) (hi' : i < 100) : b.val.indices i = s.val.indices i :=
    hw₁.frame.indices i hi (Or.inl (by omega))
  let c := pairsPrepared b
  have hrpairs : PairReady src (shift dst rows) c rows 0 es.length := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [c, pairsPrepared, Store.ofState, RAMState.setIndex] using hrb.one
    · simpa [c, pairsPrepared, Store.ofState, RAMState.setIndex] using hrb.two
    · simp [c, pairsPrepared, Store.ofState, RAMState.setIndex, metadata₁ 73 (by omega) (by omega), hm]
    · simp [c, pairsPrepared, Store.ofState, RAMState.setIndex, metadata₁ 74 (by omega) (by omega), hsc, Buffer.row]
    · simp [c, pairsPrepared, Store.ofState, RAMState.setIndex, metadata₁ 75 (by omega) (by omega), hsv, Buffer.value]
    · simpa [c, pairsPrepared, Store.ofState, RAMState.setIndex] using hrb.rowCursor
    · simpa [c, pairsPrepared, Store.ofState, RAMState.setIndex] using hrb.valueCursor
    · simpa [c, pairsPrepared, Store.ofState, RAMState.setIndex] using (metadata₁ 70 (by omega) (by omega)).trans hr
  have hw₁c := hw₁.after (pairsPrepared_scratch b) hdst
  have hcs := hw₁c.frame.preserves_source hsrc hsep hstored
  obtain ⟨d, hed, hrd, hwd⟩ := pair_executes input tape src (shift dst rows) rows 0 es.length es c hsrc
    (by dsimp [shift]; omega) (by dsimp [shift]; omega) hrpairs hcs (by omega)
  have hw₂ : Written dst s.val d.val (RealSaddle.diagonal 0 rows ++ RealSaddle.pairs rows es 0 es.length) :=
    hw₁c.append hdst (by simpa using hwd)
  have metadata₂ (i : ℕ) (hi : 20 ≤ i) (hi' : i < 100) : d.val.indices i = s.val.indices i :=
    hw₂.frame.indices i hi (Or.inl (by omega))
  let e := paddingPrepared d
  have hrpadding : DiagonalReady (shift dst (rows + 2 * es.length)) e (rows + columns) padding := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [e, paddingPrepared, Store.ofState, RAMState.setIndex] using hrd.one
    · simpa [e, paddingPrepared, Store.ofState, RAMState.setIndex] using hrd.two
    · simp [e, paddingPrepared, Store.ofState, RAMState.setIndex, metadata₂ 72 (by omega) (by omega), hp]
    · simp [e, paddingPrepared, Store.ofState, RAMState.setIndex, metadata₂ 70 (by omega) (by omega),
        metadata₂ 71 (by omega) (by omega), hr, hc]
    · simpa [e, paddingPrepared, Store.ofState, RAMState.setIndex, shift_shift] using hrd.targetRow
    · simpa [e, paddingPrepared, Store.ofState, RAMState.setIndex, shift_shift] using hrd.targetValue
  obtain ⟨t, het, _, hwt⟩ := diagonal_executes input tape (shift dst (rows + 2 * es.length))
    (rows + columns) padding e (by dsimp [shift]; omega) hrpadding
  have hw₃ : Written dst s.val t.val (RealSaddle.entries rows columns padding es) := by
    have hh := (hw₂.after (paddingPrepared_scratch d) hdst).append hdst (by simpa using hwt)
    simpa [RealSaddle.entries, List.append_assoc] using hh
  refine ⟨t, ?_, hw₃, hw₃.frame.preserves_source hsrc hsep hstored⟩
  convert (initialize_executes input tape s).seq (heb.seq ((preparePairs_executes input tape b).seq
    (hed.seq ((preparePadding_executes input tape d).seq het)))) using 1 <;> try rfl
  omega

theorem run (input : RAMInput) (tape : ℕ → Bool) (src dst : Buffer)
    (rows columns padding : ℕ) (es : List SparseEntry) (s : Store)
    (hsrc : 100 ≤ src.coefficients ∧ 100 ≤ src.coordinates)
    (hdst : 100 ≤ dst.coefficients ∧ 100 ≤ dst.coordinates)
    (hsep : src.coefficients + es.length ≤ dst.coefficients ∧ src.coordinates + 2 * es.length ≤ dst.coordinates)
    (hstored : Stored src s.val es)
    (hr : s.val.indices 70 = rows) (hc : s.val.indices 71 = columns)
    (hp : s.val.indices 72 = padding) (hm : s.val.indices 73 = es.length)
    (hsc : s.val.indices 74 = src.coordinates) (hsv : s.val.indices 75 = src.coefficients)
    (hdc : s.val.indices 76 = dst.coordinates) (hdv : s.val.indices 77 = dst.coefficients) :
    ∃ t : RAMState,
      (runCapped (program.next input tape) (29 * es.length + 15 * rows + 15 * padding + 19) s.val).finished = some t ∧
      (runCapped (program.next input tape) (29 * es.length + 15 * rows + 15 * padding + 19) s.val).instructions =
        29 * es.length + 15 * rows + 15 * padding + 18 ∧
      Written dst s.val t (RealSaddle.entries rows columns padding es) ∧ Stored src t es := by
  obtain ⟨t, ht, hw, hs⟩ := executes input tape src dst rows columns padding es s hsrc hdst hsep hstored
    hr hc hp hm hsc hsv hdc hdv
  obtain ⟨hf, hcount⟩ := ht.compiled_run (29 * es.length + 15 * rows + 15 * padding + 19) (by omega)
  exact ⟨t.place code.size, hf, hcount,
    ⟨hw.stored, ⟨hw.frame.words, hw.frame.indices, hw.frame.output, hw.frame.indexOutput, hw.frame.randomCursor⟩⟩, hs⟩

end Maxwell.Cost.RealSaddleBuffer
