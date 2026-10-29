import Maxwell.Cost.RealSaddleBuffer.PairCycle

namespace Maxwell.Cost.RealSaddleBuffer
open RealSparseOrder (Buffer Stored)
open RealSimulation.Control

theorem Frame.preserves_source {src dst : Buffer} {n : ℕ} {s t : RAMState} {es : List SparseEntry}
    (hf : Frame dst n s t) (hsrc : 100 ≤ src.coefficients ∧ 100 ≤ src.coordinates)
    (hsep : src.coefficients + es.length ≤ dst.coefficients ∧ src.coordinates + 2 * es.length ≤ dst.coordinates)
    (hstored : Stored src s es) : Stored src t es := by
  intro j hj
  obtain ⟨hr, hc, hv⟩ := hstored j hj
  exact ⟨(hf.indices (src.row j) (by dsimp [Buffer.row]; omega)
      (Or.inl (by dsimp [Buffer.row]; omega))).trans hr,
    (hf.indices (src.column j) (by dsimp [Buffer.column]; omega)
      (Or.inl (by dsimp [Buffer.column]; omega))).trans hc,
    (hf.words (src.value j) (by dsimp [Buffer.value]; omega)
      (Or.inl (by dsimp [Buffer.value]; omega))).trans hv⟩

theorem pair_executes (input : RAMInput) (tape : ℕ → Bool) (src dst : Buffer)
    (rows start n : ℕ) (es : List SparseEntry) (s : Store)
    (hsrc : 100 ≤ src.coefficients ∧ 100 ≤ src.coordinates)
    (hdst : 100 ≤ dst.coefficients ∧ 100 ≤ dst.coordinates)
    (hsep : src.coefficients + es.length ≤ dst.coefficients ∧ src.coordinates + 2 * es.length ≤ dst.coordinates)
    (h : PairReady src dst s rows start n) (hstored : Stored src s.val es) (hk : start + n ≤ es.length) :
    ∃ t : Store, Executes input tape pairLoop (29 * n + 1) s t ∧
      PairReady src (shift dst (2 * n)) t rows (start + n) 0 ∧
      Written dst s.val t.val (RealSaddle.pairs rows es start n) := by
  induction n generalizing dst start s with
  | zero =>
    refine ⟨s, Executes.done (by rw [h.one, h.remaining]; omega), ?_, Written.nil dst s.val⟩
    simpa [shift] using h
  | succ n ih =>
    obtain ⟨a, hea, hra, hwa⟩ := pair_cycle input tape src dst rows start n es s hsrc hdst h hstored (by omega)
    have hastored := hwa.frame.preserves_source hsrc hsep hstored
    obtain ⟨t, het, hrt, hwt⟩ := ih (shift dst 2) (start + 1) a (by dsimp [shift]; omega)
      (by dsimp [shift]; omega) hra hastored (by omega)
    refine ⟨t, ?_, ?_, ?_⟩
    · convert Executes.more (by rw [h.one, h.remaining]; omega) hea het using 1 <;> try rfl
      omega
    · simpa [shift_shift, Nat.mul_add, Nat.add_assoc, Nat.add_comm 2 (2 * n), Nat.add_comm 1 n] using hrt
    · simpa [RealSaddle.pairs] using hwa.append hdst hwt

end Maxwell.Cost.RealSaddleBuffer
