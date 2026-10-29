import Maxwell.Cost.RealSaddleBuffer.PairProgram
import Maxwell.Cost.RealSaddleBuffer.Scratch

namespace Maxwell.Cost.RealSaddleBuffer
open RealSparseOrder (Buffer Stored)
open RealSimulation.Control
open RealSparse (entryAt)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem pair_cycle (input : RAMInput) (tape : ℕ → Bool) (src dst : Buffer)
    (rows start n : ℕ) (es : List SparseEntry) (s : Store)
    (hsrc : 100 ≤ src.coefficients ∧ 100 ≤ src.coordinates)
    (hdst : 100 ≤ dst.coefficients ∧ 100 ≤ dst.coordinates)
    (h : PairReady src dst s rows start (n + 1)) (hstored : Stored src s.val es) (hk : start < es.length) :
    ∃ t : Store, Executes input tape pairCode 28 s t ∧
      PairReady src (shift dst 2) t rows (start + 1) n ∧
      Written dst s.val t.val [⟨(entryAt es start).row, rows + (entryAt es start).column, (entryAt es start).value⟩,
        ⟨rows + (entryAt es start).column, (entryAt es start).row, (entryAt es start).value⟩] := by
  let v := entryAt es start
  let a := pairLoaded s
  let c := Store.ofState (appended a.val)
  let d := pairSwapped c
  let e := Store.ofState (appended d.val)
  let t := pairFinished e
  have ai (i : ℕ) (h9 : i ≠ 9) (h10 : i ≠ 10) (h11 : i ≠ 11) : a.val.indices i = s.val.indices i := by
    simp [a, pairLoaded, Store.ofState, RAMState.setIndex, RAMState.setWord, h9, h10, h11]
  have a7 : a.val.indices 7 = dst.coordinates := (ai 7 (by omega) (by omega) (by omega)).trans h.targetRow
  have a8 : a.val.indices 8 = dst.coefficients := (ai 8 (by omega) (by omega) (by omega)).trans h.targetValue
  have ar : a.val.indices 9 = v.row := by
    simp [a, pairLoaded, Store.ofState, RAMState.setIndex, RAMState.setWord, h.sourceRow, (hstored start hk).1, v]
  have ac : a.val.indices 10 = rows + v.column := by
    have he := (hstored start hk).2.1
    simpa [a, pairLoaded, Store.ofState, RAMState.setIndex, RAMState.setWord,
      h.rowCount, h.sourceRow, Buffer.row, Buffer.column, v] using congrArg (rows + ·) he
  have av : a.val.words 0 = v.value := by
    simp [a, pairLoaded, Store.ofState, RAMState.setWord, h.sourceValue, (hstored start hk).2.2, v]
  have ci (i : ℕ) (hi : i < 100) (h7 : i ≠ 7) (h8 : i ≠ 8) (h11 : i ≠ 11) :
      c.val.indices i = a.val.indices i :=
    appended_register a.val i hi h7 h8 h11 (by rw [a7]; exact hdst.2)
  have cp := appended_pointers a.val
  have d7 : d.val.indices 7 = (shift dst 1).coordinates := by
    simpa [d, pairSwapped, Store.ofState, RAMState.setIndex, c, a7, shift] using cp.1
  have d8 : d.val.indices 8 = (shift dst 1).coefficients := by
    simpa [d, pairSwapped, Store.ofState, RAMState.setIndex, c, a8, shift] using cp.2
  have dr : d.val.indices 9 = rows + v.column := by
    simpa [d, pairSwapped, Store.ofState, RAMState.setIndex] using
      (ci 10 (by omega) (by omega) (by omega) (by omega)).trans ac
  have dc : d.val.indices 10 = v.row := by
    simpa [d, pairSwapped, Store.ofState, RAMState.setIndex] using
      (ci 9 (by omega) (by omega) (by omega) (by omega)).trans ar
  have dv : d.val.words 0 = v.value := by
    simp [d, pairSwapped, c, appended, Store.ofState, RAMState.setIndex, RAMState.setWord,
      a8, show (0 : ℕ) ≠ dst.coefficients by omega, av]
  have di (i : ℕ) (hi : i < 100) (h7 : i ≠ 7) (h8 : i ≠ 8)
      (h9 : i ≠ 9) (h10 : i ≠ 10) (h11 : i ≠ 11) : d.val.indices i = s.val.indices i := by
    simpa [d, pairSwapped, Store.ofState, RAMState.setIndex, h9, h10, h11] using
      (ci i hi h7 h8 h11).trans (ai i h9 h10 h11)
  have ei (i : ℕ) (hi : i < 100) (h7 : i ≠ 7) (h8 : i ≠ 8)
      (h9 : i ≠ 9) (h10 : i ≠ 10) (h11 : i ≠ 11) : e.val.indices i = s.val.indices i :=
    (appended_register d.val i hi h7 h8 h11 (by rw [d7]; dsimp [shift]; omega)).trans
      (di i hi h7 h8 h9 h10 h11)
  have ebase (i : ℕ) (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 70) :
      e.val.indices i = s.val.indices i := by
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ei _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have scratchA : Scratch s.val a.val := by
    refine ⟨?_, ?_, rfl, rfl, rfl⟩
    · intro i hi
      simp [a, pairLoaded, Store.ofState, RAMState.setIndex, RAMState.setWord, show i ≠ 0 by omega]
    · intro i hi; exact ai i (by omega) (by omega) (by omega)
  have scratchD : Scratch c.val d.val := by
    refine ⟨fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
    intro i hi
    simp [d, pairSwapped, Store.ofState, RAMState.setIndex,
      show i ≠ 9 by omega, show i ≠ 10 by omega, show i ≠ 11 by omega]
  have scratchT : Scratch e.val t.val := by
    refine ⟨fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
    intro i hi
    simp [t, pairFinished, Store.ofState, RAMState.setIndex,
      show i ≠ 3 by omega, show i ≠ 5 by omega, show i ≠ 6 by omega]
  have hw₁ := appended_written dst ⟨v.row, rows + v.column, v.value⟩ a.val hdst a7 a8 ar ac av
  have hw₂ := appended_written (shift dst 1) ⟨rows + v.column, v.row, v.value⟩ d.val
    (by dsimp [shift]; omega) d7 d8 dr dc dv
  have hw₁' : Written dst s.val c.val [⟨v.row, rows + v.column, v.value⟩] := by
    have hh := hw₁.before scratchA
    exact ⟨hh.stored, ⟨hh.frame.words, hh.frame.indices, hh.frame.output, hh.frame.indexOutput, hh.frame.randomCursor⟩⟩
  have hw₂' : Written (shift dst 1) d.val e.val [⟨rows + v.column, v.row, v.value⟩] :=
    ⟨hw₂.stored, ⟨hw₂.frame.words, hw₂.frame.indices, hw₂.frame.output, hw₂.frame.indexOutput, hw₂.frame.randomCursor⟩⟩
  have ep := appended_pointers d.val
  refine ⟨t, ?_, ?_, ?_⟩
  · exact (pairLoad_executes input tape s h.one (by rw [h.sourceRow]; dsimp [Buffer.row]; omega)).seq
      ((append_executes input tape a ((ai 1 (by omega) (by omega) (by omega)).trans h.one)
        ((ai 2 (by omega) (by omega) (by omega)).trans h.two)
        (by rw [a7]; exact hdst.2) (by rw [a8]; exact hdst.1)).seq
        ((pairSwap_executes input tape c).seq
          ((append_executes input tape d ((di 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.one)
            ((di 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.two)
            (by rw [d7]; dsimp [shift]; omega) (by rw [d8]; dsimp [shift]; omega)).seq
            (pairFinish_executes input tape e ((ebase 1 (by simp)).trans h.one) ((ebase 2 (by simp)).trans h.two)))))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [t, pairFinished, Store.ofState, RAMState.setIndex] using (ebase 1 (by simp)).trans h.one
    · simpa [t, pairFinished, Store.ofState, RAMState.setIndex] using (ebase 2 (by simp)).trans h.two
    · simp [t, pairFinished, Store.ofState, RAMState.setIndex, ebase 3 (by simp), h.remaining]
    · simp [t, pairFinished, Store.ofState, RAMState.setIndex, ebase 5 (by simp), h.sourceRow, Buffer.row]
      omega
    · simp [t, pairFinished, Store.ofState, RAMState.setIndex, ebase 6 (by simp), h.sourceValue, Buffer.value, Nat.add_assoc]
    · simpa [t, pairFinished, Store.ofState, RAMState.setIndex, e, d7, shift] using ep.1
    · simpa [t, pairFinished, Store.ofState, RAMState.setIndex, e, d8, shift, Nat.add_assoc] using ep.2
    · simpa [t, pairFinished, Store.ofState, RAMState.setIndex] using (ebase 70 (by simp)).trans h.rowCount
  · exact ((hw₁'.after scratchD hdst).append hdst hw₂').after scratchT hdst

end Maxwell.Cost.RealSaddleBuffer
