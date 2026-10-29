import Maxwell.Cost.RealSparseOrder.Buffer
import Maxwell.Cost.RealSaddle

namespace Maxwell.Cost.RealSaddleBuffer
open RealSparseOrder (Buffer Stored)
open RealSparse (entryAt)

def shift (b : Buffer) (n : ℕ) : Buffer := ⟨b.coefficients + n, b.coordinates + 2 * n⟩

@[simp] theorem shift_value (b : Buffer) (n j : ℕ) : (shift b n).value j = b.value (n + j) := by
  simp [shift, Buffer.value, Nat.add_assoc]
@[simp] theorem shift_row (b : Buffer) (n j : ℕ) : (shift b n).row j = b.row (n + j) := by
  simp [shift, Buffer.row, Nat.mul_add, Nat.add_assoc]
@[simp] theorem shift_column (b : Buffer) (n j : ℕ) : (shift b n).column j = b.column (n + j) := by
  simp [shift, Buffer.column, Nat.mul_add, Nat.add_assoc]
@[simp] theorem shift_shift (b : Buffer) (n m : ℕ) : shift (shift b n) m = shift b (n + m) := by
  simp [shift, Nat.mul_add, Nat.add_assoc]

structure Frame (b : Buffer) (n : ℕ) (s t : RAMState) : Prop where
  words : ∀ i, 1 ≤ i → (i < b.coefficients ∨ b.coefficients + n ≤ i) → t.words i = s.words i
  indices : ∀ i, 20 ≤ i → (i < b.coordinates ∨ b.coordinates + 2 * n ≤ i) → t.indices i = s.indices i
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput
  randomCursor : t.randomCursor = s.randomCursor

theorem Frame.refl (b : Buffer) (n : ℕ) (s : RAMState) : Frame b n s s :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem Frame.append {b : Buffer} {n m : ℕ} {s t u : RAMState}
    (h : Frame b n s t) (k : Frame (shift b n) m t u) : Frame b (n + m) s u := by
  refine ⟨?_, ?_, k.output.trans h.output, k.indexOutput.trans h.indexOutput,
    k.randomCursor.trans h.randomCursor⟩
  · intro i hi ho
    exact (k.words i hi (by dsimp [shift]; omega)).trans (h.words i hi (by omega))
  · intro i hi ho
    exact (k.indices i hi (by dsimp [shift]; omega)).trans (h.indices i hi (by omega))

structure Written (b : Buffer) (s t : RAMState) (es : List SparseEntry) : Prop where
  stored : Stored b t es
  frame : Frame b es.length s t

theorem Written.nil (b : Buffer) (s : RAMState) : Written b s s [] :=
  ⟨by intro j hj; simp at hj, Frame.refl b 0 s⟩

theorem stored_append (b : Buffer) (s : RAMState) (es fs : List SparseEntry)
    (he : Stored b s es) (hf : Stored (shift b es.length) s fs) : Stored b s (es ++ fs) := by
  intro j hj
  by_cases h : j < es.length
  · have heq : entryAt (es ++ fs) j = entryAt es j := by
      simp [entryAt, List.getElem?_append_left h]
    simpa [heq] using he j h
  · have hge : es.length ≤ j := by omega
    have hj' : j - es.length < fs.length := by simp only [List.length_append] at hj; omega
    have heq : entryAt (es ++ fs) j = entryAt fs (j - es.length) := by
      simp [entryAt, List.getElem?_append_right hge]
    simpa [shift_value, shift_row, shift_column, Nat.add_sub_cancel' hge, heq] using hf (j - es.length) hj'

theorem Written.append {b : Buffer} {s t u : RAMState} {es fs : List SparseEntry}
    (hb : 100 ≤ b.coefficients ∧ 100 ≤ b.coordinates)
    (he : Written b s t es) (hf : Written (shift b es.length) t u fs) : Written b s u (es ++ fs) := by
  refine ⟨stored_append b u es fs ?_ hf.stored, ?_⟩
  · intro j hj
    obtain ⟨hr, hc, hv⟩ := he.stored j hj
    refine ⟨?_, ?_, ?_⟩
    · exact (hf.frame.indices (b.row j) (by dsimp [Buffer.row]; omega)
        (Or.inl (by dsimp [Buffer.row, shift]; omega))).trans hr
    · exact (hf.frame.indices (b.column j) (by dsimp [Buffer.column]; omega)
        (Or.inl (by dsimp [Buffer.column, shift]; omega))).trans hc
    · exact (hf.frame.words (b.value j) (by dsimp [Buffer.value]; omega)
        (Or.inl (by dsimp [Buffer.value, shift]; omega))).trans hv
  · simpa using he.frame.append hf.frame

end Maxwell.Cost.RealSaddleBuffer
