import Maxwell.Cost.PhysicalEmit.Records

namespace Maxwell.Cost.PhysicalEmit
open Structured RationalAccumulator

abbrev Axis := Fin 3

def coordinateTape (i : Axis) : ℕ := 240+i.val
def dimensionTape (i : Axis) : ℕ := 250+i.val
def counterTape (i : Axis) : ℕ := 253+i.val

/-- The still-unused inner counters and coordinates are runtime words.
Outer counters need no width premise in an inner traversal: it preserves
those tapes exactly. -/
structure LowerReady (start : ℕ) (N : Axis → ℕ) (B : ℕ) (s : BitRAMState) : Prop where
  dimensions : ∀ i, Word s (dimensionTape i) (N i)
  coordinates : ∀ i, start ≤ i.val → ∃ n, n ≤ N i ∧ Word s (coordinateTape i) n
  counters : ∀ i, start ≤ i.val → ∃ word, word.length ≤ B ∧ BankArray.Word s (counterTape i) word

theorem LowerReady.mono {start finish : ℕ} {N : Axis → ℕ} {B : ℕ} {s : BitRAMState}
    (h : LowerReady start N B s) (hle : start ≤ finish) : LowerReady finish N B s :=
  ⟨h.dimensions,fun i hi => h.coordinates i (hle.trans hi),fun i hi => h.counters i (hle.trans hi)⟩

theorem LowerReady.of_frame (a : Axis) {N : Axis → ℕ} {B : ℕ} {s t : BitRAMState}
    (h : LowerReady (a.val+1) N B s)
    (hf : LoopFrame {counterTape a,coordinateTape a} s t) : LowerReady (a.val+1) N B t := by
  have keepDim (i : Axis) : t.tapes (dimensionTape i) = s.tapes (dimensionTape i) := by
    apply hf.tapes
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or,dimensionTape,counterTape,coordinateTape]
    have := a.isLt; have := i.isLt; omega
  have keepCoord (i : Axis) (hi : a.val+1 ≤ i.val) :
      t.tapes (coordinateTape i) = s.tapes (coordinateTape i) := by
    apply hf.tapes
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or,counterTape,coordinateTape]
    have := a.isLt; have := i.isLt; omega
  have keepCount (i : Axis) (hi : a.val+1 ≤ i.val) :
      t.tapes (counterTape i) = s.tapes (counterTape i) := by
    apply hf.tapes
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or,counterTape,coordinateTape]
    have := a.isLt; have := i.isLt; omega
  refine ⟨fun i => word_of_eq (keepDim i) (h.dimensions i),?_,?_⟩
  · intro i hi
    obtain ⟨n,hn,hw⟩ := h.coordinates i hi
    exact ⟨n,hn,word_of_eq (keepCoord i hi) hw⟩
  · intro i hi
    obtain ⟨word,hl,hw⟩ := h.counters i hi
    exact ⟨word,hl,BankArray.word_of_eq (keepCount i hi) hw⟩

theorem LowerReady.restore (a : Axis) {N : Axis → ℕ} {B : ℕ} {s : BitRAMState}
    (h : LowerReady (a.val+1) N B s) (hcoord : Word s (coordinateTape a) (N a))
    (hcount : ∃ word, word.length ≤ B ∧ BankArray.Word s (counterTape a) word) : LowerReady a.val N B s := by
  refine ⟨h.dimensions,?_,?_⟩
  · intro i hi
    by_cases he : i = a
    · subst i; exact ⟨N a,le_refl _,hcoord⟩
    · apply h.coordinates i
      have hv : i.val ≠ a.val := fun hv => he (Fin.ext hv)
      omega
  · intro i hi
    by_cases he : i = a
    · subst i; exact hcount
    · apply h.counters i
      have hv : i.val ≠ a.val := fun hv => he (Fin.ext hv)
      omega

def axisCode (a : Axis) (body : Code) : Code :=
  forCode (dimensionTape a) (counterTape a) (coordinateTape a) body

/-- One level of the nested physical cell traversal, with exact records
and charged control overhead. -/
theorem axis_records (a : Axis) (N : Axis → ℕ) (B : ℕ) (hB : (N a).bits.length ≤ B)
    (body : Code) (input : List Bool) (tape : ℕ → Bool)
    (R : Store → Prop) (records : ℕ → List Bool) (Q : ℕ)
    (stable : ∀ s t, LoopFrame {counterTape a,coordinateTape a} s.val t.val → R s → R t)
    (bodyCorrect : ∀ i, i < N a → ∀ s, R s → LowerReady (a.val+1) N B s.val →
      Word s.val (coordinateTape a) i →
      ∃ cost t, cost ≤ Q ∧ Executes input tape body cost s t ∧ R t ∧
        LowerReady (a.val+1) N B t.val ∧ t.val.output = (records i).reverse ++ s.val.output ∧
        t.val.tapes (coordinateTape a) = s.val.tapes (coordinateTape a) ∧
        t.val.tapes (counterTape a) = s.val.tapes (counterTape a))
    (s : Store) (hs : R s) (hr : LowerReady a.val N B s.val) :
    ∃ cost t, cost ≤ (N a+1)*(Q+52*B+58) ∧ Executes input tape (axisCode a body) cost s t ∧
      R t ∧ LowerReady a.val N B t.val ∧
      t.val.output = (recordPrefix records (N a)).reverse ++ s.val.output ∧
      Word t.val (coordinateTape a) (N a) := by
  obtain ⟨old,hold,hi⟩ := hr.coordinates a (le_refl _)
  obtain ⟨oldCount,hcl,hc⟩ := hr.counters a (le_refl _)
  let P : Store → Prop := fun s => R s ∧ LowerReady (a.val+1) N B s.val
  have hstable : ∀ s t, LoopFrame {counterTape a,coordinateTape a} s.val t.val → P s → P t := by
    intro s t hf hP
    exact ⟨stable s t hf hP.1,hP.2.of_frame a hf⟩
  have hbody : ∀ i, i < N a → ∀ s, P s → Word s.val (coordinateTape a) i →
      ∃ cost t, cost ≤ Q ∧ Executes input tape body cost s t ∧ P t ∧
        t.val.output = (records i).reverse ++ s.val.output ∧
        t.val.tapes (coordinateTape a) = s.val.tapes (coordinateTape a) ∧
        t.val.tapes (counterTape a) = s.val.tapes (counterTape a) := by
    intro i hi s hP hw
    obtain ⟨c,t,hc,he,hR,hr,ho,hi,hcount⟩ := bodyCorrect i hi s hP.1 hP.2 hw
    exact ⟨c,t,hc,he,⟨hR,hr⟩,ho,hi,hcount⟩
  obtain ⟨c,t,word,hc,he,hP,ho,hi,hcount,hlen⟩ := for_records
    (dimensionTape a) (counterTape a) (coordinateTape a) (N a)
    (by simp [counterTape,coordinateTape]) (by simp [dimensionTape,counterTape])
    (by simp [dimensionTape,coordinateTape]) body input tape P records Q hstable hbody
    old oldCount s (hr.dimensions a) hc hi ⟨hs,hr.mono (by omega)⟩
  refine ⟨c,t,?_,he,hP.1,hP.2.restore a hi ⟨word,by omega,hcount⟩,ho,hi⟩
  have hol : old.bits.length ≤ B := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le_size hold).trans (by simpa only [Nat.size_eq_bits_len] using hB)
  nlinarith

end Maxwell.Cost.PhysicalEmit
