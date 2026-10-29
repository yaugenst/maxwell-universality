import Maxwell.Cost.CalibrationMatrix.PowerStep

namespace Maxwell.Cost.CalibrationMatrix
open Structured
open RationalAccumulator (Blank)

/-- Memory outside both alternating vector buffers is retained. -/
def Buffers.Outside {n : ℕ} (b : Buffers n) (s t : BitRAMState) : Prop :=
  ∀ a,
    (a < addressValue b.data.vectorPositiveBase ∨ addressValue b.data.vectorPositiveBase+n*addressValue b.data.width ≤ a) →
    (a < addressValue b.data.vectorNegativeBase ∨ addressValue b.data.vectorNegativeBase+n*addressValue b.data.width ≤ a) →
    (a < addressValue b.output.positiveBase ∨ addressValue b.output.positiveBase+n*addressValue b.data.width ≤ a) →
    (a < addressValue b.output.negativeBase ∨ addressValue b.output.negativeBase+n*addressValue b.data.width ≤ a) →
    t.memory a = s.memory a

theorem Buffers.Outside.refl {n : ℕ} (b : Buffers n) (s : BitRAMState) : b.Outside s s := by
  intro a _ _ _ _; rfl

theorem Buffers.Outside.trans {n : ℕ} {b : Buffers n} {s t u : BitRAMState}
    (h : b.Outside s t) (k : b.Outside t u) : b.Outside s u :=
  fun a hp hn ho hq => (k a hp hn ho hq).trans (h a hp hn ho hq)

theorem Buffers.Outside.of_memory {n : ℕ} {b : Buffers n} {s t : BitRAMState}
    (h : t.memory = s.memory) : b.Outside s t := by intro a _ _ _ _; rw [h]

theorem Buffers.Outside.of_output {n : ℕ} {b : Buffers n} {s t : BitRAMState}
    (h : OutputOutside b.output n (addressValue b.data.width) s t) : b.Outside s t :=
  fun a _ _ hp hn => h a hp hn

theorem Buffers.outside_advance {n : ℕ} (b : Buffers n) (s t : BitRAMState) :
    b.advance.Outside s t ↔ b.Outside s t := by
  constructor
  · intro h a hp hn ho hq; exact h a ho hq hp hn
  · intro h a hp hn ho hq; exact h a ho hq hp hn

theorem Buffers.outside_iterate {n : ℕ} (b : Buffers n) (k : ℕ) (s t : BitRAMState) :
    (b.iterate k).Outside s t ↔ b.Outside s t := by
  induction k with
  | zero => rfl
  | succ k ih => exact (Buffers.outside_advance _ _ _).trans ih

theorem Buffers.Ready.of_memory_tapes {n B : ℕ} {b : Buffers n} {count : List Bool} {s t : BitRAMState}
    (h : b.Ready count B s) (hm : t.memory = s.memory)
    (hk : ∀ i, i ≠ 140 → t.tapes i = s.tapes i) : b.Ready count B t := by
  obtain ⟨vi, hv, hl, hr, hd, hi, ho, h107, h106, h37, h108, h109⟩ := h
  refine ⟨vi, hv, hl, hr.of_tapes (fun i hi => hk i (by omega)), ?_,
    ⟨BankArray.word_of_eq (hk 102 (by omega)) hi.1, BankArray.word_of_eq (hk 103 (by omega)) hi.2⟩,
    ho.of_memory hm (fun i hi => hk i (by omega)),
    BankArray.word_of_eq (hk 107 (by omega)) h107,
    RationalAccumulator.blank_of_eq (hk 106 (by omega)) h106,
    RationalAccumulator.blank_of_eq (hk 37 (by omega)) h37,
    RationalAccumulator.blank_of_eq (hk 108 (by omega)) h108,
    RationalAccumulator.blank_of_eq (hk 109 (by omega)) h109⟩
  exact ⟨BankArray.word_of_eq (hk 100 (by omega)) hd.width,
    BankArray.word_of_eq (hk 101 (by omega)) hd.clock,
    BankArray.word_of_eq (hk 110 (by omega)) hd.matrixPositiveBase,
    BankArray.word_of_eq (hk 111 (by omega)) hd.matrixNegativeBase,
    BankArray.word_of_eq (hk 112 (by omega)) hd.vectorPositiveBase,
    BankArray.word_of_eq (hk 113 (by omega)) hd.vectorNegativeBase,
    by simpa only [hm] using hd.matrixPositive,
    by simpa only [hm] using hd.matrixNegative,
    by simpa only [hm] using hd.vectorPositive,
    by simpa only [hm] using hd.vectorNegative⟩

theorem PowerFrame.of_counter {s t : Store} (h : CountedShifted.Frame 140 s t) : PowerFrame s.val t.val :=
  ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i _ _ _ _ _ _ _ _ _ _ _ _ _ hi => h.2.2.2.2.2.1 i hi,
    fun i hi h24 h25 _ _ _ h29 => h.2.2.2.2.2.2 i (by omega) h24 h25 h29⟩

def PowerInvariant {n : ℕ} (b : Buffers n) (count : List Bool) (N B : ℕ)
    (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ N ∧ (b.iterate (N-remaining)).Ready count B s.val ∧
    PowerFrame initial s.val ∧ b.Outside initial s.val

theorem power_invariant_stable {n : ℕ} (b : Buffers n) (count : List Bool) (N B : ℕ)
    (initial : BitRAMState) (remaining : ℕ) (s t : Store)
    (hf : CountedShifted.Frame 140 s t) (hs : PowerInvariant b count N B initial remaining s) :
    PowerInvariant b count N B initial remaining t :=
  ⟨hs.1, hs.2.1.of_memory_tapes hf.2.2.1 hf.2.2.2.2.2.1,
    hs.2.2.1.trans (PowerFrame.of_counter hf), hs.2.2.2.trans (Buffers.Outside.of_memory hf.2.2.1)⟩

def matrixPower {n : ℕ} (A : ChannelMatrix n) (x : Channels n) : ℕ → Channels n
  | 0 => x
  | k+1 => matvec A (matrixPower A x k)

theorem Buffers.iterate_decodes {n : ℕ} {b : Buffers n} {A : ChannelMatrix n} {x : Channels n}
    (h : b.data.Decodes A x) (N : ℕ) (hfit : ∀ k, k < N → (b.iterate k).Fits) :
    (b.iterate N).data.Decodes A (matrixPower A x N) := by
  induction N with
  | zero => exact h
  | succ N ih =>
    exact (b.iterate N).advance_decodes (ih (fun k hk => hfit k (by omega))) (hfit N (by omega))

end Maxwell.Cost.CalibrationMatrix
