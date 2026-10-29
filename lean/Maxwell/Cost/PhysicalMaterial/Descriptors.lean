import Maxwell.Cost.BankArray.ReadCanonical
import Maxwell.Cost.CalibrationMatrix.Affine.Load

/-! The runtime descriptor format for physical scalar defects. -/
namespace Maxwell.Cost.PhysicalMaterial.Descriptors
open Structured RationalAccumulator

/-- Read-only fixed-width arrays hold three physical anchor coordinates and
the nonnegative numerator and positive denominator of each strength. -/
structure Data (n : ℕ) where
  width : List Bool
  clock : List Bool
  bases : Fin 5 → List Bool
  words : Fin 5 → Vector (List Bool) n
  width_nonempty : 0 < width.length
  clock_length : clock.length = addressValue width

def baseTape (i : Fin 5) : ℕ := 310 + i.val

def targetTape (i : Fin 5) : ℕ := ![294, 295, 296, 276, 277] i

theorem targetTape_injective : Function.Injective targetTape := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [targetTape]

theorem targetTape_bounds (i : Fin 5) : 276 ≤ targetTape i ∧ targetTape i ≤ 296 := by
  fin_cases i <;> decide

def value {n : ℕ} (d : Data n) (row : Fin n) (port : Fin 5) : ℕ :=
  addressValue ((d.words port).get row)

structure Stored {n : ℕ} (d : Data n) (s : BitRAMState) : Prop where
  width : BankArray.Word s 300 d.width
  clock : BankArray.Word s 301 d.clock
  bases : ∀ i, BankArray.Word s (baseTape i) (d.bases i)
  arrays : ∀ i, BitArray.Represents s.memory (addressValue (d.bases i))
    (addressValue d.width) (d.words i)

def Ready (s : BitRAMState) : Prop := ∀ i, i < 10 → Blank s i

def Bank (s : BitRAMState) (v : Fin 5 → ℕ) : Prop :=
  ∀ i, Word s (targetTape i) (v i)

structure Frame (changed : Finset ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i = 4 ∨ 10 ≤ i → i ∉ changed → t.tapes i = s.tapes i

theorem Frame.refl (changed : Finset ℕ) (s : BitRAMState) : Frame changed s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem Frame.trans {changed : Finset ℕ} {s t u : BitRAMState}
    (h : Frame changed s t) (k : Frame changed t u) : Frame changed s u :=
  ⟨k.memory.trans h.memory, k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i hi hn => (k.tapes i hi hn).trans (h.tapes i hi hn)⟩

theorem Frame.mono {a b : Finset ℕ} {s t : BitRAMState}
    (h : Frame a s t) (hab : a ⊆ b) : Frame b s t :=
  ⟨h.memory, h.inputHead, h.randomCursor, h.output,
    fun i hi hn => h.tapes i hi (fun hh => hn (hab hh))⟩

def targets : Finset ℕ := {294, 295, 296, 276, 277}

theorem target_mem (i : Fin 5) : targetTape i ∈ targets := by fin_cases i <;> decide

def Data.Sized {n : ℕ} (d : Data n) (B : ℕ) : Prop :=
  d.width.length ≤ B ∧ addressValue d.width ≤ B ∧ ∀ i, (d.bases i).length ≤ B

theorem Ready.scratch {s : BitRAMState} (h : Ready s) : BankArray.Scratch s :=
  ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 5 (by decide), h 6 (by decide), h 8 (by decide), h 9 (by decide)⟩

theorem Stored.of_frame {n : ℕ} {d : Data n} {s t : BitRAMState}
    (h : Stored d s) (hf : Frame targets s t) : Stored d t := by
  refine ⟨BankArray.word_of_eq (hf.tapes 300 (by omega) (by decide)) h.width,
    BankArray.word_of_eq (hf.tapes 301 (by omega) (by decide)) h.clock, ?_, ?_⟩
  · intro i
    exact BankArray.word_of_eq (hf.tapes (baseTape i) (by simp only [baseTape]; omega)
      (by simp [baseTape, targets]; omega)) (h.bases i)
  · intro i
    simpa only [hf.memory] using h.arrays i

def loadCode (port : Fin 5) : Code :=
  BankArray.readCanonicalCode 300 302 (baseTape port) 301 (targetTape port)

/-- One actual addressed array read replaces an empty candidate field by its
canonical stored value and restores the shared bit/address scratch. -/
theorem load {n : ℕ} (d : Data n) (row : Fin n) (port : Fin 5) (B : ℕ)
    (hd : d.Sized B) (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = row.val) (hil : index.length ≤ B) (s : Store)
    (hs : Ready s.val) (hdata : Stored d s.val) (hindex : BankArray.Word s.val 302 index)
    (v : Fin 5 → ℕ) (hv : Bank s.val v) (hzero : v port = 0) :
    ∃ cost t, cost ≤ 20000 * (B+2)^2 ∧ Executes input tape (loadCode port) cost s t ∧
      Ready t.val ∧ Stored d t.val ∧ Bank t.val (Function.update v port (value d row port)) ∧
      Frame targets s.val t.val := by
  have ht := targetTape_bounds port
  have hz : Blank s.val (targetTape port) :=
    (zero_word_iff_blank _ _).mp (by simpa only [hzero] using hv port)
  obtain ⟨cost, t, hcost, he, hout, hscratch, h7, hm, _, hf⟩ := BankArray.read_canonical
    300 302 (baseTape port) 301 (targetTape port)
    (by decide) (by decide) (by simp only [baseTape]; omega) (by decide) (by omega)
    input tape d.width index (d.bases port) d.clock (d.words port) row
    d.width_nonempty hi d.clock_length s hs.scratch (hs 7 (by decide)) hz
    hdata.width hindex (hdata.bases port) hdata.clock (hdata.arrays port)
  have frame : Frame targets s.val t.val := by
    refine ⟨hm, hf.1, hf.2.1, hf.2.2.1, ?_⟩
    intro i hi hn
    exact hf.2.2.2.1 i hi (by intro heq; subst i; exact hn (target_mem port))
  refine ⟨cost, t, hcost.trans (CalibrationMatrix.Affine.read_cost_le _ _ _ _ B
    hd.1 hd.2.1 hil (hd.2.2 port) d.clock_length), he, ?_, hdata.of_frame frame, ?_, frame⟩
  · intro i hi
    rcases hscratch with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact blank_of_eq (hf.2.2.2.1 4 (by omega) (by omega)) (hs 4 (by decide))
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9
  · intro i
    by_cases heq : i = port
    · subst i
      simpa only [Function.update_self, value] using hout
    · have hne : targetTape i ≠ targetTape port := fun hh => heq (targetTape_injective hh)
      rw [Function.update_of_ne heq]
      exact word_of_eq (hf.2.2.2.1 (targetTape i)
        (by have := targetTape_bounds i; omega) hne) (hv i)

end Maxwell.Cost.PhysicalMaterial.Descriptors
