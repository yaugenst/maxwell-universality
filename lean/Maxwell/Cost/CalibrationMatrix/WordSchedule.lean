import Maxwell.Cost.CalibrationMatrix.SuccessorWord
import Maxwell.Cost.CalibrationMatrix.PadWord

/-! Fixed schedules of actual word successors and fixed-width copies. -/
namespace Maxwell.Cost.CalibrationMatrix.WordSchedule
open Structured BankArray

inductive Op where
  | successor (source target : ℕ)
  | pad (source target : ℕ)
  deriving DecidableEq

def Op.source : Op → ℕ
  | .successor s _ | .pad s _ => s

def Op.target : Op → ℕ
  | .successor _ t | .pad _ t => t

def Op.code (clock : ℕ) : Op → Code
  | .successor s t => successorWordCode s t
  | .pad s t => padWordCode s clock t

def Op.result (width : ℕ) (v : ℕ → List Bool) : Op → List Bool
  | .successor s _ => Increment.bits (v s)
  | .pad s _ => FixedWidth.bits width (v s)

def Op.apply (width : ℕ) (v : ℕ → List Bool) (op : Op) : ℕ → List Bool :=
  Function.update v op.target (op.result width v)

def Banks (domain : Finset ℕ) (s : Store) (v : ℕ → List Bool) : Prop :=
  ∀ i ∈ domain, Word s.val i (v i)

structure Frame (changed : Finset ℕ) (s t : Store) : Prop where
  address : t.val.address = s.val.address
  memory : t.val.memory = s.val.memory
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ i, i ∉ changed → t.val.tapes i = s.val.tapes i
  registers : ∀ i, 100 ≤ i → t.val.registers i = s.val.registers i

structure Valid (domain : Finset ℕ) (clock width : ℕ) (v : ℕ → List Bool) (op : Op) : Prop where
  source_mem : op.source ∈ domain
  target_mem : op.target ∈ domain
  target_high : 100 ≤ op.target
  different : op.source ≠ op.target
  clock_source : op.source ≠ clock
  clock_target : clock ≠ op.target
  target_empty : v op.target = []
  source_length : (v op.source).length ≤ width

theorem step (domain : Finset ℕ) (clock width : ℕ) (clockWord : List Bool)
    (hclock : clock ∈ domain) (hlen : clockWord.length = width)
    (op : Op) (v : ℕ → List Bool) (hvclock : v clock = clockWord)
    (hv : Valid domain clock width v op) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (hb : Banks domain s v) (hs : Scratch s.val) :
    ∃ cost t, cost ≤ 62*(width+1) ∧ Executes input tape (op.code clock) cost s t ∧
      Banks domain t (op.apply width v) ∧ Scratch t.val ∧ Frame {op.target} s t := by
  have ht : RationalAccumulator.Blank s.val op.target := by
    have h := hb op.target hv.target_mem
    rw [hv.target_empty] at h
    simpa [Word, RationalAccumulator.Blank] using h
  have hsword := hb op.source hv.source_mem
  have hcword : Word s.val clock clockWord := by simpa [hvclock] using hb clock hclock
  cases op with
  | successor source target =>
    obtain ⟨cost, t, hcost, he, hw, _, _, _, hscratch, hm, ha, hkeep, hf⟩ :=
      successor_word_bank source target (by simpa [Op.target] using le_trans (by decide : 10 ≤ 100) hv.target_high)
        hv.different input tape (v source) s hsword ht hs
    refine ⟨cost, t, ?_, he, ?_, hscratch, ?_⟩
    · have hl := hv.source_length
      simp only [Op.source] at hl
      omega
    · intro i hi
      by_cases hit : i = target
      · subst i; simpa [Op.apply, Op.target, Op.result] using hw
      · simpa [Op.apply, Op.target, hit] using word_of_eq (hkeep i hit) (hb i hi)
    · refine ⟨ha, hm, hf.1, hf.2.1, hf.2.2.1, ?_, ?_⟩
      · intro i hi
        exact hkeep i (by simpa [Op.target] using hi)
      · intro i hi
        exact hf.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
  | pad source target =>
    obtain ⟨cost, t, hcost, he, hw, _, _, hscratch, hf⟩ :=
      pad_word_bank source clock target (by simpa [Op.target] using le_trans (by decide : 10 ≤ 100) hv.target_high)
        hv.clock_source hv.different hv.clock_target input tape width clockWord (v source)
        hlen hv.source_length s hsword hcword ht hs
    refine ⟨cost, t, by omega, he, ?_, hscratch, ?_⟩
    · intro i hi
      by_cases hit : i = target
      · subst i; simpa [Op.apply, Op.target, Op.result] using hw
      · simpa [Op.apply, Op.target, hit] using word_of_eq (hf.tapes i hit) (hb i hi)
    · exact ⟨hf.address, hf.memory, hf.inputHead, hf.randomCursor, hf.output,
        fun i hi => hf.tapes i (by simpa [Op.target] using hi),
        fun i hi => hf.registers i (Or.inr (by omega))⟩

def code (clock : ℕ) : List Op → Code
  | [] => .skip
  | op :: ops => .seq (op.code clock) (code clock ops)

def run (width : ℕ) : List Op → (ℕ → List Bool) → (ℕ → List Bool)
  | [], v => v
  | op :: ops, v => run width ops (op.apply width v)

def changes (ops : List Op) : Finset ℕ := (ops.map Op.target).toFinset

def Admissible (domain : Finset ℕ) (clock width : ℕ) : List Op → (ℕ → List Bool) → Prop
  | [], _ => True
  | op :: ops, v => Valid domain clock width v op ∧
      Admissible domain clock width ops (op.apply width v)

theorem executes (domain : Finset ℕ)
    (clock width : ℕ) (clockWord : List Bool) (hclock : clock ∈ domain)
    (hlen : clockWord.length = width) (ops : List Op) (v : ℕ → List Bool)
    (hvclock : v clock = clockWord) (hv : Admissible domain clock width ops v)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : Banks domain s v) (hs : Scratch s.val) :
    ∃ cost t, cost ≤ ops.length*(62*(width+1))+1 ∧
      Executes input tape (code clock ops) cost s t ∧
      Banks domain t (run width ops v) ∧ Scratch t.val ∧ Frame (changes ops) s t := by
  induction ops generalizing v s with
  | nil => exact ⟨1, s, by simp, .skip s, hb, hs,
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  | cons op ops ih =>
    obtain ⟨ha, hrest⟩ := hv
    obtain ⟨a, t, hca, ea, hbt, hst, hf⟩ :=
      step domain clock width clockWord hclock hlen op v hvclock ha input tape s hb hs
    have hc : op.apply width v clock = clockWord := by
      simpa [Op.apply, ha.clock_target] using hvclock
    obtain ⟨b, u, hcb, eb, hbu, hsu, hg⟩ := ih (op.apply width v) hc hrest t hbt hst
    refine ⟨a+b, u, ?_, ea.seq eb, hbu, hsu, ?_⟩
    · simp only [List.length_cons]; nlinarith
    · refine ⟨hg.address.trans hf.address, hg.memory.trans hf.memory,
        hg.inputHead.trans hf.inputHead, hg.randomCursor.trans hf.randomCursor,
        hg.output.trans hf.output, ?_, fun i hi => (hg.registers i hi).trans (hf.registers i hi)⟩
      intro i hout
      have ht : i ∉ changes ops ∧ i ≠ op.target := by
        simpa [changes, not_or, and_comm] using hout
      exact (hg.tapes i ht.1).trans (hf.tapes i (by simpa using ht.2))

end Maxwell.Cost.CalibrationMatrix.WordSchedule
