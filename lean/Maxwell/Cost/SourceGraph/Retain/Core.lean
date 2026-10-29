import Maxwell.Cost.SourceGraph.Retain.Plan
import Maxwell.Cost.SourceGraph.Retain.Dimension

namespace Maxwell.Cost.SourceGraph.Retain
open Structured SourceCircuit
open RationalAccumulator (Word Blank word_of_eq blank_of_eq)

def work : Finset ℕ := {0,1,2,3} ∪ Finset.Icc 500 509
def code : Code := .seq numericCode (.seq dimensionCode (.call (WordTransfer.clone 20 508)))
def price (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  numericPrice S p+(31*InitializeMetadata.width S.nnz p+35)+
    (15*(LogRats.records (List.ofFn S.source)).length+17)

structure Ready (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState) : Prop where
  bank : NatAssign.Bank ids (initial S p) s
  next : BankArray.Word s 95 (fixedWidth (InitializeMetadata.width S.nnz p) (Logical.sourceCircuit S p).size)
  room : (Logical.sourceCircuit S p).size < 2^InitializeMetadata.width S.nnz p
  rhs : s.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source))
  scratch : BankArray.Scratch s
  dimensionBlank : Blank s 503
  rhsBlank : s.tapes 508=BitTape.blank

structure Data (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState) : Prop where
  numeric : Numeric S p s
  circuitSize : Word s 503 (Logical.sourceCircuit S p).size
  rhs : s.tapes 508=BitTape.ofList (LogRats.records (List.ofFn S.source))

theorem Numeric.transport {S : Source.SparseSystem} {p : ℕ} {s t : BitRAMState}
    (h : Numeric S p s) (keep : ∀ i, 500 ≤ i → i ≤ 509 → i ≠ 503 → i ≠ 508 → t.tapes i=s.tapes i) :
    Numeric S p t := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
  | exact word_of_eq (keep _ (by decide) (by decide) (by decide) (by decide)) h.dimension
  | exact word_of_eq (keep _ (by decide) (by decide) (by decide) (by decide)) h.count
  | exact word_of_eq (keep _ (by decide) (by decide) (by decide) (by decide)) h.precisionWord
  | exact word_of_eq (keep _ (by decide) (by decide) (by decide) (by decide)) h.matrixNumerator
  | exact word_of_eq (keep _ (by decide) (by decide) (by decide) (by decide)) h.matrixDenominator
  | exact word_of_eq (keep _ (by decide) (by decide) (by decide) (by decide)) h.sourceNumerator
  | exact word_of_eq (keep _ (by decide) (by decide) (by decide) (by decide)) h.sourceDenominator
  | exact word_of_eq (keep _ (by decide) (by decide) (by decide) (by decide)) h.power

/-- Retention executes copies and canonical trimming; no source value is
introduced by an uncharged state update. -/
theorem executes (S : Source.SparseSystem) (p : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (hs : Ready S p s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ price S p ∧ Data S p t.val ∧
      BankArray.Scratch t.val ∧ BinaryPrecision.Frame work s.val t.val := by
  have small : NatAssign.Scratch s.val := by
    intro i hi
    interval_cases i
    · exact hs.scratch.1
    · exact hs.scratch.2.1
    · exact hs.scratch.2.2.1
    · exact hs.scratch.2.2.2.1
  obtain ⟨cn,a,ea,hcn,ab,ascratch,af⟩ := NatAssign.executes ids ids_lower statements valid
    (initial S p) input tape s hs.bank small
  have keepA (i : ℕ) (hi : i ∉ NatAssign.changes statements) := af.tapes i hi
  have no503 : 503 ∉ NatAssign.changes statements := by decide
  have no508 : 508 ∉ NatAssign.changes statements := by decide
  obtain ⟨cd,b,eb,hcd,bsize,bf⟩ := dimension input tape (InitializeMetadata.width S.nnz p)
    (Logical.sourceCircuit S p).size hs.room a
    (BankArray.word_of_eq (keepA 95 (by decide)) hs.next)
    (blank_of_eq (keepA 503 no503) hs.dimensionBlank)
  have b20 : b.val.tapes 20=BitTape.shifted (LogRats.records (List.ofFn S.source)) 0 := by
    simpa [BitTape.ofList,BitTape.shifted] using
      (bf.tapes 20 (by decide)).trans ((keepA 20 (by decide)).trans hs.rhs)
  have b508 : b.val.tapes 508=BitTape.blank :=
    (bf.tapes 508 (by decide)).trans ((keepA 508 no508).trans hs.rhsBlank)
  obtain ⟨t,et,ttapes,tf⟩ := WordCall.clone 20 508 (by decide) input tape
    (LogRats.records (List.ofFn S.source)) 0 0 b b20 b508
  have frameT : BinaryPrecision.Frame {508} b.val t.val :=
    ⟨tf.1,tf.2.1,tf.2.2.1,tf.2.2.2.1,tf.2.2.2.2.1,by
      intro i hi
      have hne : i≠508 := by simpa using hi
      simp [ttapes,hne]⟩
  have numericB := (numeric_of_bank S p a.val ab).transport
    (fun i _ _ hi _ => bf.tapes i (by simpa using hi))
  have numericT := numericB.transport
    (fun i _ _ _ hi => frameT.tapes i (by simpa using hi))
  have frame : BinaryPrecision.Frame work s.val t.val :=
    (af.mono (by decide)).trans ((bf.mono (by decide)).trans (frameT.mono (by decide)))
  have ts : NatAssign.Scratch t.val := fun i hi =>
    blank_of_eq ((frameT.tapes i (by simp; omega)).trans (bf.tapes i (by simp; omega))) (ascratch i hi)
  refine ⟨cn+(cd+_),t,ea.seq (eb.seq et),?_,
    ⟨numericT,word_of_eq (frameT.tapes 503 (by decide)) bsize,?_⟩,?_,frame⟩
  · dsimp [price,numericPrice]
    omega
  · simp [ttapes,BitTape.shifted,BitTape.ofList]
  · exact ⟨ts 0 (by decide),ts 1 (by decide),ts 2 (by decide),ts 3 (by decide),
      blank_of_eq (frame.tapes 5 (by decide)) hs.scratch.2.2.2.2.1,
      blank_of_eq (frame.tapes 6 (by decide)) hs.scratch.2.2.2.2.2.1,
      blank_of_eq (frame.tapes 8 (by decide)) hs.scratch.2.2.2.2.2.2.1,
      blank_of_eq (frame.tapes 9 (by decide)) hs.scratch.2.2.2.2.2.2.2⟩

end Maxwell.Cost.SourceGraph.Retain
