import Maxwell.Cost.RealSourceSerialize.Correctness
import Maxwell.Cost.RealVectorCode
import Maxwell.Cost.RealWordFrame
import Maxwell.Codec.Source

namespace Maxwell.Cost.RealSourceSerialize
open RealNatCode (Layout StoredWord)
open RealSimulation.Control
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def workBound (d m p B : ℕ) : ℕ :=
  (59 * p + 210 + 46 * B) * m + (59 * p + 167) * d + 46 * d.size + 23 * m.size + 76

theorem program_words_bound : program.writesWordsBelow 17 = true := by decide

theorem run (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (rb cb vb d m p B : ℕ) (rows columns : ℕ → ℕ) (values rhs : ℕ → ℝ) (s : Store)
    (hrb : 32 ≤ rb) (hcb : 64 ≤ cb) (hvb : 32 ≤ vb)
    (hcache : cb + 2 * m ≤ L.cache) (hbuffer : cb + 2 * m ≤ L.buffer)
    (hlabels : ∀ j < m, (rows j).size ≤ B ∧ (columns j).size ≤ B)
    (hreal : s.val.indices 25 = rb) (hcoords : s.val.indices 28 = cb)
    (hd : s.val.indices 52 = d) (hm : s.val.indices 53 = m) (hvbreg : s.val.indices 54 = vb)
    (hp : s.val.indices 27 = p) (hc : s.val.indices 20 = L.cache)
    (hb : s.val.indices 21 = L.buffer) (hs : s.val.indices 22 = L.stride)
    (hv : ∀ j < m, s.val.words (rb + j) = values j)
    (hco : ∀ j < m, s.val.indices (cb + 2 * j) = rows j ∧ s.val.indices (cb + 2 * j + 1) = columns j)
    (hrhs : ∀ j < d, s.val.words (vb + j) = rhs j) :
    ∃ t : RAMState,
      (runCapped (program.next input tape) (workBound d m p B + 1) s.val).finished = some t ∧
      (runCapped (program.next input tape) (workBound d m p B + 1) s.val).instructions ≤ workBound d m p B ∧
      StoredWord t L (word d m p rows columns values rhs) ∧
      t.indices 21 = L.bufferAt (word d m p rows columns values rhs).length ∧
      (∀ i, 17 ≤ i → t.words i = s.val.words i) ∧ t.output = s.val.output ∧
      t.indexOutput = s.val.indexOutput ∧ t.randomCursor = s.val.randomCursor := by
  obtain ⟨cost, t, hcost, he, hstored, hcursor, ho, hio, hr⟩ :=
    executes input tape L rb cb vb d m p B rows columns values rhs s hrb hcb hvb hcache hbuffer
      hlabels hreal hcoords hd hm hvbreg hp hc hb hs hv hco hrhs
  obtain ⟨hf, hc⟩ := he.compiled_run (workBound d m p B + 1) (by simpa [workBound] using Nat.lt_succ_of_le hcost)
  exact ⟨t.place code.size, hf, hc.le.trans hcost, hstored, hcursor,
    fun i hi => he.compiled_steps.high_word program_words_bound i hi, ho, hio, hr⟩

def entryCode (e : ℕ × ℕ × ℚ) : List Bool :=
  Codec.nat e.1 ++ Codec.nat e.2.1 ++ Codec.rat e.2.2

noncomputable def entries (m p : ℕ) (rows columns : ℕ → ℕ) (values : ℕ → ℝ) : List (ℕ × ℕ × ℚ) :=
  (List.range m).map (fun i => (rows i, columns i, RealMidpoint.approximation (values i) p))

noncomputable def record (d m p : ℕ) (rows columns : ℕ → ℕ) (values rhs : ℕ → ℝ) : Codec.SourceRecord :=
  ⟨d, entries m p rows columns values, RealVectorCode.values rhs p d⟩

theorem word_eq_record (d m p : ℕ) (rows columns : ℕ → ℕ) (values rhs : ℕ → ℝ) :
    word d m p rows columns values rhs = Codec.nat d ++
      Codec.list entryCode (entries m p rows columns values) ++
      Codec.list Codec.rat (RealVectorCode.values rhs p d) := by
  simp [word, Codec.list, entries, entryCode, RealVectorCode.values,
    RealSparseCode.word_eq_flatMap, RealArrayCode.word_eq_flatMap, List.flatMap_map,
    RealRecordCode.word, List.append_assoc]

theorem readEntry_append (e : ℕ × ℕ × ℚ) (tail : List Bool) :
    Codec.readSourceEntry (entryCode e ++ tail) = some (e, tail) := by
  simp [Codec.readSourceEntry, entryCode, List.append_assoc, Codec.readNat_append, Codec.readRat_append]

/-- The emitted bytes are parsed by the authoritative source parser. -/
theorem read_word (d m p : ℕ) (rows columns : ℕ → ℕ) (values rhs : ℕ → ℝ) (tail : List Bool) :
    Codec.readSource (word d m p rows columns values rhs ++ tail) =
      some (record d m p rows columns values rhs, tail) := by
  rw [word_eq_record]
  simp [Codec.readSource, List.append_assoc, Codec.readNat_append,
    Codec.readList_append entryCode Codec.readSourceEntry readEntry_append,
    Codec.readList_append Codec.rat Codec.readRat Codec.readRat_append, record]

/-- Local array bindings to canonical ordered support and RHS identify the
actual emitted buffer with the exact input codec expected by the Bit-RAM encoder. -/
theorem word_eq_source (S : Source.SparseSystem) (m p : ℕ)
    (rows columns : ℕ → ℕ) (values rhs : ℕ → ℝ)
    (he : entries m p rows columns values = (Codec.sourceRecord S).entries)
    (hb : RealVectorCode.values rhs p S.n = (Codec.sourceRecord S).rhs) :
    word S.n m p rows columns values rhs = Codec.source S := by
  rw [word_eq_record, he, hb]
  simp [Codec.source, Codec.sourceRecord, Codec.list, Codec.vector, List.flatMap_map,
    entryCode, Codec.sourceEntryValue]
  congr 1
  funext a
  simp [Codec.sourceEntry, List.append_assoc]

theorem record_length_le (m p B : ℕ) (rows columns : ℕ → ℕ) (values : ℕ → ℝ)
    (hlabels : ∀ j < m, (rows j).size ≤ B ∧ (columns j).size ≤ B) :
    (RealSparseCode.word rows columns values p m).length ≤ (4 * B + 4 * p + 11) * m := by
  induction m with
  | zero => simp [RealSparseCode.word]
  | succ m ih =>
    have ih' := ih (by intro j hj; exact hlabels j (by omega))
    have hl := hlabels m (by omega)
    have hr := RealVectorCode.rational_length_le (values m) p
    simp only [RealSparseCode.word, RealRecordCode.word, List.length_append, RealNatCode.code_length]
    nlinarith

theorem word_length_le (d m p B : ℕ) (rows columns : ℕ → ℕ) (values rhs : ℕ → ℝ)
    (hlabels : ∀ j < m, (rows j).size ≤ B ∧ (columns j).size ≤ B) :
    (word d m p rows columns values rhs).length ≤
      4 * d.size + 2 * m.size + 3 + (4 * B + 4 * p + 11) * m + (4 * p + 9) * d := by
  have he := record_length_le m p B rows columns values hlabels
  have hb := RealVectorCode.word_length_le rhs p d
  simp only [word, List.length_append, RealNatCode.code_length]
  omega

end Maxwell.Cost.RealSourceSerialize
