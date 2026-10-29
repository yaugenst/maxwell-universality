import Maxwell.Cost.RealSourceNormalize.Correctness
import Maxwell.Cost.RealSourceSerialize.Endpoint

namespace Maxwell.Cost.RealSourcePreprocess
open RealNatCode (Layout StoredWord)
open RealSimulation.Control
open RealNormalize (normalized scale)
set_option maxRecDepth 20000

def code : Code := .seq RealSourceNormalize.code RealSourceSerialize.code
def program : Machine := code.compile

def workBound (d m p B : ℕ) : ℕ :=
  (59 * p + 232 + 46 * B) * m + (59 * p + 189) * d + 46 * d.size + 23 * m.size + 120

noncomputable def word (d m p : ℕ) (rows columns : ℕ → ℕ) (values rhs : ℕ → ℝ) : List Bool :=
  RealSourceSerialize.word d m p rows columns (normalized true m values) (normalized false d rhs)

/-- One finite program normalizes the two arrays, rounds every value,
and writes the complete canonical source record. Recovery scales remain
in actual real registers; external input and random cursor are unchanged. -/
theorem executes (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (rb cb vb d m p B : ℕ) (rows columns : ℕ → ℕ) (values rhs : ℕ → ℝ) (s : Store)
    (hrb : 32 ≤ rb) (hcb : 64 ≤ cb) (hvb : 32 ≤ vb) (hsep : rb + m ≤ vb)
    (hcache : cb + 2 * m ≤ L.cache) (hbuffer : cb + 2 * m ≤ L.buffer)
    (hlabels : ∀ j < m, (rows j).size ≤ B ∧ (columns j).size ≤ B)
    (hreal : s.val.indices 25 = rb) (hcoords : s.val.indices 28 = cb)
    (hd : s.val.indices 52 = d) (hm : s.val.indices 53 = m) (hvbreg : s.val.indices 54 = vb)
    (hp : s.val.indices 27 = p) (hc : s.val.indices 20 = L.cache)
    (hb : s.val.indices 21 = L.buffer) (hs : s.val.indices 22 = L.stride)
    (hv : ∀ j < m, s.val.words (rb + j) = values j)
    (hco : ∀ j < m, s.val.indices (cb + 2 * j) = rows j ∧ s.val.indices (cb + 2 * j + 1) = columns j)
    (hrhs : ∀ j < d, s.val.words (vb + j) = rhs j) :
    ∃ cost : ℕ, ∃ t : Store, cost ≤ workBound d m p B ∧ Executes input tape code cost s t ∧
      StoredWord t.val L (word d m p rows columns values rhs) ∧
      t.val.indices 21 = L.bufferAt (word d m p rows columns values rhs).length ∧
      t.val.words 20 = scale true m values ∧ t.val.words 21 = scale false d rhs ∧
      t.val.output = s.val.output ∧ t.val.indexOutput = s.val.indexOutput ∧
      t.val.randomCursor = s.val.randomCursor := by
  obtain ⟨a, hea, hva, hra, hmatrixScale, hsourceScale, hframe, hoa, hioa, hranda⟩ :=
    RealSourceNormalize.executes input tape rb vb d m values rhs s hrb hvb hsep hreal hd hm hvbreg hv hrhs
  have metadata (i : ℕ) (hi : 4 ≤ i) (h24 : i ≠ 24) (h26 : i ≠ 26) (h55 : i ≠ 55) :
      a.val.indices i = s.val.indices i := hframe i hi h24 h26 h55
  have hcoords' : ∀ j < m, a.val.indices (cb + 2 * j) = rows j ∧
      a.val.indices (cb + 2 * j + 1) = columns j := by
    intro j hj
    exact ⟨(metadata _ (by omega) (by omega) (by omega) (by omega)).trans (hco j hj).1,
      (metadata _ (by omega) (by omega) (by omega) (by omega)).trans (hco j hj).2⟩
  obtain ⟨c, t, hcst, het, hstored, hcursor, hot, hiot, hrandt⟩ :=
    RealSourceSerialize.executes input tape L rb cb vb d m p B rows columns
      (normalized true m values) (normalized false d rhs) a hrb hcb hvb hcache hbuffer hlabels
      ((metadata 25 (by omega) (by omega) (by omega) (by omega)).trans hreal)
      ((metadata 28 (by omega) (by omega) (by omega) (by omega)).trans hcoords)
      ((metadata 52 (by omega) (by omega) (by omega) (by omega)).trans hd)
      ((metadata 53 (by omega) (by omega) (by omega) (by omega)).trans hm)
      ((metadata 54 (by omega) (by omega) (by omega) (by omega)).trans hvbreg)
      ((metadata 27 (by omega) (by omega) (by omega) (by omega)).trans hp)
      ((metadata 20 (by omega) (by omega) (by omega) (by omega)).trans hc)
      ((metadata 21 (by omega) (by omega) (by omega) (by omega)).trans hb)
      ((metadata 22 (by omega) (by omega) (by omega) (by omega)).trans hs) hva hcoords' hra
  refine ⟨22 * m + 22 * d + 44 + c, t, ?_, hea.seq het, hstored, hcursor, ?_, ?_,
    hot.trans hoa, hiot.trans hioa, hrandt.trans hranda⟩
  · dsimp [workBound]
    nlinarith
  · exact (het.compiled_steps.high_word RealSourceSerialize.program_words_bound 20 (by omega)).trans hmatrixScale
  · exact (het.compiled_steps.high_word RealSourceSerialize.program_words_bound 21 (by omega)).trans hsourceScale

theorem run (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (rb cb vb d m p B : ℕ) (rows columns : ℕ → ℕ) (values rhs : ℕ → ℝ) (s : Store)
    (hrb : 32 ≤ rb) (hcb : 64 ≤ cb) (hvb : 32 ≤ vb) (hsep : rb + m ≤ vb)
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
      t.words 20 = scale true m values ∧ t.words 21 = scale false d rhs ∧
      t.output = s.val.output ∧ t.indexOutput = s.val.indexOutput ∧ t.randomCursor = s.val.randomCursor := by
  obtain ⟨cost, t, hcost, he, hstored, hcursor, hmatrix, hsource, ho, hio, hr⟩ :=
    executes input tape L rb cb vb d m p B rows columns values rhs s hrb hcb hvb hsep hcache hbuffer
      hlabels hreal hcoords hd hm hvbreg hp hc hb hs hv hco hrhs
  obtain ⟨hf, hc⟩ := he.compiled_run (workBound d m p B + 1) (by omega)
  exact ⟨t.place code.size, hf, hc.le.trans hcost, hstored, hcursor, hmatrix, hsource, ho, hio, hr⟩

end Maxwell.Cost.RealSourcePreprocess
