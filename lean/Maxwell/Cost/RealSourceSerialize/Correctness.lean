import Maxwell.Cost.RealSourceSerialize.Primitives

namespace Maxwell.Cost.RealSourceSerialize
open RealNatCode (Layout StoredWord)
open RealSimulation.Control
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def code : Code :=
  .seq (natCode 52) (.seq (natCode 53) (.seq (.call recordSetup)
    (.seq (.call RealSparseCode.program) (.seq (natCode 52)
      (.seq (.call vectorSetup) (.call RealArrayCode.program))))))

def program : Machine := code.compile

noncomputable def word (d m p : ℕ) (rows columns : ℕ → ℕ) (values rhs : ℕ → ℝ) : List Bool :=
  ((Codec.nat d ++ Codec.nat m) ++ RealSparseCode.word rows columns values p m) ++
    Codec.nat d ++ RealArrayCode.word rhs p d

/-- Full source framing is emitted by one fixed finite machine, reading
the coefficient, coordinate, and right-hand-side arrays in caller memory. -/
theorem executes (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
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
    ∃ cost : ℕ, ∃ t : Store,
      cost ≤ (59 * p + 210 + 46 * B) * m + (59 * p + 167) * d +
        46 * d.size + 23 * m.size + 76 ∧
      Executes input tape code cost s t ∧ StoredWord t.val L (word d m p rows columns values rhs) ∧
      t.val.indices 21 = L.bufferAt (word d m p rows columns values rhs).length ∧
      t.val.output = s.val.output ∧ t.val.indexOutput = s.val.indexOutput ∧
      t.val.randomCursor = s.val.randomCursor := by
  let w₀ := Codec.nat d ++ Codec.nat m
  let w₁ := w₀ ++ RealSparseCode.word rows columns values p m
  let w₂ := w₁ ++ Codec.nat d
  let L₁ := L.shiftBuffer (Codec.nat d).length
  let L₂ := L.shiftBuffer w₀.length
  let L₃ := L.shiftBuffer w₁.length
  let L₄ := L.shiftBuffer w₂.length
  obtain ⟨s₁, he₁, hstored₁, hcursor₁, hw₁, hi₁, ho₁, hio₁, hr₁⟩ :=
    nat_executes input tape L 52 d s hd hc hb hs
  have meta₁ (i : ℕ) (hi : 11 ≤ i) (hi' : i < 256) (hne : i ≠ 21) :
      s₁.val.indices i = s.val.indices i :=
    hi₁ i (RealNatAppend.outside_metadata L i hi hi' hne)
  obtain ⟨s₂, he₂, hstored₂, hcursor₂, hw₂, hi₂, ho₂, hio₂, hr₂⟩ :=
    nat_executes input tape L₁ 53 m s₁ ((meta₁ 53 (by omega) (by omega) (by omega)).trans hm)
      ((meta₁ 20 (by omega) (by omega) (by omega)).trans hc) hcursor₁
      ((meta₁ 22 (by omega) (by omega) (by omega)).trans hs)
  have meta₂ (i : ℕ) (hi : 11 ≤ i) (hi' : i < 256) (hne : i ≠ 21) :
      s₂.val.indices i = s.val.indices i :=
    (hi₂ i (RealNatAppend.outside_metadata L₁ i hi hi' hne)).trans (meta₁ i hi hi' hne)
  have words₂ : s₂.val.words = s.val.words := hw₂.trans hw₁
  have header₂ : StoredWord s₂.val L w₀ := by
    apply RealNatCode.storedWord_append
    · intro j hj
      exact (hi₂ _ (RealNatAppend.outside_prefix L _ j hj)).trans (hstored₁ j hj)
    · exact hstored₂
  have cursor₂ : s₂.val.indices 21 = L₂.buffer := by
    simpa [L₁, L₂, w₀, Layout.shiftBuffer_bufferAt, Layout.shiftBuffer, Layout.bufferAt,
      Nat.mul_add, Nat.add_assoc] using hcursor₂
  let a := recordState s₂
  have avalues : ∀ j < m, a.val.words (rb + j) = values j := by
    intro j hj
    exact (congrFun words₂ (rb + j)).trans (hv j hj)
  have acoords : ∀ j < m, a.val.indices (cb + 2 * j) = rows j ∧
      a.val.indices (cb + 2 * j + 1) = columns j := by
    intro j hj
    have hh (i : ℕ) (hi : cb ≤ i) (hi' : i < cb + 2 * m) : a.val.indices i = s.val.indices i := by
      have hi0 := RealSparseCode.outside_coordinate L cb m 0 i hcb hcache hbuffer hi hi'
      have hi0' : RealNatAppend.Outside L i := by simpa [RealNatAppend.Outside, Layout.shiftBuffer, Layout.cacheAt, Layout.bufferAt] using hi0
      have he := (hi₂ i (hi0'.shift (Codec.nat d).length)).trans (hi₁ i hi0')
      simpa [a, recordState, Store.ofState, RAMState.setIndex, show i ≠ 26 by omega] using he
    exact ⟨(hh _ (by omega) (by omega)).trans (hco j hj).1,
      (hh _ (by omega) (by omega)).trans (hco j hj).2⟩
  obtain ⟨c₃, r₃, hc₃, ht₃, hpc₃, hstored₃, hcursor₃, hw₃, hi₃, _, ho₃, hio₃, hr₃,
      hcache₃, hstride₃, hprecision₃⟩ :=
    RealSparseCode.terminates input tape L₂ rb cb m p B rows columns values a.val hrb hcb hcache
      (by change cb + 2 * m ≤ L.buffer + L.stride * w₀.length; omega) hlabels a.property
      (by simpa [a, recordState, Store.ofState, RAMState.setIndex] using (meta₂ 25 (by omega) (by omega) (by omega)).trans hreal)
      (by simpa [a, recordState, Store.ofState, RAMState.setIndex] using (meta₂ 28 (by omega) (by omega) (by omega)).trans hcoords)
      (by simp [a, recordState, Store.ofState, RAMState.setIndex, meta₂ 53 (by omega) (by omega) (by omega), hm])
      (by simpa [a, recordState, Store.ofState, RAMState.setIndex] using (meta₂ 27 (by omega) (by omega) (by omega)).trans hp)
      (by simpa [a, recordState, Store.ofState, RAMState.setIndex, L₂, Layout.shiftBuffer] using (meta₂ 20 (by omega) (by omega) (by omega)).trans hc)
      (by simpa [a, recordState, Store.ofState, RAMState.setIndex] using cursor₂)
      (by simpa [a, recordState, Store.ofState, RAMState.setIndex, L₂, Layout.shiftBuffer] using (meta₂ 22 (by omega) (by omega) (by omega)).trans hs)
      avalues acoords
  let s₃ := Store.ofState r₃
  have he₃ := Executes.call RealSparseCode.program a r₃ c₃ ht₃.toSteps (by
    simp [RealSparseCode.program, RealRecordCode.program, RealNatAppend.program, RealNatCode.program,
      RealRoundRat.program, RealMidpointRegister.program, RealMidpointRegister.kernel,
      RealMidpoint.program, RealRound.program, RealMidpointRegister.adapt, RealRatCode.program, hpc₃])
  have meta₃ (i : ℕ) (hi : 47 ≤ i) (hi' : i < 256) : s₃.val.indices i = s.val.indices i := by
    have he := hi₃ i hi (RealNatAppend.outside_metadata L₂ i (by omega) hi' (by omega))
    simpa [s₃, Store.ofState, a, recordState, RAMState.setIndex, show i ≠ 26 by omega,
      meta₂ i (by omega) hi' (by omega)] using he
  have header₃ : StoredWord s₃.val L w₁ := by
    apply RealNatCode.storedWord_append
    · intro j hj
      have he := hi₃ (L.bufferAt j) (by have := L.bufferAt_ge j; omega)
        (RealNatAppend.outside_prefix L _ j hj)
      simpa [s₃, a, recordState, Store.ofState, RAMState.setIndex, header₂ j hj] using he
    · exact hstored₃
  have cursor₃ : s₃.val.indices 21 = L₃.buffer := by
    simpa [s₃, Store.ofState, L₂, L₃, w₁, Layout.shiftBuffer, Layout.bufferAt, Nat.mul_add, Nat.add_assoc] using hcursor₃
  obtain ⟨s₄, he₄, hstored₄, hcursor₄, hw₄, hi₄, ho₄, hio₄, hr₄⟩ :=
    nat_executes input tape L₃ 52 d s₃ ((meta₃ 52 (by omega) (by omega)).trans hd)
      hcache₃ cursor₃ hstride₃
  have meta₄ (i : ℕ) (hi : 11 ≤ i) (hi' : i < 256) (hne : i ≠ 21) :
      s₄.val.indices i = s₃.val.indices i :=
    hi₄ i (RealNatAppend.outside_metadata L₃ i hi hi' hne)
  have header₄ : StoredWord s₄.val L w₂ := by
    apply RealNatCode.storedWord_append
    · intro j hj
      exact (hi₄ _ (RealNatAppend.outside_prefix L _ j hj)).trans (header₃ j hj)
    · exact hstored₄
  have cursor₄ : s₄.val.indices 21 = L₄.buffer := by
    simpa [L₃, L₄, w₂, Layout.shiftBuffer, Layout.bufferAt, Nat.mul_add, Nat.add_assoc] using hcursor₄
  let b := vectorState s₄
  have bvalues : ∀ j < d, b.val.words (vb + j) = rhs j := by
    intro j hj
    exact ((congrFun hw₄ (vb + j)).trans ((hw₃ (vb + j) (by omega)).trans
      (congrFun words₂ (vb + j)))).trans (hrhs j hj)
  obtain ⟨c₅, r₅, hc₅, ht₅, hpc₅, hstored₅, hcursor₅, _, ho₅, hio₅, hr₅, hi₅⟩ :=
    RealArrayCode.terminates input tape L₄ vb d p rhs b.val hvb b.property
      (by simp [b, vectorState, Store.ofState, RAMState.setIndex,
        meta₄ 54 (by omega) (by omega) (by omega), meta₃ 54 (by omega) (by omega), hvbreg])
      (by simp [b, vectorState, Store.ofState, RAMState.setIndex,
        meta₄ 52 (by omega) (by omega) (by omega), meta₃ 52 (by omega) (by omega), hd])
      (by simpa [b, vectorState, Store.ofState, RAMState.setIndex] using
        (meta₄ 27 (by omega) (by omega) (by omega)).trans hprecision₃)
      (by simpa [b, vectorState, Store.ofState, RAMState.setIndex, L₂, L₄, Layout.shiftBuffer] using
        (meta₄ 20 (by omega) (by omega) (by omega)).trans hcache₃)
      (by simpa [b, vectorState, Store.ofState, RAMState.setIndex] using cursor₄)
      (by simpa [b, vectorState, Store.ofState, RAMState.setIndex, L₂, L₄, Layout.shiftBuffer] using
        (meta₄ 22 (by omega) (by omega) (by omega)).trans hstride₃) bvalues
  have he₅ := Executes.call RealArrayCode.program b r₅ c₅ ht₅.toSteps (by
    simp [RealArrayCode.program, RealRoundRat.program, RealMidpointRegister.program,
      RealMidpointRegister.kernel, RealMidpoint.program, RealRound.program,
      RealMidpointRegister.adapt, RealRatCode.program, RealNatCode.program, hpc₅])
  have header₅ : StoredWord r₅ L w₂ := by
    intro j hj
    have he := hi₅ (L.bufferAt j) (RealArrayCode.outside_prefix L _ j hj)
    simpa [b, vectorState, Store.ofState, RAMState.setIndex, header₄ j hj] using he
  have hall := RealNatCode.storedWord_append r₅ L w₂ (RealArrayCode.word rhs p d) header₅ hstored₅
  refine ⟨_, Store.ofState r₅, ?_, he₁.seq (he₂.seq ((recordSetup_executes input tape s₂).seq
    (he₃.seq (he₄.seq ((vectorSetup_executes input tape s₄).seq he₅))))), hall, ?_, ?_, ?_, ?_⟩
  · omega
  · simpa [Store.ofState, L₄, w₂, w₁, w₀, word, Layout.shiftBuffer_bufferAt, Nat.add_assoc] using hcursor₅
  · exact ho₅.trans (ho₄.trans (ho₃.trans (ho₂.trans ho₁)))
  · exact hio₅.trans (hio₄.trans (hio₃.trans (hio₂.trans hio₁)))
  · exact hr₅.trans (hr₄.trans (hr₃.trans (hr₂.trans hr₁)))


end Maxwell.Cost.RealSourceSerialize
