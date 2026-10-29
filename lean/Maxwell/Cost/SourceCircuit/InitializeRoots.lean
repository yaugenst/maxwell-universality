import Maxwell.Cost.SourceCircuit.Roots
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.SourceCircuit
open Structured
open RationalAccumulator (Blank)

def initializeRootBody : Code :=
  .seq (BankArray.writeCode 90 91 92 91) (BankArray.incrementCode 91)

def initializeRootsCode : Code := CountedShifted.code 100 initializeRootBody

def rootInitWork : Finset ℕ := {91,100}

theorem rootInit_counted_frame {s t : Store} (h : CountedShifted.Frame 100 s t) :
    Frame rootInitWork s.val t.val := by
  refine ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,?_,?_,?_⟩
  · intro j _ hj
    have hj100 : j ≠ 100 := by intro he; exact hj (by simp [rootInitWork,he])
    exact h.2.2.2.2.2.1 j hj100
  · exact h.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)
  · intro j hj
    exact h.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)

def initializeRootBodyCost (width base : List Bool) : ℕ :=
  BankArray.costCap width (List.replicate (addressValue width) false)
    base (List.replicate (addressValue width) false) + 12*addressValue width+18

structure RootInitData (n : ℕ) where
  index : List Bool
  roots : Vector (List Bool) n

structure RootInitInv (n : ℕ) (width base : List Bool) (remaining : ℕ) (d : RootInitData n) (s : Store) : Prop where
  total : addressValue d.index + remaining = n
  length : d.index.length = addressValue width
  indexWord : BankArray.Word s.val 91 d.index
  array : BitArray.Represents s.val.memory (addressValue base) (addressValue width) d.roots
  written : ∀ i : Fin n, i.val < addressValue d.index → addressValue (d.roots.get i) = i.val
  scratch : BankArray.Scratch s.val
  widthWord : BankArray.Word s.val 90 width
  baseWord : BankArray.Word s.val 92 base
  seven : Blank s.val 7

/-- A specification of the preexisting cells, which initialization will
overwrite. No initial zero-memory assumption is needed. -/
def rootSnapshot (n : ℕ) (memory : ℕ → Bool) (base width : ℕ) : Vector (List Bool) n :=
  Vector.ofFn fun i => MemoryWord.readBits memory (base+i.val*width) width

theorem rootSnapshot_represents (n : ℕ) (memory : ℕ → Bool) (base width : ℕ) :
    BitArray.Represents memory base width (rootSnapshot n memory base width) := by
  constructor
  case length =>
    intro i
    simp [rootSnapshot,Vector.get]
  case bits =>
    intro i j hj
    simpa [rootSnapshot,Vector.get,Fin.cast] using (MemoryWord.readBits_getElem memory (base+i.val*width) width j hj).symm

theorem rootInit_ready (n : ℕ) (width base : List Bool) (s : Store)
    (hs : BankArray.Scratch s.val) (hw : BankArray.Word s.val 90 width)
    (hb : BankArray.Word s.val 92 base)
    (hi : BankArray.Word s.val 91 (List.replicate (addressValue width) false))
    (h7 : Blank s.val 7) :
    RootInitInv n width base n
      ⟨List.replicate (addressValue width) false,
        rootSnapshot n s.val.memory (addressValue base) (addressValue width)⟩ s := by
  have hz : addressValue (List.replicate (addressValue width) false) = 0 := by
    induction addressValue width with
    | zero => rfl
    | succ w ih => simp [List.replicate_succ,addressValue,ih]
  refine ⟨by simp [hz],by simp,hi,rootSnapshot_represents _ _ _ _,?_,hs,hw,hb,h7⟩
  intro i hi
  simp only [hz] at hi
  omega

theorem RootInitInv.stable {n remaining : ℕ} {width base : List Bool} {d : RootInitData n} {s t : Store}
    (h : RootInitInv n width base remaining d s) (f : CountedShifted.Frame 100 s t) :
    RootInitInv n width base remaining d t := by
  refine ⟨h.total,h.length,
    BankArray.word_of_eq (f.2.2.2.2.2.1 91 (by omega)) h.indexWord,
    ?_,h.written,
    scratch_of_tapes h.scratch (fun j hj => f.2.2.2.2.2.1 j (by omega)),
    BankArray.word_of_eq (f.2.2.2.2.2.1 90 (by omega)) h.widthWord,
    BankArray.word_of_eq (f.2.2.2.2.2.1 92 (by omega)) h.baseWord,
    RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 7 (by decide)) h.seven⟩
  simpa [f.2.2.1] using h.array

set_option maxRecDepth 8192 in
theorem initializeRootBody_executes (input : List Bool) (tape : ℕ → Bool)
    (n remaining : ℕ) (width base counter : List Bool) (counterOrigin : ℤ)
    (hwidth : 0 < width.length) (hroom : n < 2 ^ addressValue width)
    (d : RootInitData n) (s : Store) (h : RootInitInv n width base (remaining+1) d s)
    (hcounter : s.val.tapes 100 = BitTape.shifted counter counterOrigin) :
    ∃ cost t, Executes input tape initializeRootBody cost s t ∧
      (∃ nextData, RootInitInv n width base remaining nextData t) ∧
      t.val.tapes 100 = BitTape.shifted counter counterOrigin ∧
      cost ≤ initializeRootBodyCost width base ∧ Frame rootInitWork s.val t.val := by
  let i : Fin n := ⟨addressValue d.index,by have := h.total; omega⟩
  obtain ⟨wc,w,hwc,ew,_,wa,ws,w7,wf⟩ := BankArray.write_bank 90 91 92 91
    (by omega) (by omega) (by omega) (by omega) input tape width d.index base d.index
    d.roots i hwidth rfl h.length s h.scratch h.widthWord h.indexWord h.baseWord h.indexWord h.array
  have hiw : BankArray.Word w.val 91 d.index :=
    BankArray.word_of_eq (wf.2.2.2.1 91 (by omega)) h.indexWord
  obtain ⟨ic,t,hic,ei,ti,ts,tm,_,tk,tf⟩ := BankArray.increment_bank 91 (by omega)
    input tape d.index w hiw ws
  have hlen : (Increment.bits d.index).length = addressValue width := by
    rw [increment_length d.index (by rw [h.length]; have := h.total; omega),h.length]
  have ht : RootInitInv n width base remaining ⟨Increment.bits d.index,d.roots.set i d.index⟩ t := by
    refine ⟨?_,hlen,ti,?_,?_,ts,
      BankArray.word_of_eq ((tk 90 (by omega)).trans (wf.2.2.2.1 90 (by omega))) h.widthWord,
      BankArray.word_of_eq ((tk 92 (by omega)).trans (wf.2.2.2.1 92 (by omega))) h.baseWord,
      RationalAccumulator.blank_of_eq ((tk 7 (by decide)).trans w7) h.seven⟩
    · rw [Increment.bits_value]
      have := h.total
      omega
    · simpa [tm] using wa
    · intro j hj
      have hget : (d.roots.set i d.index).get j = if i = j then d.index else d.roots.get j := by
        simp [Vector.get,Fin.cast,Array.getElem_set,Fin.ext_iff]
      rw [hget]
      split_ifs with he
      · exact congrArg Fin.val he
      · apply h.written
        have hne : j.val ≠ addressValue d.index := by
          intro hh; apply he; exact Fin.ext hh.symm
        rw [Increment.bits_value] at hj
        omega
  refine ⟨_,t,ew.seq ei,⟨_,ht⟩,(tk 100 (by omega)).trans
    ((wf.2.2.2.1 100 (by omega)).trans hcounter),?_,
    ((frame_bank wf).mono (by simp)).trans
      ((frame_except tf).mono (by simp [rootInitWork]))⟩
  dsimp [initializeRootBodyCost]
  have hc : BankArray.costCap width d.index base d.index =
      BankArray.costCap width (List.replicate (addressValue width) false) base
        (List.replicate (addressValue width) false) := by
    simp [BankArray.costCap,ArrayAccess.costCap,h.length]
  rw [hc] at hwc
  rw [h.length] at hic
  omega

set_option maxRecDepth 8192 in
theorem initializeRoots_executes (input : List Bool) (tape : ℕ → Bool)
    (n : ℕ) (width base counter : List Bool) (counterOrigin : ℤ)
    (hwidth : 0 < width.length) (hroom : n < 2 ^ addressValue width)
    (hcounterValue : addressValue counter = n) (d : RootInitData n) (s : Store)
    (h : RootInitInv n width base n d s)
    (hcounter : s.val.tapes 100 = BitTape.shifted counter counterOrigin) :
    ∃ cost t finalCounter, cost ≤
        (n+1)*(13*counter.length+15)+n*initializeRootBodyCost width base ∧
      Executes input tape initializeRootsCode cost s t ∧
      t.val.tapes 100 = BitTape.shifted finalCounter counterOrigin ∧
      finalCounter.length = counter.length ∧
      Frame rootInitWork s.val t.val ∧
      ∃ nextData, RootInitInv n width base 0 nextData t ∧
        RepresentsRoots (Logical.CopyBank.initial n) nextData.roots := by
  let invariant := fun remaining u =>
    (∃ data, RootInitInv n width base remaining data u) ∧ Frame rootInitWork s.val u.val
  obtain ⟨cost,t,finalCounter,he,hi,hc,hlen,_,hcost⟩ := CountedShifted.executes 100 counterOrigin
    initializeRootBody input tape invariant
    (fun _ => initializeRootBodyCost width base)
    (by
      rintro remaining u v hf ⟨⟨data,hh⟩,frame⟩
      exact ⟨⟨data,hh.stable hf⟩,frame.trans (rootInit_counted_frame hf)⟩)
    (by
      rintro remaining xs u ⟨⟨data,hu⟩,frame⟩ hc _
      obtain ⟨cost,t,he,ht,hct,hcost,hframe⟩ := initializeRootBody_executes input tape n remaining width base xs
        counterOrigin hwidth hroom data u hu hc
      exact ⟨cost,t,he,⟨ht,frame.trans hframe⟩,hct,hcost⟩)
    n counter s hcounterValue hcounter ⟨⟨d,h⟩,⟨rfl,rfl,rfl,fun _ _ _ => rfl,rfl,fun _ _ => rfl⟩⟩
  obtain ⟨⟨nextData,hi⟩,hf⟩ := hi
  refine ⟨cost,t,finalCounter,?_,he,hc,hlen,hf,nextData,hi,?_⟩
  · simpa using hcost
  · intro i
    apply hi.written i
    have hh := hi.total
    have hit := i.isLt
    omega

end Maxwell.Cost.SourceCircuit
