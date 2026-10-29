import Maxwell.Cost.PhysicalMaterial.Dense
import Maxwell.Cost.PhysicalMaterial.Emit

/-! Per-cell emission reads the preprocessed dense strength arrays exactly
once. Its program does not scan the defect descriptors. -/
namespace Maxwell.Cost.PhysicalMaterial.DenseEmit
open Structured RationalAccumulator Maxwell.Spectral.Lattice
set_option maxHeartbeats 1000000

def readCode : Code :=
  .seq (BankArray.readCanonicalCode 300 322 320 301 272)
    (BankArray.readCanonicalCode 300 322 321 301 273)

private theorem ready_after {target : ℕ} {s t : BitRAMState} (ht : 10 ≤ target)
    (hs : Descriptors.Ready s) (hw : BankArray.Scratch t) (h7 : Blank t 7)
    (hf : BankArray.FrameExcept target s t) : Descriptors.Ready t := by
  obtain ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩ := hw
  intro i hi
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact blank_of_eq (hf.2.2.2.1 4 (by decide) (by omega)) (hs 4 (by decide))
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9

/-- Actual indexed reads of two fixed-width arrays, followed by physical
normalization into the selected-strength ports. Metadata and memory survive. -/
theorem read {cells : ℕ} (l : Dense.Layout cells) (nums dens : Vector (List Bool) cells)
    (i : Fin cells) (B : ℕ) (hl : l.Sized B) (hi : i.val.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Descriptors.Ready s.val) (hd : Dense.Stored l nums dens s.val)
    (hindex : Word s.val 322 i.val) (h272 : Blank s.val 272) (h273 : Blank s.val 273) :
    ∃ cost t, cost ≤ 40000*(B+2)^2 ∧ Executes input tape readCode cost s t ∧
      Word t.val 272 (addressValue (nums.get i)) ∧ Word t.val 273 (addressValue (dens.get i)) ∧
      Descriptors.Ready t.val ∧ Dense.Stored l nums dens t.val ∧
      Descriptors.Frame {272,273} s.val t.val := by
  obtain ⟨c1,a,hc1,e1,ha272,has,ha7,ham,_,f1⟩ := BankArray.read_canonical
    300 322 320 301 272 (by decide) (by decide) (by decide) (by decide) (by decide)
    input tape l.width i.val.bits l.numBase l.clock nums i l.width_nonempty (by simp)
    l.clock_length s hs.scratch (hs 7 (by decide)) h272 hd.width hindex hd.numBase hd.clock hd.nums
  have ha := ready_after (by decide) hs has ha7 f1
  have keepa (j : ℕ) (hj : 10 ≤ j) (hne : j ≠ 272) : a.val.tapes j = s.val.tapes j :=
    f1.2.2.2.1 j (Or.inr hj) hne
  obtain ⟨c2,t,hc2,e2,ht273,hts,ht7,htm,_,f2⟩ := BankArray.read_canonical
    300 322 321 301 273 (by decide) (by decide) (by decide) (by decide) (by decide)
    input tape l.width i.val.bits l.denBase l.clock dens i l.width_nonempty (by simp)
    l.clock_length a has ha7 (blank_of_eq (keepa 273 (by decide) (by decide)) h273)
    (BankArray.word_of_eq (keepa 300 (by decide) (by decide)) hd.width)
    (BankArray.word_of_eq (keepa 322 (by decide) (by decide)) hindex)
    (BankArray.word_of_eq (keepa 321 (by decide) (by decide)) hd.denBase)
    (BankArray.word_of_eq (keepa 301 (by decide) (by decide)) hd.clock)
    (by simpa only [ham] using hd.dens)
  have f : Descriptors.Frame {272,273} s.val t.val :=
    ⟨htm.trans ham,f2.1.trans f1.1,f2.2.1.trans f1.2.1,f2.2.2.1.trans f1.2.2.1,
      fun j hj hn => (f2.2.2.2.1 j hj (by simp only [Finset.mem_insert,Finset.mem_singleton] at hn; omega)).trans
        (f1.2.2.2.1 j hj (by simp only [Finset.mem_insert,Finset.mem_singleton] at hn; omega))⟩
  refine ⟨c1+c2,t,?_,e1.seq e2,
    word_of_eq (f2.2.2.2.1 272 (by decide) (by decide)) ha272,ht273,
    ready_after (by decide) ha hts ht7 f2,?_,f⟩
  · have h1 := CalibrationMatrix.Affine.read_cost_le l.width i.val.bits l.numBase l.clock B
      hl.1 hl.2.1 hi hl.2.2.1 l.clock_length
    have h2 := CalibrationMatrix.Affine.read_cost_le l.width i.val.bits l.denBase l.clock B
      hl.1 hl.2.1 hi hl.2.2.2 l.clock_length
    omega
  · exact ⟨BankArray.word_of_eq (f.tapes 300 (by decide) (by decide)) hd.width,
      BankArray.word_of_eq (f.tapes 301 (by decide) (by decide)) hd.clock,
      BankArray.word_of_eq (f.tapes 320 (by decide) (by decide)) hd.numBase,
      BankArray.word_of_eq (f.tapes 321 (by decide) (by decide)) hd.denBase,
      by simpa only [f.memory] using hd.nums,by simpa only [f.memory] using hd.dens⟩

def work : Finset ℕ := Emit.work ∪ Finset.range 10

structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  tapes : ∀ i ∉ work, t.tapes i = s.tapes i

structure Ready (x y z sn sd : ℕ) (s : Store) : Prop where
  xWord : Word s.val 240 x
  yWord : Word s.val 241 y
  zWord : Word s.val 242 z
  period : Word s.val 243 20
  clock : Word s.val 249 16
  sigmaNumerator : Word s.val 260 sn
  sigmaDenominator : Word s.val 261 sd
  blank : ∀ j ∈ work, Blank s.val j

def code (material : Cell20 → ℚ) : Code := .seq readCode (Emit.code material)

def costBound (material : Cell20 → ℚ) (x y z B : ℕ) : ℕ :=
  40000*(B+2)^2+Emit.costBound material x y z B

/-- A single fixed per-cell body with two array reads and canonical output.
The number of defect descriptors does not enter this execution bound. -/
theorem executes {cells : ℕ} (l : Dense.Layout cells) (nums dens : Vector (List Bool) cells)
    (i : Fin cells) (B : ℕ) (hl : l.Sized B) (hi : i.val.bits.length ≤ B)
    (material : Cell20 → ℚ) (hm : ∀ c, 0 ≤ material c)
    (input : List Bool) (tape : ℕ → Bool) (x y z sn sd : ℕ) (hsd : 0 < sd)
    (hden : 0 < addressValue (dens.get i))
    (hB : Arithmetic.Bounded (Emit.data material x y z sn sd
      (addressValue (nums.get i)) (addressValue (dens.get i))) B)
    (s : Store) (hs : Ready x y z sn sd s) (hd : Dense.Stored l nums dens s.val)
    (hindex : Word s.val 322 i.val) :
    ∃ cost t, cost ≤ costBound material x y z B ∧ Executes input tape (code material) cost s t ∧
      t.val.output = (Codec.rat (Emit.value material x y z sn sd
        (addressValue (nums.get i)) (addressValue (dens.get i)))).reverse ++ s.val.output ∧
      (∀ j ∈ work, Blank t.val j) ∧ Dense.Stored l nums dens t.val ∧
      Word t.val 322 i.val ∧ Frame s.val t.val := by
  have sr : Descriptors.Ready s.val := fun j hj => hs.blank j (Finset.mem_union_right _ (by simpa using hj))
  obtain ⟨c1,a,hc1,e1,ha272,ha273,har,had,f1⟩ := read l nums dens i B hl hi input tape s sr hd hindex
    (hs.blank 272 (by decide)) (hs.blank 273 (by decide))
  have er : Emit.Ready x y z sn sd (addressValue (nums.get i)) (addressValue (dens.get i)) a := by
    refine ⟨word_of_eq (f1.tapes 240 (by decide) (by decide)) hs.xWord,
      word_of_eq (f1.tapes 241 (by decide) (by decide)) hs.yWord,
      word_of_eq (f1.tapes 242 (by decide) (by decide)) hs.zWord,
      word_of_eq (f1.tapes 243 (by decide) (by decide)) hs.period,
      word_of_eq (f1.tapes 249 (by decide) (by decide)) hs.clock,
      word_of_eq (f1.tapes 260 (by decide) (by decide)) hs.sigmaNumerator,
      word_of_eq (f1.tapes 261 (by decide) (by decide)) hs.sigmaDenominator,ha272,ha273,?_⟩
    intro j hj
    by_cases hj10 : j < 10
    · exact har j hj10
    · apply blank_of_eq (f1.tapes j (Or.inr (by omega)) ?_)
        (hs.blank j ((by decide : Emit.scratch ⊆ work) hj))
      simp only [Emit.scratch,ArithmeticBank.work,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hj ⊢
      omega
  obtain ⟨c2,t,hc2,e2,hout,hblank,f2⟩ := Emit.executes material hm input tape x y z sn sd
    (addressValue (nums.get i)) (addressValue (dens.get i)) B hsd hden hB a er
  have f : Frame s.val t.val := by
    refine ⟨f2.memory.trans f1.memory,f2.inputHead.trans f1.inputHead,
      f2.randomCursor.trans f1.randomCursor,?_⟩
    intro j hj
    have hje : j ∉ Emit.work := fun hh => hj (Finset.mem_union_left _ hh)
    have hj10 : 10 ≤ j := by
      have hh : j ∉ Finset.range 10 := fun hh => hj (Finset.mem_union_right _ hh)
      simpa using hh
    exact (f2.tapes j hje).trans (f1.tapes j (Or.inr hj10) (by
      intro hh
      exact hje ((by decide : ({272,273}:Finset ℕ) ⊆ Emit.work) hh)))
  refine ⟨c1+c2,t,by dsimp [costBound]; omega,e1.seq e2,?_,?_,?_,
    word_of_eq (f.tapes 322 (by decide)) hindex,f⟩
  · rw [hout,f1.output]
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact hblank j hj
    · have hj10 : j < 10 := Finset.mem_range.mp hj
      by_cases hje : j ∈ Emit.work
      · exact hblank j hje
      · exact blank_of_eq (f2.tapes j hje) (har j hj10)
  · exact ⟨BankArray.word_of_eq (f.tapes 300 (by decide)) hd.width,
      BankArray.word_of_eq (f.tapes 301 (by decide)) hd.clock,
      BankArray.word_of_eq (f.tapes 320 (by decide)) hd.numBase,
      BankArray.word_of_eq (f.tapes 321 (by decide)) hd.denBase,
      by simpa only [f.memory] using hd.nums,by simpa only [f.memory] using hd.dens⟩

end Maxwell.Cost.PhysicalMaterial.DenseEmit
