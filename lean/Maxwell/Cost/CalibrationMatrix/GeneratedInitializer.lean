import Maxwell.Cost.CalibrationMatrix.GenerationLoop

namespace Maxwell.Cost.CalibrationMatrix.Generation
open Structured BankArray
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Physically installed scalar descriptors, before the radius residue has
been computed. Dense matrix memory may contain arbitrary bits. -/
structure Configured {R : ℕ} (d : Data R) (index : List Bool) (s : BitRAMState) : Prop where
  radius : Word s 120 R.bits
  width : Word s 100 d.width
  clock : Word s 101 d.clock
  index : Word s 102 index
  positiveBase : Word s 110 d.positiveBase
  negativeBase : Word s 111 d.negativeBase
  radix : Word s 121 d.radix
  dimension : Word s 122 d.dimension
  clock2 : Word s 129 (3 : ℕ).bits
  clock5 : Word s 130 (31 : ℕ).bits
  twenty : Word s 131 (20 : ℕ).bits

structure InitFrame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ work → i ≠ 102 → i ≠ 127 → i ≠ 136 → t.tapes i = s.tapes i

theorem InitFrame.high {s t : BitRAMState} (h : InitFrame s t) (i : ℕ) (hi : 230 ≤ i) :
    t.tapes i = s.tapes i := by
  apply h.tapes i _ (by omega) (by omega) (by omega)
  have hb : ∀ j ∈ work, j < 230 := by decide
  intro hin
  have := hb i hin
  omega

def initCode (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) : Code :=
  .seq (Residue.code 131 120 127) (loopCode material z D)

def initCost (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ) : ℕ :=
  700*(R.bits.length+8)^2+loopCost R material z D B

/-- Actual periodic-phase extraction followed by the complete generated
matrix traversal. No preloaded matrix entries are required. -/
theorem init_executes (input : List Bool) (tape : ℕ → Bool) (R : ℕ)
    (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ) (d : Data R)
    (hfit : d.radix.length+d.dimension.length+((3*cubeWidth R^3)^2).bits.length+1 ≤ addressValue d.width)
    (htable : MaterialTable.outputBits 34 (MaterialEntry.table material z D) ≤ addressValue d.width)
    (hsize : d.Sized B) (hcountlen : ((3*cubeWidth R^3)^2).bits.length ≤ B)
    (index : List Bool) (hindex : addressValue index = 0)
    (hilen : index.length ≤ ((3*cubeWidth R^3)^2).bits.length)
    (origin : ℤ) (s : Store) (hs : Configured d index s.val) (hw : Workspace s.val)
    (h127 : Blank s.val 127)
    (hcounter : s.val.tapes 136 = BitTape.shifted ((3*cubeWidth R^3)^2).bits origin) :
    ∃ cost t finalIndex, cost ≤ initCost R material z D B ∧
      Executes input tape (initCode material z D) cost s t ∧
      addressValue finalIndex = (3*cubeWidth R^3)^2 ∧
      finalIndex.length ≤ ((3*cubeWidth R^3)^2).bits.length ∧
      Stored d finalIndex t.val ∧ Workspace t.val ∧ Blank t.val 136 ∧
      BitArray.Represents t.val.memory (addressValue d.positiveBase) (addressValue d.width)
        (positiveWords R material z D (addressValue d.width)) ∧
      BitArray.Represents t.val.memory (addressValue d.negativeBase) (addressValue d.width)
        (negativeWords R material z D (addressValue d.width)) ∧
      InitFrame s.val t.val ∧
      OutputOutside d.output ((3*cubeWidth R^3)^2) (addressValue d.width) s.val t.val := by
  obtain ⟨a,m,hca,ea,hm127,_,hmblank,hf⟩ := Residue.executes 131 120 127
    (by decide) (by decide) (by decide) input tape R.bits s hs.twenty hs.radius h127
    (fun i hi => hw i (by
      have hh : Finset.range 5 ⊆ work := by decide
      exact hh (by simp; omega)))
  have hms : Stored d index m.val :=
    ⟨hf.word (by decide) hs.width,hf.word (by decide) hs.clock,hf.word (by decide) hs.index,
      hf.word (by decide) hs.positiveBase,hf.word (by decide) hs.negativeBase,
      hf.word (by decide) hs.radix,hf.word (by decide) hs.dimension,
      by simpa only [RationalAccumulator.Word,BankArray.Word,addressValue_bits] using hm127,
      hf.word (by decide) hs.clock2,hf.word (by decide) hs.clock5,hf.word (by decide) hs.twenty⟩
  have hmw : Workspace m.val := by
    intro i hi
    by_cases hl : i < 5
    · exact hmblank i hl
    apply hf.blank _ (hw i hi)
    have h127' : i ≠ 127 := by intro heq; subst i; exact (show 127 ∉ work by decide) hi
    simp [Residue.changes]
    omega
  obtain ⟨b,t,finalIndex,hcb,eb,hval,hlen,hts,htw,ht136,hp,hn,hg,hout⟩ :=
    loop_executes input tape R material z D B d hfit htable hsize hcountlen index hindex hilen
      origin m hms hmw ((hf.tapes 136 (by decide)).trans hcounter)
  refine ⟨a+b,t,finalIndex,by dsimp [initCost]; omega,ea.seq eb,hval,hlen,hts,htw,ht136,hp,hn,
    ⟨hg.inputHead.trans hf.inputHead,hg.randomCursor.trans hf.randomCursor,
      hg.output.trans hf.output,?_⟩,(OutputOutside.of_memory hf.memory).trans hout⟩
  intro i hi h102 h127' h136
  exact (hg.tapes i hi h102 h136).trans (hf.tapes i (by
    have hlow : 5 ≤ i := by
      have hh : Finset.range 5 ⊆ work := by decide
      by_contra h
      exact hi (hh (by simp; omega))
    simp [Residue.changes]
    omega))

end Maxwell.Cost.CalibrationMatrix.Generation
