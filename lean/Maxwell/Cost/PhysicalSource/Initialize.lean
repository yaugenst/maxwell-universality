import Maxwell.Cost.PhysicalSource.Fill
import Maxwell.Cost.BinaryPrecision

/-! Three charged passes initialize the dense signed source overlay from
arbitrary old memory. The positive and negative arrays start at zero; the
shared representation has denominator one at every retained edge. -/
namespace Maxwell.Cost.PhysicalSource.Overlay
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

structure Metadata {n : ℕ} (l : Layout n) (s : BitRAMState) : Prop where
  width : BankArray.Word s 300 l.width
  clock : BankArray.Word s 301 l.clock
  bases : ∀ i, BankArray.Word s (baseTape i) (l.bases i)

def zeroWords {n : ℕ} (l : Layout n) : Fin 3→Vector (List Bool) n :=
  fun port => Vector.replicate n
    (FixedWidth.bits (addressValue l.width) (if port=2 then (1:ℕ) else 0).bits)

theorem zeroWords_value {n : ℕ} (l : Layout n) (i : Fin n) : value (zeroWords l) i=0 := by
  simp [value,zeroWords,Vector.get,FixedWidth.bits_value]

structure InitializeFrame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ j, j=4 ∨ 10≤j → j≠37 → j≠333 → j≠336 → j≠338 → t.tapes j=s.tapes j

def initializeCode : Code := .seq (BinaryPrecision.literalCode 336 1)
  (.seq (fillCode 0) (.seq (fillCode 1) (fillCode 2)))

/-- No array representation or zero-memory premise is needed. Only the
allocated metadata and stored edge count are inputs to this fixed program. -/
theorem initialize_executes {n : ℕ} (l : Layout n) (B : ℕ) (hl : l.Sized B)
    (hn : n.bits.length≤B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready s.val) (h37 : Blank s.val 37) (hm : Metadata l s.val)
    (hcount : Word s.val 337 n) (h333 : Blank s.val 333) (h338 : Blank s.val 338)
    (h334 : Blank s.val 334) (h335 : Blank s.val 335) (h336 : Blank s.val 336) :
    ∃ cost t finalCount, cost≤150005*(n+1)*(B+2)^2 ∧
      Executes input tape initializeCode cost s t ∧ Ready t.val ∧ Blank t.val 37 ∧
      Stored l (zeroWords l) t.val ∧ Word t.val 333 n ∧
      BankArray.Word t.val 338 finalCount ∧ finalCount.length=n.bits.length ∧
      Word t.val 334 0 ∧ Word t.val 335 0 ∧ Word t.val 336 1 ∧
      InitializeFrame s.val t.val ∧ Outside l s.val t.val := by
  let words := fun port => PhysicalMaterial.Dense.snapshot s.val.memory
    (addressValue (l.bases port)) (addressValue l.width) n
  obtain ⟨a,ea,ha336,fa⟩ := BinaryPrecision.literal 336 1 input tape s h336
  have keepa (j : ℕ) (hj : j≠336) : a.val.tapes j=s.val.tapes j :=
    fa.tapes j (by simpa using hj)
  have har : Ready a.val := fun j hj => blank_of_eq (keepa j (by omega)) (hs j hj)
  have had : Stored l words a.val := ⟨BankArray.word_of_eq (keepa 300 (by decide)) hm.width,
    BankArray.word_of_eq (keepa 301 (by decide)) hm.clock,
    fun j => BankArray.word_of_eq (keepa (baseTape j)
      (by have := j.isLt; dsimp [baseTape]; omega)) (hm.bases j),
    fun j => by rw [fa.memory]; exact PhysicalMaterial.Dense.snapshot_represents _ _ _ _⟩
  have haz (j : ℕ) (hj : j≠336) (hz : Blank s.val j) : Word a.val j 0 :=
    (zero_word_iff_blank _ _).mpr (blank_of_eq (keepa j hj) hz)
  obtain ⟨c0,b,f0,hc0,e0,br,b37,bd,bv,bi,bc,bcl,bf,bo⟩ := fill l words 0 0 B hl hn
    (by simp) input tape 0 [] (by simp) (by simp) a har
    (blank_of_eq (keepa 37 (by decide)) h37) had (haz 334 (by decide) h334)
    (word_of_eq (keepa 337 (by decide)) hcount)
    (by change Word a.val 338 0; exact haz 338 (by decide) h338)
    (haz 333 (by decide) h333)
  have keepb (j : ℕ) (hj : j=4 ∨ 10≤j) (h37 : j≠37) (h333 : j≠333) (h338 : j≠338) :=
    bf.tapes j hj h37 h333 h338
  obtain ⟨c1,c,f1,hc1,e1,cr,c37,cd,cv,ci,cc,ccl,cf,co⟩ := fill l _ 1 0 B hl hn
    (by simp) input tape n f0 hn (bcl.trans_le hn) b br b37 bd
    (word_of_eq (keepb 335 (by decide) (by decide) (by decide) (by decide)) (haz 335 (by decide) h335))
    (word_of_eq (keepb 337 (by decide) (by decide) (by decide) (by decide))
      (word_of_eq (keepa 337 (by decide)) hcount)) bc bi
  have ab := bf.trans cf
  have keepc (j : ℕ) (hj : j=4 ∨ 10≤j) (h37 : j≠37) (h333 : j≠333) (h338 : j≠338) :=
    ab.tapes j hj h37 h333 h338
  have hfit : (1:ℕ).bits.length≤addressValue l.width := by
    have := l.width_positive
    norm_num
    omega
  obtain ⟨c2,t,f2,hc2,e2,tr,t37,td,tv,ti,tc,tcl,tf,hto⟩ := fill l _ 2 1 B hl hn
    hfit input tape n f1 hn (ccl.trans_le hn) c cr c37 cd
    (word_of_eq (keepc 336 (by decide) (by decide) (by decide) (by decide)) ha336)
    (word_of_eq (keepc 337 (by decide) (by decide) (by decide) (by decide))
      (word_of_eq (keepa 337 (by decide)) hcount)) cc ci
  have af := ab.trans tf
  have keep (j : ℕ) (hj : j=4 ∨ 10≤j) (h37 : j≠37) (h333 : j≠333)
      (h336 : j≠336) (h338 : j≠338) : t.val.tapes j=s.val.tapes j :=
    (af.tapes j hj h37 h333 h338).trans (keepa j h336)
  refine ⟨17+(c0+(c1+c2)),t,f2,?_,by simpa [initializeCode] using ea.seq (e0.seq (e1.seq e2)),tr,t37,?_,ti,tc,tcl,
    (zero_word_iff_blank _ _).mpr (blank_of_eq (keep 334 (by decide) (by decide)
      (by decide) (by decide) (by decide)) h334),
    (zero_word_iff_blank _ _).mpr (blank_of_eq (keep 335 (by decide) (by decide)
      (by decide) (by decide) (by decide)) h335),tv,
    ⟨af.inputHead.trans fa.inputHead,af.randomCursor.trans fa.randomCursor,
      af.output.trans fa.output,keep⟩,
    (((Outside.of_memory l fa.memory).trans bo).trans co).trans hto⟩
  · have hp : 4≤(n+1)*(B+2)^2 := by nlinarith [Nat.zero_le (n*(B+2)^2)]
    nlinarith only [hc0,hc1,hc2,hp]
  · convert td using 1
    funext port
    fin_cases port <;> simp [zeroWords,Function.update]

end Maxwell.Cost.PhysicalSource.Overlay
