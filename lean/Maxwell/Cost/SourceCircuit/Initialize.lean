import Maxwell.Cost.SourceCircuit.InitializeMetadata
import Maxwell.Cost.SourceCircuit.InitializeRoots

namespace Maxwell.Cost.SourceCircuit.Initialize
open Structured
open RationalAccumulator (Blank Word word_of_eq blank_of_eq)

def code : Code := .seq InitializeMetadata.code (.seq initializeRootsCode
  (.seq (.call (TapeOps.clear 100)) (.call (WordTransfer.clone 79 100))))

def price (n m p : ℕ) : ℕ := 20000*(m.size+p.size+6)^2+
  ((n+1)*(13*n.bits.length+15)+n*initializeRootBodyCost (InitializeMetadata.width m p).bits [])+
  (6*n.bits.length+4)+(15*m.bits.length+17)

structure Retains (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, (i = 4 ∨ 10 ≤ i) → i ∉ InitializeMetadata.work → t.tapes i = s.tapes i

structure Result (n m p : ℕ) (data : RootInitData n) (s : BitRAMState) : Prop where
  scratch : BankArray.Scratch s
  seven : Blank s 7
  temporary : Blank s 37
  widthWord : Word s 90 (InitializeMetadata.width m p)
  zeroBase : Word s 92 0
  indexWord : BankArray.Word s 91 data.index
  indexLength : data.index.length = InitializeMetadata.width m p
  indexValue : addressValue data.index = n
  clock : Word s 93 (2^InitializeMetadata.exponent m p)
  next : BankArray.Word s 95 (FixedWidth.bits (InitializeMetadata.width m p) n.bits)
  counter : Word s 100 m
  array : BitArray.Represents s.memory 0 (InitializeMetadata.width m p) data.roots
  roots : RepresentsRoots (Logical.CopyBank.initial n) data.roots

set_option maxRecDepth 8192 in
/-- All compiler metadata and the actual root-memory array are constructed
from the three canonical words already read by normalization. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (n m p : ℕ) (hn : n ≤ m)
    (s : Store) (hd : Word s.val 19 n) (hm : Word s.val 79 m) (hp : Word s.val 84 p)
    (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (hb : ∀ i ∈ InitializeMetadata.banks, Blank s.val i) :
    ∃ cost t data, Executes input tape code cost s t ∧ cost ≤ price n m p ∧
      Result n m p data t.val ∧ Retains s.val t.val := by
  obtain ⟨mc,a,em,hmc,ha,fa⟩ := InitializeMetadata.executes input tape n m p hn s hd hm hp hs h7 hb
  let width := (InitializeMetadata.width m p).bits
  have hw : addressValue width = InitializeMetadata.width m p := RationalAccumulator.address_bits _
  have hwidth : 0 < width.length := RationalAccumulator.bits_nonempty (InitializeMetadata.width_pos m p)
  have hnfit : n < 2^addressValue width := by
    rw [hw]
    apply Nat.size_le.mp
    have hh := Nat.size_le_size hn
    dsimp [InitializeMetadata.width,InitializeMetadata.exponent]
    omega
  have hinit := rootInit_ready n width [] a ha.scratch ha.widthWord ha.zeroBase
    (by simpa only [hw] using ha.zeroIndex) ha.seven
  obtain ⟨counterOrigin,hcounter⟩ := ha.counter
  obtain ⟨rc,r,finalCounter,hrc,er,hr100,hrlen,fr,data,hr,hrroots⟩ := initializeRoots_executes
    input tape n width [] n.bits counterOrigin hwidth hnfit (RationalAccumulator.address_bits n)
    _ a hinit hcounter
  obtain ⟨b,eb,hbTapes,fb⟩ := WordCall.clear 100 input tape finalCounter counterOrigin r hr100
  have bm : Word b.val 79 m := word_of_eq (by
    rw [hbTapes]
    simp only [Function.update_of_ne (show (79:ℕ) ≠ 100 by decide)]
    exact (fr.tapes 79 (by decide) (by decide)).trans
      (fa.tapes 79 (by decide) (by decide))) hm
  have b100 : Blank b.val 100 := ⟨counterOrigin+finalCounter.length,by simp [hbTapes]⟩
  obtain ⟨t,et,ht100,ft,ftsmall⟩ := DecoderConstants.cloneStored 79 100 (by decide) (by decide)
    (by decide) input tape m b bm b100
  have tr (i : ℕ) (hi : i ≠ 100) : t.val.tapes i = r.val.tapes i := by
    have htb : t.val.tapes i = b.val.tapes i := by
      by_cases hsmall : i < 4
      · exact ftsmall i hsmall
      · exact ft.2.2.2.2.2.1 i (by omega) hi
    exact htb.trans (by simp [hbTapes,hi])
  have tm : t.val.memory = r.val.memory := ft.2.2.1.trans fb.2.2.1
  have ta (i : ℕ) (hi : i = 4 ∨ 10 ≤ i) (h91 : i ≠ 91) (h100 : i ≠ 100) :
      t.val.tapes i = a.val.tapes i := (tr i h100).trans
    (fr.tapes i hi (by simp [rootInitWork,h91,h100]))
  refine ⟨_,t,data,em.seq (er.seq (eb.seq et)),?_,?_,?_⟩
  · dsimp [price]
    rw [hrlen]
    change rc ≤ (n+1)*(13*n.bits.length+15)+n*initializeRootBodyCost (InitializeMetadata.width m p).bits [] at hrc
    omega
  · refine ⟨InitializeMetadata.scratch_transport hr.scratch (fun i hi => tr i (by omega)),
      blank_of_eq (tr 7 (by decide)) hr.seven,
      blank_of_eq (ta 37 (by decide) (by decide) (by decide)) ha.temporary,
      word_of_eq (tr 90 (by decide)) hr.widthWord,
      word_of_eq (tr 92 (by decide)) hr.baseWord,
      BankArray.word_of_eq (tr 91 (by decide)) hr.indexWord,
      by simpa only [hw] using hr.length,by have hh := hr.total; omega,
      word_of_eq (ta 93 (by decide) (by decide) (by decide)) ha.clock,
      BankArray.word_of_eq (ta 95 (by decide) (by decide) (by decide)) ha.next,
      ht100,?_,hrroots⟩
    simpa only [tm,hw,addressValue] using hr.array
  · refine ⟨ft.2.1.trans (fb.2.1.trans (fr.inputHead.trans fa.inputHead)),
      ft.2.2.2.1.trans (fb.2.2.2.1.trans (fr.randomCursor.trans fa.randomCursor)),
      ft.2.2.2.2.1.trans (fb.2.2.2.2.1.trans (fr.output.trans fa.output)),?_⟩
    intro i hi hc
    have h91 : i ≠ 91 := by
      intro he; subst i; exact hc (by decide)
    have h100 : i ≠ 100 := by
      intro he; subst i; exact hc (by decide)
    exact (ta i hi h91 h100).trans (fa.tapes i hi hc)

end Maxwell.Cost.SourceCircuit.Initialize
