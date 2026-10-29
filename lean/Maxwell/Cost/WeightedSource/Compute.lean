import Maxwell.Cost.WeightedSource.Weight
import Maxwell.Cost.WeightedSource.Split
import Maxwell.Cost.ModeRead.Signed
import Maxwell.Cost.NormalizeSource.RhsBounds

namespace Maxwell.Cost.WeightedSource.Compute
open Structured RationalAccumulator CalibrationMatrix
open Maxwell.Defect.DyadicSqrt.Integer
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def layout : ModeRead.Layout := ⟨100,101,128,129,153,104,![30,31,351]⟩
def work : Finset ℕ := {30,31,32,33,34,35,36,40,350,351,410,411}

def cleanup : List NatAssign.Instruction :=
  [.literal 350 0,.literal 351 0,.literal 410 0,.literal 411 0]
def cleanIds : Finset ℕ := {350,351,410,411}

def code (A D : ℕ) : Code := .seq (Weight.code A D)
  (.seq (ModeRead.Signed.code layout) (.seq Round.code
    (.seq Split.code (NatAssign.code cleanup))))

def inputValue {n : ℕ} (d : ModeRead.Data n) (i : Fin n) (A D k : ℕ) : ℚ :=
  Round.value (decide (d.value i 0 < d.value i 1))
    (((d.value i 0 : ℤ)-d.value i 1).natAbs) d.denominator (lowerNum A D k) (2^k)
def numerator {n : ℕ} (d : ModeRead.Data n) (i : Fin n) (A D k p : ℕ) : ℤ :=
  (Logical.Rounding.nearest p (inputValue d i A D k)).numerator

def costBound (A D k p B : ℕ) : ℕ :=
  Weight.costBound A D k+100100000000*(B+k+p+4)^2

structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ j, 10  ≤  j → j  ∉  work → t.tapes j=s.tapes j

def Workspace (s : BitRAMState) : Prop :=
  ModeRead.Ready s ∧ Bank s (fun _ => 0) ∧
  Blank s 37 ∧ Blank s 40 ∧ Blank s 350 ∧ Blank s 351 ∧ Blank s 410 ∧ Blank s 411

private theorem arith_of_ready {s : BitRAMState} (h : ModeRead.Ready s) : Scratch s 0 :=
  ⟨h 0 (by decide),(zero_word_iff_blank _ _).mpr (h 1 (by decide)),h 2 (by decide),h 3 (by decide)⟩

private theorem indexed_ready {s : BitRAMState} {v : ℕ → ℕ}
    (h : ModeRead.Ready s) (hb : Bank s v) : Ready s v :=
  ⟨hb,⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),
    h 5 (by decide),h 6 (by decide),h 8 (by decide),h 9 (by decide)⟩,h 7 (by decide)⟩

private theorem bits_value_length (word : List Bool) : (addressValue word).bits.length  ≤  word.length := by
  obtain ⟨core,n,he,hc⟩ := TapeOps.trailing_zero_decomposition word
  rw [he,TapeOps.addressValue_append_zeros,TapeOps.canonicalBits_bits hc]
  simp

/-- The whole coefficient calculation reads its two actual indexed channels,
executes the fixed-weight square root, multiplies and rounds, and restores
all private tapes before the following pair of indexed writes. -/
theorem executes {n : ℕ} (d : ModeRead.Data n) (i : Fin n) (A D k p B : ℕ)
    (hd : d.Sized B) (hden : 0<d.denominator) (hvalue : |inputValue d i A D k| ≤ 1)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index=i.val) (hil : index.length ≤ B) (s : Store)
    (hs : Workspace s.val) (hst : ModeRead.Stored layout d s.val)
    (hindex : BankArray.Word s.val 104 index) (hk : Word s.val 400 k)
    (hp : Word s.val 412 (2^p)) :
    ∃ cost, ∃ t : Store, cost ≤ costBound A D k p B ∧ Executes input tape (code A D) cost s t ∧
      Ready t.val (dotValues (Split.positive (numerator d i A D k p))
        (Split.negative (numerator d i A D k p))) ∧
      Blank t.val 4 ∧ Blank t.val 37 ∧ Blank t.val 40 ∧
      Blank t.val 350 ∧ Blank t.val 351 ∧ Blank t.val 410 ∧ Blank t.val 411 ∧ Frame s.val t.val := by
  obtain ⟨c1,a,hc1,e1,wa410,wa411,ba,ra,a40,fa⟩ := Weight.executes A D k input tape s
    hs.2.1 (arith_of_ready hs.1) hk hs.2.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2
  have keepa (j : ℕ) (hj : 37 ≤ j) (h40 : j ≠ 40) (h410 : j ≠ 410) (h411 : j ≠ 411) :
      a.val.tapes j=s.val.tapes j := fa.2.2.2.2.2.1 j (Or.inr ⟨hj,h40⟩) h410 h411
  have aready : ModeRead.Ready a.val := by
    intro j hj
    by_cases hsmall : j<4
    · interval_cases j
      · exact ra.1
      · exact (zero_word_iff_blank _ _).mp ra.2.1
      · exact ra.2.2.1
      · exact ra.2.2.2
    · exact blank_of_eq (fa.2.2.2.2.2.1 j (Or.inl ⟨by omega,by omega⟩) (by omega) (by omega)) (hs.1 j hj)
  have astored : ModeRead.Stored layout d a.val := by
    refine ⟨BankArray.word_of_eq (keepa _ (by decide) (by decide) (by decide) (by decide)) hst.width,
      BankArray.word_of_eq (keepa _ (by decide) (by decide) (by decide) (by decide)) hst.clock,?_,
      word_of_eq (keepa _ (by decide) (by decide) (by decide) (by decide)) hst.denominator,?_⟩
    · intro j
      apply BankArray.word_of_eq (keepa _ ?_ ?_ ?_ ?_) (hst.bases j)
      all_goals fin_cases j <;> decide
    · intro j; simpa only [fa.2.2.1] using hst.arrays j
  have valid : layout.Valid := by
    constructor
    · simp [layout,ModeRead.Layout.inputs]
    · refine ⟨?_,?_,?_⟩
      · intro j;fin_cases j <;> decide
      · intro x y h;fin_cases x <;> fin_cases y <;> simp_all [layout]
      · intro j;fin_cases j <;> decide
  obtain ⟨c2,b,hc2,e2,rb,_,bb,wb350,wb351,sgb,fb⟩ := ModeRead.Signed.executes
    layout valid rfl (by simp [layout,ModeRead.Layout.inputs]) (by decide) d i B hd
    input tape index hi hil a aready astored
    (BankArray.word_of_eq (keepa _ (by decide) (by decide) (by decide) (by decide)) hindex) ba
    (blank_of_eq (keepa _ (by decide) (by decide) (by decide) (by decide)) hs.2.2.2.2.1)
    (blank_of_eq (keepa _ (by decide) (by decide) (by decide) (by decide)) hs.2.2.2.2.2.1)
  have keepb (j : ℕ) (hj : 37 ≤ j) (h350 : j ≠ 350) (h351 : j ≠ 351) : b.val.tapes j=a.val.tapes j :=
    fb.tapes j (Or.inr (by omega)) (by simp only [ModeRead.Signed.changed,Finset.mem_insert,Finset.mem_singleton];omega)
  let C := B+k+p+2
  have hbits (j : Fin 2) : (d.value i j).bits.length ≤ B :=
    (bits_value_length _).trans ((hst.arrays j).length i ▸ hd.2.1)
  have hm := IntegerNormSquare.magnitude_bits_length_le (d.value i 0) (d.value i 1)
  have hl := lowerNum_bits_length_le A D k
  have hpowk : (2^k : ℕ).bits.length=k+1 := by simp [PowerOfTwo.power_bits]
  have hpowp : (2^p : ℕ).bits.length=p+1 := by simp [PowerOfTwo.power_bits]
  obtain ⟨c3,c,hc3,e3,oc,bc,rc,fc,_⟩ := Round.executes input tape
    (((d.value i 0 : ℤ)-d.value i 1).natAbs) d.denominator (lowerNum A D k) (2^k) p C
    (decide (d.value i 0<d.value i 1)) hden (by positivity) (by dsimp [C];omega)
    (by have h0:=hbits 0;have h1:=hbits 1;dsimp [IntegerNormSquare.magnitude] at hm;dsimp [C];omega)
    (by have := hd.2.2.2;dsimp [C];omega) (by dsimp [C];omega)
    (by dsimp [C];omega) (by dsimp [C];omega) b bb (arith_of_ready rb) (rb 4 (by decide))
    wb350 wb351
    (word_of_eq (keepb _ (by decide) (by decide) (by decide)) wa410)
    (word_of_eq (keepb _ (by decide) (by decide) (by decide)) wa411)
    (word_of_eq ((keepb _ (by decide) (by decide) (by decide)).trans
      (keepa _ (by decide) (by decide) (by decide) (by decide))) hp) sgb
  have cbaready : BankArray.Scratch c.val := by
    refine ⟨rc.1,(zero_word_iff_blank _ _).mp rc.2.1,rc.2.2.1,rc.2.2.2,?_,?_,?_,?_⟩
    all_goals exact blank_of_eq (fc.tapes _ (by decide)) (rb _ (by decide))
  have cr : Ready c.val (dotValues 0 0) :=
    ⟨by simpa [dotValues] using bc,cbaready,blank_of_eq (fc.tapes 7 (by decide)) (rb 7 (by decide))⟩
  obtain ⟨r,e4,rr,r4,fr⟩ := Split.executes input tape (numerator d i A D k p) c cr oc
  let cv (j : ℕ) : ℕ := if j=350 then ((d.value i 0 : ℤ)-d.value i 1).natAbs else
    if j=351 then d.denominator else if j=410 then lowerNum A D k else if j=411 then 2^k else 0
  have keepc (j : ℕ) (hj : 37 ≤ j) : c.val.tapes j=b.val.tapes j :=
    fc.tapes j (by simp only [Round.changed,Finset.mem_insert,Finset.mem_singleton];omega)
  have keepr (j : ℕ) (hj : 37 ≤ j) : r.val.tapes j=c.val.tapes j :=
    fr.tapes j (by simp only [Split.changed,Finset.mem_insert,Finset.mem_singleton];omega)
  have cb : NatAssign.Bank cleanIds cv r.val := by
    intro j hj
    simp only [cleanIds,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl
    · exact word_of_eq ((keepr _ (by decide)).trans (keepc _ (by decide))) wb350
    · exact word_of_eq ((keepr _ (by decide)).trans (keepc _ (by decide))) wb351
    · exact word_of_eq ((keepr _ (by decide)).trans ((keepc _ (by decide)).trans
        (keepb _ (by decide) (by decide) (by decide)))) wa410
    · exact word_of_eq ((keepr _ (by decide)).trans ((keepc _ (by decide)).trans
        (keepb _ (by decide) (by decide) (by decide)))) wa411
  have cvalid : ∀ op ∈ cleanup, op.Valid cleanIds := by simp [cleanup,cleanIds,NatAssign.Instruction.Valid]
  obtain ⟨c5,t,e5,hc5,bt,st,ft⟩ := NatAssign.executes cleanIds (by
    intro j hj;simp only [cleanIds,Finset.mem_insert,Finset.mem_singleton] at hj;omega)
    cleanup cvalid cv input tape r cb (by
      intro j hj
      interval_cases j
      · exact rr.2.1.1
      · exact rr.2.1.2.1
      · exact rr.2.1.2.2.1
      · exact rr.2.1.2.2.2.1)
  have cleanbits : ∀ j ∈ cleanIds, (cv j).bits.length ≤ C := by
    intro j _
    dsimp [cv]
    split_ifs
    · have h0:=hbits 0;have h1:=hbits 1;dsimp [IntegerNormSquare.magnitude] at hm;dsimp [C];omega
    · have := hd.2.2.2;dsimp [C];omega
    · dsimp [C];omega
    · dsimp [C];omega
    · simp
  have hprice := NatAssign.price_bound cleanIds cleanup cvalid cv C cleanbits
    (by simp [cleanup,NatAssign.Instruction.literalWidth])
  have hcost5 : c5 ≤ 3000*8^4*(C+2)^2 := by simpa [cleanup] using hc5.trans hprice
  have hnum : (numerator d i A D k p).natAbs.bits.length ≤ p+1 :=
    NormalizeSource.nearest_numerator_bits p _ hvalue
  have samefinal (j : ℕ) (hj : 10 ≤ j) (hjwork : j ∉ work) : t.val.tapes j=s.val.tapes j := by
    have hne : j ≠ 30 ∧ j ≠ 31 ∧ j ≠ 32 ∧ j ≠ 33 ∧ j ≠ 34 ∧ j ≠ 35 ∧ j ≠ 36 ∧ j ≠ 40 ∧ j ≠ 350 ∧ j ≠ 351 ∧ j ≠ 410 ∧ j ≠ 411 := by
      simpa [work] using hjwork
    refine (ft.tapes j (by simp [NatAssign.changes,cleanup,NatAssign.Instruction.target];omega)).trans
      ((fr.tapes j (by simp [Split.changed];omega)).trans
        ((fc.tapes j (by simp [Round.changed];omega)).trans
          ((fb.tapes j (Or.inr hj) (by simp [ModeRead.Signed.changed];omega)).trans ?_)))
    exact fa.2.2.2.2.2.1 j (by omega) (by omega) (by omega)
  have clean (j : ℕ) (hj : j ∈ cleanIds) : Blank t.val j := by
    have hh:=bt j hj
    rw [← zero_word_iff_blank]
    simp only [cleanIds,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl <;> simpa [cleanup,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value] using hh
  refine ⟨c1+(c2+(c3+((12*(numerator d i A D k p).natAbs.bits.length+12)+c5))),t,?_,
    e1.seq (e2.seq (e3.seq (e4.seq e5))),?_,blank_of_eq (ft.tapes 4 (by decide)) r4,
    blank_of_eq (samefinal 37 (by decide) (by decide)) hs.2.2.1,
    blank_of_eq ((ft.tapes 40 (by decide)).trans ((keepr 40 (by decide)).trans
      ((keepc 40 (by decide)).trans (keepb 40 (by decide) (by decide) (by decide))))) a40,
    clean 350 (by decide),clean 351 (by decide),clean 410 (by decide),clean 411 (by decide),?_⟩
  · dsimp [costBound,C] at *
    nlinarith
  · refine ⟨fun j hj hj' => word_of_eq (ft.tapes j (by
      interval_cases j <;> decide)) (rr.1 j hj hj'),?_,?_⟩
    · refine ⟨st 0 (by decide),st 1 (by decide),st 2 (by decide),st 3 (by decide),?_,?_,?_,?_⟩
      · exact blank_of_eq (ft.tapes 5 (by decide)) rr.2.1.2.2.2.2.1
      · exact blank_of_eq (ft.tapes 6 (by decide)) rr.2.1.2.2.2.2.2.1
      · exact blank_of_eq (ft.tapes 8 (by decide)) rr.2.1.2.2.2.2.2.2.1
      · exact blank_of_eq (ft.tapes 9 (by decide)) rr.2.1.2.2.2.2.2.2.2
    · exact blank_of_eq (ft.tapes 7 (by decide)) rr.2.2
  · exact ⟨ft.memory.trans (fr.memory.trans (fc.memory.trans (fb.memory.trans fa.2.2.1))),
      ft.inputHead.trans (fr.inputHead.trans (fc.inputHead.trans (fb.inputHead.trans fa.2.1))),
      ft.randomCursor.trans (fr.randomCursor.trans (fc.randomCursor.trans (fb.randomCursor.trans fa.2.2.2.1))),
      ft.output.trans (fr.output.trans (fc.output.trans (fb.output.trans fa.2.2.2.2.1))),samefinal⟩

end Maxwell.Cost.WeightedSource.Compute
