import Maxwell.Cost.CalibrationMatrix.Dot
import Maxwell.Cost.CalibrationMatrix.Value
import Maxwell.Cost.RationalAccumulator.EmitCleanup

/-! The final signed scalar pairing and its literal rational serialization. -/
namespace Maxwell.Cost.CalibrationMatrix.Pairing
open Structured RationalAccumulator
open scoped BigOperators
set_option maxHeartbeats 800000

def positive {n : ℕ} (x y : Channels n) : ℕ :=
  ∑ i, (x.positive i*y.positive i+x.negative i*y.negative i)

def negative {n : ℕ} (x y : Channels n) : ℕ :=
  ∑ i, (x.positive i*y.negative i+x.negative i*y.positive i)

theorem signed_value {n : ℕ} (x y : Channels n) :
    (positive x y : ℤ)-negative x y = ∑ i, x.value i*y.value i := by
  simp only [positive, negative, Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Channels.value]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

structure Decodes {n : ℕ} (d : Data n n) (x y : Channels n) : Prop where
  rowPositive : ∀ i, addressValue (d.matrixPositive.get i) = x.positive i
  rowNegative : ∀ i, addressValue (d.matrixNegative.get i) = x.negative i
  vectorPositive : ∀ i, addressValue (d.vectorPositive.get i) = y.positive i
  vectorNegative : ∀ i, addressValue (d.vectorNegative.get i) = y.negative i

theorem decoded_positive {n : ℕ} {d : Data n n} {x y : Channels n}
    (h : Decodes d x y) : (∑ i, d.rowPositive 0 (by omega) i) = positive x y := by
  apply Finset.sum_congr rfl
  intro i _
  have hi : rowIndex 0 (show 0+n ≤ n by omega) i = i := by ext; simp [rowIndex]
  simp only [Data.rowPositive, Data.positiveTerm, hi, h.rowPositive, h.rowNegative,
    h.vectorPositive, h.vectorNegative]

theorem decoded_negative {n : ℕ} {d : Data n n} {x y : Channels n}
    (h : Decodes d x y) : (∑ i, d.rowNegative 0 (by omega) i) = negative x y := by
  apply Finset.sum_congr rfl
  intro i _
  have hi : rowIndex 0 (show 0+n ≤ n by omega) i = i := by ext; simp [rowIndex]
  simp only [Data.rowNegative, Data.negativeTerm, hi, h.rowPositive, h.rowNegative,
    h.vectorPositive, h.vectorNegative]

def output (p n den : ℕ) (hden : 0 < den) : Codec.RationalPair :=
  ⟨(p : ℤ)-n, den, hden⟩

def tailCode (denBank : ℕ) : Code :=
  .seq (.call (WordTransfer.clone denBank 32))
    (.seq emitCleanCode (.call (TapeOps.clear 32)))

def TailFrame (s t : BitRAMState) : Prop :=
  t.memory = s.memory ∧ t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧
    (∀ i, 100 ≤ i → t.tapes i = s.tapes i)

private theorem ready_from_scratch {s t : BitRAMState} {v w : ℕ → ℕ}
    (h : Ready s v) (hb : Bank t w) (hs : Scratch t 0)
    (ht : ∀ i, 4 ≤ i → i < 10 → t.tapes i = s.tapes i) : Ready t w :=
  ⟨hb, ⟨hs.1, (zero_word_iff_blank t 1).mp hs.2.1, hs.2.2.1, hs.2.2.2,
    blank_of_eq (ht 5 (by omega) (by omega)) h.2.1.2.2.2.2.1,
    blank_of_eq (ht 6 (by omega) (by omega)) h.2.1.2.2.2.2.2.1,
    blank_of_eq (ht 8 (by omega) (by omega)) h.2.1.2.2.2.2.2.2.1,
    blank_of_eq (ht 9 (by omega) (by omega)) h.2.1.2.2.2.2.2.2.2⟩,
    blank_of_eq (ht 7 (by omega) (by omega)) h.2.2⟩

theorem tail (denBank : ℕ) (hdenBank : 120 ≤ denBank)
    (input : List Bool) (tape : ℕ → Bool) (p n den : ℕ) (hden : 0 < den)
    (s : Store) (hready : Ready s.val (dotValues p n))
    (hword : Word s.val denBank den) :
    ∃ cost, ∃ t : Store,
      cost ≤ 500*(p.bits.length+n.bits.length+den.bits.length+4) ∧
      Executes input tape (tailCode denBank) cost s t ∧
      t.val.output = (output p n den hden).encode.reverse ++ s.val.output ∧
      Ready t.val (dotValues p n) ∧ TailFrame s.val t.val := by
  obtain ⟨so, hso⟩ := hword
  have h32 := hready.1 32 (by omega) (by omega)
  simp only [dotValues, Function.update_apply] at h32
  obtain ⟨dest, hdest⟩ := (zero_word_iff_blank s.val 32).mp h32
  obtain ⟨a, hea, hat, haf⟩ := WordCall.clone denBank 32 (by omega) input tape den.bits
    so dest s hso hdest
  let v := Function.update (dotValues p n) 32 den
  have hba : Bank a.val v := by
    intro i hi hi'
    by_cases hit : i = 32
    · subst i
      exact ⟨dest, by simp [hat, v]⟩
    · exact word_of_eq (s := s.val) (by simp [hat, hit])
        (by simpa [v, hit] using hready.1 i hi hi')
  have hsa : Scratch a.val 0 := by
    rcases hready.arithmetic with ⟨h0,h1,h2,h3⟩
    exact ⟨blank_of_eq (by simp [hat]) h0, word_of_eq (by simp [hat]) h1,
      blank_of_eq (by simp [hat]) h2, blank_of_eq (by simp [hat]) h3⟩
  have hvden : 0 < v 32 := by simpa [v] using hden
  obtain ⟨ecost, b, hecost, heb, hbo, hbb, hbs, hbf⟩ :=
    emit_clean_bank input tape v hvden a hba hsa
  have h32b : Word b.val 32 den := by simpa [v] using hbb 32 (by omega) (by omega)
  obtain ⟨origin, horigin⟩ := h32b
  obtain ⟨t, het, htt, htf⟩ := WordCall.clear 32 input tape den.bits origin b horigin
  have hbt : Bank t.val (dotValues p n) := by
    intro i hi hi'
    by_cases hit : i = 32
    · subst i
      apply (zero_word_iff_blank t.val 32).mpr
      exact ⟨origin+den.bits.length, by simp [htt]⟩
    · exact word_of_eq (s := b.val) (by simp [htt, hit])
        (by simpa [v, hit] using hbb i hi hi')
  have hst : Scratch t.val 0 :=
    ⟨blank_of_eq (by simp [htt]) hbs.1, word_of_eq (by simp [htt]) hbs.2.1,
      blank_of_eq (by simp [htt]) hbs.2.2.1, blank_of_eq (by simp [htt]) hbs.2.2.2⟩
  have hkeep (i : ℕ) (hi : 4 ≤ i) (hne : i ≠ 32) : t.val.tapes i = s.val.tapes i := by
    rw [htt, Function.update_of_ne hne, hbf.2.2.2.2.1 i hi, hat, Function.update_of_ne hne]
  refine ⟨(15*den.bits.length+17)+(ecost+(6*den.bits.length+4)),t,?_,
    hea.seq (heb.seq het),?_,ready_from_scratch hready hbt hst
      (fun i hi hi' => hkeep i hi (by omega)),?_⟩
  · have hecost' : ecost ≤ 400*(p.bits.length+n.bits.length+den.bits.length+4) := by
      simpa [v, dotValues] using hecost
    omega
  · have hvout : emitPair v hvden = output p n den hden := by
      simp [emitPair, output, v, dotValues]
    rw [htf.2.2.2.2.1, hbo, hvout, haf.2.2.2.2.1]
  · exact ⟨htf.2.2.1.trans (hbf.2.2.1.trans haf.2.2.1),
      htf.2.1.trans (hbf.2.1.trans haf.2.1),
      htf.2.2.2.1.trans (hbf.2.2.2.1.trans haf.2.2.2.1),
      fun i hi => hkeep i (by omega) (by omega)⟩

theorem output_value {n : ℕ} (x y : Channels n) (den : ℕ) (hden : 0 < den) :
    (output (positive x y) (negative x y) den hden).value =
      (∑ i, (x.value i : ℚ)*(y.value i : ℚ))/(den : ℚ) := by
  change (((positive x y : ℤ)-negative x y : ℤ) : ℚ)/(den : ℚ) = _
  rw [signed_value]
  simp only [Int.cast_sum, Int.cast_mul]

def code (denBank : ℕ) : Code := .seq dotCode (tailCode denBank)

def costCap (n B : ℕ) : ℕ := dotCost n B B + 500*(3*B+4)

theorem costCap_le (n B : ℕ) : costCap n B ≤ 520000*(n+1)*(B+2)^2 := by
  have hbase : 13*B+15 ≤ 20*(B+2)^2 := by nlinarith
  have hrest : 6*B+4+500*(3*B+4) ≤ 2000*(B+2)^2 := by nlinarith
  calc
    _ ≤ (n+1)*(20*(B+2)^2)+n*(510000*(B+2)^2)+2000*(B+2)^2 := by
      dsimp [costCap,dotCost]
      nlinarith only [Nat.mul_le_mul_left (n+1) hbase,hrest]
    _ ≤ _ := by nlinarith only [Nat.zero_le ((9980*n+517980)*(B+2)^2)]

def Frame (s t : BitRAMState) : Prop :=
  t.memory = s.memory ∧ t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧
    (∀ i, 100 ≤ i → i ≠ 102 → i ≠ 103 → i ≠ 106 → t.tapes i = s.tapes i)

private theorem Stored.of_tail {m n : ℕ} {d : Data m n} {s t : BitRAMState}
    (h : Stored d s) (hf : TailFrame s t) : Stored d t :=
  ⟨BankArray.word_of_eq (hf.2.2.2 100 (by omega)) h.width,
    BankArray.word_of_eq (hf.2.2.2 101 (by omega)) h.clock,
    BankArray.word_of_eq (hf.2.2.2 110 (by omega)) h.matrixPositiveBase,
    BankArray.word_of_eq (hf.2.2.2 111 (by omega)) h.matrixNegativeBase,
    BankArray.word_of_eq (hf.2.2.2 112 (by omega)) h.vectorPositiveBase,
    BankArray.word_of_eq (hf.2.2.2 113 (by omega)) h.vectorNegativeBase,
    by simpa only [hf.1] using h.matrixPositive,
    by simpa only [hf.1] using h.matrixNegative,
    by simpa only [hf.1] using h.vectorPositive,
    by simpa only [hf.1] using h.vectorNegative⟩

theorem executes {n : ℕ} (d : Data n n) (x y : Channels n) (hdecode : Decodes d x y)
    (denBank B den : ℕ) (hdenBank : 120 ≤ denBank) (hden : 0 < den)
    (hsized : d.Sized B) (hn : n < 2^B)
    (hp : (positive x y).bits.length ≤ B) (hneg : (negative x y).bits.length ≤ B)
    (hdenLength : den.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (mi vi countWord : List Bool)
    (hmi : addressValue mi = 0) (hvi : addressValue vi = 0)
    (hml : mi.length ≤ B) (hvl : vi.length ≤ B)
    (hcount : addressValue countWord = n) (hcountLength : countWord.length ≤ B)
    (countOrigin : ℤ) (s : Store)
    (hcountWord : s.val.tapes 106 = BitTape.shifted countWord countOrigin)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d s.val) (hindices : Indices s.val mi vi)
    (hdenWord : Word s.val denBank den) :
    ∃ cost, ∃ t : Store,
      cost ≤ costCap n B ∧ Executes input tape (code denBank) cost s t ∧
      t.val.output = (output (positive x y) (negative x y) den hden).encode.reverse ++ s.val.output ∧
      Ready t.val (dotValues (positive x y) (negative x y)) ∧ Stored d t.val ∧
      Blank t.val 106 ∧ Frame s.val t.val := by
  have hrow : 0+n ≤ n := by omega
  obtain ⟨dcost,a,fm,fv,hdcost,hed,hfm,hfv,hfml,hfvl,hai,had,har,ha106,haf⟩ :=
    dot d 0 B hrow hsized hn (by simpa only [decoded_positive hdecode] using hp)
      (by simpa only [decoded_negative hdecode] using hneg) input tape mi vi countWord
      hmi hvi hml hvl hcount countOrigin s hcountWord hready hdata hindices
  have hda : Word a.val denBank den := word_of_eq
    (haf.2.2.2.2.1 denBank (Or.inr (by omega)) (Or.inr (by omega))
      (by omega) (by omega) (by omega)) hdenWord
  have hra : Ready a.val (dotValues (positive x y) (negative x y)) := by
    simpa only [decoded_positive hdecode, decoded_negative hdecode] using har
  obtain ⟨tcost,t,htcost,het,hto,htr,htf⟩ :=
    tail denBank hdenBank input tape (positive x y) (negative x y) den hden a hra hda
  refine ⟨dcost+tcost,t,?_,hed.seq het,?_,htr,Stored.of_tail had htf,
    blank_of_eq (htf.2.2.2 106 (by omega)) ha106,?_⟩
  · have hdot : dotCost n B countWord.length ≤ dotCost n B B := by
      dsimp [dotCost]
      gcongr
    dsimp [costCap]
    omega
  · rw [hto,haf.2.2.2.1]
  · exact ⟨htf.1.trans haf.1,htf.2.1.trans haf.2.1,htf.2.2.1.trans haf.2.2.1,
      fun i hi h102 h103 h106 => (htf.2.2.2 i hi).trans
        (haf.2.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) h102 h103 h106)⟩

theorem compiled_run {n : ℕ} (d : Data n n) (x y : Channels n) (hdecode : Decodes d x y)
    (denBank B den : ℕ) (hdenBank : 120 ≤ denBank) (hden : 0 < den)
    (hsized : d.Sized B) (hn : n < 2^B)
    (hp : (positive x y).bits.length ≤ B) (hneg : (negative x y).bits.length ≤ B)
    (hdenLength : den.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (mi vi countWord : List Bool)
    (hmi : addressValue mi = 0) (hvi : addressValue vi = 0)
    (hml : mi.length ≤ B) (hvl : vi.length ≤ B)
    (hcount : addressValue countWord = n) (hcountLength : countWord.length ≤ B)
    (countOrigin : ℤ) (s : Store)
    (hcountWord : s.val.tapes 106 = BitTape.shifted countWord countOrigin)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d s.val) (hindices : Indices s.val mi vi)
    (hdenWord : Word s.val denBank den) :
    ∃ t : Store,
      (runPriced ((code denBank).compile.next input tape) (costCap n B+1) s.val).finished =
        some (t.place (code denBank).size) ∧
      (runPriced ((code denBank).compile.next input tape) (costCap n B+1) s.val).instructions ≤
        costCap n B ∧
      t.val.output = (output (positive x y) (negative x y) den hden).encode.reverse ++ s.val.output ∧
      Ready t.val (dotValues (positive x y) (negative x y)) ∧ Stored d t.val ∧
      Blank t.val 106 ∧ Frame s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := executes d x y hdecode denBank B den hdenBank hden hsized hn
    hp hneg hdenLength input tape mi vi countWord hmi hvi hml hvl hcount hcountLength countOrigin
    s hcountWord hready hdata hindices hdenWord
  have hh := he.compiled_run (costCap n B+1) (by omega)
  exact ⟨t,hh.1,hh.2 ▸ hcost,ht⟩

end Maxwell.Cost.CalibrationMatrix.Pairing
