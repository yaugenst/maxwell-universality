import Maxwell.Continuum.CalibrationSeedDenominatorData
import Maxwell.Cost.BankArray.Unique

/-! Compute the seed normalization denominator from the executed sqrt19
pair, including actual signed subtraction, GCD reduction and the second root. -/
namespace Maxwell.Continuum.Calibration.SeedMachine
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def denominatorCode : Code := .seq (NatAssign.code denominatorPrepare)
  (.seq (WordDifference.code 708 709 711)
    (.seq (NatAssign.code denominatorLoad) RationalRoot.Raw.code))
def denominatorPrepareWidth (B : ℕ) : ℕ := 2^denominatorPrepare.length*(B+10)
def denominatorRootWidth (B : ℕ) : ℕ := 2^denominatorLoad.length*(denominatorPrepareWidth B+1)
def denominatorWidth (N B : ℕ) : ℕ := RationalRoot.outputWidth (N+7) (denominatorRootWidth B)
def denominatorCost (N B : ℕ) : ℕ := 3000*8^denominatorPrepare.length*(B+11)^2+
  (300*(2*denominatorPrepareWidth B+4)+
    (3000*8^denominatorLoad.length*(denominatorPrepareWidth B+2)^2+
      RationalRoot.Raw.costBound (N+7) (denominatorRootWidth B)))

theorem denominator_executes (N : ℕ) (v : ℕ→ℕ) (B : ℕ)
    (width : ∀i∈ids,(v i).bits.length≤B) (precision : v 544=N+7)
    (positive : 0<v 548) (radical : (v 32:ℚ)/v 548=seedRadical N)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t num den,Executes input tape denominatorCode cost s t ∧
      cost≤denominatorCost N B ∧
      NatAssign.Bank componentIds (denominatorValues v num den) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈componentIds,(denominatorValues v num den i).bits.length≤denominatorWidth N B) ∧
      0<num ∧ 0<den ∧ (num:ℚ)/den=seedDenominator N ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have literals : ∀a∈denominatorPrepare,a.literalWidth≤B+9 := by
    simp [denominatorPrepare,NatAssign.Instruction.literalWidth,
      show (8:ℕ).bits.length=4 by decide,show (361:ℕ).bits.length=9 by decide,
      show (28:ℕ).bits.length=5 by decide,show (225:ℕ).bits.length=8 by decide]
  obtain ⟨c0,a,e0,h0,ba,sa,f0⟩ := NatAssign.executes ids ids_ge denominatorPrepare denominatorPrepare_valid
    v input tape s bank scratch
  change NatAssign.Bank ids (denominatorPrepared v) a.val at ba
  have wa : ∀i∈ids,(denominatorPrepared v i).bits.length≤denominatorPrepareWidth B := by
    intro i hi
    have h := NatAssign.values_width ids denominatorPrepare denominatorPrepare_valid v (B+9)
      (fun i hi=>(width i hi).trans (by omega)) literals i hi
    exact (Nat.le_add_right _ 1).trans h
  obtain ⟨hp,hm,hd,hz,_,_,_⟩ := denominatorPrepared_fields v
  obtain ⟨c1,b,e1,h1,bb,sb,wb,f1⟩ := NatAssign.difference_executes ids 708 709 711
    (denominatorPrepareWidth B) ids_ge (by decide) (by decide) (by decide) (denominatorPrepared v)
    (by rw [hp,hm];exact denominator_order N _ _ positive radical) hz wa input tape a ba sa
  have diff : Function.update (denominatorPrepared v) 711
      (denominatorPrepared v 708-denominatorPrepared v 709)=denominatorDifference v := by rw [hp,hm];rfl
  rw [diff] at bb wb
  obtain ⟨c2,c,e2,h2,bc,sc,f2⟩ := NatAssign.executes ids ids_ge denominatorLoad denominatorLoad_valid
    (denominatorDifference v) input tape b bb sb
  change NatAssign.Bank ids (denominatorLoaded v) c.val at bc
  have clearLiterals : ∀a∈denominatorLoad,a.literalWidth≤denominatorPrepareWidth B := by
    intro a ha
    have hz : ∀a∈denominatorLoad,a.literalWidth=0 := by decide+kernel
    rw [hz a ha];omega
  have wc : ∀i∈ids,(denominatorLoaded v i).bits.length≤denominatorRootWidth B := by
    intro i hi
    have h := NatAssign.values_width ids denominatorLoad denominatorLoad_valid (denominatorDifference v)
      (denominatorPrepareWidth B) wb clearLiterals i hi
    exact (Nat.le_add_right _ 1).trans h
  let A := denominatorNumerator (v 32) (v 548)
  let D := denominatorBase (v 548)
  have bankRoot : NatAssign.Bank RationalRoot.Raw.ids (RationalRoot.Raw.inputValues A D (N+7)) c.val := by
    intro i hi
    simpa only [denominatorLoaded_root v i hi,precision] using bc i (Finset.mem_union_left _ hi)
  have widthRoot (i : ℕ) (hi : i∈RationalRoot.Raw.ids) :
      (RationalRoot.Raw.inputValues A D (N+7) i).bits.length≤denominatorRootWidth B := by
    simpa only [denominatorLoaded_root v i hi,precision] using wc i (Finset.mem_union_left _ hi)
  have aw : A.bits.length≤denominatorRootWidth B := by
    simpa [RationalRoot.Raw.inputValues,RationalCanonicalBank.inputValues] using widthRoot 228 (by decide)
  have dw : D.bits.length≤denominatorRootWidth B := by
    simpa [RationalRoot.Raw.inputValues,RationalCanonicalBank.inputValues] using widthRoot 229 (by decide)
  have nw : (N+7).bits.length≤denominatorRootWidth B := by
    simpa [RationalRoot.Raw.inputValues] using widthRoot 544 (by decide)
  have dpos : 0<D := by dsimp [D,denominatorBase];positivity
  obtain ⟨c3,t,num,den,e3,h3,wn,wd,dpositive,value,dwidth,root,st,f3,_⟩ :=
    RationalRoot.Raw.executes A D (N+7) (denominatorRootWidth B) dpos aw dw nw input tape c bankRoot sc
  have semantic : (num:ℚ)/den=seedDenominator N := by
    rw [value,show (A:ℚ)/D=seedDenominatorSq N from denominator_value N _ _ positive radical]
    rfl
  have npositive : 0<num := by
    have lower : (1:ℚ)≤(num:ℚ)/den := by rw [semantic];exact_mod_cast seedDenominator_lower N
    by_contra hn
    have zero : num=0 := by omega
    norm_num [zero] at lower
  have resultBank : NatAssign.Bank componentIds (denominatorValues v num den) t.val := by
    intro i hi
    by_cases hden : i=548
    · subst i;simpa only [denominatorValues,Function.update_self] using wd
    · by_cases hnum : i=32
      · subst i;simpa only [denominatorValues,Function.update_of_ne (by decide : 32≠548),Function.update_self] using wn
      · have saved : i∈savedIds := by simpa [componentIds,hden,hnum] using hi
        have outside : i∉RationalRoot.Raw.changed := by
          have bound : ∀j∈RationalRoot.Raw.changed,j<600 := by decide+kernel
          intro member
          have :=bound i member
          have :=(Finset.mem_Icc.mp saved).1
          omega
        simpa only [denominatorValues,Function.update_of_ne hden,Function.update_of_ne hnum] using
          RationalAccumulator.word_of_eq (f3.tapes i outside) (bc i (componentIds_subset hi))
  have numWidth : num.bits.length≤denominatorWidth N B := by
    have smaller (x y : ℕ) : (x/y).bits.length≤x.bits.length := by
      rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
      exact Nat.size_le_size (Nat.div_le_self x y)
    have rwid := RationalRoot.radicand_bits (A/Nat.gcd A D) (D/Nat.gcd A D) (N+7)
      (denominatorRootWidth B) ((smaller _ _).trans aw) ((smaller _ _).trans dw)
    have actual := BankArray.word_unique wn (root 32 (by decide))
    rw [actual]
    have h := NaturalRoot.done_width (RationalRoot.radicand (A/Nat.gcd A D) (D/Nat.gcd A D) (N+7)) 32
    unfold denominatorWidth RationalRoot.outputWidth
    omega
  have resultWidth : ∀i∈componentIds,(denominatorValues v num den i).bits.length≤denominatorWidth N B := by
    intro i hi
    by_cases hden : i=548
    · subst i;simp only [denominatorValues,Function.update_self]
      unfold denominatorWidth RationalRoot.outputWidth;omega
    · by_cases hnum : i=32
      · subst i;simpa only [denominatorValues,Function.update_of_ne hden,Function.update_self] using numWidth
      · simp only [denominatorValues,Function.update_of_ne hden,Function.update_of_ne hnum]
        have := wc i (componentIds_subset hi)
        unfold denominatorWidth RationalRoot.outputWidth;omega
  have p0 := NatAssign.price_bound ids denominatorPrepare denominatorPrepare_valid v (B+9)
    (fun i hi=>(width i hi).trans (by omega)) literals
  have p2 := NatAssign.price_bound ids denominatorLoad denominatorLoad_valid (denominatorDifference v)
    (denominatorPrepareWidth B) wb clearLiterals
  refine ⟨c0+(c1+(c2+c3)),t,num,den,e0.seq (e1.seq (e2.seq e3)),
    Nat.add_le_add (h0.trans p0) (Nat.add_le_add h1 (Nat.add_le_add (h2.trans p2) h3)),
    resultBank,st,resultWidth,npositive,dpositive,semantic,?_⟩
  exact (f0.mono (NatAssign.changes_subset ids denominatorPrepare denominatorPrepare_valid)).trans
    ((f1.mono (by decide+kernel)).trans
      ((f2.mono (NatAssign.changes_subset ids denominatorLoad denominatorLoad_valid)).trans
        (f3.mono (by decide+kernel))))

#print axioms denominator_executes
end Maxwell.Continuum.Calibration.SeedMachine
