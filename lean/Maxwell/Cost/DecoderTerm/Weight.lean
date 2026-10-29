import Maxwell.Cost.DecoderTerm.Multiply
import Maxwell.Cost.TakeParsed

namespace Maxwell.Cost.DecoderTerm
open Structured
open RationalAccumulator (Word Blank)

def weightCode : Code :=
  .seq (TakeParsed.code 12 33) (.seq (TakeParsed.code 13 34)
    (.seq (multiplyCode 65 33) (.seq (multiplyCode 67 34) (.call (TapeOps.clear 65)))))

def WeightFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 12 → i ≠ 13 → i ≠ 33 → i ≠ 34 → i ≠ 65 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem weight (input : List Bool) (tape : ℕ → Bool) (num den mag scale : ℕ)
    (s : Store) (h12 : s.val.tapes 12 = BitTape.atEnd num.bits)
    (h13 : s.val.tapes 13 = BitTape.atEnd den.bits)
    (h65 : Word s.val 65 mag) (h67 : Word s.val 67 scale)
    (hblank : ∀ i, i < 4 → Blank s.val i) (h33 : Blank s.val 33) (h34 : Blank s.val 34) :
    ∃ cost, ∃ t : Store,
      cost ≤ 2000*(num.bits.length+den.bits.length+mag.bits.length+scale.bits.length+3)^2 ∧
      Executes input tape weightCode cost s t ∧
      Word t.val 33 (mag*num) ∧ Word t.val 34 (scale*den) ∧
      (∀ i, i < 4 → Blank t.val i) ∧ Blank t.val 65 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧ WeightFrame s.val t.val := by
  obtain ⟨no,hno⟩ := h33
  obtain ⟨de,hde⟩ := h34
  obtain ⟨a,ea,ha12,ha33,af⟩ := TakeParsed.steps 12 33 (by omega) input tape num.bits no s h12 hno
  obtain ⟨b,eb,hb13,hb34,bf⟩ := TakeParsed.steps 13 34 (by omega) input tape den.bits de a
    ((af.2.2.2.2.2.1 13 (by omega) (by omega)).trans h13)
    ((af.2.2.2.2.2.1 34 (by omega) (by omega)).trans hde)
  have bkeep (i : ℕ) (h12' : i ≠ 12) (h13' : i ≠ 13) (h33' : i ≠ 33) (h34' : i ≠ 34) :
      b.val.tapes i = s.val.tapes i :=
    (bf.2.2.2.2.2.1 i h13' h34').trans (af.2.2.2.2.2.1 i h12' h33')
  have bblank (i : ℕ) (hi : i < 4) : Blank b.val i :=
    RationalAccumulator.blank_of_eq (bkeep i (by omega) (by omega) (by omega) (by omega)) (hblank i hi)
  obtain ⟨mcost,m,hmcost,em,hm33,hmblank,mf⟩ := multiply 65 33 (by omega) (by omega) (by omega)
    input tape mag num b
    (RationalAccumulator.word_of_eq (bkeep 65 (by omega) (by omega) (by omega) (by omega)) h65)
    ⟨no,(bf.2.2.2.2.2.1 33 (by omega) (by omega)).trans ha33⟩ bblank
  have hm67 : Word m.val 67 scale := RationalAccumulator.word_of_eq
    ((mf.2.2.2.2.2.1 67 (by omega) (by omega)).trans
      (bkeep 67 (by omega) (by omega) (by omega) (by omega))) h67
  have hm34 : Word m.val 34 den :=
    ⟨de,(mf.2.2.2.2.2.1 34 (by omega) (by omega)).trans hb34⟩
  obtain ⟨dcost,d,hdcost,ed,hd34,hdblank,df⟩ := multiply 67 34 (by omega) (by omega) (by omega)
    input tape scale den m hm67 hm34 hmblank
  have hd65 : Word d.val 65 mag := RationalAccumulator.word_of_eq
    ((df.2.2.2.2.2.1 65 (by omega) (by omega)).trans
      ((mf.2.2.2.2.2.1 65 (by omega) (by omega)).trans
        (bkeep 65 (by omega) (by omega) (by omega) (by omega)))) h65
  obtain ⟨mo,hmo⟩ := hd65
  obtain ⟨f,hf,hfp,hf65,ff⟩ := TapeOps.clear_steps 65 input tape mag.bits mo d.val d.property hmo
  let fS := Store.ofState f
  have ef : Executes input tape (.call (TapeOps.clear 65)) (6*mag.bits.length+4) d fS := by
    simpa using Executes.call _ d f _ hf (by rw [hfp]; rfl)
  have fkeep (i : ℕ) (hi : i ≠ 65) : fS.val.tapes i = d.val.tapes i := ff.2.2.2.2.2.1 i hi hi
  have mdkeep (i : ℕ) (hi : 4 ≤ i) (h33' : i ≠ 33) (h34' : i ≠ 34) : d.val.tapes i = b.val.tapes i :=
    (df.2.2.2.2.2.1 i hi h34').trans (mf.2.2.2.2.2.1 i hi h33')
  refine ⟨_,fS,?_,ea.seq (eb.seq (em.seq (ed.seq ef))),?_,?_,?_,⟨mo+mag.bits.length,hf65⟩,?_,?_,?_⟩
  · let B := num.bits.length+den.bits.length+mag.bits.length+scale.bits.length+3
    have hmcap : mcost ≤ 600*B^2 := hmcost.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [B]; omega) _))
    have hdcap : dcost ≤ 600*B^2 := hdcost.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [B]; omega) _))
    have hB : B ≤ B^2 := by dsimp [B]; nlinarith
    change _ ≤ 2000*B^2
    dsimp [B] at hB hmcap hdcap ⊢
    nlinarith
  · exact RationalAccumulator.word_of_eq ((fkeep 33 (by omega)).trans
      (df.2.2.2.2.2.1 33 (by omega) (by omega))) hm33
  · exact RationalAccumulator.word_of_eq (fkeep 34 (by omega)) hd34
  · intro i hi; exact RationalAccumulator.blank_of_eq (fkeep i (by omega)) (hdblank i hi)
  · exact (fkeep 12 (by omega)).trans ((mdkeep 12 (by omega) (by omega) (by omega)).trans
      ((bf.2.2.2.2.2.1 12 (by omega) (by omega)).trans ha12))
  · exact (fkeep 13 (by omega)).trans ((mdkeep 13 (by omega) (by omega) (by omega)).trans hb13)
  · rcases af with ⟨aa,ai,am,ar,ao,ats,ag⟩
    rcases bf with ⟨ba,bi,bm,br,bo,bt,bg⟩
    rcases mf with ⟨ma,mi,mm,mr,mo',mt,mg⟩
    rcases df with ⟨da,di,dm,dr,do',dt,dg⟩
    rcases ff with ⟨fa,fi,fm,fr,fo,ft,fg⟩
    exact ⟨fa.trans (da.trans (ma.trans (ba.trans aa))),fi.trans (di.trans (mi.trans (bi.trans ai))),
      fm.trans (dm.trans (mm.trans (bm.trans am))),fr.trans (dr.trans (mr.trans (br.trans ar))),
      fo.trans (do'.trans (mo'.trans (bo.trans ao))),
      fun i hi h12' h13' h33' h34' h65' => (ft i h65' h65').trans
        ((dt i hi h34').trans ((mt i hi h33').trans ((bt i h13' h34').trans (ats i h12' h33')))),
      fun i hi h24 h25 h26 h27 => (fg i h26 h27).trans ((dg i hi h24 h25 h26 h27).trans
        ((mg i hi h24 h25 h26 h27).trans ((bg i h24 h25 h26 h27).trans (ag i h24 h25 h26 h27))))⟩

end Maxwell.Cost.DecoderTerm
