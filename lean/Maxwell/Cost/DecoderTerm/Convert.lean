import Maxwell.Cost.DecoderTerm.Difference

namespace Maxwell.Cost.DecoderTerm
open Structured
open RationalAccumulator (Word Blank)

def convertCode : Code :=
  .seq (takeEndCode 7 0) (.seq (.call (WordTransfer.clone 66 1)) differenceCode)

def ConvertFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 7 → i ≠ 65 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 23 → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem convert (input : List Bool) (tape : ℕ → Bool) (sample : List Bool)
    (center : ℕ) (sampleOrigin : ℤ) (s : Store)
    (h7 : s.val.tapes 7 = BitTape.shiftedEnd sample sampleOrigin)
    (hcenter : Word s.val 66 center) (hblank : ∀ i, i < 4 → Blank s.val i)
    (h65 : Blank s.val 65) :
    ∃ cost, ∃ t : Store,
      cost ≤ 250*(sample.length+center.bits.length+
        (addressValue (SignedDifference.magnitude sample center.bits)).bits.length+3) ∧
      Executes input tape convertCode cost s t ∧
      Word t.val 65 (addressValue (SignedDifference.magnitude sample center.bits)) ∧
      (∀ i, i < 4 → Blank t.val i) ∧ Blank t.val 7 ∧
      t.val.registers 23 = SignedDifference.sign sample center.bits ∧ ConvertFrame s.val t.val := by
  obtain ⟨xo,hx⟩ := hblank 0 (by omega)
  obtain ⟨yo,hy⟩ := hblank 1 (by omega)
  obtain ⟨co,hco⟩ := hcenter
  obtain ⟨a,ea,ha7,ha0,af⟩ := takeEnd 7 0 (by omega) input tape sample sampleOrigin xo s h7 hx
  have ha66 : a.val.tapes 66 = BitTape.shifted center.bits co :=
    (af.2.2.2.2.2.1 66 (by omega) (by omega)).trans hco
  have ha1 : a.val.tapes 1 = {BitTape.blank with head := yo} :=
    (af.2.2.2.2.2.1 1 (by omega) (by omega)).trans hy
  obtain ⟨b,hb,hbp,hb66,hb1,bf⟩ := WordTransfer.clone_steps 66 1 (by omega)
    input tape center.bits co yo a.val a.property ha66 ha1
  let bS := Store.ofState b
  have eb : Executes input tape (.call (WordTransfer.clone 66 1))
      (15*center.bits.length+17) a bS := by
    simpa using Executes.call _ a b _ hb (by rw [hbp]; rfl)
  have bkeep (i : ℕ) (h7 : i ≠ 7) (h0 : i ≠ 0) (h66 : i ≠ 66) (h1 : i ≠ 1) :
      bS.val.tapes i = s.val.tapes i :=
    (bf.2.2.2.2.2.1 i h66 h1).trans (af.2.2.2.2.2.1 i h7 h0)
  obtain ⟨dcost,t,hdcost,ed,ht65,htblank,ht23,df⟩ := difference input tape sample center.bits xo yo bS
    ((bf.2.2.2.2.2.1 0 (by omega) (by omega)).trans ha0) hb1
    (RationalAccumulator.blank_of_eq (bkeep 2 (by omega) (by omega) (by omega) (by omega))
      (hblank 2 (by omega)))
    (RationalAccumulator.blank_of_eq (bkeep 65 (by omega) (by omega) (by omega) (by omega)) h65)
  refine ⟨_,t,by omega,ea.seq (eb.seq ed),ht65,?_,?_,ht23,?_⟩
  · intro i hi
    by_cases h3 : i = 3
    · subst i
      exact RationalAccumulator.blank_of_eq ((df.2.2.2.2.2.1 3 (by omega) (by omega)).trans
        (bkeep 3 (by omega) (by omega) (by omega) (by omega))) (hblank 3 (by omega))
    · exact htblank i (by omega)
  · exact ⟨sampleOrigin+sample.length,(df.2.2.2.2.2.1 7 (by omega) (by omega)).trans
      ((bf.2.2.2.2.2.1 7 (by omega) (by omega)).trans ha7)⟩
  · rcases af with ⟨aa,ai,am,ar,ao,ats,ag⟩
    rcases bf with ⟨ba,bi,bm,br,bo,bt,bg⟩
    rcases df with ⟨da,di,dm,dr,do',dt,dg⟩
    refine ⟨da.trans (ba.trans aa),di.trans (bi.trans ai),dm.trans (bm.trans am),
      dr.trans (br.trans ar),do'.trans (bo.trans ao),?_,?_⟩
    · intro i hi h7' h65'
      apply (dt i (by omega) h65').trans
      by_cases h66 : i = 66
      · subst i; exact hb66.trans hco.symm
      · exact (bt i h66 (by omega)).trans (ats i h7' (by omega))
    · intro i hi h23 h24 h25 h26 h27
      exact (dg i hi h23 h24 h25 h26 h27).trans
        ((bg i h24 h25 h26 h27).trans (ag i h24 h25 h26 h27))

end Maxwell.Cost.DecoderTerm
