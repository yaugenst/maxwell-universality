import Maxwell.Cost.DecoderTerm.Transfer
import Maxwell.Cost.RationalAccumulator.Bank
import Maxwell.Cost.SignedDifference.Frame

namespace Maxwell.Cost.DecoderTerm
open Structured
open RationalAccumulator (Word Blank)

def differenceCode : Code := 
  .seq (.call SignedDifference.program)
    (.seq (clearOvershootCode 0) (.seq (clearOvershootCode 1) (takeEndCode 2 65)))

def DifferenceFrame (s t : BitRAMState) : Prop := 
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 3 ≤ i → i ≠ 65 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 23 → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem difference (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool)
    (xo yo : ℤ) (s : Store)
    (h0 : s.val.tapes 0 = BitTape.shifted xs xo) (h1 : s.val.tapes 1 = BitTape.shifted ys yo)
    (h2 : Blank s.val 2) (h65 : Blank s.val 65) :
    ∃ cost, ∃ t : Store,
      cost  ≤  200*(xs.length+ys.length+(addressValue (SignedDifference.magnitude xs ys)).bits.length+3) ∧
      Executes input tape differenceCode cost s t ∧
      Word t.val 65 (addressValue (SignedDifference.magnitude xs ys)) ∧
      (∀ i, i<3 → Blank t.val i) ∧
      t.val.registers 23 = SignedDifference.sign xs ys ∧ DifferenceFrame s.val t.val :=  by
  obtain ⟨zo,hzo⟩ :=  h2
  obtain ⟨dest,hdest⟩ :=  h65
  obtain ⟨dcost,d,ro,hdcost,hd,hdpc,hd23,hd2,hd0,hd1⟩ := 
    SignedDifference.simulation_cleanup input tape s.val xs ys xo yo zo s.property h0 h1 hzo
  let dS :=  Store.ofState d
  have ed : Executes input tape (.call SignedDifference.program) (dcost+1) s dS := 
    .call _ s d dcost hd (by rw [hdpc]; rfl)
  have df :=  SignedDifference.execution_frame input tape hd
  let N :=  max (SignedDifference.padded xs).length (SignedDifference.padded ys).length
  obtain ⟨a,ea,ha0,af⟩ :=  clearOvershoot 0 input tape (SignedDifference.padded xs) xo N
    (SignedDifference.padded_pos xs) (le_max_left _ _) dS hd0
  have ha1 : a.val.tapes 1  =  {BitTape.shifted (SignedDifference.padded ys) yo with head :=  yo+N} := 
    (af.2.2.2.2.2.1 1 (by omega) (by omega)).trans hd1
  obtain ⟨b,eb,hb1,bf⟩ :=  clearOvershoot 1 input tape (SignedDifference.padded ys) yo N
    (SignedDifference.padded_pos ys) (le_max_right _ _) a ha1
  have hb2 : b.val.tapes 2 = BitTape.shiftedEnd (addressValue (SignedDifference.magnitude xs ys)).bits ro := 
    (bf.2.2.2.2.2.1 2 (by omega) (by omega)).trans
      ((af.2.2.2.2.2.1 2 (by omega) (by omega)).trans hd2)
  have hb65 : b.val.tapes 65 = {BitTape.blank with head :=  dest} := 
    (bf.2.2.2.2.2.1 65 (by omega) (by omega)).trans
      ((af.2.2.2.2.2.1 65 (by omega) (by omega)).trans
      ((df.2.2.2.2.2.1 65 (by omega)).trans hdest))
  obtain ⟨t,et,ht2,ht65,tf⟩ :=  takeEnd 2 65 (by omega) input tape
    (addressValue (SignedDifference.magnitude xs ys)).bits ro dest b hb2 hb65
  refine ⟨_,t,?_,ed.seq (ea.seq (eb.seq et)),⟨dest,ht65⟩,?_,?_,?_⟩
  · have hx :=  SignedDifference.padded_length xs
    have hy :=  SignedDifference.padded_length ys
    have hn : N  ≤  xs.length+ys.length+1 :=  by dsimp [N]; omega
    omega
  · intro i hi
    interval_cases i
    · exact ⟨xo+(SignedDifference.padded xs).length,
        (tf.2.2.2.2.2.1 0 (by omega) (by omega)).trans
        ((bf.2.2.2.2.2.1 0 (by omega) (by omega)).trans ha0)⟩
    · exact ⟨yo+(SignedDifference.padded ys).length,
        (tf.2.2.2.2.2.1 1 (by omega) (by omega)).trans hb1⟩
    · exact ⟨ro+(addressValue (SignedDifference.magnitude xs ys)).bits.length,ht2⟩
  · exact (tf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)).trans
      ((bf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)).trans
      ((af.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)).trans hd23))
  · rcases df with ⟨da,di,dm,dr,do',dt,dg⟩
    rcases af with ⟨aa,ai,am,ar,ao,ats,ag⟩
    rcases bf with ⟨ba,bi,bm,br,bo,bt,bg⟩
    rcases tf with ⟨ta,ti,tm,tr,to',tt,tg⟩
    exact ⟨ta.trans (ba.trans (aa.trans da)),ti.trans (bi.trans (ai.trans di)),
      tm.trans (bm.trans (am.trans dm)),tr.trans (br.trans (ar.trans dr)),
      to'.trans (bo.trans (ao.trans do')),
      fun i hi h65  => (tt i (by omega) h65).trans
        ((bt i (by omega) (by omega)).trans ((ats i (by omega) (by omega)).trans (dt i hi))),
      fun i hi h23 h24 h25 h26 h27  => (tg i h24 h25 h26 h27).trans
        ((bg i h24 h25 h26 h27).trans ((ag i h24 h25 h26 h27).trans (dg i hi h23 h24 h25 h26 h27)))⟩

end Maxwell.Cost.DecoderTerm
