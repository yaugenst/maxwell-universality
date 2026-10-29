import Maxwell.Cost.SourceCircuit.InitializeMetadata.Width
import Maxwell.Cost.SourceMetadata

namespace Maxwell.Cost.SourceCircuit.InitializeMetadata
open Structured RationalAccumulator

def clockWork : Finset ℕ := {90,93,107,108,109}
def clockCode : Code := .seq (PowerOfTwo.code 90 109 93)
  (.seq (.call (Rewind.program 93)) (.seq (WordLength.code 93 109)
    (.seq (.call (TapeOps.clear 90)) (.seq (.call (WordTransfer.move 109 90))
      (.seq (.call (TapeOps.clear 107)) (.call (TapeOps.clear 108)))))))

theorem clear (target n : ℕ) (htarget : 4 ≤ target)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hw : Word s.val target n) :
    ∃ t, Executes input tape (.call (TapeOps.clear target)) (6*n.bits.length+4) s t ∧
      Blank t.val target ∧ Frame {target} s.val t.val := by
  obtain ⟨t,he,hb,hf,hsmall⟩ := DecoderConstants.clearStored target htarget input tape n s hw
  refine ⟨t,he,hb,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  intro i hi
  by_cases hs : i < 4
  · exact hsmall i hs
  · exact hf.2.2.2.2.2.1 i (by omega) (by simpa using hi)

theorem clock_executes (input : List Bool) (tape : ℕ → Bool) (m p : ℕ) (s : Store)
    (he : Word s.val 90 (exponent m p)) (hp : Word s.val 107 p.size)
    (hfour : Word s.val 108 4) (hclock : Blank s.val 93) (hcounter : Blank s.val 109) :
    ∃ cost t, Executes input tape clockCode cost s t ∧
      cost ≤ 1000*(exponent m p+2)^2 ∧ Word t.val 90 (width m p) ∧
      Word t.val 93 (2^exponent m p) ∧
      Blank t.val 107 ∧ Blank t.val 108 ∧ Blank t.val 109 ∧
      Frame clockWork s.val t.val := by
  let E := exponent m p
  obtain ⟨eo,heo⟩ := he
  obtain ⟨co,hco⟩ := hcounter
  obtain ⟨wo,hwo⟩ := hclock
  obtain ⟨ac,a,ea,hac,_,ha109,ha93,fa'⟩ := PowerOfTwo.executes 90 109 93
    (by decide) (by decide) (by decide) input tape E.bits eo co wo s heo hco hwo
  simp only [addressValue_bits] at hac ha93
  have fa : Frame {109,93} s.val a.val := by
    refine ⟨fa'.1,fa'.2.1,fa'.2.2.1,fa'.2.2.2.1,fa'.2.2.2.2.1,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    exact fa'.2.2.2.2.2.1 i hi.1 hi.2
  have hr := WordTransfer.rewind_shifted 93 wo input tape (2^E).bits a.val a.property ha93
  let b := Store.ofState (Rewind.finishAt 93 wo a.val)
  have eb : Executes input tape (.call (Rewind.program 93))
      (4*(2^E).bits.length+6) a b := .call _ a _ _ hr.1 rfl
  have fb : Frame {93} a.val b.val := by
    refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
    intro i hi
    have hi93 : i ≠ 93 := by simpa using hi
    simp [b,Store.ofState,Rewind.finishAt,hi93]
  have fab : Frame clockWork s.val b.val :=
    (fa.mono (by decide)).trans (fb.mono (by decide))
  have hb109 : Blank b.val 109 := ⟨co+E.bits.length,
    (fb.tapes 109 (by decide)).trans ha109⟩
  obtain ⟨cc,c,ec,hcc,hc109,fc⟩ := wordLength 93 109 (2^E) (by decide) input tape b ⟨wo,hr.2⟩ hb109
  have hw : (2^E).size = width m p := by rw [Nat.size_pow]; rfl
  rw [hw] at hc109 hcc
  have hc90 : Word c.val 90 E := word_of_eq ((fc.tapes 90 (by decide)).trans
    ((fb.tapes 90 (by decide)).trans (fa.tapes 90 (by decide)))) ⟨eo,heo⟩
  obtain ⟨d,ed,hd90,fd⟩ := clear 90 E (by decide) input tape c hc90
  obtain ⟨f,ef,hf90,hf109,ff⟩ := SourceMetadata.move 109 90 (width m p) (by decide) input tape d
    (word_of_eq (fd.tapes 109 (by decide)) hc109) hd90
  have fac : Frame clockWork s.val c.val := fab.trans (fc.mono (by decide))
  have fad : Frame clockWork s.val d.val := fac.trans (fd.mono (by decide))
  have faf : Frame clockWork s.val f.val := fad.trans (ff.mono (by decide))
  have hf107 : Word f.val 107 p.size := word_of_eq
    ((ff.tapes 107 (by decide)).trans ((fd.tapes 107 (by decide)).trans
      ((fc.tapes 107 (by decide)).trans ((fb.tapes 107 (by decide)).trans
        (fa.tapes 107 (by decide)))))) hp
  obtain ⟨g,eg,hg107,fg⟩ := clear 107 p.size (by decide) input tape f hf107
  have hg108 : Word g.val 108 4 := word_of_eq
    ((fg.tapes 108 (by decide)).trans ((ff.tapes 108 (by decide)).trans
      ((fd.tapes 108 (by decide)).trans ((fc.tapes 108 (by decide)).trans
        ((fb.tapes 108 (by decide)).trans (fa.tapes 108 (by decide))))))) hfour
  obtain ⟨t,et,ht108,ft⟩ := clear 108 4 (by decide) input tape g hg108
  refine ⟨_,t,ea.seq (eb.seq (ec.seq (ed.seq (ef.seq (eg.seq et))))),?_,
    word_of_eq ((ft.tapes 90 (by decide)).trans (fg.tapes 90 (by decide))) hf90,
    ?_,blank_of_eq (ft.tapes 107 (by decide)) hg107,ht108,
    blank_of_eq ((ft.tapes 109 (by decide)).trans (fg.tapes 109 (by decide))) hf109,
    (faf.trans (fg.mono (by decide))).trans (ft.mono (by decide))⟩
  · have hE : E.bits.length ≤ E := by
      simpa only [WordLength.countBits_eq] using WordLength.countBits_length E
    have hW : (width m p).bits.length ≤ width m p := by
      simpa only [WordLength.countBits_eq] using WordLength.countBits_length (width m p)
    have hP : p.size.bits.length ≤ p.size := by
      simpa only [WordLength.countBits_eq] using WordLength.countBits_length p.size
    have hPE : p.size ≤ E := by dsimp [E,exponent]; omega
    have hpow : (2^E).bits.length = E+1 := by rw [Nat.size_eq_bits_len,Nat.size_pow]
    have h4 : (Nat.bits 4).length = 3 := by decide
    rw [hpow,h4]
    change cc ≤ 48*(E+2)^2+1 at hcc
    change (width m p).bits.length ≤ E+1 at hW
    change _ ≤ 1000*(E+2)^2
    nlinarith only [hac,hcc,hE,hW,hP,hPE]
  · refine ⟨wo,?_⟩
    exact ((ft.tapes 93 (by decide)).trans ((fg.tapes 93 (by decide)).trans
      ((ff.tapes 93 (by decide)).trans ((fd.tapes 93 (by decide)).trans
        (fc.tapes 93 (by decide)))))).trans hr.2

end Maxwell.Cost.SourceCircuit.InitializeMetadata
