import Maxwell.Cost.BankArray.WriteCanonical
import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.SparseEmission.Encoding

namespace Maxwell.Cost.SparseEmission.Initialize
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq (BankArray.packCanonicalCode 19 93)
  (.seq (.call (WordTransfer.move 37 115))
    (.seq (.call (WordTransfer.clone 115 113)) (.call (Rewind.program 97))))
def work : Finset ℕ := {37,97,113,115}

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (width n : ℕ) (bytes clock : List Bool) (clockOrigin : ℤ) (s : Store)
    (hwidth : 0 < width) (hfit : n < 2^width) (hc : clock.length = width)
    (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (hn : BankArray.Word s.val 19 n.bits)
    (hclock : s.val.tapes 93 = BitTape.shifted clock clockOrigin)
    (h113 : s.val.tapes 113 = BitTape.blank) (h115 : s.val.tapes 115 = BitTape.blank)
    (h97 : s.val.tapes 97 = BitTape.atEnd bytes) :
    ∃ cost t, cost ≤ 107*width+4*bytes.length+124 ∧ Executes input randomTape code cost s t ∧
      t.val.tapes 97 = BitTape.shifted bytes 0 ∧
      t.val.tapes 113 = BitTape.shifted (SourceCircuit.fixedWidth width n) 0 ∧
      t.val.tapes 115 = BitTape.shifted (SourceCircuit.fixedWidth width n) 0 ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧
      t.val.memory = s.val.memory ∧ SourceCircuit.Frame work s.val t.val := by
  have hsize : n.bits.length ≤ clock.length := by
    rw [hc,Nat.size_eq_bits_len,Nat.size_le]
    exact hfit
  obtain ⟨pCost,p,pBound,ep,p37,pScratch,p7,pControl,pFrame⟩ := BankArray.pack_canonical 19 93
    (by decide) (by decide) input randomTape n.bits clock (by omega) hsize s hs h7 h37 hn
    ⟨clockOrigin,hclock⟩
  rcases p37 with ⟨po,p37⟩
  have pWord : p.val.tapes 37 = BitTape.shifted (SourceCircuit.fixedWidth width n) po := by
    simpa [SourceCircuit.fixedWidth,hc] using p37
  obtain ⟨aState,eaSteps,aPC,a37,a115,af⟩ := WordTransfer.move_steps 37 115 (by decide)
    input randomTape (SourceCircuit.fixedWidth width n) po 0 p.val p.property pWord
    (by simpa [BitTape.blank] using (pFrame.2.2.2.1 115 (by omega) (by decide)).trans h115)
  let a := Store.ofState aState
  have ea : Executes input randomTape (.call (WordTransfer.move 37 115)) (12*width+11) p a := by
    simpa using Executes.call _ p aState _ eaSteps (by rw [aPC]; rfl)
  obtain ⟨b,eb,bt,bf⟩ := WordCall.clone 115 113 (by decide) input randomTape
    (SourceCircuit.fixedWidth width n) 0 0 a a115
    (by simpa [a,Store.ofState,BitTape.blank] using ((af.2.2.2.2.2.1 113 (by decide) (by decide)).trans
      ((pFrame.2.2.2.1 113 (by omega) (by decide)).trans h113)))
  have b97 : b.val.tapes 97 = BitTape.shiftedEnd bytes 0 := by
    have he : b.val.tapes 97 = s.val.tapes 97 := by
      simpa [bt,a,Store.ofState] using ((af.2.2.2.2.2.1 97 (by decide) (by decide)).trans
        (pFrame.2.2.2.1 97 (by omega) (by decide)))
    simpa [BitTape.shiftedEnd,BitTape.atEnd,BitTape.shifted,BitTape.ofList] using he.trans h97
  obtain ⟨etSteps,t97⟩ := WordTransfer.rewind_shifted 97 0 input randomTape bytes b.val b.property b97
  let t := Store.ofState (Rewind.finishAt 97 0 b.val)
  have et : Executes input randomTape (.call (Rewind.program 97)) (4*bytes.length+6) b t :=
    .call _ _ _ _ etSteps rfl
  have tf : WordTransfer.Frame 97 97 b.val t.val := WordTransfer.frame_rewind 97 97 97 (Or.inl rfl) 0 b.val
  have keep (i : ℕ) (hi : i ∉ work) : t.val.tapes i = p.val.tapes i := by
    have h97i : i ≠ 97 := by simp_all [work]
    have h113i : i ≠ 113 := by simp_all [work]
    have h37i : i ≠ 37 := by simp_all [work]
    have h115i : i ≠ 115 := by simp_all [work]
    rw [tf.2.2.2.2.2.1 i h97i h97i,bt]
    simpa [h113i,a,Store.ofState] using af.2.2.2.2.2.1 i h37i h115i
  have aFrame : SourceCircuit.Frame work p.val a.val := SourceCircuit.frame_transfer af (by
    intro i hi; exact af.2.2.2.2.2.1 i (by simp_all [work]) (by simp_all [work]))
  have bFrame : SourceCircuit.Frame work a.val b.val := SourceCircuit.frame_transfer bf (by
    intro i hi; simp [bt,show i ≠ 113 by simp_all [work]])
  have tFrame : SourceCircuit.Frame work b.val t.val := SourceCircuit.frame_transfer tf (by
    intro i hi; exact tf.2.2.2.2.2.1 i (by simp_all [work]) (by simp_all [work]))
  refine ⟨_,t,?_,ep.seq (ea.seq (eb.seq et)),t97,?_,?_,?_,?_,?_,
    tf.2.2.1.trans (bf.2.2.1.trans (af.2.2.1.trans pControl.2.2.2.1)),
    ((SourceCircuit.frame_except pFrame).mono (by decide)).trans (aFrame.trans (bFrame.trans tFrame))⟩
  · simp only [SourceCircuit.fixedWidth_length] at *
    rw [hc] at pBound
    omega
  · rw [tf.2.2.2.2.2.1 113 (by decide) (by decide),bt]
    simp
  · rw [tf.2.2.2.2.2.1 115 (by decide) (by decide),bt]
    simpa [a,Store.ofState] using a115
  · exact SourceCircuit.scratch_of_tapes pScratch (fun i hi => keep i (by simp [work]; omega))
  · exact RationalAccumulator.blank_of_eq (keep 7 (by decide)) p7
  · refine ⟨po+width,?_⟩
    rw [tf.2.2.2.2.2.1 37 (by decide) (by decide),bt]
    simpa [a,Store.ofState] using a37

end Maxwell.Cost.SparseEmission.Initialize
