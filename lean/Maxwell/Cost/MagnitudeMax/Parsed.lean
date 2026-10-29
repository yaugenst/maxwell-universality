import Maxwell.Cost.MagnitudeMax.Update
import Maxwell.Cost.MagnitudeMax.CloneParsed
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.MagnitudeMax

open Structured RationalAccumulator

def loaded (v : ℕ → ℕ) (q : ℚ) : ℕ → ℕ :=
  Function.update (Function.update v 32 q.num.natAbs) 33 q.den

def after (v : ℕ → ℕ) (q : ℚ) : ℕ → ℕ := updated (loaded v q)

def parsedCode : Code :=
  .seq (Code.atom (.bitAnd 60 23 23))
    (.seq (cloneParsedCode 12 32)
      (.seq (cloneParsedCode 13 33)
        (.seq updateCode (Code.atom (.bitAnd 23 60 60)))))

/-- Original parsed fields and the caller's tapes are retained. Register 60
is a literal Boolean sign save; no rational is stored in a finite register. -/
def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 23 → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 35 → i ≠ 60 →
    t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h4 hb => (kt i h4 hb).trans (ht i h4 hb),
    fun i h15 h23 h24 h25 h26 h27 h35 h60 =>
      (kg i h15 h23 h24 h25 h26 h27 h35 h60).trans (hg i h15 h23 h24 h25 h26 h27 h35 h60)⟩

theorem frame_compare {s t : BitRAMState} (h : RationalCompare.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    fun i h15 h23 h24 h25 h26 h27 h35 _ => h.2.2.2.2.2.2 i h15 h23 h24 h25 h26 h27 h35⟩

theorem frame_register (s : BitRAMState) (register : ℕ) (h : register = 23 ∨ register = 60)
    (value : Bool) : Frame s (s.setRegister register value) := by
  rcases h with rfl | rfl <;> simp [Frame, BitRAMState.setRegister]
  all_goals intros; simp_all

/-- Update the maximum from one already parsed rational, keeping all exact
source words and restoring the original sign for subsequent record logging. -/
theorem parsed (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (q : ℚ) (B : ℕ)
    (hbits : ∀ i, i = 30 ∨ i = 31 → (v i).bits.length ≤ B)
    (hn : q.num.natAbs.bits.length ≤ B) (hd : q.den.bits.length ≤ B)
    (hA : 0 < v 31) (h32 : v 32 = 0) (h33 : v 33 = 0) (h35 : v 35 = 0) (h36 : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0)
    (hnum : s.val.tapes 12 = BitTape.atEnd q.num.natAbs.bits)
    (hden : s.val.tapes 13 = BitTape.atEnd q.den.bits) :
    ∃ cost, ∃ t : Store, cost ≤ 10000 * (B + 2)^2 ∧
      Executes input tape parsedCode cost s t ∧
      Bank t.val (after v q) ∧ Scratch t.val 0 ∧
      t.val.registers 23 = s.val.registers 23 ∧ Frame s.val t.val := by
  have hs := Executes.bitAnd input tape s 60 23 23
  let a := Store.ofState (s.val.setRegister 60 (s.val.registers 23 && s.val.registers 23))
  obtain ⟨b, hb, hbb, hbr, hbf⟩ := clone_parsed_bank 12 32 (Or.inl rfl) (by decide) (by decide)
    input tape v q.num.natAbs a hbank hready h32 hnum
  let v1 := Function.update v 32 q.num.natAbs
  have hbden : b.val.tapes 13 = BitTape.atEnd q.den.bits :=
    (hbf.2.2.2.2.2.1 13 (by decide) (Or.inl (by decide))).trans hden
  obtain ⟨c, hc, hcb, hcr, hcf⟩ := clone_parsed_bank 13 33 (Or.inr rfl) (by decide) (by decide)
    input tape v1 q.den b hbb hbr (by simpa [v1] using h33) hbden
  have hloadbits : ∀ i, 30 ≤ i → i ≤ 33 → (loaded v q i).bits.length ≤ B := by
    intro i hi hi'
    interval_cases i
    · simpa [loaded] using hbits 30 (Or.inl rfl)
    · simpa [loaded] using hbits 31 (Or.inr rfl)
    · simpa [loaded] using hn
    · simpa [loaded] using hd
  obtain ⟨dCost, d, hdCost, he, hdb, hdr, hdf⟩ := update input tape (loaded v q) B hloadbits
    (by simpa [loaded] using hA) (by simpa [loaded] using q.pos)
    (by simpa [loaded] using h35) (by simpa [loaded] using h36) c hcb hcr
  have hrestore := Executes.bitAnd input tape d 23 60 60
  let t := Store.ofState (d.val.setRegister 23 (d.val.registers 60 && d.val.registers 60))
  have h60 : d.val.registers 60 = s.val.registers 23 := by
    have hu := hdf.2.2.2.2.2.2 60 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    have hv := hcf.2.2.2.2.2.2 60 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hw := hbf.2.2.2.2.2.2 60 (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa [a, Store.ofState, BitRAMState.setRegister] using (hu.trans hv).trans hw
  refine ⟨2 + ((15*q.num.natAbs.bits.length+16) +
      ((15*q.den.bits.length+16) + (dCost+2))), t, by nlinarith,
    hs.seq (hb.seq (hc.seq (he.seq hrestore))), hdb, hdr, ?_, ?_⟩
  · simp [t, Store.ofState, BitRAMState.setRegister, h60]
  · exact ((((frame_register s.val 60 (Or.inr rfl) _).trans
      (frame_compare (RationalCompare.frame_of_bank hbf))).trans
      (frame_compare (RationalCompare.frame_of_bank hcf))).trans (frame_compare hdf)).trans
      (frame_register d.val 23 (Or.inl rfl) _)

end Maxwell.Cost.MagnitudeMax
