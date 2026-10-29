import Maxwell.Cost.DecoderConstants.Helpers
import Maxwell.Cost.RationalAccumulator.Move

namespace Maxwell.Cost.DecoderConstants
open Structured
open RationalAccumulator (Word Blank)

/-- One-time setup from parsed format fields. Every constant is written by
finite bit operations, including zero integer or fractional widths. -/
def code : Code := .seq (.call (WordTransfer.clone 42 65))
  (.seq (addCode 41 65) (.seq (powerCode 65 66) (.seq (powerCode 42 67)
    (.seq (.call (oneProgram 64)) (.seq (addCode 65 64) (.call (TapeOps.clear 65)))))))

def costBound (I F : ℕ) : ℕ := 2000*(I+F+I.bits.length+F.bits.length+5)^2

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → (i < 64 ∨ 68 < i) → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha,hi,hm,hr,ho,ht,hg⟩
  rcases k with ⟨ka,ki,km,kr,ko,kt,kg⟩
  exact ⟨ka.trans ha,ki.trans hi,km.trans hm,kr.trans hr,ko.trans ho,
    fun i hi hb => (kt i hi hb).trans (ht i hi hb),
    fun i hi h24 h25 h26 h27 h28 h29 =>
      (kg i hi h24 h25 h26 h27 h28 h29).trans (hg i hi h24 h25 h26 h27 h28 h29)⟩

theorem Frame.of_stored {target : ℕ} {s t : BitRAMState} (hlo : 64 ≤ target) (hhi : target ≤ 68)
    (h : StoredProduct.Frame target s t) : Frame s t := by
  rcases h with ⟨a,b,c,d,e,f,g⟩
  exact ⟨a,b,c,d,e,fun i hi hb => f i hi (by omega),fun i hi h24 h25 h26 h27 _ _ => g i hi h24 h25 h26 h27⟩

theorem Frame.of_power {target : ℕ} {s t : Store} (hlo : 64 ≤ target) (hhi : target ≤ 68)
    (h : PowerOfTwo.BankFrame 68 target s t) : Frame s.val t.val := by
  rcases h with ⟨a,b,c,d,e,f,g⟩
  exact ⟨a,b,c,d,e,fun i _ hb => f i (by omega) (by omega),
    fun i hi => g i (by omega)⟩

theorem executes (input : List Bool) (randomTape : ℕ → Bool) (I F : ℕ) (s : Store)
    (h41 : Word s.val 41 I) (h42 : Word s.val 42 F)
    (hblank : ∀ i, i < 4 ∨ (64 ≤ i ∧ i ≤ 68) → Blank s.val i) :
    ∃ cost, ∃ t : Store, cost ≤ costBound I F ∧ Executes input randomTape code cost s t ∧
      Word t.val 64 (I+F+1) ∧ Word t.val 66 (2^(I+F)) ∧ Word t.val 67 (2^F) ∧
      (∀ i, i < 4 → Blank t.val i) ∧ Blank t.val 65 ∧ Blank t.val 68 ∧ Frame s.val t.val := by
  obtain ⟨a,ea,ha65,af,ascratch⟩ := cloneStored 42 65 (by omega) (by omega) (by omega) input randomTape F s h42
    (hblank 65 (by omega))
  have ablank (i : ℕ) (hi : i < 4) : Blank a.val i :=
    RationalAccumulator.blank_of_eq (ascratch i hi) (hblank i (Or.inl hi))
  obtain ⟨bcost,b,hbcost,eb,hb65,hbblank,bf⟩ := add 41 65 (by omega) (by omega) (by omega)
    input randomTape I F a
      (RationalAccumulator.word_of_eq (af.2.2.2.2.2.1 41 (by omega) (by omega)) h41) ha65 ablank
  have bkeep (i : ℕ) (hi : 4 ≤ i) (h65 : i ≠ 65) : b.val.tapes i = s.val.tapes i :=
    (bf.2.2.2.2.2.1 i hi h65).trans (af.2.2.2.2.2.1 i hi h65)
  obtain ⟨ccost,c,hccost,ec,hc66,hc68,cf⟩ := power 65 66 (by omega) (by omega) (by omega)
    input randomTape (I+F) b hb65
    (RationalAccumulator.blank_of_eq (bkeep 66 (by omega) (by omega)) (hblank 66 (by omega)))
    (RationalAccumulator.blank_of_eq (bkeep 68 (by omega) (by omega)) (hblank 68 (by omega)))
  obtain ⟨dcost,d,hdcost,ed,hd67,hd68,df⟩ := power 42 67 (by omega) (by omega) (by omega)
    input randomTape F c
    (RationalAccumulator.word_of_eq ((cf.2.2.2.2.2.1 42 (by omega) (by omega)).trans
      (bkeep 42 (by omega) (by omega))) h42)
    (RationalAccumulator.blank_of_eq ((cf.2.2.2.2.2.1 67 (by omega) (by omega)).trans
      (bkeep 67 (by omega) (by omega))) (hblank 67 (by omega))) hc68
  have dkeep (i : ℕ) (h66 : i ≠ 66) (h67 : i ≠ 67) (h68 : i ≠ 68) : d.val.tapes i = b.val.tapes i :=
    (df.2.2.2.2.2.1 i h68 h67).trans (cf.2.2.2.2.2.1 i h68 h66)
  have hd64 : Blank d.val 64 := RationalAccumulator.blank_of_eq
    ((dkeep 64 (by omega) (by omega) (by omega)).trans (bkeep 64 (by omega) (by omega)))
    (hblank 64 (by omega))
  have hone := one 64 input randomTape d hd64
  let e := Store.ofState (oneState 64 d.val)
  have ekeep (i : ℕ) (hi : i ≠ 64) : e.val.tapes i = d.val.tapes i := by
    simp [e,Store.ofState,oneState,hi]
  have eblank (i : ℕ) (hi : i < 4) : Blank e.val i :=
    RationalAccumulator.blank_of_eq ((ekeep i (by omega)).trans (dkeep i (by omega) (by omega) (by omega))) (hbblank i hi)
  have he65 : Word e.val 65 (I+F) := RationalAccumulator.word_of_eq
    ((ekeep 65 (by omega)).trans (dkeep 65 (by omega) (by omega) (by omega))) hb65
  obtain ⟨fcost,f,hfcost,ef,hf64,hfblank,ff⟩ := add 65 64 (by omega) (by omega) (by omega)
    input randomTape (I+F) 1 e he65 hone.2.1 eblank
  have hf65 : Word f.val 65 (I+F) := RationalAccumulator.word_of_eq
    (ff.2.2.2.2.2.1 65 (by omega) (by omega)) he65
  obtain ⟨t,et,ht65,tf,tscratch⟩ := clearStored 65 (by omega) input randomTape (I+F) f hf65
  have tkeep (i : ℕ) (hi : 4 ≤ i) (h64 : i ≠ 64) (h65 : i ≠ 65) : t.val.tapes i = d.val.tapes i :=
    (tf.2.2.2.2.2.1 i hi h65).trans ((ff.2.2.2.2.2.1 i hi h64).trans (ekeep i h64))
  refine ⟨_,t,?_,ea.seq (eb.seq (ec.seq (ed.seq (hone.1.seq (ef.seq et))))),?_,?_,?_,?_,ht65,?_,?_⟩
  · have hsum := RationalAccumulator.bits_add_le I F
    let B := I+F+I.bits.length+F.bits.length+5
    have hB : 5 ≤ B := by dsimp [B]; omega
    have hc' : ccost ≤ 100*B^2 := by
      have h1 : I+F+1 ≤ B := by dsimp [B]; omega
      have h2 : (I+F).bits.length ≤ B := by dsimp [B]; omega
      have hh : ccost ≤ B*(13*B+25)+21*B+27 := hccost.trans (by gcongr)
      nlinarith
    have hd' : dcost ≤ 100*B^2 := by
      have h1 : F+1 ≤ B := by dsimp [B]; omega
      have h2 : F.bits.length ≤ B := by dsimp [B]; omega
      have hh : dcost ≤ B*(13*B+25)+21*B+27 := hdcost.trans (by gcongr)
      nlinarith
    change _ ≤ 2000*B^2
    have hb' : bcost ≤ 200*B := hbcost.trans (by dsimp [B]; omega)
    have honeLen : (1 : ℕ).bits.length = 1 := rfl
    rw [honeLen] at hfcost
    have hf' : fcost ≤ 200*(B+5) := hfcost.trans (by dsimp [B]; omega)
    have hsum' : (I+F).bits.length ≤ B := by dsimp [B]; omega
    have hF : F.bits.length ≤ B := by dsimp [B]; omega
    nlinarith
  · exact RationalAccumulator.word_of_eq (tf.2.2.2.2.2.1 64 (by omega) (by omega)) hf64
  · exact RationalAccumulator.word_of_eq ((tkeep 66 (by omega) (by omega) (by omega)).trans
      (df.2.2.2.2.2.1 66 (by omega) (by omega))) hc66
  · exact RationalAccumulator.word_of_eq (tkeep 67 (by omega) (by omega) (by omega)) hd67
  · intro i hi
    exact RationalAccumulator.blank_of_eq (tscratch i hi) (hfblank i hi)
  · exact RationalAccumulator.blank_of_eq (tkeep 68 (by omega) (by omega) (by omega)) hd68
  · exact ((((((Frame.of_stored (by omega) (by omega) af).trans
      (Frame.of_stored (by omega) (by omega) bf)).trans (Frame.of_power (by omega) (by omega) cf)).trans
      (Frame.of_power (by omega) (by omega) df)).trans (Frame.of_stored (by omega) (by omega) hone.2.2)).trans
      (Frame.of_stored (by omega) (by omega) ff)).trans (Frame.of_stored (by omega) (by omega) tf)


def program : BitRAM := code.compile

theorem run (input : List Bool) (randomTape : ℕ → Bool) (I F : ℕ) (s : Store)
    (h41 : Word s.val 41 I) (h42 : Word s.val 42 F)
    (hblank : ∀ i, i < 4 ∨ (64 ≤ i ∧ i ≤ 68) → Blank s.val i) :
    ∃ t : Store,
      (runPriced (program.next input randomTape) (costBound I F+1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (program.next input randomTape) (costBound I F+1) s.val).instructions ≤ costBound I F ∧
      Word t.val 64 (I+F+1) ∧ Word t.val 66 (2^(I+F)) ∧ Word t.val 67 (2^F) ∧
      (∀ i, i < 4 → Blank t.val i) ∧ Blank t.val 65 ∧ Blank t.val 68 ∧ Frame s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := executes input randomTape I F s h41 h42 hblank
  have hr := he.compiled_run (costBound I F+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.DecoderConstants
