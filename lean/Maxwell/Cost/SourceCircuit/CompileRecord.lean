import Maxwell.Cost.SourceCircuit.TermStore
import Maxwell.Cost.SourceCircuit.TermCleanup
import Maxwell.Cost.NormalizedRecordParser

namespace Maxwell.Cost.SourceCircuit.CompileRecord
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq NormalizedRecordParser.code (.seq TermStore.code TermCleanup.code)

def work : Finset ℕ := {15,16,83,85,94,95,96,97,98,99,103,104,106}

structure Persistent (s t : Store) : Prop where
  memory : t.val.memory = s.val.memory
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ j, (j = 4 ∨ 10 ≤ j) → j ∉ work → t.val.tapes j = s.val.tapes j

def bound (row column precision width counterWidth : ℕ) : ℕ :=
  40*(row.bits.length+column.bits.length)+precision*(158*width+246)+112*width+12*counterWidth+275

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem executes (input : List Bool) (tape : ℕ → Bool) (width row column : ℕ)
    (clock bits next gates beforeAll leafSuffix preceding suffix counter : List Bool)
    (leaves terms : List (List Bool)) (negative : Bool) (origin powerOrigin : ℤ) (s : Store)
    (hclock : clock.length = width) (hlen : next.length = width)
    (hcount : leaves.length = bits.count true) (hleaves : ∀ word ∈ leaves, word.length = width)
    (hroom : addressValue next + 1 + bits.length + bits.count true + negative.toNat < 2^width)
    (hs : BankArray.Scratch s.val) (h94 : Blank s.val 94) (h96 : Blank s.val 96)
    (h99 : Blank s.val 99) (hn : BankArray.Word s.val 95 next)
    (hg : s.val.tapes 97 = BitTape.atEnd gates) (hc : BankArray.Word s.val 93 clock)
    (hl : s.val.tapes 103 = BitTape.blank)
    (hsource : s.val.tapes 98 = Increment.cursor beforeAll (leaves.flatten ++ leafSuffix) 0)
    (hterms : s.val.tapes 104 = BitTape.atEnd terms.flatten)
    (hcounter : BankArray.Word s.val 106 counter)
    (h10 : s.val.tapes 10 = BitTape.blank) (h15 : s.val.tapes 15 = BitTape.blank)
    (h16 : s.val.tapes 16 = BitTape.blank) (h83 : s.val.tapes 83 = {BitTape.blank with head := origin})
    (h82 : s.val.tapes 82 = BitTape.shifted (2^bits.length).bits powerOrigin)
    (h85 : s.val.tapes 85 = NormalizedRecordParser.cursor
      (preceding ++ (normalizedRecord row column negative bits ++ suffix)) preceding.length) :
    ∃ cost t, cost ≤ bound row column bits.length width counter.length ∧ Executes input tape code cost s t ∧
      TermStore.Done clock (TermStore.result negative bits next gates leaves) terms t ∧
      HornerLoop.Valid width [] (TermStore.result negative bits next gates leaves) ∧
      t.val.tapes 10 = BitTape.blank ∧ t.val.tapes 15 = BitTape.blank ∧ t.val.tapes 16 = BitTape.blank ∧
      t.val.tapes 83 = {BitTape.blank with head := origin+bits.length} ∧
      BankArray.Word t.val 106 (Increment.bits counter) ∧
      t.val.tapes 98 = Increment.cursor (beforeAll ++ leaves.flatten) leafSuffix 0 ∧
      t.val.tapes 85 = NormalizedRecordParser.cursor
        (preceding ++ (normalizedRecord row column negative bits ++ suffix))
        (preceding.length+(normalizedRecord row column negative bits).length) ∧ Persistent s t := by
  obtain ⟨pc,p,ep,hpc,p15,p16,p23,p83,p85,pi,pf⟩ := NormalizedRecordParser.executes input tape
    row column negative bits preceding suffix powerOrigin origin s h85 h10 h15 h16 h83 h82
  have pk (j : ℕ) (hj : j ∉ NormalizedRecordParser.work) : p.val.tapes j = s.val.tapes j := pf.tapes j hj
  obtain ⟨tc,a,htc,ea,ad,av,a83,a98,af⟩ := TermStore.executes input tape width
    clock bits next gates beforeAll leafSuffix leaves terms negative origin p
    hclock hlen hcount hleaves hroom
    (scratch_of_tapes hs (fun j hj => pk j (by simp [NormalizedRecordParser.work]; omega)))
    (RationalAccumulator.blank_of_eq (pk 94 (by decide)) h94)
    (RationalAccumulator.blank_of_eq (pk 96 (by decide)) h96)
    (RationalAccumulator.blank_of_eq (pk 99 (by decide)) h99)
    (BankArray.word_of_eq (pk 95 (by decide)) hn) ((pk 97 (by decide)).trans hg)
    (BankArray.word_of_eq (pk 93 (by decide)) hc) ((pk 103 (by decide)).trans hl)
    ((pk 98 (by decide)).trans hsource) ((pk 104 (by decide)).trans hterms) p23 p83
  obtain ⟨cc,t,hcc,et,t15,t16,t83,t106,ts,tm,tf⟩ := TermCleanup.executes input tape
    row.bits column.bits bits counter origin a ad.scratch
    ((af.tapes 15 (by omega) (by decide)).trans p15)
    ((af.tapes 16 (by omega) (by decide)).trans p16) a83
    (BankArray.word_of_eq ((af.tapes 106 (by omega) (by decide)).trans (pk 106 (by decide))) hcounter)
  have done : TermStore.Done clock (TermStore.result negative bits next gates leaves) terms t :=
    ⟨ts,RationalAccumulator.blank_of_eq (tf.tapes 94 (by omega) (by decide)) ad.blank94,
      RationalAccumulator.blank_of_eq (tf.tapes 96 (by omega) (by decide)) ad.blank96,
      RationalAccumulator.blank_of_eq (tf.tapes 99 (by omega) (by decide)) ad.blank99,
      (tf.tapes 103 (by omega) (by decide)).trans ad.blank103,
      BankArray.word_of_eq (tf.tapes 95 (by omega) (by decide)) ad.next,
      (tf.tapes 97 (by omega) (by decide)).trans ad.gates,
      (tf.tapes 104 (by omega) (by decide)).trans ad.terms,
      BankArray.word_of_eq (tf.tapes 93 (by omega) (by decide)) ad.clock⟩
  have keep (j : ℕ) (hj : j = 4 ∨ 10 ≤ j) (hn : j ∉ work) : t.val.tapes j = s.val.tapes j := by
    have includeT : TermStore.work ⊆ work := by decide
    have includeC : TermCleanup.work ⊆ work := by decide
    have includeP : NormalizedRecordParser.work ⊆ work := by decide
    have hterm : j ∉ TermStore.work := fun he => hn (includeT he)
    have hcleanup : j ∉ TermCleanup.work := fun he => hn (includeC he)
    have hparser : j ∉ NormalizedRecordParser.work := fun he => hn (includeP he)
    exact (tf.tapes j hj hcleanup).trans ((af.tapes j hj hterm).trans (pk j hparser))
  refine ⟨pc+(tc+cc),t,?_,ep.seq (ea.seq et),done,av,
    (keep 10 (by omega) (by decide)).trans h10,t15,t16,t83,t106,
    (tf.tapes 98 (by omega) (by decide)).trans a98,
    (tf.tapes 85 (by omega) (by decide)).trans ((af.tapes 85 (by omega) (by decide)).trans p85),
    ⟨tm.trans (af.memory.trans pf.memory),tf.inputHead.trans (af.inputHead.trans pi),
      tf.randomCursor.trans (af.randomCursor.trans pf.randomCursor),
      tf.output.trans (af.output.trans pf.output),keep⟩⟩
  unfold bound
  unfold TermStore.costBound at htc
  nlinarith

end Maxwell.Cost.SourceCircuit.CompileRecord
