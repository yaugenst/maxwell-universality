import Maxwell.Cost.SourceCircuit.WordStack

namespace Maxwell.Cost.SparseEmission.Prepend
open Structured
open SourceCircuit (Frame)

/-- Consume a temporary word backwards and prepend it, in its original bit
order, to the actual sparse archive. The physical width clock is restored. -/
def code (source clock archive : ℕ) : Code := SourceCircuit.WordStack.code source clock archive

theorem executes (source clock archive : ℕ) (hsc : source ≠ clock)
    (hsa : source ≠ archive) (hca : clock ≠ archive)
    (input : List Bool) (randomTape : ℕ → Bool)
    (word preceding clockWord : List Bool) (origin clockOrigin : ℤ) (s : Store)
    (hwidth : clockWord.length = word.length)
    (hs : s.val.tapes source = BitTape.atEnd word)
    (ha : s.val.tapes archive = BitTape.shifted preceding origin)
    (hc : s.val.tapes clock = BitTape.shifted clockWord clockOrigin) :
    ∃ t, Executes input randomTape (code source clock archive) (15*word.length+10) s t ∧
      t.val.tapes source = BitTape.blank ∧
      t.val.tapes archive = BitTape.shifted (word ++ preceding) (origin-word.length) ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      Frame {source,archive} s.val t.val ∧
      (∀ i, i ≠ source → i ≠ archive → t.val.tapes i = s.val.tapes i) := by
  let cells := (BitTape.shifted clockWord clockOrigin).cells
  have present : ∀ k : ℕ, k < word.length → ∃ b, cells (clockOrigin+k) = some b := by
    intro k hk
    have hk' : k < clockWord.length := by omega
    exact ⟨clockWord[k], by simp [cells, BitTape.shifted, hk']⟩
  have ended : cells (clockOrigin+word.length) = none := by
    simp [cells, BitTape.shifted, ← hwidth]
  obtain ⟨a, ea, hap, has, hat, hac, haf⟩ := SourceCircuit.WordStack.loop source clock archive
    hsc hsa hca input randomTape word [] preceding origin clockOrigin cells s.val s.property
    (by simpa using hs) ha (by simpa [cells,BitTape.shifted] using hc) present ended
  let a' := Store.ofState a
  have e1 := Executes.call (SourceCircuit.WordStack.rawProgram source clock archive) s a _ ea
    (by simp [SourceCircuit.WordStack.rawProgram,hap])
  have haClock : a'.val.tapes clock = BitTape.shiftedEnd clockWord clockOrigin := by
    simpa [a',Store.ofState,cells,BitTape.shiftedEnd,hwidth] using hac
  have rewind := WordTransfer.rewind_shifted clock clockOrigin input randomTape clockWord
    a'.val a'.property haClock
  let t := Store.ofState (Rewind.finishAt clock clockOrigin a'.val)
  have e2 : Executes input randomTape (.call (Rewind.program clock)) (4*clockWord.length+6) a' t :=
    .call _ a' _ _ rewind.1 (by simp [Rewind.program,Rewind.finishAt])
  have htClock : t.val.tapes clock = s.val.tapes clock := rewind.2.trans hc.symm
  have keep (i : ℕ) (his : i ≠ source) (hia : i ≠ archive) : t.val.tapes i = s.val.tapes i := by
    by_cases hic : i = clock
    · subst i; exact htClock
    · simpa [t,a',Store.ofState,Rewind.finishAt,hic] using haf.2.2.2.2.2.1 i his hic hia
  refine ⟨t, ?_, ?_, ?_, haf.1, haf.2.2.1, ?_, keep⟩
  · unfold code SourceCircuit.WordStack.code
    convert e1.seq e2 using 1
    omega
  · simpa [t,a',Store.ofState,Rewind.finishAt,hsc,BitTape.atEnd_nil] using has
  · simpa [t,a',Store.ofState,Rewind.finishAt,hca.symm] using hat
  · refine ⟨haf.2.1,haf.2.2.2.1,haf.2.2.2.2.1,?_,?_,?_⟩
    · intro i _ hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
      exact keep i hi.1 hi.2
    · simpa [t,a',Store.ofState,Rewind.finishAt] using
        haf.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)
    · intro i hi
      simpa [t,a',Store.ofState,Rewind.finishAt,show i ≠ 24 by omega,show i ≠ 25 by omega] using
        haf.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)

def literalBit (archive : ℕ) (bit : Bool) : Code :=
  .seq (.atom (.literal 26 bit))
    (.seq (.atom (.tapeLeft archive)) (.atom (.writeTape archive 26)))

def bitState (archive : ℕ) (bit : Bool) (s : Store) : Store := Store.ofState
  {s.val with
    registers := Function.update s.val.registers 26 bit
    tapes := Function.update s.val.tapes archive
      (({s.val.tapes archive with head := (s.val.tapes archive).head-1}).write (some bit))}

theorem literalBit_executes (archive : ℕ) (bit : Bool) (input : List Bool)
    (randomTape : ℕ → Bool) (s : Store) :
    Executes input randomTape (literalBit archive bit) 6 s (bitState archive bit s) := by
  let a := Store.ofState (s.val.setRegister 26 bit)
  let b := Store.ofState (a.val.setTape archive {a.val.tapes archive with head := (a.val.tapes archive).head-1})
  have e1 := Executes.literal input randomTape s 26 bit
  have e2 := Executes.tapeLeft input randomTape a archive
  have e3 := Executes.writeTape input randomTape b archive 26
  convert e1.seq (e2.seq e3) using 1 <;>
    simp [literalBit,bitState,a,b,Store.ofState,BitRAMState.setRegister,BitRAMState.setTape]

theorem bitState_word (archive : ℕ) (bit : Bool) (s : Store) (preceding : List Bool) (origin : ℤ)
    (ha : s.val.tapes archive = BitTape.shifted preceding origin) :
    (bitState archive bit s).val.tapes archive = BitTape.shifted (bit::preceding) (origin-1) := by
  simpa [bitState,Store.ofState,ha,BitTape.shifted] using
    NormalizeCoefficient.PadReverse.prepend_word preceding origin bit

def literals (archive : ℕ) : List Bool → Code
  | [] => .skip
  | bit::rest => .seq (literals archive rest) (literalBit archive bit)

theorem literals_executes (archive : ℕ) (bits preceding : List Bool) (origin : ℤ)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (ha : s.val.tapes archive = BitTape.shifted preceding origin) :
    ∃ t, Executes input randomTape (literals archive bits) (6*bits.length+1) s t ∧
      t.val.tapes = Function.update s.val.tapes archive
        (BitTape.shifted (bits++preceding) (origin-bits.length)) ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧ Frame {archive} s.val t.val := by
  induction bits generalizing s origin with
  | nil =>
    refine ⟨s,.skip s,?_,rfl,rfl,?_⟩
    · simp [← ha]
    · exact ⟨rfl,rfl,rfl,fun _ _ _ => rfl,rfl,fun _ _ => rfl⟩
  | cons bit bits ih =>
    obtain ⟨a,ea,atapes,aa,am,af⟩ := ih origin s ha
    have aw : a.val.tapes archive = BitTape.shifted (bits++preceding) (origin-bits.length) := by simp [atapes]
    let t := bitState archive bit a
    have tw := bitState_word archive bit a _ _ aw
    have btapes : t.val.tapes = Function.update a.val.tapes archive
        (BitTape.shifted ((bit::bits)++preceding) (origin-(bit::bits).length)) := by
      funext i
      by_cases hi : i = archive
      · subst i; simpa [Nat.cast_add,sub_sub] using tw
      · simp [t,bitState,Store.ofState,hi]
    have bf : Frame {archive} a.val t.val := by
      refine ⟨rfl,rfl,rfl,?_,by simp [t,bitState,Store.ofState],?_⟩
      · intro i _ hi
        simp only [Finset.mem_singleton] at hi
        simp [t,bitState,Store.ofState,hi]
      · intro i hi
        simp [t,bitState,Store.ofState,show i ≠ 26 by omega]
    refine ⟨t,?_,?_,aa,am,af.trans bf⟩
    · simpa [literals,Nat.mul_add,Nat.add_assoc] using ea.seq (literalBit_executes archive bit input randomTape a)
    · simp [btapes,atapes]

end Maxwell.Cost.SparseEmission.Prepend
