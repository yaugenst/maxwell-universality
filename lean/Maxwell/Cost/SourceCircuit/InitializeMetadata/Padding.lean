import Maxwell.Cost.SourceCircuit.InitializeMetadata.Clock
import Maxwell.Cost.BankArray.WriteCanonical

namespace Maxwell.Cost.SourceCircuit.InitializeMetadata
open Structured
open RationalAccumulator (Blank)

/-- Stored compiler data and sequential channels survive scratch work. -/
structure Preservation (changed : Finset ℕ) (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, (i = 4 ∨ 10 ≤ i) → i ∉ changed → t.tapes i = s.tapes i

theorem Preservation.trans {changed : Finset ℕ} {s t u : BitRAMState}
    (h : Preservation changed s t) (k : Preservation changed t u) : Preservation changed s u :=
  ⟨k.inputHead.trans h.inputHead,k.memory.trans h.memory,
    k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi hc => (k.tapes i hi hc).trans (h.tapes i hi hc)⟩

theorem Preservation.mono {a b : Finset ℕ} {s t : BitRAMState}
    (h : Preservation a s t) (hab : a ⊆ b) : Preservation b s t :=
  ⟨h.inputHead,h.memory,h.randomCursor,h.output,
    fun i hi hc => h.tapes i hi (fun ha => hc (hab ha))⟩

theorem preservation_frame {changed : Finset ℕ} {s t : BitRAMState}
    (h : Frame changed s t) : Preservation changed s t :=
  ⟨h.inputHead,h.memory,h.randomCursor,h.output,fun i _ hi => h.tapes i hi⟩

theorem scratch_transport {s t : BitRAMState} (hs : BankArray.Scratch s)
    (ht : ∀ i, i < 10 → t.tapes i = s.tapes i) : BankArray.Scratch t := by
  rcases hs with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
  exact ⟨RationalAccumulator.blank_of_eq (ht 0 (by decide)) h0,
    RationalAccumulator.blank_of_eq (ht 1 (by decide)) h1,
    RationalAccumulator.blank_of_eq (ht 2 (by decide)) h2,
    RationalAccumulator.blank_of_eq (ht 3 (by decide)) h3,
    RationalAccumulator.blank_of_eq (ht 5 (by decide)) h5,
    RationalAccumulator.blank_of_eq (ht 6 (by decide)) h6,
    RationalAccumulator.blank_of_eq (ht 8 (by decide)) h8,
    RationalAccumulator.blank_of_eq (ht 9 (by decide)) h9⟩

def packCode (source target : ℕ) : Code := .seq (BankArray.packCanonicalCode source 93)
  (.call (WordTransfer.move 37 target))

/-- Padding is performed by actual tape reads, writes and moves. -/
theorem pack (source target : ℕ) (hs : 10 ≤ source) (ht : 10 ≤ target)
    (h37 : target ≠ 37) (input : List Bool) (tape : ℕ → Bool)
    (xs clock : List Bool) (hclock : 0 < clock.length) (hfit : xs.length ≤ clock.length)
    (s : Store) (hsource : BankArray.Word s.val source xs)
    (hclockBank : BankArray.Word s.val 93 clock)
    (hblank : Blank s.val target) (h7 : Blank s.val 7) (h37blank : Blank s.val 37)
    (hready : BankArray.Scratch s.val) :
    ∃ cost t, cost ≤ 100*clock.length+110 ∧ Executes input tape (packCode source target) cost s t ∧
      BankArray.Word t.val target (FixedWidth.bits clock.length xs) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧
      Preservation {37,target} s.val t.val := by
  obtain ⟨ac,a,hac,ea,ha37,has,ha7,hacontrol,fa⟩ :=
    BankArray.pack_canonical source 93 hs (by decide) input tape xs clock hclock hfit s
      hready h7 h37blank hsource hclockBank
  obtain ⟨origin,ho⟩ := ha37
  obtain ⟨dest,hd⟩ := hblank
  have hat : a.val.tapes target = {BitTape.blank with head := dest} :=
    (fa.2.2.2.1 target (Or.inr ht) h37).trans hd
  obtain ⟨tstate,et,hpc,ht37,htt,ft⟩ := WordTransfer.move_steps 37 target h37.symm input tape
    (FixedWidth.bits clock.length xs) origin dest a.val a.property ho hat
  let t := Store.ofState tstate
  have ee : Executes input tape (.call (WordTransfer.move 37 target))
      (12*(FixedWidth.bits clock.length xs).length+11) a t :=
    .call _ a _ _ et (by rw [hpc]; rfl)
  refine ⟨_,t,by simp only [FixedWidth.bits_length]; omega,ea.seq ee,⟨dest,htt⟩,
    scratch_transport has (fun i hi => ft.2.2.2.2.2.1 i (by omega) (by omega)),
    RationalAccumulator.blank_of_eq (ft.2.2.2.2.2.1 7 (by decide) (by omega)) ha7,
    ⟨origin+(FixedWidth.bits clock.length xs).length,ht37⟩,
    ft.2.1.trans hacontrol.1,ft.2.2.1.trans hacontrol.2.2.2.1,
    ft.2.2.2.1.trans hacontrol.2.1,ft.2.2.2.2.1.trans hacontrol.2.2.1,?_⟩
  intro i hi hc
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hc
  exact (ft.2.2.2.2.2.1 i hc.1 hc.2).trans (fa.2.2.2.1 i hi hc.1)

end Maxwell.Cost.SourceCircuit.InitializeMetadata
