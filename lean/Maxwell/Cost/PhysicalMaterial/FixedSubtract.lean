import Maxwell.Cost.CounterShifted
import Maxwell.Cost.NormalizeWord
import Maxwell.Cost.BinaryPrecision

/-! Subtract a fixed prototype offset with charged bit operations. The amount
is unrolled into finite syntax; it is never an unbounded runtime primitive. -/
namespace Maxwell.Cost.PhysicalMaterial.FixedSubtract
open Structured RationalAccumulator

abbrev Frame (target : ℕ) := BinaryPrecision.Frame {target}

private def decrements (target : ℕ) : ℕ → Code
  | 0 => .skip
  | k+1 => .seq (.call (Counter.programOn target)) (decrements target k)

def code (target : ℕ) : ℕ → Code
  | 0 => .skip
  | k+1 => .seq (decrements target (k+1)) (.call (NormalizeWord.program target))

def costBound (amount width : ℕ) : ℕ := 1+amount*(29*width+30)

private theorem decrement_executes (target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (word : List Bool) (origin : ℤ) (s : Store)
    (hw : s.val.tapes target = BitTape.shifted word origin) :
    ∃ t, Executes input randomTape (.call (Counter.programOn target)) (13*word.length+12) s t ∧
      t.val.tapes target = BitTape.shifted (subtractBit true word) origin ∧ Frame target s.val t.val := by
  obtain ⟨t,et,hpc,ht,_,hf⟩ := CounterShifted.steps_on target input randomTape word origin s.val s.property hw
  refine ⟨Store.ofState t,?_,ht,⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩⟩
  · exact Executes.call _ s t _ et (by
      simp [Counter.programOn,BitRAM.renameTapes,hpc,Counter.program,BitRAM.link,
        Counter.counterSuffix,binaryCounter,Rewind.program,BitRAMInstruction.relocate,
        BitRAMInstruction.renameTapes])
  · intro i hi
    exact hf.2.2.2.2.2.1 i (by simpa using hi)

private theorem decrements_executes (target amount : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (word : List Bool) (origin : ℤ) (s : Store) (hroom : amount ≤ addressValue word)
    (hw : s.val.tapes target = BitTape.shifted word origin) :
    ∃ t result, Executes input randomTape (decrements target amount)
        (amount*(13*word.length+12)+1) s t ∧
      t.val.tapes target = BitTape.shifted result origin ∧ result.length = word.length ∧
      addressValue result = addressValue word-amount ∧ Frame target s.val t.val := by
  induction amount generalizing word s with
  | zero => exact ⟨s,word,by simpa [decrements] using (Executes.skip (input := input) (randomTape := randomTape) s),hw,rfl,by simp,BinaryPrecision.Frame.refl _ _⟩
  | succ amount ih =>
    obtain ⟨a,ea,ha,fa⟩ := decrement_executes target input randomTape word origin s hw
    have hpred : addressValue (subtractBit true word) = addressValue word-1 :=
      subtractBit_pred word (by omega)
    obtain ⟨t,result,et,ht,hlen,hvalue,ft⟩ := ih (subtractBit true word) a (by omega) ha
    refine ⟨t,result,?_,ht,hlen.trans (subtractBit_length true word),?_,fa.trans ft⟩
    · convert ea.seq et using 1 <;> first | rfl | simp only [subtractBit_length]; ring
    · rw [hvalue,hpred]
      omega

/-- The output is canonical and returns to exactly the original tape origin,
including the boundary case where subtraction produces the empty zero word. -/
theorem executes_shifted (target amount n : ℕ) (hroom : amount ≤ n)
    (input : List Bool) (randomTape : ℕ → Bool) (origin : ℤ) (s : Store)
    (hw : s.val.tapes target = BitTape.shifted n.bits origin) :
    ∃ cost t, Executes input randomTape (code target amount) cost s t ∧
      cost ≤ costBound amount n.bits.length ∧
      t.val.tapes target = BitTape.shifted (n-amount).bits origin ∧ Frame target s.val t.val := by
  cases amount with
  | zero => exact ⟨1,s,.skip s,by simp [costBound],by simpa using hw,BinaryPrecision.Frame.refl _ _⟩
  | succ k =>
    obtain ⟨a,result,ea,ha,hlen,hvalue,fa⟩ := decrements_executes target (k+1) input randomTape
      n.bits origin s (by simpa using hroom) hw
    obtain ⟨nc,t,hnc,et,hpc,ht,_,ft⟩ := NormalizeWord.simulation target origin input randomTape
      result a.val a.property ha
    have en : Executes input randomTape (.call (NormalizeWord.program target)) (nc+1) a (Store.ofState t) :=
      .call _ a t _ et (by simp [NormalizeWord.program,hpc,ScanForward.program,TapeOps.trim,
        Rewind.program,BitRAMInstruction.relocate])
    have fn : Frame target a.val (Store.ofState t).val :=
      ⟨ft.1,ft.2.1,ft.2.2.1,ft.2.2.2.1,ft.2.2.2.2.1,
        fun i hi => ft.2.2.2.2.2.1 i (by simpa using hi)⟩
    refine ⟨_,Store.ofState t,ea.seq en,?_,?_,fa.trans fn⟩
    · rw [hlen] at hnc
      dsimp [costBound]
      nlinarith
    · change t.tapes target = _
      simpa only [hvalue,address_bits] using ht

/-- Origin-independent form used when composing prototype-coordinate work. -/
theorem executes (target amount n : ℕ) (hroom : amount ≤ n)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store) (hw : Word s.val target n) :
    ∃ cost t, Executes input randomTape (code target amount) cost s t ∧
      cost ≤ costBound amount n.bits.length ∧ Word t.val target (n-amount) ∧ Frame target s.val t.val := by
  obtain ⟨origin,ho⟩ := hw
  obtain ⟨cost,t,he,hc,ht,hf⟩ := executes_shifted target amount n hroom input randomTape origin s ho
  exact ⟨cost,t,he,hc,⟨origin,ht⟩,hf⟩

end Maxwell.Cost.PhysicalMaterial.FixedSubtract
