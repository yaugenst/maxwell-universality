import Maxwell.Cost.DecoderParser.Target
import Maxwell.Cost.DecoderParser.Bounds

namespace Maxwell.Cost.DecoderParser
open Structured

theorem retainedTargetPrice_le {n : ℕ} (I : Target.Instance n) :
    retainedTargetPrice I ≤ 2 * targetPrice I := by
  simp only [retainedTargetPrice,targetPrice,targetPayload,decoderPayload,physicalPrefix,
    coordinatePayload,rowPayload,price,retainedListPrice,listPrice]
  omega

theorem retainedTargetPrice_bound {n : ℕ} (I : Target.Instance n) (B : ℕ)
    (hB : WidthBound targetShape (targetPayload I) B) :
    retainedTargetPrice I ≤ 2 * shapeConstant targetShape * (Codec.target I).length * (B+1) := by
  have h := price_le targetShape (targetPayload I) B hB
  rw [target_wire] at h
  have hh := (retainedTargetPrice_le I).trans (Nat.mul_le_mul_left 2 h)
  simpa [Nat.mul_assoc] using hh

/-- End-to-end finite parsing, including actual halt and charged operation
count. Scalar metadata and the exact encoded plan are available to the
subsequent finite message loader and weighted row evaluator. -/
theorem retainedTarget_run {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages)
    (randomTape : ℕ → Bool) :
    ∃ (cost : ℕ) (t : Store),
      (runPriced (retainedTargetCode.compile.next
        (Codec.target I ++ Codec.messages I.decoder w) randomTape)
        (retainedTargetPrice I+1) BitRAMState.initial).finished =
          some (t.place retainedTargetCode.size) ∧
      (runPriced (retainedTargetCode.compile.next
        (Codec.target I ++ Codec.messages I.decoder w) randomTape)
        (retainedTargetPrice I+1) BitRAMState.initial).instructions = cost ∧
      cost ≤ retainedTargetPrice I ∧ t.val.inputHead = (Codec.target I).length ∧
      t.val.tapes 18 = BitTape.atEnd (Codec.target I) ∧ DecoderMetadata I t.val ∧
      Ready 0 t.val ∧ Frame {18,40,41,42,43,44} BitRAMState.initial t.val := by
  obtain ⟨cost,t,ht,hc,hh,hl,hm,hr,hf⟩ := retainedTarget_steps I (Codec.messages I.decoder w) randomTape
  have he := ht.compiled_run (retainedTargetPrice I+1) (by omega)
  exact ⟨cost,t,he.1,he.2,hc,hh,hl,hm,hr,hf⟩

end Maxwell.Cost.DecoderParser
