import Maxwell.Main

/-! Fixed finite programs for the two possible nonsingular `nnz ≤ 1`
dimensions. Both programs inspect one input bit and emit compile-time
Boolean constants. Their proofs execute the actual charged BitRAM. -/

namespace Maxwell.Cost.BaseCases

def dimensionSource (n : ℕ) : Source.SparseSystem where
  n := n
  matrix :=
    { support := ∅
      coefficient := fun p => False.elim (Finset.notMem_empty p.val p.property)
      coefficient_ne_zero := fun p => False.elim (Finset.notMem_empty p.val p.property) }
  source := 0

def targetBits (n : ℕ) : List Bool :=
  Codec.target (Maxwell.BaseCases.zeroInstance (dimensionSource n))

def outputBits (n : ℕ) : List Bool := Codec.output (0 : Fin n → ℚ)

def emitBits (bits : List Bool) : List BitRAMInstruction :=
  bits.flatMap fun b => [.literal 0 b, .output 0]

/-- Only the first input bit selects between two fixed literal output strings. -/
def selectEmitter (zero one : List Bool) : BitRAM :=
  ⟨[.readSequential 0, .branch 0 (3 + (emitBits zero).length) 2] ++
    emitBits zero ++ [.halt] ++ emitBits one ++ [.halt]⟩

def encoder : BitRAM := selectEmitter (targetBits 0) (targetBits 1)
def decoder : BitRAM := selectEmitter (outputBits 0) (outputBits 1)
def fuel : ℕ := 2048

def encoderStop0 : BitRAMState :=
  (encoder.run [false] (fun _ => false) fuel).finished.getD BitRAMState.initial
def encoderStop1 : BitRAMState :=
  (encoder.run [true] (fun _ => false) fuel).finished.getD BitRAMState.initial
def decoderStop0 : BitRAMState :=
  (decoder.run [false] (fun _ => false) fuel).finished.getD BitRAMState.initial
def decoderStop1 : BitRAMState :=
  (decoder.run [true] (fun _ => false) fuel).finished.getD BitRAMState.initial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem encoder_run0 (tail : List Bool) (tape : ℕ → Bool) :
    (encoder.run (false :: tail) tape fuel).finished = some encoderStop0 := by rfl
theorem encoder_run1 (tail : List Bool) (tape : ℕ → Bool) :
    (encoder.run (true :: tail) tape fuel).finished = some encoderStop1 := by
  with_unfolding_all rfl
theorem decoder_run0 (tail : List Bool) (tape : ℕ → Bool) :
    (decoder.run (false :: tail) tape fuel).finished = some decoderStop0 := by rfl
theorem decoder_run1 (tail : List Bool) (tape : ℕ → Bool) :
    (decoder.run (true :: tail) tape fuel).finished = some decoderStop1 := by rfl

theorem encoder_output0 : encoderStop0.output.reverse = targetBits 0 := by decide +kernel
theorem encoder_output1 : encoderStop1.output.reverse = targetBits 1 := by decide +kernel
theorem decoder_output0 : decoderStop0.output.reverse = outputBits 0 := by decide +kernel
theorem decoder_output1 : decoderStop1.output.reverse = outputBits 1 := by decide +kernel
theorem encoder_random0 : encoderStop0.randomCursor = 0 := by decide +kernel
theorem encoder_random1 : encoderStop1.randomCursor = 0 := by decide +kernel
theorem decoder_random0 : decoderStop0.randomCursor = 0 := by decide +kernel
theorem decoder_random1 : decoderStop1.randomCursor = 0 := by decide +kernel

theorem targetBits_eq (S : Source.SparseSystem) :
    Codec.target (Maxwell.BaseCases.zeroInstance S) = targetBits S.n := rfl

theorem source_prefix (S : Source.SparseSystem) :
    ∃ tail, Codec.source S = Codec.nat S.n ++ tail := by
  unfold Codec.source
  simp only [List.append_assoc]
  exact ⟨_, rfl⟩

theorem target_prefix (S : Source.SparseSystem) :
    ∃ tail, Codec.target (Maxwell.BaseCases.zeroInstance S) = Codec.nat S.n ++ tail := by
  unfold Codec.target
  simp only [List.append_assoc]
  exact ⟨_, rfl⟩

theorem nat_zero : Codec.nat 0 = [false] := by decide +kernel
theorem nat_one : Codec.nat 1 = [true, false, true] := by decide +kernel

theorem encodes (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1)
    (draw : Realization.Draw 0) :
    Realization.Encodes encoder S draw fuel (Maxwell.BaseCases.zeroInstance S) := by
  have hn : S.n ≤ 1 := (Source.dimension_le_nnz S hunit).trans hm
  obtain ⟨tail, hs⟩ := source_prefix S
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with hn | hn
  · refine ⟨encoderStop0, ?_, ?_, encoder_random0⟩
    · rw [hs, hn, nat_zero]
      exact encoder_run0 tail _
    · rw [targetBits_eq, hn]
      exact encoder_output0
  · refine ⟨encoderStop1, ?_, ?_, encoder_random1⟩
    · rw [hs, hn, nat_one]
      exact encoder_run1 (false :: true :: tail) _
    · rw [targetBits_eq, hn]
      exact encoder_output1

theorem zero_represents (n : ℕ) :
    Codec.RepresentsOutput 1 (0 : Fin n → ℚ) (outputBits n) := by
  apply Codec.canonical_represents
  intro i
  norm_num [Source.ShortRational, signedBitLength, unsignedBitLength]

theorem decodes (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1) :
    Realization.Decodes decoder 1 (Maxwell.BaseCases.zeroInstance S) fuel := by
  intro messages
  have hn : S.n ≤ 1 := (Source.dimension_le_nnz S hunit).trans hm
  obtain ⟨tail, ht⟩ := target_prefix S
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with hn | hn
  · refine ⟨decoderStop0, ?_, ?_, decoder_random0⟩
    · have hnat : Codec.nat S.n = [false] := by rw [hn, nat_zero]
      rw [ht, hnat]
      exact decoder_run0 (tail ++ Codec.messages _ messages) _
    · rw [Maxwell.BaseCases.zero_decoder_decode, decoder_output0]
      simpa only [hn] using zero_represents S.n
  · refine ⟨decoderStop1, ?_, ?_, decoder_random1⟩
    · have hnat : Codec.nat S.n = [true, false, true] := by rw [hn, nat_one]
      rw [ht, hnat]
      exact decoder_run1 (false :: true :: (tail ++ Codec.messages _ messages)) _
    · rw [Maxwell.BaseCases.zero_decoder_decode, decoder_output1]
      simpa only [hn] using zero_represents S.n

/-- Every run, including arbitrary malformed input, is capped by the same
literal number of charged bit operations. -/
theorem encoder_all_inputs_cost (input : List Bool) (tape : ℕ → Bool) :
    (encoder.run input tape fuel).instructions ≤ 2048 :=
  encoder.run_all_inputs_le input tape fuel

theorem decoder_all_inputs_cost (input : List Bool) (tape : ℕ → Bool) :
    (decoder.run input tape fuel).instructions ≤ 2048 :=
  decoder.run_all_inputs_le input tape fuel

theorem finite_base_programs :
    ∃ E D : BitRAM, ∃ N : ℕ,
      ∀ S : Source.SparseSystem, IsUnit (Source.realMatrix S) → S.nnz ≤ 1 →
        (∀ draw : Realization.Draw 0,
          Realization.Encodes E S draw N (Maxwell.BaseCases.zeroInstance S)) ∧
        Realization.Decodes D 1 (Maxwell.BaseCases.zeroInstance S) N := by
  exact ⟨encoder, decoder, fuel, fun S hu hm => ⟨encodes S hu hm, decodes S hu hm⟩⟩

#print axioms finite_base_programs

end Maxwell.Cost.BaseCases
