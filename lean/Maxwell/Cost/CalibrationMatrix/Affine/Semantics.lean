import Maxwell.Cost.CalibrationMatrix.Affine.Pass
import Maxwell.Cost.CalibrationMatrix.Value

namespace Maxwell.Cost.CalibrationMatrix.Affine
variable {n : ℕ}

def channels (words : Fin 10 → Vector (List Bool) n) (positive negative : Fin 10) : Channels n :=
  ⟨fun i => value words positive i, fun i => value words negative i⟩

def output (K S : ℕ) (w x u : Channels n) : Channels n × Channels n :=
  (w.scale K, ((w.scale K).add (x.scale K)).add (u.scale S).negate)

theorem output_eq_hornerStep (A : ChannelMatrix n) (D S : ℕ) (w x : Channels n) :
    output (D^3) S w x (matvec A (matvec A x)) = hornerStep A D S (w,x) := rfl

theorem filled_value (d : Data n) (words : Fin 10 → Vector (List Bool) n) (port : Fin 10)
    (hp : 6 ≤ port.val) (i : Fin n) (value : ℕ)
    (he : payload d words port i = FixedWidth.bits (addressValue d.width) value.bits)
    (hfit : value.bits.length ≤ addressValue d.width) :
    Affine.value (filledWords d words n) port i = value := by
  simp only [Affine.value, filledWords, ite_eq_right (by omega : ¬port.val < 6), fillPrefix_full]
  have hg : (Vector.ofFn (payload d words port)).get i = payload d words port i := by
    simp [Vector.get, Fin.cast]
  rw [hg, he, FixedWidth.bits_value _ _ hfit, addressValue_bits]

theorem filled_channels (d : Data n) (words : Fin 10 → Vector (List Bool) n)
    (hwp : ∀ i, (newWPositive d words i).bits.length ≤ addressValue d.width)
    (hwn : ∀ i, (newWNegative d words i).bits.length ≤ addressValue d.width)
    (hxp : ∀ i, (newXPositive d words i).bits.length ≤ addressValue d.width)
    (hxn : ∀ i, (newXNegative d words i).bits.length ≤ addressValue d.width) :
    (channels (filledWords d words n) 6 7, channels (filledWords d words n) 8 9) =
      output d.K d.S (channels words 0 1) (channels words 2 3) (channels words 4 5) := by
  have p6 := fun i => filled_value d words 6 (by decide) i _ (by simp [payload]) (hwp i)
  have p7 := fun i => filled_value d words 7 (by decide) i _ (by simp [payload]) (hwn i)
  have p8 := fun i => filled_value d words 8 (by decide) i _ (by simp [payload]) (hxp i)
  have p9 := fun i => filled_value d words 9 (by decide) i _ (by simp [payload]) (hxn i)
  apply Prod.ext
  · apply congrArg₂ Channels.mk <;> funext i
    · change value (filledWords d words n) 6 i = d.K * value words 0 i
      rw [p6]; exact Nat.mul_comm _ _
    · change value (filledWords d words n) 7 i = d.K * value words 1 i
      rw [p7]; exact Nat.mul_comm _ _
  · apply congrArg₂ Channels.mk <;> funext i
    · change value (filledWords d words n) 8 i =
        d.K * value words 0 i + d.K * value words 2 i + d.S * value words 5 i
      rw [p8]; simp only [newXPositive, partialPositive, newWPositive, Nat.mul_comm]
    · change value (filledWords d words n) 9 i =
        d.K * value words 1 i + d.K * value words 3 i + d.S * value words 4 i
      rw [p9]; simp only [newXNegative, partialNegative, newWNegative, Nat.mul_comm]

open Structured
open RationalAccumulator (Blank)

theorem compiled_run (d : Data n) (words : Fin 10 → Vector (List Bool) n) (B : ℕ)
    (hd : d.Sized B) (hn : n < 2^B)
    (hwp : ∀ i, (newWPositive d words i).bits.length ≤ addressValue d.width)
    (hwn : ∀ i, (newWNegative d words i).bits.length ≤ addressValue d.width)
    (hxp : ∀ i, (newXPositive d words i).bits.length ≤ addressValue d.width)
    (hxn : ∀ i, (newXNegative d words i).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (index count : List Bool)
    (hi : addressValue index = 0) (hc : addressValue count = n)
    (hil : index.length ≤ B) (hcl : count.length ≤ B) (origin : ℤ) (s : Store)
    (hr : Ready s.val (dotValues 0 0)) (hdata : Stored d words s.val)
    (hindex : BankArray.Word s.val 104 index) (h37 : Blank s.val 37)
    (h108 : s.val.tapes 108 = BitTape.shifted count origin) :
    ∃ t : Store, ∃ finalIndex : List Bool,
      (runPriced (code.compile.next input tape) (costBound n B+1) s.val).finished = some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costBound n B+1) s.val).instructions ≤
        2100000*(n+1)*(B+2)^2 ∧
      addressValue finalIndex = n ∧ finalIndex.length ≤ B ∧ BankArray.Word t.val 104 finalIndex ∧
      Stored d (filledWords d words n) t.val ∧ Ready t.val (dotValues 0 0) ∧
      Blank t.val 37 ∧ Blank t.val 108 ∧
      (∀ j, j = 102 ∨ j = 103 ∨ j = 106 → t.val.tapes j = s.val.tapes j) ∧
      MatrixFrame s.val t.val ∧ Outside d s.val t.val := by
  obtain ⟨steps, t, fi, hs, he, ht⟩ := executes d words B hd hn hwp hwn hxp hxn
    input tape index count hi hc hil hcl origin s hr hdata hindex h37 h108
  have hrun := he.compiled_run (costBound n B+1) (by omega)
  exact ⟨t, fi, hrun.1, hrun.2 ▸ hs.trans (costBound_le n B), ht⟩

end Maxwell.Cost.CalibrationMatrix.Affine
