import Maxwell.Cost.CalibrationMatrix.Scale.Pass
import Maxwell.Cost.CalibrationMatrix.Value

namespace Maxwell.Cost.CalibrationMatrix.Scale
variable {n : ℕ}

def channels (words : Fin 4 → Vector (List Bool) n) (positive negative : Fin 4) : Channels n :=
  ⟨fun i => value words positive i, fun i => value words negative i⟩

theorem filled_value (d : Data n) (words : Fin 4 → Vector (List Bool) n) (port : Fin 4)
    (hp : 2 ≤ port.val) (i : Fin n) (value : ℕ)
    (he : payload d words port i = FixedWidth.bits (addressValue d.width) value.bits)
    (hfit : value.bits.length ≤ addressValue d.width) :
    Scale.value (filledWords d words n) port i = value := by
  simp only [Scale.value, filledWords, ite_eq_right (by omega : ¬port.val < 2), fillPrefix_full]
  have hg : (Vector.ofFn (payload d words port)).get i = payload d words port i := by
    simp [Vector.get, Fin.cast]
  rw [hg, he, FixedWidth.bits_value _ _ hfit, addressValue_bits]

theorem filled_channels (d : Data n) (words : Fin 4 → Vector (List Bool) n)
    (hp : ∀ i, (positive d words i).bits.length ≤ addressValue d.width)
    (hn : ∀ i, (negative d words i).bits.length ≤ addressValue d.width) :
    channels (filledWords d words n) 2 3 = (channels words 0 1).scale d.K := by
  have p2 := fun i => filled_value d words 2 (by decide) i _ (by simp [payload]) (hp i)
  have p3 := fun i => filled_value d words 3 (by decide) i _ (by simp [payload]) (hn i)
  apply congrArg₂ Channels.mk <;> funext i
  · change value (filledWords d words n) 2 i = d.K * value words 0 i
    rw [p2]; exact Nat.mul_comm _ _
  · change value (filledWords d words n) 3 i = d.K * value words 1 i
    rw [p3]; exact Nat.mul_comm _ _

open Structured
open RationalAccumulator (Blank)

theorem compiled_run (d : Data n) (words : Fin 4 → Vector (List Bool) n) (B : ℕ)
    (hd : d.Sized B) (hn : n < 2^B)
    (hwp : ∀ i, (positive d words i).bits.length ≤ addressValue d.width)
    (hwn : ∀ i, (negative d words i).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (index count : List Bool)
    (hi : addressValue index = 0) (hc : addressValue count = n)
    (hil : index.length ≤ B) (hcl : count.length ≤ B) (origin : ℤ) (s : Store)
    (hr : Ready s.val (dotValues 0 0)) (hdata : Stored d words s.val)
    (hindex : BankArray.Word s.val 104 index) (h37 : Blank s.val 37)
    (h108 : s.val.tapes 108 = BitTape.shifted count origin) :
    ∃ t : Store, ∃ finalIndex : List Bool,
      (runPriced (code.compile.next input tape) (costBound n B+1) s.val).finished = some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costBound n B+1) s.val).instructions ≤
        750000*(n+1)*(B+2)^2 ∧
      addressValue finalIndex = n ∧ finalIndex.length ≤ B ∧ BankArray.Word t.val 104 finalIndex ∧
      Stored d (filledWords d words n) t.val ∧ Ready t.val (dotValues 0 0) ∧
      Blank t.val 37 ∧ Blank t.val 108 ∧
      (∀ j, j = 102 ∨ j = 103 ∨ j = 106 → t.val.tapes j = s.val.tapes j) ∧
      MatrixFrame s.val t.val ∧ Outside d s.val t.val := by
  obtain ⟨steps, t, fi, hs, he, ht⟩ := executes d words B hd hn hwp hwn
    input tape index count hi hc hil hcl origin s hr hdata hindex h37 h108
  have hrun := he.compiled_run (costBound n B+1) (by omega)
  exact ⟨t, fi, hrun.1, hrun.2 ▸ hs.trans (costBound_le n B), ht⟩

end Maxwell.Cost.CalibrationMatrix.Scale
