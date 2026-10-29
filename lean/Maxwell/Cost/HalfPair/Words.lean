import Maxwell.Cost.SourceCircuit.TraceBinding
import Maxwell.Logical.Routing.NumericSplit

/-! The source-pair table for a power-of-two array is produced by flipping
one existing bit of each padded index word. -/
namespace Maxwell.Cost.HalfPair
open Maxwell.Logical.Routing.Coloring.NumericSplit

theorem addressValue_append (xs ys : List Bool) :
    addressValue (xs++ys) = addressValue xs + 2^xs.length * addressValue ys := by
  induction xs with
  | nil => simp [addressValue]
  | cons b xs ih =>
    simp only [List.cons_append,addressValue,List.length_cons,ih,pow_succ]
    ring

theorem array_bits_length (k : ℕ) : (2*(2^k)).bits.length = k+2 := by
  rw [Nat.size_eq_bits_len,← pow_succ',Nat.size_pow]

/-- The extra high bit is zero for every index in the source array. -/
theorem word_decomposition (k : ℕ) (i : Fin (2*(2^k))) :
    ∃ xs : List Bool, ∃ b : Bool, xs.length = k ∧
      SourceCircuit.fixedWidth (k+2) i.val = xs++[b,false] := by
  let word := SourceCircuit.fixedWidth (k+2) i.val
  have hlen : word.length = k+2 := SourceCircuit.fixedWidth_length _ _
  have htake : (word.take k).length = k := by simp [List.length_take,hlen]
  have hdrop : (word.drop k).length = 2 := by simp [List.length_drop,hlen]
  obtain ⟨b,c,hbc⟩ := List.length_eq_two.mp hdrop
  have hw : word = word.take k ++ [b,c] := by
    rw [← hbc,List.take_append_drop]
  have hi : i.val < 2^(k+2) := by
    have h := i.isLt
    rw [show k+2 = (k+1)+1 by omega,pow_succ,pow_succ]
    omega
  have hv := SourceCircuit.fixedWidth_value (k+2) i.val hi
  change addressValue word = i.val at hv
  rw [hw,addressValue_append,htake] at hv
  cases c
  · exact ⟨word.take k,b,htake,hw⟩
  · have h := i.isLt
    cases b <;> simp only [addressValue,Bool.toNat_true,Bool.toNat_false,
      mul_zero,mul_one,add_zero,zero_add] at hv <;> omega

/-- Flipping the next-to-last stored bit computes the actual half pairing. -/
theorem flip_value (k : ℕ) (i : Fin (2*(2^k))) (xs : List Bool) (b : Bool)
    (hlen : xs.length = k)
    (hword : SourceCircuit.fixedWidth (k+2) i.val = xs++[b,false]) :
    addressValue (xs++[!b,false]) = (halfSwap (2^k) i).val := by
  have hi : i.val < 2^(k+2) := by
    have h := i.isLt
    rw [show k+2 = (k+1)+1 by omega,pow_succ,pow_succ]
    omega
  have hv := SourceCircuit.fixedWidth_value (k+2) i.val hi
  rw [hword,addressValue_append,hlen] at hv
  have hlo := IndexedAddress.value_lt_pow_length xs
  rw [hlen] at hlo
  rw [addressValue_append,hlen,halfSwap_val]
  cases b <;> simp only [Bool.not_false,Bool.not_true,addressValue,
    Bool.toNat_false,Bool.toNat_true,mul_zero,mul_one,add_zero] at hv ⊢
  · rw [ite_eq_left (by omega)]
    omega
  · rw [ite_eq_right (by omega)]
    omega

theorem flip_word (k : ℕ) (i : Fin (2*(2^k))) (xs : List Bool) (b : Bool)
    (hlen : xs.length = k)
    (hword : SourceCircuit.fixedWidth (k+2) i.val = xs++[b,false]) :
    xs++[!b,false] = SourceCircuit.fixedWidth (k+2) (halfSwap (2^k) i).val := by
  apply SourceCircuit.fixedWidth_eq
  · simp [hlen]
  · exact flip_value k i xs b hlen hword

theorem exists_flip_word (k : ℕ) (i : Fin (2*(2^k))) :
    ∃ xs : List Bool, ∃ b : Bool, xs.length = k ∧
      SourceCircuit.fixedWidth (k+2) i.val = xs++[b,false] ∧
      xs++[!b,false] = SourceCircuit.fixedWidth (k+2) (halfSwap (2^k) i).val := by
  obtain ⟨xs,b,hlen,hword⟩ := word_decomposition k i
  exact ⟨xs,b,hlen,hword,flip_word k i xs b hlen hword⟩

end Maxwell.Cost.HalfPair
