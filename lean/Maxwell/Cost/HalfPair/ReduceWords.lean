import Maxwell.Cost.HalfPair.Words

namespace Maxwell.Cost.HalfPair

theorem reduce_value (xs : List Bool) (b : Bool) :
    addressValue (xs++[false]) = addressValue (xs++[b,false]) % 2^xs.length := by
  rw [addressValue_append,addressValue_append]
  simp only [addressValue,Bool.toNat_false,mul_zero,add_zero]
  rw [Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (IndexedAddress.value_lt_pow_length xs)).symm

/-- A child label keeps its low bits and one explicit padding zero. -/
theorem reduce_word (k : ℕ) (i : Fin (2*(2^k))) (xs : List Bool) (b : Bool)
    (hlen : xs.length = k)
    (hword : SourceCircuit.fixedWidth (k+2) i.val = xs++[b,false]) :
    xs++[false] = SourceCircuit.fixedWidth (k+1) (i.val % 2^k) := by
  apply SourceCircuit.fixedWidth_eq
  · simp [hlen]
  · rw [reduce_value,hlen,← hword,SourceCircuit.fixedWidth_value]
    have h := i.isLt
    rw [show k+2=(k+1)+1 by omega,pow_succ,pow_succ]
    omega

theorem exists_reduce_word (k : ℕ) (i : Fin (2*(2^k))) :
    ∃ xs : List Bool, ∃ b : Bool, xs.length = k ∧
      SourceCircuit.fixedWidth (k+2) i.val = xs++[b,false] ∧
      xs++[false] = SourceCircuit.fixedWidth (k+1) (i.val % 2^k) := by
  obtain ⟨xs,b,hlen,hword⟩ := word_decomposition k i
  exact ⟨xs,b,hlen,hword,reduce_word k i xs b hlen hword⟩

end Maxwell.Cost.HalfPair
