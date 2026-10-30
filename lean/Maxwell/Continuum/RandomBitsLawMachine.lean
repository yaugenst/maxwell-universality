import Maxwell.Continuum.RandomBitsMachine
import Maxwell.Continuum.FairBitsLaw
import Mathlib.Data.Nat.Size

/-! The integer stored by the actual random-reading loop is the explicit
binary equivalence whose pushforward law was proved uniform. -/

namespace Maxwell.Continuum.RandomBitsMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 800000

theorem addressValue_ofFn {n : ℕ} (w : Fin n → Bool) :
    addressValue (List.ofFn w)=∑i : Fin n,(w i).toNat*2^i.val := by
  induction n with
  | zero => simp [addressValue]
  | succ n ih =>
    rw [List.ofFn_succ,addressValue,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem bits_eq_ofFn (randomTape : ℕ → Bool) (start n : ℕ) :
    bits randomTape start n=List.ofFn (fun i : Fin n => randomTape (start+i.val)) := by
  apply List.ext_getElem
  · simp [bits]
  · intro i hi hj
    simp [bits]

theorem bits_binary_value (randomTape : ℕ → Bool) (start n : ℕ) :
    addressValue (bits randomTape start n)=
      (FairBits.binaryEquiv n (fun i => randomTape (start+i.val))).val := by
  rw [bits_eq_ofFn,addressValue_ofFn,FairBits.binaryEquiv_value]
  apply Finset.sum_congr rfl
  intro i _
  have h (b : Bool) : (finTwoEquiv.symm b).val=b.toNat := by cases b <;> rfl
  rw [h]

theorem compiled_run (input : List Bool) (randomTape : ℕ → Bool) (n : ℕ) (s : Store)
    (hcount : s.val.tapes 240=BitTape.ofList n.bits) (hblank : s.val.tapes 241=BitTape.blank) :
    ∃t : Store,
      (runPriced (code.compile.next input randomTape) (cap n+1) s.val).finished=some (t.place code.size) ∧
      (runPriced (code.compile.next input randomTape) (cap n+1) s.val).instructions≤cap n ∧
      t.val.tapes 241=BitTape.atEnd (bits randomTape s.val.randomCursor n) ∧
      t.val.randomCursor=s.val.randomCursor+n ∧ Frame s.val t.val := by
  obtain ⟨cost,t,he,hc,ht⟩ := executes input randomTape n s hcount hblank
  have hr := he.compiled_run (cap n+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hc,ht⟩

theorem cap_bound (n : ℕ) : cap n≤34*(n+1)^2 := by
  have hn : n.bits.length≤n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  unfold cap
  nlinarith only [hn,Nat.zero_le n]

#print axioms bits_binary_value
#print axioms compiled_run

end Maxwell.Continuum.RandomBitsMachine
