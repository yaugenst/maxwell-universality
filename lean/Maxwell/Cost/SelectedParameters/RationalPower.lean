import Maxwell.Cost.SelectedParameters.RationalBasic

/-! Fixed natural powers are finite lists of actual stored-word
multiplications. The exponent occurs in program construction only. -/
namespace Maxwell.Cost.SelectedParameters.Rational
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

def powerLoop (a b num den : ℕ) : ℕ → List NatAssign.Instruction
  | 0 => []
  | k+1 => .multiply a num :: .multiply b den :: powerLoop a b num den k

def powerInstructions (k a b num den : ℕ) : List NatAssign.Instruction :=
  [.literal num 1,.literal den 1] ++ powerLoop a b num den k ++ clear

def powerCode (k a b num den : ℕ) : Code := NatAssign.code (powerInstructions k a b num den)

def powerPair (k a b : ℕ) : ℕ × ℕ := (a^k,b^k)

theorem power_value (k a b : ℕ) : value (powerPair k a b) = ((a:ℚ)/b)^k := by
  simp [value,powerPair,div_pow]

theorem power_denominator (k a b : ℕ) (hb : 0 < b) : 0 < (powerPair k a b).2 :=
  pow_pos hb k

theorem power_bits (k a B : ℕ) (ha : a.bits.length ≤ B) : (a^k).bits.length ≤ k*B+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,Nat.succ_mul]
    have h := bits_mul_le (a^k) a
    omega

theorem power_width (k a b B : ℕ) (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B) :
    (powerPair k a b).1.bits.length ≤ k*B+1 ∧ (powerPair k a b).2.bits.length ≤ k*B+1 :=
  ⟨power_bits k a B ha,power_bits k b B hb⟩

private theorem values_append (xs ys : List NatAssign.Instruction) (v : ℕ → ℕ) :
    NatAssign.values (xs++ys) v = NatAssign.values ys (NatAssign.values xs v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => exact ih (x.update v)

private theorem loop_values (k a b num den : ℕ)
    (han : a ≠ num) (had : a ≠ den) (hbn : b ≠ num) (hbd : b ≠ den) (hne : num ≠ den)
    (v : ℕ → ℕ) :
    NatAssign.values (powerLoop a b num den k) v =
      Function.update (Function.update v num ((v a)^k*v num)) den ((v b)^k*v den) := by
  induction k generalizing v with
  | zero => simp [powerLoop,NatAssign.values]
  | succ k ih =>
    simp only [powerLoop,NatAssign.values]
    rw [ih]
    ext i
    simp only [NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]
    by_cases hin : i = num
    · subst i
      simp [Function.update_apply,han,had,hbn,hbd,hne,pow_succ]
      ring
    · by_cases hid : i = den
      · subst i
        simp [han,had,hbn,hbd,hne,Ne.symm hne,pow_succ]
        ring
      · simp [Function.update_apply,hin,hid]

private theorem power_values (k a b num den : ℕ)
    (han : a ≠ num) (had : a ≠ den) (hbn : b ≠ num) (hbd : b ≠ den) (hne : num ≠ den)
    (v : ℕ → ℕ) :
    NatAssign.values (powerInstructions k a b num den) v = after v num den (powerPair k (v a) (v b)) := by
  rw [powerInstructions,values_append,values_append,loop_values k a b num den han had hbn hbd hne]
  simp only [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,after,powerPair]
  congr 1
  ext i
  by_cases hin : i = num
  · subst i
    simp [han,had,hbn,hbd,hne]
  · by_cases hid : i = den
    · subst i
      simp [han,had,hbn,hbd,hne]
    · simp [Function.update_apply,hin,hid]

private theorem loop_members (k a b num den : ℕ) (inst : NatAssign.Instruction)
    (h : inst ∈ powerLoop a b num den k) : inst = .multiply a num ∨ inst = .multiply b den := by
  induction k with
  | zero => simp [powerLoop] at h
  | succ k ih =>
    simp only [powerLoop,List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact ih h

private theorem loop_length (k a b num den : ℕ) : (powerLoop a b num den k).length = 2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [powerLoop,ih]; omega

def powerCostBound (k B : ℕ) : ℕ := 3000*8^(2*k+9)*(B+3)^2

/-- Fresh output ports preserve the base words throughout the unrolled power.
The two base ports may coincide. -/
theorem power_executes (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i)
    (k a b num den : ℕ) (ha : a ∈ extra) (hb : b ∈ extra) (hnum : num ∈ extra) (hden : den ∈ extra)
    (han : a ≠ num) (had : a ≠ den) (hbn : b ≠ num) (hbd : b ≠ den) (hne : num ≠ den)
    (v : ℕ → ℕ) (B : ℕ) (hwidth : ∀ i ∈ ids extra, (v i).bits.length ≤ B)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank (ids extra) v s.val) (hscratch : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input randomTape (powerCode k a b num den) cost s t ∧
      cost ≤ powerCostBound k B ∧
      NatAssign.Bank (ids extra) (after v num den (powerPair k (v a) (v b))) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (workspace num den) s.val t.val := by
  have hids : ∀ i ∈ ids extra, 4 ≤ i := by
    intro i hi
    simp only [ids,common,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · exact (by omega : 4 ≤ 540).trans (hextra i hi)
    · omega
  have hv : ∀ inst ∈ powerInstructions k a b num den, inst.Valid (ids extra) := by
    intro inst hi
    simp only [powerInstructions,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with ((rfl | rfl) | hi) | hi
    · simp [NatAssign.Instruction.Valid,ids,hnum]
    · simp [NatAssign.Instruction.Valid,ids,hden]
    · rcases loop_members k a b num den inst hi with rfl | rfl <;>
        simp [NatAssign.Instruction.Valid,ids,ha,hb,hnum,hden,han,hbd]
    · simp only [clear,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [NatAssign.Instruction.Valid,ids,common]
  obtain ⟨cost,t,he,hcost,ht,hs,hf⟩ := NatAssign.executes (ids extra) hids
    (powerInstructions k a b num den) hv v input randomTape s hbank hscratch
  have heq := power_values k a b num den han had hbn hbd hne v
  refine ⟨cost,t,he,?_,heq ▸ ht,hs,hf.mono ?_⟩
  · have hp := NatAssign.price_bound (ids extra) (powerInstructions k a b num den) hv v (B+1)
      (fun i hi => (hwidth i hi).trans (by omega)) (by
        intro inst hi
        simp only [powerInstructions,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with ((rfl | rfl) | hi) | hi
        · simp [NatAssign.Instruction.literalWidth]
        · simp [NatAssign.Instruction.literalWidth]
        · rcases loop_members k a b num den inst hi with rfl | rfl <;> simp [NatAssign.Instruction.literalWidth]
        · simp only [clear,List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [NatAssign.Instruction.literalWidth])
    have hlen : (powerInstructions k a b num den).length = 2*k+9 := by
      simp [powerInstructions,loop_length,clear]
    rw [hlen] at hp
    exact hcost.trans (by simpa only [powerCostBound,Nat.add_assoc] using hp)
  · intro i hi
    simp only [NatAssign.changes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      List.mem_toFinset,List.mem_map] at hi
    rcases hi with hi | ⟨inst,hinst,rfl⟩
    · simp only [workspace,common,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    · simp only [powerInstructions,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hinst
      rcases hinst with ((rfl | rfl) | hi) | hi
      · simp [NatAssign.Instruction.target,workspace]
      · simp [NatAssign.Instruction.target,workspace]
      · rcases loop_members k a b num den inst hi with rfl | rfl <;> simp [NatAssign.Instruction.target,workspace]
      · simp only [clear,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [NatAssign.Instruction.target,workspace,common]

end Maxwell.Cost.SelectedParameters.Rational
