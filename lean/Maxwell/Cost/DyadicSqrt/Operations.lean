import Maxwell.Cost.DyadicSqrt.Bank

namespace Maxwell.Cost.DyadicSqrt

open Structured RationalAccumulator

def bankIndex (i : Fin 7) : ℕ := 30 + i.val

inductive Operation where
  | add (source target : Fin 7)
  | multiply (source target : Fin 7)
  | copy (source target : Fin 7) (different : source ≠ target)

def Operation.code : Operation → Code
  | .add source target => addCode (bankIndex source) (bankIndex target)
  | .multiply source target => multiplyCode (bankIndex source) (bankIndex target)
  | .copy source target _ => .seq (.call (TapeOps.clear (bankIndex target)))
      (.call (WordTransfer.clone (bankIndex source) (bankIndex target)))

def Operation.value : Operation → (ℕ → ℕ) → (ℕ → ℕ)
  | .add source target, v =>
      Function.update v (bankIndex target) (v (bankIndex source) + v (bankIndex target))
  | .multiply source target, v =>
      Function.update v (bankIndex target) (v (bankIndex source) * v (bankIndex target))
  | .copy source target _, v => Function.update v (bankIndex target) (v (bankIndex source))

def Width (v : ℕ → ℕ) (B : ℕ) : Prop :=
  ∀ i, 30 ≤ i → i ≤ 36 → (v i).bits.length ≤ B

theorem Operation.width (op : Operation) (v : ℕ → ℕ) (B : ℕ) (h : Width v B) :
    Width (op.value v) (2 * B + 1) := by
  cases op with
  | add source target =>
    have hs := h (bankIndex source) (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
    have ht := h (bankIndex target) (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
    intro i hi hi'
    by_cases hit : i = bankIndex target
    · subst i
      simp only [Operation.value, Function.update_self]
      exact (bits_add_le _ _).trans (by omega)
    · simpa only [Operation.value, Function.update_of_ne hit] using (h i hi hi').trans (by omega)
  | multiply source target =>
    have hs := h (bankIndex source) (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
    have ht := h (bankIndex target) (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
    intro i hi hi'
    by_cases hit : i = bankIndex target
    · subst i
      simp only [Operation.value, Function.update_self]
      exact (bits_mul_le _ _).trans (by omega)
    · simpa only [Operation.value, Function.update_of_ne hit] using (h i hi hi').trans (by omega)
  | copy source target hne =>
    intro i hi hi'
    by_cases hit : i = bankIndex target
    · subst i
      simp only [Operation.value, Function.update_self]
      exact (h (bankIndex source) (by dsimp [bankIndex]; omega)
        (by dsimp [bankIndex]; omega)).trans (by omega)
    · simpa only [Operation.value, Function.update_of_ne hit] using (h i hi hi').trans (by omega)

theorem Operation.executes (op : Operation) (input : List Bool) (tape : ℕ → Bool)
    (v : ℕ → ℕ) (B : ℕ) (hwidth : Width v B)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, cost ≤ 5000 * (B + 4)^2 ∧
      Executes input tape op.code cost s t ∧ Bank t.val (op.value v) ∧
      Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  cases op with
  | add source target =>
    have hs := hwidth (bankIndex source) (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
    have ht := hwidth (bankIndex target) (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
    obtain ⟨cost, t, hc, he, hb, hr, hf⟩ := DyadicSqrt.add (bankIndex source) (bankIndex target)
      (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
      (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega) input tape v s hbank hready
    refine ⟨cost, t, ?_, he, hb, hr, hf⟩
    have hpow : B + 4 ≤ (B + 4)^2 := Nat.le_self_pow (by decide) _
    omega
  | multiply source target =>
    have hs := hwidth (bankIndex source) (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
    have ht := hwidth (bankIndex target) (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
    obtain ⟨cost, t, hc, he, hb, hr, hf⟩ := DyadicSqrt.multiply (bankIndex source) (bankIndex target)
      (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
      (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega) input tape v s hbank hready
    refine ⟨cost, t, ?_, he, hb, hr, hf⟩
    have hp := Nat.pow_le_pow_left (show (v (bankIndex source)).bits.length +
      (v (bankIndex target)).bits.length + 3 ≤ 2 * (B + 4) by omega) 2
    nlinarith only [hc, hp, Nat.zero_le ((B + 4)^2)]
  | copy source target hne =>
    have hs := hwidth (bankIndex source) (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
    have ht := hwidth (bankIndex target) (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
    have hidx : bankIndex source ≠ bankIndex target := by
      intro h
      apply hne
      apply Fin.ext
      simpa [bankIndex] using h
    obtain ⟨a, ea, ba, ra, fa⟩ := clear_bank (bankIndex target)
      (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega) input tape v 0 s hbank hready
    obtain ⟨t, et, bt, rt, ft⟩ := clone_bank (bankIndex source) (bankIndex target)
      (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega)
      (by dsimp [bankIndex]; omega) (by dsimp [bankIndex]; omega) hidx input tape
      (Function.update v (bankIndex target) 0) 0 a ba (by simp) ra
    have hv : Function.update (Function.update v (bankIndex target) 0) (bankIndex target)
        ((Function.update v (bankIndex target) 0) (bankIndex source)) =
        Function.update v (bankIndex target) (v (bankIndex source)) := by simp [hidx]
    refine ⟨(6 * (v (bankIndex target)).bits.length + 4) +
      (15 * ((Function.update v (bankIndex target) 0) (bankIndex source)).bits.length + 17),
      t, ?_, ea.seq et, by simpa only [hv, Operation.value] using bt, rt, fa.trans ft⟩
    simp only [Function.update_of_ne hidx]
    have hpow : B + 4 ≤ (B + 4)^2 := Nat.le_self_pow (by decide) _
    omega

def operationsCode : List Operation → Code
  | [] => .skip
  | op :: ops => .seq op.code (operationsCode ops)

def operationsValue : List Operation → (ℕ → ℕ) → (ℕ → ℕ)
  | [], v => v
  | op :: ops, v => operationsValue ops (op.value v)

theorem operations_executes (ops : List Operation) (input : List Bool) (tape : ℕ → Bool)
    (v : ℕ → ℕ) (B : ℕ) (hwidth : Width v B)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store,
      cost ≤ (ops.length + 1) * 5000 * (2 ^ ops.length * (B + 4))^2 ∧
      Executes input tape (operationsCode ops) cost s t ∧
      Bank t.val (operationsValue ops v) ∧ Scratch t.val 0 ∧
      RationalAccumulator.Frame s.val t.val := by
  induction ops generalizing v B s with
  | nil =>
    refine ⟨1, s, ?_, Executes.skip s, hbank, hready, ?_⟩
    · simp only [List.length_nil, zero_add, pow_zero, one_mul]
      have hpow : B + 4 ≤ (B + 4)^2 := Nat.le_self_pow (by decide) _
      omega
    · simp [RationalAccumulator.Frame]
  | cons op ops ih =>
    obtain ⟨c, a, hc, ea, ba, ra, fa⟩ := op.executes input tape v B hwidth s hbank hready
    obtain ⟨d, t, hd, et, bt, rt, ft⟩ :=
      ih (op.value v) (2 * B + 1) (op.width v B hwidth) a ba ra
    refine ⟨c + d, t, ?_, ea.seq et, bt, rt, fa.trans ft⟩
    have hscale : 2 ^ ops.length * (2 * B + 1 + 4) ≤
        2 ^ (ops.length + 1) * (B + 4) := by
      rw [pow_succ]
      nlinarith [Nat.zero_le (2 ^ ops.length)]
    have hscale2 := Nat.pow_le_pow_left hscale 2
    have hbase : B + 4 ≤ 2 ^ (ops.length + 1) * (B + 4) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    have hbase2 := Nat.pow_le_pow_left hbase 2
    simp only [List.length_cons]
    calc
      c + d ≤ 5000 * (2 ^ (ops.length + 1) * (B + 4))^2 +
          (ops.length + 1) * 5000 * (2 ^ (ops.length + 1) * (B + 4))^2 :=
        Nat.add_le_add (hc.trans (Nat.mul_le_mul_left 5000 hbase2))
          (hd.trans (Nat.mul_le_mul_left _ hscale2))
      _ = _ := by ring

end Maxwell.Cost.DyadicSqrt
