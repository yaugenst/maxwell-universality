import Maxwell.Cost.Execution
import Maxwell.Cost.IndexedAddress

/-! Bounds on the actual source machine state from its charged execution.
The centered simulation tapes therefore need no unproved head assumptions. -/
namespace Maxwell.Cost.RealSimulation

structure SourceBounds (s : BitRAMState) (n : ℕ) : Prop where
  input_lower : -(n:ℤ) ≤ s.inputHead
  input_upper : s.inputHead ≤ (n:ℤ)
  tape_lower : ∀ t, -(n:ℤ) ≤ (s.tapes t).head
  tape_upper : ∀ t, (s.tapes t).head ≤ (n:ℤ)
  address : s.address.length ≤ n
  output : s.output.length ≤ n
  random : s.randomCursor ≤ n

theorem SourceBounds.mono {s : BitRAMState} {n m : ℕ}
    (h : SourceBounds s n) (hn : n ≤ m) : SourceBounds s m := by
  rcases h with ⟨hil, hiu, htl, htu, ha, ho, hr⟩
  refine ⟨by omega, by omega, ?_, ?_, by omega, by omega, by omega⟩
  · intro t; have := htl t; omega
  · intro t; have := htu t; omega

theorem SourceBounds.initial : SourceBounds BitRAMState.initial 0 := by
  constructor <;> simp [BitRAMState.initial, BitTape.blank]

theorem SourceBounds.step {M : BitRAM} {input : List Bool} {tape : ℕ → Bool}
    {s t : BitRAMState} {extra n : ℕ}
    (hs : SourceBounds s n) (h : M.next input tape s = some ⟨t, extra⟩) :
    SourceBounds t (n+1) := by
  rcases hs with ⟨hil, hiu, htl, htu, ha, ho, hr⟩
  cases hc : M.code[s.pc]? with
  | none => simp [BitRAM.next, hc] at h
  | some instruction =>
    cases instruction <;>
      simp only [BitRAM.next, hc, Option.some.injEq, PricedStep.mk.injEq] at h
    all_goals try contradiction
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals constructor
    all_goals simp only [BitRAMState.setRegister, BitRAMState.setTape, BitTape.write,
      List.length_cons, List.length_nil, List.length_tail]
    all_goals try omega
    all_goals intro t
    all_goals try simp only [Function.update_apply]
    all_goals try split_ifs
    all_goals have hlt := htl t
    all_goals have hut := htu t
    all_goals clear htl htu
    all_goals try simp_all only []
    all_goals omega

theorem SourceBounds.priced {M : BitRAM} {input : List Bool} {tape : ℕ → Bool}
    {s t : BitRAMState} {n b : ℕ}
    (h : PricedSteps (M.next input tape) n s t) (hs : SourceBounds s b) :
    SourceBounds t (b+n) := by
  induction h generalizing b with
  | refl s => simpa using hs
  | @step n extra s t u h rest ih =>
    have ht := ih (hs.step h)
    exact ht.mono (by omega)

theorem sourceBounds_of_priced {M : BitRAM} {input : List Bool} {tape : ℕ → Bool}
    {s : BitRAMState} {n : ℕ}
    (h : PricedSteps (M.next input tape) n BitRAMState.initial s) :
    SourceBounds s n := by
  simpa using SourceBounds.initial.priced h

theorem SourceBounds.input_abs {s : BitRAMState} {n : ℕ} (h : SourceBounds s n) :
    |s.inputHead| ≤ (n:ℤ) := abs_le.mpr ⟨h.input_lower, h.input_upper⟩

theorem SourceBounds.tape_abs {s : BitRAMState} {n : ℕ} (h : SourceBounds s n) (t : ℕ) :
    |(s.tapes t).head| ≤ (n:ℤ) := abs_le.mpr ⟨h.tape_lower t, h.tape_upper t⟩

theorem SourceBounds.input_before_cap {s : BitRAMState} {n cap : ℕ}
    (h : SourceBounds s n) (hn : n < cap) : -(cap:ℤ) < s.inputHead := by
  have := h.input_lower
  omega

theorem SourceBounds.tape_before_cap {s : BitRAMState} {n cap : ℕ}
    (h : SourceBounds s n) (hn : n < cap) (t : ℕ) : -(cap:ℤ) < (s.tapes t).head := by
  have := h.tape_lower t
  omega

theorem SourceBounds.address_value {s : BitRAMState} {n : ℕ} (h : SourceBounds s n) :
    addressValue s.address < 2^n :=
  (IndexedAddress.value_lt_pow_length s.address).trans_le (Nat.pow_le_pow_right (by omega) h.address)

end Maxwell.Cost.RealSimulation
