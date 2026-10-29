import Maxwell.Cost.RealNatCode.Header

namespace Maxwell.Cost.RealNatCode
open RealSparse (execute execute_add execute_sound)
set_option maxRecDepth 20000

structure PayloadReady (s : RAMState) (L : Layout) (n k : ℕ) : Prop where
  pc : s.pc = 23
  zero : s.indices 0 = 0
  one : s.indices 1 = 1
  number : s.indices 2 = n % 2 ^ k
  count : s.indices 3 = k
  cacheCursor : s.indices 5 = L.cacheAt k
  payloadCursor : s.indices 6 = L.bufferAt (n.size + k)
  length : s.indices 7 = n.size
  cacheBase : s.indices 20 = L.cache
  bufferBase : s.indices 21 = L.buffer
  stride : s.indices 22 = L.stride
  cache : ∀ i < n.size, s.indices (L.cacheAt i) = 2 ^ i
  header : ∀ i < n.size, s.indices (L.bufferAt i) = 1
  separator : s.indices (L.bufferAt n.size) = 0
  payload : ∀ i, k ≤ i → i < n.size →
    s.indices (L.bufferAt (n.size + 1 + i)) = (n.testBit i).toNat

noncomputable def payloadStart (s : RAMState) : RAMState :=
  ({s with pc := 22} : RAMState).setIndex (s.indices 8) (s.indices 0)

theorem payload_start_steps (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n : ℕ)
    (s : RAMState) (h : HeaderReady s L n n.size) :
    execute (program.next input tape) 2 s = some (payloadStart s) := by
  simp [execute, program, Machine.next, payloadStart, h.pc, h.zero, h.remaining,
    RAMState.setIndex]

theorem payloadStart_ready (L : Layout) (n : ℕ) (s : RAMState)
    (h : HeaderReady s L n n.size) : PayloadReady (payloadStart s) L n n.size := by
  constructor
  all_goals try simp only [payloadStart, RAMState.setIndex, h.headerCursor, h.zero, h.one,
    h.number, h.count, h.cacheCursor, h.payloadCursor, h.length, h.cacheBase,
    h.bufferBase, h.stride, Function.update_apply]
  all_goals try simp only [Layout.low_ne_bufferAt, Nat.reduceLT, ↓reduceIte]
  · exact (Nat.mod_eq_of_lt (Nat.lt_size_self n)).symm
  · congr 1; omega
  · intro i hi
    have hne : L.cacheAt i ≠ L.bufferAt n.size := L.disjoint i n.size
    simp [hne, h.cache i hi]
  · intro i hi
    have hne : L.bufferAt i ≠ L.bufferAt n.size := fun he => by
      have := L.bufferAt_injective he; omega
    simp [hne, h.header i hi]
  · intro i hle hlt
    omega

noncomputable def payloadPrepared (s : RAMState) : RAMState :=
  let t := ({s with pc := 24} : RAMState).setIndex 3 (s.indices 3 - s.indices 1)
  let t := t.setIndex 5 (s.indices 5 - s.indices 22)
  t.setIndex 10 (s.indices (s.indices 5 - s.indices 22))

noncomputable def payloadAdvanced (s : RAMState) : RAMState :=
  let t := payloadPrepared s
  let a := s.indices (s.indices 5 - s.indices 22)
  let t := t.setIndex 2 (if a ≤ s.indices 2 then s.indices 2 - a else s.indices 2)
  let t := t.setIndex (s.indices 6) (if a ≤ s.indices 2 then s.indices 1 else s.indices 0)
  let t := t.setIndex 6 (s.indices 6 - s.indices 22)
  {t with pc := 23}

theorem cache_prev (L : Layout) (k : ℕ) : L.cacheAt (k + 1) - L.stride = L.cacheAt k := by
  simp only [Layout.cacheAt, Nat.mul_add, Nat.mul_one]
  omega

theorem buffer_prev (L : Layout) (n k : ℕ) :
    L.bufferAt (n + (k + 1)) - L.stride = L.bufferAt (n + k) := by
  simp only [Layout.bufferAt, Nat.mul_add, Nat.mul_one]
  omega

set_option maxHeartbeats 1200000 in
theorem payload_cycle (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n k : ℕ)
    (s : RAMState) (h : PayloadReady s L n (k + 1)) :
    execute (program.next input tape) 10 s = some (payloadAdvanced s) := by
  have ha : execute (program.next input tape) 4 s = some (payloadPrepared s) := by
    simp [execute, program, Machine.next, payloadPrepared, h.pc, h.zero, h.one,
      h.count, h.cacheCursor, h.stride, cache_prev, RAMState.setIndex]
  rw [show 10 = 4 + 6 from rfl, execute_add, ha, Option.bind_some]
  by_cases hd : s.indices (L.cacheAt k) ≤ s.indices 2
  · simp [execute, program, Machine.next, payloadPrepared, payloadAdvanced,
      h.one, h.payloadCursor, h.cacheCursor, h.stride, cache_prev,
      RAMState.setIndex, hd]
  · simp [execute, program, Machine.next, payloadPrepared, payloadAdvanced,
      h.one, h.zero, h.payloadCursor, h.cacheCursor, h.stride, cache_prev,
      RAMState.setIndex, hd]

theorem payloadAdvanced_ready (L : Layout) (n k : ℕ) (s : RAMState)
    (h : PayloadReady s L n (k + 1)) (hk : k < n.size) :
    PayloadReady (payloadAdvanced s) L n k := by
  have hp := h.cache k hk
  have hbit : (if 2 ^ k ≤ n % 2 ^ (k + 1) then 1 else 0) = (n.testBit k).toNat := by
    rw [← bit_decision]
    split_ifs <;> simp_all [not_le_of_gt]
  constructor
  all_goals try simp only [payloadAdvanced, payloadPrepared, RAMState.setIndex,
    h.zero, h.one, h.number, h.count, h.cacheCursor, h.payloadCursor, h.length,
    h.cacheBase, h.bufferBase, h.stride, cache_prev, hp, Function.update_apply]
  all_goals try simp only [Layout.bufferAt_ne_low, Layout.low_ne_bufferAt, Nat.reduceLT,
    Nat.reduceEqDiff, ↓reduceIte, Nat.add_sub_cancel, remainder_step, buffer_prev]
  · intro i hi
    have hne : L.cacheAt i ≠ L.bufferAt (n.size + (k + 1)) := L.disjoint i (n.size + (k + 1))
    simp [hne, h.cache i hi]
  · intro i hi
    have hne : L.bufferAt i ≠ L.bufferAt (n.size + (k + 1)) := fun he => by
      have := L.bufferAt_injective he; omega
    simp [hne, h.header i hi]
  · have hne : L.bufferAt n.size ≠ L.bufferAt (n.size + (k + 1)) := fun he => by
      have := L.bufferAt_injective he; omega
    simp [hne, h.separator]
  · intro i hki hi
    by_cases he : i = k
    · subst i
      have heq : n.size + 1 + k = n.size + (k + 1) := by omega
      simp [heq, hbit]
    · have hne : L.bufferAt (n.size + 1 + i) ≠ L.bufferAt (n.size + (k + 1)) := fun hh => by
        have := L.bufferAt_injective hh; omega
      simp [hne, h.payload i (by omega) hi]

theorem payloads (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n k : ℕ)
    (s : RAMState) (h : PayloadReady s L n k) (hk : k ≤ n.size) :
    ∃ t : RAMState, Steps (program.next input tape) (10 * k) s t ∧ PayloadReady t L n 0 := by
  induction k generalizing s with
  | zero => exact ⟨s, Steps.refl s, h⟩
  | succ k ih =>
    obtain ⟨t, ht, hr⟩ := ih (payloadAdvanced s) (payloadAdvanced_ready L n k s h (by omega)) (by omega)
    refine ⟨t, ?_, hr⟩
    convert (execute_sound _ (payload_cycle input tape L n k s h)).trans ht using 1
    omega

end Maxwell.Cost.RealNatCode
