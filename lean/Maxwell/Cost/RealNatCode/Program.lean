import Maxwell.Cost.RealSparse
import Maxwell.Cost.RealLink
import Maxwell.Cost.RealNatCode.Arithmetic

namespace Maxwell.Cost.RealNatCode
open RealSparse (execute execute_add execute_sound)
set_option maxRecDepth 20000

/-- Separate affine memory banks; the caller supplies their actual addresses. -/
structure Layout where
  cache : ℕ
  buffer : ℕ
  stride : ℕ
  cache_ge : 256 ≤ cache
  buffer_ge : 256 ≤ buffer
  stride_pos : 0 < stride
  disjoint : ∀ i j, cache + stride * i ≠ buffer + stride * j

def Layout.cacheAt (L : Layout) (k : ℕ) : ℕ := L.cache + L.stride * k
def Layout.bufferAt (L : Layout) (k : ℕ) : ℕ := L.buffer + L.stride * k

theorem Layout.cacheAt_ge (L : Layout) (k : ℕ) : 256 ≤ L.cacheAt k :=
  le_trans L.cache_ge (Nat.le_add_right _ _)
theorem Layout.bufferAt_ge (L : Layout) (k : ℕ) : 256 ≤ L.bufferAt k :=
  le_trans L.buffer_ge (Nat.le_add_right _ _)
@[simp] theorem Layout.cacheAt_ne_low (L : Layout) (k i : ℕ) (hi : i < 256) :
    L.cacheAt k ≠ i := by have := L.cacheAt_ge k; omega
@[simp] theorem Layout.low_ne_cacheAt (L : Layout) (k i : ℕ) (hi : i < 256) :
    i ≠ L.cacheAt k := (L.cacheAt_ne_low k i hi).symm
@[simp] theorem Layout.bufferAt_ne_low (L : Layout) (k i : ℕ) (hi : i < 256) :
    L.bufferAt k ≠ i := by have := L.bufferAt_ge k; omega
@[simp] theorem Layout.low_ne_bufferAt (L : Layout) (k i : ℕ) (hi : i < 256) :
    i ≠ L.bufferAt k := (L.bufferAt_ne_low k i hi).symm

theorem Layout.cacheAt_injective (L : Layout) : Function.Injective L.cacheAt := by
  intro i j h
  have he : L.stride * i = L.stride * j := Nat.add_left_cancel h
  exact Nat.eq_of_mul_eq_mul_left L.stride_pos he

theorem Layout.bufferAt_injective (L : Layout) : Function.Injective L.bufferAt := by
  intro i j h
  have he : L.stride * i = L.stride * j := Nat.add_left_cancel h
  exact Nat.eq_of_mul_eq_mul_left L.stride_pos he

/-- A fixed natural codec writes its header and little-endian payload into
an explicit strided Boolean buffer. No index division is needed. -/
def program : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .indexLiteral 3 0, .indexLiteral 4 1,
  .indexCopy 5 20, .indexCopy 6 21,
  .branchIndexLE 4 2 7 14,
  .storeIndex 5 4, .indexAdd 5 5 22, .indexAdd 6 6 22, .indexAdd 6 6 22,
  .indexAdd 4 4 4, .indexAdd 3 3 1, .jump 6,
  .indexCopy 7 3, .indexCopy 8 21, .indexCopy 9 3,
  .branchIndexLE 9 0 22 18, .storeIndex 8 1, .indexAdd 8 8 22,
  .indexSubtract 9 9 1, .jump 17,
  .storeIndex 8 0,
  .branchIndexLE 3 0 36 24, .indexSubtract 3 3 1,
  .indexSubtract 5 5 22, .loadIndex 10 5,
  .branchIndexLE 10 2 28 31, .indexSubtract 2 2 10, .storeIndex 6 1, .jump 34,
  .indexCopy 2 2, .storeIndex 6 0, .jump 34,
  .indexSubtract 6 6 22, .jump 23, .halt]⟩

def PowerReady (s : RAMState) (L : Layout) (n k : ℕ) : Prop :=
  s.pc = 6 ∧ s.indices 0 = 0 ∧ s.indices 1 = 1 ∧ s.indices 2 = n ∧
  s.indices 3 = k ∧ s.indices 4 = 2 ^ k ∧ s.indices 5 = L.cacheAt k ∧
  s.indices 6 = L.bufferAt (2 * k) ∧ s.indices 20 = L.cache ∧
  s.indices 21 = L.buffer ∧ s.indices 22 = L.stride ∧
  ∀ j < k, s.indices (L.cacheAt j) = 2 ^ j

noncomputable def initialized (s : RAMState) : RAMState :=
  let t := s.setIndex 0 0
  let t := t.setIndex 1 1
  let t := t.setIndex 3 0
  let t := t.setIndex 4 1
  let t := t.setIndex 5 (s.indices 20)
  t.setIndex 6 (s.indices 21)

theorem initialize_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 0) :
    execute (program.next input tape) 6 s = some (initialized s) := by
  simp [execute, program, Machine.next, initialized, hpc, RAMState.setIndex]

theorem initialized_ready (s : RAMState) (L : Layout) (n : ℕ) (hpc : s.pc = 0)
    (hn : s.indices 2 = n) (hc : s.indices 20 = L.cache)
    (hb : s.indices 21 = L.buffer) (hd : s.indices 22 = L.stride) :
    PowerReady (initialized s) L n 0 := by
  simp [PowerReady, initialized, RAMState.setIndex, hpc, hn, hc, hb, hd,
    Layout.cacheAt, Layout.bufferAt]

noncomputable def powerAdvanced (s : RAMState) : RAMState :=
  let t := ({s with pc := 7} : RAMState).setIndex (s.indices 5) (s.indices 4)
  let t := t.setIndex 5 (s.indices 5 + s.indices 22)
  let t := t.setIndex 6 (s.indices 6 + s.indices 22)
  let t := t.setIndex 6 (s.indices 6 + s.indices 22 + s.indices 22)
  let t := t.setIndex 4 (s.indices 4 + s.indices 4)
  let t := t.setIndex 3 (s.indices 3 + s.indices 1)
  {t with pc := 6}

set_option maxHeartbeats 1200000 in
theorem power_cycle (input : RAMInput) (tape : ℕ → Bool) (s : RAMState)
    (L : Layout) (n k : ℕ) (h : PowerReady s L n k) (hk : k < n.size) :
    execute (program.next input tape) 8 s = some (powerAdvanced s) := by
  rcases h with ⟨hpc, _, _, hn, _, hp, hc, _, _, _, _, _⟩
  have hgo : 2 ^ k ≤ n := Nat.lt_size.mp hk
  simp [execute, program, Machine.next, powerAdvanced, hpc, hn, hp, hc, hgo,
    RAMState.setIndex]

theorem powerAdvanced_ready (s : RAMState) (L : Layout) (n k : ℕ)
    (h : PowerReady s L n k) : PowerReady (powerAdvanced s) L n (k + 1) := by
  rcases h with ⟨hpc, hz, ho, hn, hk, hp, hc, hb, hlc, hlb, hls, hcache⟩
  simp only [PowerReady, powerAdvanced, RAMState.setIndex, hz, ho, hn, hk, hp, hc, hb,
    hlc, hlb, hls, Function.update_apply]
  simp only [Layout.cacheAt_ne_low, Layout.low_ne_cacheAt, Nat.reduceLT, ↓reduceIte,
    Nat.reduceEqDiff, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow_succ]; omega
  · simp [Layout.cacheAt, Nat.mul_add]; omega
  · simp [Layout.bufferAt, Nat.mul_add]; omega
  · intro j hj
    by_cases he : j = k
    · subst j
      simp
    · have hne : L.cacheAt j ≠ L.cacheAt k := fun hh => he (L.cacheAt_injective hh)
      simp only [hne, ↓reduceIte]
      exact hcache j (by omega)

theorem powers (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n remaining : ℕ)
    (s : RAMState) (k : ℕ) (h : PowerReady s L n k) (hlen : k + remaining = n.size) :
    ∃ t : RAMState, Steps (program.next input tape) (8 * remaining) s t ∧
      PowerReady t L n n.size := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = n.size := by omega
    exact ⟨s, Steps.refl s, hk ▸ h⟩
  | succ remaining ih =>
    obtain ⟨t, ht, hr⟩ := ih (powerAdvanced s) (k + 1) (powerAdvanced_ready s L n k h) (by omega)
    refine ⟨t, ?_, hr⟩
    convert (execute_sound _ (power_cycle input tape s L n k h (by omega))).trans ht using 1
    omega

end Maxwell.Cost.RealNatCode
