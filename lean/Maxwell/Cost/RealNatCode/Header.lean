import Maxwell.Cost.RealNatCode.Program

namespace Maxwell.Cost.RealNatCode
open RealSparse (execute execute_add execute_sound)
set_option maxRecDepth 20000

structure HeaderReady (s : RAMState) (L : Layout) (n j : ℕ) : Prop where
  pc : s.pc = 17
  zero : s.indices 0 = 0
  one : s.indices 1 = 1
  number : s.indices 2 = n
  count : s.indices 3 = n.size
  cacheCursor : s.indices 5 = L.cacheAt n.size
  payloadCursor : s.indices 6 = L.bufferAt (2 * n.size)
  length : s.indices 7 = n.size
  headerCursor : s.indices 8 = L.bufferAt j
  remaining : s.indices 9 = n.size - j
  cacheBase : s.indices 20 = L.cache
  bufferBase : s.indices 21 = L.buffer
  stride : s.indices 22 = L.stride
  cache : ∀ i < n.size, s.indices (L.cacheAt i) = 2 ^ i
  header : ∀ i < j, s.indices (L.bufferAt i) = 1

noncomputable def headerStart (s : RAMState) : RAMState :=
  let t := ({s with pc := 14} : RAMState).setIndex 7 (s.indices 3)
  let t := t.setIndex 8 (s.indices 21)
  t.setIndex 9 (s.indices 3)

theorem header_start_steps (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n : ℕ)
    (s : RAMState) (h : PowerReady s L n n.size) :
    execute (program.next input tape) 4 s = some (headerStart s) := by
  rcases h with ⟨hpc, _, _, hn, _, hp, _, _, _, _, _, _⟩
  have hstop : ¬ 2 ^ n.size ≤ n := not_le_of_gt (Nat.lt_size_self n)
  simp [execute, program, Machine.next, headerStart, hpc, hn, hp, hstop, RAMState.setIndex]

theorem headerStart_ready (L : Layout) (n : ℕ) (s : RAMState)
    (h : PowerReady s L n n.size) : HeaderReady (headerStart s) L n 0 := by
  rcases h with ⟨_, hz, ho, hn, hk, _, hc, hb, hlc, hlb, hls, hcache⟩
  constructor <;> simp_all [headerStart, RAMState.setIndex, Layout.bufferAt]

noncomputable def headerAdvanced (s : RAMState) : RAMState :=
  let t := ({s with pc := 18} : RAMState).setIndex (s.indices 8) (s.indices 1)
  let t := t.setIndex 8 (s.indices 8 + s.indices 22)
  let t := t.setIndex 9 (s.indices 9 - s.indices 1)
  {t with pc := 17}

theorem header_cycle (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n j : ℕ)
    (s : RAMState) (h : HeaderReady s L n j) (hj : j < n.size) :
    execute (program.next input tape) 5 s = some (headerAdvanced s) := by
  have hgo : ¬ n.size - j ≤ 0 := by omega
  simp [execute, program, Machine.next, headerAdvanced, h.pc, h.zero, h.remaining,
    h.headerCursor, hgo, RAMState.setIndex]

theorem headerAdvanced_ready (L : Layout) (n j : ℕ) (s : RAMState)
    (h : HeaderReady s L n j) (_hj : j < n.size) :
    HeaderReady (headerAdvanced s) L n (j + 1) := by
  constructor
  all_goals simp only [headerAdvanced, RAMState.setIndex, h.zero, h.one, h.number,
    h.count, h.cacheCursor, h.payloadCursor, h.length, h.headerCursor, h.remaining,
    h.cacheBase, h.bufferBase, h.stride, Function.update_apply]
  all_goals try simp only [Layout.bufferAt_ne_low, Layout.low_ne_bufferAt, Nat.reduceLT,
    Nat.reduceEqDiff, ↓reduceIte]
  · simp [Layout.bufferAt, Nat.mul_add, Nat.add_assoc]
  · omega
  · intro i hi
    have he : L.cacheAt i ≠ L.bufferAt j := L.disjoint i j
    simp [he, h.cache i hi]
  · intro i hi
    by_cases he : i = j
    · subst i
      simp
    · have hne : L.bufferAt i ≠ L.bufferAt j := fun hh => he (L.bufferAt_injective hh)
      simp [hne, h.header i (by omega)]

theorem headers (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n remaining : ℕ)
    (s : RAMState) (j : ℕ) (h : HeaderReady s L n j) (hlen : j + remaining = n.size) :
    ∃ t : RAMState, Steps (program.next input tape) (5 * remaining) s t ∧
      HeaderReady t L n n.size := by
  induction remaining generalizing s j with
  | zero =>
    have hj : j = n.size := by omega
    exact ⟨s, Steps.refl s, hj ▸ h⟩
  | succ remaining ih =>
    obtain ⟨t, ht, hr⟩ := ih (headerAdvanced s) (j + 1)
      (headerAdvanced_ready L n j s h (by omega)) (by omega)
    refine ⟨t, ?_, hr⟩
    convert (execute_sound _ (header_cycle input tape L n j s h (by omega))).trans ht using 1
    omega

end Maxwell.Cost.RealNatCode
