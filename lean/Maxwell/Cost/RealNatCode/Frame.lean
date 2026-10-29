import Maxwell.Cost.RealNatCode.Correctness

namespace Maxwell.Cost.RealNatCode
open RealSparse (execute execute_sound)

/-- Only low work registers, the live power cache, and the newly emitted
codec interval may be changed. Earlier serialized words remain protected. -/
def Protected (L : Layout) (n i : ℕ) : Prop :=
  11 ≤ i ∧ (∀ j < n.size, i ≠ L.cacheAt j) ∧
    ∀ j < 2 * n.size + 1, i ≠ L.bufferAt j

structure Frame (L : Layout) (n : ℕ) (s t : RAMState) : Prop where
  words : t.words = s.words
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput
  indices : ∀ i, Protected L n i → t.indices i = s.indices i

theorem Frame.refl (L : Layout) (n : ℕ) (s : RAMState) : Frame L n s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {L : Layout} {n : ℕ} {s t u : RAMState}
    (h : Frame L n s t) (k : Frame L n t u) : Frame L n s u :=
  ⟨k.words.trans h.words, k.randomCursor.trans h.randomCursor,
    k.output.trans h.output, k.indexOutput.trans h.indexOutput,
    fun i hi => (k.indices i hi).trans (h.indices i hi)⟩

@[simp] theorem protected_ne_low {L : Layout} {n i : ℕ} (h : Protected L n i)
    (j : ℕ) (hj : j < 11) : i ≠ j := by have := h.1; omega

theorem initialized_frame (L : Layout) (n : ℕ) (s : RAMState) :
    Frame L n s (initialized s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  simp [initialized, RAMState.setIndex, protected_ne_low hi]

theorem powerAdvanced_frame (L : Layout) (n k : ℕ) (s : RAMState)
    (h : PowerReady s L n k) (hk : k < n.size) : Frame L n s (powerAdvanced s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have hc : i ≠ s.indices 5 := by rw [h.2.2.2.2.2.2.1]; exact hi.2.1 k hk
  simp [powerAdvanced, RAMState.setIndex, protected_ne_low hi, hc]

theorem headerStart_frame (L : Layout) (n : ℕ) (s : RAMState) : Frame L n s (headerStart s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  simp [headerStart, RAMState.setIndex, protected_ne_low hi]

theorem headerAdvanced_frame (L : Layout) (n j : ℕ) (s : RAMState)
    (h : HeaderReady s L n j) (hj : j < n.size) : Frame L n s (headerAdvanced s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have hb : i ≠ s.indices 8 := by rw [h.headerCursor]; exact hi.2.2 j (by omega)
  simp [headerAdvanced, RAMState.setIndex, protected_ne_low hi, hb]

theorem payloadStart_frame (L : Layout) (n : ℕ) (s : RAMState)
    (h : HeaderReady s L n n.size) : Frame L n s (payloadStart s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have hb : i ≠ s.indices 8 := by rw [h.headerCursor]; exact hi.2.2 n.size (by omega)
  simp [payloadStart, RAMState.setIndex, hb]

theorem payloadAdvanced_frame (L : Layout) (n k : ℕ) (s : RAMState)
    (h : PayloadReady s L n (k + 1)) (hk : k < n.size) : Frame L n s (payloadAdvanced s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have hb : i ≠ s.indices 6 := by rw [h.payloadCursor]; exact hi.2.2 (n.size + (k + 1)) (by omega)
  simp [payloadAdvanced, payloadPrepared, RAMState.setIndex, protected_ne_low hi, hb]

theorem powers_frame (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n remaining : ℕ)
    (s : RAMState) (k : ℕ) (h : PowerReady s L n k) (hlen : k + remaining = n.size) :
    ∃ t : RAMState, Steps (program.next input tape) (8 * remaining) s t ∧
      PowerReady t L n n.size ∧ Frame L n s t := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = n.size := by omega
    exact ⟨s, Steps.refl s, hk ▸ h, Frame.refl L n s⟩
  | succ remaining ih =>
    obtain ⟨t, ht, hr, hf⟩ := ih (powerAdvanced s) (k + 1) (powerAdvanced_ready s L n k h) (by omega)
    refine ⟨t, ?_, hr, (powerAdvanced_frame L n k s h (by omega)).trans hf⟩
    convert (execute_sound _ (power_cycle input tape s L n k h (by omega))).trans ht using 1
    omega

theorem headers_frame (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n remaining : ℕ)
    (s : RAMState) (j : ℕ) (h : HeaderReady s L n j) (hlen : j + remaining = n.size) :
    ∃ t : RAMState, Steps (program.next input tape) (5 * remaining) s t ∧
      HeaderReady t L n n.size ∧ Frame L n s t := by
  induction remaining generalizing s j with
  | zero =>
    have hj : j = n.size := by omega
    exact ⟨s, Steps.refl s, hj ▸ h, Frame.refl L n s⟩
  | succ remaining ih =>
    obtain ⟨t, ht, hr, hf⟩ := ih (headerAdvanced s) (j + 1)
      (headerAdvanced_ready L n j s h (by omega)) (by omega)
    refine ⟨t, ?_, hr, (headerAdvanced_frame L n j s h (by omega)).trans hf⟩
    convert (execute_sound _ (header_cycle input tape L n j s h (by omega))).trans ht using 1
    omega

theorem payloads_frame (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n k : ℕ)
    (s : RAMState) (h : PayloadReady s L n k) (hk : k ≤ n.size) :
    ∃ t : RAMState, Steps (program.next input tape) (10 * k) s t ∧
      PayloadReady t L n 0 ∧ Frame L n s t := by
  induction k generalizing s with
  | zero => exact ⟨s, Steps.refl s, h, Frame.refl L n s⟩
  | succ k ih =>
    obtain ⟨t, ht, hr, hf⟩ := ih (payloadAdvanced s)
      (payloadAdvanced_ready L n k s h (by omega)) (by omega)
    refine ⟨t, ?_, hr, (payloadAdvanced_frame L n k s h (by omega)).trans hf⟩
    convert (execute_sound _ (payload_cycle input tape L n k s h)).trans ht using 1
    omega

theorem terminates_frame (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n : ℕ)
    (s : RAMState) (hpc : s.pc = 0) (hn : s.indices 2 = n)
    (hc : s.indices 20 = L.cache) (hb : s.indices 21 = L.buffer)
    (hd : s.indices 22 = L.stride) :
    ∃ t : RAMState, Terminates (program.next input tape) (23 * n.size + 13) s t ∧
      t.pc = 36 ∧ t.indices 7 = n.size ∧ t.indices 6 = L.bufferAt n.size ∧
      Stored t L n ∧ Frame L n s t := by
  have hi := execute_sound _ (initialize_steps input tape s hpc)
  obtain ⟨s₁, h₁, hr₁, hf₁⟩ := powers_frame input tape L n n.size (initialized s) 0
    (initialized_ready s L n hpc hn hc hb hd) (by omega)
  have hb₁ := execute_sound _ (header_start_steps input tape L n s₁ hr₁)
  obtain ⟨s₂, h₂, hr₂, hf₂⟩ := headers_frame input tape L n n.size (headerStart s₁) 0
    (headerStart_ready L n s₁ hr₁) (by omega)
  have hb₂ := execute_sound _ (payload_start_steps input tape L n s₂ hr₂)
  obtain ⟨s₃, h₃, hr₃, hf₃⟩ := payloads_frame input tape L n n.size (payloadStart s₂)
    (payloadStart_ready L n s₂ hr₂) (by omega)
  let t : RAMState := {s₃ with pc := 36}
  have he : Steps (program.next input tape) 1 s₃ t := by
    apply execute_sound
    simp [execute, program, Machine.next, t, hr₃.pc, hr₃.count, hr₃.zero]
  have hf := (((((initialized_frame L n s).trans hf₁).trans
    (headerStart_frame L n s₁)).trans hf₂).trans (payloadStart_frame L n s₂ hr₂)).trans hf₃
  have hft : Frame L n s t := ⟨hf.words, hf.randomCursor, hf.output, hf.indexOutput, hf.indices⟩
  have hcursor : t.indices 6 = L.bufferAt n.size := by simpa [t] using hr₃.payloadCursor
  refine ⟨t, ?_, rfl, hr₃.length, hcursor, payloadReady_stored s₃ L n hr₃, hft⟩
  convert ((((((hi.trans h₁).trans hb₁).trans h₂).trans hb₂).trans h₃).trans he).terminates
    (Terminates.halt t (by simp [program, Machine.next, t])) using 1
  omega

/-- Caller metadata lives below all array banks and above the work frame. -/
theorem protected_metadata (L : Layout) (n i : ℕ) (hi : 11 ≤ i) (hi' : i < 256) :
    Protected L n i := by
  refine ⟨hi, ?_, ?_⟩
  · intro j _
    exact L.low_ne_cacheAt j i hi'
  · intro j _
    exact L.low_ne_bufferAt j i hi'

end Maxwell.Cost.RealNatCode
