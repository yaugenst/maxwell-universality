import Maxwell.Cost.RealSimulation.BasicInstructions

namespace Maxwell.Cost.RealSimulation

open Control

namespace Initialization

/-- The caller supplies the encoded input and fresh dynamic storage. The finite
register and head frame is initialized by the compiled program below. -/
structure Entry (L : Layout) (origin center : ℕ) (bits : List Bool) (s : Store) : Prop where
  origin_above_frame : L.frameEnd ≤ origin
  origin_word : s.val.indices workspaceOrigin = origin
  stride_word : s.val.indices bankStride = L.stride
  center_word : s.val.indices headCenter = center
  input_base : s.val.indices inputBase = origin + L.inputBank
  input_length : s.val.indices inputLength = bits.length
  output_base : s.val.indices outputBase = origin + L.outputBank
  input_cells : ∀ j < bits.length,
    s.val.indices (L.slot origin L.inputBank j) = (bits[j]?.getD false).toNat
  memory_cells : ∀ a, s.val.indices (L.slot origin 0 a) = 0
  tape_cells : ∀ t < L.tapeCount, ∀ z : ℤ, -(center : ℤ) ≤ z →
    s.val.indices (L.slot origin (2 + t) (centered center z)) = 0
  random_cursor : s.val.randomCursor = 0

/-- The same entry contract at the current random-tape position. Initialization
never resets or advances that position. -/
structure EntryAt (L : Layout) (origin center : ℕ) (bits : List Bool)
    (randomBase : ℕ) (s : Store) : Prop where
  origin_above_frame : L.frameEnd ≤ origin
  origin_word : s.val.indices workspaceOrigin = origin
  stride_word : s.val.indices bankStride = L.stride
  center_word : s.val.indices headCenter = center
  input_base : s.val.indices inputBase = origin + L.inputBank
  input_length : s.val.indices inputLength = bits.length
  output_base : s.val.indices outputBase = origin + L.outputBank
  input_cells : ∀ j < bits.length,
    s.val.indices (L.slot origin L.inputBank j) = (bits[j]?.getD false).toNat
  memory_cells : ∀ a, s.val.indices (L.slot origin 0 a) = 0
  tape_cells : ∀ t < L.tapeCount, ∀ z : ℤ, -(center : ℤ) ≤ z →
    s.val.indices (L.slot origin (2 + t) (centered center z)) = 0
  random_cursor : s.val.randomCursor = randomBase

theorem Entry.atZero {L : Layout} {origin center : ℕ} {bits : List Bool} {s : Store}
    (h : Entry L origin center bits s) : EntryAt L origin center bits 0 s :=
  ⟨h.origin_above_frame, h.origin_word, h.stride_word, h.center_word,
    h.input_base, h.input_length, h.output_base, h.input_cells,
    h.memory_cells, h.tape_cells, h.random_cursor⟩

private abbrev Assignment := ℕ × Option ℕ

private def command (a : Assignment) : Code :=
  match a.2 with
  | some v => literal a.1 v
  | none => copy a.1 headCenter

private def applyAssignments (center : ℕ) : List Assignment → Store → Store
  | [], s => s
  | a :: rest, s => applyAssignments center rest (s.put a.1 (a.2.getD center))

private theorem applyAssignments_preserves (center : ℕ) (as : List Assignment) (s : Store)
    (j : ℕ) (h : ∀ a ∈ as, j ≠ a.1) :
    (applyAssignments center as s).val.indices j = s.val.indices j := by
  induction as generalizing s with
  | nil => rfl
  | cons a rest ih =>
    rw [applyAssignments, ih _ (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    simp [h a (by simp)]

private theorem applyAssignments_value (center : ℕ) (as : List Assignment) (s : Store)
    (j v : ℕ) (hex : ∃ a ∈ as, a.1 = j)
    (h : ∀ a ∈ as, a.1 = j → a.2.getD center = v) :
    (applyAssignments center as s).val.indices j = v := by
  induction as generalizing s with
  | nil => simp at hex
  | cons a rest ih =>
    by_cases he : ∃ b ∈ rest, b.1 = j
    · exact ih _ he (fun b hb => h b (List.mem_cons_of_mem _ hb))
    · have haj : a.1 = j := by
        rcases hex with ⟨b, hb, hj⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hj
        · exact (he ⟨b, hb, hj⟩).elim
      have hn : ∀ b ∈ rest, j ≠ b.1 := by
        intro b hb hj
        exact he ⟨b, hb, hj.symm⟩
      rw [applyAssignments, applyAssignments_preserves center rest _ j hn]
      simp [← haj, h a (by simp) haj]

private theorem applyAssignments_cursor (center : ℕ) (as : List Assignment) (s : Store) :
    (applyAssignments center as s).val.randomCursor = s.val.randomCursor := by
  induction as generalizing s with
  | nil => rfl
  | cons a rest ih => exact ih _

private theorem assignments_executes (input : RAMInput) (tape : ℕ → Bool)
    (center : ℕ) (as : List Assignment) (s : Store)
    (hc : s.val.indices headCenter = center)
    (hs : ∀ a ∈ as, headCenter ≠ a.1) :
    Executes input tape (sequence (as.map command))
      (if as = [] then 1 else 2 * as.length) s (applyAssignments center as s) := by
  induction as generalizing s with
  | nil => exact Executes.skip s
  | cons a rest ih =>
    have ha : Executes input tape (command a) 2 s (s.put a.1 (a.2.getD center)) := by
      cases he : a.2 with
      | none => simpa [command, he, hc] using copy_executes input tape s a.1 headCenter
      | some v => simpa [command, he] using literal_executes input tape s a.1 v
    have hc' : (s.put a.1 (a.2.getD center)).val.indices headCenter = center := by
      simpa [hs a (by simp)] using hc
    cases rest with
    | nil => simpa [sequence, applyAssignments] using ha
    | cons b rest =>
      have hr := ih _ hc' (fun d hd => hs d (List.mem_cons_of_mem _ hd))
      convert ha.seq hr using 1 <;> simp [sequence, applyAssignments, Nat.mul_add, Nat.add_assoc]
      omega

private def assignments (L : Layout) : List Assignment :=
  [(zeroRegister, some 0), (oneRegister, some 1), (activeRegister, some 1),
    (virtualPC, some 0), (addressLength, some 0), (outputLength, some 0), (inputHead, none)] ++
  (List.range L.registerCount).map (fun r => (L.bitRegister r, some 0)) ++
  (List.range L.tapeCount).map (fun t => (L.tapeHead t, none))

private theorem assignments_code (L : Layout) :
    sequence ((assignments L).map command) = initializeState L := by
  simp [assignments, List.map_append, List.map_map, command, initializeState, Function.comp_def]

private theorem assignments_center (L : Layout) :
    ∀ a ∈ assignments L, headCenter ≠ a.1 := by
  simp only [assignments, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range]
  intro a ha
  rcases ha with ((ha | ha | ha | ha | ha | ha | ha) | ⟨r, hr, ha⟩) | ⟨t, ht, ha⟩ <;>
    subst a <;> simp [headCenter, zeroRegister, oneRegister, activeRegister, virtualPC,
      addressLength, outputLength, inputHead, Layout.bitRegister, Layout.tapeHead] <;> omega

private theorem assignments_below (L : Layout) :
    ∀ a ∈ assignments L, a.1 < L.frameEnd := by
  simp only [assignments, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range]
  intro a ha
  rcases ha with ((ha | ha | ha | ha | ha | ha | ha) | ⟨r, hr, ha⟩) | ⟨t, ht, ha⟩ <;>
    subst a <;> simp only [zeroRegister, oneRegister, activeRegister, virtualPC,
      addressLength, outputLength, inputHead, Layout.bitRegister, Layout.tapeHead, Layout.frameEnd] <;>
    omega

private def initialValue (L : Layout) (center j : ℕ) : ℕ :=
  if j = oneRegister ∨ j = activeRegister then 1
  else if j = inputHead ∨ (256 + L.registerCount ≤ j ∧ j < L.frameEnd) then center else 0

private theorem assignments_value (L : Layout) (center : ℕ) :
    ∀ a ∈ assignments L, a.2.getD center = initialValue L center a.1 := by
  simp only [assignments, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range]
  intro a ha
  rcases ha with ((ha | ha | ha | ha | ha | ha | ha) | ⟨r, hr, ha⟩) | ⟨t, ht, ha⟩ <;>
    subst a <;> simp_all [initialValue,
      oneRegister, activeRegister, zeroRegister, virtualPC, addressLength, outputLength, inputHead,
      Layout.bitRegister, Layout.tapeHead, Layout.frameEnd] <;>
      first | omega | (split_ifs <;> omega)

private theorem assignments_metadata (L : Layout) (j : ℕ) (hlo : 128 ≤ j)
    (hhi : j ≤ 134) (hout : j ≠ outputLength) :
    ∀ a ∈ assignments L, j ≠ a.1 := by
  simp only [assignments, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range]
  intro a ha
  rcases ha with ((ha | ha | ha | ha | ha | ha | ha) | ⟨r, hr, ha⟩) | ⟨t, ht, ha⟩ <;>
    subst a <;> simp only [zeroRegister, oneRegister, activeRegister, virtualPC,
      addressLength, inputHead, Layout.bitRegister, Layout.tapeHead] <;> omega

end Initialization

/-- The existing finite prefix executes every literal/copy assignment and
establishes the complete initial simulation relation. -/
theorem initializeState_executes_at (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center randomBase : ℕ} {bits : List Bool}
    (s : Store) (h : Initialization.EntryAt L origin center bits randomBase s) :
    ∃ u, Executes input tape (initializeState L)
        (2 * (L.registerCount + L.tapeCount + 7)) s u ∧
      Ready L origin center bits {BitRAMState.initial with randomCursor := randomBase} u := by
  let u := Initialization.applyAssignments center (Initialization.assignments L) s
  have value (a : Initialization.Assignment) (ha : a ∈ Initialization.assignments L) :
      u.val.indices a.1 = a.2.getD center := by
    apply Initialization.applyAssignments_value center (Initialization.assignments L) s
      a.1 (a.2.getD center) ⟨a, ha, rfl⟩
    intro b hb he
    rw [Initialization.assignments_value L center b hb, he,
      ← Initialization.assignments_value L center a ha]
  have metadata (j : ℕ) (hlo : 128 ≤ j) (hhi : j ≤ 134) (hout : j ≠ outputLength) :
      u.val.indices j = s.val.indices j :=
    Initialization.applyAssignments_preserves center _ s j
      (Initialization.assignments_metadata L j hlo hhi hout)
  have bank (b a : ℕ) : u.val.indices (L.slot origin b a) = s.val.indices (L.slot origin b a) := by
    apply Initialization.applyAssignments_preserves
    intro v hv
    have := Initialization.assignments_below L v hv
    have := h.origin_above_frame.trans (L.slot_ge_origin origin b a)
    omega
  have he := Initialization.assignments_executes input tape center (Initialization.assignments L) s
    h.center_word (Initialization.assignments_center L)
  rw [Initialization.assignments_code] at he
  have he' : Executes input tape (initializeState L)
      (2 * (L.registerCount + L.tapeCount + 7)) s u := by
    convert he using 1
    simp [Initialization.assignments, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  refine ⟨u, he', ⟨⟨h.origin_above_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · exact value (virtualPC, some 0) (by simp [Initialization.assignments])
  · exact value (addressLength, some 0) (by simp [Initialization.assignments])
  · simpa [BitRAMState.initial, centered] using
      value (inputHead, none) (by simp [Initialization.assignments])
  · intro r hr
    apply value (L.bitRegister r, some 0)
    simp only [Initialization.assignments, List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩))
  · intro t ht
    have hv := value (L.tapeHead t, none)
      (show (L.tapeHead t, none) ∈ Initialization.assignments L from
        List.mem_append_right _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
    simpa [BitRAMState.initial, BitTape.blank, centered] using hv
  · exact (metadata workspaceOrigin (by decide) (by decide) (by decide)).trans h.origin_word
  · exact (metadata bankStride (by decide) (by decide) (by decide)).trans h.stride_word
  · exact (metadata headCenter (by decide) (by decide) (by decide)).trans h.center_word
  · exact (metadata inputBase (by decide) (by decide) (by decide)).trans h.input_base
  · exact (metadata inputLength (by decide) (by decide) (by decide)).trans h.input_length
  · exact (metadata outputBase (by decide) (by decide) (by decide)).trans h.output_base
  · exact value (outputLength, some 0) (by simp [Initialization.assignments])
  · intro j hj; exact (bank _ _).trans (h.input_cells j hj)
  · intro j hj; exact (Nat.not_lt_zero j hj).elim
  · intro j hj; exact (Nat.not_lt_zero j hj).elim
  · intro a; exact (bank _ _).trans (h.memory_cells a)
  · intro t ht z hz; exact (bank _ _).trans (h.tape_cells t ht z hz)
  · exact (Initialization.applyAssignments_cursor center _ s).trans h.random_cursor
  · exact value (zeroRegister, some 0) (by simp [Initialization.assignments])
  · exact value (oneRegister, some 1) (by simp [Initialization.assignments])
  · exact value (activeRegister, some 1) (by simp [Initialization.assignments])

theorem initializeState_executes (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool}
    (s : Store) (h : Initialization.Entry L origin center bits s) :
    ∃ u, Executes input tape (initializeState L)
        (2 * (L.registerCount + L.tapeCount + 7)) s u ∧
      Ready L origin center bits BitRAMState.initial u :=
  initializeState_executes_at input tape s h.atZero

end Maxwell.Cost.RealSimulation
