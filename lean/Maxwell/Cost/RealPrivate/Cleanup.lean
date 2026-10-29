import Maxwell.Cost.RealPrivate.CleanupLoop

namespace Maxwell.Cost.RealPrivate.Cleanup
open RealSimulation.Control

def EmptyBank (origin : ℕ) (s : RAMState) : Prop :=
  ∀ a, s.words (slot origin 0 a)=0 ∧ s.indices (slot origin 0 a)=0

/-- The actual log traversal clears both typed source cells at each
recorded address. Repeated writes need no deduplication. The coverage
invariant discharges all addresses absent from the finite log. -/
theorem executes (input : RAMInput) (tape : ℕ→Bool) (origin : ℕ)
    (source : RAMState) (written : List ℕ) (s : Store)
    (h : Represents origin source written s.val) (covered : Covered source written) :
    ∃ t, Executes input tape RealPrivate.cleanup (37*written.length+5) s t ∧
      EmptyBank origin t.val ∧ Config origin written.length t.val ∧
      t.val.indices 9=written.length+1 ∧ Frame origin s.val t.val := by
  let a := s.put 9 1
  let b := putWord a 3 0
  have hn (bank index j : ℕ) (hj : j<256) : slot origin bank index≠j :=
    slot_ne_small h.high bank index j hj
  have bc : Config origin written.length b.val := by
    refine ⟨h.high,?_,?_,?_,?_,?_⟩
    · simpa [b,a,putWord,originRegister] using h.origin_word
    · simpa [b,a,putWord,zeroRegister] using h.zero
    · simpa [b,a,putWord,oneRegister] using h.one
    · simpa [b,a,putWord,logLength] using h.log_length
    · simp [b]
  have bf : Frame origin s.val b.val := by
    refine ⟨?_,?_,rfl,rfl,rfl⟩
    · intro j hj _
      simp [b,a,putWord,Store.put,hj]
    · intro j _ _ hj _ _
      simp [b,a,putWord,hj]
  have bl : LogTail origin 0 written.reverse b.val := by
    intro j hj
    have hh := h.log_cells j (by simpa using hj)
    simpa [b,a,putWord,hn,List.getElem?_eq_getElem hj] using hh
  obtain ⟨t,et,tc,ti,cleared,tf⟩ := loop_executes input tape origin 0 written.length written.reverse b bc
    (by simp) (by simp [b,a,putWord]) bl
  refine ⟨t,?_,?_,tc,ti,bf.trans tf⟩
  · have initReal : Executes input tape (realLiteral 3 0) 2 a b := by
      simpa only [Rat.cast_zero] using realLiteral_executes input tape a 3 0
    have erun := (literal_executes input tape s 9 1).seq (initReal.seq et)
    convert erun using 1 <;> first | rfl | simp only [List.length_reverse]; omega
  · intro address
    rw [cleared.words,cleared.indices]
    by_cases hm : address∈written
    · simp [hm]
    · have hc := covered address hm
      have hw : b.val.words (slot origin 0 address)=source.words address := by
        simpa [b,a,putWord,Store.put,hn] using h.words address
      have hi : b.val.indices (slot origin 0 address)=source.indices address := by
        simpa [b,a,putWord,hn] using h.indices address
      simp [hm,hw,hi,hc]

def program : Machine := RealPrivate.cleanup.compile

theorem run (input : RAMInput) (tape : ℕ→Bool) (origin : ℕ)
    (source : RAMState) (written : List ℕ) (s : Store)
    (h : Represents origin source written s.val) (covered : Covered source written) :
    ∃ t : Store, (runCapped (program.next input tape) (37*written.length+6) s.val).finished =
        some (t.place RealPrivate.cleanup.size) ∧
      (runCapped (program.next input tape) (37*written.length+6) s.val).instructions=37*written.length+5 ∧
      EmptyBank origin t.val ∧ Config origin written.length t.val ∧
      t.val.indices 9=written.length+1 ∧ Frame origin s.val t.val := by
  obtain ⟨t,et,ht,hc,hi,hf⟩ := executes input tape origin source written s h covered
  obtain ⟨hr,hcost⟩ := et.compiled_run (37*written.length+6) (by omega)
  exact ⟨t,hr,hcost,ht,hc,hi,hf⟩

end Maxwell.Cost.RealPrivate.Cleanup
