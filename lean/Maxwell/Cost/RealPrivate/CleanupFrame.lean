import Maxwell.Cost.RealPrivate.CleanupStep
import Maxwell.Cost.RealPrivate.CallerFrame

namespace Maxwell.Cost.RealPrivate.Cleanup
open RealSimulation.Control

/-- Cleanup touches only its four index scratch registers, real scratch3,
and the represented source memory. Output and log banks are retained. -/
structure Frame (origin : ℕ) (s t : RAMState) : Prop where
  words : ∀ j, j≠3 → (∀ a, j≠slot origin 0 a) → t.words j=s.words j
  indices : ∀ j, j≠0 → j≠2 → j≠9 → j≠10 →
    (∀ a, j≠slot origin 0 a) → t.indices j=s.indices j
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  indexOutput : t.indexOutput=s.indexOutput

theorem Frame.refl (origin : ℕ) (s : RAMState) : Frame origin s s :=
  ⟨by intros; rfl,by intros; rfl,rfl,rfl,rfl⟩

theorem Frame.trans {origin : ℕ} {s t u : RAMState}
    (h : Frame origin s t) (h' : Frame origin t u) : Frame origin s u :=
  ⟨fun j h3 hb => (h'.words j h3 hb).trans (h.words j h3 hb),
    fun j h0 h2 h9 h10 hb => (h'.indices j h0 h2 h9 h10 hb).trans (h.indices j h0 h2 h9 h10 hb),
    h'.randomCursor.trans h.randomCursor,h'.output.trans h.output,h'.indexOutput.trans h.indexOutput⟩

theorem Frame.caller {origin : ℕ} {s t : RAMState} (h : Frame origin s t) :
    CallerFrame origin s t := by
  have hn (j : ℕ) (hj : j<origin) (a : ℕ) : j≠slot origin 0 a := by
    have := slot_ge_origin origin 0 a
    omega
  exact ⟨fun j hj ho => h.words j (by omega) (hn j ho),
    fun j hj ho _ => h.indices j (by omega) (by omega) (by omega) (by omega) (hn j ho),
    h.output,h.indexOutput⟩

theorem Frame.index_bank {origin : ℕ} {s t : RAMState} (h : Frame origin s t)
    (high : 256≤origin) (bank : ℕ) (hb : bank<4) (hne : bank≠0) (a : ℕ) :
    t.indices (slot origin bank a)=s.indices (slot origin bank a) := by
  exact h.indices _ (slot_ne_small high bank a 0 (by decide))
    (slot_ne_small high bank a 2 (by decide)) (slot_ne_small high bank a 9 (by decide))
    (slot_ne_small high bank a 10 (by decide))
    (fun _ => slot_different hb (by decide) hne)

theorem Frame.word_bank {origin : ℕ} {s t : RAMState} (h : Frame origin s t)
    (high : 256≤origin) (bank : ℕ) (hb : bank<4) (hne : bank≠0) (a : ℕ) :
    t.words (slot origin bank a)=s.words (slot origin bank a) :=
  h.words _ (slot_ne_small high bank a 3 (by decide)) (fun _ => slot_different hb (by decide) hne)

theorem step_frame (s : Store) (origin index address : ℕ) :
    Frame origin s.val (stepState s origin index address).val := by
  refine ⟨?_,?_,rfl,rfl,rfl⟩
  · intro j _ hj
    simp [stepState,putWord,Store.put,hj address]
  · intro j h0 h2 h9 h10 hj
    simp [stepState,putWord,Store.put,coordinateRegister,pointerRegister,
      h0,h2,h9,h10,hj address]

theorem step_words (s : Store) (origin index address a : ℕ) :
    (stepState s origin index address).val.words (slot origin 0 a)=
      if a=address then 0 else s.val.words (slot origin 0 a) := by
  simp [stepState,putWord,Store.put,Function.update_apply]

theorem step_indices (s : Store) (origin index address a : ℕ) (high : 256≤origin) :
    (stepState s origin index address).val.indices (slot origin 0 a)=
      if a=address then 0 else s.val.indices (slot origin 0 a) := by
  have hn (j : ℕ) (hj : j<256) := slot_ne_small high 0 a j hj
  simp [stepState,putWord,Store.put,Function.update_apply,coordinateRegister,pointerRegister,hn]

structure Config (origin total : ℕ) (s : RAMState) : Prop where
  high : 256≤origin
  origin_word : s.indices originRegister=origin
  zero : s.indices zeroRegister=0
  one : s.indices oneRegister=1
  length : s.indices logLength=total
  realZero : s.words 3=0

theorem step_config {origin total : ℕ} {s : Store} (h : Config origin total s.val)
    (index address : ℕ) : Config origin total (stepState s origin index address).val := by
  have hn (j : ℕ) (hj : j<256) : j≠slot origin 0 address :=
    (slot_ne_small h.high 0 address j hj).symm
  refine ⟨h.high,?_,?_,?_,?_,?_⟩
  · simpa [stepState,putWord,hn,originRegister,coordinateRegister,pointerRegister] using h.origin_word
  · simpa [stepState,putWord,hn,zeroRegister,coordinateRegister,pointerRegister] using h.zero
  · simpa [stepState,putWord,hn,oneRegister,coordinateRegister,pointerRegister] using h.one
  · simpa [stepState,putWord,hn,logLength,coordinateRegister,pointerRegister] using h.length
  · simpa [stepState,putWord,Store.put,Function.update_apply,hn] using h.realZero

@[simp] theorem step_cursor (s : Store) (origin index address : ℕ) :
    (stepState s origin index address).val.indices 9=index+2 := by simp [stepState]

end Maxwell.Cost.RealPrivate.Cleanup
