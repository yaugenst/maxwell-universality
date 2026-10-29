import Maxwell.Cost.PhysicalEmit.Controls

namespace Maxwell.Cost.PhysicalEmit
open Structured RationalAccumulator

/-- Earlier coordinates and countdowns are exactly preserved by an inner
traversal; all dimensions are immutable runtime words. -/
structure Held (start : ℕ) (s t : BitRAMState) : Prop where
  dimensions : ∀ a, t.tapes (dimensionTape a) = s.tapes (dimensionTape a)
  coordinates : ∀ a, a.val < start → t.tapes (coordinateTape a) = s.tapes (coordinateTape a)
  counters : ∀ a, a.val < start → t.tapes (counterTape a) = s.tapes (counterTape a)

theorem Held.refl (start : ℕ) (s : BitRAMState) : Held start s s :=
  ⟨fun _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩
theorem Held.trans {start : ℕ} {s t u : BitRAMState} (h : Held start s t) (k : Held start t u) :
    Held start s u :=
  ⟨fun a => (k.dimensions a).trans (h.dimensions a),
    fun a ha => (k.coordinates a ha).trans (h.coordinates a ha),
    fun a ha => (k.counters a ha).trans (h.counters a ha)⟩
theorem Held.mono {start finish : ℕ} {s t : BitRAMState} (h : Held finish s t)
    (hle : start ≤ finish) : Held start s t :=
  ⟨h.dimensions,fun a ha => h.coordinates a (ha.trans_le hle),
    fun a ha => h.counters a (ha.trans_le hle)⟩

def loopTapes : Finset ℕ := {240,241,242,253,254,255}

theorem axis_subset (a : Axis) : {counterTape a,coordinateTape a} ⊆ loopTapes := by
  fin_cases a <;> decide

theorem Held.of_frame (a : Axis) {s t : BitRAMState}
    (hf : LoopFrame {counterTape a,coordinateTape a} s t) : Held a.val s t := by
  refine ⟨?_,?_,?_⟩
  · intro i
    apply hf.tapes
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or,dimensionTape,counterTape,coordinateTape]
    have := a.isLt; have := i.isLt; omega
  · intro i hi
    apply hf.tapes
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or,counterTape,coordinateTape]
    have := a.isLt; have := i.isLt; omega
  · intro i hi
    apply hf.tapes
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or,counterTape,coordinateTape]
    have := a.isLt; have := i.isLt; omega

def nestedCode (start : ℕ) : ℕ → Code → Code
  | 0, body => body
  | fuel+1, body => if h : start < 3 then
      axisCode ⟨start,h⟩ (nestedCode (start+1) fuel body) else body

def nestedRecords (N : Axis → ℕ) (records : (Axis → ℕ) → List Bool) (start : ℕ) :
    ℕ → (Axis → ℕ) → List Bool
  | 0, coords => records coords
  | fuel+1, coords => if h : start < 3 then
      recordPrefix (fun i => nestedRecords N records (start+1) fuel (Function.update coords ⟨start,h⟩ i))
        (N ⟨start,h⟩) else records coords

def nestedBudget (N : Axis → ℕ) (B Q start : ℕ) : ℕ → ℕ
  | 0 => Q
  | fuel+1 => if h : start < 3 then
      (N ⟨start,h⟩+1)*(nestedBudget N B Q (start+1) fuel+52*B+58) else Q

/-- The nested loops supply every coordinate to one fixed finite body in
lexicographic order. The dimensions, counters, and coordinates are all
actual machine tapes throughout the execution. -/
theorem nested (N : Axis → ℕ) (B Q : ℕ) (hB : ∀ a, (N a).bits.length ≤ B)
    (body : Code) (input : List Bool) (tape : ℕ → Bool)
    (R : Store → Prop) (records : (Axis → ℕ) → List Bool)
    (stable : ∀ s t, LoopFrame loopTapes s.val t.val → R s → R t)
    (bodyCorrect : ∀ coords, (∀ a, coords a < N a) → ∀ s, R s → LowerReady 3 N B s.val →
      (∀ a, Word s.val (coordinateTape a) (coords a)) →
      ∃ cost t, cost ≤ Q ∧ Executes input tape body cost s t ∧ R t ∧ Held 3 s.val t.val ∧
        t.val.output = (records coords).reverse ++ s.val.output)
    (fuel start : ℕ) (hdepth : start+fuel=3) (coords : Axis → ℕ)
    (hcoords : ∀ a, a.val < start → coords a < N a)
    (s : Store) (hs : R s) (hr : LowerReady start N B s.val)
    (hp : ∀ a, a.val < start → Word s.val (coordinateTape a) (coords a)) :
    ∃ cost t, cost ≤ nestedBudget N B Q start fuel ∧
      Executes input tape (nestedCode start fuel body) cost s t ∧ R t ∧
      LowerReady start N B t.val ∧ Held start s.val t.val ∧
      t.val.output = (nestedRecords N records start fuel coords).reverse ++ s.val.output := by
  induction fuel generalizing start coords s with
  | zero =>
    have hstart : start=3 := by omega
    subst start
    obtain ⟨c,t,hc,he,hR,hheld,ho⟩ := bodyCorrect coords (fun a => hcoords a a.isLt) s hs hr
      (fun a => hp a a.isLt)
    refine ⟨c,t,hc,he,hR,?_,hheld,ho⟩
    refine ⟨fun a => word_of_eq (hheld.dimensions a) (hr.dimensions a),?_,?_⟩
    · intro a ha; have := a.isLt; omega
    · intro a ha; have := a.isLt; omega
  | succ fuel ih =>
    have hstart : start < 3 := by omega
    let a : Axis := ⟨start,hstart⟩
    let P : Store → Prop := fun t => R t ∧ Held start s.val t.val
    have hstable : ∀ u v, LoopFrame {counterTape a,coordinateTape a} u.val v.val → P u → P v := by
      intro u v hf hP
      exact ⟨stable u v (hf.mono (axis_subset a)) hP.1,hP.2.trans (Held.of_frame a hf)⟩
    have hbody : ∀ i, i < N a → ∀ u, P u → LowerReady (a.val+1) N B u.val →
        Word u.val (coordinateTape a) i →
        ∃ cost t, cost ≤ nestedBudget N B Q (start+1) fuel ∧
          Executes input tape (nestedCode (start+1) fuel body) cost u t ∧ P t ∧
          LowerReady (a.val+1) N B t.val ∧
          t.val.output = (nestedRecords N records (start+1) fuel (Function.update coords a i)).reverse ++ u.val.output ∧
          t.val.tapes (coordinateTape a) = u.val.tapes (coordinateTape a) ∧
          t.val.tapes (counterTape a) = u.val.tapes (counterTape a) := by
      intro i hi u hP hru hwu
      have hcs : ∀ j : Axis, j.val < start+1 → (Function.update coords a i) j < N j := by
        intro j hj
        by_cases he : j=a
        · subst j; simpa using hi
        · have hjval : j.val < start := by
            have hne : j.val ≠ start := fun h => he (Fin.ext h)
            omega
          simpa only [Function.update_of_ne he] using hcoords j hjval
      have hps : ∀ j : Axis, j.val < start+1 → Word u.val (coordinateTape j) ((Function.update coords a i) j) := by
        intro j hj
        by_cases he : j=a
        · subst j; simpa using hwu
        · have hjval : j.val < start := by
            have hne : j.val ≠ start := fun h => he (Fin.ext h)
            omega
          exact (Function.update_of_ne he i coords) ▸ word_of_eq (hP.2.coordinates j hjval) (hp j hjval)
      obtain ⟨c,t,hc,he,hR,hrt,hht,ho⟩ := ih (start+1) (by omega)
        (Function.update coords a i) hcs u hP.1 hru hps
      exact ⟨c,t,hc,he,⟨hR,hP.2.trans (hht.mono (by omega))⟩,hrt,ho,
        hht.coordinates a (by simp [a]),hht.counters a (by simp [a])⟩
    obtain ⟨c,t,hc,he,hP,hrt,ho,_⟩ := axis_records a N B (hB a)
      (nestedCode (start+1) fuel body) input tape P
      (fun i => nestedRecords N records (start+1) fuel (Function.update coords a i))
      (nestedBudget N B Q (start+1) fuel) hstable hbody s ⟨hs,Held.refl _ _⟩ hr
    refine ⟨c,t,?_,?_,hP.1,hrt,hP.2,?_⟩
    · simpa only [nestedBudget,dite_eq_left hstart] using hc
    · simpa only [nestedCode,dite_eq_left hstart] using he
    · simpa only [nestedRecords,dite_eq_left hstart] using ho

end Maxwell.Cost.PhysicalEmit
