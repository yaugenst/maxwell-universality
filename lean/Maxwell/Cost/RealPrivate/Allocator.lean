import Maxwell.Cost.RealPrivate.Layout

namespace Maxwell.Cost.RealPrivate.Allocator
open RealSimulation.Control

def body : Code := .seq (add originRegister originRegister originRegister) (subtract 0 0 3)
def loop : Code := .loop 3 0 body
def code : Code := .seq (literal 3 1) (.seq (literal originRegister 1) loop)
def program : Machine := code.compile

structure Frame (s t : RAMState) : Prop where
  words : t.words=s.words
  indices : ∀ i, i≠0 → i≠3 → i≠originRegister → t.indices i=s.indices i
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  indexOutput : t.indexOutput=s.indexOutput

theorem Frame.refl (s : RAMState) : Frame s s := ⟨rfl,by intros; rfl,rfl,rfl,rfl⟩

theorem Frame.trans {s t u : RAMState} (a : Frame s t) (b : Frame t u) : Frame s u :=
  ⟨b.words.trans a.words,fun i h0 h3 hG => (b.indices i h0 h3 hG).trans (a.indices i h0 h3 hG),
    b.randomCursor.trans a.randomCursor,b.output.trans a.output,b.indexOutput.trans a.indexOutput⟩

theorem Frame.put (s : Store) (r v : ℕ) (hr : r=0 ∨ r=3 ∨ r=originRegister) :
    Frame s.val (s.put r v).val := by
  refine ⟨rfl,?_,rfl,rfl,rfl⟩
  intro i h0 h3 hG
  have hi : i≠r := by rcases hr with rfl | rfl | rfl <;> assumption
  simp [hi]

theorem loop_executes (input : RAMInput) (tape : ℕ→Bool) (remaining value : ℕ)
    (s : Store) (hremaining : s.val.indices 0=remaining) (hone : s.val.indices 3=1)
    (hvalue : s.val.indices originRegister=value) :
    ∃ t, Executes input tape loop (5*remaining+1) s t ∧
      t.val.indices originRegister=value*2^remaining ∧ t.val.indices 0=0 ∧
      t.val.indices 3=1 ∧ Frame s.val t.val := by
  induction remaining generalizing value s with
  | zero =>
    refine ⟨s,Executes.done (by rw [hone,hremaining]; omega),?_,hremaining,hone,Frame.refl _⟩
    simpa using hvalue
  | succ remaining ih =>
    let a := s.put originRegister (value+value)
    let b := a.put 0 remaining
    have ea : Executes input tape (add originRegister originRegister originRegister) 2 s a := by
      simpa only [hvalue] using add_executes input tape s originRegister originRegister originRegister
    have eb : Executes input tape (subtract 0 0 3) 2 a b := by
      simpa [a,b,originRegister,hremaining,hone] using subtract_executes input tape a 0 0 3
    obtain ⟨t,et,tvalue,tzero,tone,tf⟩ := ih (value+value) b
      (by simp [b]) (by simp [b,a,originRegister,hone]) (by simp [b,a,originRegister])
    refine ⟨t,?_,?_,tzero,tone,?_⟩
    · have h := Executes.more (body := body) (by rw [hone,hremaining]; omega) (ea.seq eb) et
      convert h using 1 <;> first | rfl | omega
    · rw [tvalue,pow_succ]
      ring
    · exact ((Frame.put s originRegister (value+value) (by simp)).trans
        (Frame.put a 0 remaining (by simp))).trans tf

/-- The fresh-bank origin is computed by the fixed finite doubling loop.
Every initialization, arithmetic instruction and loop test is charged. -/
theorem executes (input : RAMInput) (tape : ℕ→Bool) (width : ℕ)
    (s : Store) (hwidth : s.val.indices 0=width) :
    ∃ t, Executes input tape code (5*width+5) s t ∧
      t.val.indices originRegister=2^width ∧ t.val.indices 0=0 ∧
      t.val.indices 3=1 ∧ Frame s.val t.val := by
  let a := s.put 3 1
  let b := a.put originRegister 1
  obtain ⟨t,et,tvalue,tzero,tone,tf⟩ := loop_executes input tape width 1 b
    (by simp [b,a,originRegister,hwidth]) (by simp [b,a,originRegister]) (by simp [b])
  refine ⟨t,?_,by simpa using tvalue,tzero,tone,?_⟩
  · have h := (literal_executes input tape s 3 1).seq
      ((literal_executes input tape a originRegister 1).seq et)
    convert h using 1 <;> first | rfl | omega
  · exact ((Frame.put s 3 1 (by simp)).trans (Frame.put a originRegister 1 (by simp))).trans tf

theorem run (input : RAMInput) (tape : ℕ→Bool) (width : ℕ)
    (s : Store) (hwidth : s.val.indices 0=width) :
    ∃ t : Store, (runCapped (program.next input tape) (5*width+6) s.val).finished =
        some (t.place code.size) ∧
      (runCapped (program.next input tape) (5*width+6) s.val).instructions=5*width+5 ∧
      t.val.indices originRegister=2^width ∧ t.val.indices 0=0 ∧
      t.val.indices 3=1 ∧ Frame s.val t.val := by
  obtain ⟨t,et,hG,h0,h3,hf⟩ := executes input tape width s hwidth
  obtain ⟨hr,hc⟩ := et.compiled_run (5*width+6) (by omega)
  exact ⟨t,hr,hc,hG,h0,h3,hf⟩

end Maxwell.Cost.RealPrivate.Allocator
