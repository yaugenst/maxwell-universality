import Maxwell.Continuum.RationalDataflowStoredParts
import Maxwell.Continuum.RuntimeCounterClear

/-! Reusable, charged cleanup of a saved three-channel rational word. -/
namespace Maxwell.Continuum.RationalDataflow.StoredParts
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 1000000

def clearCode (base : ℕ) : Code :=
  .seq (.call (TapeOps.clear base))
    (.seq (.call (TapeOps.clear (base+1))) (.call (TapeOps.clear (base+2))))

theorem clear_executes (base : ℕ) (x : Parts) (B : ℕ) (hx : x.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Stored base x s.val) :
    ∃cost t,Executes input tape (clearCode base) cost s t ∧ cost≤18*B+12 ∧
      (∀i∈ports base,Blank t.val i) ∧ BinaryPrecision.Frame (ports base) s.val t.val := by
  obtain ⟨op,hp⟩ := hs.1
  obtain ⟨s1,e1,z1,f1⟩ := RuntimeCounter.clear_executes base input tape x.positive.bits op s hp
  have wn : Word s1.val (base+1) x.negative := word_of_eq
    (f1.tapes _ (by simp)) hs.2.1
  obtain ⟨on,hn⟩ := wn
  obtain ⟨s2,e2,z2,f2⟩ := RuntimeCounter.clear_executes (base+1) input tape x.negative.bits on s1 hn
  have wd : Word s2.val (base+2) x.denominator := word_of_eq
    (f2.tapes _ (by simp)) (word_of_eq (f1.tapes _ (by simp)) hs.2.2)
  obtain ⟨od,hd⟩ := wd
  obtain ⟨t,e3,z3,f3⟩ := RuntimeCounter.clear_executes (base+2) input tape x.denominator.bits od s2 hd
  refine ⟨_,t,e1.seq (e2.seq e3),?_,?_,
    (f1.mono (by simp [ports])).trans ((f2.mono (by simp [ports])).trans (f3.mono (by simp [ports])))⟩
  · rcases hx with ⟨hp,hn,hd⟩
    omega
  · intro i hi
    simp only [ports,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · exact blank_of_eq (f3.tapes _ (by simp)) (blank_of_eq (f2.tapes _ (by simp)) z1)
    · exact blank_of_eq (f3.tapes _ (by simp)) z2
    · exact z3

#print axioms clear_executes
end Maxwell.Continuum.RationalDataflow.StoredParts
