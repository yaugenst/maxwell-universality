import Maxwell.Cost.RationalCanonical.Correctness
import Maxwell.Cost.Structured.WordCleanup

/-! Runtime fractions can be serialized after charged cleanup of measured
workspace words. The caller supplies the computed numerator and denominator,
not a prepared Euclidean-machine state. -/
namespace Maxwell.Cost.RationalCanonical
open Structured RationalAccumulator
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def workspace : List ℕ := [0,1,2,3,4,220,221,222,223,230,231]

def preparedCode : Code := .seq (WordCleanup.code workspace) code

theorem NormalizeReady.workspace_blank {s : BitRAMState} {a b : ℕ}
    (h : NormalizeReady s a b) : ∀i∈workspace,Blank s i:=by
  intro i hi
  simp only [workspace,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.work.scratch 0 (by decide)
  · exact h.work.scratch 1 (by decide)
  · exact h.work.scratch 2 (by decide)
  · exact h.work.scratch 3 (by decide)
  · exact h.work.scratch 4 (by decide)
  · exact (zero_word_iff_blank _ _).mp h.work.first
  · exact (zero_word_iff_blank _ _).mp h.work.second
  · exact h.work.quotient
  · exact h.work.remainder
  · exact h.outputNumerator
  · exact h.outputDenominator

theorem prepares (input : List Bool) (tape : ℕ→Bool) (a b B : ℕ) (s : Store)
    (num : Word s.val 228 a) (den : Word s.val 229 b)
    (old : WordCleanup.Bounded workspace B s.val) :
    ∃cost t,Executes input tape (WordCleanup.code workspace) cost s t ∧
      cost≤11*(6*B+4)+1 ∧ NormalizeReady t.val a b ∧
      BinaryPrecision.Frame workspace.toFinset s.val t.val := by
  obtain ⟨cost,t,ex,hc,blank,frame⟩:=WordCleanup.executes workspace B input tape s old
  refine ⟨cost,t,ex,hc,?_,frame⟩
  refine ⟨word_of_eq (frame.tapes 228 (by decide)) num,
    word_of_eq (frame.tapes 229 (by decide)) den,
    ⟨(zero_word_iff_blank _ _).mpr (blank 220 (by decide)),
     (zero_word_iff_blank _ _).mpr (blank 221 (by decide)),
     blank 222 (by decide),blank 223 (by decide),?_⟩,
    blank 230 (by decide),blank 231 (by decide)⟩
  intro i hi
  exact blank i (by unfold workspace; simp only [List.mem_cons]; omega)

theorem prepared_executes (input : List Bool) (tape : ℕ→Bool) (negative : Bool)
    (a b B : ℕ) (hb : 0<b) (s : Store)
    (num : Word s.val 228 a) (den : Word s.val 229 b)
    (old : WordCleanup.Bounded workspace B s.val)
    (sign : s.val.registers 23=negative) :
    ∃cost t,Executes input tape preparedCode cost s t ∧
      cost≤11*(6*B+4)+1+costBound a b ∧
      t.val.output=(Codec.rat (value negative a b)).reverse++s.val.output ∧
      NormalizeReady t.val a b ∧ EmitFrame s.val t.val := by
  obtain ⟨c,u,ex,hc,ready,frame⟩:=prepares input tape a b B s num den old
  have signU : u.val.registers 23=negative:=
    (ex.protectsRegister 23 (WordCleanup.code_register _ _ (by decide) (by decide))).trans sign
  obtain ⟨d,t,hd,ed,out,rt,ft⟩:=executes input tape negative a b hb u ready signU
  have fu : EmitFrame s.val u.val:=by
    refine ⟨frame.address,frame.memory,frame.inputHead,frame.randomCursor,?_,?_⟩
    · intro i hi
      apply frame.tapes i
      exact fun hm=>hi ((by decide : workspace.toFinset ⊆
        ({0,1,2,3,4,220,221,222,223,228,229,230,231}:Finset ℕ)) hm)
    · intro i _ _ _ _ h26 h27 _ _ _
      exact ex.protectsRegister i (WordCleanup.code_register _ _ h26 h27)
  exact ⟨c+d,t,ex.seq ed,by omega,by rw [out,frame.output],rt,fu.trans ft⟩

#print axioms prepared_executes
end Maxwell.Cost.RationalCanonical
