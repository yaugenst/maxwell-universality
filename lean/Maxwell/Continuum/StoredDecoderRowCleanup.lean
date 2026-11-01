import Maxwell.Continuum.StoredDecoderRowEmission

/-! Row temporaries are cleared by actual scans after emission. Repeated
rows keep the original word envelope instead of accumulating growth. -/
namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def outputList : List ℕ:=[228,229,4800,4803,4804,4805,4806,4807]
def cleanCode : Code:=.seq code (WordCleanup.code outputList)
def reset (v : ℕ→ℕ) (i : ℕ):=if i∈outputs then 0 else v i
def cleanCost (B H : ℕ):=emissionCost B H+8*(6*width B+4)+1

theorem reset_width (v : ℕ→ℕ) (B : ℕ) (bound : ∀i∈ids,(v i).bits.length≤B) :
    ∀i∈ids,(reset v i).bits.length≤B:=by
  intro i hi
  by_cases ho : i∈outputs
  · simp [reset,ho]
  · simpa only [reset,ite_eq_right ho] using bound i hi

theorem clean_emit (v : ℕ→ℕ) (B H : ℕ) (hB : 2≤B)
    (bound : ∀i∈ids,(v i).bits.length≤B)
    (positivePower : 0<v 144) (positiveScale : 0<v 4708)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val)
    (old : WordCleanup.Bounded RationalCanonical.workspace H s.val):
    ∃cost t,Executes input tape cleanCode cost s t ∧cost≤cleanCost B H ∧
      t.val.output=(bits v).reverse++s.val.output ∧
      NatAssign.Bank ids (reset v) t.val ∧NatAssign.Scratch t.val ∧
      (∀i∈RationalCanonical.workspace,Blank t.val i) ∧
      GeometryOutput.OutputFrame work s.val t.val:=by
  obtain ⟨c0,a,e0,h0,out,ba,sa,ra,fa⟩:=emit v B H hB bound positivePower positiveScale
    input tape s bank scratch old
  have wa : ∀i∈ids,(values v i).bits.length≤width B:=by
    intro i hi
    have hh:=NatAssign.values_width ids plan valid v B bound
      (fun a ha=>(literals a ha).trans hB) i hi
    change (values v i).bits.length+1≤width B at hh
    omega
  have oldA : WordCleanup.Bounded outputList (width B) a.val:=by
    intro i hi
    have mem : i∈ids:=(by decide : outputList.toFinset⊆ids) (by simpa using hi)
    exact ⟨(values v i).bits,wa i mem,ba i mem⟩
  obtain ⟨c1,t,e1,h1,blank,frame⟩:=WordCleanup.executes outputList (width B) input tape a oldA
  have finalBank : NatAssign.Bank ids (reset v) t.val:=by
    intro i hi
    by_cases ho : i∈outputs
    · rw [reset,ite_eq_left ho]
      exact (zero_word_iff_blank _ _).mpr (blank i (by simpa [outputs,outputList] using ho))
    · rw [reset,ite_eq_right ho,←kept v i ho]
      exact word_of_eq (frame.tapes i (by simpa [outputList,outputs] using ho)) (ba i hi)
  have finalScratch : NatAssign.Scratch t.val:=by
    intro i hi
    exact blank_of_eq (frame.tapes i (by simp only [outputList,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false];omega))
      (sa i hi)
  refine ⟨c0+c1,t,e0.seq e1,by change c1≤8*(6*width B+4)+1 at h1; unfold cleanCost;omega,
    frame.output.trans out,finalBank,finalScratch,?_,?_⟩
  · intro i hi
    apply blank_of_eq (frame.tapes i ?_) (ra.workspace_blank i hi)
    have hd : Disjoint RationalCanonical.workspace.toFinset outputList.toFinset:=by decide
    exact fun ho=>Finset.disjoint_left.mp hd (by simpa using hi) ho
  · refine ⟨frame.memory.trans fa.memory,frame.inputHead.trans fa.inputHead,
      frame.randomCursor.trans fa.randomCursor,?_⟩
    intro i hi
    exact (frame.tapes i (fun hm=>hi ((by decide : outputList.toFinset⊆work) hm))).trans (fa.tapes i hi)

#print axioms clean_emit
end Maxwell.Continuum.DecoderRow
