import Maxwell.Continuum.SourceRoutingPhaseLoop

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def generateCode : Code := .seq (.call (WordTransfer.clone 709 1240))
  (.seq loopCode (.call (TapeOps.clear 1240)))
def generateCost {q : ℕ} (p : Plan q) : ℕ := loopCost p p.width+21*p.width+23

theorem generate_executes {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q) (colors : RowColoring target)
    (initial : Fin 3→Vector (List Bool) (q*q)) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : Runtime p colors initial 0 s) (count : Word s.val 709 (q*q)) (blank : Blank s.val 1240) :
    ∃steps t,Executes input tape generateCode steps s t ∧ steps ≤ generateCost p ∧
      Runtime p colors initial (q*q) t ∧ Blank t.val 1240 ∧
      ArchiveFrame loopWork s.val t.val ∧ MemoryFrame p s.val.memory t.val.memory := by
  obtain ⟨co,hco⟩:=count
  obtain ⟨origin,ho⟩:=blank
  obtain ⟨a,ea,atapes,af⟩:=WordCall.clone 709 1240 (by decide) input tape (q*q).bits co origin s hco ho
  have keepa (j : ℕ) (hj : j≠1240) : a.val.tapes j=s.val.tapes j := by simp [atapes,hj]
  have ra:=state.counter_frame af.2.2.1 keepa
  have ac : a.val.tapes 1240=BitTape.shifted (q*q).bits origin := by simp [atapes]
  have fa : ArchiveFrame loopWork s.val a.val :=
    ⟨af.2.1,af.2.2.2.1,af.2.2.2.2.1,fun j _ hj => keepa j (by
      intro h;subst j;exact hj (by simp [loopWork]))⟩
  obtain ⟨cb,b,word,eb,hcb,rb,bword,hlen,fb,mb⟩:=loop_executes p colors initial input tape
    (q*q).bits origin (addressValue_bits _) a ra ac
  obtain ⟨t,et,ttapes,tf⟩:=WordCall.clear 1240 input tape word origin b bword
  have keept (j : ℕ) (hj : j≠1240) : t.val.tapes j=b.val.tapes j := by simp [ttapes,hj]
  have rt:=rb.counter_frame tf.2.2.1 keept
  have ft : ArchiveFrame loopWork b.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,fun j _ hj => keept j (by
      intro h;subst j;exact hj (by simp [loopWork]))⟩
  refine ⟨_,t,ea.seq (eb.seq et),?_,rt,⟨origin+word.length,by simp [ttapes]⟩,
    fa.trans (fb.trans ft),(MemoryFrame.of_eq p af.2.2.1).trans (mb.trans (MemoryFrame.of_eq p tf.2.2.1))⟩
  dsimp only [generateCost,Plan.width]
  omega

theorem generate_arrays {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q) (colors : RowColoring target)
    (initial : Fin 3→Vector (List Bool) (q*q)) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : Runtime p colors initial 0 s) (count : Word s.val 709 (q*q)) (blank : Blank s.val 1240) :
    ∃steps t,Executes input tape generateCode steps s t ∧ steps ≤ generateCost p ∧
      Runtime p colors initial (q*q) t ∧ Blank t.val 1240 ∧
      GeometryArrays.Stored t.val.memory p.base p.width
        ![IncidenceEncoding.words p.width (targets target),IncidenceEncoding.words p.width (labels colors),
          IncidenceEncoding.words p.width (PhaseKeys.first colors),
          IncidenceEncoding.words p.width (PhaseKeys.middle colors),
          IncidenceEncoding.words p.width (PhaseKeys.last colors)] ∧
      ArchiveFrame loopWork s.val t.val ∧ MemoryFrame p s.val.memory t.val.memory := by
  obtain ⟨steps,t,he,hc,rt,t1240,ft,mt⟩:=generate_executes p colors initial input tape s state count blank
  exact ⟨steps,t,he,hc,rt,t1240,by simpa only [arrays_complete] using rt.stored,ft,mt⟩

theorem generateCost_polynomial {q : ℕ} (p : Plan q) :
    generateCost p ≤ 2^116*(q*q+1)*(p.bound+3)^2 := by
  have main:=loopCost_polynomial p
  have width:=p.width_bound
  have extra : 21*p.width+23 ≤ 32*(p.bound+3)^2 := by nlinarith
  have big : (p.bound+3)^2 ≤ (q*q+1)*(p.bound+3)^2 := Nat.le_mul_of_pos_left _ (by omega)
  dsimp only [generateCost]
  nlinarith only [main,extra,big]

#print axioms generate_arrays
#print axioms generateCost_polynomial
end Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
