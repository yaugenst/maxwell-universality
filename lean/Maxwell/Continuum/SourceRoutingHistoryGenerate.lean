import Maxwell.Continuum.SourceRoutingHistoryCounter

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def generateCode : Code := .seq counterCode (.seq loopCode (.call (TapeOps.clear 1241)))
def generateCost {q : ℕ} (p : Plan q) : ℕ :=
  2^50*(p.bound+3)^2+loopCost p (2*q).bits.length+6*(2*q).bits.length+5

theorem generate_executes {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q)
    (fit : GeometrySort.Fits p.width initial) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : Runtime p initial 0 s) (blank : Blank s.val 1241) :
    ∃steps t,Executes input tape generateCode steps s t ∧ steps ≤ generateCost p ∧
      Runtime p initial (2*q) t ∧ Blank t.val 1241 ∧
      ArchiveFrame loopWork s.val t.val ∧ MemoryFrame p s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,ra,ac,f0,m0⟩:=counter_executes p initial input tape s state blank
  obtain ⟨origin,ho⟩:=ac
  obtain ⟨c1,b,word,e1,h1,rb,bword,hlen,f1,m1⟩:=loop_executes p initial fit input tape
    (2*q).bits origin (addressValue_bits _) a ra ho
  obtain ⟨t,et,ttapes,tf⟩:=WordCall.clear 1241 input tape word origin b bword
  have keept (j : ℕ) (hj : j≠1241) : t.val.tapes j=b.val.tapes j := by simp [ttapes,hj]
  have rt:=rb.counter_frame tf.2.2.1 keept
  have ft : ArchiveFrame loopWork b.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,fun j _ hj => keept j (by
      intro h;subst j;exact hj (by simp [loopWork]))⟩
  refine ⟨_,t,e0.seq (e1.seq et),?_,rt,⟨origin+word.length,by simp [ttapes]⟩,
    f0.trans (f1.trans ft),?_⟩
  · dsimp only [generateCost];omega
  · simpa only [tf.2.2.1,m0] using m1

theorem generate_history {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q)
    (fit : GeometrySort.Fits p.width initial) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : Runtime p initial 0 s) (blank : Blank s.val 1241) :
    ∃steps t,Executes input tape generateCode steps s t ∧ steps ≤ generateCost p ∧
      Runtime p initial (2*q) t ∧ Blank t.val 1241 ∧
      (∀j : Fin (2*q+1),BitArray.Represents t.val.memory (p.slab j.val) p.width
        (IncidenceEncoding.words p.width ((SortArrays.history initial (2*q)).get j))) ∧
      ArchiveFrame loopWork s.val t.val ∧ MemoryFrame p s.val.memory t.val.memory := by
  obtain ⟨steps,t,he,hc,rt,blankt,ft,mt⟩:=generate_executes p initial fit input tape s state blank
  exact ⟨steps,t,he,hc,rt,blankt,fun j => by
    simpa only [SortArrays.history_get] using rt.stored j.val (by have := j.isLt;omega),ft,mt⟩

theorem generateCost_polynomial {q : ℕ} (p : Plan q) :
    generateCost p ≤ 2^210*(q+1)^3*(p.bound+3)^2 := by
  have main:=loopCost_polynomial p
  have counterWidth:=Maxwell.Continuum.RationalWords.bits_mono (Nat.le_succ (2*q))
  change (2*q).bits.length ≤ (2*q+1).bits.length at counterWidth
  have width : (2*q).bits.length ≤ p.bound := by dsimp only [Plan.bound];omega
  have extra : 6*(2*q).bits.length+5 ≤ 8*(p.bound+3)^2 := by nlinarith
  have big : (p.bound+3)^2 ≤ (q+1)^3*(p.bound+3)^2 := Nat.le_mul_of_pos_left _ (by positivity)
  dsimp only [generateCost]
  nlinarith only [main,extra,big]

#print axioms generate_history
#print axioms generateCost_polynomial
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
