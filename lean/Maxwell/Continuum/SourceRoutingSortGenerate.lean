import Maxwell.Continuum.SourceRoutingSortLoop

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def generateCode : Code := .seq (.call (WordTransfer.clone 709 1240))
  (.seq loopCode (.call (TapeOps.clear 1240)))
def generateCost {q : ℕ} (p : Plan q) (round : ℕ) : ℕ := loopCost p round p.width+21*p.width+23

theorem generate_executes {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (initial : Vector (List Bool) (q*q))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : Runtime p round saved initial 0 s) (count : Word s.val 709 (q*q)) (blank : Blank s.val 1240) :
    ∃steps t,Executes input tape generateCode steps s t ∧ steps ≤ generateCost p round ∧
      Runtime p round saved initial (q*q) t ∧ Blank t.val 1240 ∧
      ArchiveFrame loopWork s.val t.val ∧ Tree.Memory.Frame p.destination (q*q*p.width) s.val.memory t.val.memory := by
  obtain ⟨co,hco⟩:=count
  obtain ⟨origin,ho⟩:=blank
  obtain ⟨a,ea,atapes,af⟩:=WordCall.clone 709 1240 (by decide) input tape (q*q).bits co origin s hco ho
  have keepa (j : ℕ) (hj : j≠1240) : a.val.tapes j=s.val.tapes j := by simp [atapes,hj]
  have ra:=state.counter_frame af.2.2.1 keepa
  have ac : a.val.tapes 1240=BitTape.shifted (q*q).bits origin := by simp [atapes]
  have fa : ArchiveFrame loopWork s.val a.val :=
    ⟨af.2.1,af.2.2.2.1,af.2.2.2.2.1,fun j _ hj => keepa j (by
      intro h;subst j;exact hj (by simp [loopWork]))⟩
  obtain ⟨cb,b,word,eb,hcb,rb,bword,hlen,fb,mb⟩:=loop_executes p round saved fit initial input tape
    (q*q).bits origin (addressValue_bits _) a ra ac
  obtain ⟨t,et,ttapes,tf⟩:=WordCall.clear 1240 input tape word origin b bword
  have keept (j : ℕ) (hj : j≠1240) : t.val.tapes j=b.val.tapes j := by simp [ttapes,hj]
  have rt:=rb.counter_frame tf.2.2.1 keept
  have ft : ArchiveFrame loopWork b.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,fun j _ hj => keept j (by
      intro h;subst j;exact hj (by simp [loopWork]))⟩
  refine ⟨_,t,ea.seq (eb.seq et),?_,rt,⟨origin+word.length,by simp [ttapes]⟩,
    fa.trans (fb.trans ft),?_⟩
  · dsimp only [generateCost,Plan.width]
    omega
  · simpa only [tf.2.2.1,af.2.2.1] using mb

theorem generate_keys {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (seed p round 0) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (metadata : Metadata p s.val)
    (source : BitArray.Represents s.val.memory p.source p.width (IncidenceEncoding.words p.width saved))
    (count : Word s.val 709 (q*q)) (blank : Blank s.val 1240) :
    ∃steps t,Executes input tape generateCode steps s t ∧ steps ≤ generateCost p round ∧
      NatAssign.Bank GeometryArithmetic.ids (seed p round (q*q)) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ Metadata p t.val ∧ Blank t.val 1240 ∧
      BitArray.Represents t.val.memory p.source p.width (IncidenceEncoding.words p.width saved) ∧
      BitArray.Represents t.val.memory p.destination p.width (IncidenceEncoding.words p.width (SortArrays.step round saved)) ∧
      ArchiveFrame loopWork s.val t.val ∧ Tree.Memory.Frame p.destination (q*q*p.width) s.val.memory t.val.memory := by
  let initial:=GeometryArray.snapshot s.val.memory p.destination p.width (q*q)
  have state : Runtime p round saved initial 0 s :=
    ⟨Nat.zero_le _,bank,ready,privateBlank,metadata,source,GeometryArray.snapshot_represents _ _ _ _⟩
  obtain ⟨steps,t,he,hc,rt,t1240,ft,mt⟩:=generate_executes p round saved fit initial input tape s state count blank
  exact ⟨steps,t,he,hc,rt.bank,rt.ready,rt.privateBlank,rt.metadata,t1240,rt.source,rt.complete,ft,mt⟩

theorem generateCost_polynomial {q : ℕ} (p : Plan q) (round : ℕ) :
    generateCost p round ≤ 2^204*(q*q+1)*(p.bound round+3)^2 := by
  have main:=loopCost_polynomial p round
  have width:=p.width_bound round
  have extra : 21*p.width+23 ≤ 32*(p.bound round+3)^2 := by nlinarith
  have big : (p.bound round+3)^2 ≤ (q*q+1)*(p.bound round+3)^2 := Nat.le_mul_of_pos_left _ (by omega)
  dsimp only [generateCost]
  nlinarith only [main,extra,big]

#print axioms generate_keys
#print axioms generateCost_polynomial
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
