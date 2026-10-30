import Maxwell.Continuum.SourceRoutingScatterLoop

/-! The public scatter program copies its actual stored incidence count,
runs the fixed traversal, and reclaims the countdown tape. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Scatter
open Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

def code : Code := .seq (.call (WordTransfer.clone 142 779))
  (.seq loopCode (.call (TapeOps.clear 779)))
def cost {k n : ℕ} (p : Plan k n) : ℕ := loopCost p k.bits.length+21*k.bits.length+23

theorem executes {k n : ℕ} (p : Plan k n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Runtime p 0 s)
    (hcount : Word s.val 142 k) (h779 : Blank s.val 779) :
    ∃steps t, Executes input tape code steps s t ∧ steps≤cost p ∧ Runtime p k t ∧
      Blank t.val 779 ∧ RoutingOutside p.routing s.val t.val ∧ ArchiveFrame loopWork s.val t.val := by
  obtain ⟨co,hco⟩ := hcount
  obtain ⟨origin,ho⟩ := h779
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 142 779 (by decide) input tape k.bits co origin s hco ho
  have keepa (i : ℕ) (hi : i≠779) : a.val.tapes i=s.val.tapes i := by simp [atapes,hi]
  have ra := hs.counter_frame af.2.2.1 keepa
  have ac : a.val.tapes 779=BitTape.shifted k.bits origin := by simp [atapes]
  have framea : ArchiveFrame loopWork s.val a.val :=
    ⟨af.2.1,af.2.2.2.1,af.2.2.2.2.1,fun i _ hi => keepa i (by
      intro he; subst i; exact hi (by simp [loopWork]))⟩
  obtain ⟨cb,b,word,eb,hcb,rb,bword,hlen,ob,fb⟩ := loop_executes p input tape k.bits origin
    (addressValue_bits _) a ra ac
  obtain ⟨t,et,ttapes,tf⟩ := WordCall.clear 779 input tape word origin b bword
  have keept (i : ℕ) (hi : i≠779) : t.val.tapes i=b.val.tapes i := by simp [ttapes,hi]
  have rt := rb.counter_frame tf.2.2.1 keept
  have framet : ArchiveFrame loopWork b.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,fun i _ hi => keept i (by
      intro he; subst i; exact hi (by simp [loopWork]))⟩
  refine ⟨_,t,ea.seq (eb.seq et),?_,rt,⟨origin+word.length,by simp [ttapes]⟩,
    (RoutingOutside.of_memory af.2.2.1).trans (ob.trans (RoutingOutside.of_memory tf.2.2.1)),
    framea.trans (fb.trans framet)⟩
  unfold cost
  omega

theorem partial_tables {k n : ℕ} (p : Plan k n)
    (hsource : Function.Injective p.source) (htarget : Function.Injective p.target)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Runtime p 0 s)
    (hcount : Word s.val 142 k) (h779 : Blank s.val 779) :
    ∃steps t, Executes input tape code steps s t ∧ steps≤cost p ∧ Runtime p k t ∧
      Stored p.routing (table (realPairs p.source p.target))
        (table ((realPairs p.source p.target).map Prod.swap)) t.val ∧
      Blank t.val 730 ∧ Blank t.val 731 ∧ Blank t.val 779 ∧
      RoutingOutside p.routing s.val t.val ∧ ArchiveFrame loopWork s.val t.val := by
  obtain ⟨steps,t,he,hc,ht,h779,ho,hf⟩ := executes p input tape s hs hcount h779
  have stored := ht.stored
  rw [forward_complete p.source p.target hsource,backward_complete p.source p.target htarget] at stored
  exact ⟨steps,t,he,hc,ht,stored,
    (RationalAccumulator.zero_word_iff_blank _ _).mp (ht.bank 730 (by decide)),
    (RationalAccumulator.zero_word_iff_blank _ _).mp (ht.bank 731 (by decide)),h779,ho,hf⟩

#print axioms partial_tables

end Maxwell.Cost.RoutingPorts.Complete.Scatter
