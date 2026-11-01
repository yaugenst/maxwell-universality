import Maxwell.Continuum.SourceRoutingPhaseStartupPlan

namespace Maxwell.Cost.RoutingPorts.Complete.PhaseStartup
open Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def work : Finset ℕ := {0,1,2,3}∪GeometryArithmetic.controls
def code : Code := NatAssign.code instructions
def inputWidth (half forward backward : ℕ) : ℕ :=
  ((2*half)*(2*half)).bits.length+half.bits.length+
    (((2*half)*(2*half)).bits.length).bits.length+forward.bits.length+backward.bits.length+16
def cost (half forward backward : ℕ) : ℕ :=
  3000*8^instructions.length*(inputWidth half forward backward+2)^2

theorem initial_width (half forward backward i : ℕ) :
    (initial half forward backward i).bits.length≤ inputWidth half forward backward := by
  simp only [initial]
  split_ifs <;> simp only [inputWidth,show (0:ℕ).bits.length=0 by decide] <;> omega

theorem initial_bank (half : ℕ) (l : Layout ((2*half)*(2*half))) (s : BitRAMState)
    (metadata : Metadata l s) (halfWord : Word s 710 half)
    (fresh : ∀ i∈GeometryArithmetic.ids,Blank s i) :
    NatAssign.Bank ids (initial half l.forward l.backward) s := by
  intro i hi
  by_cases h709 : i=709
  · subst i;simpa [initial] using metadata.count
  by_cases h710 : i=710
  · subst i;simpa [initial] using halfWord
  by_cases h711 : i=711
  · subst i;simpa [initial] using metadata.width
  by_cases h716 : i=716
  · subst i;simpa [initial] using metadata.forward
  by_cases h717 : i=717
  · subst i;simpa [initial] using metadata.backward
  have him : i∈GeometryArithmetic.ids := by
    rcases Finset.mem_union.mp hi with hi|hi
    · exact hi
    · simp only [sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  simpa [initial,h709,h710,h711,h716,h717] using
    (RationalAccumulator.zero_word_iff_blank s i).mpr (fresh i him)

theorem executes (half : ℕ) (hh : 0<half) (l : Layout ((2*half)*(2*half)))
    (ordered : l.forward+(2*half)*(2*half)*((2*half)*(2*half)).bits.length≤l.backward)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (metadata : Metadata l s.val) (halfWord : Word s.val 710 half)
    (fresh : ∀ i∈GeometryArithmetic.ids,Blank s.val i) (ready : GeometryArray.Ready s.val) :
    let p := plan (2*half) (by positivity) l ordered
    ∃ steps t, Executes input tape code steps s t ∧ steps≤cost half l.forward l.backward ∧
      NatAssign.Bank GeometryArithmetic.ids (GeometryPhase.seed p 0) t.val ∧
      GeometryArray.Ready t.val ∧ GeometryPhase.Metadata p t.val ∧
      Word t.val 709 ((2*half)*(2*half)) ∧ BinaryPrecision.Frame work s.val t.val := by
  dsimp only
  have lower (i : ℕ) (hi : i∈ids) : 4≤ i := by
    rcases Finset.mem_union.mp hi with hi|hi
    · have h := GeometryArithmetic.ids_lower i hi;omega
    · simp only [sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  obtain ⟨steps,t,he,hc,bt,st,hf⟩ := NatAssign.executes ids lower instructions valid
    (initial half l.forward l.backward) input tape s (initial_bank half l s.val metadata halfWord fresh)
    (GeometryArithmetic.scratch ready)
  have hp := NatAssign.price_bound ids instructions valid (initial half l.forward l.backward)
    (inputWidth half l.forward l.backward) (fun i _ => initial_width half l.forward l.backward i) (by
      simp [instructions,List.range_succ,NatAssign.Instruction.literalWidth,inputWidth]
      change 4≤_
      omega)
  have frame : BinaryPrecision.Frame work s.val t.val := hf.mono (by decide +kernel)
  refine ⟨steps,t,he,hc.trans hp,?_,GeometryArithmetic.ready_of_frame ready st
    (frame.mono (by decide +kernel)),?_,
    RationalAccumulator.word_of_eq (frame.tapes 709 (by decide)) metadata.count,frame⟩
  · intro i hi
    rw [←values half hh l ordered i hi]
    exact bt i (Finset.mem_union_left _ hi)
  · exact ⟨RationalAccumulator.word_of_eq (frame.tapes 711 (by decide)) metadata.width,
      RationalAccumulator.word_of_eq (frame.tapes 716 (by decide)) metadata.forward,
      BankArray.word_of_eq (frame.tapes 718 (by decide)) metadata.clock⟩

#print axioms executes

end Maxwell.Cost.RoutingPorts.Complete.PhaseStartup
