import Maxwell.Continuum.SourceRoutingMetadata
import Maxwell.Cost.RoutingPorts.SelectSize

/-! The routing descriptor and half-side are computed by one fixed program
from the graph's stored vertex count and diagonal-array address. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Startup
open Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000

def banks : Finset ℕ := Size.banks ∪ {708,709,710,711,712,716,717,718,719}
def allWork : Finset ℕ := {0,1,2,3} ∪ banks
def sourceValues (vertices diagonal square i : ℕ) : ℕ :=
  if i=141 then vertices else if i=145 then diagonal else if i=705 then square else 0
def sourceWidth (vertices diagonal : ℕ) : ℕ :=
  vertices.bits.length+diagonal.bits.length+(4^Nat.clog 4 vertices).bits.length+3
def gridSize (vertices : ℕ) : ℕ := 4*4^Nat.clog 4 vertices
def gridLayout (vertices diagonal : ℕ) : Layout (gridSize vertices) :=
  layout (gridSize vertices) (diagonal+4*vertices) (by unfold gridSize; positivity)
def code : Code := .seq Size.code (.seq metadataCode (RoutingPorts.powerCode 706 708 710))
def cost (vertices diagonal : ℕ) : ℕ :=
  Size.rawPrice vertices+1+2^60*(sourceWidth vertices diagonal+2)^2+
    (Nat.clog 4 vertices+1)*(13*(Nat.clog 4 vertices).bits.length+25)+
      21*(Nat.clog 4 vertices).bits.length+27

theorem allWork_small (i : ℕ) (hi : i∈allWork) : i<4 ∨ (700 ≤ i ∧ i<752) := by
  simp only [allWork,banks,Size.banks,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem gridSize_square (vertices : ℕ) : gridSize vertices=(2*2^Nat.clog 4 vertices)^2 := by
  unfold gridSize
  have hp : 4^Nat.clog 4 vertices=(2^Nat.clog 4 vertices)^2 := by
    rw [show (4 : ℕ)=2^2 by decide,←pow_mul,←pow_mul]
    rw [Nat.mul_comm 2]
  rw [hp]
  ring

theorem source_values_width (vertices diagonal : ℕ) :
    ∀i∈ids, (sourceValues vertices diagonal (4^Nat.clog 4 vertices) i).bits.length≤
      sourceWidth vertices diagonal := by
  intro i _
  simp only [sourceValues]
  split_ifs <;> simp only [sourceWidth,show (0 : ℕ).bits.length=0 by decide] <;> omega

theorem executes (vertices diagonal : ℕ) (hv : 0<vertices)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hvertices : Word s.val 141 vertices) (hdiagonal : Word s.val 145 diagonal)
    (hs : Ready s.val) (hfresh : ∀i∈banks,Blank s.val i) :
    ∃steps t, Executes input tape code steps s t ∧ steps≤cost vertices diagonal ∧
      Ready t.val ∧ Metadata (gridLayout vertices diagonal) t.val ∧
      Word t.val 705 (4^Nat.clog 4 vertices) ∧ Word t.val 706 (Nat.clog 4 vertices) ∧
      Word t.val 710 (2^Nat.clog 4 vertices) ∧
      Word t.val 719 (diagonal+4*vertices+2*(gridSize vertices*(gridSize vertices).bits.length)) ∧
      Blank t.val 708 ∧ Blank t.val 712 ∧ BinaryPrecision.Frame allWork s.val t.val := by
  obtain ⟨c0,a,e0,hc0,a705,a706,za,fa⟩ := Size.executes vertices hv input tape s hvertices
    (ready_scratch hs) (fun i hi => hfresh i (Finset.mem_union_left _ hi))
  have fa' : BinaryPrecision.Frame allWork s.val a.val := fa.mono (by
    intro i hi
    simp only [Size.work,allWork,banks,Finset.mem_union] at hi ⊢
    tauto)
  have ra := ready_of_binary hs za fa' allWork_small
  have ba : NatAssign.Bank ids (sourceValues vertices diagonal (4^Nat.clog 4 vertices)) a.val := by
    intro i hi
    by_cases h141 : i=141
    · subst i
      simpa only [sourceValues,ite_true] using
        RationalAccumulator.word_of_eq (fa.tapes 141 (by decide)) hvertices
    · by_cases h145 : i=145
      · subst i
        simpa only [sourceValues,show ¬(145 : ℕ)=141 by decide,ite_false,ite_true] using
          RationalAccumulator.word_of_eq (fa.tapes 145 (by decide)) hdiagonal
      · by_cases h705 : i=705
        · subst i
          simpa [sourceValues] using a705
        · have hn : i∉Size.work := by
            simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
            simp only [Size.work,Size.banks,Finset.mem_union,Finset.mem_insert,
              Finset.mem_singleton,Finset.mem_Icc]
            omega
          have hb : i∈banks := by
            simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
            simp only [banks,Size.banks,Finset.mem_union,Finset.mem_insert,
              Finset.mem_singleton,Finset.mem_Icc]
            omega
          have blank := RationalAccumulator.blank_of_eq (fa.tapes i hn) (hfresh i hb)
          simpa [sourceValues,h141,h145,h705] using
            (RationalAccumulator.zero_word_iff_blank a.val i).mpr blank
  obtain ⟨c1,b,e1,hc1,rb,mb,b719,b712,fb⟩ := metadata_executes
    (sourceValues vertices diagonal (4^Nat.clog 4 vertices)) (by simp [sourceValues])
    (by simp [sourceValues]) (sourceWidth vertices diagonal)
    (by unfold sourceWidth; omega) (source_values_width vertices diagonal) input tape a ba ra
  change Metadata (gridLayout vertices diagonal) b.val at mb
  change Word b.val 719 (diagonal+4*vertices+2*(gridSize vertices*(gridSize vertices).bits.length)) at b719
  have fb' : BinaryPrecision.Frame allWork a.val b.val := fb.mono (by decide)
  have frameb := fa'.trans fb'
  have b706 := RationalAccumulator.word_of_eq (fb.tapes 706 (by decide)) a706
  have b708 := RationalAccumulator.blank_of_eq
    ((fb.tapes 708 (by decide)).trans (fa.tapes 708 (by decide))) (hfresh 708 (by decide))
  have b710 := RationalAccumulator.blank_of_eq
    ((fb.tapes 710 (by decide)).trans (fa.tapes 710 (by decide))) (hfresh 710 (by decide))
  obtain ⟨c2,t,e2,hc2,t710,t708,ft⟩ := RoutingPorts.power 706 708 710 (by decide) (by decide)
    (by decide) input tape (Nat.clog 4 vertices) b b706 b708 b710
  have zt : NatAssign.Scratch t.val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (ft.tapes i (by simp; omega)) (ready_scratch rb i hi)
  have ft' : BinaryPrecision.Frame allWork b.val t.val := ft.mono (by decide)
  have rt := ready_of_binary rb zt ft' allWork_small
  have mt : Metadata (gridLayout vertices diagonal) t.val :=
    ⟨RationalAccumulator.word_of_eq (ft.tapes 709 (by decide)) mb.count,
      RationalAccumulator.word_of_eq (ft.tapes 711 (by decide)) mb.width,
      RationalAccumulator.word_of_eq (ft.tapes 716 (by decide)) mb.forward,
      RationalAccumulator.word_of_eq (ft.tapes 717 (by decide)) mb.backward,
      BankArray.word_of_eq (ft.tapes 718 (by decide)) mb.clock⟩
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,rt,mt,
    RationalAccumulator.word_of_eq ((ft.tapes 705 (by decide)).trans (fb.tapes 705 (by decide))) a705,
    RationalAccumulator.word_of_eq (ft.tapes 706 (by decide)) b706,t710,
    RationalAccumulator.word_of_eq (ft.tapes 719 (by decide)) b719,t708,
    RationalAccumulator.blank_of_eq (ft.tapes 712 (by decide)) b712,frameb.trans ft'⟩
  unfold cost
  omega

#print axioms executes

end Maxwell.Cost.RoutingPorts.Complete.Startup
