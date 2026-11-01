import Maxwell.Continuum.SourceRoutingGeometryDivisionBounds
import Maxwell.Cost.Structured.WordDifference

/-! Nonnegative subtraction in the geometry arithmetic bank. The generic
word kernel is shared with every encoder using natural-word controls. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Structured Maxwell.Continuum.RationalDataflow
open RationalAccumulator (Blank)
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

theorem subtract (left right target : ℕ) (hl : left∈controls) (hr : right∈controls)
    (ht : target∈controls) (v : ℕ→ℕ) (zero : v target=0) (ordered : v right≤v left)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape (WordDifference.code left right target) steps s t ∧
      steps≤300*((v left).bits.length+(v right).bits.length+4) ∧
      NatAssign.Bank ids (Function.update v target (v left-v right)) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧
      BinaryPrecision.Frame work s.val t.val := by
  have bounds (i : ℕ) (hi : i∈controls) : 1200 ≤ i ∧ i ≤ 1239 := Finset.mem_Icc.mp hi
  have hleft:=bounds left hl
  have hright:=bounds right hr
  have htarget:=bounds target ht
  have bz : Blank s.val target := by
    apply (RationalAccumulator.zero_word_iff_blank s.val target).mp
    simpa only [zero] using bank target (Finset.mem_union_left _ ht)
  obtain ⟨steps,t,he,hcost,word,zt,ft⟩:=WordDifference.executes left right target
    (by omega) (by omega) (by omega) input tape (v left) (v right) ordered s
    (bank left (Finset.mem_union_left _ hl)) (bank right (Finset.mem_union_left _ hr)) bz (scratch ready)
  have frame : BinaryPrecision.Frame work s.val t.val := ft.mono (by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · decide
    · decide
    · decide
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ ht))
  refine ⟨steps,t,he,hcost,?_,ready_of_frame ready zt frame,
    RationalAccumulator.blank_of_eq (ft.tapes 1249 (by simp;omega)) privateBlank,frame⟩
  intro i hi
  by_cases heq : i=target
  · subst i
    simpa only [Function.update_self] using word
  · rw [Function.update_of_ne heq]
    exact RationalAccumulator.word_of_eq (ft.tapes i (by
      have h:=ids_lower i hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      omega)) (bank i hi)

#print axioms subtract
end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
