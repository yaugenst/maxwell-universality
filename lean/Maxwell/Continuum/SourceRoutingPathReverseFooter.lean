import Maxwell.Continuum.SourceRoutingPathRestore
import Maxwell.Continuum.SourceRoutingPathNextFields

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def footerCode : Code := .seq (loadCode 1234 1253) (NatAssign.code restoreSeed)
def footerWork : Finset ℕ := {1253}∪GeometryArithmetic.work

theorem emission_fields {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ)
    (saved : SortArrays.Keys q) (i : Fin (q*q)) (level cursor next : ℕ) (transpose : Bool) :
    ∀j∈seedFields,cursorValues (emissionValues p round saved i level cursor transpose) next j=
      GeometrySort.seed p round i.val j := by
  intro j hj
  have ranges : j=1200 ∨ j=1201 ∨ j=1202 ∨ j=1215 ∨ j=1216 ∨ j=1217 ∨ j=1219 ∨ j=1220 := by
    simpa only [seedFields,Finset.mem_insert,Finset.mem_singleton] using hj
  rw [cursorValues_other _ _ j (by omega)]
  by_cases same : j=1201
  · subst j
    rw [emission_other _ _ _ _ _ _ _ 1201 (by decide)]
    exact advanced_seed_other p round saved i 1201 (by decide) (by decide) (by decide)
  · apply emission_seed_field
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega

theorem emission_quotient_zero {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ)
    (saved : SortArrays.Keys q) (i : Fin (q*q)) (level cursor next : ℕ) (transpose : Bool) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      cursorValues (emissionValues p round saved i level cursor transpose) next j=0 := by
  intro j hj
  have small : j<1200 := by
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  rw [cursorValues_other _ _ j (by omega)]
  exact emission_zero p round saved i level cursor transpose j hj

theorem footer_executes {q : ℕ} (p : GeometrySort.Plan q) (round index old B : ℕ) (v : ℕ→ℕ)
    (fields : ∀j∈seedFields,v j=GeometrySort.seed p round index j)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (width : ∀j∈ids,(v j).bits.length ≤ B) (oldWidth : old.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (bank : NatAssign.Bank ids v s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (cursor : Word s.val 1253 old) :
    ∃steps t,Executes input tape footerCode steps s t ∧ steps ≤ 2^112*(B+2)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed p round index) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ Word t.val 1253 (v 1234) ∧
      BinaryPrecision.Frame footerWork s.val t.val := by
  obtain ⟨c₀,a,e₀,h₀,ca,f₀⟩ := copyWord_executes 1234 1253 old (v 1234) (by decide)
    input tape s (bank 1234 (by decide)) cursor
  have ba := bank_of_frame bank f₀ (by decide)
  have za := ready.of_tapes (fun j hj => f₀.tapes j (by simp only [Finset.mem_singleton];omega))
  obtain ⟨c₁,t,e₁,h₁,bt,zt,pt,f₁⟩ := restoreSeed_executes p round index B v fields zero width
    input tape a ba za (RationalAccumulator.blank_of_eq (f₀.tapes 1249 (by decide)) privateBlank)
  refine ⟨c₀+c₁,t,e₀.seq e₁,?_,bt,zt,pt,
    RationalAccumulator.word_of_eq (f₁.tapes 1253 (by decide)) ca,
    (f₀.mono (by decide)).trans (f₁.mono Finset.subset_union_right)⟩
  have nextWidth := width 1234 (by decide)
  nlinarith only [h₀,h₁,oldWidth,nextWidth]

#print axioms footer_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
