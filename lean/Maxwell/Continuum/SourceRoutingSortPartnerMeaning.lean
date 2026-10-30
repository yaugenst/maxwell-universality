import Maxwell.Continuum.SourceRoutingSortPartner

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured GeometryArithmetic Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem partner_admissible {q index round : ℕ} {v : ℕ→ℕ}
    (setup : PartnerSetup q index round v) (positive : 0<q) : partnerProgram.Admissible v := by
  have fields:=prepared_fields setup
  have chosen : choosePartner.Admissible (prepared v) := by
    have hr:=right_admissible (prepared v)
    have hl:=left_admissible (prepared v) fields.2.2.2.2.2.2.2.2
    simp only [choosePartner,Control.Admissible,hr,hl,ite_self]
  change 0<v 1200 ∧ 0<v 1220 ∧ 0<v 1220 ∧ choosePartner.Admissible (prepared v)
  exact ⟨by simpa only [setup.count] using positive,by rw [setup.two];decide,
    by rw [setup.two];decide,chosen⟩

theorem choose_evaluate (v : ℕ→ℕ) (h5 : v 1205<2) (h6 : v 1206<2) :
    choosePartner.evaluate v=if v 1205=v 1206 then rightPartner.evaluate v else leftPartner.evaluate v := by
  change (if 0<v 1206 then (if 0<v 1205 then rightPartner.evaluate v else leftPartner.evaluate v)
    else (if 0<v 1205 then leftPartner.evaluate v else rightPartner.evaluate v))=_
  split_ifs <;> first | rfl | omega

theorem partner_result {q index round : ℕ} {v : ℕ→ℕ} (setup : PartnerSetup q index round v) :
    (partnerProgram.evaluate v 1210,partnerProgram.evaluate v 1211)=
      if (index/q)%2=round%2 then
        (if 0 < index/q then (q*(index/q-1)+index%q,1) else (index,0))
      else if index/q+1<q then (index+q,0) else (index,0) := by
  obtain ⟨h0,h3,h4,h5,h6,h7,h10,h11,h19⟩:=prepared_fields setup
  have w5 : prepared v 1205<2 := by rw [h5];omega
  have w6 : prepared v 1206<2 := by rw [h6];omega
  simp only [program_evaluate,choose_evaluate _ w5 w6,h5,h6]
  by_cases same : (index/q)%2=round%2
  · simp only [same,ite_true]
    rw [right_result,h0,h3,h4,h10,h11]
  · simp only [same,ite_false]
    rw [left_result _ h19,h7,h0,h10,h11]

theorem partner_cost {q index round : ℕ} {v : ℕ→ℕ}
    (setup : PartnerSetup q index round v) (positive : 0<q)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (B : ℕ) (hB : 1 ≤ B) (width : ∀j∈GeometryArithmetic.ids,(v j).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids v s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : RationalAccumulator.Blank s.val 1249) :
    ∃steps t,Executes input tape partnerProgram.code steps s t ∧ steps ≤ 2^170*(B+2)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (partnerProgram.evaluate v) t.val ∧
      GeometryArray.Ready t.val ∧ RationalAccumulator.Blank t.val 1249 ∧
      BinaryPrecision.Frame GeometryArithmetic.work s.val t.val := by
  obtain ⟨steps,t,he,hc,bt,zt,pt,ft⟩:=partnerProgram.executes partner_valid v zero
    (partner_admissible setup positive) B width (partner_literals B hB) input tape s bank ready privateBlank
  exact ⟨steps,t,he,hc.trans (controlCost_steps _ _ _ partner_steps),bt,zt,pt,ft⟩

#print axioms partner_result
#print axioms partner_cost
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
