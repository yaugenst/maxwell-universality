import Maxwell.Continuum.ParameterGeometryCountData

namespace Maxwell.Continuum.Parameters.GeometryCountMachine
open Maxwell.Cost Maxwell.Cost.Structured
open Maxwell.Cost.RoutingPorts.Complete GeometryArithmetic
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem executes (v : ℕ→ℕ) (cursor vertices edges B : ℕ) (large : 4≤B)
    (width : ∀i∈ids,(v i).bits.length≤B)
    (cursorWidth : cursor.bits.length≤B) (verticesWidth : vertices.bits.length≤B)
    (edgesWidth : edges.bits.length≤B) (ordered : 3*vertices+11*edges≤2*cursor)
    (zero : ∀i∈RationalDataflow.NaturalQuotient.workPorts,v i=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) (cursorWord : Word s.val 1253 cursor)
    (verticesWord : Word s.val 141 vertices) (edgesWord : Word s.val 153 edges) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤2^130*(B+2)^2 ∧
      NatAssign.Bank ids (output v cursor vertices edges) t.val ∧ GeometryArray.Ready t.val ∧
      Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c₀,a,e₀,h₀,ba,za,a1249,f₀⟩:=load_executes 1253 1202 (by decide) (by decide)
    v cursor input tape s bank ready privateBlank cursorWord
  obtain ⟨c₁,b,e₁,h₁,bb,zb,b1249,f₁⟩:=load_executes 141 1203 (by decide) (by decide)
    (Function.update v 1202 cursor) vertices input tape a ba za a1249
    (RationalAccumulator.word_of_eq (f₀.tapes 141 (by decide)) verticesWord)
  obtain ⟨c₂,c,e₂,h₂,bc,zc,c1249,f₂⟩:=load_executes 153 1204 (by decide) (by decide)
    (Function.update (Function.update v 1202 cursor) 1203 vertices) edges input tape b bb zb b1249
    (RationalAccumulator.word_of_eq ((f₁.tapes 153 (by decide)).trans (f₀.tapes 153 (by decide))) edgesWord)
  have literals : ∀a∈instructions,a.literalWidth≤B := by
    have small : ∀a∈instructions,a.literalWidth≤4 := by decide +kernel
    exact fun a ha=>(small a ha).trans large
  have wc:=loaded_width v cursor vertices edges B width cursorWidth verticesWidth edgesWidth
  obtain ⟨c₃,d,e₃,h₃,bd,zd,f₃⟩:=stage instructions valid (loaded v cursor vertices edges) B
    wc literals input tape c bc zc
  have privateD : Blank d.val 1249 := RationalAccumulator.blank_of_eq (f₃.tapes 1249 (by decide)) c1249
  have pv:=prepared_values v cursor vertices edges
  obtain ⟨c₄,e,e₄,h₄,be,ze,e1249,f₄⟩:=subtract 1205 1206 1207
    (by decide) (by decide) (by decide) (prepared v cursor vertices edges) pv.2.2.1
    (by simpa only [pv.1,pv.2.1] using ordered) input tape d bd zd privateD
  have be' : NatAssign.Bank ids (subtracted v cursor vertices edges) e.val := by
    simpa only [subtracted,pv.1,pv.2.1] using be
  have wd : ∀i∈ids,(prepared v cursor vertices edges i).bits.length≤2^9*(B+1) := by
    intro i hi
    have h:=NatAssign.values_width ids instructions valid (loaded v cursor vertices edges) B wc literals i hi
    change (prepared v cursor vertices edges i).bits.length+1≤2^9*(B+1) at h
    omega
  have we : ∀i∈ids,(subtracted v cursor vertices edges i).bits.length≤2^9*(B+1) := by
    intro i hi
    by_cases heq : i=1207
    · subst i
      simp only [subtracted,Function.update_self]
      have h:=(RationalWords.bits_mono (Nat.sub_le (2*cursor) (3*vertices+11*edges))).trans
        (by simpa only [pv.1] using wd 1205 (by decide))
      exact h
    · simpa only [subtracted,Function.update_of_ne heq] using wd i hi
  have zeq : ∀i∈RationalDataflow.NaturalQuotient.workPorts,subtracted v cursor vertices edges i=0 := by
    intro i hi
    have hn : i≠1207 := by
      simp only [RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    rw [subtracted,Function.update_of_ne hn,prepared_quotient v cursor vertices edges i hi,zero i hi]
  obtain ⟨c₅,t,e₅,h₅,bt,zt,t1249,f₅⟩:=divide 1207 1208 1209 1210
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (subtracted v cursor vertices edges) zeq (by
      simpa only [subtracted,Function.update_of_ne (by decide : (1208:ℕ)≠1207),pv.2.2.2]
        using (by decide : 0<3))
    (2^9*(B+1)) we input tape e be' ze e1249
  refine ⟨c₀+(c₁+(c₂+(c₃+(c₄+c₅)))),t,e₀.seq (e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅)))),?_,
    bt,zt,t1249,?_⟩
  · have w₂:=width 1202 (by decide)
    have w₃:=width 1203 (by decide)
    have w₄:=width 1204 (by decide)
    simp only [Function.update_of_ne (by decide : (1203:ℕ)≠1202)] at h₁
    simp only [Function.update_of_ne (by decide : (1204:ℕ)≠1203),
      Function.update_of_ne (by decide : (1204:ℕ)≠1202)] at h₂
    change c₃≤3000*8^9*(B+2)^2 at h₃
    have dw₅:=wd 1205 (by decide)
    have dw₆:=wd 1206 (by decide)
    nlinarith only [h₀,h₁,h₂,h₃,h₄,h₅,w₂,w₃,w₄,cursorWidth,verticesWidth,edgesWidth,dw₅,dw₆]
  · exact (f₀.mono (by decide)).trans ((f₁.mono (by decide)).trans
      ((f₂.mono (by decide)).trans ((f₃.mono (by decide)).trans (f₄.trans f₅))))

#print axioms executes
end Maxwell.Continuum.Parameters.GeometryCountMachine
