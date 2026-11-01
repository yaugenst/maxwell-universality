import Maxwell.Continuum.WellStrengthPrecisionData
import Maxwell.Cost.SelectedParameters.GeometricAdapterBounds
import Maxwell.Cost.Structured.NatAssign.Values
import Maxwell.Cost.RoutingPorts.Primitives
import Maxwell.Cost.Structured.WordCleanup

/-! Fixed execution of the well precision selector and its binary rounding
power from the retained length and spacing-power words. -/
namespace Maxwell.Continuum.WellStrengthInitialization.Precision
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def extra : Finset ℕ := {990,2221,2228,2601,2602,2604}
def ids : Finset ℕ := Rational.ids extra
def prepare : List NatAssign.Instruction :=
  [.literal 2601 1,.literal 2602 2,.multiply 2221 2602,.multiply 2221 2602,
   .multiply 2221 2602,.multiply 2221 2602,.multiply 2228 2602,.multiply 2228 2602]
def prepared (v : ℕ→ℕ) : ℕ→ℕ:=NatAssign.values prepare v
def headers : List ℕ := [144,2605]
def code : Code := .seq (NatAssign.code prepare)
  (.seq (GeometricAdapter.code 1 2 2601 2602 990 2604)
    (.seq (WordCleanup.code headers) (RoutingPorts.powerCode 990 2605 144)))
def work : Finset ℕ := {0,1,2,3,2601,2602}∪GeometricAdapter.workspace 990 2604∪{144,2605}
def costBound (P B H : ℕ) : ℕ := 3000*8^8*(B+2)^2+
  (GeometricAdapter.costBound P 2 (2^8*(B+1))+
    (2*(6*H+4)+1+((P+1)*(13*P.bits.length+25)+21*P.bits.length+27)))

theorem extra_ge (i : ℕ) (hi : i∈extra) : 540 ≤ i:=by
  simp only [extra,Finset.mem_insert,Finset.mem_singleton] at hi;omega

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i:=by
  rcases Finset.mem_union.mp hi with he|hc
  · exact (by decide : (4:ℕ)≤540).trans (extra_ge i he)
  · simp only [Rational.common,Finset.mem_insert,Finset.mem_singleton] at hc;omega

theorem valid : ∀a∈prepare,a.Valid ids:=by
  simp [prepare,NatAssign.Instruction.Valid,ids,Rational.ids,extra]

theorem prepared_outputs (v : ℕ→ℕ) : prepared v 2601=1 ∧
    prepared v 2602=precisionDenominator (v 2221) (v 2228) := by
  simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,precisionDenominator]
  ring

theorem literals (B : ℕ) (hB : 2≤B) : ∀a∈prepare,a.literalWidth≤B:=by
  simp [prepare,NatAssign.Instruction.literalWidth]
  exact ⟨by omega,hB⟩

theorem executes (L d : ℕ) (hL : 0<L) (v : ℕ→ℕ) (B H : ℕ) (hB : 2≤B)
    (length : v 2221=L) (spacing : v 2228=3^d)
    (width : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val)
    (geo : ∀i∈Geometric.extra,Blank s.val i) (old : WordCleanup.Bounded headers H s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound (FiniteAuxiliary.onsitePrecision L d hL) B H ∧
      Word t.val 990 (FiniteAuxiliary.onsitePrecision L d hL) ∧
      Word t.val 144 (2^FiniteAuxiliary.onsitePrecision L d hL) ∧ Blank t.val 2605 ∧
      NatAssign.Scratch t.val ∧ (∀i∈Geometric.extra∪Rational.common,Blank t.val i) ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,za,f0⟩:=NatAssign.executes ids ids_ge prepare valid v input tape s bank scratch
  change NatAssign.Bank ids (prepared v) a.val at ba
  have price:=NatAssign.price_bound ids prepare valid v B width (literals B hB)
  change NatAssign.price prepare v≤3000*8^8*(B+2)^2 at price
  have aw : ∀i∈ids,(prepared v i).bits.length≤2^8*(B+1):=by
    intro i hi
    have result:=NatAssign.values_width ids prepare valid v B width (literals B hB) i hi
    change (prepared v i).bits.length+1≤2^8*(B+1) at result
    omega
  have ag : ∀i∈Geometric.extra,Blank a.val i:=by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f0.tapes i ?_) (geo i hi)
    exact Finset.disjoint_left.mp (show Disjoint Geometric.extra (NatAssign.changes prepare) by decide) hi
  have one:= (prepared_outputs v).1
  have denominator : prepared v 2602=precisionDenominator L (3^d):=by
    rw [(prepared_outputs v).2,length,spacing]
  have positive : 0<prepared v 2602:=by rw [denominator];unfold precisionDenominator;positivity
  have execution:=GeometricAdapter.executes extra extra_ge 1 2 2601 2602 990 2604
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (prepared v) 2 (2^8*(B+1)) (by decide) (by decide) (by rw [one];decide) positive
    aw input tape a ba za ag
  dsimp only at execution
  simp only [one,denominator,selected_precision L d hL] at execution
  obtain ⟨c1,b,e1,h1,bb,zb,gb,_,f1⟩:=execution
  have precision : Word b.val 990 (FiniteAuxiliary.onsitePrecision L d hL):=by
    simpa only [Rational.after_num (prepared v) 990 2604 (FiniteAuxiliary.onsitePrecision L d hL,1) (by decide) (by decide)] using bb 990 (by decide)
  have frame01 : BinaryPrecision.Frame ({0,1,2,3,2601,2602}∪GeometricAdapter.workspace 990 2604) s.val b.val:=
    (f0.mono (by decide)).trans (f1.mono Finset.subset_union_right)
  have old1 : WordCleanup.Bounded headers H b.val:=by
    intro i hi
    obtain ⟨xs,hxs,w⟩:=old i hi
    have cases : i=144 ∨ i=2605:=by simpa only [headers,List.mem_cons,List.not_mem_nil,or_false] using hi
    refine ⟨xs,hxs,BankArray.word_of_eq (frame01.tapes i ?_) w⟩
    rcases cases with rfl|rfl <;> decide
  obtain ⟨c2,c,e2,h2,zc,f2⟩:=WordCleanup.executes headers H input tape b old1
  have pc : Word c.val 990 (FiniteAuxiliary.onsitePrecision L d hL):=
    RationalAccumulator.word_of_eq (f2.tapes 990 (by decide)) precision
  obtain ⟨c3,t,e3,h3,power,temp,f3⟩:=RoutingPorts.power 990 2605 144 (by decide) (by decide) (by decide)
    input tape (FiniteAuxiliary.onsitePrecision L d hL) c pc (zc 2605 (by decide)) (zc 144 (by decide))
  have finalFrame : BinaryPrecision.Frame {144,2605} b.val t.val:=
    (f2.mono (by decide)).trans (f3.mono (by decide))
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,
    RationalAccumulator.word_of_eq (f3.tapes 990 (by decide)) pc,power,temp,?_,?_,
    (frame01.mono Finset.subset_union_left).trans (finalFrame.mono Finset.subset_union_right)⟩
  · have a0:=h0.trans price
    change c2≤2*(6*H+4)+1 at h2
    unfold costBound
    omega
  · intro i hi
    exact RationalAccumulator.blank_of_eq (finalFrame.tapes i (by
      simp only [Finset.mem_insert,Finset.mem_singleton];omega)) (zb i hi)
  · intro i hi
    apply RationalAccumulator.blank_of_eq (finalFrame.tapes i ?_) (gb i hi)
    simp only [Geometric.extra,Rational.common,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [Finset.mem_insert,Finset.mem_singleton];omega

#print axioms executes
end Maxwell.Continuum.WellStrengthInitialization.Precision
