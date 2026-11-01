import Maxwell.Continuum.CalibrationSeedRootControlData
import Maxwell.Cost.Structured.NatAssign.BankFrame

/-! Actual exact subtractions and cache flattening after the support test. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def indexCode : Code := .seq (WordDifference.code 753 756 762)
  (.seq (WordDifference.code 754 757 763)
    (.seq (WordDifference.code 755 758 764) (NatAssign.code finish)))
def indexWidth (B : ℕ) : ℕ := 2^finish.length*(B+1)
def indexCost (B : ℕ) : ℕ := 3*(300*(2*B+4))+3000*8^finish.length*(B+2)^2

theorem index_executes (v : ℕ→ℕ) (B : ℕ) (width : ∀i∈ids,(v i).bits.length≤B)
    (ordered : v 756≤v 753 ∧ v 757≤v 754 ∧ v 758≤v 755)
    (zero : v 762=0 ∧ v 763=0 ∧ v 764=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape indexCode cost s t ∧ cost≤ indexCost B ∧
      NatAssign.Bank ids (finished v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(finished v i).bits.length≤ indexWidth B) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,sa,wa,f0⟩ := NatAssign.difference_executes ids 753 756 762 B
    ids_lower (by decide) (by decide) (by decide) v ordered.1 zero.1 width input tape s bank scratch
  let va := Function.update v 762 (v 753-v 756)
  obtain ⟨c1,b,e1,h1,bb,sb,wb,f1⟩ := NatAssign.difference_executes ids 754 757 763 B
    ids_lower (by decide) (by decide) (by decide) va
    (by simpa [va] using ordered.2.1) (by simpa [va] using zero.2.1) wa input tape a ba sa
  let vb := Function.update va 763 (v 754-v 757)
  have bbank : NatAssign.Bank ids vb b.val := by simpa [vb,va] using bb
  have bwidth : ∀i∈ids,(vb i).bits.length≤B := by simpa [vb,va] using wb
  obtain ⟨c2,c,e2,h2,bc,sc,wc,f2⟩ := NatAssign.difference_executes ids 755 758 764 B
    ids_lower (by decide) (by decide) (by decide) vb
    (by simpa [vb,va] using ordered.2.2) (by simpa [vb,va] using zero.2.2) bwidth
    input tape b bbank sb
  have cbank : NatAssign.Bank ids (differences v) c.val := by
    simpa [differences,vb,va] using bc
  have cwidth : ∀i∈ids,(differences v i).bits.length≤B := by
    simpa [differences,vb,va] using wc
  obtain ⟨c3,t,e3,h3,bt,st,f3⟩ := NatAssign.executes ids ids_lower finish finish_valid
    (differences v) input tape c cbank sc
  have literals : ∀a∈finish,a.literalWidth≤B := by simp [finish,NatAssign.Instruction.literalWidth]
  have price := NatAssign.price_bound ids finish finish_valid (differences v) B cwidth literals
  have wt : ∀i∈ids,(finished v i).bits.length≤ indexWidth B := by
    intro i hi
    have hh := NatAssign.values_width ids finish finish_valid (differences v) B cwidth literals i hi
    exact (Nat.le_add_right _ 1).trans hh
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,bt,st,wt,?_⟩
  · unfold indexCost
    omega
  · exact (f0.mono (by decide)).trans ((f1.mono (by decide)).trans
      ((f2.mono (by decide)).trans (f3.mono (NatAssign.changes_subset ids finish finish_valid))))

#print axioms index_executes
end Maxwell.Continuum.Calibration.SeedRoot
