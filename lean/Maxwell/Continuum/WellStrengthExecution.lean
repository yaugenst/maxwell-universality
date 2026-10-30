import Maxwell.Continuum.WellStrengthArithmetic

/-! The fixed strength routine computes its reciprocal and actual nearest
integer from stored rational channels. All internal widths and inverse
admissibility are derived from the represented midpoint and target. -/
namespace Maxwell.Continuum.RationalDataflow.WellStrength
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def code : Code := .seq reciprocal.code (NearestInteger.code 0 3)

theorem executes (P W : ℕ) (hW : 2≤W) (hP : (2^P).bits.length≤W)
    (v : ℕ→Parts) (hw : WidthBank bank W v) (hg : Good bank v)
    (hn : (v 1).value+(v 2).value≠0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready bank v s) (hclean : DyadicFloor.Clean s.val) (hpower : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape code cost s t ∧
      cost≤2^168*(P+W+8)^2 ∧ Ready bank (values P v) t ∧
      Good bank (values P v) ∧ WidthBank bank (P+64*W+83) (values P v) ∧
      values P v 0=Parts.literal (numerator P (v 1).value (v 2).value : ℚ) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace bank) s.val t.val := by
  have trace := reciprocal.automatic_widthTrace bank reciprocal_valid v W hw (reciprocal_fits W)
  obtain ⟨c0,u,e0,hc0,r0,f0⟩ := reciprocal.executes bank reciprocal_valid v (4*(W+1))
    trace hg (reciprocal_admissible v hg hn) input tape s hr
  have g0 : Good bank (prepared v) := reciprocal.evaluate_good bank reciprocal_valid v hg
    (reciprocal_admissible v hg hn)
  have w0 : WidthBank bank (4*(W+1)) (prepared v) := trace.result
  have clean0 := hclean.arithmetic_frame f0
  have power0 : Word u.val 144 (2^P) := RationalAccumulator.word_of_eq
    (f0.tapes 144 (outside_workspace bank 144 (by decide))) hpower
  obtain ⟨c1,t,e1,hc1,r1,g1,w1,z1,p1,f1⟩ := NearestInteger.executes bank P 0 3 (4*(W+1))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega) (hP.trans (by omega)) (prepared v) w0 g0 input tape u r0 clean0 power0
  refine ⟨c0+c1,t,e0.seq e1,?_,r1,g1,?_,values_zero P v hg hn,z1,p1,
    (f0.mono (RoundedInteger.arithmetic_workspace_subset bank)).trans f1⟩
  · change c0≤2*operationCost (4*(W+1))+1 at hc0
    unfold operationCost at hc0
    nlinarith only [hc0,hc1,Nat.zero_le P,Nat.zero_le W]
  · change WidthBank bank (P+64*W+83) (NearestInteger.values P 0 3 (prepared v))
    convert w1 using 1
    omega

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellStrength
