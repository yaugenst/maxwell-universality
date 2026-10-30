import Maxwell.Continuum.WellTargetArithmetic

/-! Three fixed target routines followed by the actual reciprocal and
half-up numerator routine. The kind is static in the three chronological
passes; no graph-dependent instruction list or arithmetic oracle is used. -/
namespace Maxwell.Continuum.RationalDataflow.WellTarget
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

inductive Kind where
  | original | internal | mediator
  deriving DecidableEq

def control : Kind→Control
  | .original=>original | .internal=>internal | .mediator=>mediator

def target : Kind→(ℕ→Parts)→ℚ
  | .original,v=>(v 4).value*(((v 8).value-8)/2-(v 9).value)
  | .internal,v=> -2*(v 4).value
  | .mediator,v=> -(v 8).value^2/(v 4).value

def code (k : Kind) : Code := .seq (control k).code WellStrength.code

def output (k : Kind) (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  WellStrength.values P ((control k).evaluate v)

theorem control_valid (k : Kind) : (control k).Valid WellStrength.bank := by
  cases k
  · exact original_valid
  · exact internal_valid
  · exact mediator_valid

theorem control_admissible (k : Kind) (v : ℕ→Parts) (ha : (v 4).value≠0) :
    (control k).AdmissibleTrace v := by
  cases k
  · exact original_admissible v
  · exact internal_admissible v
  · exact mediator_admissible v ha

theorem control_fits (k : Kind) : (control k).LiteralsFit 4 := by
  have w8 : (Parts.literal 8).Width 4 := by norm_num [Parts.literal,Parts.Width];decide
  have wh : (Parts.literal (1/2)).Width 4 := by norm_num [Parts.literal,Parts.Width];decide
  have w2 : (Parts.literal (-2)).Width 4 := by norm_num [Parts.literal,Parts.Width];decide
  have w1 : (Parts.literal (-1)).Width 4 := by norm_num [Parts.literal,Parts.Width]
  cases k
  · exact ⟨w8,trivial,wh,trivial,trivial,trivial,trivial⟩
  · exact ⟨w2,trivial,trivial⟩
  · exact ⟨trivial,trivial,trivial,w1,trivial,trivial⟩

theorem control_steps (k : Kind) : (control k).steps≤6 := by cases k <;> decide

theorem control_midpoint (k : Kind) (v : ℕ→Parts) : (control k).evaluate v 1=v 1 := by
  cases k
  · exact original_midpoint v
  · exact internal_midpoint v
  · exact mediator_midpoint v

theorem control_target (k : Kind) (v : ℕ→Parts) (hg : Good WellStrength.bank v)
    (ha : (v 4).value≠0) : ((control k).evaluate v 2).value=target k v := by
  cases k
  · exact original_value v hg
  · exact internal_value v hg
  · exact mediator_value v hg ha

theorem executes (k : Kind) (P W : ℕ) (hW : 4≤W) (hP : (2^P).bits.length≤W)
    (v : ℕ→Parts) (hw : WidthBank WellStrength.bank W v) (hg : Good WellStrength.bank v)
    (ha : (v 4).value≠0) (hn : (v 1).value+target k v≠0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready WellStrength.bank v s) (hz : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape (code k) cost s t ∧ cost≤2^184*(P+W+16)^2 ∧
      Ready WellStrength.bank (output k P v) t ∧ Good WellStrength.bank (output k P v) ∧
      WidthBank WellStrength.bank (P+4096*W+4179) (output k P v) ∧
      output k P v 0=Parts.literal (WellStrength.numerator P (v 1).value (target k v):ℚ) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace WellStrength.bank) s.val t.val := by
  have hc := control_valid k
  have adm := control_admissible k v ha
  have trace0 := (control k).automatic_widthTrace WellStrength.bank hc v W hw ((control_fits k).mono hW)
  have widthLe : 2^(control k).steps*(W+1)≤64*(W+1) := by
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (control_steps k))
  have trace := trace0.mono widthLe
  obtain ⟨c0,u,e0,hc0,r0,f0⟩ := (control k).executes WellStrength.bank hc v (64*(W+1)) trace hg adm input tape s hr
  have g0 := (control k).evaluate_good WellStrength.bank hc v hg adm
  have hn0 : ((control k).evaluate v 1).value+((control k).evaluate v 2).value≠0 := by
    rwa [control_midpoint,control_target k v hg ha]
  have pow0 : Word u.val 144 (2^P) := RationalAccumulator.word_of_eq
    (f0.tapes 144 (outside_workspace WellStrength.bank 144 (by decide))) hp
  obtain ⟨c1,t,e1,hc1,r1,g1,w1,val1,z1,p1,f1⟩ := WellStrength.executes P (64*(W+1)) (by omega)
    (hP.trans (by omega)) ((control k).evaluate v) trace.result g0 hn0 input tape u r0 (hz.arithmetic_frame f0) pow0
  rw [control_midpoint,control_target k v hg ha] at val1
  refine ⟨c0+c1,t,e0.seq e1,?_,r1,g1,?_,val1,z1,p1,
    (f0.mono (RoundedInteger.arithmetic_workspace_subset WellStrength.bank)).trans f1⟩
  · have h0 : c0≤6*operationCost (64*(W+1))+1 := hc0.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (control_steps k)) 1)
    unfold operationCost at h0
    nlinarith only [h0,hc1,Nat.zero_le P,Nat.zero_le W]
  · change WidthBank WellStrength.bank (P+4096*W+4179)
      (WellStrength.values P ((control k).evaluate v))
    convert w1 using 1
    omega

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellTarget
