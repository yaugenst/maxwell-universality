import Maxwell.Continuum.WellStrengthExecution

/-! Physical calibration and the proved target interval discharge the
reciprocal's nonzero-denominator condition. The fixed program returns the
literal onsiteRound numerator used by the actual continuum instance. -/
namespace Maxwell.Continuum.RationalDataflow.WellStrength
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word)
open MasterConstants EffectiveMass
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

 theorem onsite_denominator_pos {L : ℕ} {z : ℝ} (hL : Ls≤(L:ℝ))
    (D : Auxiliary.Calibration (L:ℝ)⁻¹ z)
    (d : ℕ) (I : Calibration.RationalInterval) (θ : ℚ)
    (hI : I.Contains (muH D (inverse_length_le_1024 hL)))
    (hw : I.width≤(Parameters.zeta d)^2/8)
    (hθ : |(θ:ℝ)|≤(1/(2:ℝ)^196)*(L:ℝ)^2) : 0<I.midpoint+θ := by
  have hm := I.midpoint_error hI
  have hwr : (I.width:ℝ)≤(Parameters.zeta d:ℝ)^2/8 := by exact_mod_cast hw
  have he : |(I.midpoint:ℝ)-muH D (inverse_length_le_1024 hL)|≤(Parameters.zeta d:ℝ)^2/16 := by
    linarith only [hm,hwr]
  have hμ := muH_bounds D (inverse_length_le_1024 hL)
  simp only [inv_pow,inv_inv] at hμ
  have hd := Parameters.reciprocal_denominator_enclosure hL hμ.1 hμ.2 hθ he
    (by exact_mod_cast (Parameters.zeta_pos d).le)
    (by exact_mod_cast Parameters.zeta_le_one d)
  have hl : (0:ℝ)<L := MasterConstants.length_pos hL
  have hp : (0:ℝ)<(I.midpoint:ℝ)+(θ:ℝ) := (by positivity : (0:ℝ)<(1/2^129)*(L:ℝ)^2).trans_le hd.1
  exact_mod_cast hp

theorem onsite_executes {L : ℕ} {z : ℝ} (hL : Ls≤(L:ℝ))
    (D : Auxiliary.Calibration (L:ℝ)⁻¹ z) (hLN : 0<L) (d W : ℕ)
    (I : Calibration.RationalInterval) (θ : ℚ)
    (hI : I.Contains (muH D (inverse_length_le_1024 hL)))
    (hwidth : I.width≤(Parameters.zeta d)^2/8)
    (hθ : |(θ:ℝ)|≤(1/(2:ℝ)^196)*(L:ℝ)^2)
    (hW : 2≤W) (hP : (2^FiniteAuxiliary.onsitePrecision L d hLN).bits.length≤W)
    (v : ℕ→Parts) (hw : WidthBank bank W v) (hg : Good bank v)
    (hmid : (v 1).value=I.midpoint) (htarget : (v 2).value=θ)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready bank v s) (hclean : DyadicFloor.Clean s.val)
    (hpower : Word s.val 144 (2^FiniteAuxiliary.onsitePrecision L d hLN)) :
    ∃cost t,Executes input tape code cost s t ∧
      cost≤2^168*(FiniteAuxiliary.onsitePrecision L d hLN+W+8)^2 ∧
      Ready bank (values (FiniteAuxiliary.onsitePrecision L d hLN) v) t ∧
      values (FiniteAuxiliary.onsitePrecision L d hLN) v 0=
        Parts.literal ((FiniteAuxiliary.onsiteRound L hLN (Parameters.zeta d)
          (Parameters.zeta_pos d) I θ).numerator:ℚ) ∧
      Good bank (values (FiniteAuxiliary.onsitePrecision L d hLN) v) ∧
      WidthBank bank (FiniteAuxiliary.onsitePrecision L d hLN+64*W+83)
        (values (FiniteAuxiliary.onsitePrecision L d hLN) v) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^FiniteAuxiliary.onsitePrecision L d hLN) ∧
      BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace bank) s.val t.val := by
  have hn : (v 1).value+(v 2).value≠0 := by
    rw [hmid,htarget]
    exact (onsite_denominator_pos hL D d I θ hI hwidth hθ).ne'
  obtain ⟨c,t,ex,hc,ready,good,width,value,clean,power,frame⟩ :=
    executes (FiniteAuxiliary.onsitePrecision L d hLN) W hW hP v hw hg hn input tape s hr hclean hpower
  rw [hmid,htarget,onsite_numerator L d hLN I θ] at value
  exact ⟨c,t,ex,hc,ready,value,good,width,clean,power,frame⟩

#print axioms onsite_executes
end Maxwell.Continuum.RationalDataflow.WellStrength
