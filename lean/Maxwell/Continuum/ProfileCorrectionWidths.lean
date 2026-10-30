import Maxwell.Continuum.ProfileCorrectionData

/-! Widths of the executed correction pass. The growing index occupies one
register; every coefficient result is recomputed from its stored input. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow
set_option maxHeartbeats 2500000

theorem correctionFinish_width (v : ℕ→Parts) (A B M : ℕ)
    (hw : WidthBank dftRegisters M v) (h1 : (v 1).Width A) (h6 : (v 6).Width B)
    (hfit : A+B+1≤M) : correctionFinish.WidthTrace dftRegisters M v :=
  ⟨hw,trivial,hw.update 1 ((h1.mul h6).mono hfit)⟩

theorem correctionSelect_width (v : ℕ→Parts) (B I M : ℕ)
    (hw : WidthBank dftRegisters M v)
    (h0 : (v 0).Width B) (h1 : (v 1).Width B) (h3 : (v 3).Width B)
    (h6 : (v 6).Width B) (h7 : (v 7).Width 1) (h8 : (v 8).Width I)
    (hfit : 4*B+I+10≤M) : correctionSelect.WidthTrace dftRegisters M v := by
  refine ⟨hw,?_⟩
  split_ifs
  · let w := Function.update v 4 ((v 8).sub (v 7))
    have h4 : (w 4).Width (I+2) := by simpa only [w,Function.update_self] using h8.sub h7
    have hw' : WidthBank dftRegisters M w := hw.update 4 ((h8.sub h7).mono (by omega))
    have hw1 : (w 1).Width B := by simpa [w] using h1
    have hw3 : (w 3).Width B := by simpa [w] using h3
    have hw6 : (w 6).Width B := by simpa [w] using h6
    refine ⟨hw,trivial,hw',?_⟩
    split_ifs
    · exact correctionFinish_width w B B M hw' hw1 hw6 (by omega)
    · have hsub := hw1.sub hw3
      refine ⟨hw',trivial,?_⟩
      apply correctionFinish_width _ (B+B+1) B M
      · exact hw'.update 1 (hsub.mono (by omega))
      · exact hsub
      · simpa [w,Instruction.update,BinaryOp.eval] using h6
      · omega
  · let w := Function.update v 4 ((v 3).sub (v 0))
    have h4 : (w 4).Width (B+B+1) := by simpa only [w,Function.update_self] using h3.sub h0
    have hw' : WidthBank dftRegisters M w := hw.update 4 ((h3.sub h0).mono (by omega))
    have hw1 : (w 1).Width B := by simpa [w] using h1
    have hw6 : (w 6).Width B := by simpa [w] using h6
    have hadd := hw1.add h4
    refine ⟨hw,trivial,hw',trivial,?_⟩
    apply correctionFinish_width _ (B+(B+B+1)+1) B M
    · exact hw'.update 1 (hadd.mono (by omega))
    · exact hadd
    · simpa [w,Instruction.update,BinaryOp.eval] using h6
    · omega

theorem correctionControl_width (v : ℕ→Parts) (B I M : ℕ)
    (hw : WidthBank dftRegisters M v)
    (h0 : (v 0).Width B) (h1 : (v 1).Width B) (h3 : (v 3).Width B)
    (h6 : (v 6).Width B) (h7 : (v 7).Width 1) (h8 : (v 8).Width I)
    (hfit : 4*B+I+12≤M) : correctionControl.WidthTrace dftRegisters M v := by
  let w := Function.update v 8 ((v 8).sub (v 7))
  have hw' : WidthBank dftRegisters M w := hw.update 8 ((h8.sub h7).mono (by omega))
  refine ⟨hw,trivial,?_⟩
  apply correctionSelect_width w B (I+2) M hw'
  · simpa [w] using h0
  · simpa [w] using h1
  · simpa [w] using h3
  · simpa [w] using h6
  · simpa [w] using h7
  · simpa only [w,Function.update_self] using h8.sub h7
  · omega

#print axioms correctionControl_width
end Maxwell.Continuum.Profile.Runtime
