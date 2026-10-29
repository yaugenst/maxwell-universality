import Maxwell.Certificate.PointWitness.Gram
namespace Maxwell.Certificate.PointWitness
noncomputable section
open Matrix
private def gramUpperL : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; (-12726570293075289356076593750000000 / 170135926041560637651729572774233715103), 1]
private def gramUpperD : Fin 2 → ℝ := ![(170135926041560637651729572774233715103 / 170141183460469231731687303715884105728000000000000), (7407993837800308423848147195686048263747395777222334943073039127050649525471529 / 7410464718298622261917749595599066250813790897169065422427708514810440296955904000000000000)]
theorem gramUpper_psd : (((1000000000001 / 1000000000000) : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - pointGram).PosSemidef := by
  apply real_ldl_sound _ gramUpperL gramUpperD
  · ext i j
    simp only [ldl_apply]
    fin_cases i <;> fin_cases j <;> norm_num [pointGram, gramUpperL, gramUpperD,
      Fin.sum_univ_succ, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]
  · intro i
    fin_cases i <;> norm_num [gramUpperD]
end
end Maxwell.Certificate.PointWitness
