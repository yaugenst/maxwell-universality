import Maxwell.Certificate.PointWitness.Gram
namespace Maxwell.Certificate.PointWitness
noncomputable section
open Matrix
private def gramLowerL : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; (12726570293075289356076593750000000 / 170146440879377825811645034657534496353), 1]
private def gramLowerD : Fin 2 → ℝ := ![(170146440879377825811645034657534496353 / 170141183460469231731687303715884105728000000000000), (7413393654353989123664912132674580286699602478902927968624947859978649525471529 / 7410922704077850752299336485512985954404767140032926774622862238202440296955904000000000000)]
theorem gramLower_psd : (pointGram - ((999999999999 / 1000000000000) : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef := by
  apply real_ldl_sound _ gramLowerL gramLowerD
  · ext i j
    simp only [ldl_apply]
    fin_cases i <;> fin_cases j <;> norm_num [pointGram, gramLowerL, gramLowerD,
      Fin.sum_univ_succ, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]
  · intro i
    fin_cases i <;> norm_num [gramLowerD]
end
end Maxwell.Certificate.PointWitness
