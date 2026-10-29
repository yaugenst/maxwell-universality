import Maxwell.Certificate.GlobalWeightKernel
import Maxwell.Certificate.DyadicKernelSqrtSound
import Maxwell.Certificate.GlobalDerivativeSound

namespace Maxwell.Certificate.DyadicKernel.Weight

theorem inverseLaplacian_contains {p : ℕ} {lap result : Rectangle} {x : ℝ}
    (h : inverseLaplacian p lap = some result) (hl : lap.toDyadic.Contains p (x:ℂ)) :
    result.toDyadic.Contains p ((1/x:ℝ):ℂ) := by
  simpa only [Int.cast_one,Complex.ofReal_div,Complex.ofReal_one] using
    divRound_contains h (Derivative.integerAt_contains p 1) hl

theorem inverseRoot_contains {p : ℕ} {lap result : Rectangle} {x : ℝ}
    (h : inverseRoot p lap = some result) (hl : lap.toDyadic.Contains p (x:ℂ)) :
    result.toDyadic.Contains p ((1/Real.sqrt x:ℝ):ℂ) := by
  obtain ⟨root,hr,hdiv⟩ :=
    (by simpa only [inverseRoot,bind,Option.bind_eq_some_iff] using h :
      ∃ root, sqrtRound p lap = some root ∧ divRound p (Derivative.integerAt p 1) root = some result)
  simpa only [Int.cast_one,Complex.ofReal_div,Complex.ofReal_one] using
    divRound_contains hdiv (Derivative.integerAt_contains p 1) (sqrtRound_contains hr hl)

theorem high_contains {rho : ℕ} {lap result : Rectangle} {x : ℝ}
    (h : high rho lap = some result) (hl : lap.toDyadic.Contains 52 (x:ℂ)) :
    result.toDyadic.Contains 52 ((1/Real.sqrt (x/rho-1/64):ℝ):ℂ) := by
  obtain ⟨scaled,hs,hroot⟩ :=
    (by simpa only [high,bind,Option.bind_eq_some_iff] using h :
      ∃ scaled, divRound 52 lap (Derivative.integerAt 52 rho) = some scaled ∧
        inverseRoot 52 (add scaled ⟨-70368744177664,0,0⟩) = some result)
  have hscaled : scaled.toDyadic.Contains 52 ((x/rho:ℝ):ℂ) := by
    simpa only [Int.cast_natCast,Complex.ofReal_div,Complex.ofReal_natCast] using
      divRound_contains hs hl (Derivative.integerAt_contains 52 rho)
  apply inverseRoot_contains hroot
  rw [toDyadic_add]
  have hshift : (⟨-70368744177664,0,0⟩:Rectangle).toDyadic.Contains 52 (-1/64:ℂ) := by
    norm_num [Rectangle.toDyadic,DyadicRectangle.Contains]
  convert DyadicRectangle.add_contains hscaled hshift using 1
  push_cast
  ring

end Maxwell.Certificate.DyadicKernel.Weight
