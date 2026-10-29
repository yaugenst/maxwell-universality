import Maxwell.Certificate.GlobalDerivativeKernel
import Maxwell.Certificate.GlobalDerivative
import Maxwell.Certificate.DyadicKernelVectorSound

namespace Maxwell.Certificate.DyadicKernel.Derivative

open Matrix FourierBinding GlobalDerivative
open Maxwell.Spectral BoxCrossNorm BoxSymbols
open Maxwell.Spectral.PeriodicYee (Momentum Direction)

theorem integerAt_contains (p : ℕ) (n : ℤ) :
    (integerAt p n).toDyadic.Contains p (n : ℂ) := by
  simp [integerAt, Rectangle.toDyadic, DyadicRectangle.Contains]

theorem axisRound_contains {p : ℕ} {d : Triple} {theta : Rectangle}
    {c : Momentum} {a : Direction} {f : Frequency}
    (hd : ∀ j, (d.toVector j).Contains p (symbol c f j))
    (ht : theta.toDyadic.Contains p (Complex.I*(phaseScale : ℂ))) (j : Direction) :
    ((axisRound p a theta d).toVector j).Contains p (axisSymbol c a f j) := by
  rw [← Triple.toDyadic_get]
  simp only [axisRound, Triple.get_ofFn, axisSymbol]
  by_cases hj : j = a
  · simp only [hj, ite_true]
    apply mulRound_contains
    · rw [toDyadic_add, Triple.toDyadic_get]
      exact DyadicRectangle.add_contains (hd a) (by simpa using integerAt_contains p 1)
    · exact ht
  · simp only [hj, ite_false]
    exact DyadicRectangle.zero_contains p

theorem curlRow_contains_cross {p : ℕ} {d : Triple} {δ : Fin 3 → ℂ}
    (hd : ∀ j, (d.toVector j).Contains p (δ j)) (i j : Fin 3) :
    ((curlRow d i).get j).toDyadic.Contains p (crossMatrix δ i j) := by
  have he : ((curlRow d i).get j).toDyadic = DyadicRectangle.curlMatrix d.toVector i j := by
    fin_cases i <;> fin_cases j <;> rfl
  rw [he]
  fin_cases i <;> fin_cases j <;>
    simp only [DyadicRectangle.curlMatrix, crossMatrix] <;>
    first | exact DyadicRectangle.zero_contains p | exact hd _ |
      exact DyadicRectangle.neg_contains (hd _)

/-- The arithmetic curl evaluator is valid for arbitrary complex symbols,
including the sparse derivative `dp`, not only for a Bloch phase symbol. -/
theorem curlRound_contains_cross {p : ℕ} {adjoint : Bool} {d u : Triple}
    {δ v : Fin 3 → ℂ}
    (hd : ∀ j, (d.toVector j).Contains p (δ j))
    (hu : ∀ j, (u.toVector j).Contains p (v j)) (i : Fin 3) :
    ((curlRound p adjoint d u).toVector i).Contains p
      (((if adjoint then (crossMatrix δ).conjTranspose else crossMatrix δ) *ᵥ v) i) := by
  rw [← Triple.toDyadic_get]
  simp only [curlRound, Triple.get_ofFn]
  apply dotRound_fin_contains
  · intro j
    cases adjoint
    · exact curlRow_contains_cross hd i j
    · exact DyadicRectangle.conjugate_contains (curlRow_contains_cross hd j i)
  · simpa only [Triple.toDyadic_get] using hu

theorem projectionPrimeRound_contains {p : ℕ} {d dp u result : Triple} {lap : Rectangle}
    {δ δp v : Fin 3 → ℂ} {l : ℝ}
    (h : projectionPrimeRound p d dp u lap = some result)
    (hd : ∀ j, (d.toVector j).Contains p (δ j))
    (hp : ∀ j, (dp.toVector j).Contains p (δp j))
    (hu : ∀ j, (u.toVector j).Contains p (v j))
    (hl : lap.toDyadic.Contains p (l : ℂ)) (i : Fin 3) :
    (result.toVector i).Contains p (star (δ i)*((∑ j, δp j*v j)/(l : ℂ))) := by
  cases he : divRound p (dotTriple p dp u) lap with
  | none => simp [projectionPrimeRound, he] at h
  | some z =>
      simp [projectionPrimeRound, he] at h
      subst result
      rw [← Triple.toDyadic_get, Triple.get_ofFn]
      apply mulRound_contains
      · rw [toDyadic_conjugate, Triple.toDyadic_get]
        exact DyadicRectangle.conjugate_contains (hd i)
      · exact divRound_contains he (dotTriple_contains hp hu) hl

theorem gradientRound_contains {p : ℕ} {d result : Triple} {root : Rectangle}
    {δ : Fin 3 → ℂ} {r : ℝ}
    (h : gradientRound p d root = some result)
    (hd : ∀ j, (d.toVector j).Contains p (δ j))
    (hr : root.toDyadic.Contains p (r : ℂ)) (i : Fin 3) :
    (result.toVector i).Contains p (8*star (δ i)/(r : ℂ)) := by
  cases he : divideTriple p (Triple.ofFn fun j => conjugate (d.get j))
      (Triple.ofFn fun _ => root) with
  | none => simp [gradientRound, he] at h
  | some z =>
      simp [gradientRound, he] at h
      subst result
      rw [← Triple.toDyadic_get, Triple.get_ofFn]
      have hz := divideTriple_contains (v := fun j => star (δ j)) (m := fun _ => r) he
        (by intro j; rw [← Triple.toDyadic_get, Triple.get_ofFn,
          toDyadic_conjugate, Triple.toDyadic_get]; exact DyadicRectangle.conjugate_contains (hd j))
        (by intro j; rw [← Triple.toDyadic_get, Triple.get_ofFn]; exact hr) i
      rw [← Triple.toDyadic_get] at hz
      convert mulRound_contains (integerAt_contains p 8) hz using 1
      push_cast
      ring

theorem addTriple_contains {p : ℕ} {u v : Triple} {x y : Fin 3 → ℂ}
    (hu : ∀ j, (u.toVector j).Contains p (x j))
    (hv : ∀ j, (v.toVector j).Contains p (y j)) (i : Fin 3) :
    ((addTriple u v).toVector i).Contains p (x i+y i) := by
  rw [← Triple.toDyadic_get]
  simp only [addTriple, Triple.get_ofFn, toDyadic_add, Triple.toDyadic_get]
  exact DyadicRectangle.add_contains (hu i) (hv i)

theorem scaledAddRound_contains {p : ℕ} {u v : Triple} {s : Rectangle}
    {x y : Fin 3 → ℂ} {z : ℂ}
    (hu : ∀ j, (u.toVector j).Contains p (x j))
    (hs : s.toDyadic.Contains p z)
    (hv : ∀ j, (v.toVector j).Contains p (y j)) (i : Fin 3) :
    ((scaledAddRound p u s v).toVector i).Contains p (x i+z*y i) := by
  rw [← Triple.toDyadic_get]
  simp only [scaledAddRound, Triple.get_ofFn, toDyadic_add]
  apply DyadicRectangle.add_contains
  · simpa only [Triple.toDyadic_get] using hu i
  · exact mulRound_contains hs (by simpa only [Triple.toDyadic_get] using hv i)

theorem magneticPrimeRound_contains {p : ℕ} {d dp w wp : Triple}
    {δ δp v vp : Fin 3 → ℂ}
    (hd : ∀ j, (d.toVector j).Contains p (δ j))
    (hp : ∀ j, (dp.toVector j).Contains p (δp j))
    (hw : ∀ j, (w.toVector j).Contains p (v j))
    (hwp : ∀ j, (wp.toVector j).Contains p (vp j)) (i : Fin 3) :
    ((magneticPrimeRound p d dp w wp).toVector i).Contains p
      ((crossMatrix δp *ᵥ v) i+(crossMatrix δ *ᵥ vp) i) :=
  addTriple_contains (curlRound_contains_cross (adjoint := false) hp hw)
    (curlRound_contains_cross (adjoint := false) hd hwp) i

theorem curlPrimeRound_contains_field {p : ℕ} {dp field : Triple}
    {c : Momentum} {a : Direction} {f : Frequency} {u : FourierSpace}
    (hp : ∀ j, (dp.toVector j).Contains p (axisSymbol c a f j))
    (hu : ∀ j, (field.toVector j).Contains p (u (j,f))) (i : Direction) :
    ((curlRound p true dp field).toVector i).Contains p (curlPrimeField c a u (i,f)) := by
  rw [curlPrimeField_apply]
  exact curlRound_contains_cross (adjoint := true) hp hu i

theorem projectionPrimeRound_contains_field {p : ℕ} {d dp field result : Triple}
    {lap : Rectangle} {c : Momentum} {a : Direction} {f : Frequency} {u : FourierSpace}
    (h : projectionPrimeRound p d dp field lap = some result)
    (hd : ∀ j, (d.toVector j).Contains p (symbol c f j))
    (hp : ∀ j, (dp.toVector j).Contains p (axisSymbol c a f j))
    (hu : ∀ j, (field.toVector j).Contains p (u (j,f)))
    (hl : lap.toDyadic.Contains p (laplacianSymbol c f : ℂ)) (i : Direction) :
    (result.toVector i).Contains p (projectionPrimeField c a u (i,f)) :=
  projectionPrimeRound_contains h hd hp hu hl i

theorem gradientRound_contains_center {p : ℕ} {d result : Triple} {root : Rectangle}
    {c : Momentum} {f : Frequency}
    (h : gradientRound p d root = some result)
    (hd : ∀ j, (d.toVector j).Contains p (symbol c f j))
    (hr : root.toDyadic.Contains p (Real.sqrt (laplacianSymbol c f) : ℂ)) (i : Direction) :
    (result.toVector i).Contains p (BoxFourierProjection.normalizedGradient c f i) := by
  rw [normalizedGradient_coordinate]
  exact gradientRound_contains h hd hr i

theorem gradientRound_contains_prime {p : ℕ} {dp result : Triple} {root : Rectangle}
    {c : Momentum} {a : Direction} {f : Frequency}
    (h : gradientRound p dp root = some result)
    (hp : ∀ j, (dp.toVector j).Contains p (axisSymbol c a f j))
    (hr : root.toDyadic.Contains p (Real.sqrt (laplacianSymbol c f) : ℂ)) (i : Direction) :
    (result.toVector i).Contains p (BoxFourierProjection.normalizedGradientLinear c (BoxLinear.axis a) f i) := by
  rw [normalizedGradientLinear_coordinate]
  exact gradientRound_contains h hp hr i

theorem magneticPrimeRound_contains_field {p : ℕ} {d dp weighted weightedPrime : Triple}
    {material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ} {c : Momentum}
    {a : Direction} {f : Frequency} {u : FourierSpace}
    (hd : ∀ j, (d.toVector j).Contains p (symbol c f j))
    (hp : ∀ j, (dp.toVector j).Contains p (axisSymbol c a f j))
    (hw : ∀ j, (weighted.toVector j).Contains p (GlobalCenter.weightedField material c u (j,f)))
    (hwp : ∀ j, (weightedPrime.toVector j).Contains p (weightedPrimeField material c a u (j,f)))
    (i : Direction) :
    ((magneticPrimeRound p d dp weighted weightedPrime).toVector i).Contains p
      (magneticPrimeField material c a u (i,f)) := by
  rw [magneticPrimeField_apply]
  exact magneticPrimeRound_contains hd hp hw hwp i

theorem auxiliaryPrimeRound_contains_field {p : ℕ} {magnetic projection : Triple} {s : Rectangle}
    {material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ} {c : Momentum}
    {a : Direction} {f : Frequency} {u : FourierSpace}
    (hm : ∀ j, (magnetic.toVector j).Contains p (magneticPrimeField material c a u (j,f)))
    (hs : s.toDyadic.Contains p (1/32 : ℂ))
    (hp : ∀ j, (projection.toVector j).Contains p (projectionPrimeField c a u (j,f)))
    (i : Direction) :
    ((scaledAddRound p magnetic s projection).toVector i).Contains p
      (auxiliaryPrimeField material c a u (i,f)) :=
  scaledAddRound_contains hm hs hp i

theorem gradientMagneticRound_contains_field {p : ℕ} {d weightedPrime : Triple}
    {material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ} {c : Momentum}
    {a : Direction} {f : Frequency} {low : Finset Frequency} {g : BoxGradient.Coefficients}
    (hd : ∀ j, (d.toVector j).Contains p (symbol c f j))
    (hwp : ∀ j, (weightedPrime.toVector j).Contains p
      (weightedPrimeField material c a (BoxMixedForm.gradientOperator c low g) (j,f)))
    (i : Direction) :
    ((curlRound p false d weightedPrime).toVector i).Contains p
      (gradientMagneticPrimeField material c a low g (i,f)) := by
  change ((curlRound p false d weightedPrime).toVector i).Contains p
    ((frequencyCurl c *ᵥ _) (i,f))
  rw [frequencyCurl_mulVec]
  exact curlRound_contains (adjoint := false) hd hwp i

theorem mixedPrimeRound_contains_field {p : ℕ} {magnetic gradient : Triple} {s : Rectangle}
    {material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ} {c : Momentum}
    {a : Direction} {f : Frequency} {low : Finset Frequency} {g : BoxGradient.Coefficients}
    (hm : ∀ j, (magnetic.toVector j).Contains p (gradientMagneticPrimeField material c a low g (j,f)))
    (hs : s.toDyadic.Contains p (1/32 : ℂ))
    (hg : ∀ j, (gradient.toVector j).Contains p (gradientPrimeField c a low g (j,f)))
    (i : Direction) :
    ((scaledAddRound p magnetic s gradient).toVector i).Contains p
      (mixedPrimeField material c a low g (i,f)) :=
  scaledAddRound_contains hm hs hg i

end Maxwell.Certificate.DyadicKernel.Derivative
