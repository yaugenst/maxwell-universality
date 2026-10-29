import Maxwell.Logical.SourceSquare
import Maxwell.Logical.CompilerAmplitude

/-! Euclidean inverse estimates for the actual square source circuit. -/

namespace Maxwell.Logical

noncomputable section

/-- The concrete square circuit in its Euclidean norm. -/
def sourceSquareOperator (S : Source.SparseSystem) (precision : ℕ) :
    EuclideanSpace ℝ (Fin (sourceCircuit S precision).size) →L[ℝ]
      EuclideanSpace ℝ (Fin (sourceCircuit S precision).size) :=
  ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp
    ((sourceSquareMap S precision).comp (WithLp.linearEquiv 2 ℝ _).toLinearMap)).toContinuousLinearMap

@[simp] theorem sourceSquareOperator_apply (S : Source.SparseSystem) (precision : ℕ)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size)) :
    sourceSquareOperator S precision state =
      WithLp.toLp 2 (sourceSquareMap S precision (WithLp.ofLp state)) := rfl

/-- The gate residual is bounded by the complete square-system residual,
when the input is read from the actual input coordinates. -/
theorem sourceSquare_gate_residual (S : Source.SparseSystem) (precision : ℕ)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size))
    (j : Fin (sourceCircuit S precision).size) :
    |(sourceCircuit S precision).circuit.residual
      ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state))
      (WithLp.ofLp state) j| ≤ ‖sourceSquareOperator S precision state‖ := by
  let c := (sourceCircuit S precision).circuit
  by_cases hj : j.val < S.n
  · let i : Fin S.n := ⟨j.val, hj⟩
    have he : c.inputIndex i = j := Fin.ext (c.inputIndex_value i)
    rw [← he, c.residual_at_input]
    simp [c, Circuit.originalInput]
  · rw [c.residual_noninput _ _ _ (Nat.le_of_not_gt hj)]
    have h := PiLp.norm_apply_le (sourceSquareOperator S precision state) j
    simpa only [sourceSquareOperator_apply, WithLp.ofLp_toLp, Real.norm_eq_abs,
      sourceSquareMap, Circuit.squareMap_noninput _ _ _ _ (Nat.le_of_not_gt hj)] using h

/-- Every selected output is a coordinate of the complete square residual. -/
theorem sourceSquare_output_bound (S : Source.SparseSystem) (precision : ℕ)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size)) (i : Fin S.n) :
    |state (sourceOutput S precision i)| ≤ ‖sourceSquareOperator S precision state‖ := by
  have h := PiLp.norm_apply_le (sourceSquareOperator S precision state)
    ((sourceCircuit S precision).circuit.inputIndex i)
  simpa only [sourceSquareOperator_apply, WithLp.ofLp_toLp, Real.norm_eq_abs,
    sourceSquareMap, Circuit.squareMap_input] using h

/-- The actual rounded source output is controlled by all square equations. -/
theorem sourceSquare_rounded_output_bound (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hs : 1 ≤ precision)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size)) (i : Fin S.n) :
    |roundedProduct S precision
      ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state)) i| ≤
      ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
        ‖sourceSquareOperator S precision state‖ := by
  have h := sourceCircuit_arbitrary_residual S hm precision hs
    ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state))
    (WithLp.ofLp state) ‖sourceSquareOperator S precision state‖ (norm_nonneg _)
    (sourceSquare_gate_residual S precision state)
  have hi : i.val < (sourceCircuit S precision).outputs.length := by
    rw [sourceCircuit_output_count]
    exact i.isLt
  have hv := h.get hi (by simp)
  simp only [List.get_ofFn] at hv
  change |state (sourceOutput S precision i) - roundedProduct S precision
    ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state)) i| ≤ _ at hv
  calc
    _ ≤ |state (sourceOutput S precision i) -
        roundedProduct S precision
          ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state)) i| +
        |state (sourceOutput S precision i)| := by
      let a := state (sourceOutput S precision i)
      let b := roundedProduct S precision
        ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state)) i
      change |b| ≤ |a - b| + |a|
      calc
        |b| = |(b - a) + a| := by congr 1; ring
        _ ≤ |b - a| + |a| := abs_add_le _ _
        _ = _ := by rw [abs_sub_comm]
    _ ≤ _ := by nlinarith [sourceSquare_output_bound S precision state i]

/-- Input amplification follows from the proved inverse bound for the actual
rounded matrix, including the full gate residual. -/
theorem sourceSquare_input_norm_le (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2)
    (L : ℝ) (hL : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size)) :
    ‖WithLp.toLp 2 ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state))‖ ≤
      2 * L * Real.sqrt S.n * ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
        ‖sourceSquareOperator S precision state‖ := by
  obtain ⟨u, hu, hnorm⟩ := Normalization.roundedOperator_unit S hunit (by omega) precision hsmall
  let x : EuclideanSpace ℝ (Fin S.n) :=
    WithLp.toLp 2 ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state))
  have hux : (u : EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n)) x =
      WithLp.toLp 2 (roundedProduct S precision (WithLp.ofLp x)) := by
    rw [hu]
    rfl
  have hx : x = (↑u⁻¹ : EuclideanSpace ℝ (Fin S.n) →L[ℝ]
      EuclideanSpace ℝ (Fin S.n)) ((u : EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n)) x) := by
    change x = (↑u⁻¹ * ↑u : EuclideanSpace ℝ (Fin S.n) →L[ℝ]
      EuclideanSpace ℝ (Fin S.n)) x
    simp
  have hout := Target.WeightedDecoder.euclidean_norm_le_sqrt_card
    (WithLp.toLp 2 (roundedProduct S precision (WithLp.ofLp x)))
    (((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
      ‖sourceSquareOperator S precision state‖) (by positivity)
    (sourceSquare_rounded_output_bound S hm precision hs state)
  have hnorm' : ‖(↑u⁻¹ : EuclideanSpace ℝ (Fin S.n) →L[ℝ]
      EuclideanSpace ℝ (Fin S.n))‖ ≤ 2 * L := by linarith
  have hL0 : 0 ≤ 2 * L := (norm_nonneg _).trans hnorm'
  change ‖x‖ ≤ _
  calc
    ‖x‖ = ‖(↑u⁻¹ : EuclideanSpace ℝ (Fin S.n) →L[ℝ]
      EuclideanSpace ℝ (Fin S.n)) ((u : EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n)) x)‖ := congrArg norm hx
    _ ≤ ‖(↑u⁻¹ : EuclideanSpace ℝ (Fin S.n) →L[ℝ]
      EuclideanSpace ℝ (Fin S.n))‖ * ‖(u : EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n)) x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (2 * L) * (Real.sqrt S.n *
        (((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
          ‖sourceSquareOperator S precision state‖)) :=
      mul_le_mul hnorm' (by simpa only [hux] using hout) (norm_nonneg _) hL0
    _ = _ := by ring


private lemma sqrt_nat_le_self_of_two_le (d : ℕ) (hd : 2 ≤ d) :
    Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

private lemma sqrt_nat_mul_le_self (n d : ℕ) (hnd : n ≤ d) :
    Real.sqrt (d : ℝ) * Real.sqrt (n : ℝ) ≤ (d : ℝ) := by
  have hn : (n : ℝ) ≤ d := by exact_mod_cast hnd
  calc
    Real.sqrt (d : ℝ) * Real.sqrt (n : ℝ) ≤ Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hn) (Real.sqrt_nonneg _)
    _ = d := Real.mul_self_sqrt (by positivity)

private lemma source_inverse_algebra (n d : ℕ) (hnd : n ≤ d) (hd : 2 ≤ d)
    (L R : ℝ) (hL : 1 ≤ L) (hR : 0 ≤ R) :
    Real.sqrt (d : ℝ) *
      (((d : ℝ) + 1) * (2 * L * Real.sqrt (n : ℝ) * (((d : ℝ) + 1)^2 + 1) * R) +
        ((d : ℝ) + 1)^2 * R) ≤
      16 * L * (d : ℝ)^4 * R := by
  have hroot := sqrt_nat_le_self_of_two_le d hd
  have hroots := sqrt_nat_mul_le_self n d hnd
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd₀ : 0 ≤ (d : ℝ) := by positivity
  have hL₀ : 0 ≤ L := by linarith
  have hD : (d : ℝ) + 1 ≤ (3 / 2 : ℝ) * d := by linarith
  have hD₂ : ((d : ℝ) + 1)^2 + 1 ≤ (5 / 2 : ℝ) * (d : ℝ)^2 := by nlinarith
  have hD₂' : ((d : ℝ) + 1)^2 ≤ (5 / 2 : ℝ) * (d : ℝ)^2 := by linarith
  have hD₃ : (d : ℝ)^3 ≤ (d : ℝ)^4 := by
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) - 1 by linarith)
      (show 0 ≤ (d : ℝ)^3 by positivity)]
  calc
    _ = (2 * L * ((d : ℝ) + 1) * (((d : ℝ) + 1)^2 + 1) * R) *
          (Real.sqrt (d : ℝ) * Real.sqrt (n : ℝ)) +
          (((d : ℝ) + 1)^2 * R) * Real.sqrt (d : ℝ) := by ring
    _ ≤ (2 * L * ((d : ℝ) + 1) * (((d : ℝ) + 1)^2 + 1) * R) * (d : ℝ) +
          (((d : ℝ) + 1)^2 * R) * (d : ℝ) := by gcongr
    _ ≤ (2 * L * ((3 / 2 : ℝ) * d) * ((5 / 2 : ℝ) * (d : ℝ)^2) * R) * (d : ℝ) +
          (((5 / 2 : ℝ) * (d : ℝ)^2) * R) * (d : ℝ) := by gcongr
    _ = (15 / 2 : ℝ) * L * R * (d : ℝ)^4 + (5 / 2 : ℝ) * R * (d : ℝ)^3 := by ring
    _ ≤ (15 / 2 : ℝ) * L * R * (d : ℝ)^4 + (5 / 2 : ℝ) * L * R * (d : ℝ)^4 := by
      apply add_le_add le_rfl
      calc
        _ ≤ (5 / 2 : ℝ) * R * (d : ℝ)^4 := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg hR (show 0 ≤ (d : ℝ)^4 by positivity)]
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hL₀ hR) (show 0 ≤ (d : ℝ)^4 by positivity)]

/-- The actual compiled square source has the advertised polynomial inverse
estimate. Both its internal states and its gate errors are included. -/
theorem sourceSquare_norm_le (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2)
    (L : ℝ) (hL : 1 ≤ L)
    (hcondition : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size)) :
    ‖state‖ ≤ 16 * L * ((sourceCircuit S precision).size : ℝ)^4 *
      ‖sourceSquareOperator S precision state‖ := by
  let d := (sourceCircuit S precision).size
  let X := 2 * L * Real.sqrt S.n * (((d : ℝ) + 1)^2 + 1) *
    ‖sourceSquareOperator S precision state‖
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hx : ∀ i, |(sourceCircuit S precision).circuit.originalInput
      (WithLp.ofLp state) i| ≤ X := by
    intro i
    have hi := PiLp.norm_apply_le
      (WithLp.toLp 2 ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state))) i
    simpa only [Real.norm_eq_abs] using hi.trans
      (sourceSquare_input_norm_le S hunit hm precision hs hsmall L hcondition state)
  have hstate := Target.WeightedDecoder.euclidean_norm_le_sqrt_card state
    (((d : ℝ) + 1) * X + ((d : ℝ) + 1)^2 * ‖sourceSquareOperator S precision state‖)
    (by positivity)
    (sourceCircuit_state_bound S precision
      ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state))
      (WithLp.ofLp state) X ‖sourceSquareOperator S precision state‖ hX (norm_nonneg _) hx
      (sourceSquare_gate_residual S precision state))
  exact hstate.trans (source_inverse_algebra S.n d
    (sourceCircuit S precision).circuit.inputs_le_size
    (sourceCircuit_size_two_le S hm precision) L
    ‖sourceSquareOperator S precision state‖ hL (norm_nonneg _))

/-- Transport the actual square-system equivalence to the Euclidean space. -/
def sourceSquareEuclideanEquiv (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    EuclideanSpace ℝ (Fin (sourceCircuit S precision).size) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (sourceCircuit S precision).size) :=
  (((WithLp.linearEquiv 2 ℝ _).trans
    (sourceSquareEquiv S hunit hm precision hs hsmall)).trans
      (WithLp.linearEquiv 2 ℝ _).symm).toContinuousLinearEquiv

@[simp] theorem sourceSquareEuclideanEquiv_apply (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size)) :
    sourceSquareEuclideanEquiv S hunit hm precision hs hsmall state =
      sourceSquareOperator S precision state := rfl

/-- Operator norm bound for the inverse of the actual encoded square system. -/
theorem sourceSquare_inverse_norm_le (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2)
    (L : ℝ) (hL : 1 ≤ L)
    (hcondition : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L) :
    ‖(sourceSquareEuclideanEquiv S hunit hm precision hs hsmall).symm.toContinuousLinearMap‖ ≤
      16 * L * ((sourceCircuit S precision).size : ℝ)^4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro r
  have h := sourceSquare_norm_le S hunit hm precision hs hsmall L hL hcondition
    ((sourceSquareEuclideanEquiv S hunit hm precision hs hsmall).symm r)
  have he : sourceSquareOperator S precision
      ((sourceSquareEuclideanEquiv S hunit hm precision hs hsmall).symm r) = r := by
    rw [← sourceSquareEuclideanEquiv_apply S hunit hm precision hs hsmall]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  simpa only [he, ContinuousLinearEquiv.coe_coe] using h

end
end Maxwell.Logical
