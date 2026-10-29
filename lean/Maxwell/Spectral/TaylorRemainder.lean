import Maxwell.Spectral.ScalarBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Operator Taylor-tail estimates for the local spectral polynomial

Every norm here is the operator norm of a bounded map between Hilbert spaces.
In particular, specializing to Euclidean spaces does not use the entrywise
matrix norm. The coefficient bounds are explicit hypotheses. The series
below are proved summable before their sums are used. Identifying these
series with the expansion of the concrete Yee fiber is a separate theorem.
-/

namespace Maxwell.Spectral

noncomputable section

variable {𝕜 H V : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

omit [CompleteSpace H] [CompleteSpace V] in
/-- Operator-norm composition with explicit scalar bounds. -/
theorem norm_comp_of_bounds (A : H →L[𝕜] H) (X : V →L[𝕜] H)
    (a x : ℝ) (hA : ‖A‖ ≤ a) (hX : ‖X‖ ≤ x) (ha : 0 ≤ a) :
    ‖A.comp X‖ ≤ a * x :=
  (ContinuousLinearMap.opNorm_comp_le A X).trans
    (mul_le_mul hA hX (norm_nonneg X) ha)

/-- The rectangular compression is bounded in the Hilbert operator norm. -/
theorem norm_compression_of_bounds (L R : V →L[𝕜] H) (A : H →L[𝕜] H)
    (l a x : ℝ) (hL : ‖L‖ ≤ l) (hA : ‖A‖ ≤ a) (hR : ‖R‖ ≤ x)
    (hl : 0 ≤ l) (ha : 0 ≤ a) :
    ‖L.adjoint.comp (A.comp R)‖ ≤ l * (a * x) := by
  have hadj : ‖L.adjoint‖ = ‖L‖ := LinearIsometryEquiv.norm_map _ _
  calc
    _ ≤ ‖L.adjoint‖ * ‖A.comp R‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖L‖ * ‖A.comp R‖ := by rw [hadj]
    _ ≤ l * (a * x) :=
      mul_le_mul hL (norm_comp_of_bounds A R a x hA hR ha)
        (norm_nonneg _) hl

/-- Degree-`j+1` coefficient of `(A(q)-E)(Φ-Y(q))`, beyond its
constant and cancelled linear terms. -/
def residualTaylorTerm (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H) (j : ℕ) :
    V →L[𝕜] H :=
  (A (j + 1)).comp Φ - (A j).comp Y

/-- Degree-`j+2` coefficient of the compressed quadratic form. -/
def compressedTaylorTerm (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H) (j : ℕ) :
    V →L[𝕜] V :=
  Φ.adjoint.comp ((A (j + 2)).comp Φ) -
    Φ.adjoint.comp ((A (j + 1)).comp Y) -
    Y.adjoint.comp ((A (j + 1)).comp Φ) +
    Y.adjoint.comp ((A j).comp Y)

omit [CompleteSpace H] [CompleteSpace V] in
theorem residualTaylorTerm_norm (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H)
    (r : ℝ) (hr0 : 0 ≤ r) (hΦ : ‖Φ‖ ≤ 1) (hY : ‖Y‖ ≤ 3 * r)
    (hA : ∀ j, 1 ≤ j → ‖A j‖ ≤ taylorCoefficientMajorant j * r ^ j)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖residualTaylorTerm A Φ Y j‖ ≤
      taylorCoefficientMajorant (j + 1) * r ^ (j + 1) +
        3 * taylorCoefficientMajorant j * r ^ (j + 1) := by
  have ha0 := mul_nonneg (taylorCoefficientMajorant_nonnegative j) (pow_nonneg hr0 j)
  have ha1 := mul_nonneg (taylorCoefficientMajorant_nonnegative (j + 1))
    (pow_nonneg hr0 (j + 1))
  have hfirst := norm_comp_of_bounds (A (j + 1)) Φ
    (taylorCoefficientMajorant (j + 1) * r ^ (j + 1)) 1 (hA _ (by omega)) hΦ ha1
  have hsecond := norm_comp_of_bounds (A j) Y
    (taylorCoefficientMajorant j * r ^ j) (3 * r) (hA j hj) hY ha0
  calc
    _ ≤ ‖(A (j + 1)).comp Φ‖ + ‖(A j).comp Y‖ := norm_sub_le _ _
    _ ≤ (taylorCoefficientMajorant (j + 1) * r ^ (j + 1)) * 1 +
        (taylorCoefficientMajorant j * r ^ j) * (3 * r) := add_le_add hfirst hsecond
    _ = _ := by rw [pow_succ]; ring

theorem compressedTaylorTerm_norm (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H)
    (r : ℝ) (hr0 : 0 ≤ r) (hΦ : ‖Φ‖ ≤ 1) (hY : ‖Y‖ ≤ 3 * r)
    (hA : ∀ j, 1 ≤ j → ‖A j‖ ≤ taylorCoefficientMajorant j * r ^ j)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖compressedTaylorTerm A Φ Y j‖ ≤
      taylorCoefficientMajorant (j + 2) * r ^ (j + 2) +
        6 * taylorCoefficientMajorant (j + 1) * r ^ (j + 2) +
        9 * taylorCoefficientMajorant j * r ^ (j + 2) := by
  have ha0 := mul_nonneg (taylorCoefficientMajorant_nonnegative j) (pow_nonneg hr0 j)
  have ha1 := mul_nonneg (taylorCoefficientMajorant_nonnegative (j + 1))
    (pow_nonneg hr0 (j + 1))
  have ha2 := mul_nonneg (taylorCoefficientMajorant_nonnegative (j + 2))
    (pow_nonneg hr0 (j + 2))
  have hfirst := norm_compression_of_bounds Φ Φ (A (j + 2)) 1
    (taylorCoefficientMajorant (j + 2) * r ^ (j + 2)) 1
    hΦ (hA _ (by omega)) hΦ (by norm_num) ha2
  have hsecond := norm_compression_of_bounds Φ Y (A (j + 1)) 1
    (taylorCoefficientMajorant (j + 1) * r ^ (j + 1)) (3 * r)
    hΦ (hA _ (by omega)) hY (by norm_num) ha1
  have hthird := norm_compression_of_bounds Y Φ (A (j + 1)) (3 * r)
    (taylorCoefficientMajorant (j + 1) * r ^ (j + 1)) 1
    hY (hA _ (by omega)) hΦ (by positivity) ha1
  have hfourth := norm_compression_of_bounds Y Y (A j) (3 * r)
    (taylorCoefficientMajorant j * r ^ j) (3 * r)
    hY (hA j hj) hY (by positivity) ha0
  have htriangle : ‖compressedTaylorTerm A Φ Y j‖ ≤
      ‖Φ.adjoint.comp ((A (j + 2)).comp Φ)‖ +
      ‖Φ.adjoint.comp ((A (j + 1)).comp Y)‖ +
      ‖Y.adjoint.comp ((A (j + 1)).comp Φ)‖ +
      ‖Y.adjoint.comp ((A j).comp Y)‖ := by
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  unfold compressedTaylorTerm at htriangle ⊢
  simp only [pow_succ] at hfirst hsecond hthird ⊢
  nlinarith only [htriangle, hfirst, hsecond, hthird, hfourth]

def evenResidualTail (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H) (n : ℕ) :
    V →L[𝕜] H := residualTaylorTerm A Φ Y (3 + 2 * n)

def oddResidualTail (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H) (n : ℕ) :
    V →L[𝕜] H := residualTaylorTerm A Φ Y (2 + 2 * n)

def compressedTail (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H) (n : ℕ) :
    V →L[𝕜] V := compressedTaylorTerm A Φ Y (2 + 2 * n)

omit [CompleteSpace V] in
/-- The even residual remainder is an actual absolutely convergent operator
series, with the complete infinite-tail estimate. -/
theorem evenResidualTail_bound (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (hΦ : ‖Φ‖ ≤ 1) (hY : ‖Y‖ ≤ 3 * r)
    (hA : ∀ j, 1 ≤ j → ‖A j‖ ≤ taylorCoefficientMajorant j * r ^ j) :
    Summable (evenResidualTail A Φ Y) ∧
      ‖∑' n, evenResidualTail A Φ Y n‖ ≤ (2 / 25) * r ^ 4 := by
  obtain ⟨hs, ht⟩ := evenResidualMajorant_bound r hr0 hr
  have hbound : ∀ n, ‖evenResidualTail A Φ Y n‖ ≤ evenResidualMajorant r n := by
    intro n
    have h := residualTaylorTerm_norm A Φ Y r hr0 hΦ hY hA (3 + 2 * n) (by omega)
    have heq : 3 + 2 * n + 1 = 4 + 2 * n := by omega
    simpa [evenResidualTail, evenResidualMajorant, taylorTail, heq, mul_assoc] using h
  exact ⟨hs.of_norm_bounded hbound, (tsum_of_norm_bounded hs.hasSum hbound).trans ht⟩

omit [CompleteSpace V] in
/-- The odd residual series starts in degree three after exact linear
cancellation; that algebraic cancellation is not replaced by a tolerance. -/
theorem oddResidualTail_bound (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (hΦ : ‖Φ‖ ≤ 1) (hY : ‖Y‖ ≤ 3 * r)
    (hA : ∀ j, 1 ≤ j → ‖A j‖ ≤ taylorCoefficientMajorant j * r ^ j) :
    Summable (oddResidualTail A Φ Y) ∧
      ‖∑' n, oddResidualTail A Φ Y n‖ ≤ (17 / 20) * r ^ 3 := by
  obtain ⟨hs, ht⟩ := oddResidualMajorant_bound r hr0 hr
  have hbound : ∀ n, ‖oddResidualTail A Φ Y n‖ ≤ oddResidualMajorant r n := by
    intro n
    have h := residualTaylorTerm_norm A Φ Y r hr0 hΦ hY hA (2 + 2 * n) (by omega)
    have heq : 2 + 2 * n + 1 = 3 + 2 * n := by omega
    simpa [oddResidualTail, oddResidualMajorant, taylorTail, heq, mul_assoc] using h
  exact ⟨hs.of_norm_bounded hbound, (tsum_of_norm_bounded hs.hasSum hbound).trans ht⟩

/-- The compressed-form remainder is an absolutely convergent operator
series with the fourth-order bound used by the spectral polynomial. -/
theorem compressedTail_bound (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (hΦ : ‖Φ‖ ≤ 1) (hY : ‖Y‖ ≤ 3 * r)
    (hA : ∀ j, 1 ≤ j → ‖A j‖ ≤ taylorCoefficientMajorant j * r ^ j) :
    Summable (compressedTail A Φ Y) ∧
      ‖∑' n, compressedTail A Φ Y n‖ ≤ (13 / 5) * r ^ 4 := by
  obtain ⟨hs, ht⟩ := kRemainderMajorant_bound r hr0 hr
  have hbound : ∀ n, ‖compressedTail A Φ Y n‖ ≤ kRemainderMajorant r n := by
    intro n
    have h := compressedTaylorTerm_norm A Φ Y r hr0 hΦ hY hA (2 + 2 * n) (by omega)
    have heq1 : 2 + 2 * n + 1 = 3 + 2 * n := by omega
    have heq2 : 2 + 2 * n + 2 = 4 + 2 * n := by omega
    simpa [compressedTail, kRemainderMajorant, taylorTail, heq1, heq2, mul_assoc] using h
  exact ⟨hs.of_norm_bounded hbound, (tsum_of_norm_bounded hs.hasSum hbound).trans ht⟩

omit [CompleteSpace H] [CompleteSpace V] in
/-- Taking a convergent operator series commutes with composition on the
right by a fixed bounded operator. -/
theorem hasSum_comp_right (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H)
    (hA : HasSum A B) (X : V →L[𝕜] H) :
    HasSum (fun n => (A n).comp X) (B.comp X) := by
  simpa using hA.mapL ((ContinuousLinearMap.compL 𝕜 V H H).flip X)

omit [CompleteSpace H] [CompleteSpace V] in
/-- The residual series is derived from the original convergent operator
series; no equality with the desired remainder is assumed. -/
theorem residualTaylorTerm_hasSum (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H)
    (hA : HasSum A B) (Φ Y : V →L[𝕜] H) :
    HasSum (residualTaylorTerm A Φ Y) ((B - A 0).comp Φ - B.comp Y) := by
  have htail : HasSum (fun n => A (n + 1)) (B - A 0) := by
    simpa using (hasSum_nat_add_iff' 1).2 hA
  exact (hasSum_comp_right _ _ htail Φ).sub (hasSum_comp_right A B hA Y)

omit [CompleteSpace H] [CompleteSpace V] in
/-- Reassemble both residual parities and the exact quadratic term. The
constant and linear coefficients are kept exact rather than norm-bounded. -/
theorem residual_series_identity (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H)
    (hA : HasSum A B) (Φ Y : V →L[𝕜] H)
    (hcancel : (A 0).comp Y = (A 1).comp Φ)
    (heven : Summable (evenResidualTail A Φ Y))
    (hodd : Summable (oddResidualTail A Φ Y)) :
    B.comp (Φ - Y) = (A 0).comp Φ + residualTaylorTerm A Φ Y 1 +
      (∑' n, evenResidualTail A Φ Y n) + (∑' n, oddResidualTail A Φ Y n) := by
  have he : HasSum (fun n => residualTaylorTerm A Φ Y (2 * n + 1))
      (residualTaylorTerm A Φ Y 1 + ∑' n, evenResidualTail A Φ Y n) := by
    apply HasSum.zero_add
    convert heven.hasSum using 1
    ext n
    unfold evenResidualTail
    rw [show 2 * (n + 1) + 1 = 3 + 2 * n by omega]
  have ho : HasSum (fun n => residualTaylorTerm A Φ Y ((2 * n + 1) + 1))
      (∑' n, oddResidualTail A Φ Y n) := by
    convert hodd.hasSum using 1
    ext n
    unfold oddResidualTail
    rw [show 2 * n + 1 + 1 = 2 + 2 * n by omega]
  have hsplit := HasSum.even_add_odd (f := fun n => residualTaylorTerm A Φ Y (n + 1)) he ho
  have hsplit0 := hsplit.zero_add
  have heq := (residualTaylorTerm_hasSum A B hA Φ Y).unique hsplit0
  have hzero : residualTaylorTerm A Φ Y 0 = 0 := by
    simp [residualTaylorTerm, hcancel]
  rw [hzero, zero_add] at heq
  calc
    B.comp (Φ - Y) = (A 0).comp Φ + ((B - A 0).comp Φ - B.comp Y) := by
      ext x
      simp
      abel
    _ = _ := by rw [heq]; abel

theorem hasSum_compression (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H)
    (hA : HasSum A B) (L R : V →L[𝕜] H) :
    HasSum (fun n => L.adjoint.comp ((A n).comp R)) (L.adjoint.comp (B.comp R)) := by
  simpa using (hasSum_comp_right A B hA R).mapL
    ((ContinuousLinearMap.compL 𝕜 V H V) L.adjoint)

/-- The complete compressed-coefficient series is obtained by three
shifted copies of the original convergent operator series. -/
theorem compressedTaylorTerm_hasSum (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H)
    (hA : HasSum A B) (Φ Y : V →L[𝕜] H) :
    HasSum (compressedTaylorTerm A Φ Y)
      (Φ.adjoint.comp ((B - (A 0 + A 1)).comp Φ) -
        Φ.adjoint.comp ((B - A 0).comp Y) -
        Y.adjoint.comp ((B - A 0).comp Φ) + Y.adjoint.comp (B.comp Y)) := by
  have htail1 : HasSum (fun n => A (n + 1)) (B - A 0) := by
    simpa using (hasSum_nat_add_iff' 1).2 hA
  have htail2 : HasSum (fun n => A (n + 2)) (B - (A 0 + A 1)) := by
    simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 2).2 hA
  exact (((hasSum_compression _ _ htail2 Φ Φ).sub
    (hasSum_compression _ _ htail1 Φ Y)).sub
    (hasSum_compression _ _ htail1 Y Φ)).add (hasSum_compression A B hA Y Y)

def compressedLinearTerm (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H) : V →L[𝕜] V :=
  Φ.adjoint.comp ((A 1).comp Φ) - Φ.adjoint.comp ((A 0).comp Y) -
    Y.adjoint.comp ((A 0).comp Φ)

/-- Exact reconstruction before using inversion to remove odd degrees. -/
theorem compressed_series_identity (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H)
    (hA : HasSum A B) (Φ Y : V →L[𝕜] H) :
    (Φ - Y).adjoint.comp (B.comp (Φ - Y)) =
      Φ.adjoint.comp ((A 0).comp Φ) + compressedLinearTerm A Φ Y +
        ∑' n, compressedTaylorTerm A Φ Y n := by
  rw [(compressedTaylorTerm_hasSum A B hA Φ Y).tsum_eq]
  ext x
  simp [compressedLinearTerm, map_sub]
  abel

/-- Reassembly of the even compressed tail from exact vanishing of the
odd coefficients. The vanishing premise can be supplied by inversion. -/
theorem compressed_even_series_identity (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H)
    (hA : HasSum A B) (Φ Y : V →L[𝕜] H)
    (hlinear : compressedLinearTerm A Φ Y = 0)
    (hodd : ∀ n, compressedTaylorTerm A Φ Y (2 * n + 1) = 0)
    (heven : Summable (compressedTail A Φ Y)) :
    (Φ - Y).adjoint.comp (B.comp (Φ - Y)) =
      Φ.adjoint.comp ((A 0).comp Φ) + compressedTaylorTerm A Φ Y 0 +
        ∑' n, compressedTail A Φ Y n := by
  have he : HasSum (fun n => compressedTaylorTerm A Φ Y (2 * n))
      (compressedTaylorTerm A Φ Y 0 + ∑' n, compressedTail A Φ Y n) := by
    apply HasSum.zero_add
    convert heven.hasSum using 1
    ext n
    unfold compressedTail
    rw [show 2 * (n + 1) = 2 + 2 * n by omega]
  have ho : HasSum (fun n => compressedTaylorTerm A Φ Y (2 * n + 1)) 0 := by
    simp only [hodd]
    exact hasSum_zero
  have hsplit := HasSum.even_add_odd (f := compressedTaylorTerm A Φ Y) he ho
  have hsum : (∑' n, compressedTaylorTerm A Φ Y n) =
      compressedTaylorTerm A Φ Y 0 + ∑' n, compressedTail A Φ Y n := by
    simpa using hsplit.tsum_eq
  rw [compressed_series_identity A B hA Φ Y, hlinear, add_zero, hsum]
  abel

/-- An entire operator image lies in one inversion eigenspace. -/
def HasParity (I : H ≃ₗᵢ[𝕜] H) (σ : 𝕜) (X : V →L[𝕜] H) : Prop :=
  ∀ v, I (X v) = σ • X v

omit [CompleteSpace H] [CompleteSpace V] in
theorem HasParity.add {I : H ≃ₗᵢ[𝕜] H} {σ : 𝕜} {X Y : V →L[𝕜] H}
    (hX : HasParity I σ X) (hY : HasParity I σ Y) : HasParity I σ (X + Y) := by
  intro v
  simp only [add_apply, map_add, hX v, hY v, smul_add]

omit [CompleteSpace H] [CompleteSpace V] in
theorem HasParity.sub {I : H ≃ₗᵢ[𝕜] H} {σ : 𝕜} {X Y : V →L[𝕜] H}
    (hX : HasParity I σ X) (hY : HasParity I σ Y) : HasParity I σ (X - Y) := by
  intro v
  simp only [sub_apply, map_sub, hX v, hY v, smul_sub]

omit [CompleteSpace H] [CompleteSpace V] in
theorem HasParity.comp {I : H ≃ₗᵢ[𝕜] H} {σ τ : 𝕜} {X : V →L[𝕜] H}
    (hX : HasParity I σ X) (A : H →L[𝕜] H)
    (hA : ∀ v, I (A v) = τ • A (I v)) :
    HasParity I (τ * σ) (A.comp X) := by
  intro v
  simp only [ContinuousLinearMap.comp_apply, hA, hX v, map_smul, smul_smul]

omit [CompleteSpace H] [CompleteSpace V] in
/-- A convergent sum of one parity stays in that exact parity space. -/
theorem HasParity.tsum {I : H ≃ₗᵢ[𝕜] H} {σ : 𝕜} (X : ℕ → V →L[𝕜] H)
    (hs : Summable X) (hp : ∀ n, HasParity I σ (X n)) :
    HasParity I σ (∑' n, X n) := by
  let J : H →L[𝕜] H := I.toContinuousLinearEquiv.toContinuousLinearMap
  have hmap := hs.hasSum.mapL ((ContinuousLinearMap.compL 𝕜 V H H) J)
  have hscaled := hs.hasSum.const_smul σ
  have hpoint : (fun n => J.comp (X n)) = (fun n => σ • X n) := by
    funext n
    ext v
    exact hp n v
  change HasSum (fun n => J.comp (X n)) (J.comp (∑' n, X n)) at hmap
  rw [hpoint] at hmap
  have heq := hmap.unique hscaled
  intro v
  exact congrArg (fun T : V →L[𝕜] H => T v) heq

omit [CompleteSpace H] [CompleteSpace V] in
/-- Opposite inversion eigenvalues give exact orthogonality, not a small
cross-term estimate. -/
theorem inner_zero_of_opposite_parity (I : H ≃ₗᵢ[𝕜] H) (σ : 𝕜)
    (hσ : σ = 1 ∨ σ = -1) (X Y : V →L[𝕜] H)
    (hX : HasParity I σ X) (hY : HasParity I (-σ) Y) (x y : V) :
    inner 𝕜 (X x) (Y y) = 0 := by
  have h := I.inner_map_map (X x) (Y y)
  rw [hX x, hY y] at h
  rcases hσ with rfl | rfl <;>
    simp only [one_smul, neg_smul, neg_neg, inner_neg_left, inner_neg_right] at h <;>
    exact CharZero.neg_eq_self_iff.mp h

/-- The whole cross Gram operator vanishes between opposite parity images. -/
theorem adjoint_comp_zero_of_opposite_parity (I : H ≃ₗᵢ[𝕜] H) (σ : 𝕜)
    (hσ : σ = 1 ∨ σ = -1) (X Y : V →L[𝕜] H)
    (hX : HasParity I σ X) (hY : HasParity I (-σ) Y) : X.adjoint.comp Y = 0 := by
  ext v
  apply ext_inner_left 𝕜
  intro w
  simp only [ContinuousLinearMap.comp_apply, zero_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]
  simpa using inner_zero_of_opposite_parity I σ hσ X Y hX hY w v

/-- Both cross terms in the full residual square vanish by inversion. -/
theorem opposite_parity_square (I : H ≃ₗᵢ[𝕜] H) (σ : 𝕜)
    (hσ : σ = 1 ∨ σ = -1) (X Y : V →L[𝕜] H)
    (hX : HasParity I σ X) (hY : HasParity I (-σ) Y) :
    (X + Y).adjoint.comp (X + Y) = X.adjoint.comp X + Y.adjoint.comp Y := by
  have hxy := adjoint_comp_zero_of_opposite_parity I σ hσ X Y hX hY
  have hyx : Y.adjoint.comp X = 0 := by
    have h := congrArg (fun T : V →L[𝕜] V => T.adjoint) hxy
    simpa using h
  simp [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hxy, hyx]

/-- Coefficient-by-coefficient inversion covariance of a homogeneous series. -/
def TaylorParity (I : H ≃ₗᵢ[𝕜] H) (A : ℕ → H →L[𝕜] H) : Prop :=
  ∀ j v, I (A j v) = (-1 : 𝕜) ^ j • A j (I v)

omit [CompleteSpace H] [CompleteSpace V] in
theorem HasParity.even_comp {I : H ≃ₗᵢ[𝕜] H} {σ : 𝕜} {X : V →L[𝕜] H}
    (hX : HasParity I σ X) (A : ℕ → H →L[𝕜] H) (hA : TaylorParity I A) (n : ℕ) :
    HasParity I σ ((A (2 * n)).comp X) := by
  simpa [pow_mul] using hX.comp (A (2 * n)) (hA (2 * n))

omit [CompleteSpace H] [CompleteSpace V] in
theorem HasParity.odd_comp {I : H ≃ₗᵢ[𝕜] H} {σ : 𝕜} {X : V →L[𝕜] H}
    (hX : HasParity I σ X) (A : ℕ → H →L[𝕜] H) (hA : TaylorParity I A) (n : ℕ) :
    HasParity I (-σ) ((A (2 * n + 1)).comp X) := by
  simpa [pow_add, pow_mul] using hX.comp (A (2 * n + 1)) (hA (2 * n + 1))

omit [CompleteSpace H] [CompleteSpace V] in
theorem evenResidualTail_parity (I : H ≃ₗᵢ[𝕜] H) (σ : 𝕜)
    (A : ℕ → H →L[𝕜] H) (hA : TaylorParity I A) (Φ Y : V →L[𝕜] H)
    (hΦ : HasParity I σ Φ) (hY : HasParity I (-σ) Y) (n : ℕ) :
    HasParity I σ (evenResidualTail A Φ Y n) := by
  have hfirst := hΦ.even_comp A hA (n + 2)
  have hsecond := hY.odd_comp A hA (n + 1)
  rw [show 2 * (n + 2) = 4 + 2 * n by omega] at hfirst
  rw [show 2 * (n + 1) + 1 = 3 + 2 * n by omega] at hsecond
  have hsecond' : HasParity I σ ((A (3 + 2 * n)).comp Y) := by simpa using hsecond
  simpa [evenResidualTail, residualTaylorTerm,
    show 3 + 2 * n + 1 = 4 + 2 * n by omega] using hfirst.sub hsecond'

omit [CompleteSpace H] [CompleteSpace V] in
theorem oddResidualTail_parity (I : H ≃ₗᵢ[𝕜] H) (σ : 𝕜)
    (A : ℕ → H →L[𝕜] H) (hA : TaylorParity I A) (Φ Y : V →L[𝕜] H)
    (hΦ : HasParity I σ Φ) (hY : HasParity I (-σ) Y) (n : ℕ) :
    HasParity I (-σ) (oddResidualTail A Φ Y n) := by
  have hfirst := hΦ.odd_comp A hA (n + 1)
  have hsecond := hY.even_comp A hA (n + 1)
  rw [show 2 * (n + 1) + 1 = 3 + 2 * n by omega] at hfirst
  rw [show 2 * (n + 1) = 2 + 2 * n by omega] at hsecond
  simpa [oddResidualTail, residualTaylorTerm,
    show 2 + 2 * n + 1 = 3 + 2 * n by omega] using hfirst.sub hsecond

theorem compressedLinearTerm_zero (I : H ≃ₗᵢ[𝕜] H) (σ : 𝕜)
    (hσ : σ = 1 ∨ σ = -1) (A : ℕ → H →L[𝕜] H) (hA : TaylorParity I A)
    (Φ Y : V →L[𝕜] H) (hΦ : HasParity I σ Φ) (hY : HasParity I (-σ) Y) :
    compressedLinearTerm A Φ Y = 0 := by
  have h1 : Φ.adjoint.comp ((A 1).comp Φ) = 0 :=
    adjoint_comp_zero_of_opposite_parity I σ hσ Φ _ hΦ (hΦ.odd_comp A hA 0)
  have h2 : Φ.adjoint.comp ((A 0).comp Y) = 0 :=
    adjoint_comp_zero_of_opposite_parity I σ hσ Φ _ hΦ (hY.even_comp A hA 0)
  have hσneg : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> simp
  have hp : HasParity I (-(-σ)) ((A 0).comp Φ) := by
    simpa using hΦ.even_comp A hA 0
  have h3 : Y.adjoint.comp ((A 0).comp Φ) = 0 :=
    adjoint_comp_zero_of_opposite_parity I (-σ) hσneg Y _ hY hp
  simp [compressedLinearTerm, h1, h2, h3]

/-- All odd compressed coefficients vanish as a consequence of actual
inversion covariance and common center parity. -/
theorem compressedTaylorTerm_odd_zero (I : H ≃ₗᵢ[𝕜] H) (σ : 𝕜)
    (hσ : σ = 1 ∨ σ = -1) (A : ℕ → H →L[𝕜] H) (hA : TaylorParity I A)
    (Φ Y : V →L[𝕜] H) (hΦ : HasParity I σ Φ) (hY : HasParity I (-σ) Y) (n : ℕ) :
    compressedTaylorTerm A Φ Y (2 * n + 1) = 0 := by
  have h1 : Φ.adjoint.comp ((A (2 * (n + 1) + 1)).comp Φ) = 0 :=
    adjoint_comp_zero_of_opposite_parity I σ hσ Φ _ hΦ (hΦ.odd_comp A hA (n + 1))
  have h2 : Φ.adjoint.comp ((A (2 * (n + 1))).comp Y) = 0 :=
    adjoint_comp_zero_of_opposite_parity I σ hσ Φ _ hΦ (hY.even_comp A hA (n + 1))
  have hσneg : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> simp
  have hp3 : HasParity I (-(-σ)) ((A (2 * (n + 1))).comp Φ) := by
    simpa using hΦ.even_comp A hA (n + 1)
  have hp4 : HasParity I (-(-σ)) ((A (2 * n + 1)).comp Y) := hY.odd_comp A hA n
  have h3 : Y.adjoint.comp ((A (2 * (n + 1))).comp Φ) = 0 :=
    adjoint_comp_zero_of_opposite_parity I (-σ) hσneg Y _ hY hp3
  have h4 : Y.adjoint.comp ((A (2 * n + 1)).comp Y) = 0 :=
    adjoint_comp_zero_of_opposite_parity I (-σ) hσneg Y _ hY hp4
  simp only [compressedTaylorTerm,
    show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by omega,
    show 2 * n + 1 + 1 = 2 * (n + 1) by omega, h1, h2, h3, h4,
    sub_zero, add_zero]

/-- Exact first-order cancellation identifies the compressed quadratic
coefficient without any approximate residual constant. -/
theorem compressedTaylorTerm_zero_eq (A : ℕ → H →L[𝕜] H) (Φ Y : V →L[𝕜] H)
    (hcancel : (A 0).comp Y = (A 1).comp Φ) :
    compressedTaylorTerm A Φ Y 0 =
      Φ.adjoint.comp ((A 2).comp Φ) - Φ.adjoint.comp ((A 1).comp Y) := by
  simp only [compressedTaylorTerm, Nat.zero_add, hcancel]
  abel

/-- Complete operator remainder package for a convergent homogeneous
series. The witnesses are the norm-convergent tails constructed above.
The zeroth coefficient is the shifted center operator `H(0)-E`; no
numerical center residual or assumed remainder estimate occurs here. -/
theorem local_taylor_decomposition
    (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H) (hseries : HasSum A B)
    (Φ Y : V →L[𝕜] H) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (hΦnorm : ‖Φ‖ ≤ 1) (hYnorm : ‖Y‖ ≤ 3 * r)
    (hcoeff : ∀ j, 1 ≤ j → ‖A j‖ ≤ taylorCoefficientMajorant j * r ^ j)
    (hcancel : (A 0).comp Y = (A 1).comp Φ)
    (I : H ≃ₗᵢ[𝕜] H) (σ : 𝕜) (hσ : σ = 1 ∨ σ = -1)
    (hparity : TaylorParity I A) (hΦ : HasParity I σ Φ) (hY : HasParity I (-σ) Y) :
    ∃ (Krem : V →L[𝕜] V) (Reven Rodd : V →L[𝕜] H),
      (Φ - Y).adjoint.comp (B.comp (Φ - Y)) =
        Φ.adjoint.comp ((A 0).comp Φ) +
          (Φ.adjoint.comp ((A 2).comp Φ) - Φ.adjoint.comp ((A 1).comp Y)) + Krem ∧
      B.comp (Φ - Y) = (A 0).comp Φ + residualTaylorTerm A Φ Y 1 + Reven + Rodd ∧
      ‖Krem‖ ≤ (13 / 5) * r ^ 4 ∧ ‖Reven‖ ≤ (2 / 25) * r ^ 4 ∧
      ‖Rodd‖ ≤ (17 / 20) * r ^ 3 ∧
      ((A 0).comp Φ + residualTaylorTerm A Φ Y 1 + Reven).adjoint.comp Rodd = 0 := by
  obtain ⟨heven, hEvenNorm⟩ := evenResidualTail_bound A Φ Y r hr0 hr hΦnorm hYnorm hcoeff
  obtain ⟨hodd, hOddNorm⟩ := oddResidualTail_bound A Φ Y r hr0 hr hΦnorm hYnorm hcoeff
  obtain ⟨hcompressed, hCompressedNorm⟩ := compressedTail_bound A Φ Y r hr0 hr hΦnorm hYnorm hcoeff
  have hcomp := compressed_even_series_identity A B hseries Φ Y
    (compressedLinearTerm_zero I σ hσ A hparity Φ Y hΦ hY)
    (compressedTaylorTerm_odd_zero I σ hσ A hparity Φ Y hΦ hY) hcompressed
  rw [compressedTaylorTerm_zero_eq A Φ Y hcancel] at hcomp
  have hres := residual_series_identity A B hseries Φ Y hcancel heven hodd
  have hp0 : HasParity I σ ((A 0).comp Φ) := hΦ.even_comp A hparity 0
  have hp2 : HasParity I σ (residualTaylorTerm A Φ Y 1) := by
    have hleft : HasParity I σ ((A 2).comp Φ) := hΦ.even_comp A hparity 1
    have hright : HasParity I σ ((A 1).comp Y) := by
      simpa using hY.odd_comp A hparity 0
    exact hleft.sub hright
  have hpeven : HasParity I σ (∑' n, evenResidualTail A Φ Y n) :=
    HasParity.tsum _ heven (evenResidualTail_parity I σ A hparity Φ Y hΦ hY)
  have hpodd : HasParity I (-σ) (∑' n, oddResidualTail A Φ Y n) :=
    HasParity.tsum _ hodd (oddResidualTail_parity I σ A hparity Φ Y hΦ hY)
  refine ⟨∑' n, compressedTail A Φ Y n, ∑' n, evenResidualTail A Φ Y n,
    ∑' n, oddResidualTail A Φ Y n, hcomp, hres, hCompressedNorm, hEvenNorm, hOddNorm, ?_⟩
  exact adjoint_comp_zero_of_opposite_parity I σ hσ _ _ ((hp0.add hp2).add hpeven) hpodd

end

end Maxwell.Spectral
