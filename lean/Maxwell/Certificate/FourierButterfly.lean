import Maxwell.Certificate.FourierRoots
import Mathlib.Algebra.BigOperators.Fin

/-! Exact mixed-radix butterflies for the twenty-root Fourier kernels.
The intermediate five- and ten-point arrays can be computed once and reused
by the low and high output halves. Both Fourier signs are supported. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix

theorem root20_add (a b : ℤ) : root20 (a + b) = root20 a * root20 b := by
  simp only [root20_eq_cis, Int.cast_add, add_div, cis_add]

theorem root20_add_twenty_mul (a b : ℤ) : root20 (a + 20 * b) = root20 a := by
  simp [root20, Int.add_emod]

theorem root20_neg (a : ℤ) : root20 (-a) = star (root20 a) := by
  rw [root20_eq_cis, root20_eq_cis, cis_conjugate]
  congr 1
  push_cast
  ring

theorem root20_ten : root20 10 = -1 := by
  rw [root20_eq_cis]
  apply Complex.ext
  · rw [Trigonometric.cis_re]
    norm_num
    convert Real.cos_pi using 1
    congr 1
    ring
  · rw [Trigonometric.cis_im]
    norm_num
    convert Real.sin_pi using 1
    congr 1
    ring

theorem root20_add_ten (a : ℤ) : root20 (a + 10) = -root20 a := by
  rw [root20_add, root20_ten]
  ring

/-- An unnormalized cyclic transform using the fixed twentieth roots. -/
def rootSum (n : ℕ) (stride k : ℤ) (v : Fin n → ℂ) : ℂ :=
  ∑ j, root20 (stride * k * j.val) * v j

def evenSamples {n : ℕ} (v : Fin (n * 2) → ℂ) : Fin n → ℂ :=
  fun j => v (finProdFinEquiv (j, 0))

def oddSamples {n : ℕ} (v : Fin (n * 2) → ℂ) : Fin n → ℂ :=
  fun j => v (finProdFinEquiv (j, 1))

private theorem sum_even_odd {n : ℕ} (f : Fin (n * 2) → ℂ) :
    ∑ j, f j = (∑ j : Fin n, f (finProdFinEquiv (j, 0))) +
      ∑ j : Fin n, f (finProdFinEquiv (j, 1)) := by
  rw [← finProdFinEquiv.sum_comp f, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib]

/-- Decimation in time: one length-2n transform is two length-n transforms
and one twiddle multiplication per paired output. -/
theorem rootSum_double (n : ℕ) (stride k : ℤ) (v : Fin (n * 2) → ℂ) :
    rootSum (n * 2) stride k v =
      rootSum n (2 * stride) k (evenSamples v) +
        root20 (stride * k) * rootSum n (2 * stride) k (oddSamples v) := by
  unfold rootSum
  rw [sum_even_odd, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    change root20 (stride * k * (finProdFinEquiv (j, 0)).val) * evenSamples v j = _
    have he : stride * k * (finProdFinEquiv (j, (0 : Fin 2))).val =
        (2 * stride) * k * j.val := by
      change stride * k * ((0 + 2 * j.val : ℕ) : ℤ) = _
      push_cast
      ring
    rw [he]
  · apply Finset.sum_congr rfl
    intro j _
    change root20 (stride * k * (finProdFinEquiv (j, 1)).val) * oddSamples v j = _
    have he : stride * k * (finProdFinEquiv (j, (1 : Fin 2))).val =
        stride * k + (2 * stride) * k * j.val := by
      change stride * k * ((1 + 2 * j.val : ℕ) : ℤ) = _
      push_cast
      ring
    rw [he, root20_add, mul_assoc]

/-- The period follows from the exact twentieth-root period. -/
theorem rootSum_periodic (n : ℕ) (stride period : ℤ) (v : Fin n → ℂ)
    (h : (20 : ℤ) ∣ stride * period) :
    Function.Periodic (fun k => rootSum n stride k v) period := by
  obtain ⟨a, ha⟩ := h
  intro k
  apply Finset.sum_congr rfl
  intro j _
  have he : stride * (k + period) * j.val = stride * k * j.val + 20 * (a * j.val) := by
    calc
      _ = stride * k * j.val + (stride * period) * j.val := by ring
      _ = _ := by rw [ha]; ring
  rw [he, root20_add_twenty_mul]

/-- The upper output half reuses the same two smaller transforms and
subtracts the twiddled odd half. -/
theorem rootSum_double_high (n : ℕ) (stride k : ℤ) (v : Fin (n * 2) → ℂ)
    (hp : (20 : ℤ) ∣ (2 * stride) * n) (hh : root20 (stride * n) = -1) :
    rootSum (n * 2) stride (k + n) v =
      rootSum n (2 * stride) k (evenSamples v) -
        root20 (stride * k) * rootSum n (2 * stride) k (oddSamples v) := by
  have he : rootSum n (2 * stride) (k + n) (evenSamples v) =
      rootSum n (2 * stride) k (evenSamples v) :=
    rootSum_periodic n (2 * stride) n (evenSamples v) hp k
  have ho : rootSum n (2 * stride) (k + n) (oddSamples v) =
      rootSum n (2 * stride) k (oddSamples v) :=
    rootSum_periodic n (2 * stride) n (oddSamples v) hp k
  rw [rootSum_double, he, ho, mul_add, root20_add, hh]
  ring

/-- Exact normalization and sign for the existing twenty-point matrix. -/
theorem cyclicFourier_twenty_mulVec (v : Fin 20 → ℂ) (a : Fin 20) :
    (cyclicFourier 20 *ᵥ v) a = ((Real.sqrt 20 : ℂ))⁻¹ * rootSum 20 (-1) a.val v := by
  simp only [Matrix.mulVec, dotProduct, cyclicFourier_twenty_root, rootSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, ← root20_neg]
  have he : -((a.val : ℤ) * j.val) = (-1 : ℤ) * a.val * j.val := by ring
  rw [he]

theorem cyclicFourier_ten_mulVec (v : Fin 10 → ℂ) (a : Fin 10) :
    (cyclicFourier 10 *ᵥ v) a = ((Real.sqrt 10 : ℂ))⁻¹ * rootSum 10 (-2) a.val v := by
  simp only [Matrix.mulVec, dotProduct, cyclicFourier_ten_root, rootSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, ← root20_neg]
  have he : -(2 * (a.val : ℤ) * j.val) = (-2 : ℤ) * a.val * j.val := by ring
  rw [he]

theorem cyclicFourier_twenty_adjoint_mulVec (v : Fin 20 → ℂ) (a : Fin 20) :
    ((cyclicFourier 20).conjTranspose *ᵥ v) a =
      ((Real.sqrt 20 : ℂ))⁻¹ * rootSum 20 1 a.val v := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, cyclicFourier_twenty_root,
    rootSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [star_mul', star_inv₀, star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [mul_assoc]
  have he : (j.val : ℤ) * a.val = 1 * (a.val : ℤ) * j.val := by ring
  rw [he]

theorem cyclicFourier_ten_adjoint_mulVec (v : Fin 10 → ℂ) (a : Fin 10) :
    ((cyclicFourier 10).conjTranspose *ᵥ v) a =
      ((Real.sqrt 10 : ℂ))⁻¹ * rootSum 10 2 a.val v := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, cyclicFourier_ten_root,
    rootSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [star_mul', star_inv₀, star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [mul_assoc]
  have he : 2 * (j.val : ℤ) * a.val = 2 * (a.val : ℤ) * j.val := by ring
  rw [he]


/-- Combine two stored half-transform arrays. Each lower output uses a sum;
its paired upper output uses a difference with the very same twiddle. -/
def butterfly (n : ℕ) (stride : ℤ) (even odd : Fin n → ℂ) (a : Fin (n * 2)) : ℂ :=
  if h : a.val < n then
    even ⟨a.val, h⟩ + root20 (stride * a.val) * odd ⟨a.val, h⟩
  else
    let j : Fin n := ⟨a.val - n, by have := a.isLt; omega⟩
    even j - root20 (stride * j.val) * odd j

theorem butterfly_rootSum (n : ℕ) (stride : ℤ) (v : Fin (n * 2) → ℂ)
    (hp : (20 : ℤ) ∣ (2 * stride) * n) (hh : root20 (stride * n) = -1) :
    butterfly n stride
      (fun j => rootSum n (2 * stride) j.val (evenSamples v))
      (fun j => rootSum n (2 * stride) j.val (oddSamples v)) =
      fun a => rootSum (n * 2) stride a.val v := by
  funext a
  unfold butterfly
  split_ifs with ha
  · exact (rootSum_double n stride a.val v).symm
  · dsimp only
    have he : (a.val : ℤ) = ((a.val - n : ℕ) : ℤ) + n := by omega
    rw [he, rootSum_double_high n stride _ v hp hh]

theorem root20_signed_half_turn (sign : ℤ) (hs : sign = 1 ∨ sign = -1) :
    root20 (sign * 10) = -1 := by
  rcases hs with rfl | rfl
  · simpa using root20_ten
  · simp [root20_neg, root20_ten]

def combine10 (sign : ℤ) (even odd : Fin 5 → ℂ) : Fin 10 → ℂ :=
  butterfly 5 (2 * sign) even odd

def combine20 (sign : ℤ) (even odd : Fin 10 → ℂ) : Fin 20 → ℂ :=
  butterfly 10 sign even odd

theorem combine10_rootSum (sign : ℤ) (hs : sign = 1 ∨ sign = -1) (v : Fin 10 → ℂ) :
    combine10 sign (fun j => rootSum 5 (4 * sign) j.val (evenSamples v))
      (fun j => rootSum 5 (4 * sign) j.val (oddSamples v)) =
      fun a => rootSum 10 (2 * sign) a.val v := by
  have hp : (20 : ℤ) ∣ (2 * (2 * sign)) * 5 := ⟨sign, by ring⟩
  have hh : root20 ((2 * sign) * 5) = -1 := by
    have he : (2 * sign) * 5 = sign * 10 := by ring
    rw [he]
    exact root20_signed_half_turn sign hs
  have h := butterfly_rootSum 5 (2 * sign) v hp hh
  have he : (2 : ℤ) * (2 * sign) = 4 * sign := by ring
  simpa only [combine10, he] using h

theorem combine20_rootSum (sign : ℤ) (hs : sign = 1 ∨ sign = -1) (v : Fin 20 → ℂ) :
    combine20 sign (fun j => rootSum 10 (2 * sign) j.val (evenSamples v))
      (fun j => rootSum 10 (2 * sign) j.val (oddSamples v)) =
      fun a => rootSum 20 sign a.val v :=
  butterfly_rootSum 10 sign v ⟨sign, by ring⟩ (root20_signed_half_turn sign hs)

/-- Two five-point arrays followed by a ten-point butterfly. -/
def transform10 (sign : ℤ) (v : Fin 10 → ℂ) : Fin 10 → ℂ :=
  combine10 sign (fun j => rootSum 5 (4 * sign) j.val (evenSamples v))
    (fun j => rootSum 5 (4 * sign) j.val (oddSamples v))

/-- Four five-point arrays, two ten-point butterflies, then one
 twenty-point butterfly. The intermediate arrays have no normalization. -/
def transform20 (sign : ℤ) (v : Fin 20 → ℂ) : Fin 20 → ℂ :=
  combine20 sign (transform10 sign (evenSamples v)) (transform10 sign (oddSamples v))

theorem transform10_eq_rootSum (sign : ℤ) (hs : sign = 1 ∨ sign = -1) (v : Fin 10 → ℂ) :
    transform10 sign v = fun a => rootSum 10 (2 * sign) a.val v :=
  combine10_rootSum sign hs v

theorem transform20_eq_rootSum (sign : ℤ) (hs : sign = 1 ∨ sign = -1) (v : Fin 20 → ℂ) :
    transform20 sign v = fun a => rootSum 20 sign a.val v := by
  unfold transform20
  rw [transform10_eq_rootSum sign hs, transform10_eq_rootSum sign hs]
  exact combine20_rootSum sign hs v

theorem cyclicFourier_twenty_butterfly (v : Fin 20 → ℂ) (a : Fin 20) :
    (cyclicFourier 20 *ᵥ v) a =
      ((Real.sqrt 20 : ℂ))⁻¹ * transform20 (-1) v a := by
  rw [transform20_eq_rootSum (-1) (Or.inr rfl)]
  exact cyclicFourier_twenty_mulVec v a

theorem cyclicFourier_twenty_adjoint_butterfly (v : Fin 20 → ℂ) (a : Fin 20) :
    ((cyclicFourier 20).conjTranspose *ᵥ v) a =
      ((Real.sqrt 20 : ℂ))⁻¹ * transform20 1 v a := by
  rw [transform20_eq_rootSum 1 (Or.inl rfl)]
  exact cyclicFourier_twenty_adjoint_mulVec v a

theorem cyclicFourier_ten_butterfly (v : Fin 10 → ℂ) (a : Fin 10) :
    (cyclicFourier 10 *ᵥ v) a =
      ((Real.sqrt 10 : ℂ))⁻¹ * transform10 (-1) v a := by
  rw [transform10_eq_rootSum (-1) (Or.inr rfl)]
  simpa using cyclicFourier_ten_mulVec v a

theorem cyclicFourier_ten_adjoint_butterfly (v : Fin 10 → ℂ) (a : Fin 10) :
    ((cyclicFourier 10).conjTranspose *ᵥ v) a =
      ((Real.sqrt 10 : ℂ))⁻¹ * transform10 1 v a := by
  rw [transform10_eq_rootSum 1 (Or.inl rfl)]
  simpa using cyclicFourier_ten_adjoint_mulVec v a

end Maxwell.Certificate.FourierBinding
