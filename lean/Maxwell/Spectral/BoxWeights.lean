import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Maxwell.Spectral.BoxWeights

/-- The center/shifted inverse-weight ratio is maximal at the lowest high
frequency. This is the exact scalar inequality behind χ in verify_scalar. -/
theorem transverse_inverse_ratio (ρ t σ s r x : ℝ)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hσ : 0 ≤ σ) (hs : 0 ≤ s)
    (hsr : s < r) (hrx : r ≤ x)
    (hshift : 0 < (r-s)^2/ρ-t-σ) :
    (x^2/ρ-t) / ((x-s)^2/ρ-t-σ) ≤
      (r^2/ρ-t) / ((r-s)^2/ρ-t-σ) := by
  have hr : 0 < r := hs.trans_lt hsr
  have hx : 0 < x := hr.trans_le hrx
  have hxr : 0 ≤ x-r := sub_nonneg.mpr hrx
  have hrs : 0 ≤ r-s := sub_nonneg.mpr hsr.le
  have hxs : 0 ≤ x-s := sub_nonneg.mpr (hsr.le.trans hrx)
  have hxshift : 0 < (x-s)^2/ρ-t-σ := by
    have hp : (r-s)^2/ρ ≤ (x-s)^2/ρ := by gcongr
    linarith
  apply (div_le_div_iff₀ hxshift hshift).mpr
  have hp : 0 ≤ (x-r) *
      (s*(x*(r-s)+r*(x-s)) + ρ*σ*(x+r) + 2*ρ*t*s) := by positivity
  have he : (r^2/ρ-t)*((x-s)^2/ρ-t-σ) -
      (x^2/ρ-t)*((r-s)^2/ρ-t-σ) =
      ((x-r)*(s*(x*(r-s)+r*(x-s))+ρ*σ*(x+r)+2*ρ*t*s))/ρ^2 := by
    field_simp
    ring
  have hn : 0 ≤ ((x-r)*(s*(x*(r-s)+r*(x-s))+ρ*σ*(x+r)+2*ρ*t*s))/ρ^2 :=
    div_nonneg hp (sq_nonneg _)
  rw [← he] at hn
  linarith

/-- The weighted center curl decreases with the high-frequency Laplacian. -/
theorem curl_weight_ratio (ρ t r x : ℝ)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hr : 0 < r) (hrx : r ≤ x)
    (hbase : 0 < r^2/ρ-t) :
    x^2/(x^2/ρ-t) ≤ r^2/(r^2/ρ-t) := by
  have hx : 0 < x := hr.trans_le hrx
  have hxr : 0 ≤ x-r := sub_nonneg.mpr hrx
  have hxbase : 0 < x^2/ρ-t := by
    have h : r^2/ρ ≤ x^2/ρ := by gcongr
    linarith
  apply (div_le_div_iff₀ hxbase hbase).mpr
  have hp : 0 ≤ t*(x-r)*(x+r) := by positivity
  have he : r^2*(x^2/ρ-t) - x^2*(r^2/ρ-t) = t*(x-r)*(x+r) := by ring
  nlinarith only [hp, he]

theorem curl_weight_sqrt (ρ t r x : ℝ)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hr : 0 < r) (hrx : r ≤ x)
    (hbase : 0 < r^2/ρ-t) :
    x / Real.sqrt (x^2/ρ-t) ≤ r / Real.sqrt (r^2/ρ-t) := by
  have hx : 0 < x := hr.trans_le hrx
  have hxbase : 0 < x^2/ρ-t := by
    have h : r^2/ρ ≤ x^2/ρ := by gcongr
    linarith
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, div_pow, Real.sq_sqrt hxbase.le, Real.sq_sqrt hbase.le]
  exact curl_weight_ratio ρ t r x hρ ht hr hrx hbase

/-- The enlarged high-projector remainder coefficient decreases on r>s. -/
theorem projector_remainder_coefficient (s r x : ℝ)
    (hs : 0 ≤ s) (hsr : s < r) (hrx : r ≤ x) :
    (x/2+3+s/x)/(x-s)^2 ≤ (r/2+3+s/r)/(r-s)^2 := by
  have hr : 0 < r := hs.trans_lt hsr
  have hx : 0 < x := hr.trans_le hrx
  have hdr : 0 < r-s := sub_pos.mpr hsr
  have hdx : 0 < x-s := hdr.trans_le (by linarith)
  have hfirst : x/(x-s)^2 ≤ r/(r-s)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hdx) (sq_pos_of_pos hdr)).mpr
    have hp : 0 ≤ (x-r)*(r*x-s^2) := by
      apply mul_nonneg (sub_nonneg.mpr hrx)
      have hxx : s ≤ x := hsr.le.trans hrx
      nlinarith
    nlinarith only [hp]
  have hsecond : 3/(x-s)^2 ≤ 3/(r-s)^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hdr)
    gcongr
  have hthird : (s/x)/(x-s)^2 ≤ (s/r)/(r-s)^2 := by
    apply div_le_div₀ (by positivity)
    · exact div_le_div_of_nonneg_left hs hr hrx
    · positivity
    · gcongr
  have hxid : (x/2+3+s/x)/(x-s)^2 =
      (1/2)*(x/(x-s)^2) + 3/(x-s)^2 + (s/x)/(x-s)^2 := by ring
  have hrid : (r/2+3+s/r)/(r-s)^2 =
      (1/2)*(r/(r-s)^2) + 3/(r-s)^2 + (s/r)/(r-s)^2 := by ring
  rw [hxid, hrid]
  linarith

theorem projector_remainder_enlargement (s x : ℝ) (hs : 0 ≤ s) (hsx : s < x) :
    1/(2*x)+(3+s/x)/(x-s)^2 ≤ (x/2+3+s/x)/(x-s)^2 := by
  have hx : 0 < x := hs.trans_lt hsx
  have hd : 0 < x-s := sub_pos.mpr hsx
  have h : 1/(2*x) ≤ (x/2)/(x-s)^2 := by
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hd)).mpr
    nlinarith
  calc
    _ ≤ (x/2)/(x-s)^2+(3+s/x)/(x-s)^2 := add_le_add_left h _
    _ = _ := by ring

/-- The actual changed Laplacian and spectral parameter are controlled by
the center inverse weight and the verifier's common factor χ. -/
theorem shifted_inverse_sqrt_weight (ρ t σ s r x y t' : ℝ)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hσ : 0 ≤ σ) (hs : 0 ≤ s)
    (hsr : s < r) (hrx : r ≤ x) (hxy : x-s ≤ y) (ht' : t' ≤ t+σ)
    (hshift : 0 < (r-s)^2/ρ-t-σ) :
    1 / Real.sqrt (y^2/ρ-t') ≤
      Real.sqrt ((r^2/ρ-t)/((r-s)^2/ρ-t-σ)) / Real.sqrt (x^2/ρ-t) := by
  have hr : 0 < r := hs.trans_lt hsr
  have hx : 0 < x := hr.trans_le hrx
  have hxs : 0 < x-s := sub_pos.mpr (hsr.trans_le hrx)
  have hy : 0 < y := hxs.trans_le hxy
  have hxb : 0 < x^2/ρ-t := by
    have hmon : (r-s)^2/ρ ≤ x^2/ρ := by gcongr; linarith
    linarith
  have hxs' : 0 < (x-s)^2/ρ-t-σ := by
    have hmon : (r-s)^2/ρ ≤ (x-s)^2/ρ := by gcongr
    linarith
  have hnew : (x-s)^2/ρ-t-σ ≤ y^2/ρ-t' := by
    have hmon : (x-s)^2/ρ ≤ y^2/ρ := by gcongr
    linarith
  have hrb : 0 < r^2/ρ-t := by
    have hmon : (r-s)^2/ρ ≤ r^2/ρ := by gcongr; linarith
    linarith
  have hratio := transverse_inverse_ratio ρ t σ s r x hρ ht hσ hs hsr hrx hshift
  have hratio' : (x^2/ρ-t)/(y^2/ρ-t') ≤
      (r^2/ρ-t)/((r-s)^2/ρ-t-σ) := by
    apply le_trans _ hratio
    exact div_le_div_of_nonneg_left hxb.le hxs' hnew
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, div_pow, one_pow, Real.sq_sqrt (hxs'.trans_le hnew).le,
    Real.sq_sqrt hxb.le, Real.sq_sqrt (div_pos hrb hshift).le]
  apply (le_div_iff₀ hxb).mpr
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hratio'

theorem center_inverse_sqrt_weight (ρ t r x : ℝ)
    (hρ : 0 < ρ) (hr : 0 < r) (hrx : r ≤ x) (hbase : 0 < r^2/ρ-t) :
    1/Real.sqrt (x^2/ρ-t) ≤ 1/Real.sqrt (r^2/ρ-t) := by
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hbase)
  apply Real.sqrt_le_sqrt
  have hmon : r^2/ρ ≤ x^2/ρ := by gcongr
  linarith

/-- The low-gradient mixed remainder keeps the inverse-Laplacian weight
on the positive witness, with the exact coefficient `cp` from the verifier. -/
theorem low_projector_cross_coefficient (s r R x : ℝ)
    (hs : 0 ≤ s) (hsr : s < r) (hrx : r ≤ x) (hxR : x ≤ R) :
    1/(x*(x-s))+1/(2*x) ≤
      ((3+s/r)/(1-s/r)^2+(1/2)*R/(1-s/r))/x^2 := by
  have hr : 0 < r := hs.trans_lt hsr
  have hx : 0 < x := hr.trans_le hrx
  have hR : 0 < R := hx.trans_le hxR
  have ha : 0 < 1-s/r := sub_pos.mpr ((div_lt_one hr).mpr hsr)
  have ha1 : 1-s/r ≤ 1 := by linarith [div_nonneg hs hr.le]
  have hd : x*(1-s/r) ≤ x-s := by
    have h := (le_div_iff₀ hr).mpr (mul_le_mul_of_nonneg_left hrx hs)
    change s ≤ s*x/r at h
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith
  have hfirst : x/(x-s) ≤ 1/(1-s/r) := by
    apply (div_le_div_iff₀ (sub_pos.mpr (hsr.trans_le hrx)) ha).mpr
    simpa only [one_mul] using hd
  have hfirst' : 1/(1-s/r) ≤ (3+s/r)/(1-s/r)^2 := by
    apply (div_le_div_iff₀ ha (sq_pos_of_pos ha)).mpr
    have hratio : 0 ≤ s/r := div_nonneg hs hr.le
    nlinarith
  have hsecond : x/2 ≤ (1/2)*R/(1-s/r) := by
    apply (le_div_iff₀ ha).mpr
    have h := mul_le_mul_of_nonneg_left ha1 hx.le
    nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hx)).mpr
  have hid : (1/(x*(x-s))+1/(2*x))*x^2 = x/(x-s)+x/2 := by
    field_simp
  rw [hid]
  linarith

end Maxwell.Spectral.BoxWeights
