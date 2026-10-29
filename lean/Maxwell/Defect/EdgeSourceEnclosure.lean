import Maxwell.Defect.ModeCertificate
import Mathlib.Analysis.SpecificLimits.Normed

/-! Executable rational enclosures of a selected, oriented eigenvector of
an exact rational symmetric matrix. The search reads only rational matrix,
interval, reference, and accuracy data; the real eigenpair occurs only in
the correctness and termination proof. -/

namespace Maxwell.Defect.EdgeSourceEnclosure

open InnerProductSpace Module.End Filter Topology

variable {n : ℕ}

def proposal (c : SimpleCertificate n) (scale : ℚ) : Fin n → ℚ := scale • c.vector

def accepts (T : Matrix (Fin n) (Fin n) ℚ) (left right : ℚ)
    (reference : Fin n → ℚ) (bound accuracy : ℚ)
    (c : SimpleCertificate n) (scale slack : ℚ) : Bool :=
  decide (c.accepts T 0 = true ∧ 0 < scale ∧ 0 < slack ∧ 2 * slack ≤ accuracy ∧
    left < c.target - 2 * c.residual ∧ c.target + 2 * c.residual < right ∧
    8 * c.residual / c.gap ≤ slack ∧
    |scale ^ 2 * rationalNormSq c.vector - 1| ≤ slack ^ 2 ∧
    2 * slack * bound < rationalOverlap (proposal c scale) reference)

theorem scaledVector (v : Fin n → ℚ) (scale : ℚ) :
    rationalVector (scale • v) = (scale : ℝ) • rationalVector v := by
  ext i
  simp [rationalVector]

theorem scaled_unit_error (v : Fin n → ℚ) (hv : v ≠ 0) (scale slack : ℚ)
    (hscale : 0 < scale) (hslack : 0 ≤ slack)
    (hcheck : |scale ^ 2 * rationalNormSq v - 1| ≤ slack ^ 2) :
    ‖rationalVector (scale • v) - rationalUnitVector v‖ ≤ (slack : ℝ) := by
  have hN : 0 < ‖rationalVector v‖ := norm_pos_iff.mpr (rationalVector_ne_zero v hv)
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  have ht : (0 : ℝ) ≤ slack := by exact_mod_cast hslack
  have hcheck' : |(scale : ℝ) ^ 2 * ‖rationalVector v‖ ^ 2 - 1| ≤ (slack : ℝ) ^ 2 := by
    rw [← rationalNormSq_cast]
    exact_mod_cast hcheck
  have hunit : ‖rationalUnitVector v‖ = 1 := rationalUnitVector_norm v hv
  have hrep : rationalVector (scale • v) - rationalUnitVector v =
      ((scale : ℝ) * ‖rationalVector v‖ - 1) • rationalUnitVector v := by
    rw [scaledVector, rationalUnitVector, smul_smul]
    rw [← sub_smul]
    congr 1
    field_simp
  rw [hrep, norm_smul, hunit, mul_one, Real.norm_eq_abs]
  have ha : 0 ≤ (scale : ℝ) * ‖rationalVector v‖ := mul_nonneg hs.le hN.le
  rcases le_total ((scale : ℝ) * ‖rationalVector v‖) 1 with hle | hge
  · rw [abs_of_nonpos (by linarith)]
    have hh := (abs_le.mp hcheck').1
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hle)]
  · rw [abs_of_nonneg (by linarith)]
    have hh := (abs_le.mp hcheck').2
    nlinarith

theorem oriented_eigenvector_unique
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u x b : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) (hSu : S u = μ • u) (hSx : S x = μ • x)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hub : 0 < inner ℝ u b) (hxb : 0 < inner ℝ x b) : x = u := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hspan : eigenspace S.toLinearMap μ = ℝ ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hsimple (mem_eigenspace_iff.mpr hSu) hu0
  have hxmem : x ∈ ℝ ∙ u := hspan ▸ mem_eigenspace_iff.mpr hSx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxmem
  rw [← ha, norm_smul, hu, mul_one, Real.norm_eq_abs] at hx
  have hap : 0 < a := by
    rw [← ha, inner_smul_left] at hxb
    simp only [conj_trivial] at hxb
    exact pos_of_mul_pos_left hxb hub.le
  have hae : a = 1 := by rwa [abs_of_pos hap] at hx
  simpa only [hae, one_smul] using ha.symm

/-- Soundness uses only local finite spectral isolation and a positive
reference overlap to identify the selected real eigenvector. -/
theorem accepts_sound (T : Matrix (Fin n) (Fin n) ℚ) (left right : ℚ)
    (reference : Fin n → ℚ) (bound accuracy : ℚ)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (hu : ‖u‖ = 1) (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1)
    (hisolate : ∀ ν ∈ spectrum ℝ (rationalOperator T),
      ν ∈ Set.Icc (left : ℝ) (right : ℝ) → ν = μ)
    (horient : 0 < inner ℝ u (rationalVector reference))
    (hbound : ‖rationalVector reference‖ ≤ (bound : ℝ))
    (c : SimpleCertificate n) (scale slack : ℚ)
    (hcheck : accepts T left right reference bound accuracy c scale slack = true) :
    ‖u - rationalVector (proposal c scale)‖ ≤ (accuracy : ℝ) := by
  obtain ⟨hc, hs, ht, hbudget, hlo, hhi, hdir, hnorm, hsign⟩ := of_decide_eq_true hcheck
  obtain ⟨hT, hv, _⟩ := of_decide_eq_true hc
  obtain ⟨ν, x, hx, hTx, hν, _, _, hxu, _⟩ := c.sound T 0 (rationalOperator T)
    (rationalOperator_symmetric T hT) (by simp) hc
  simp only [Rat.cast_zero, zero_add] at hν hxu
  have hνμ : ν = μ := by
    apply hisolate ν
    · rw [ContinuousLinearMap.spectrum_eq]
      apply HasEigenvalue.mem_spectrum
      apply hasEigenvalue_iff.mpr
      intro hbot
      have hxmem := mem_eigenspace_iff.mpr hTx
      rw [hbot] at hxmem
      have hxzero : x = 0 := hxmem
      simp [hxzero] at hx
    · have hlo' : (left : ℝ) < (c.target : ℝ) - 2 * (c.residual : ℝ) := by exact_mod_cast hlo
      have hhi' : (c.target : ℝ) + 2 * (c.residual : ℝ) < (right : ℝ) := by exact_mod_cast hhi
      have he := abs_le.mp hν
      constructor <;> linarith
  have hdir' : 8 * (c.residual : ℝ) / (c.gap : ℝ) ≤ (slack : ℝ) := by exact_mod_cast hdir
  have hxu' : ‖x - rationalUnitVector c.vector‖ ≤ (slack : ℝ) := by
    have he : 4 * (2 * (c.residual : ℝ)) / (c.gap : ℝ) =
        8 * (c.residual : ℝ) / (c.gap : ℝ) := by ring
    rw [he] at hxu
    exact hxu.trans hdir'
  have hqu := scaled_unit_error c.vector hv scale slack hs ht.le hnorm
  have hxq : ‖x - rationalVector (proposal c scale)‖ ≤ 2 * (slack : ℝ) := by
    calc
      _ ≤ ‖x - rationalUnitVector c.vector‖ +
        ‖rationalUnitVector c.vector - rationalVector (proposal c scale)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (slack : ℝ) + slack := add_le_add hxu' (by simpa only [proposal, norm_sub_rev] using hqu)
      _ = _ := by ring
  have hxb : 0 < inner ℝ x (rationalVector reference) := by
    have hd : |inner ℝ (rationalVector (proposal c scale)) (rationalVector reference) -
        inner ℝ x (rationalVector reference)| ≤ 2 * (slack : ℝ) * (bound : ℝ) := by
      rw [← inner_sub_left]
      apply (abs_real_inner_le_norm _ _).trans
      apply mul_le_mul _ hbound (norm_nonneg _) (by positivity)
      simpa only [norm_sub_rev] using hxq
    have hs' : 2 * (slack : ℝ) * (bound : ℝ) <
        inner ℝ (rationalVector (proposal c scale)) (rationalVector reference) := by
      rw [← rationalOverlap_cast]
      exact_mod_cast hsign
    have hd' := (abs_le.mp hd).2
    linarith
  have hxu_eq := oriented_eigenvector_unique (rationalOperator T) u x (rationalVector reference)
    μ hu hx hTu (hνμ ▸ hTx) hsimple horient hxb
  rw [hxu_eq] at hxq
  exact hxq.trans (by exact_mod_cast hbudget)

theorem exists_scale (v : Fin n → ℚ) (hv : v ≠ 0) (slack : ℚ) (ht : 0 < slack) :
    ∃ scale : ℚ, 0 < scale ∧ |scale ^ 2 * rationalNormSq v - 1| ≤ slack ^ 2 := by
  have hN : 0 < ‖rationalVector v‖ := norm_pos_iff.mpr (rationalVector_ne_zero v hv)
  obtain ⟨s, hs⟩ := exists_rational_target_sequence (‖rationalVector v‖⁻¹)
  have hz : ‖rationalVector v‖⁻¹ ^ 2 * (rationalNormSq v : ℝ) - 1 = 0 := by
    rw [rationalNormSq_cast]
    field_simp
    ring
  have herr : Tendsto (fun k => |(s k : ℝ) ^ 2 * (rationalNormSq v : ℝ) - 1|)
      atTop (𝓝 0) := by
    simpa only [hz, abs_zero] using (((hs.pow 2).mul_const (rationalNormSq v : ℝ)).sub_const 1).abs
  have ht' : 0 < (slack : ℝ) ^ 2 := by exact_mod_cast sq_pos_of_pos ht
  obtain ⟨k, hkpos, hkerr⟩ := ((hs.eventually_const_lt (inv_pos.mpr hN)).and
    (herr.eventually_lt_const ht')).exists
  exact ⟨s k, by exact_mod_cast hkpos, by exact_mod_cast hkerr.le⟩

/-- Every strict rational isolating interval and positively oriented
reference admits accepted certificates at every positive rational accuracy. -/
theorem accepts_complete (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm)
    (left right : ℚ) (reference : Fin n → ℚ) (bound accuracy : ℚ)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (hu : ‖u‖ = 1) (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1)
    (hleft : (left : ℝ) < μ) (hright : μ < (right : ℝ))
    (horient : 0 < inner ℝ u (rationalVector reference))
    (hbound : ‖rationalVector reference‖ ≤ (bound : ℝ)) (hboundpos : 0 < bound)
    (haccuracy : 0 < accuracy) :
    ∃ (c : SimpleCertificate n) (scale slack : ℚ),
      accepts T left right reference bound accuracy c scale slack = true := by
  have hM : (0 : ℝ) < bound := by exact_mod_cast hboundpos
  have ha : (0 : ℝ) < accuracy := by exact_mod_cast haccuracy
  obtain ⟨slack, ht0, ht⟩ := exists_rat_btwn (show (0 : ℝ) <
    min ((accuracy : ℝ) / 2) (inner ℝ u (rationalVector reference) / (8 * (bound : ℝ))) by positivity)
  have hslack : (0 : ℚ) < slack := by exact_mod_cast ht0
  have hbudget : 2 * slack ≤ accuracy := by
    have h := ht.trans_le (min_le_left _ _)
    exact_mod_cast (show 2 * (slack : ℝ) ≤ (accuracy : ℝ) by linarith)
  have hmargin : 4 * (slack : ℝ) * (bound : ℝ) < inner ℝ u (rationalVector reference) := by
    have h := (lt_div_iff₀ (show (0 : ℝ) < 8 * (bound : ℝ) by positivity)).mp
      (ht.trans_le (min_le_right _ _))
    nlinarith
  let a : ℝ := min (slack : ℝ) (min ((μ - left) / 4) (((right : ℝ) - μ) / 4))
  have ha0 : 0 < a := by dsimp only [a]; positivity
  have hat : a ≤ (slack : ℝ) := min_le_left _ _
  have hal : a ≤ (μ - left) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have har : a ≤ ((right : ℝ) - μ) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨_, c, hc, htarget, hvector, hres, _, hdir⟩ :=
    (simpleCertificate_complete_eventually (rationalOperator T) u μ
      (fun _ => T) (fun _ => 0) hu hTu hsimple (fun _ => hT) (fun _ => le_rfl)
      tendsto_const_nhds (by simp)
      a ha0).exists
  simp only [Rat.cast_zero, zero_add] at hres hdir
  have hv : c.vector ≠ 0 := (of_decide_eq_true hc).2.1
  obtain ⟨scale, hs, hnorm⟩ := exists_scale c.vector hv slack hslack
  have hqu := scaled_unit_error c.vector hv scale slack hs hslack.le hnorm
  have hqu' : ‖rationalVector (proposal c scale) - u‖ ≤ 2 * (slack : ℝ) := by
    calc
      _ ≤ ‖rationalVector (proposal c scale) - rationalUnitVector c.vector‖ +
        ‖rationalUnitVector c.vector - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (slack : ℝ) + slack := add_le_add hqu (hvector.le.trans hat)
      _ = _ := by ring
  have hover : 2 * (slack : ℝ) * (bound : ℝ) <
      inner ℝ (rationalVector (proposal c scale)) (rationalVector reference) := by
    have hdiff : |inner ℝ (rationalVector (proposal c scale)) (rationalVector reference) -
        inner ℝ u (rationalVector reference)| ≤ 2 * (slack : ℝ) * (bound : ℝ) := by
      rw [← inner_sub_left]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul hqu' hbound (norm_nonneg _) (by positivity))
    have hd := (abs_le.mp hdiff).1
    linarith
  refine ⟨c, scale, slack, decide_eq_true ?_⟩
  refine ⟨hc, hs, hslack, hbudget, ?_, ?_, ?_, hnorm, ?_⟩
  · have hh := (abs_lt.mp htarget).1
    exact_mod_cast (show (left : ℝ) < (c.target : ℝ) - 2 * (c.residual : ℝ) by linarith)
  · have hh := (abs_lt.mp htarget).2
    exact_mod_cast (show (c.target : ℝ) + 2 * (c.residual : ℝ) < (right : ℝ) by linarith)
  · have hh : 8 * (c.residual : ℝ) / (c.gap : ℝ) ≤ (slack : ℝ) := by
      convert hdir.le.trans hat using 1
      ring
    exact_mod_cast hh
  · rw [← rationalOverlap_cast] at hover
    exact_mod_cast hover

/-- All runtime search data are rational and finitely encoded. -/
def check (T : Matrix (Fin n) (Fin n) ℚ) (left right : ℚ)
    (reference : Fin n → ℚ) (bound accuracy : ℚ) (code : ℕ) : Bool :=
  match Encodable.decode (α := SimpleCertificate n × ℚ × ℚ) code with
  | none => false
  | some (c, scale, slack) => accepts T left right reference bound accuracy c scale slack

def decodeVector (code : ℕ) : Fin n → ℚ :=
  match Encodable.decode (α := SimpleCertificate n × ℚ × ℚ) code with
  | none => 0
  | some (c, scale, _) => proposal c scale

theorem check_complete (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm)
    (left right : ℚ) (reference : Fin n → ℚ) (bound accuracy : ℚ)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (hu : ‖u‖ = 1) (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1)
    (hleft : (left : ℝ) < μ) (hright : μ < (right : ℝ))
    (horient : 0 < inner ℝ u (rationalVector reference))
    (hbound : ‖rationalVector reference‖ ≤ (bound : ℝ)) (hboundpos : 0 < bound)
    (haccuracy : 0 < accuracy) :
    ∃ code, check T left right reference bound accuracy code = true := by
  obtain ⟨c, scale, slack, hc⟩ := accepts_complete T hT left right reference bound accuracy
    u μ hu hTu hsimple hleft hright horient hbound hboundpos haccuracy
  exact ⟨Encodable.encode (c, scale, slack), by simp [check, hc]⟩

/-- Proof of termination is erased; execution enumerates rational
certificates and returns the first accepted rational vector. -/
def search (T : Matrix (Fin n) (Fin n) ℚ) (left right : ℚ)
    (reference : Fin n → ℚ) (bound accuracy : ℚ)
    (h : ∃ code, check T left right reference bound accuracy code = true) : Fin n → ℚ :=
  decodeVector (Nat.find h)

theorem check_sound (T : Matrix (Fin n) (Fin n) ℚ) (left right : ℚ)
    (reference : Fin n → ℚ) (bound accuracy : ℚ)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (hu : ‖u‖ = 1) (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1)
    (hisolate : ∀ ν ∈ spectrum ℝ (rationalOperator T),
      ν ∈ Set.Icc (left : ℝ) (right : ℝ) → ν = μ)
    (horient : 0 < inner ℝ u (rationalVector reference))
    (hbound : ‖rationalVector reference‖ ≤ (bound : ℝ)) (code : ℕ)
    (hcheck : check T left right reference bound accuracy code = true) :
    ‖u - rationalVector (decodeVector code)‖ ≤ (accuracy : ℝ) := by
  cases hd : Encodable.decode (α := SimpleCertificate n × ℚ × ℚ) code with
  | none => simp [check, hd] at hcheck
  | some c =>
    simp only [check, hd] at hcheck
    simp only [decodeVector, hd]
    exact accepts_sound T left right reference bound accuracy u μ hu hTu hsimple
      hisolate horient hbound c.1 c.2.1 c.2.2 hcheck

def accuracy (k : ℕ) : ℚ := 1 / ((k : ℚ) + 1)

theorem accuracy_pos (k : ℕ) : 0 < accuracy k := by unfold accuracy; positivity

theorem accuracy_tendsto : Tendsto (fun k => (accuracy k : ℝ)) atTop (𝓝 0) := by
  simpa only [accuracy, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

def sequence (T : Matrix (Fin n) (Fin n) ℚ) (left right : ℚ)
    (reference : Fin n → ℚ) (bound : ℚ)
    (h : ∀ k, ∃ code, check T left right reference bound (accuracy k) code = true)
    (k : ℕ) : Fin n → ℚ := search T left right reference bound (accuracy k) (h k)

theorem sequence_error (T : Matrix (Fin n) (Fin n) ℚ) (left right : ℚ)
    (reference : Fin n → ℚ) (bound : ℚ)
    (h : ∀ k, ∃ code, check T left right reference bound (accuracy k) code = true)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (hu : ‖u‖ = 1) (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1)
    (hisolate : ∀ ν ∈ spectrum ℝ (rationalOperator T),
      ν ∈ Set.Icc (left : ℝ) (right : ℝ) → ν = μ)
    (horient : 0 < inner ℝ u (rationalVector reference))
    (hbound : ‖rationalVector reference‖ ≤ (bound : ℝ)) (k : ℕ) :
    ‖u - rationalVector (sequence T left right reference bound h k)‖ ≤ (accuracy k : ℝ) :=
  check_sound T left right reference bound (accuracy k) u μ hu hTu hsimple hisolate horient hbound
    _ (Nat.find_spec (h k))

/-- An executable rational norm bound for any supplied reference vector. -/
def referenceBound (reference : Fin n → ℚ) : ℚ := 1 + ∑ i, |reference i|

theorem referenceBound_pos (reference : Fin n → ℚ) : 0 < referenceBound reference := by
  have h : (0 : ℚ) ≤ ∑ i, |reference i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  unfold referenceBound
  linarith

theorem reference_norm_le (reference : Fin n → ℚ) :
    ‖rationalVector reference‖ ≤ (referenceBound reference : ℝ) := by
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i : Fin n => |(reference i : ℝ)|) (fun _ _ => abs_nonneg _)
  simp only [sq_abs] at hsq
  have hnorm : ‖rationalVector reference‖ ^ 2 = ∑ i, (reference i : ℝ) ^ 2 := by
    simp [rationalVector, EuclideanSpace.real_norm_sq_eq]
  have hsum : (0 : ℝ) ≤ ∑ i, |(reference i : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hle : ‖rationalVector reference‖ ≤ ∑ i, |(reference i : ℝ)| := by
    nlinarith [norm_nonneg (rationalVector reference)]
  simp only [referenceBound, Rat.cast_add, Rat.cast_one, Rat.cast_sum, Rat.cast_abs]
  linarith

/-- The actual simple eigenpair proves termination at every precision.
The finite program receives this theorem only as an erased proof. -/
theorem sequence_terminates (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm)
    (left right : ℚ) (reference : Fin n → ℚ)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (hu : ‖u‖ = 1) (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1)
    (hleft : (left : ℝ) < μ) (hright : μ < (right : ℝ))
    (horient : 0 < inner ℝ u (rationalVector reference)) :
    ∀ k, ∃ code, check T left right reference (referenceBound reference) (accuracy k) code = true := by
  intro k
  exact check_complete T hT left right reference (referenceBound reference) (accuracy k)
    u μ hu hTu hsimple hleft hright horient (reference_norm_le reference)
    (referenceBound_pos reference) (accuracy_pos k)

/-- Certified rational eigenvector enclosures with an explicit vanishing
error sequence, derived from the actual finite matrix and isolated mode. -/
theorem certified_sequence (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm)
    (left right : ℚ) (reference : Fin n → ℚ)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (hu : ‖u‖ = 1) (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1)
    (hleft : (left : ℝ) < μ) (hright : μ < (right : ℝ))
    (hisolate : ∀ ν ∈ spectrum ℝ (rationalOperator T),
      ν ∈ Set.Icc (left : ℝ) (right : ℝ) → ν = μ)
    (horient : 0 < inner ℝ u (rationalVector reference)) :
    let h := sequence_terminates T hT left right reference u μ hu hTu hsimple hleft hright horient
    (∀ k, ‖u - rationalVector (sequence T left right reference (referenceBound reference) h k)‖ ≤
      (accuracy k : ℝ)) ∧ Tendsto (fun k => (accuracy k : ℝ)) atTop (𝓝 0) := by
  dsimp only
  exact ⟨fun k => sequence_error T left right reference (referenceBound reference) _
    u μ hu hTu hsimple hisolate horient (reference_norm_le reference) k, accuracy_tendsto⟩

end Maxwell.Defect.EdgeSourceEnclosure
