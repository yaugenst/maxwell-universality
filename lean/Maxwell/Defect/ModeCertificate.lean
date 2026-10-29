import Maxwell.Defect.SimpleCertificate

/-! Finite rational certificates for a simple mode above a threshold with
a strictly positive, explicitly bounded source overlap. -/
namespace Maxwell.Defect

open InnerProductSpace Filter Topology Module.End

variable {n : ℕ}

def rationalOverlap (q v : Fin n → ℚ) : ℚ := ∑ i, q i * v i

/-- Every acceptance condition is rational and finite, including the
overlap bound for the irrationally normalized candidate vector. -/
def modeCertificateAccepts (c : SimpleCertificate n) (a : ℚ)
    (T : Matrix (Fin n) (Fin n) ℚ) (error threshold : ℚ)
    (q : Fin n → ℚ) (β M : ℚ) : Bool :=
  let κ := error + 2 * c.residual
  decide (c.accepts T error = true ∧ 0 ≤ β ∧ 0 < M ∧ 0 < a ∧
    threshold < c.target - κ ∧
    a ^ 2 * rationalNormSq c.vector ≤ rationalOverlap q c.vector ^ 2 ∧
    β + M * (4 * κ / c.gap) < a)

theorem rationalOverlap_cast (q v : Fin n → ℚ) :
    (rationalOverlap q v : ℝ) = inner ℝ (rationalVector q) (rationalVector v) := by
  simp [rationalOverlap, rationalVector, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, mul_comm]

theorem rationalOverlap_normalized (q v : Fin n → ℚ) :
    inner ℝ (rationalVector q) (rationalUnitVector v) =
      ‖rationalVector v‖⁻¹ * (rationalOverlap q v : ℝ) := by
  rw [rationalUnitVector, inner_smul_right, rationalOverlap_cast]

theorem rationalOverlap_lower_iff (q v : Fin n → ℚ) (a : ℚ)
    (hv : v ≠ 0) (ha : 0 ≤ a) :
    a ^ 2 * rationalNormSq v ≤ rationalOverlap q v ^ 2 ↔
      (a : ℝ) ≤ |inner ℝ (rationalVector q) (rationalUnitVector v)| := by
  have hn := norm_pos_iff.mpr (rationalVector_ne_zero v hv)
  have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
  rw [rationalOverlap_normalized, abs_mul, abs_of_pos (inv_pos.mpr hn)]
  have hc : a ^ 2 * rationalNormSq v ≤ rationalOverlap q v ^ 2 ↔
      (a : ℝ) ^ 2 * ‖rationalVector v‖ ^ 2 ≤ (rationalOverlap q v : ℝ) ^ 2 := by
    rw [← rationalNormSq_cast]
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor
  · intro h
    have hb : (a : ℝ) * ‖rationalVector v‖ ≤ |(rationalOverlap q v : ℝ)| := by
      nlinarith [abs_nonneg (rationalOverlap q v : ℝ), sq_abs (rationalOverlap q v : ℝ),
        mul_nonneg har hn.le]
    calc
      (a : ℝ) = ‖rationalVector v‖⁻¹ * ((a : ℝ) * ‖rationalVector v‖) := by field_simp
      _ ≤ ‖rationalVector v‖⁻¹ * |(rationalOverlap q v : ℝ)| := by gcongr
  · intro h
    have hb : (a : ℝ) * ‖rationalVector v‖ ≤ |(rationalOverlap q v : ℝ)| := by
      have hh := mul_le_mul_of_nonneg_right h hn.le
      field_simp at hh
      nlinarith
    have hh := pow_le_pow_left₀ (mul_nonneg har hn.le) hb 2
    simpa only [mul_pow, sq_abs] using hh

/-- Stability of the scalar overlap accounts separately for the certified
source enclosure and the certified eigenvector direction. -/
theorem source_overlap_difference_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w q u x : E) (β M d : ℝ) (hu : ‖u‖ = 1)
    (hq : ‖w - q‖ ≤ β) (hw : ‖w‖ ≤ M) (hdir : ‖x - u‖ ≤ d) :
    |inner ℝ q u - inner ℝ w x| ≤ β + M * d := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hw
  have hfirst : |inner ℝ q u - inner ℝ w u| ≤ β := by
    rw [← inner_sub_left]
    calc
      _ ≤ ‖q - w‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ β := by simpa [hu, norm_sub_rev] using hq
  have hsecond : |inner ℝ w u - inner ℝ w x| ≤ M * d := by
    rw [← inner_sub_right]
    calc
      _ ≤ ‖w‖ * ‖u - x‖ := abs_real_inner_le_norm _ _
      _ ≤ M * d := by rw [norm_sub_rev]; gcongr
  calc
    _ ≤ |inner ℝ q u - inner ℝ w u| + |inner ℝ w u - inner ℝ w x| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add hfirst hsecond

theorem source_overlap_enclosure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w q u x : E) (β M d : ℝ) (hu : ‖u‖ = 1)
    (hq : ‖w - q‖ ≤ β) (hw : ‖w‖ ≤ M) (hdir : ‖x - u‖ ≤ d) :
    |inner ℝ q u| - β - M * d ≤ |inner ℝ w x| := by
  have htotal := source_overlap_difference_bound w q u x β M d hu hq hw hdir
  have habs := abs_sub_abs_le_abs_sub (inner ℝ q u) (inner ℝ w x)
  linarith

/-- Acceptance certifies the true operator's mode and a positive numerical
lower bound on its actual source overlap. -/
theorem modeCertificate_sound (c : SimpleCertificate n) (a : ℚ)
    (T : Matrix (Fin n) (Fin n) ℚ) (error threshold : ℚ)
    (q : Fin n → ℚ) (β M : ℚ)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n))
    (hS : S.toLinearMap.IsSymmetric) (happrox : ‖S - rationalOperator T‖ ≤ (error : ℝ))
    (hq : ‖w - rationalVector q‖ ≤ (β : ℝ)) (hw : ‖w‖ ≤ (M : ℝ))
    (hcheck : modeCertificateAccepts c a T error threshold q β M = true) :
    let κ : ℝ := (error : ℝ) + 2 * (c.residual : ℝ)
    ∃ ν : ℝ, ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧ S x = ν • x ∧
      (threshold : ℝ) < ν ∧ Module.finrank ℝ (eigenspace S.toLinearMap ν) = 1 ∧
      0 < (a : ℝ) - (β : ℝ) - (M : ℝ) * (4 * κ / (c.gap : ℝ)) ∧
      (a : ℝ) - (β : ℝ) - (M : ℝ) * (4 * κ / (c.gap : ℝ)) ≤ |inner ℝ w x| ∧
      |ν - (c.target : ℝ)| ≤ κ ∧
      ‖x - rationalUnitVector c.vector‖ ≤ 4 * κ / (c.gap : ℝ) := by
  dsimp only
  obtain ⟨hc, _, _, ha, hthreshold, hoverlap, hmargin⟩ := of_decide_eq_true hcheck
  obtain ⟨ν, x, hx, hSx, hν, hdim, _, hdir, _⟩ := c.sound T error S hS happrox hc
  have hv : c.vector ≠ 0 := (of_decide_eq_true hc).2.1
  have hlow := (rationalOverlap_lower_iff q c.vector a hv ha.le).mp hoverlap
  have hthr : (threshold : ℝ) < (c.target : ℝ) -
      ((error : ℝ) + 2 * (c.residual : ℝ)) := by exact_mod_cast hthreshold
  have hpos : 0 < (a : ℝ) - (β : ℝ) - (M : ℝ) *
      (4 * ((error : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ)) := by
    have hm : (β : ℝ) + (M : ℝ) *
        (4 * ((error : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ)) < a := by
      exact_mod_cast hmargin
    linarith
  refine ⟨ν, x, hx, hSx, ?_, hdim, hpos, ?_, hν, hdir⟩
  · have hn := (abs_le.mp hν).1
    linarith
  · have h := source_overlap_enclosure w (rationalVector q) (rationalUnitVector c.vector) x
      β M (4 * ((error : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ))
      (rationalUnitVector_norm _ hv) hq hw hdir
    linarith

/-- Every actual simple mode strictly above the threshold with nonzero
source overlap eventually passes the finite checker. Rational source
enclosures suffice; the checker never needs an exact irrational source. -/
theorem modeCertificate_complete_eventually_strong
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u w : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (error : ℕ → ℚ) (threshold : ℚ)
    (q : ℕ → Fin n → ℚ) (β : ℕ → ℚ) (M : ℚ)
    (hu : ‖u‖ = 1) (hSu : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hthreshold : (threshold : ℝ) < μ) (hoverlap : inner ℝ w u ≠ 0)
    (hT : ∀ k, (T k).IsSymm) (herror : ∀ k, 0 ≤ error k)
    (hTlim : Tendsto (fun k => rationalOperator (T k)) atTop (𝓝 S))
    (herrlim : Tendsto (fun k => (error k : ℝ)) atTop (𝓝 0))
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hβlim : Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0))
    (hw : ‖w‖ ≤ (M : ℝ)) (hM : 0 < M) :
    ∃ a : ℚ, 0 < a ∧ |inner ℝ w u| / 4 < (a : ℝ) ∧
      ∀ᶠ k in atTop, ∃ c : SimpleCertificate n,
        modeCertificateAccepts c a (T k) (error k) threshold (q k) (β k) M = true ∧
        (a : ℝ) / 2 < (a : ℝ) - (β k : ℝ) -
          (M : ℝ) * (4 * ((error k : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ)) ∧
        8 * (error k + 2 * c.residual) < c.gap := by
  have hs : 0 < |inner ℝ w u| := abs_pos.mpr hoverlap
  obtain ⟨a, haL, haU⟩ := exists_rat_btwn
    (show |inner ℝ w u| / 4 < |inner ℝ w u| / 2 by linarith)
  have ha0 : (0 : ℝ) < a := by linarith
  have ha : (0 : ℚ) < a := by exact_mod_cast ha0
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let δ := min ((μ - (threshold : ℝ)) / 4) ((a : ℝ) / (4 * (M : ℝ)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδthreshold : δ ≤ (μ - (threshold : ℝ)) / 4 := min_le_left _ _
  have hδoverlap : (M : ℝ) * δ ≤ (a : ℝ) / 4 := by
    have hh : δ ≤ (a : ℝ) / (4 * (M : ℝ)) := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_left hh hMr.le
    convert hm using 1
    field_simp
  have hc := simpleCertificate_complete_eventually S u μ T error hu hSu hsimple
    hT herror hTlim herrlim δ hδ
  refine ⟨a, ha, haL, ?_⟩
  filter_upwards [hc, hβlim.eventually_lt_const (show (0 : ℝ) < (a : ℝ) / 4 by positivity)]
    with k hk hβsmall
  obtain ⟨c, hc, htarget, hvec, hκ, hg, hdir⟩ := hk
  have hv : c.vector ≠ 0 := (of_decide_eq_true hc).2.1
  have hβ0r : (0 : ℝ) ≤ β k := (norm_nonneg _).trans (hq k)
  have hβ0 : 0 ≤ β k := by exact_mod_cast hβ0r
  have hth : threshold < c.target - (error k + 2 * c.residual) := by
    have ht := (abs_lt.mp htarget).1
    have hh : (threshold : ℝ) < (c.target : ℝ) -
        ((error k : ℝ) + 2 * (c.residual : ℝ)) := by linarith
    exact_mod_cast hh
  have hdiff := source_overlap_difference_bound w (rationalVector (q k))
    (rationalUnitVector c.vector) u (β k) M δ (rationalUnitVector_norm _ hv)
    (hq k) hw (by simpa only [norm_sub_rev] using hvec.le)
  have habs := abs_sub_abs_le_abs_sub (inner ℝ w u)
    (inner ℝ (rationalVector (q k)) (rationalUnitVector c.vector))
  rw [abs_sub_comm] at habs
  have hlower : (a : ℝ) ≤ |inner ℝ (rationalVector (q k)) (rationalUnitVector c.vector)| := by
    linarith
  have hmargin : β k + M * (4 * (error k + 2 * c.residual) / c.gap) < a := by
    have hd := mul_lt_mul_of_pos_left hdir hMr
    have hh : (β k : ℝ) + (M : ℝ) *
        (4 * ((error k : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ)) < a := by linarith
    exact_mod_cast hh
  refine ⟨c, decide_eq_true ?_, ?_, ?_⟩
  · exact ⟨hc, hβ0, hM, ha, hth, (rationalOverlap_lower_iff _ _ _ hv ha.le).mpr hlower, hmargin⟩
  · have hd := mul_lt_mul_of_pos_left hdir hMr
    linarith
  · have hi : |inner ℝ w u| ≤ (M : ℝ) := by
      simpa only [hu, mul_one] using (abs_real_inner_le_norm w u).trans
        (mul_le_mul_of_nonneg_right hw (norm_nonneg u))
    have hδsmall : δ < 1 / 2 := by nlinarith
    have hgr : (0 : ℝ) < c.gap := by exact_mod_cast hg
    have hd := (div_lt_iff₀ hgr).mp (hdir.trans hδsmall)
    have hh : 8 * ((error k : ℝ) + 2 * (c.residual : ℝ)) < (c.gap : ℝ) := by linarith
    exact_mod_cast hh

theorem modeCertificate_complete_eventually
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u w : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (error : ℕ → ℚ) (threshold : ℚ)
    (q : ℕ → Fin n → ℚ) (β : ℕ → ℚ) (M : ℚ)
    (hu : ‖u‖ = 1) (hSu : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hthreshold : (threshold : ℝ) < μ) (hoverlap : inner ℝ w u ≠ 0)
    (hT : ∀ k, (T k).IsSymm) (herror : ∀ k, 0 ≤ error k)
    (hTlim : Tendsto (fun k => rationalOperator (T k)) atTop (𝓝 S))
    (herrlim : Tendsto (fun k => (error k : ℝ)) atTop (𝓝 0))
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hβlim : Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0))
    (hw : ‖w‖ ≤ (M : ℝ)) (hM : 0 < M) :
    ∃ a : ℚ, 0 < a ∧ ∀ᶠ k in atTop, ∃ c : SimpleCertificate n,
      modeCertificateAccepts c a (T k) (error k) threshold (q k) (β k) M = true := by
  obtain ⟨a, ha, _, hc⟩ := modeCertificate_complete_eventually_strong S u w μ T error threshold
    q β M hu hSu hsimple hthreshold hoverlap hT herror hTlim herrlim hq hβlim hw hM
  refine ⟨a, ha, hc.mono ?_⟩
  rintro k ⟨c, hc, _⟩
  exact ⟨c, hc⟩

/-- A natural-number proposal decodes all mode-certificate fields and runs
the exact finite checker. -/
def modeCertificateCheck (T : Matrix (Fin n) (Fin n) ℚ) (error threshold : ℚ)
    (q : Fin n → ℚ) (β M : ℚ) (code : ℕ) : Bool :=
  match Encodable.decode (α := SimpleCertificate n × ℚ) code with
  | none => false
  | some (c, a) => modeCertificateAccepts c a T error threshold q β M

@[simp] theorem modeCertificateCheck_encode (c : SimpleCertificate n) (a : ℚ)
    (T : Matrix (Fin n) (Fin n) ℚ) (error threshold : ℚ)
    (q : Fin n → ℚ) (β M : ℚ) :
    modeCertificateCheck T error threshold q β M (Encodable.encode (c, a)) =
      modeCertificateAccepts c a T error threshold q β M := by
  simp [modeCertificateCheck, Encodable.encodek]

theorem modeCertificateCheck_witness (T : Matrix (Fin n) (Fin n) ℚ) (error threshold : ℚ)
    (q : Fin n → ℚ) (β M : ℚ) (code : ℕ)
    (hcheck : modeCertificateCheck T error threshold q β M code = true) :
    ∃ c : SimpleCertificate n, ∃ a : ℚ,
      modeCertificateAccepts c a T error threshold q β M = true := by
  cases h : Encodable.decode (α := SimpleCertificate n × ℚ) code with
  | none => simp [modeCertificateCheck, h] at hcheck
  | some z => exact ⟨z.1, z.2, by simpa [modeCertificateCheck, h] using hcheck⟩

/-- Fair enumeration of precision and all finite certificate fields finds
every actual simple mode with strict threshold and overlap margins. -/
theorem modeCertificate_search_terminates
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u w : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (error : ℕ → ℚ) (threshold : ℚ)
    (q : ℕ → Fin n → ℚ) (β : ℕ → ℚ) (M : ℚ)
    (hu : ‖u‖ = 1) (hSu : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hthreshold : (threshold : ℝ) < μ) (hoverlap : inner ℝ w u ≠ 0)
    (hT : ∀ k, (T k).IsSymm) (herror : ∀ k, 0 ≤ error k)
    (hTlim : Tendsto (fun k => rationalOperator (T k)) atTop (𝓝 S))
    (herrlim : Tendsto (fun k => (error k : ℝ)) atTop (𝓝 0))
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hβlim : Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0))
    (hw : ‖w‖ ≤ (M : ℝ)) (hM : 0 < M) :
    ∃ stage : ℕ,
      modeCertificateCheck (T (Nat.unpair stage).1) (error (Nat.unpair stage).1)
        threshold (q (Nat.unpair stage).1) (β (Nat.unpair stage).1) M
        (Nat.unpair stage).2 = true := by
  obtain ⟨a, _, hevent⟩ := modeCertificate_complete_eventually S u w μ T error threshold q β M
    hu hSu hsimple hthreshold hoverlap hT herror hTlim herrlim hq hβlim hw hM
  obtain ⟨k, c, hc⟩ := hevent.exists
  refine ⟨Nat.pair k (Encodable.encode (c, a)), ?_⟩
  simpa only [Nat.unpair_pair, modeCertificateCheck_encode] using hc

end Maxwell.Defect
