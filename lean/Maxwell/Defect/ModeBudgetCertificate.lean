import Maxwell.Defect.ModeCertificate

/-! A finite rational stopping test for the strict numerator margin. -/
namespace Maxwell.Defect
open Filter Topology Module.End
variable {n : ℕ}

def certifiedOverlapLower (c : SimpleCertificate n) (a error β M : ℚ) : ℚ :=
  a - β - M * (4 * (error + 2 * c.residual) / c.gap)

def modeBudgetAccepts (c : SimpleCertificate n) (a : ℚ)
    (T : Matrix (Fin n) (Fin n) ℚ) (error threshold : ℚ)
    (q : Fin n → ℚ) (β M budget : ℚ) : Bool :=
  modeCertificateAccepts c a T error threshold q β M &&
    decide (0 ≤ budget ∧ budget < (certifiedOverlapLower c a error β M) ^ 2 ∧
      8 * (error + 2 * c.residual) < c.gap)

theorem modeBudget_sound (c : SimpleCertificate n) (a : ℚ)
    (T : Matrix (Fin n) (Fin n) ℚ) (error threshold : ℚ)
    (q : Fin n → ℚ) (β M budget : ℚ)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n))
    (hS : S.toLinearMap.IsSymmetric) (happrox : ‖S - rationalOperator T‖ ≤ (error : ℝ))
    (hq : ‖w - rationalVector q‖ ≤ (β : ℝ)) (hw : ‖w‖ ≤ (M : ℝ))
    (hcheck : modeBudgetAccepts c a T error threshold q β M budget = true) :
    ∃ ν : ℝ, ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧ S x = ν • x ∧
      (threshold : ℝ) < ν ∧ Module.finrank ℝ (eigenspace S.toLinearMap ν) = 1 ∧
      (budget : ℝ) < |inner ℝ w x| ^ 2 := by
  obtain ⟨hc, hb⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨ν, x, hx, he, hν, hdim, hpos, hlow, _, _⟩ :=
    modeCertificate_sound c a T error threshold q β M S w hS happrox hq hw hc
  have hb' : (budget : ℝ) < ((certifiedOverlapLower c a error β M : ℚ) : ℝ) ^ 2 := by
    exact_mod_cast (of_decide_eq_true hb).2.1
  simp only [certifiedOverlapLower, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_add, Rat.cast_ofNat] at hb'
  exact ⟨ν, x, hx, he, hν, hdim, hb'.trans_le (pow_le_pow_left₀ hpos.le hlow 2)⟩

theorem modeBudget_complete_eventually
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u w : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (error : ℕ → ℚ) (threshold budget : ℚ)
    (q : ℕ → Fin n → ℚ) (β : ℕ → ℚ) (M : ℚ)
    (hu : ‖u‖ = 1) (hSu : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hthreshold : (threshold : ℝ) < μ) (hoverlap : inner ℝ w u ≠ 0)
    (hbudget : 0 ≤ budget) (hmargin : (budget : ℝ) < |inner ℝ w u| ^ 2 / 64)
    (hT : ∀ k, (T k).IsSymm) (herror : ∀ k, 0 ≤ error k)
    (hTlim : Tendsto (fun k => rationalOperator (T k)) atTop (𝓝 S))
    (herrlim : Tendsto (fun k => (error k : ℝ)) atTop (𝓝 0))
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hβlim : Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0))
    (hw : ‖w‖ ≤ (M : ℝ)) (hM : 0 < M) :
    ∃ a : ℚ, 0 < a ∧ ∀ᶠ k in atTop, ∃ c : SimpleCertificate n,
      modeBudgetAccepts c a (T k) (error k) threshold (q k) (β k) M budget = true := by
  obtain ⟨a, ha, halow, hc⟩ := modeCertificate_complete_eventually_strong S u w μ T error
    threshold q β M hu hSu hsimple hthreshold hoverlap hT herror hTlim herrlim hq hβlim hw hM
  refine ⟨a, ha, hc.mono ?_⟩
  rintro k ⟨c, hc, hlow, hsmall⟩
  have hlo : |inner ℝ w u| / 8 < (certifiedOverlapLower c a (error k) (β k) M : ℝ) := by
    simp only [certifiedOverlapLower, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_add, Rat.cast_ofNat]
    linarith
  have hsq : (|inner ℝ w u| / 8) ^ 2 <
      (certifiedOverlapLower c a (error k) (β k) M : ℝ) ^ 2 := by
    nlinarith [abs_nonneg (inner ℝ w u)]
  have hb : budget < (certifiedOverlapLower c a (error k) (β k) M) ^ 2 := by
    have hh : (budget : ℝ) < (certifiedOverlapLower c a (error k) (β k) M : ℝ) ^ 2 := by
      nlinarith
    exact_mod_cast hh
  exact ⟨c, Bool.and_eq_true_iff.mpr ⟨hc, decide_eq_true ⟨hbudget, hb, hsmall⟩⟩⟩

def modeBudgetCheck (T : Matrix (Fin n) (Fin n) ℚ) (error threshold : ℚ)
    (q : Fin n → ℚ) (β M budget : ℚ) (code : ℕ) : Bool :=
  match Encodable.decode (α := SimpleCertificate n × ℚ) code with
  | none => false
  | some (c, a) => modeBudgetAccepts c a T error threshold q β M budget

theorem modeBudget_search_terminates
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u w : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (error : ℕ → ℚ) (threshold budget : ℚ)
    (q : ℕ → Fin n → ℚ) (β : ℕ → ℚ) (M : ℚ)
    (hu : ‖u‖ = 1) (hSu : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hthreshold : (threshold : ℝ) < μ) (hoverlap : inner ℝ w u ≠ 0)
    (hbudget : 0 ≤ budget) (hmargin : (budget : ℝ) < |inner ℝ w u| ^ 2 / 64)
    (hT : ∀ k, (T k).IsSymm) (herror : ∀ k, 0 ≤ error k)
    (hTlim : Tendsto (fun k => rationalOperator (T k)) atTop (𝓝 S))
    (herrlim : Tendsto (fun k => (error k : ℝ)) atTop (𝓝 0))
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hβlim : Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0))
    (hw : ‖w‖ ≤ (M : ℝ)) (hM : 0 < M) :
    ∃ stage : ℕ, modeBudgetCheck (T (Nat.unpair stage).1) (error (Nat.unpair stage).1)
      threshold (q (Nat.unpair stage).1) (β (Nat.unpair stage).1) M budget
        (Nat.unpair stage).2 = true := by
  obtain ⟨a, _, h⟩ := modeBudget_complete_eventually S u w μ T error threshold budget q β M
    hu hSu hsimple hthreshold hoverlap hbudget hmargin hT herror hTlim herrlim hq hβlim hw hM
  obtain ⟨k, c, hc⟩ := h.exists
  exact ⟨Nat.pair k (Encodable.encode (c, a)), by simpa [modeBudgetCheck] using hc⟩

end Maxwell.Defect
