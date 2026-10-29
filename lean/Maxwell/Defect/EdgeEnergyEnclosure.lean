import Maxwell.Defect.EdgeSourceReference

/-! Executable rational enclosures of the actual isolated finite-matrix
edge energy. The real eigenvalue occurs only in soundness and termination
proofs; the search reads the exact rational matrix and isolating interval. -/

namespace Maxwell.Defect.EdgeEnergyEnclosure

open Filter Topology InnerProductSpace Module.End

variable {n : ℕ}

def accepts (T : Matrix (Fin n) (Fin n) ℚ) (left right accuracy : ℚ)
    (c : SimpleCertificate n) : Bool :=
  decide (c.accepts T 0 = true ∧ left < c.target - 2 * c.residual ∧
    c.target + 2 * c.residual < right ∧ c.residual ≤ accuracy)

def check (T : Matrix (Fin n) (Fin n) ℚ) (left right accuracy : ℚ) (code : ℕ) : Bool :=
  match Encodable.decode (α := SimpleCertificate n) code with
  | none => false
  | some c => accepts T left right accuracy c

def endpoints (code : ℕ) : ℚ × ℚ :=
  match Encodable.decode (α := SimpleCertificate n) code with
  | none => (0, 0)
  | some c => (c.target - 2 * c.residual, c.target + 2 * c.residual)

/-- Every accepted finite energy certificate encloses the selected actual
spectral value, with width bounded by four times the requested accuracy. -/
theorem accepts_sound (T : Matrix (Fin n) (Fin n) ℚ) (left right accuracy : ℚ)
    (μ : ℝ)
    (hisolate : ∀ ν ∈ spectrum ℝ (rationalOperator T),
      ν ∈ Set.Icc (left : ℝ) (right : ℝ) → ν = μ)
    (c : SimpleCertificate n) (hcheck : accepts T left right accuracy c = true) :
    ((c.target - 2 * c.residual : ℚ) : ℝ) ≤ μ ∧
      μ ≤ ((c.target + 2 * c.residual : ℚ) : ℝ) ∧
      (c.target + 2 * c.residual) - (c.target - 2 * c.residual) ≤ 4 * accuracy := by
  obtain ⟨hc, hl, hr, hres⟩ := of_decide_eq_true hcheck
  have hT := (of_decide_eq_true hc).1
  obtain ⟨ν, u, hu, heig, herror, _⟩ :=
    c.sound T 0 (rationalOperator T) (rationalOperator_symmetric T hT) (by simp) hc
  simp only [Rat.cast_zero, zero_add] at herror
  have hν : ν ∈ spectrum ℝ (rationalOperator T) := by
    rw [ContinuousLinearMap.spectrum_eq]
    apply HasEigenvalue.mem_spectrum
    apply hasEigenvalue_iff.mpr
    intro hbot
    have hmem := mem_eigenspace_iff.mpr heig
    rw [hbot] at hmem
    have hz : u = 0 := hmem
    simp [hz] at hu
  have hνμ : ν = μ := by
    apply hisolate ν hν
    have hl' : (left : ℝ) < (c.target : ℝ) - 2 * (c.residual : ℝ) := by exact_mod_cast hl
    have hr' : (c.target : ℝ) + 2 * (c.residual : ℝ) < right := by exact_mod_cast hr
    have he := abs_le.mp herror
    constructor <;> linarith
  rw [hνμ] at herror
  have he := abs_le.mp herror
  refine ⟨?_, ?_, by linarith⟩
  · push_cast
    linarith
  · push_cast
    linarith

/-- The actual simple eigenpair supplies finite certificates at every
positive rational energy accuracy. -/
theorem accepts_complete (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm)
    (left right accuracy : ℚ) (haccuracy : 0 < accuracy)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (hu : ‖u‖ = 1)
    (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1)
    (hleft : (left : ℝ) < μ) (hright : μ < (right : ℝ)) :
    ∃ c : SimpleCertificate n, accepts T left right accuracy c = true := by
  let a : ℝ := min (accuracy : ℝ) (min ((μ - left) / 4) (((right : ℝ) - μ) / 4))
  have haccuracy' : (0 : ℝ) < accuracy := by exact_mod_cast haccuracy
  have ha : 0 < a := by dsimp only [a]; positivity
  obtain ⟨_, c, hc, htarget, _, hres, _, _⟩ :=
    (simpleCertificate_complete_eventually (rationalOperator T) u μ
      (fun _ => T) (fun _ => 0) hu hTu hsimple (fun _ => hT) (fun _ => le_rfl)
      tendsto_const_nhds (by simp) a ha).exists
  simp only [Rat.cast_zero, zero_add] at hres
  have hal : a ≤ (μ - left) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have har : a ≤ ((right : ℝ) - μ) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have haacc : a ≤ (accuracy : ℝ) := min_le_left _ _
  have ht := abs_lt.mp htarget
  have hrespos : (0 : ℝ) < c.residual := by exact_mod_cast (of_decide_eq_true hc).2.2.2.1
  refine ⟨c, decide_eq_true ⟨hc, ?_, ?_, ?_⟩⟩
  · exact_mod_cast (show (left : ℝ) < (c.target : ℝ) - 2 * (c.residual : ℝ) by linarith)
  · exact_mod_cast (show (c.target : ℝ) + 2 * (c.residual : ℝ) < (right : ℝ) by linarith)
  · exact_mod_cast (show (c.residual : ℝ) ≤ accuracy by linarith)

theorem check_complete (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm)
    (left right accuracy : ℚ) (haccuracy : 0 < accuracy)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (hu : ‖u‖ = 1)
    (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1)
    (hleft : (left : ℝ) < μ) (hright : μ < (right : ℝ)) :
    ∃ code, check T left right accuracy code = true := by
  obtain ⟨c, hc⟩ := accepts_complete T hT left right accuracy haccuracy u μ hu hTu hsimple hleft hright
  exact ⟨Encodable.encode c, by simp [check, hc]⟩

theorem check_sound (T : Matrix (Fin n) (Fin n) ℚ) (left right accuracy : ℚ)
    (μ : ℝ)
    (hisolate : ∀ ν ∈ spectrum ℝ (rationalOperator T),
      ν ∈ Set.Icc (left : ℝ) (right : ℝ) → ν = μ)
    (code : ℕ) (hcheck : check T left right accuracy code = true) :
    ((endpoints (n := n) code).1 : ℝ) ≤ μ ∧ μ ≤ ((endpoints (n := n) code).2 : ℝ) ∧
      (endpoints (n := n) code).2 - (endpoints (n := n) code).1 ≤ 4 * accuracy := by
  cases hd : Encodable.decode (α := SimpleCertificate n) code with
  | none => simp [check, hd] at hcheck
  | some c =>
    simp only [check, hd] at hcheck
    simpa only [endpoints, hd] using accepts_sound T left right accuracy μ hisolate c hcheck

/-- Only finite rational inputs and an erased termination proof are
supplied to the runtime search. -/
def sequence (T : Matrix (Fin n) (Fin n) ℚ) (left right : ℚ)
    (h : ∀ k, ∃ code, check T left right (EdgeSourceEnclosure.accuracy k) code = true)
    (k : ℕ) : ℚ × ℚ := endpoints (n := n) (Nat.find (h k))

theorem sequence_terminates (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm)
    (left right : ℚ) (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (hu : ‖u‖ = 1)
    (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1)
    (hleft : (left : ℝ) < μ) (hright : μ < (right : ℝ)) :
    ∀ k, ∃ code, check T left right (EdgeSourceEnclosure.accuracy k) code = true := by
  intro k
  exact check_complete T hT left right (EdgeSourceEnclosure.accuracy k)
    (EdgeSourceEnclosure.accuracy_pos k) u μ hu hTu hsimple hleft hright

/-- Both rational endpoint sequences converge to the same selected actual
energy while enclosing it at every finite stage. -/
theorem certified_sequence (T : Matrix (Fin n) (Fin n) ℚ) (left right : ℚ)
    (h : ∀ k, ∃ code, check T left right (EdgeSourceEnclosure.accuracy k) code = true)
    (μ : ℝ)
    (hisolate : ∀ ν ∈ spectrum ℝ (rationalOperator T),
      ν ∈ Set.Icc (left : ℝ) (right : ℝ) → ν = μ) :
    (∀ k, ((sequence T left right h k).1 : ℝ) ≤ μ ∧
      μ ≤ ((sequence T left right h k).2 : ℝ) ∧
      (sequence T left right h k).2 - (sequence T left right h k).1 ≤
        4 * EdgeSourceEnclosure.accuracy k) ∧
    Tendsto (fun k => ((sequence T left right h k).1 : ℝ)) atTop (𝓝 μ) ∧
    Tendsto (fun k => ((sequence T left right h k).2 : ℝ)) atTop (𝓝 μ) := by
  have hbounds (k : ℕ) := check_sound T left right (EdgeSourceEnclosure.accuracy k)
    μ hisolate (Nat.find (h k)) (Nat.find_spec (h k))
  change ∀ k, ((sequence T left right h k).1 : ℝ) ≤ μ ∧
    μ ≤ ((sequence T left right h k).2 : ℝ) ∧
    (sequence T left right h k).2 - (sequence T left right h k).1 ≤
      4 * EdgeSourceEnclosure.accuracy k at hbounds
  have hlim : Tendsto (fun k => 4 * (EdgeSourceEnclosure.accuracy k : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using EdgeSourceEnclosure.accuracy_tendsto.const_mul 4
  refine ⟨hbounds, ?_, ?_⟩
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
    intro k
    obtain ⟨hl, hu, hw⟩ := hbounds k
    have hw' : ((sequence T left right h k).2 : ℝ) - (sequence T left right h k).1 ≤
        4 * (EdgeSourceEnclosure.accuracy k : ℝ) := by exact_mod_cast hw
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hl)]
    linarith
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
    intro k
    obtain ⟨hl, hu, hw⟩ := hbounds k
    have hw' : ((sequence T left right h k).2 : ℝ) - (sequence T left right h k).1 ≤
        4 * (EdgeSourceEnclosure.accuracy k : ℝ) := by exact_mod_cast hw
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hu)]
    linarith

/-- The actual simple eigenpair determines fixed rational isolation data
and therefore a fully executable convergent energy-bracket sequence. -/
theorem exists_certified_sequence (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (hu : ‖u‖ = 1)
    (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1) :
    ∃ (left right : ℚ)
      (h : ∀ k, ∃ code, check T left right (EdgeSourceEnclosure.accuracy k) code = true),
      (left : ℝ) < μ ∧ μ < (right : ℝ) ∧
      (∀ k, ((sequence T left right h k).1 : ℝ) ≤ μ ∧
        μ ≤ ((sequence T left right h k).2 : ℝ)) ∧
      Tendsto (fun k => ((sequence T left right h k).1 : ℝ)) atTop (𝓝 μ) ∧
      Tendsto (fun k => ((sequence T left right h k).2 : ℝ)) atTop (𝓝 μ) := by
  obtain ⟨left, right, hleft, hright, hisolate⟩ :=
    EdgeSourceEnclosure.exists_rational_isolating_interval T μ
  let h := sequence_terminates T hT left right u μ hu hTu hsimple hleft hright
  obtain ⟨hb, hl, hr⟩ := certified_sequence T left right h μ hisolate
  exact ⟨left, right, h, hleft, hright, fun k => ⟨(hb k).1, (hb k).2.1⟩, hl, hr⟩

/-- Source coordinates and edge-energy brackets are certified against
the same exact rational matrix, actual eigenpair, and isolating interval. -/
theorem exists_source_energy_sequences (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (hu : ‖u‖ = 1)
    (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1) :
    ∃ (left right : ℚ) (reference : Fin n → ℚ)
      (hs : ∀ k, ∃ code, EdgeSourceEnclosure.check T left right reference
        (EdgeSourceEnclosure.referenceBound reference) (EdgeSourceEnclosure.accuracy k) code = true)
      (he : ∀ k, ∃ code, check T left right (EdgeSourceEnclosure.accuracy k) code = true),
      (left : ℝ) < μ ∧ μ < (right : ℝ) ∧
      (∀ k, ‖u - rationalVector (EdgeSourceEnclosure.sequence T left right reference
        (EdgeSourceEnclosure.referenceBound reference) hs k)‖ ≤ (EdgeSourceEnclosure.accuracy k : ℝ)) ∧
      (∀ k, ((sequence T left right he k).1 : ℝ) ≤ μ ∧
        μ ≤ ((sequence T left right he k).2 : ℝ)) ∧
      Tendsto (fun k => ((sequence T left right he k).1 : ℝ)) atTop (𝓝 μ) ∧
      Tendsto (fun k => ((sequence T left right he k).2 : ℝ)) atTop (𝓝 μ) := by
  obtain ⟨left, right, reference, hs, hleft, hright, hisolate, _, hsource, _⟩ :=
    EdgeSourceEnclosure.exists_certified_sequence T hT u μ hu hTu hsimple
  let he := sequence_terminates T hT left right u μ hu hTu hsimple hleft hright
  obtain ⟨hb, hl, hr⟩ := certified_sequence T left right he μ hisolate
  exact ⟨left, right, reference, hs, he, hleft, hright, hsource,
    fun k => ⟨(hb k).1, (hb k).2.1⟩, hl, hr⟩

end Maxwell.Defect.EdgeEnergyEnclosure
