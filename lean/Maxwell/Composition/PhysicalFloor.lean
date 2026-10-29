import Maxwell.Composition.PhysicalPlatform

/-! A fixed rational-search enlargement of the physical spacing floor.
It enforces local tuning headroom and complementary-block smallness without
adding any input-dependent analytic assumptions. -/
namespace Maxwell.Composition.PhysicalPlatform

def tuningMargin (P : PhysicalPlatform) : ℚ :=
  min (P.defectGap/8) (1/(2*P.incrementBound))

theorem tuningMargin_pos (P : PhysicalPlatform) : 0 < P.tuningMargin := by
  unfold tuningMargin
  exact lt_min (div_pos P.defectGap_pos (by norm_num))
    (div_pos (by norm_num) (mul_pos (by norm_num) P.incrementBound_pos))

def zetaTarget (P : PhysicalPlatform) : ℚ :=
  min (1/2) (min P.tuningMargin (P.defectGap/(8*(64*P.greenConstant+2))))

theorem zetaTarget_pos (P : PhysicalPlatform) : 0 < P.zetaTarget := by
  have hC := P.greenConstant_nonneg
  unfold zetaTarget
  exact lt_min (by norm_num) (lt_min P.tuningMargin_pos (div_pos P.defectGap_pos (by positivity)))

def mediatorScale (P : PhysicalPlatform) : ℚ := 4*(P.greenConstant+1)^2/P.spacing.c

theorem mediatorScale_pos (P : PhysicalPlatform) : 0 < P.mediatorScale := by
  have hC := P.greenConstant_nonneg
  unfold mediatorScale
  exact div_pos (by positivity) P.spacing.c_pos

def alphaTarget (P : PhysicalPlatform) : ℚ := P.tuningMargin/(6*(P.spacing.c/4))

theorem alphaTarget_pos (P : PhysicalPlatform) : 0 < P.alphaTarget :=
  div_pos P.tuningMargin_pos (mul_pos (by norm_num) (div_pos P.spacing.c_pos (by norm_num)))

def coreFloor (P : PhysicalPlatform) : ℕ := max P.spacing.minimumDistance
  (max (Realization.geometricSteps P.spacing.r P.zetaTarget P.spacing.r_pos P.spacing.r_lt_one P.zetaTarget_pos)
    (max (Realization.geometricSteps P.spacing.a P.alphaTarget P.spacing.a_pos P.spacing.a_lt_one P.alphaTarget_pos)
      (Realization.geometricSteps P.spacing.ratio (P.tuningMargin/P.mediatorScale)
        P.spacing.ratio_pos P.spacing.ratio_lt_one (div_pos P.tuningMargin_pos P.mediatorScale_pos))))

theorem coreFloor_minimum (P : PhysicalPlatform) : P.spacing.minimumDistance ≤ P.coreFloor := le_max_left _ _

private theorem pow_le_after_steps (r t : ℚ) (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t)
    (d : ℕ) (hd : Realization.geometricSteps r t hr hr1 ht ≤ d) : r^d ≤ t :=
  ((pow_le_pow_iff_right_of_lt_one₀ hr hr1).mpr hd).trans (Realization.geometricSteps_spec r t hr hr1 ht)

theorem coreFloor_zeta (P : PhysicalPlatform) (d : ℕ) (hd : P.coreFloor ≤ d) :
    P.spacing.zeta d ≤ P.zetaTarget := by
  apply pow_le_after_steps
  exact (le_max_left _ _).trans ((le_max_right _ _).trans hd)

theorem coreFloor_alpha (P : PhysicalPlatform) (d : ℕ) (hd : P.coreFloor ≤ d) :
    6*P.spacing.alpha d ≤ P.tuningMargin := by
  have ha : P.spacing.a^d ≤ P.alphaTarget := by
    apply pow_le_after_steps
    exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  have hc : 0 < 6*(P.spacing.c/4) := by have := P.spacing.c_pos; positivity
  have h := (le_div_iff₀ hc).mp ha
  change P.spacing.a^d * (6*(P.spacing.c/4)) ≤ P.tuningMargin at h
  simpa only [Realization.SpacingPlatform.alpha, mul_assoc, mul_left_comm, mul_comm] using h

theorem mediatorScale_identity (P : PhysicalPlatform) (d : ℕ) :
    ((P.greenConstant+1)*P.spacing.zeta d)^2/P.spacing.alpha d = P.mediatorScale*P.spacing.ratio^d := by
  have hc := P.spacing.c_pos.ne'
  have ha := (pow_pos P.spacing.a_pos d).ne'
  simp only [Realization.SpacingPlatform.zeta, Realization.SpacingPlatform.alpha,
    Realization.SpacingPlatform.ratio, mediatorScale, div_pow, mul_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm d 2]
  field_simp

theorem coreFloor_mediator (P : PhysicalPlatform) (d : ℕ) (hd : P.coreFloor ≤ d) :
    ((P.greenConstant+1)*P.spacing.zeta d)^2/P.spacing.alpha d ≤ P.tuningMargin := by
  rw [mediatorScale_identity]
  have hr : P.spacing.ratio^d ≤ P.tuningMargin/P.mediatorScale := by
    apply pow_le_after_steps
    exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  exact (mul_le_mul_of_nonneg_left hr P.mediatorScale_pos.le).trans_eq
    (mul_div_cancel₀ _ P.mediatorScale_pos.ne')

theorem coreFloor_small (P : PhysicalPlatform) (d : ℕ) (hd : P.coreFloor ≤ d) :
    P.spacing.zeta d ≤ 1/2 ∧ (P.spacing.zeta d)^2 ≤ P.tuningMargin ∧
      P.tuningMargin + 64*P.greenConstant*P.spacing.zeta d + 2*(P.spacing.zeta d)^2 ≤ P.defectGap/2 := by
  have hz := P.coreFloor_zeta d hd
  have hhalf := hz.trans (min_le_left _ _)
  have hmargin := hz.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hscale := hz.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hC := P.greenConstant_nonneg
  have hg := P.defectGap_pos
  have hz0 := (P.spacing.zeta_pos d).le
  have hs := (le_div_iff₀ (by positivity : (0 : ℚ)<8*(64*P.greenConstant+2))).mp hscale
  have hm := min_le_left (P.defectGap/8) (1/(2*P.incrementBound))
  change P.tuningMargin ≤ P.defectGap/8 at hm
  refine ⟨hhalf, ?_, ?_⟩ <;> nlinarith

/-- Enlarging the fixed spacing floor preserves every actual physical
certificate; this constructor does not alter any operator or source. -/
def withCoreFloor (P : PhysicalPlatform) : PhysicalPlatform :=
  { P with
    spacing := { P.spacing with minimumDistance := P.coreFloor }
    radius_floor := P.radius_floor.trans P.coreFloor_minimum
    green_upper := fun d hd => P.green_upper d (P.coreFloor_minimum.trans hd)
    green_axial := fun d hd => P.green_axial d (P.coreFloor_minimum.trans hd) }

end Maxwell.Composition.PhysicalPlatform
