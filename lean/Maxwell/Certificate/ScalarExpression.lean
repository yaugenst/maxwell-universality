import Maxwell.Certificate.Elementary

/-! Exact arithmetic expression certificates with an independently proposed
rational enclosure at every operation. Producers may round each enclosure
outward without forcing later checks to retain expanding denominators. -/
namespace Maxwell.Certificate.ScalarExpression

-- `Certificate` names the annotated expression, within the certificate library.
set_option linter.dupNamespace false

inductive Expr where
  | rat (q : ℚ)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | inv (a : Expr)
  | sqrt (a : Expr)
  deriving DecidableEq

/-- A proof-free initializer for rational interval proposals. -/
def enclosure (lo hi : ℚ) : Interval := ⟨min lo hi, max lo hi, min_le_max⟩

noncomputable def Expr.eval : Expr → ℝ
  | .rat q => q
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval
  | .inv a => 1 / a.eval
  | .sqrt a => Real.sqrt a.eval

/-- The certificate stores the expression and proposed enclosures in one
tree. Literal leaves have their exact singleton enclosure. -/
inductive Certificate where
  | rat (q : ℚ)
  | add (a b : Certificate) (out : Interval)
  | sub (a b : Certificate) (out : Interval)
  | mul (a b : Certificate) (out : Interval)
  | inv (a : Certificate) (out : Interval)
  | sqrt (a : Certificate) (out : Interval)

def Certificate.expr : Certificate → Expr
  | .rat q => .rat q
  | .add a b _ => .add a.expr b.expr
  | .sub a b _ => .sub a.expr b.expr
  | .mul a b _ => .mul a.expr b.expr
  | .inv a _ => .inv a.expr
  | .sqrt a _ => .sqrt a.expr

def Certificate.interval : Certificate → Interval
  | .rat q => Interval.point q
  | .add _ _ out | .sub _ _ out | .mul _ _ out | .inv _ out | .sqrt _ out => out

/-- Multiplication is enclosed by checking all four endpoint products. -/
def mulCheck (a b out : Interval) : Bool :=
  decide (out.lo ≤ a.lo * b.lo ∧ out.lo ≤ a.lo * b.hi ∧
    out.lo ≤ a.hi * b.lo ∧ out.lo ≤ a.hi * b.hi ∧
    a.lo * b.lo ≤ out.hi ∧ a.lo * b.hi ≤ out.hi ∧
    a.hi * b.lo ≤ out.hi ∧ a.hi * b.hi ≤ out.hi)

/-- Only a strictly positive denominator interval is accepted. -/
def invCheck (a out : Interval) : Bool :=
  decide (0 < a.lo ∧ out.lo ≤ 1 / a.hi ∧ 1 / a.lo ≤ out.hi)

def verify : Certificate → Bool
  | .rat _ => true
  | .add a b out => verify a && verify b && Interval.subsetCheck (a.interval.add b.interval) out
  | .sub a b out => verify a && verify b &&
      Interval.subsetCheck (a.interval.add b.interval.neg) out
  | .mul a b out => verify a && verify b && mulCheck a.interval b.interval out
  | .inv a out => verify a && invCheck a.interval out
  | .sqrt a out => verify a && Interval.sqrtCheck a.interval out

private theorem affine_bounds (l u x k low high : ℝ)
    (hx : l ≤ x ∧ x ≤ u)
    (hl : low ≤ k * l ∧ k * l ≤ high)
    (hu : low ≤ k * u ∧ k * u ≤ high) :
    low ≤ k * x ∧ k * x ≤ high := by
  by_cases hk : 0 ≤ k
  · exact ⟨hl.1.trans (mul_le_mul_of_nonneg_left hx.1 hk),
      (mul_le_mul_of_nonneg_left hx.2 hk).trans hu.2⟩
  · exact ⟨hu.1.trans (mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge hk)),
      (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hk)).trans hl.2⟩

theorem mulCheck_sound {a b out : Interval} (h : mulCheck a b out = true)
    {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) : out.Contains (x * y) := by
  have hq : out.lo ≤ a.lo * b.lo ∧ out.lo ≤ a.lo * b.hi ∧
      out.lo ≤ a.hi * b.lo ∧ out.lo ≤ a.hi * b.hi ∧
      a.lo * b.lo ≤ out.hi ∧ a.lo * b.hi ≤ out.hi ∧
      a.hi * b.lo ≤ out.hi ∧ a.hi * b.hi ≤ out.hi := of_decide_eq_true h
  have hll : (out.lo : ℝ) ≤ (a.lo : ℝ) * b.lo ∧ (a.lo : ℝ) * b.lo ≤ out.hi := by
    exact_mod_cast And.intro hq.1 hq.2.2.2.2.1
  have hlu : (out.lo : ℝ) ≤ (a.lo : ℝ) * b.hi ∧ (a.lo : ℝ) * b.hi ≤ out.hi := by
    exact_mod_cast And.intro hq.2.1 hq.2.2.2.2.2.1
  have hul : (out.lo : ℝ) ≤ (a.hi : ℝ) * b.lo ∧ (a.hi : ℝ) * b.lo ≤ out.hi := by
    exact_mod_cast And.intro hq.2.2.1 hq.2.2.2.2.2.2.1
  have huu : (out.lo : ℝ) ≤ (a.hi : ℝ) * b.hi ∧ (a.hi : ℝ) * b.hi ≤ out.hi := by
    exact_mod_cast And.intro hq.2.2.2.1 hq.2.2.2.2.2.2.2
  have hlo := affine_bounds b.lo b.hi y a.lo out.lo out.hi hy hll hlu
  have hhi := affine_bounds b.lo b.hi y a.hi out.lo out.hi hy hul huu
  have hh := affine_bounds a.lo a.hi x y out.lo out.hi hx
    (by simpa only [mul_comm] using hlo) (by simpa only [mul_comm] using hhi)
  simpa only [Interval.Contains, mul_comm] using hh

theorem invCheck_sound {a out : Interval} (h : invCheck a out = true)
    {x : ℝ} (hx : a.Contains x) : out.Contains (1 / x) := by
  have hq : 0 < a.lo ∧ out.lo ≤ 1 / a.hi ∧ 1 / a.lo ≤ out.hi := of_decide_eq_true h
  have hr := Interval.reciprocal_contains hq.1 hx
  have hlo : (out.lo : ℝ) ≤ (1 : ℝ) / a.hi := by exact_mod_cast hq.2.1
  have hhi : (1 : ℝ) / a.lo ≤ (out.hi : ℝ) := by exact_mod_cast hq.2.2
  have hr' : 1 / (a.hi : ℝ) ≤ 1 / x ∧ 1 / x ≤ 1 / (a.lo : ℝ) := by
    simpa only [Interval.Contains, Interval.reciprocal, Rat.cast_div, Rat.cast_one] using hr
  exact ⟨hlo.trans hr'.1, hr'.2.trans hhi⟩

/-- Acceptance is a finite rational check; its conclusion refers to the
ordinary real arithmetic semantics of the expression. -/
theorem verify_sound (c : Certificate) (h : verify c = true) :
    c.interval.Contains c.expr.eval := by
  induction c with
  | rat q => exact Interval.contains_point q
  | add a b out iha ihb =>
    simp only [verify, Bool.and_eq_true] at h
    exact Interval.subsetCheck_sound h.2 (Interval.contains_add (iha h.1.1) (ihb h.1.2))
  | sub a b out iha ihb =>
    simp only [verify, Bool.and_eq_true] at h
    simpa only [Certificate.interval, Certificate.expr, Expr.eval, sub_eq_add_neg] using
      Interval.subsetCheck_sound h.2
        (Interval.contains_add (iha h.1.1) (Interval.contains_neg (ihb h.1.2)))
  | mul a b out iha ihb =>
    simp only [verify, Bool.and_eq_true] at h
    exact mulCheck_sound h.2 (iha h.1.1) (ihb h.1.2)
  | inv a out ih =>
    simp only [verify, Bool.and_eq_true] at h
    exact invCheck_sound h.2 (ih h.1)
  | sqrt a out ih =>
    simp only [verify, Bool.and_eq_true] at h
    exact Interval.sqrtCheck_sound h.2 (ih h.1)

/-- Tie an enclosure certificate to the exact expected arithmetic formula. -/
def verifyExpr (e : Expr) (c : Certificate) : Bool := verify c && decide (c.expr = e)

theorem verifyExpr_sound (e : Expr) (c : Certificate) (h : verifyExpr e c = true) :
    c.interval.Contains e.eval := by
  simp only [verifyExpr, Bool.and_eq_true] at h
  obtain ⟨hv, he⟩ := h
  have he' : c.expr = e := of_decide_eq_true he
  rw [← he']
  exact verify_sound c hv

end Maxwell.Certificate.ScalarExpression
