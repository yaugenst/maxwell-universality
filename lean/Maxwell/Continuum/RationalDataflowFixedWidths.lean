import Maxwell.Continuum.RationalDataflowTrace

/-! Automatic raw-width bounds for fixed arithmetic and comparison control. -/
namespace Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 2000000

theorem Instruction.update_width (S : Finset ℕ) (a : Instruction) (ha : a.Valid S)
    (v : ℕ→Parts) (W : ℕ) (hv : WidthBank S W v) (hl : a.LiteralFits W) :
    WidthBank S (2*W+1) (a.update v) := by
  have base := hv.mono (show W≤2*W+1 by omega)
  cases a with
  | literal target q => exact base.update target (hl.mono (by omega))
  | binary op target left right =>
    have hx := hv left ha.2.1
    have hy := hv right ha.2.2
    cases op
    · exact base.update target ((hx.add hy).mono (by omega))
    · exact base.update target ((hx.sub hy).mono (by omega))
    · exact base.update target ((hx.mul hy).mono (by omega))
  | inverse target source => exact base.update target ((hv source ha.2).inverse.mono (by omega))

def Control.LiteralsFit (W : ℕ) : Control→Prop
  | .done => True
  | .step a rest => a.LiteralFits W ∧ rest.LiteralsFit W
  | .positive _ yes no => yes.LiteralsFit W ∧ no.LiteralsFit W

theorem Instruction.LiteralFits.mono {a : Instruction} {B C : ℕ} (h : a.LiteralFits B)
    (hBC : B≤C) : a.LiteralFits C := by
  cases a
  · exact Parts.Width.mono h hBC
  · trivial
  · trivial

theorem Control.LiteralsFit.mono {c : Control} {B C : ℕ} (h : c.LiteralsFit B)
    (hBC : B≤C) : c.LiteralsFit C := by
  induction c with
  | done => trivial
  | step a rest ih => exact ⟨h.1.mono hBC,ih h.2⟩
  | positive source yes no iy ino => exact ⟨iy h.1,ino h.2⟩

theorem Control.WidthTrace.mono {c : Control} {S : Finset ℕ} {B C : ℕ} {v : ℕ→Parts}
    (h : c.WidthTrace S B v) (hBC : B≤C) : c.WidthTrace S C v := by
  induction c generalizing v with
  | done => exact WidthBank.mono h hBC
  | step a rest ih => exact ⟨WidthBank.mono h.1 hBC,Instruction.LiteralFits.mono h.2.1 hBC,ih h.2.2⟩
  | positive source yes no iy ino =>
    refine ⟨WidthBank.mono h.1 hBC,?_⟩
    split_ifs with hp
    · exact iy (by simpa only [Control.WidthTrace,hp,ite_true] using h.2)
    · exact ino (by simpa only [Control.WidthTrace,hp,ite_false] using h.2)

theorem Control.automatic_widthTrace (c : Control) (S : Finset ℕ) (hc : c.Valid S)
    (v : ℕ→Parts) (W : ℕ) (hv : WidthBank S W v) (hl : c.LiteralsFit W) :
    c.WidthTrace S (2^c.steps*(W+1)) v := by
  induction c generalizing v W with
  | done => exact hv.mono (by simp only [Control.steps,pow_zero,one_mul]; omega)
  | step a rest ih =>
    have hp : 1≤2^(.step a rest : Control).steps := one_le_pow₀ (by decide)
    have base : W≤2^(.step a rest : Control).steps*(W+1) := by nlinarith
    refine ⟨hv.mono base,hl.1.mono base,?_⟩
    have tail := ih hc.2 (a.update v) (2*W+1)
      (a.update_width S hc.1 v W hv hl.1) (hl.2.mono (by omega))
    have he : 2^rest.steps*(2*W+1+1)=2^(.step a rest : Control).steps*(W+1) := by
      simp only [Control.steps,pow_add,pow_one]
      ring
    rw [he] at tail
    exact tail
  | positive source yes no iy ino =>
    have hp : 1≤2^(.positive source yes no : Control).steps := one_le_pow₀ (by decide)
    have base : W≤2^(.positive source yes no : Control).steps*(W+1) := by nlinarith
    refine ⟨hv.mono base,?_⟩
    split_ifs
    · apply (iy hc.2.1 v W hv hl.1).mono
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_right (by decide) (by simp only [Control.steps]; omega)
    · apply (ino hc.2.2 v W hv hl.2).mono
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_right (by decide) (by simp only [Control.steps]; omega)

#print axioms Control.automatic_widthTrace
end Maxwell.Continuum.RationalDataflow
